import Mathlib
import SteinTomasCircle.Basic.Elementary
import SteinTomasCircle.Section2.BesselGlobal
import SteinTomasCircle.Section3.LargeMeanCore
import SteinTomasCircle.Section2.LocalBessel
import SteinTomasCircle.Section2.Analysis
import SteinTomasCircle.Section2.FourierSeries
import SteinTomasCircle.Section2.PolarKernel
import SteinTomasCircle.Section2.NormalizedExtension
import SteinTomasCircle.Section2.PhiIdentity
import SteinTomasCircle.Section2.QuadraticSpectral

/-!
# Assembly of Prop 3.1: all results of Section 2 fed into Section 3

`prop_large_mean_full`: for f ≥ 0 antipodal with ‖f‖₂ = 1, nonconstant and ‖Ef‖₆ ≥ ‖Ee₀‖₆, we have a₀ < 5/8.
All other premises are external inputs from the literature:
* `BesselKernel` (DLMF 10.9.2, 10.4.1), continuity of J_{2k}, the zero set of J₀ is null (DLMF 10.21);
* `SeriesHyp` (DLMF 10.2.2), DLMF 10.14.4: |J_n(r)| ≤ (r/2)ⁿ/n!;
* `AlphaLit` (CFOT17 Table 1, OST17) and integrability of J₀⁴J_{2n}²r;
* the EL equation paired with e₀ (CQ14, OQ21b) and integrability of (Ef)⁶, (Ef)⁵Ee₀, (Ee₀)⁶ (Stein–Tomas).
-/

namespace SteinTomas.S2W

open Real MeasureTheory Set SteinTomas.S2F SteinTomas.S2K SteinTomas.Section2

noncomputable section

variable {f : ℝ → ℝ} {Jb : ℕ → ℝ → ℝ}

/-- ∫(Ee₀)⁶ = (2π)⁴ α₀ -/
lemma energy_e0 (hB : S2E.BesselKernel Jb) (hi0 : Integrable (fun x => S2P.Ec S2P.e0 x ^ 6)) :
    ∫ x, S2P.Ec S2P.e0 x ^ 6 = (2 * π) ^ 4 * S2Q.alpha Jb 0 := by
  rw [S2P.polar_integral hi0]
  have e : ∀ r ∈ Ioi (0 : ℝ),
      (∫ φ in Ioo (-π) π, S2P.Ec S2P.e0 (r * Real.cos φ, r * Real.sin φ) ^ 6) * r
        = (2 * π) ^ 4 * (Jb 0 r ^ 4 * Jb 0 r ^ 2 * r) := by
    intro r _
    simp_rw [S2P.Ec_e0_polar hB]
    rw [S2P.angle_range (g := fun _ => (Real.sqrt (2 * π) * Jb 0 r) ^ 6) (fun _ => rfl),
      intervalIntegral.integral_const, smul_eq_mul]
    have hs : Real.sqrt (2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
    rw [mul_pow, show Real.sqrt (2 * π) ^ 6 = (Real.sqrt (2 * π) ^ 2) ^ 3 by ring, hs]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, MeasureTheory.integral_const_mul]
  rfl

/-- Nonconstant ⇒ 1 − a₀² > 0 (since ∫(f − a₀/√(2π))² = 1 − a₀²) -/
lemma one_sub_a0_sq_pos (hf : MemLp f 2 (volume.restrict (Ioc 0 (2 * π))))
    (hnorm : ∫ θ in (0 : ℝ)..(2 * π), f θ ^ 2 = 1)
    (hnc : ∀ c : ℝ, ¬ (∀ᵐ θ ∂(volume.restrict (Ioc 0 (2 * π))), f θ = c)) :
    0 < 1 - a0 f ^ 2 := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hs0 : Real.sqrt (2 * π) ≠ 0 := Real.sqrt_ne_zero'.2 (by positivity)
  have hs : Real.sqrt (2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt (2 * π) := ⟨_, rfl⟩
  rw [← hsdef] at hs0 hs
  have hf1 : IntervalIntegrable f volume 0 (2 * π) := intervalIntegrable_of_memLp hf
  have hf2 : IntervalIntegrable (fun θ => f θ ^ 2) volume 0 (2 * π) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).2 hf.integrable_sq
  have e : (fun θ => (f θ - a0 f / s) ^ 2)
      = fun θ => (f θ ^ 2 - (2 * (a0 f / s)) * f θ) + (a0 f / s) ^ 2 := by
    funext θ; ring
  have hII : IntervalIntegrable (fun θ => (f θ - a0 f / s) ^ 2) volume 0 (2 * π) := by
    rw [e]; exact (hf2.sub (hf1.const_mul _)).add (continuous_const.intervalIntegrable _ _)
  have ha : ∫ θ in (0 : ℝ)..(2 * π), f θ = s * a0 f := by
    rw [a0, ← hsdef]; field_simp
  have hI : ∫ θ in (0 : ℝ)..(2 * π), (f θ - a0 f / s) ^ 2 = 1 - a0 f ^ 2 := by
    rw [e, intervalIntegral.integral_add (hf2.sub (hf1.const_mul _))
        (continuous_const.intervalIntegrable _ _),
      intervalIntegral.integral_sub hf2 (hf1.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, hnorm, ha, smul_eq_mul, div_pow, hs]
    field_simp
    ring
  by_contra hcon
  have hle : 1 - a0 f ^ 2 ≤ 0 := not_lt.mp hcon
  have hint : Integrable (fun θ => (f θ - a0 f / s) ^ 2) (volume.restrict (Ioc 0 (2 * π))) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).1 hII
  have hz : ∫ θ in Ioc 0 (2 * π), (f θ - a0 f / s) ^ 2 = 0 := by
    have h1 : ∫ θ in Ioc 0 (2 * π), (f θ - a0 f / s) ^ 2 = 1 - a0 f ^ 2 := by
      rw [← intervalIntegral.integral_of_le h2π]; exact hI
    have h2 : 0 ≤ ∫ θ in Ioc 0 (2 * π), (f θ - a0 f / s) ^ 2 :=
      integral_nonneg (fun θ => sq_nonneg _)
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg (fun θ => sq_nonneg _) hint).1 hz
  apply hnc (a0 f / s)
  filter_upwards [hae] with θ hθ
  have h0 : (f θ - a0 f / s) ^ 2 = 0 := hθ
  have := (pow_eq_zero_iff two_ne_zero).1 h0
  linarith

/-- J₀ > 0 on (0, 7/4] (pointwise estimate of Lemma 2.1) -/
lemma J0_pos (hser : Lemma21.SeriesHyp (Jb 0) (Jb 1)) {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) (7 / 4)) :
    0 < Jb 0 r := by
  have hrI : r ∈ Icc (0 : ℝ) (7 / 4) := ⟨hr.1.le, hr.2⟩
  have hx0 : 0 ≤ r ^ 2 / 4 := by positivity
  have hxx : r ^ 2 / 4 ≤ 49 / 64 := by nlinarith [hr.1, hr.2]
  exact (Analysis1.bessel_pointwise hx0 hxx (hser.1 r hrI) (hser.2 r hrI)).1

/-- DLMF 10.14.4 ⇒ |J_{2(n+2)}(r)| ≤ (r/2)⁴/24 on (0, 7/4] -/
lemma tail_kappa
    (hdlmf : ∀ (k : ℕ) (r : ℝ), 0 ≤ r → |Jb k r| ≤ (r / 2) ^ (2 * k) / ((2 * k).factorial : ℝ))
    {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) (7 / 4)) (n : ℕ) : |Jb (n + 2) r| ≤ (r / 2) ^ 4 / 24 := by
  have h := hdlmf (n + 2) r hr.1.le
  have hr2 : r / 2 ≤ 1 := by linarith [hr.2]
  have hr0 : 0 ≤ r / 2 := by linarith [hr.1]
  have hp : (r / 2) ^ (2 * (n + 2)) ≤ (r / 2) ^ 4 := pow_le_pow_of_le_one hr0 hr2 (by omega)
  have hfac : (24 : ℝ) ≤ ((2 * (n + 2)).factorial : ℝ) := by
    have := Nat.factorial_le (show 4 ≤ 2 * (n + 2) by omega)
    have h4 : Nat.factorial 4 = 24 := rfl
    rw [h4] at this
    exact_mod_cast this
  have hfp : (0 : ℝ) < ((2 * (n + 2)).factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos _)
  calc |Jb (n + 2) r| ≤ (r / 2) ^ (2 * (n + 2)) / ((2 * (n + 2)).factorial : ℝ) := h
    _ ≤ (r / 2) ^ 4 / ((2 * (n + 2)).factorial : ℝ) := (div_le_div_iff_of_pos_right hfp).2 hp
    _ ≤ (r / 2) ^ 4 / 24 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hfac

/-- **Prop 3.1 (full version)**: a₀ < 5/8 -/
theorem prop_large_mean_full
    -- about f
    (hf : MemLp f 2 (volume.restrict (Ioc 0 (2 * π)))) (hpos : ∀ θ, 0 ≤ f θ)
    (hanti : ∀ θ, f (θ + π) = f θ) (hnorm : ∫ θ in (0 : ℝ)..(2 * π), f θ ^ 2 = 1)
    (hnc : ∀ c : ℝ, ¬ (∀ᵐ θ ∂(volume.restrict (Ioc 0 (2 * π))), f θ = c))
    (hext : ∫ x, S2P.Ec S2P.e0 x ^ 6 ≤ ∫ x, S2P.Ec f x ^ 6)
    -- external input: EL equation (paired with e₀) and Stein–Tomas integrability
    (hi0 : Integrable (fun x => S2P.Ec S2P.e0 x ^ 6))
    (hi5 : Integrable (fun x => S2P.Ec f x ^ 5 * S2P.Ec S2P.e0 x))
    (hi6 : Integrable (fun x => S2P.Ec f x ^ 6))
    (hEL : ∫ x, S2P.Ec f x ^ 5 * S2P.Ec S2P.e0 x = (∫ x, S2P.Ec f x ^ 6) * a0 f)
    -- external input: Bessel functions
    (hB : S2E.BesselKernel Jb) (hcont : ∀ n, Continuous (Jb n))
    (hz : volume {r : ℝ | 0 < r ∧ Jb 0 r = 0} = 0)
    (hser : Lemma21.SeriesHyp (Jb 0) (Jb 1))
    (hdlmf : ∀ (k : ℕ) (r : ℝ), 0 ≤ r → |Jb k r| ≤ (r / 2) ^ (2 * k) / ((2 * k).factorial : ℝ))
    (hint : ∀ n, IntegrableOn (fun r => Jb 0 r ^ 4 * Jb n r ^ 2 * r) (Ioi 0))
    (hlit : AlphaLit (S2Q.alpha Jb)) :
    a0 f < 5 / 8 := by
  obtain ⟨l0, l0', l1, l2⟩ := bessel_global hlit
  have hbd : ∃ C, ∀ n, S2Q.alpha Jb n ≤ C := by
    refine ⟨1, fun n => ?_⟩
    rcases n with _ | _ | n
    · show S2Q.alpha Jb 0 ≤ 1; linarith
    · show S2Q.alpha Jb 1 ≤ 1; linarith
    · show S2Q.alpha Jb (n + 2) ≤ 1; linarith [l2 (n + 2) (by omega)]
  obtain ⟨S, hS, hi2, hquad⟩ := S2Q.quad_spectral hf hanti hB hcont hint hbd
  -- Parseval
  have hasq : ∀ k, 0 ≤ asq f k := fun k => by unfold asq; positivity
  have hpar : HasSum (asq f) (1 - a0 f ^ 2) := by
    have := parseval_even hf hanti
    rwa [hnorm] at this
  set a : ℕ → ℝ := fun n => Real.sqrt (asq f n) with ha_def
  have hsq : ∀ n, a n ^ 2 = asq f n := fun n => Real.sq_sqrt (hasq n)
  have hpars : HasSum (fun n => a n ^ 2) (1 - a0 f ^ 2) := by simp_rw [hsq]; exact hpar
  have hS' : HasSum (fun n => S2Q.alpha Jb (n + 1) * a n ^ 2) S := by simp_rw [hsq]; exact hS
  have hpos1 := one_sub_a0_sq_pos hf hnorm hnc
  have ha2sq : S2E.a2 f ^ 2 = asq f 0 := by rw [S2E.a2]; exact Real.sq_sqrt (hasq 0)
  have ha2b := S2E.a2_bound hf hpos hnorm
  have hS1 : S < S2Q.alpha Jb 0 / 9 * (1 - a0 f ^ 2) := by
    refine prop31a (α' := fun n => S2Q.alpha Jb (n + 1)) (fun n => ?_) hpars hpos1 hS'
    rcases n with _ | n
    · show S2Q.alpha Jb 1 < S2Q.alpha Jb 0 / 9; linarith
    · show S2Q.alpha Jb (n + 2) < S2Q.alpha Jb 0 / 9; linarith [l2 (n + 2) (by omega)]
  have hS2 : S ≤ 19 / 1000 * (1 - a0 f ^ 2) + 9 / 1000 := by
    refine sum_alpha_bound (α' := fun n => S2Q.alpha Jb (n + 1)) (a := a)
      (show S2Q.alpha Jb 1 < 37 / 1000 from l1)
      (fun n hn => show S2Q.alpha Jb (n + 1) < 19 / 1000 from l2 (n + 1) (by omega))
      ?_ hpars hS'
    rw [hsq 0, ← ha2sq]; exact ha2b
  have hsum : a0 f ^ 2 + S2E.a2 f ^ 2 ≤ 1 := by
    have h0 := le_hasSum hpar 0 (fun j _ => hasq j)
    linarith
  -- μ ≥ α₀
  have hμ : S2Q.alpha Jb 0 ≤ (1 / (2 * π) ^ 4) * ∫ x, S2P.Ec f x ^ 6 := by
    rw [energy_e0 hB hi0] at hext
    have hp : (0 : ℝ) < (2 * π) ^ 4 := by positivity
    calc S2Q.alpha Jb 0 = (1 / (2 * π) ^ 4) * ((2 * π) ^ 4 * S2Q.alpha Jb 0) := by
          rw [← mul_assoc, one_div, inv_mul_cancel₀ hp.ne', one_mul]
      _ ≤ (1 / (2 * π) ^ 4) * ∫ x, S2P.Ec f x ^ 6 := by gcongr
  -- the Φ-identity
  have hΦc : Continuous Φ := by show Continuous (fun x : ℝ => x ^ 5 - x ^ 6); fun_prop
  have hh : ∀ y : ℝ, 1 / 2 * y = y / 2 := fun y => by ring
  have id12 := S2P.phi_identity hf hB hz hi5 hi6 hEL (1 / 2)
  simp_rw [hh] at id12
  have idtt := S2P.phi_identity hf hB hz hi5 hi6 hEL tt
  -- angular integrability
  have hFc : ∀ r, Continuous (S2E.F Jb f r) := fun r => S2E.F_cont hf r
  have hwc : ∀ r, Continuous (S2E.w Jb f r) := fun r => S2E.w_cont hf r
  have hΦ2 : ∀ r, IntervalIntegrable (fun x => Φ (tt * S2E.F Jb f r x)) volume 0 (2 * π) :=
    fun r => (hΦc.comp (continuous_const.mul (hFc r))).intervalIntegrable _ _
  have hq : ∀ r, IntervalIntegrable (fun x => 27 / 256 * (tt * S2E.F Jb f r x) ^ 2)
      volume 0 (2 * π) := by
    intro r; have := hFc r
    exact (by fun_prop : Continuous fun x => 27 / 256 * (tt * S2E.F Jb f r x) ^ 2).intervalIntegrable _ _
  have i0 : IntegrableOn (fun r => Jb 0 r ^ 6 * r) (Ioi 0) :=
    (hint 0).congr_fun (fun r _ => by ring) measurableSet_Ioi
  have i4 : IntegrableOn (fun r => Jb 0 r ^ 6
      * avg (fun x => Φ (tt * S2E.F Jb f r x) - 27 / 256 * (tt * S2E.F Jb f r x) ^ 2) * r)
      (Ioi 0) := by
    have hI : IntegrableOn (fun r => Jb 0 r ^ 6 * avg (fun ψ => Φ (tt * S2E.F Jb f r ψ)) * r
        - 27 / 256 * tt ^ 2 * (Jb 0 r ^ 6 * avg (fun ψ => S2E.F Jb f r ψ ^ 2) * r)) (Ioi 0) :=
      idtt.1.sub (hi2.const_mul _)
    refine hI.congr_fun (fun r _ => ?_) measurableSet_Ioi
    dsimp only
    have h1 := avg_sub (hΦ2 r) (hq r)
    have e2 : avg (fun x => 27 / 256 * (tt * S2E.F Jb f r x) ^ 2)
        = 27 / 256 * tt ^ 2 * avg (fun x => S2E.F Jb f r x ^ 2) := by
      rw [← avg_const_mul]; congr 1; funext x; ring
    rw [h1, e2]; ring
  exact Section3.prop_large_mean (J0 := Jb 0) (J2 := Jb 1) (F := S2E.F Jb f) (w := S2E.w Jb f)
    (γ := S2E.γ Jb f) (μ := (1 / (2 * π) ^ 4) * ∫ x, S2P.Ec f x ^ 6) (α0 := S2Q.alpha Jb 0)
    (a0 := a0 f) (a2 := S2E.a2 f) (S := S)
    hser (hcont 0).continuousOn (hcont 1).continuousOn l0 l0'
    hμ (by nlinarith) (Real.sqrt_nonneg _) ha2b hsum hS1 hS2
    (fun r => (hFc r).intervalIntegrable _ _)
    (fun r => ((hFc r).pow 2).intervalIntegrable _ _)
    (fun r => (hΦc.comp ((hFc r).div_const 2)).intervalIntegrable _ _)
    hΦ2
    (fun r => (hwc r).intervalIntegrable _ _)
    (fun r => ((hwc r).pow 2).intervalIntegrable _ _)
    id12.1 hi2 i0 idtt.1 i4
    id12.2 idtt.2
    (fun r _ hJ => S2E.avg_F hf hB hJ)
    hquad
    (by rw [S2Q.alpha]; congr 1; funext r; ring)
    (fun r _ x => by unfold S2E.w; ring)
    (fun r hr => by
      have := (J0_pos hser hr).ne'
      unfold S2E.γ; field_simp)
    (fun r hr => S2E.avg_w hf hB (J0_pos hser hr).ne')
    (fun r hr => S2E.avg_cos_w hf hB (J0_pos hser hr).ne')
    (fun r hr => S2E.tail_L2 hf hanti hB hnorm (J0_pos hser hr).ne' (tail_kappa hdlmf hr))

end

end SteinTomas.S2W

#print axioms SteinTomas.S2W.prop_large_mean_full
