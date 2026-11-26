import Mathlib
import SteinTomasCircle.Section5.SecondVariation
import SteinTomasCircle.Section3.LargeMean

/-!
# Section 5 (IV): Proposition 5.3 and the core of Theorem 1.1 (maximizers are constant)

* `prop_small_mean'`: a nonnegative antipodal normalized maximizer satisfies a₀ > 5/8
* `maximizer_const`: Prop 3.1 (a₀ < 5/8 if nonconstant) contradicts Prop 5.3 ⇒ every normalized nonnegative antipodal maximizer is constant

Here "maximizer" enters through the properties it satisfies (from the literature):
‖Ef‖₆⁶ ≥ ‖Ee₀‖₆⁶ (`hext`), the EL equation (`hEL`), the second variation (`hsv`).
-/

namespace SteinTomas.S5D

open Real MeasureTheory Set Function
open scoped ENNReal

noncomputable section

local notation "μI" => (volume.restrict (Ioc (0 : ℝ) (2 * π)))

variable {f : ℝ → ℝ} {Jb : ℕ → ℝ → ℝ} {ν ρ : ℝ × ℝ → ℝ} {ρr : ℝ → ℝ}

set_option maxHeartbeats 1000000 in
/-- **Proposition 5.3** (prop:small-mean): a₀ > 5/8 -/
theorem prop_small_mean' (hsin : S2C.SinSeries) (hfm : Measurable f) (hf0 : ∀ θ, 0 ≤ f θ)
    (hper : Periodic f (2 * π)) (hanti : ∀ θ, f (θ + π) = f θ) (hf : MemLp f 2 μI)
    (hB1 : ∫ θ in Ioc 0 (2 * π), f θ ^ 2 = 1)
    -- maximality: ‖Ef‖₆⁶ ≥ ‖Ee₀‖₆⁶
    (hext : ∫ x, S2P.Ec S2P.e0 x ^ 6 ≤ ∫ x, S2P.Ec f x ^ 6)
    (hi0 : Integrable (fun x => S2P.Ec S2P.e0 x ^ 6))
    (hi6 : Integrable (fun x => S2P.Ec f x ^ 6))
    (hB : S2E.BesselKernel Jb) (hlit : Section2.AlphaLit (S2Q.alpha Jb))
    -- second variation [GN22]
    (hsv : ∀ g : ℝ → ℝ, MemLp g 2 μI → Periodic g (2 * π) → (∀ θ, g (θ + π) = g θ) →
      ∫⁻ x, ENNReal.ofReal (5 * (S2P.Ec f x ^ 4 * S2P.Ec g x ^ 2))
        ≤ ENNReal.ofReal ((∫ x, S2P.Ec f x ^ 6) * ((∫ θ in Ioc 0 (2 * π), g θ ^ 2)
          + 4 * (∫ θ in Ioc 0 (2 * π), f θ * g θ) ^ 2)))
    -- ν = (fσ)*³ (CO15)
    (hνm : Measurable ν) (hν0 : ∀ y, 0 ≤ ν y)
    (hν : ∀ Ψ : ℝ × ℝ → ℝ≥0∞, Measurable Ψ →
      ∫⁻ y, Ψ y * ENNReal.ofReal (ν y) = ∫⁻ p, Ψ (S4R.ss p) * ENNReal.ofReal (S4R.FF f p) ∂S4R.M3)
    (hνL2 : ∫⁻ x, ENNReal.ofReal (ν x ^ 2)
      = ENNReal.ofReal ((∫ x, S2P.Ec f x ^ 6) / (4 * π ^ 2)))
    -- Plancherel
    (hpl : ∫⁻ x, ENNReal.ofReal (ν x) * S5B.conv (fun θ => ENNReal.ofReal (f θ))
        (fun y => ENNReal.ofReal (S2H.hfun f y)) x
      = ENNReal.ofReal (1 / (4 * π ^ 2) * ∫ x, S2P.Ec f x ^ 4 * (S2HF.hhat f x).re))
    -- ρ = σ*³ (BSWZ12, Becker25)
    (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρd : ∀ Ψ : ℝ × ℝ → ℝ≥0∞, Measurable Ψ →
      ∫⁻ y, Ψ y * ENNReal.ofReal (ρ y) = ∫⁻ p, Ψ (S4R.ss p) ∂S4R.M3)
    (hrad : ∀ y, ρ y = ρr (Real.sqrt (nsq y))) (hρr0 : ∀ r, 0 ≤ ρr r)
    (hρr : ∀ r, 1 < r → r < 3 → ρr r = 4 / Real.sqrt r * S2R.Kl ((r + 1) ^ 3 * (3 - r) / (16 * r)))
    -- magic identity (CFOT17)
    (hmint : Integrable (fun x => (nsq x - 1) * ν x ^ 2))
    (hmagic : (∫ x, S2P.Ec f x ^ 6) = 5 * π ^ 2 * ∫ x, (nsq x - 1) * ν x ^ 2) :
    5 / 8 < S2F.a0 f := by
  have hp := pi_pos
  obtain ⟨E6, hE6⟩ : ∃ E6, E6 = ∫ x, S2P.Ec f x ^ 6 := ⟨_, rfl⟩
  rw [← hE6] at hext hsv hνL2 hmagic
  -- ‖Ef‖₆⁶ > 404π⁴/75
  have he0 := S2W.energy_e0 hB hi0
  have hα := (Section2.bessel_global hlit).1
  have hE : 404 * π ^ 4 / 75 < E6 := by
    have h1 : (2 * π) ^ 4 * (101 / 300) < (2 * π) ^ 4 * S2Q.alpha Jb 0 :=
      mul_lt_mul_of_pos_left hα (by positivity)
    have h2 : 404 * π ^ 4 / 75 = (2 * π) ^ 4 * (101 / 300) := by ring
    linarith
  have hEpos : 0 < E6 := lt_trans (by positivity) hE
  -- Lemma 5.2
  have hsv' := S5C.lemma52 hsin hfm hf0 hper hanti hf hB1 hEpos hE6 hi6 hsv hνm hν0 hνL2 hpl
  -- Prop 5.1
  have hmaster := S4M.master hfm hf0 hper hanti hf hνm hν0 hν
    (by rw [hνL2]; exact ENNReal.ofReal_lt_top) hρm hρ0 hρd hrad hρr0 hρr hmint hmagic
  have hc := S5A.prop_convolution hsin hf rfl rfl hmaster
  rw [hB1] at hc
  simp only [one_pow, mul_one] at hc
  unfold Mconc at hc
  -- a₀ and L
  obtain ⟨L, hL⟩ : ∃ L, L = ∫ θ in Ioc 0 (2 * π), f θ := ⟨_, rfl⟩
  rw [← hL] at hsv' hc
  have hL0 : 0 ≤ L := hL ▸ integral_nonneg hf0
  have ha : S2F.a0 f = 1 / Real.sqrt (2 * π) * L := by
    unfold S2F.a0; rw [intervalIntegral.integral_of_le (by positivity), hL]
  have hne : (2 * π) ≠ 0 := by positivity
  have hL2 : L ^ 2 = 2 * π * S2F.a0 f ^ 2 := by
    rw [ha, mul_pow, div_pow, one_pow, Real.sq_sqrt (by positivity), ← mul_assoc,
      mul_one_div_cancel hne, one_mul]
  have ha0 : 0 ≤ S2F.a0 f := by rw [ha]; exact mul_nonneg (by positivity) hL0
  by_contra hlt
  push_neg at hlt
  have hsq : S2F.a0 f ^ 2 ≤ 25 / 64 := by nlinarith
  have hLb : L ^ 2 ≤ 25 * π / 32 := by rw [hL2]; nlinarith
  have hQ0 : 0 ≤ S2C.Qa (fun θ => f θ ^ 2) :=
    (S2C.Q_bounds' hsin hf.integrable_sq (fun x => sq_nonneg _)).1
  exact Chains.small_mean hE hLb hQ0 hsv' hc

/-- **Core of Theorem 1.1**: every normalized nonnegative antipodal maximizer is (a.e.) constant -/
theorem maximizer_const (hsin : S2C.SinSeries) (hfm : Measurable f) (hf0 : ∀ θ, 0 ≤ f θ)
    (hper : Periodic f (2 * π)) (hanti : ∀ θ, f (θ + π) = f θ) (hf : MemLp f 2 μI)
    (hB1 : ∫ θ in Ioc 0 (2 * π), f θ ^ 2 = 1)
    (hext : ∫ x, S2P.Ec S2P.e0 x ^ 6 ≤ ∫ x, S2P.Ec f x ^ 6)
    -- external inputs from Section 3
    (hi0 : Integrable (fun x => S2P.Ec S2P.e0 x ^ 6))
    (hi5 : Integrable (fun x => S2P.Ec f x ^ 5 * S2P.Ec S2P.e0 x))
    (hi6 : Integrable (fun x => S2P.Ec f x ^ 6))
    (hEL : ∫ x, S2P.Ec f x ^ 5 * S2P.Ec S2P.e0 x = (∫ x, S2P.Ec f x ^ 6) * S2F.a0 f)
    (hB : S2E.BesselKernel Jb) (hcont : ∀ n, Continuous (Jb n))
    (hz : volume {r : ℝ | 0 < r ∧ Jb 0 r = 0} = 0)
    (hser : Lemma21.SeriesHyp (Jb 0) (Jb 1))
    (hdlmf : ∀ (k : ℕ) (r : ℝ), 0 ≤ r → |Jb k r| ≤ (r / 2) ^ (2 * k) / ((2 * k).factorial : ℝ))
    (hint : ∀ n, IntegrableOn (fun r => Jb 0 r ^ 4 * Jb n r ^ 2 * r) (Ioi 0))
    (hlit : Section2.AlphaLit (S2Q.alpha Jb))
    -- external inputs from Sections 4 and 5
    (hsv : ∀ g : ℝ → ℝ, MemLp g 2 μI → Periodic g (2 * π) → (∀ θ, g (θ + π) = g θ) →
      ∫⁻ x, ENNReal.ofReal (5 * (S2P.Ec f x ^ 4 * S2P.Ec g x ^ 2))
        ≤ ENNReal.ofReal ((∫ x, S2P.Ec f x ^ 6) * ((∫ θ in Ioc 0 (2 * π), g θ ^ 2)
          + 4 * (∫ θ in Ioc 0 (2 * π), f θ * g θ) ^ 2)))
    (hνm : Measurable ν) (hν0 : ∀ y, 0 ≤ ν y)
    (hν : ∀ Ψ : ℝ × ℝ → ℝ≥0∞, Measurable Ψ →
      ∫⁻ y, Ψ y * ENNReal.ofReal (ν y) = ∫⁻ p, Ψ (S4R.ss p) * ENNReal.ofReal (S4R.FF f p) ∂S4R.M3)
    (hνL2 : ∫⁻ x, ENNReal.ofReal (ν x ^ 2)
      = ENNReal.ofReal ((∫ x, S2P.Ec f x ^ 6) / (4 * π ^ 2)))
    (hpl : ∫⁻ x, ENNReal.ofReal (ν x) * S5B.conv (fun θ => ENNReal.ofReal (f θ))
        (fun y => ENNReal.ofReal (S2H.hfun f y)) x
      = ENNReal.ofReal (1 / (4 * π ^ 2) * ∫ x, S2P.Ec f x ^ 4 * (S2HF.hhat f x).re))
    (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρd : ∀ Ψ : ℝ × ℝ → ℝ≥0∞, Measurable Ψ →
      ∫⁻ y, Ψ y * ENNReal.ofReal (ρ y) = ∫⁻ p, Ψ (S4R.ss p) ∂S4R.M3)
    (hrad : ∀ y, ρ y = ρr (Real.sqrt (nsq y))) (hρr0 : ∀ r, 0 ≤ ρr r)
    (hρr : ∀ r, 1 < r → r < 3 → ρr r = 4 / Real.sqrt r * S2R.Kl ((r + 1) ^ 3 * (3 - r) / (16 * r)))
    (hmint : Integrable (fun x => (nsq x - 1) * ν x ^ 2))
    (hmagic : (∫ x, S2P.Ec f x ^ 6) = 5 * π ^ 2 * ∫ x, (nsq x - 1) * ν x ^ 2) :
    ∃ c : ℝ, ∀ᵐ θ ∂μI, f θ = c := by
  by_contra hnc
  rw [not_exists] at hnc
  have hnorm : ∫ θ in (0 : ℝ)..(2 * π), f θ ^ 2 = 1 := by
    rw [intervalIntegral.integral_of_le (by positivity)]; exact hB1
  have h1 := S2W.prop_large_mean_full hf hf0 hanti hnorm hnc hext hi0 hi5 hi6 hEL hB hcont hz
    hser hdlmf hint hlit
  have h2 := prop_small_mean' hsin hfm hf0 hper hanti hf hB1 hext hi0 hi6 hB hlit hsv hνm hν0 hν
    hνL2 hpl hρm hρ0 hρd hrad hρr0 hρr hmint hmagic
  linarith

end

end SteinTomas.S5D

#print axioms SteinTomas.S5D.prop_small_mean'
#print axioms SteinTomas.S5D.maximizer_const
