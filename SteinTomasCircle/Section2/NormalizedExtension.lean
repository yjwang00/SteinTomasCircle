import Mathlib
import SteinTomasCircle.Basic.Elementary
import SteinTomasCircle.Section2.FourierSeries
import SteinTomasCircle.Section2.PolarKernel
import SteinTomasCircle.Section2.BesselGlobal

/-!
# Section 2 (§2.1): eq:normalized-extension and its consequences

For real-valued antipodal f with ‖f‖₂ = 1:
* `G f r ψ` = Ef(r, (ψ−β)/2), β = arg(−f̂(2)) (this is the rotation making f̂(2) = −|f̂(2)| in the paper,
  with ψ = 2φ as angular variable)
* `F f r ψ` = G/(√(2π)J₀(r)) (eq:normalized-extension)
* `γ f r` = √2·t·a₂·J₂(r)/J₀(r), `w f r ψ` = tF − ta₀ − γ cos ψ
* Proved: avg F = a₀; avg w = 0; avg(cos ψ·w) = 0 (eq:prop31-b);
  avg F² = (a₀²J₀² + Σ_{n≥1} a_{2n}²J_{2n}²)/J₀² (angular part of eq:quadratic-spectral);
  eq:tail-L2; eq:a2-bound (a₂² ≤ 1/2, needs f ≥ 0).

The only external input is `BesselKernel`: κ_{2m}(r) = (−1)^m J_{2|m|}(r) (DLMF 10.9.2 and 10.4.1,
i.e. the Jacobi–Anger expansion cos(r cos u) = Σ_m (−1)^m J_{2m}(r) e^{2imu}).
-/

namespace SteinTomas.S2E

open Real MeasureTheory Complex SteinTomas.S2F SteinTomas.S2K SteinTomas.Section2

noncomputable section

/-- External input (DLMF 10.9.2, 10.4.1). `Jb k r` = J_{2k}(r). -/
structure BesselKernel (Jb : ℕ → ℝ → ℝ) : Prop where
  kc_even : ∀ (r : ℝ) (m : ℤ), kc r (2 * m) = (((-1 : ℝ) ^ m.natAbs * Jb m.natAbs r : ℝ) : ℂ)

/-! ## Periodicity and change of variables -/

lemma Ep_periodic (f : ℝ → ℝ) (r φ : ℝ) : Ep f r (φ + π) = Ep f r φ := by
  simp only [Ep]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  rw [show θ - (φ + π) = (θ - φ) - π by ring, Real.cos_sub_pi, mul_neg, Real.cos_neg]

/-- If H has period π, the k-th coefficient of ψ ↦ H((ψ−β)/2) is e^{−ikβ}·Ĥ(2k) -/
lemma coef_half {H : ℝ → ℝ} (hH : Continuous H) (hper : ∀ φ, H (φ + π) = H φ) (β : ℝ) (k : ℤ) :
    coef (fun ψ => H ((ψ - β) / 2)) k = Complex.exp (-(k : ℂ) * β * I) * coef H (2 * k) := by
  rw [coef_eq, coef_eq]
  set u : ℝ → ℂ := fun φ => Complex.exp (-((2 * k : ℤ) : ℂ) * φ * I) * ((H φ : ℝ) : ℂ) with hu
  have hucont : Continuous u := by simp only [hu]; fun_prop
  have huper : Function.Periodic u π := by
    intro φ
    simp only [hu, hper φ]
    have e : -((2 * k : ℤ) : ℂ) * ((φ + π : ℝ) : ℂ) * I
        = -((2 * k : ℤ) : ℂ) * (φ : ℂ) * I + ((-k : ℤ) : ℂ) * (2 * π * I) := by push_cast; ring
    rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hfull : ∫ φ in (0 : ℝ)..(2 * π), u φ = 2 * ∫ φ in (0 : ℝ)..π, u φ := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hucont.intervalIntegrable (μ := volume) 0 π) (hucont.intervalIntegrable (μ := volume) π (2 * π))
    have h2 := huper.intervalIntegral_add_eq π 0
    rw [zero_add, show π + π = 2 * π by ring] at h2
    rw [← h1, h2]; ring
  set g : ℝ → ℂ := fun ψ => Complex.exp (-(k : ℂ) * ψ * I) * ((H ((ψ - β) / 2) : ℝ) : ℂ) with hg
  have hsub := intervalIntegral.integral_comp_mul_add (f := g) (a := -β / 2) (b := π - β / 2)
    (c := (2 : ℝ)) (by norm_num) β
  rw [show 2 * (-β / 2) + β = 0 by ring, show 2 * (π - β / 2) + β = 2 * π by ring] at hsub
  have hgu : ∀ φ : ℝ, g (2 * φ + β) = Complex.exp (-(k : ℂ) * β * I) * u φ := by
    intro φ
    simp only [hg, hu]
    rw [show (2 * φ + β - β) / 2 = φ by ring, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  simp_rw [hgu] at hsub
  rw [intervalIntegral.integral_const_mul] at hsub
  have hshift := huper.intervalIntegral_add_eq (-β / 2) 0
  rw [zero_add, show -β / 2 + π = π - β / 2 by ring] at hshift
  rw [hshift, Complex.real_smul] at hsub
  have hgint : ∫ ψ in (0 : ℝ)..(2 * π), g ψ
      = 2 * (Complex.exp (-(k : ℂ) * β * I) * ∫ φ in (0 : ℝ)..π, u φ) := by
    push_cast at hsub
    linear_combination (-2 : ℂ) * hsub
  rw [hgint, hfull]
  ring

/-! ## Definitions -/

/-- Phase β = arg(−f̂(2)) -/
def β (f : ℝ → ℝ) : ℝ := Complex.arg (-coef f 2)

/-- Ef in the variable ψ: G(r,ψ) = Ef(r,(ψ−β)/2) -/
def G (f : ℝ → ℝ) (r ψ : ℝ) : ℝ := Ep f r ((ψ - β f) / 2)

/-- a₂ = √(a₂²) -/
def a2 (f : ℝ → ℝ) : ℝ := Real.sqrt (asq f 0)

/-- eq:normalized-extension -/
def F (Jb : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (r ψ : ℝ) : ℝ := G f r ψ / (Real.sqrt (2 * π) * Jb 0 r)

/-- γ(r) = √2·t·a₂·J₂(r)/J₀(r) -/
def γ (Jb : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (r : ℝ) : ℝ := Real.sqrt 2 * tt * a2 f * Jb 1 r / Jb 0 r

/-- Higher-order part w = tF − ta₀ − γ cos ψ -/
def w (Jb : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (r ψ : ℝ) : ℝ :=
  tt * F Jb f r ψ - tt * a0 f - γ Jb f r * Real.cos ψ

variable {f : ℝ → ℝ} {Jb : ℕ → ℝ → ℝ}

lemma G_cont (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) (r : ℝ) :
    Continuous (G f r) := by
  unfold G
  exact (Ep_continuous hf r).comp (by fun_prop)

lemma G_memLp (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) (r : ℝ) :
    MemLp (G f r) 2 (volume.restrict (Set.Ioc 0 (2 * π))) := by
  have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  exact MemLp.of_bound (G_cont hf r).aestronglyMeasurable _
    (Filter.Eventually.of_forall (fun ψ => Ep_bound hf r _))

lemma F_cont (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) (r : ℝ) :
    Continuous (F Jb f r) := by
  unfold F; exact (G_cont hf r).div_const _

lemma w_cont (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) (r : ℝ) :
    Continuous (w Jb f r) := by
  unfold w; have := F_cont (Jb := Jb) hf r; fun_prop

/-- Coefficients of G -/
theorem coef_G (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) (r : ℝ) (k : ℤ) :
    coef (G f r) k
      = Complex.exp (-(k : ℂ) * (β f) * I) * (2 * π * coef f (2 * k) * kc r (-(2 * k))) := by
  have h := coef_half (Ep_continuous hf r) (Ep_periodic f r) (β f) k
  rw [coef_Ep hf r] at h
  exact h

lemma norm_coef_neg (f : ℝ → ℝ) (n : ℤ) : ‖coef f (-n)‖ = ‖coef f n‖ := by
  rw [coef_neg, Complex.norm_conj]

lemma asq_zero (f : ℝ → ℝ) : asq f 0 = 4 * π * ‖coef f 2‖ ^ 2 := by
  simp only [asq]
  have : ((2 * (0 + 1) : ℕ) : ℤ) = 2 := by norm_num
  rw [this, norm_coef_neg]
  ring

lemma a2_eq (f : ℝ → ℝ) : a2 f = 2 * Real.sqrt π * ‖coef f 2‖ := by
  rw [a2, asq_zero]
  rw [show 4 * π * ‖coef f 2‖ ^ 2 = (2 * Real.sqrt π * ‖coef f 2‖) ^ 2 by
    rw [mul_pow, mul_pow, Real.sq_sqrt pi_pos.le]; ring]
  exact Real.sqrt_sq (by positivity)

/-! ## avg G and avg(cos ψ·G) -/

lemma avg_eq_coef0 (g : ℝ → ℝ) : ((avg g : ℝ) : ℂ) = coef g 0 := by
  rw [coef_zero, avg]

theorem avg_G (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) (hB : BesselKernel Jb)
    (r : ℝ) : avg (G f r) = Real.sqrt (2 * π) * a0 f * Jb 0 r := by
  have h := coef_G hf r 0
  rw [← avg_eq_coef0] at h
  have hk : kc r (-(2 * (0 : ℤ))) = ((Jb 0 r : ℝ) : ℂ) := by
    rw [show -(2 * (0 : ℤ)) = 2 * 0 by norm_num, hB.kc_even]; simp
  rw [hk, show (2 : ℤ) * 0 = 0 by norm_num, coef_zero] at h
  simp only [Int.cast_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul] at h
  have h2 : avg (G f r) = 2 * π * ((1 / (2 * π)) * ∫ θ in (0 : ℝ)..(2 * π), f θ) * Jb 0 r := by
    exact_mod_cast h
  rw [h2, a0]
  have hs : Real.sqrt (2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  have hs0 : Real.sqrt (2 * π) ≠ 0 := by positivity
  field_simp

/-- avg(cos ψ·G) = Re Ĝ(1) -/
lemma avg_cos_eq_re (g : ℝ → ℝ) (hg : Continuous g) :
    avg (fun ψ => Real.cos ψ * g ψ) = (coef g 1).re := by
  rw [coef_eq, avg]
  rw [show (((1 / (2 * π) : ℝ) : ℂ) * ∫ θ in (0 : ℝ)..(2 * π),
      Complex.exp (-((1 : ℤ) : ℂ) * θ * I) * ((g θ : ℝ) : ℂ)).re
      = (1 / (2 * π)) * (∫ θ in (0 : ℝ)..(2 * π),
      Complex.exp (-((1 : ℤ) : ℂ) * θ * I) * ((g θ : ℝ) : ℂ)).re by
    rw [Complex.re_ofReal_mul]]
  congr 1
  rw [intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_of_le (by positivity)]
  have hint : Integrable (fun θ : ℝ => Complex.exp (-((1 : ℤ) : ℂ) * θ * I) * ((g θ : ℝ) : ℂ))
      (volume.restrict (Set.Ioc 0 (2 * π))) := Continuous.integrableOn_Ioc (by fun_prop)
  have key := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply] at key
  rw [← key]
  apply integral_congr_ae
  filter_upwards with θ
  have : -((1 : ℤ) : ℂ) * (θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

theorem avg_cos_G (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) (hB : BesselKernel Jb)
    (r : ℝ) : avg (fun ψ => Real.cos ψ * G f r ψ) = Real.sqrt π * a2 f * Jb 1 r := by
  rw [avg_cos_eq_re _ (G_cont hf r), coef_G hf r 1]
  have hk : kc r (-(2 * (1 : ℤ))) = ((-Jb 1 r : ℝ) : ℂ) := by
    rw [show -(2 * (1 : ℤ)) = 2 * (-1) by norm_num, hB.kc_even]; simp
  rw [hk]
  have hc : -coef f 2 = ((‖coef f 2‖ : ℝ) : ℂ) * Complex.exp ((β f : ℂ) * I) := by
    have := Complex.norm_mul_exp_arg_mul_I (-coef f 2)
    rw [norm_neg] at this
    rw [← this]; rfl
  have e : Complex.exp (-((1 : ℤ) : ℂ) * (β f : ℂ) * I)
      * (2 * π * coef f (2 * (1 : ℤ)) * ((-Jb 1 r : ℝ) : ℂ))
      = ((2 * π * Jb 1 r * ‖coef f 2‖ : ℝ) : ℂ) := by
    have h2 : coef f (2 * (1 : ℤ)) = -(((‖coef f 2‖ : ℝ) : ℂ) * Complex.exp ((β f : ℂ) * I)) := by
      rw [← hc]; norm_num
    rw [h2]
    have hexp : Complex.exp (-((1 : ℤ) : ℂ) * (β f : ℂ) * I) * Complex.exp ((β f : ℂ) * I) = 1 := by
      rw [← Complex.exp_add]; push_cast; ring_nf; exact Complex.exp_zero
    push_cast at hexp ⊢
    linear_combination (2 * π * Jb 1 r * ‖coef f 2‖ : ℂ) * hexp
  rw [e, Complex.ofReal_re, a2_eq]
  have hs : Real.sqrt π ^ 2 = π := Real.sq_sqrt pi_pos.le
  have e2 : Real.sqrt π * (2 * Real.sqrt π * ‖coef f 2‖) * Jb 1 r
      = 2 * Real.sqrt π ^ 2 * ‖coef f 2‖ * Jb 1 r := by ring
  rw [e2, hs]; ring

/-! ## Parseval: avg G² -/

theorem parseval_G (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) (hB : BesselKernel Jb)
    (r : ℝ) :
    HasSum (fun k : ℤ => 4 * π ^ 2 * ‖coef f (2 * k)‖ ^ 2 * Jb k.natAbs r ^ 2)
      (avg (fun ψ => G f r ψ ^ 2)) := by
  have h := parseval (G_memLp hf r)
  have e : ∀ k : ℤ, ‖coef (G f r) k‖ ^ 2 = 4 * π ^ 2 * ‖coef f (2 * k)‖ ^ 2 * Jb k.natAbs r ^ 2 := by
    intro k
    have h1 : ‖Complex.exp (-(k : ℂ) * (β f : ℂ) * I)‖ = 1 := by
      have : -(k : ℂ) * (β f : ℂ) * I = ((-(k : ℝ) * β f : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [coef_G hf r k, show -(2 * k) = 2 * (-k) by ring, hB.kc_even, norm_mul, h1, one_mul,
      Int.natAbs_neg]
    have h4 : ‖2 * (π : ℂ) * coef f (2 * k) * (((-1 : ℝ) ^ k.natAbs * Jb k.natAbs r : ℝ) : ℂ)‖
        = 2 * π * ‖coef f (2 * k)‖ * |Jb k.natAbs r| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_pos pi_pos]
      norm_num
    rw [h4, mul_pow, mul_pow, mul_pow, sq_abs]
    ring
  simp_rw [e] at h
  simpa [avg] using h

/-- eq:quadratic-spectral (angular part): avg G² = 2π(a₀²J₀² + Σ_{n≥1} a_{2n}² J_{2n}²) -/
theorem avg_G_sq (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π))))
    (hanti : ∀ θ, f (θ + π) = f θ) (hB : BesselKernel Jb) (r : ℝ) :
    HasSum (fun n : ℕ => asq f n * Jb (n + 1) r ^ 2)
      (avg (fun ψ => G f r ψ ^ 2) / (2 * π) - a0 f ^ 2 * Jb 0 r ^ 2) := by
  have hP := (parseval_G hf hB r).nat_add_neg
  have hE1 := (hasSum_nat_add_iff' 1).mpr hP
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, neg_zero,
    Int.natAbs_zero] at hE1
  have hmul := hE1.mul_left (1 / (2 * π))
  have hp : (0 : ℝ) < 2 * π := by positivity
  convert hmul using 1
  · funext n
    simp only [asq]
    have h1 : ((n + 1 : ℕ) : ℤ).natAbs = n + 1 := rfl
    have h2 : (-((n + 1 : ℕ) : ℤ)).natAbs = n + 1 := by rw [Int.natAbs_neg]; rfl
    rw [h1, h2]
    push_cast
    field_simp
    ring_nf
  · rw [a0_sq]
    field_simp
    ring

/-! ## Consequences of eq:normalized-extension -/

theorem avg_F (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) (hB : BesselKernel Jb)
    {r : ℝ} (hJ : Jb 0 r ≠ 0) : avg (F Jb f r) = a0 f := by
  have hs : Real.sqrt (2 * π) ≠ 0 := by positivity
  unfold F
  have e : (fun ψ => G f r ψ / (Real.sqrt (2 * π) * Jb 0 r))
      = fun ψ => (1 / (Real.sqrt (2 * π) * Jb 0 r)) * G f r ψ := by funext ψ; ring
  rw [e, avg_const_mul, avg_G hf hB r]
  field_simp

theorem avg_cos_F (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) (hB : BesselKernel Jb)
    {r : ℝ} (hJ : Jb 0 r ≠ 0) :
    avg (fun ψ => Real.cos ψ * F Jb f r ψ) = γ Jb f r / (2 * tt) := by
  have hs : Real.sqrt (2 * π) ≠ 0 := by positivity
  have htt : tt ≠ 0 := by unfold tt; norm_num
  unfold F
  have e : (fun ψ => Real.cos ψ * (G f r ψ / (Real.sqrt (2 * π) * Jb 0 r)))
      = fun ψ => (1 / (Real.sqrt (2 * π) * Jb 0 r)) * (Real.cos ψ * G f r ψ) := by funext ψ; ring
  rw [e, avg_const_mul, avg_cos_G hf hB r, γ]
  have h2 : Real.sqrt (2 * π) = Real.sqrt 2 * Real.sqrt π := by
    rw [Real.sqrt_mul (by norm_num)]
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2' : Real.sqrt 2 ≠ 0 := by positivity
  rw [h2]
  field_simp
  rw [hs2]
  ring

lemma avg_cos_sq : avg (fun ψ => Real.cos ψ ^ 2) = 1 / 2 := by
  unfold avg; rw [mom2]; field_simp

/-- eq:prop31-b: avg w = 0 -/
theorem avg_w (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) (hB : BesselKernel Jb)
    {r : ℝ} (hJ : Jb 0 r ≠ 0) : avg (w Jb f r) = 0 := by
  have hF := F_cont (Jb := Jb) hf r
  unfold w
  have i1 : IntervalIntegrable (fun ψ => tt * F Jb f r ψ - tt * a0 f) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun ψ => tt * F Jb f r ψ - tt * a0 f).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun ψ => γ Jb f r * Real.cos ψ) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun ψ => γ Jb f r * Real.cos ψ).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun ψ => tt * F Jb f r ψ) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun ψ => tt * F Jb f r ψ).intervalIntegrable _ _
  have i4 : IntervalIntegrable (fun _ : ℝ => tt * a0 f) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun _ : ℝ => tt * a0 f).intervalIntegrable _ _
  rw [avg_sub i1 i2, avg_sub i3 i4, avg_const_mul, avg_const_mul, avg_const, avg_const_mul,
    avg_F hf hB hJ, avg_cos]
  ring

/-- eq:prop31-b: avg(cos ψ·w) = 0 -/
theorem avg_cos_w (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) (hB : BesselKernel Jb)
    {r : ℝ} (hJ : Jb 0 r ≠ 0) : avg (fun ψ => Real.cos ψ * w Jb f r ψ) = 0 := by
  have hF := F_cont (Jb := Jb) hf r
  have htt : tt ≠ 0 := by unfold tt; norm_num
  have e : (fun ψ => Real.cos ψ * w Jb f r ψ)
      = fun ψ => (tt * (Real.cos ψ * F Jb f r ψ) - (tt * a0 f) * Real.cos ψ)
        - γ Jb f r * Real.cos ψ ^ 2 := by
    funext ψ; unfold w; ring
  have i1 : IntervalIntegrable (fun ψ => tt * (Real.cos ψ * F Jb f r ψ) - (tt * a0 f) * Real.cos ψ)
      volume 0 (2 * π) := (by fun_prop : Continuous fun ψ =>
        tt * (Real.cos ψ * F Jb f r ψ) - (tt * a0 f) * Real.cos ψ).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun ψ => γ Jb f r * Real.cos ψ ^ 2) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun ψ => γ Jb f r * Real.cos ψ ^ 2).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun ψ => tt * (Real.cos ψ * F Jb f r ψ)) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun ψ => tt * (Real.cos ψ * F Jb f r ψ)).intervalIntegrable _ _
  have i4 : IntervalIntegrable (fun ψ => (tt * a0 f) * Real.cos ψ) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun ψ => (tt * a0 f) * Real.cos ψ).intervalIntegrable _ _
  rw [e, avg_sub i1 i2, avg_sub i3 i4, avg_const_mul, avg_const_mul, avg_const_mul,
    avg_cos_F hf hB hJ, avg_cos, avg_cos_sq]
  field_simp
  ring

/-- avg F² -/
theorem avg_F_sq (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) {r : ℝ} (hJ : Jb 0 r ≠ 0) :
    avg (fun ψ => F Jb f r ψ ^ 2) = avg (fun ψ => G f r ψ ^ 2) / (2 * π * Jb 0 r ^ 2) := by
  unfold F
  have hs : Real.sqrt (2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  have e : (fun ψ => (G f r ψ / (Real.sqrt (2 * π) * Jb 0 r)) ^ 2)
      = fun ψ => (1 / (2 * π * Jb 0 r ^ 2)) * G f r ψ ^ 2 := by
    funext ψ
    rw [div_pow, mul_pow, hs]; ring
  rw [e, avg_const_mul]; ring

/-- eq:tail-L2: avg w² · J₀² ≤ t²(1 − a₀² − a₂²)κ², if |J_{2n}(r)| ≤ κ (n ≥ 2) and ‖f‖₂ = 1 -/
theorem tail_L2 (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π))))
    (hanti : ∀ θ, f (θ + π) = f θ) (hB : BesselKernel Jb) (hnorm : ∫ θ in (0 : ℝ)..(2 * π), f θ ^ 2 = 1)
    {r κ : ℝ} (hJ : Jb 0 r ≠ 0) (hκ : ∀ n : ℕ, |Jb (n + 2) r| ≤ κ) :
    avg (fun ψ => w Jb f r ψ ^ 2) * Jb 0 r ^ 2
      ≤ tt ^ 2 * (1 - a0 f ^ 2 - a2 f ^ 2) * κ ^ 2 := by
  have hF := F_cont (Jb := Jb) hf r
  have htt : tt ≠ 0 := by unfold tt; norm_num
  set b := γ Jb f r / tt with hb
  -- expand w²
  have e : (fun ψ => w Jb f r ψ ^ 2)
      = fun ψ => ((((tt ^ 2 * F Jb f r ψ ^ 2 + (-2 * tt ^ 2 * a0 f) * F Jb f r ψ)
          + (-2 * tt * γ Jb f r) * (Real.cos ψ * F Jb f r ψ)) + (tt * a0 f) ^ 2)
          + (2 * tt * a0 f * γ Jb f r) * Real.cos ψ) + γ Jb f r ^ 2 * Real.cos ψ ^ 2 := by
    funext ψ; unfold w; ring
  have c1 : Continuous fun ψ => tt ^ 2 * F Jb f r ψ ^ 2 := by fun_prop
  have c2 : Continuous fun ψ => (-2 * tt ^ 2 * a0 f) * F Jb f r ψ := by fun_prop
  have c3 : Continuous fun ψ => (-2 * tt * γ Jb f r) * (Real.cos ψ * F Jb f r ψ) := by fun_prop
  have c4 : Continuous fun _ : ℝ => (tt * a0 f) ^ 2 := by fun_prop
  have c5 : Continuous fun ψ => (2 * tt * a0 f * γ Jb f r) * Real.cos ψ := by fun_prop
  have c6 : Continuous fun ψ => γ Jb f r ^ 2 * Real.cos ψ ^ 2 := by fun_prop
  have i12 : IntervalIntegrable (fun ψ => tt ^ 2 * F Jb f r ψ ^ 2
      + (-2 * tt ^ 2 * a0 f) * F Jb f r ψ) volume 0 (2 * π) :=
    (c1.add c2).intervalIntegrable _ _
  have i123 : IntervalIntegrable (fun ψ => tt ^ 2 * F Jb f r ψ ^ 2
      + (-2 * tt ^ 2 * a0 f) * F Jb f r ψ
      + (-2 * tt * γ Jb f r) * (Real.cos ψ * F Jb f r ψ)) volume 0 (2 * π) :=
    ((c1.add c2).add c3).intervalIntegrable _ _
  have i1234 : IntervalIntegrable (fun ψ => tt ^ 2 * F Jb f r ψ ^ 2
      + (-2 * tt ^ 2 * a0 f) * F Jb f r ψ
      + (-2 * tt * γ Jb f r) * (Real.cos ψ * F Jb f r ψ) + (tt * a0 f) ^ 2) volume 0 (2 * π) :=
    (((c1.add c2).add c3).add c4).intervalIntegrable _ _
  have i12345 : IntervalIntegrable (fun ψ => tt ^ 2 * F Jb f r ψ ^ 2
      + (-2 * tt ^ 2 * a0 f) * F Jb f r ψ
      + (-2 * tt * γ Jb f r) * (Real.cos ψ * F Jb f r ψ) + (tt * a0 f) ^ 2
      + (2 * tt * a0 f * γ Jb f r) * Real.cos ψ) volume 0 (2 * π) :=
    ((((c1.add c2).add c3).add c4).add c5).intervalIntegrable _ _
  rw [e, avg_add i12345 (c6.intervalIntegrable _ _), avg_add i1234 (c5.intervalIntegrable _ _),
    avg_add i123 (c4.intervalIntegrable _ _), avg_add i12 (c3.intervalIntegrable _ _),
    avg_add (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _),
    avg_const_mul, avg_const_mul, avg_const_mul, avg_const, avg_const_mul, avg_const_mul,
    avg_F hf hB hJ, avg_cos_F hf hB hJ, avg_cos, avg_cos_sq, avg_F_sq hf hJ]
  -- Parseval expression for avg G²
  have hS := avg_G_sq hf hanti hB r
  have hS1 := (hasSum_nat_add_iff' 1).mpr hS
  simp only [Finset.range_one, Finset.sum_singleton] at hS1
  -- tail ≤ κ²·Σ_{n≥1} a_{2n}²
  have hpar := (hasSum_nat_add_iff' 1).mpr (parseval_even hf hanti)
  simp only [Finset.range_one, Finset.sum_singleton] at hpar
  have hle : ∀ n, asq f (n + 1) * Jb (n + 1 + 1) r ^ 2 ≤ κ ^ 2 * asq f (n + 1) := by
    intro n
    have ha : 0 ≤ asq f (n + 1) := by unfold asq; positivity
    have hk := hκ n
    have : Jb (n + 1 + 1) r ^ 2 ≤ κ ^ 2 := by
      rw [show n + 1 + 1 = n + 2 by ring, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hk 2
    nlinarith
  have hcmp := hasSum_le hle hS1 (hpar.mul_left (κ ^ 2))
  rw [hnorm] at hcmp
  have ha2 : a2 f ^ 2 = asq f 0 := by
    rw [a2, Real.sq_sqrt (by unfold asq; positivity)]
  have hγ : γ Jb f r ^ 2 = 2 * tt ^ 2 * asq f 0 * Jb 1 r ^ 2 / Jb 0 r ^ 2 := by
    rw [γ, div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num), ha2]
  have hJ2 : 0 < Jb 0 r ^ 2 := by positivity
  have hp : (0 : ℝ) < 2 * π := by positivity
  rw [ha2]
  have key : (tt ^ 2 * (avg (fun ψ => G f r ψ ^ 2) / (2 * π * Jb 0 r ^ 2))
      + -2 * tt ^ 2 * a0 f * a0 f + -2 * tt * γ Jb f r * (γ Jb f r / (2 * tt)) + (tt * a0 f) ^ 2
      + 2 * tt * a0 f * γ Jb f r * 0 + γ Jb f r ^ 2 * (1 / 2)) * Jb 0 r ^ 2
      = tt ^ 2 * (avg (fun ψ => G f r ψ ^ 2) / (2 * π) - a0 f ^ 2 * Jb 0 r ^ 2
        - asq f 0 * Jb (0 + 1) r ^ 2) := by
    have hγ2 : γ Jb f r ^ 2 * Jb 0 r ^ 2 = 2 * tt ^ 2 * asq f 0 * Jb 1 r ^ 2 := by
      rw [hγ]; field_simp
    rw [hγ]; field_simp
    linear_combination (-2 * π) * hγ2
  rw [key]
  have := mul_le_mul_of_nonneg_left hcmp (sq_nonneg tt)
  nlinarith [this]

/-! ## eq:a2-bound (needs f ≥ 0) -/

/-- ∫₀^{2π} (−cos(2θ+β))₊² dθ = π/2 -/
lemma int_pos_part_sq (β : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * π), (max (-Real.cos (2 * θ + β)) 0) ^ 2 = π / 2 := by
  set h : ℝ → ℝ := fun θ => (max (-Real.cos (2 * θ + β)) 0) ^ 2 with hh
  set h' : ℝ → ℝ := fun θ => (max (Real.cos (2 * θ + β)) 0) ^ 2 with hh'
  have hc : Continuous h := by simp only [hh]; fun_prop
  have hc' : Continuous h' := by simp only [hh']; fun_prop
  -- h(θ + π/2) = h'(θ)
  have hshift : ∀ θ, h (θ + π / 2) = h' θ := by
    intro θ
    simp only [hh, hh']
    rw [show 2 * (θ + π / 2) + β = (2 * θ + β) + π by ring, Real.cos_add_pi, neg_neg]
  have hper : Function.Periodic h (2 * π) := by
    intro θ; simp only [hh]
    rw [show 2 * (θ + 2 * π) + β = (2 * θ + β) + 2 * π * 2 by ring]
    have : Real.cos ((2 * θ + β) + 2 * π * 2) = Real.cos (2 * θ + β) := by
      rw [show (2 * θ + β) + 2 * π * 2 = (2 * θ + β) + ((2 : ℕ) : ℝ) * (2 * π) by push_cast; ring,
        Real.cos_add_nat_mul_two_pi]
    rw [this]
  have heq : ∫ θ in (0 : ℝ)..(2 * π), h θ = ∫ θ in (0 : ℝ)..(2 * π), h' θ := by
    have h1 := intervalIntegral.integral_comp_add_right (f := h) (a := 0) (b := 2 * π) (π / 2)
    simp_rw [hshift] at h1
    rw [zero_add, show 2 * π + π / 2 = π / 2 + 2 * π by ring,
      hper.intervalIntegral_add_eq (π / 2) 0, zero_add] at h1
    exact h1.symm
  -- h + h' = cos²(2θ+β)
  have hsum : ∀ θ, h θ + h' θ = Real.cos (2 * θ + β) ^ 2 := by
    intro θ
    simp only [hh, hh']
    rcases le_total (Real.cos (2 * θ + β)) 0 with hle | hle
    · rw [max_eq_left (by linarith), max_eq_right hle]; ring
    · rw [max_eq_right (by linarith), max_eq_left hle]; ring
  have htot : ∫ θ in (0 : ℝ)..(2 * π), Real.cos (2 * θ + β) ^ 2 = π := by
    have e : ∀ θ, Real.cos (2 * θ + β) ^ 2 = 1 / 2 + Real.cos (4 * θ + 2 * β) / 2 := by
      intro θ
      rw [show 4 * θ + 2 * β = 2 * (2 * θ + β) by ring, Real.cos_two_mul]; ring
    have hc1 : ∫ θ in (0 : ℝ)..(2 * π), Real.cos (4 * θ + 2 * β) = 0 := by
      have h4 := intervalIntegral.integral_comp_mul_add (f := Real.cos) (a := 0) (b := 2 * π)
        (c := (4 : ℝ)) (by norm_num) (2 * β)
      rw [h4, integral_cos, mul_zero, zero_add,
        show (4 : ℝ) * (2 * π) + 2 * β = 2 * β + ((4 : ℕ) : ℝ) * (2 * π) by push_cast; ring,
        Real.sin_add_nat_mul_two_pi, sub_self, smul_zero]
    have hi1 : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ)) volume 0 (2 * π) :=
      (by fun_prop : Continuous fun _ : ℝ => (1 / 2 : ℝ)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun θ : ℝ => Real.cos (4 * θ + 2 * β) / 2) volume 0 (2 * π) :=
      (by fun_prop : Continuous fun θ : ℝ => Real.cos (4 * θ + 2 * β) / 2).intervalIntegrable _ _
    simp_rw [e]
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_div,
      intervalIntegral.integral_div, hc1, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hadd := intervalIntegral.integral_add (hc.intervalIntegrable (μ := volume) 0 (2 * π))
    (hc'.intervalIntegrable (μ := volume) 0 (2 * π))
  simp_rw [hsum] at hadd
  rw [htot, ← heq] at hadd
  linarith

/-- eq:a2-bound: f ≥ 0, ‖f‖₂ = 1 ⇒ a₂² ≤ 1/2 -/
theorem a2_bound (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) (hpos : ∀ θ, 0 ≤ f θ)
    (hnorm : ∫ θ in (0 : ℝ)..(2 * π), f θ ^ 2 = 1) : a2 f ^ 2 ≤ 1 / 2 := by
  set ρ := ‖coef f 2‖ with hρ
  set hfun : ℝ → ℝ := fun θ => -Real.cos (2 * θ + β f) with hhf
  -- ρ = avg(h·f)
  have hρeq : ρ = avg (fun θ => hfun θ * f θ) := by
    have hc : -coef f 2 = ((ρ : ℝ) : ℂ) * Complex.exp ((β f : ℂ) * I) := by
      have := Complex.norm_mul_exp_arg_mul_I (-coef f 2)
      rw [norm_neg] at this
      rw [← this]; rfl
    -- ρ = Re(−e^{−iβ} f̂(2))
    have hre : ρ = (-(Complex.exp (-(β f : ℂ) * I) * coef f 2)).re := by
      have : -(Complex.exp (-(β f : ℂ) * I) * coef f 2)
          = Complex.exp (-(β f : ℂ) * I) * (-coef f 2) := by ring
      rw [this, hc]
      have e3 : Complex.exp (-(β f : ℂ) * I) * ((ρ : ℂ) * Complex.exp ((β f : ℂ) * I))
          = (ρ : ℂ) * Complex.exp (-(β f : ℂ) * I + (β f : ℂ) * I) := by
        rw [Complex.exp_add]; ring
      rw [e3, show -(β f : ℂ) * I + (β f : ℂ) * I = 0 by ring, Complex.exp_zero, mul_one,
        Complex.ofReal_re]
    rw [hre, coef_eq]
    rw [show -(Complex.exp (-(β f : ℂ) * I) * ((((1 / (2 * π) : ℝ) : ℂ)) * ∫ θ in (0 : ℝ)..(2 * π),
        Complex.exp (-((2 : ℤ) : ℂ) * θ * I) * ((f θ : ℝ) : ℂ)))
        = (((1 / (2 * π) : ℝ) : ℂ)) * ∫ θ in (0 : ℝ)..(2 * π),
          -(Complex.exp (-(β f : ℂ) * I) * (Complex.exp (-((2 : ℤ) : ℂ) * θ * I) * ((f θ : ℝ) : ℂ))) by
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]; ring]
    rw [Complex.re_ofReal_mul, avg]
    congr 1
    have hfi := intervalIntegrable_of_memLp hf
    rw [intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_of_le (by positivity)]
    have hint : Integrable (fun θ : ℝ => -(Complex.exp (-(β f : ℂ) * I)
        * (Complex.exp (-((2 : ℤ) : ℂ) * θ * I) * ((f θ : ℝ) : ℂ))))
        (volume.restrict (Set.Ioc 0 (2 * π))) := by
      have h1 : IntervalIntegrable (fun θ => ((f θ : ℝ) : ℂ)) volume 0 (2 * π) :=
        ⟨Integrable.ofReal hfi.1, Integrable.ofReal hfi.2⟩
      have h2 := h1.continuousOn_mul (Continuous.continuousOn (f := fun θ : ℝ =>
        -(Complex.exp (-(β f : ℂ) * I) * Complex.exp (-((2 : ℤ) : ℂ) * θ * I))) (by fun_prop))
      refine h2.1.congr ?_
      filter_upwards with θ
      ring
    have key := Complex.reCLM.integral_comp_comm hint
    simp only [Complex.reCLM_apply] at key
    rw [← key]
    · apply integral_congr_ae
      filter_upwards with θ
      have : -(Complex.exp (-(β f : ℂ) * I) * (Complex.exp (-((2 : ℤ) : ℂ) * θ * I) * ((f θ : ℝ) : ℂ)))
          = ((-Real.cos (2 * θ + β f) * f θ : ℝ) : ℂ) + ((Real.sin (2 * θ + β f) * f θ : ℝ) : ℂ) * I := by
        rw [← mul_assoc, ← Complex.exp_add]
        rw [show -(β f : ℂ) * I + -((2 : ℤ) : ℂ) * (θ : ℂ) * I = ((-(2 * θ + β f) : ℝ) : ℂ) * I by
          push_cast; ring]
        rw [Complex.exp_mul_I]
        rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
        push_cast; ring
      rw [this]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero,
        add_zero, hhf]
  -- ρ ≤ avg(h₊·f)
  set hp : ℝ → ℝ := fun θ => max (hfun θ) 0 with hhp
  have hfi := intervalIntegrable_of_memLp hf
  have hpc : Continuous hp := by simp only [hhp, hhf]; fun_prop
  have hhc : Continuous hfun := by simp only [hhf]; fun_prop
  have i1 : IntervalIntegrable (fun θ => hfun θ * f θ) volume 0 (2 * π) :=
    hfi.continuousOn_mul hhc.continuousOn
  have i2 : IntervalIntegrable (fun θ => hp θ * f θ) volume 0 (2 * π) :=
    hfi.continuousOn_mul hpc.continuousOn
  have hle1 : ρ ≤ avg (fun θ => hp θ * f θ) := by
    rw [hρeq]
    apply avg_mono i1 i2
    intro θ _
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hpos θ)
  -- Cauchy–Schwarz
  have if2 : IntervalIntegrable (fun θ => f θ ^ 2) volume 0 (2 * π) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
    exact hf.integrable_sq
  have ip2 : IntervalIntegrable (fun θ => hp θ ^ 2) volume 0 (2 * π) :=
    (hpc.pow 2).intervalIntegrable _ _
  have i2' : IntervalIntegrable (fun θ => f θ * hp θ) volume 0 (2 * π) := by
    refine i2.congr ?_; intro θ _; ring
  have cs := cs_avg if2 ip2 i2'
  have e1 : avg (fun θ => f θ * hp θ) = avg (fun θ => hp θ * f θ) := by
    congr 1; funext θ; ring
  have hf2 : avg (fun θ => f θ ^ 2) = 1 / (2 * π) := by rw [avg, hnorm]; ring
  have hp2 : avg (fun θ => hp θ ^ 2) = 1 / 4 := by
    rw [avg]
    have := int_pos_part_sq (β f)
    simp only [hhp, hhf]
    rw [this]; field_simp; ring
  rw [e1, hf2, hp2] at cs
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hρ2 : ρ ^ 2 ≤ 1 / (8 * π) := by
    have : ρ ^ 2 ≤ avg (fun θ => hp θ * f θ) ^ 2 := pow_le_pow_left₀ hρ0 hle1 2
    have hp' : (0 : ℝ) < π := pi_pos
    calc ρ ^ 2 ≤ avg (fun θ => hp θ * f θ) ^ 2 := this
      _ ≤ 1 / (2 * π) * (1 / 4) := cs
      _ = 1 / (8 * π) := by field_simp; ring
  rw [a2_eq]
  have hs : Real.sqrt π ^ 2 = π := Real.sq_sqrt pi_pos.le
  have hp' : (0 : ℝ) < π := pi_pos
  calc (2 * Real.sqrt π * ρ) ^ 2 = 4 * π * ρ ^ 2 := by rw [mul_pow, mul_pow, hs]; ring
    _ ≤ 4 * π * (1 / (8 * π)) := by gcongr
    _ = 1 / 2 := by field_simp; ring

end

end SteinTomas.S2E

#print axioms SteinTomas.S2E.tail_L2
#print axioms SteinTomas.S2E.a2_bound
#print axioms SteinTomas.S2E.avg_cos_w
