import Mathlib
import SteinTomasCircle.Section2.BesselGlobal

/-!
# Section 2 (§2.3): analytic part of the upper bound for ρ = σ*³ (eq:density-upper)

* `Kl m` = K(√m) = ∫₀^{π/2} (1 − m sin²θ)^{-1/2} dθ (Legendre form; equal to the u-form of the paper via u = sin θ)
* `int_inv`: ∫₀^{π/2} dθ/(1 − m sin²θ) = π/(2√(1−m)) (0 ≤ m < 1; the same integral as the u-form in the paper)
* `K_sq_le`: K² ≤ (π/2)·π/(2√(1−m)) (Cauchy–Schwarz)
* `density_upper`: from ρ(r) = (4/√r)K(√((r+1)³(3−r)/(16r))) (external input BSWZ12, Becker25)
  we get ρ(r)² ≤ 16π²/√(r(r−1)³(r+3)) and ρ(r) ≤ 4π/(√3(r−1)).
-/

namespace SteinTomas.S2R

open Real MeasureTheory Set

noncomputable section

/-- K(√m) (Legendre form) -/
def Kl (m : ℝ) : ℝ := ∫ θ in (0 : ℝ)..(π / 2), 1 / Real.sqrt (1 - m * Real.sin θ ^ 2)

/-- Cauchy–Schwarz on an interval (continuous functions) -/
theorem cs_interval {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    (∫ x in a..b, f x * g x) ^ 2 ≤ (∫ x in a..b, f x ^ 2) * (∫ x in a..b, g x ^ 2) := by
  have i1 : IntervalIntegrable (fun x => f x ^ 2) volume a b :=
    (by fun_prop : Continuous fun x => f x ^ 2).intervalIntegrable _ _
  have i2 : ∀ s : ℝ, IntervalIntegrable (fun x => (2 * s) * (f x * g x)) volume a b :=
    fun s => (by fun_prop : Continuous fun x => (2 * s) * (f x * g x)).intervalIntegrable _ _
  have i3 : ∀ s : ℝ, IntervalIntegrable (fun x => (s * s) * g x ^ 2) volume a b :=
    fun s => (by fun_prop : Continuous fun x => (s * s) * g x ^ 2).intervalIntegrable _ _
  have hquad : ∀ s : ℝ, 0 ≤ (∫ x in a..b, g x ^ 2) * (s * s) + 2 * (∫ x in a..b, f x * g x) * s
      + ∫ x in a..b, f x ^ 2 := by
    intro s
    have h0 : 0 ≤ ∫ x in a..b, (f x + s * g x) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun x _ => sq_nonneg _)
    have e : (fun x => (f x + s * g x) ^ 2)
        = fun x => (f x ^ 2 + (2 * s) * (f x * g x)) + (s * s) * g x ^ 2 := by
      funext x; ring
    rw [e, intervalIntegral.integral_add (i1.add (i2 s)) (i3 s),
      intervalIntegral.integral_add i1 (i2 s), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at h0
    linarith
  have := discrim_le_zero hquad
  unfold discrim at this
  nlinarith [this]

/-- Algebraic identity for the derivative: the derivative of H(θ) = θ − arctan(N/D) equals c/(cos²θ + c²sin²θ) -/
lemma key_alg {s co c : ℝ} (hsc : s ^ 2 + co ^ 2 = 1) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    1 - 1 / (1 + ((1 - c) * s * co / (co * co + c * (s * s))) ^ 2)
      * (((1 - c) * (co ^ 2 - s ^ 2) * (co * co + c * (s * s))
          - (1 - c) * s * co * (-2 * (1 - c) * s * co)) / (co * co + c * (s * s)) ^ 2)
      = c / (co ^ 2 + c ^ 2 * s ^ 2) := by
  have hD : 0 < co * co + c * (s * s) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hc1) (sq_nonneg co)]
  have hc2 : 0 ≤ 1 - c ^ 2 := by nlinarith
  have hP : 0 < co ^ 2 + c ^ 2 * s ^ 2 := by
    nlinarith [mul_nonneg hc2 (sq_nonneg co), pow_pos hc0 2]
  have hDN : 0 < (co * co + c * (s * s)) ^ 2 + ((1 - c) * s * co) ^ 2 := by positivity
  have F1 : (co * co + c * (s * s)) ^ 2 + ((1 - c) * s * co) ^ 2 = co ^ 2 + c ^ 2 * s ^ 2 := by
    linear_combination (co ^ 2 + c ^ 2 * s ^ 2) * hsc
  have F2 : (1 - c) * (co ^ 2 - s ^ 2) * (co * co + c * (s * s))
      - (1 - c) * s * co * (-2 * (1 - c) * s * co) = (1 - c) * (co ^ 2 - c * s ^ 2) := by
    linear_combination (1 - c) * (co ^ 2 - c * s ^ 2) * hsc
  have F3 : co ^ 2 + c ^ 2 * s ^ 2 - (1 - c) * (co ^ 2 - c * s ^ 2) = c := by
    linear_combination c * hsc
  have e1 : 1 / (1 + ((1 - c) * s * co / (co * co + c * (s * s))) ^ 2)
      * (((1 - c) * (co ^ 2 - s ^ 2) * (co * co + c * (s * s))
          - (1 - c) * s * co * (-2 * (1 - c) * s * co)) / (co * co + c * (s * s)) ^ 2)
      = ((1 - c) * (co ^ 2 - s ^ 2) * (co * co + c * (s * s))
          - (1 - c) * s * co * (-2 * (1 - c) * s * co))
        / ((co * co + c * (s * s)) ^ 2 + ((1 - c) * s * co) ^ 2) := by
    have e0 : 1 + ((1 - c) * s * co / (co * co + c * (s * s))) ^ 2
        = ((co * co + c * (s * s)) ^ 2 + ((1 - c) * s * co) ^ 2) / (co * co + c * (s * s)) ^ 2 := by
      rw [div_pow, eq_div_iff (pow_ne_zero 2 hD.ne'), add_mul,
        div_mul_cancel₀ _ (pow_ne_zero 2 hD.ne')]
      ring
    rw [e0, one_div_div, div_mul_div_comm, mul_comm ((co * co + c * (s * s)) ^ 2),
      mul_div_mul_right _ _ (pow_ne_zero 2 hD.ne')]
  rw [e1, F1, F2, eq_div_iff hP.ne', sub_mul, div_mul_cancel₀ _ hP.ne']
  linarith [F3]

/-- ∫₀^{π/2} dθ/(1 − m sin²θ) = π/(2√(1−m)) -/
theorem int_inv {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m < 1) :
    ∫ θ in (0 : ℝ)..(π / 2), 1 / (1 - m * Real.sin θ ^ 2) = π / (2 * Real.sqrt (1 - m)) := by
  obtain ⟨c, hcdef⟩ : ∃ c, c = Real.sqrt (1 - m) := ⟨_, rfl⟩
  rw [← hcdef]
  have hc0 : 0 < c := by rw [hcdef]; exact Real.sqrt_pos.2 (by linarith)
  have hc2 : c ^ 2 = 1 - m := by rw [hcdef]; exact Real.sq_sqrt (by linarith)
  have hc1 : c ≤ 1 := by nlinarith
  have hm : m = 1 - c ^ 2 := by linarith
  have hPpos : ∀ θ : ℝ, 0 < Real.cos θ ^ 2 + c ^ 2 * Real.sin θ ^ 2 := by
    intro θ
    have := sin_sq_add_cos_sq θ
    have hc2' : 0 ≤ 1 - c ^ 2 := by nlinarith
    nlinarith [mul_nonneg hc2' (sq_nonneg (Real.cos θ)), pow_pos hc0 2]
  have hDpos : ∀ θ : ℝ, Real.cos θ * Real.cos θ + c * (Real.sin θ * Real.sin θ) ≠ 0 := by
    intro θ
    have := sin_sq_add_cos_sq θ
    nlinarith [mul_nonneg (sub_nonneg.2 hc1) (sq_nonneg (Real.cos θ))]
  -- H(θ) = θ − arctan(N/D)
  have hH : ∀ θ : ℝ, HasDerivAt (fun x => x - Real.arctan ((1 - c) * Real.sin x * Real.cos x
      / (Real.cos x * Real.cos x + c * (Real.sin x * Real.sin x))))
      (c / (Real.cos θ ^ 2 + c ^ 2 * Real.sin θ ^ 2)) θ := by
    intro θ
    have hN : HasDerivAt (fun x => (1 - c) * Real.sin x * Real.cos x)
        ((1 - c) * (Real.cos θ ^ 2 - Real.sin θ ^ 2)) θ := by
      have := ((Real.hasDerivAt_sin θ).const_mul (1 - c)).mul (Real.hasDerivAt_cos θ)
      convert this using 1; ring
    have hD : HasDerivAt (fun x => Real.cos x * Real.cos x + c * (Real.sin x * Real.sin x))
        (-2 * (1 - c) * Real.sin θ * Real.cos θ) θ := by
      have := ((Real.hasDerivAt_cos θ).mul (Real.hasDerivAt_cos θ)).add
        (((Real.hasDerivAt_sin θ).mul (Real.hasDerivAt_sin θ)).const_mul c)
      convert this using 1; ring
    have h := (hasDerivAt_id' θ).sub ((hN.div hD (hDpos θ)).arctan)
    exact h.congr_deriv (key_alg (sin_sq_add_cos_sq θ) hc0 hc1)
  have hcont : Continuous fun θ => c / (Real.cos θ ^ 2 + c ^ 2 * Real.sin θ ^ 2) :=
    continuous_const.div (show Continuous fun θ : ℝ => Real.cos θ ^ 2 + c ^ 2 * Real.sin θ ^ 2 by
      fun_prop) (fun θ => (hPpos θ).ne')
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := π / 2)
    (fun x _ => hH x) (hcont.intervalIntegrable _ _)
  simp only [Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_zero, Real.cos_zero, mul_zero,
    mul_one, zero_div, Real.arctan_zero, sub_zero] at hFTC
  have e : ∀ θ ∈ uIcc (0 : ℝ) (π / 2), 1 / (1 - m * Real.sin θ ^ 2)
      = 1 / c * (c / (Real.cos θ ^ 2 + c ^ 2 * Real.sin θ ^ 2)) := by
    intro θ _
    have hsc := sin_sq_add_cos_sq θ
    have h1 : 1 - m * Real.sin θ ^ 2 = Real.cos θ ^ 2 + c ^ 2 * Real.sin θ ^ 2 := by
      rw [hm]; linear_combination -hsc
    rw [h1]
    field_simp
  rw [intervalIntegral.integral_congr e, intervalIntegral.integral_const_mul, hFTC]
  field_simp

/-- K(√m)² ≤ (π/2)·π/(2√(1−m)) -/
theorem K_sq_le {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m < 1) :
    Kl m ^ 2 ≤ π / 2 * (π / (2 * Real.sqrt (1 - m))) := by
  have hpos : ∀ θ : ℝ, 0 < 1 - m * Real.sin θ ^ 2 := by
    intro θ
    have := Real.sin_sq_le_one θ
    nlinarith
  have hb : Continuous fun θ => 1 / Real.sqrt (1 - m * Real.sin θ ^ 2) :=
    continuous_const.div (Real.continuous_sqrt.comp (by fun_prop))
      (fun θ => (Real.sqrt_pos.2 (hpos θ)).ne')
  have h := cs_interval (a := 0) (b := π / 2) (by positivity) (f := fun _ => (1 : ℝ))
    continuous_const hb
  have e1 : ∫ x in (0 : ℝ)..(π / 2), (1 : ℝ) * (1 / Real.sqrt (1 - m * Real.sin x ^ 2)) = Kl m := by
    simp only [one_mul]; rfl
  have e2 : ∫ x in (0 : ℝ)..(π / 2), (1 : ℝ) ^ 2 = π / 2 := by simp
  have e3 : ∫ x in (0 : ℝ)..(π / 2), (1 / Real.sqrt (1 - m * Real.sin x ^ 2)) ^ 2
      = ∫ x in (0 : ℝ)..(π / 2), 1 / (1 - m * Real.sin x ^ 2) := by
    apply intervalIntegral.integral_congr
    intro θ _
    simp only
    rw [div_pow, one_pow, Real.sq_sqrt (hpos θ).le]
  rw [e1, e2, e3, int_inv hm0 hm1] at h
  exact h

/-- eq:density-upper -/
theorem density_upper {ρ : ℝ → ℝ}
    (hρ : ∀ r, 1 < r → r < 3 → ρ r = 4 / Real.sqrt r * Kl ((r + 1) ^ 3 * (3 - r) / (16 * r)))
    {r : ℝ} (hr1 : 1 < r) (hr3 : r < 3) :
    ρ r ^ 2 ≤ 16 * π ^ 2 / Real.sqrt (r * (r - 1) ^ 3 * (r + 3)) ∧
    ρ r ≤ 4 * π / (Real.sqrt 3 * (r - 1)) := by
  have hr : 0 < r := by linarith
  obtain ⟨hid, hm0, hm1⟩ := Section2.k_sq_identity hr1 hr3
  set m := (r + 1) ^ 3 * (3 - r) / (16 * r) with hmdef
  have hK := K_sq_le hm0.le hm1
  have hK0 : 0 ≤ Kl m := by
    unfold Kl
    apply intervalIntegral.integral_nonneg (by positivity)
    intro θ _; positivity
  have hQ : 0 < r * (r - 1) ^ 3 * (r + 3) := by
    have : 0 < r - 1 := by linarith
    positivity
  have h1m : 1 - m = r * (r - 1) ^ 3 * (r + 3) / (4 * r) ^ 2 := by
    rw [hid]; field_simp; ring
  have hs1m : Real.sqrt (1 - m) = Real.sqrt (r * (r - 1) ^ 3 * (r + 3)) / (4 * r) := by
    rw [h1m, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
  have hsQ : 0 < Real.sqrt (r * (r - 1) ^ 3 * (r + 3)) := Real.sqrt_pos.2 hQ
  have hsr : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have hsr0 : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hρr := hρ r hr1 hr3
  have hsq : ρ r ^ 2 ≤ 16 * π ^ 2 / Real.sqrt (r * (r - 1) ^ 3 * (r + 3)) := by
    rw [hρr, mul_pow, div_pow, hsr]
    calc 4 ^ 2 / r * Kl m ^ 2 ≤ 4 ^ 2 / r * (π / 2 * (π / (2 * Real.sqrt (1 - m)))) :=
          mul_le_mul_of_nonneg_left hK (by positivity)
      _ = 16 * π ^ 2 / Real.sqrt (r * (r - 1) ^ 3 * (r + 3)) := by
          rw [hs1m]; field_simp; ring
  refine ⟨hsq, Section2.rho_bound hr1 hr3 ?_ hsq⟩
  rw [hρr]; positivity

end

end SteinTomas.S2R

#print axioms SteinTomas.S2R.int_inv
#print axioms SteinTomas.S2R.density_upper
