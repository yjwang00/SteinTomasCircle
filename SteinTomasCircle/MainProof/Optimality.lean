import SteinTomasCircle.MainProof.Compactness

namespace SteinTomas.S6

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

/-- The sixth power of the modulus of the one-dimensional Gaussian Schrödinger profile. -/
private def gaussianSixth (t x : ℝ) : ℝ :=
  Real.exp (-(3 / (1 + t ^ 2)) * x ^ 2) / (Real.sqrt (1 + t ^ 2)) ^ 3

/-- The Gaussian quotient before the factor (2π)⁻³ in FLS16, §7. -/
def gaussianSixthQuotient : ℝ :=
  (∫ t : ℝ, ∫ x : ℝ, gaussianSixth t x) /
    (∫ x : ℝ, Real.exp (-x ^ 2)) ^ 3

lemma gaussianSixthQuotient_eq : gaussianSixthQuotient = (Real.sqrt 3)⁻¹ := by
  have hinner (t : ℝ) :
      (∫ x : ℝ, gaussianSixth t x) = Real.sqrt (π / 3) * (1 + t ^ 2)⁻¹ := by
    have ht : 0 < 1 + t ^ 2 := by positivity
    unfold gaussianSixth
    rw [integral_div, integral_gaussian,
      show π / (3 / (1 + t ^ 2)) = (π / 3) * (1 + t ^ 2) by field_simp,
      Real.sqrt_mul (by positivity)]
    let q := Real.sqrt (1 + t ^ 2)
    have hq : 0 < q := Real.sqrt_pos.mpr ht
    have hq2 : q ^ 2 = 1 + t ^ 2 := Real.sq_sqrt ht.le
    change Real.sqrt (π / 3) * q / q ^ 3 = Real.sqrt (π / 3) * (1 + t ^ 2)⁻¹
    rw [← hq2]
    field_simp
    <;> ring
  have hg : (∫ x : ℝ, Real.exp (-x ^ 2)) = Real.sqrt π := by
    simpa only [neg_one_mul, div_one] using integral_gaussian 1
  unfold gaussianSixthQuotient
  simp_rw [hinner, integral_const_mul]
  rw [integral_univ_inv_one_add_sq, hg, Real.sqrt_div pi_pos.le]
  let p := Real.sqrt π
  have hp : 0 < p := Real.sqrt_pos.mpr pi_pos
  have h3 : 0 < Real.sqrt 3 := by positivity
  have hp2 : p ^ 2 = π := Real.sq_sqrt pi_pos.le
  change (p / Real.sqrt 3 * π) / p ^ 3 = (Real.sqrt 3)⁻¹
  rw [← hp2]
  field_simp

/-- The two-profile multiplier in FLS16, Corollary 6.2, with q = 6. -/
def antipodalFactor : ℝ := (8 / Real.sqrt π) * (Real.Gamma (7 / 2) / Real.Gamma 4)

lemma antipodalFactor_eq : antipodalFactor = 5 / 2 := by
  have h1 : Real.Gamma (3 / 2) = (1 / 2) * Real.sqrt π := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
  have h2 : Real.Gamma (5 / 2) = (3 / 2) * Real.Gamma (3 / 2) := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
  have h3 : Real.Gamma (7 / 2) = (5 / 2) * Real.Gamma (5 / 2) := by
    rw [show (7 / 2 : ℝ) = 5 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
  have h4 : Real.Gamma 4 = 6 := by
    calc
      Real.Gamma 4 = Real.Gamma (((3 : ℕ) : ℝ) + 1) := by norm_num
      _ = ((Nat.factorial 3 : ℕ) : ℝ) := Real.Gamma_nat_eq_factorial 3
      _ = 6 := by norm_num [Nat.factorial]
  unfold antipodalFactor
  rw [h3, h2, h1, h4]
  have hp : 0 < Real.sqrt π := Real.sqrt_pos.mpr pi_pos
  field_simp
  <;> ring

/-- The Gaussian two-profile limit in the unitary inverse Fourier convention of FLS16. -/
def flsTrialLimit : ℝ :=
  antipodalFactor * ((2 * π) ^ 3)⁻¹ * gaussianSixthQuotient

lemma flsTrialLimit_scale : (2 * π) ^ 6 * flsTrialLimit = Mconc := by
  rw [flsTrialLimit, antipodalFactor_eq, gaussianSixthQuotient_eq, Mconc]
  have hp : 0 < π := pi_pos
  have h3 : 0 < Real.sqrt 3 := by positivity
  field_simp
  <;> ring

/-- Sixth-power energy in the inverse Fourier normalization of FLS16, equation (1.1)
and the definition preceding it, specialized to N = 2. -/
def flsEnergy6 (F : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ × ℝ, ‖((1 / (2 * π) : ℝ) : ℂ) * E F (-x)‖ₑ ^ 6

lemma ext6_eq_flsEnergy6 (F : ℝ → ℂ) :
    ext6 F = ENNReal.ofReal ((2 * π) ^ 6) * flsEnergy6 F := by
  have hc : ‖((1 / (2 * π) : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (1 / (2 * π)) := by
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hf : flsEnergy6 F = ENNReal.ofReal (1 / (2 * π)) ^ 6 * ext6 F := by
    simp_rw [flsEnergy6, enorm_mul, hc, mul_pow]
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
    exact congrArg (_ * ·) (lintegral_neg_eq_self (fun x : ℝ × ℝ => ‖E F x‖ₑ ^ 6))
  have h : ENNReal.ofReal ((2 * π) ^ 6) * ENNReal.ofReal (1 / (2 * π)) ^ 6 = 1 := by
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
      mul_one_div_cancel (show 2 * π ≠ 0 by positivity), one_pow, ENNReal.ofReal_one]
  rw [hf, ← mul_assoc, h, one_mul]

/-- FLS16, §7 and Proposition 7.1, in dimension two: normalized antipodal Gaussian
trials converge weakly to zero and their unitary extension energies tend to the leading
term of (7.1). The limit uses only the Gaussian quotient, with no strict inequality
or assertion about the best constant on the circle. -/
def FLSGaussianTrial : Prop :=
  ∃ u : ℕ → ℝ → ℝ, (∀ j, Adm (u j)) ∧ (∀ j, sqNorm (u j) = 1) ∧
    (∀ g, MemLp g 2 σ → Tendsto (fun j => ∫ θ, u j θ * g θ ∂σ) atTop (𝓝 0)) ∧
    Tendsto (fun j => flsEnergy6 (toC (u j))) atTop (𝓝 (ENNReal.ofReal flsTrialLimit))

/-- A trial sequence with unit L² norm, vanishing L¹ norm and energy tending to Mconc. -/
theorem fls_trial_sequence (hFLS : FLSGaussianTrial) :
    ∃ U : ℕ → ℝ → ℂ, (∀ j, MemLp (U j) 2 σ) ∧ (∀ j, L2n (U j) = 1) ∧
      Tendsto (fun j => L1n (U j)) atTop (𝓝 0) ∧
      Tendsto (fun j => ext6 (U j)) atTop (𝓝 (ENNReal.ofReal Mconc)) := by
  obtain ⟨u, hu, hB, hweak, hE⟩ := hFLS
  haveI : IsFiniteMeasure σ := isFin
  refine ⟨fun j => toC (u j), fun j => (hu j).memLp.ofReal, ?_, ?_, ?_⟩
  · intro j
    rw [L2n_eq (F := toC (u j)) (hu j).memLp.ofReal]
    simp only [toC, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [show (∫ θ in Ioc 0 (2 * π), u j θ ^ 2) = 1 from hB j,
      Real.sqrt_one, ENNReal.ofReal_one]
  · have h := hweak (fun _ => 1) (memLp_const _)
    simp only [mul_one] at h
    have h' := ENNReal.continuous_ofReal.tendsto 0 |>.comp h
    simp only [ENNReal.ofReal_zero] at h'
    convert h' using 1
    funext j
    rw [L1n_eq (F := toC (u j)) (hu j).memLp.ofReal]
    simp only [toC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ((hu j).nonneg _)]
    rfl
  · simp_rw [ext6_eq_flsEnergy6]
    have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ((2 * π) ^ 6)) hE
      (Or.inr ENNReal.ofReal_ne_top)
    rwa [← ENNReal.ofReal_mul (by positivity), flsTrialLimit_scale] at h

/-- Every upper bound of this form with a finite L¹ coefficient has leading constant ≥ Mconc. -/
theorem Mconc_optimal (hFLS : FLSGaussianTrial) {A R : ℝ≥0∞} (hR : R ≠ ∞)
    (h : ∀ F : ℝ → ℂ, MemLp F 2 σ →
      ext6 F ≤ A * L2n F ^ 6 + R * L1n F ^ 2 * L2n F ^ 4) :
    ENNReal.ofReal Mconc ≤ A := by
  obtain ⟨U, hU, h2, h1, hE⟩ := fls_trial_sequence hFLS
  have hL : Tendsto (fun j => R * L1n (U j) ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using
      ENNReal.Tendsto.const_mul (ENNReal.Tendsto.pow (n := 2) h1) (Or.inr hR)
  have hA : Tendsto (fun j => A + R * L1n (U j) ^ 2) atTop (𝓝 A) := by
    simpa only [add_zero] using tendsto_const_nhds.add hL
  refine le_of_tendsto_of_tendsto' hE hA (fun j => ?_)
  simpa only [h2 j, one_pow, mul_one] using h (U j) (hU j)

/-- Theorem 1.2: Mconc is the least leading coefficient when the remainder has coefficient 90π. -/
theorem thm_L1_remainder_optimal {ρ : ℝ × ℝ → ℝ} {ρr : ℝ → ℝ}
    (hsin : S2C.SinSeries) (hρ : RhoData ρ ρr) (hnu : ∀ g, Adm g → ∃ ν, NuData g ν)
    (hred : CFOTReduction) (hFLS : FLSGaussianTrial) :
    IsLeast {A : ℝ≥0∞ | ∀ F : ℝ → ℂ, MemLp F 2 σ →
      ext6 F ≤ A * L2n F ^ 6 + ENNReal.ofReal (90 * π) * L1n F ^ 2 * L2n F ^ 4}
      (ENNReal.ofReal Mconc) := by
  refine ⟨thm_L1_remainder hsin hρ hnu hred, fun A hA => ?_⟩
  exact Mconc_optimal hFLS (R := ENNReal.ofReal (90 * π)) ENNReal.ofReal_ne_top hA

end

end SteinTomas.S6

#print axioms SteinTomas.S6.thm_L1_remainder_optimal
