import Mathlib

/-!
# Section 2 (§2.1): Fourier expansion on the unit circle and Parseval's identity

Functions on the circle are parametrized by the angle: f : ℝ → ℝ, only values on (0, 2π] are used.
* `coef f n` = f̂(n) = (1/2π)∫₀^{2π} f(θ)e^{−inθ}dθ (Mathlib's `fourierCoeffOn`)
* `parseval`: Σ_{n∈ℤ} |f̂(n)|² = (1/2π)∫₀^{2π} f² (Mathlib's Parseval identity)
* `coef_neg`: f real-valued ⇒ f̂(−n) = conj f̂(n)
* `coef_odd`: f antipodal (f(θ+π) = f(θ)) ⇒ the odd coefficients vanish
* `parseval_even`: a₀² + Σ_{n≥1} a_{2n}² = ‖f‖₂², where a₀ = (2π)^{-1/2}∫f,
  a_{2n}² = 2π(|f̂(2n)|² + |f̂(−2n)|²) (= 4π|f̂(2n)|², as in the paper)
-/

namespace SteinTomas.S2F

open Real MeasureTheory Complex

noncomputable section

/-- f̂(n) -/
def coef (f : ℝ → ℝ) (n : ℤ) : ℂ := fourierCoeffOn Real.two_pi_pos (fun θ => ((f θ : ℝ) : ℂ)) n

/-- Explicit formula -/
lemma coef_eq (f : ℝ → ℝ) (n : ℤ) :
    coef f n = ((1 / (2 * π) : ℝ) : ℂ)
      * ∫ θ in (0 : ℝ)..(2 * π), Complex.exp (-(n : ℂ) * θ * I) * f θ := by
  rw [coef, fourierCoeffOn_eq_integral]
  have hx : ∀ x : ℝ, fourier (-n) (x : AddCircle (2 * π - 0)) • ((f x : ℝ) : ℂ)
      = Complex.exp (-(n : ℂ) * x * I) * f x := by
    intro x
    rw [fourier_coe_apply, smul_eq_mul]
    congr 2
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast [sub_zero]
    field_simp
  simp_rw [hx]
  rw [Complex.real_smul, sub_zero]

/-- The 0-th coefficient is real: f̂(0) = (1/2π)∫f -/
lemma coef_zero (f : ℝ → ℝ) :
    coef f 0 = (((1 / (2 * π)) * ∫ θ in (0 : ℝ)..(2 * π), f θ : ℝ) : ℂ) := by
  rw [coef_eq]
  simp only [Int.cast_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul]
  rw [intervalIntegral.integral_ofReal]
  push_cast; ring

/-- Parseval's identity -/
theorem parseval {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) :
    HasSum (fun n => ‖coef f n‖ ^ 2) ((1 / (2 * π)) * ∫ θ in (0 : ℝ)..(2 * π), f θ ^ 2) := by
  have h := hasSum_sq_fourierCoeffOn (f := fun θ => ((f θ : ℝ) : ℂ)) Real.two_pi_pos
    (hf.ofReal (K := ℂ))
  have e : ∀ x : ℝ, ‖((f x : ℝ) : ℂ)‖ ^ 2 = f x ^ 2 := fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [e] at h
  rw [sub_zero, smul_eq_mul] at h
  simp only [coef]
  convert h using 1
  ring

/-- Interval integrability from L² -/
lemma intervalIntegrable_of_memLp {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) :
    IntervalIntegrable f volume 0 (2 * π) := by
  have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
  exact hf.integrable one_le_two

/-- Real function: f̂(−n) = conj f̂(n) -/
lemma coef_neg (f : ℝ → ℝ) (n : ℤ) : coef f (-n) = (starRingEnd ℂ) (coef f n) := by
  rw [coef_eq, coef_eq, map_mul, Complex.conj_ofReal,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π),
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π), ← integral_conj]
  have key : ∫ x in Set.Ioc 0 (2 * π), Complex.exp (-((-n : ℤ) : ℂ) * x * I) * f x
      = ∫ x in Set.Ioc 0 (2 * π), (starRingEnd ℂ) (Complex.exp (-(n : ℂ) * x * I) * f x) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I] <;> ring
  rw [key]

/-- Antipodal ⇒ the odd coefficients vanish -/
lemma coef_odd {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π))))
    (hanti : ∀ θ, f (θ + π) = f θ) {n : ℤ} (hn : Odd n) : coef f n = 0 := by
  obtain ⟨m, rfl⟩ := hn
  rw [coef_eq]
  set g : ℝ → ℂ := fun θ => Complex.exp (-(((2 * m + 1 : ℤ)) : ℂ) * θ * I) * f θ with hg
  have hfi := intervalIntegrable_of_memLp hf
  have hgi : ∀ a b : ℝ, 0 ≤ a → b ≤ 2 * π → a ≤ b → IntervalIntegrable g volume a b := by
    intro a b ha hb hab
    have h1 : IntervalIntegrable (fun θ => ((f θ : ℝ) : ℂ)) volume 0 (2 * π) :=
      ⟨Integrable.ofReal hfi.1, Integrable.ofReal hfi.2⟩
    have h2 : IntervalIntegrable g volume 0 (2 * π) :=
      h1.continuousOn_mul (Continuous.continuousOn (by fun_prop))
    exact h2.mono_set (by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by positivity)]
      exact Set.Icc_subset_Icc ha hb)
  have hshift : ∀ x : ℝ, g (x + π) = -g x := by
    intro x
    simp only [hg, hanti x]
    have e : -(((2 * m + 1 : ℤ)) : ℂ) * ((x + π : ℝ) : ℂ) * I
        = -(((2 * m + 1 : ℤ)) : ℂ) * (x : ℂ) * I + ((-m : ℤ) : ℂ) * (2 * π * I) + -(π * I) := by
      push_cast; ring
    rw [e, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_neg,
      Complex.exp_pi_mul_I]
    ring
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hgi 0 π le_rfl (by linarith [pi_pos]) pi_pos.le)
    (hgi π (2 * π) pi_pos.le le_rfl (by linarith [pi_pos]))
  have hsecond : ∫ θ in π..(2 * π), g θ = -∫ θ in (0 : ℝ)..π, g θ := by
    have := intervalIntegral.integral_comp_add_right (f := g) (a := 0) (b := π) π
    rw [zero_add, show π + π = 2 * π by ring] at this
    rw [← this]
    simp_rw [hshift]
    rw [intervalIntegral.integral_neg]
  have hzero : ∫ θ in (0 : ℝ)..(2 * π), g θ = 0 := by
    rw [← hsplit, hsecond]; ring
  simp only [hg] at hzero
  rw [hzero, mul_zero]

/-- a₀ = ⟨f, e₀⟩ = (2π)^{-1/2}∫f from the paper -/
def a0 (f : ℝ → ℝ) : ℝ := (1 / Real.sqrt (2 * π)) * ∫ θ in (0 : ℝ)..(2 * π), f θ

/-- a_{2n}² from the paper (n ≥ 1), indexed by `n+1`: 2π(|f̂(2n)|² + |f̂(−2n)|²) -/
def asq (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  2 * π * (‖coef f ((2 * (n + 1) : ℕ) : ℤ)‖ ^ 2 + ‖coef f (-((2 * (n + 1) : ℕ) : ℤ))‖ ^ 2)

lemma a0_sq (f : ℝ → ℝ) : a0 f ^ 2 = 2 * π * ‖coef f 0‖ ^ 2 := by
  have hs : Real.sqrt (2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  have hp : (0 : ℝ) < 2 * π := by positivity
  have h1 : (1 / Real.sqrt (2 * π)) ^ 2 = 1 / (2 * π) := by rw [div_pow, one_pow, hs]
  rw [coef_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs, a0, mul_pow, h1]
  field_simp

/-- Parseval form of eq:angular-expansion: Σ_{n≥1} a_{2n}² = ‖f‖₂² − a₀² -/
theorem parseval_even {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π))))
    (hanti : ∀ θ, f (θ + π) = f θ) :
    HasSum (asq f) ((∫ θ in (0 : ℝ)..(2 * π), f θ ^ 2) - a0 f ^ 2) := by
  have hP := (parseval hf).nat_add_neg
  set t : ℕ → ℝ := fun n => ‖coef f (n : ℤ)‖ ^ 2 + ‖coef f (-(n : ℤ))‖ ^ 2 with ht
  -- the odd terms vanish
  have hodd : ∀ x : ℕ, x ∉ Set.range (fun m : ℕ => 2 * m) → t x = 0 := by
    intro x hx
    have hxo : Odd x := by
      rcases Nat.even_or_odd x with he | ho
      · exfalso; apply hx; obtain ⟨r, hr⟩ := he; exact ⟨r, by simp only; omega⟩
      · exact ho
    have h1 : Odd (x : ℤ) := by exact_mod_cast hxo
    have h2 : Odd (-(x : ℤ)) := h1.neg
    simp only [ht, coef_odd hf hanti h1, coef_odd hf hanti h2, norm_zero]
    ring
  have hinj : Function.Injective (fun m : ℕ => 2 * m) := fun a b h => by simpa using h
  have hE : HasSum (t ∘ fun m : ℕ => 2 * m)
      ((1 / (2 * π)) * (∫ θ in (0 : ℝ)..(2 * π), f θ ^ 2) + ‖coef f 0‖ ^ 2) := by
    rw [hinj.hasSum_iff hodd]
    simpa [ht] using hP
  have hE1 := (hasSum_nat_add_iff' 1).mpr hE
  simp only [Finset.range_one, Finset.sum_singleton, Function.comp, ht] at hE1
  have hmul := hE1.mul_left (2 * π)
  have hp : (2 * π) ≠ 0 := by positivity
  convert hmul using 1
  · funext n
    simp only [asq]
    try (push_cast; ring_nf)
  · rw [a0_sq]
    push_cast
    field_simp
    ring

end

end SteinTomas.S2F

#print axioms SteinTomas.S2F.parseval_even
#print axioms SteinTomas.S2F.coef_neg
