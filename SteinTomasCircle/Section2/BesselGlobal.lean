import Mathlib
import SteinTomasCircle.Basic.Elementary
import SteinTomasCircle.Section3.Algebra

/-!
# Formalization of Section 2 (Preliminaries)

Convention: in Section 3 all angular functions depend on θ only through θ^{2n} (θ = e^{iφ}),
so ψ = 2φ is used as angular variable, c = cos ψ = Re θ², Re θ^{2j} = cos(jψ) = T_j(c).
The angular average avg g = (1/2π)∫₀^{2π} g(ψ)dψ (the same as the average with respect to dσ(θ)/2π, by periodicity).

This file contains:
* §2.1: the numerical part of the OST17 tail estimate; eq:bessel-global from the tabulated values;
  eq:prop31-a and the upper bound for Σα_{2n}a_{2n}² (HasSum form); γ(r) ≤ 1/3.
* §2.2: the algebraic derivation of the Φ-identity from the Euler–Lagrange equation.
* §2.3: upper bounds from the Fourier formula for Q; derivation of the bound eq:density-upper for ρ.
* angular tools needed in Section 3: moments of cos, averages of polynomials, Cauchy–Schwarz,
  the formula for avg[Φ(v)−(27/256)v²], avg[(ΣA_jT_j)²] = ½ΣA_j².
-/

namespace SteinTomas.Section2

open Real Finset MeasureTheory intervalIntegral

noncomputable section

/-! ## Angular average and its linearity -/

/-- Angular average (1/2π)∫₀^{2π} g -/
def avg (g : ℝ → ℝ) : ℝ := (1 / (2 * π)) * ∫ x in (0 : ℝ)..(2 * π), g x

lemma avg_add {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 (2 * π))
    (hg : IntervalIntegrable g volume 0 (2 * π)) :
    avg (fun x => f x + g x) = avg f + avg g := by
  unfold avg; rw [intervalIntegral.integral_add hf hg]; ring

lemma avg_sub {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 (2 * π))
    (hg : IntervalIntegrable g volume 0 (2 * π)) :
    avg (fun x => f x - g x) = avg f - avg g := by
  unfold avg; rw [intervalIntegral.integral_sub hf hg]; ring

lemma avg_const_mul (c : ℝ) (f : ℝ → ℝ) : avg (fun x => c * f x) = c * avg f := by
  unfold avg; rw [intervalIntegral.integral_const_mul]; ring

lemma avg_const (c : ℝ) : avg (fun _ => c) = c := by
  unfold avg; simp; field_simp

lemma avg_mono {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 (2 * π))
    (hg : IntervalIntegrable g volume 0 (2 * π)) (h : ∀ x ∈ Set.Icc 0 (2 * π), f x ≤ g x) :
    avg f ≤ avg g := by
  unfold avg
  have := intervalIntegral.integral_mono_on (by positivity) hf hg h
  have hp : 0 ≤ 1 / (2 * π) := by positivity
  exact mul_le_mul_of_nonneg_left this hp

lemma avg_nonneg {f : ℝ → ℝ} (h : ∀ x ∈ Set.Icc 0 (2 * π), 0 ≤ f x) : 0 ≤ avg f := by
  unfold avg
  have := intervalIntegral.integral_nonneg (μ := volume) (by positivity) h
  positivity

/-! ## Moments of cos -/

lemma int_cos_pow_rec (n : ℕ) :
    ∫ x in (0 : ℝ)..(2 * π), cos x ^ (n + 2)
      = ((n : ℝ) + 1) / ((n : ℝ) + 2) * ∫ x in (0 : ℝ)..(2 * π), cos x ^ n := by
  rw [integral_cos_pow]; simp

lemma int_cos_pow_zero : ∫ x in (0 : ℝ)..(2 * π), cos x ^ 0 = 2 * π := by simp

lemma int_cos_pow_one : ∫ x in (0 : ℝ)..(2 * π), cos x ^ 1 = 0 := by simp [integral_cos]

lemma mom2 : ∫ x in (0 : ℝ)..(2 * π), cos x ^ 2 = π := by
  rw [show (2 : ℕ) = 0 + 2 from rfl, int_cos_pow_rec, int_cos_pow_zero]; push_cast; ring
lemma mom3 : ∫ x in (0 : ℝ)..(2 * π), cos x ^ 3 = 0 := by
  rw [show (3 : ℕ) = 1 + 2 from rfl, int_cos_pow_rec, int_cos_pow_one]; ring
lemma mom4 : ∫ x in (0 : ℝ)..(2 * π), cos x ^ 4 = 3 / 4 * π := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, int_cos_pow_rec, mom2]; push_cast; ring
lemma mom5 : ∫ x in (0 : ℝ)..(2 * π), cos x ^ 5 = 0 := by
  rw [show (5 : ℕ) = 3 + 2 from rfl, int_cos_pow_rec, mom3]; ring
lemma mom6 : ∫ x in (0 : ℝ)..(2 * π), cos x ^ 6 = 5 / 8 * π := by
  have h := int_cos_pow_rec 4
  rw [show 4 + 2 = 6 from rfl] at h
  rw [h, mom4]; push_cast; ring
lemma mom7 : ∫ x in (0 : ℝ)..(2 * π), cos x ^ 7 = 0 := by
  have h := int_cos_pow_rec 5
  rw [show 5 + 2 = 7 from rfl] at h
  rw [h, mom5]; ring
lemma mom8 : ∫ x in (0 : ℝ)..(2 * π), cos x ^ 8 = 35 / 64 * π := by
  have h := int_cos_pow_rec 6
  rw [show 6 + 2 = 8 from rfl] at h
  rw [h, mom6]; push_cast; ring
lemma mom9 : ∫ x in (0 : ℝ)..(2 * π), cos x ^ 9 = 0 := by
  have h := int_cos_pow_rec 7
  rw [show 7 + 2 = 9 from rfl] at h
  rw [h, mom7]; ring
lemma mom10 : ∫ x in (0 : ℝ)..(2 * π), cos x ^ 10 = 63 / 128 * π := by
  have h := int_cos_pow_rec 8
  rw [show 8 + 2 = 10 from rfl] at h
  rw [h, mom8]; push_cast; ring

/-- Integral of a polynomial: ∫ Σ p_k cos^k = Σ p_k ∫cos^k -/
lemma int_poly_cos (p : ℕ → ℝ) (N : ℕ) :
    ∫ x in (0 : ℝ)..(2 * π), ∑ k ∈ range N, p k * cos x ^ k
      = ∑ k ∈ range N, p k * ∫ x in (0 : ℝ)..(2 * π), cos x ^ k := by
  rw [intervalIntegral.integral_finsetSum]
  · congr 1; ext k; rw [intervalIntegral.integral_const_mul]
  · intro k _
    exact (by fun_prop : Continuous fun x => p k * cos x ^ k).intervalIntegrable _ _

/-! ## Cauchy–Schwarz (angular) -/

theorem cs_avg {f g : ℝ → ℝ} (hf2 : IntervalIntegrable (fun x => f x ^ 2) volume 0 (2 * π))
    (hg2 : IntervalIntegrable (fun x => g x ^ 2) volume 0 (2 * π))
    (hfg : IntervalIntegrable (fun x => f x * g x) volume 0 (2 * π)) :
    avg (fun x => f x * g x) ^ 2 ≤ avg (fun x => f x ^ 2) * avg (fun x => g x ^ 2) := by
  have hquad : ∀ s : ℝ, 0 ≤ avg (fun x => g x ^ 2) * (s * s) + 2 * avg (fun x => f x * g x) * s
      + avg (fun x => f x ^ 2) := by
    intro s
    have h0 : 0 ≤ avg (fun x => (f x + s * g x) ^ 2) := avg_nonneg (fun x _ => sq_nonneg _)
    have e : (fun x => (f x + s * g x) ^ 2)
        = fun x => (f x ^ 2 + (2 * s) * (f x * g x)) + (s * s) * g x ^ 2 := by
      funext x; ring
    rw [e, avg_add (hf2.add (hfg.const_mul (2 * s))) (hg2.const_mul (s * s)),
      avg_add hf2 (hfg.const_mul (2 * s)), avg_const_mul, avg_const_mul] at h0
    linarith
  have := discrim_le_zero hquad
  unfold discrim at this
  nlinarith [this]

/-! ## Two angular average formulas used in Section 3 -/

/-- avg[Φ(a+γc) − (27/256)(a+γc)²] = Φ(a) − (27/256)a² + ½K(a)γ² + (15/8)a(1−3a)γ⁴ − (5/16)γ⁶ -/
def phiCoef (a γ : ℝ) : ℕ → ℝ
  | 0 => a ^ 5 - a ^ 6 - 27 / 256 * a ^ 2
  | 1 => (5 * a ^ 4 - 6 * a ^ 5 - 27 / 128 * a) * γ
  | 2 => (10 * a ^ 3 - 15 * a ^ 4 - 27 / 256) * γ ^ 2
  | 3 => 10 * a ^ 2 * (1 - 2 * a) * γ ^ 3
  | 4 => 5 * a * (1 - 3 * a) * γ ^ 4
  | 5 => (1 - 6 * a) * γ ^ 5
  | 6 => -γ ^ 6
  | _ => 0

theorem avg_phi_expand (a γ : ℝ) :
    avg (fun x => Φ (a + γ * cos x) - 27 / 256 * (a + γ * cos x) ^ 2)
      = Φ a - 27 / 256 * a ^ 2 + 1 / 2 * Kp a * γ ^ 2 + 15 / 8 * a * (1 - 3 * a) * γ ^ 4
        - 5 / 16 * γ ^ 6 := by
  have e : (fun x => Φ (a + γ * cos x) - 27 / 256 * (a + γ * cos x) ^ 2)
      = fun x => ∑ k ∈ range 7, phiCoef a γ k * cos x ^ k := by
    funext x
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, phiCoef]
    unfold Φ; ring
  unfold avg
  rw [e, int_poly_cos]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, phiCoef]
  rw [int_cos_pow_zero, int_cos_pow_one, mom2, mom3, mom4, mom5, mom6]
  unfold Φ Kp
  field_simp
  ring

/-- Coefficients of (A₂T₂ + A₃T₃ + A₄T₄ + A₅T₅)(c)² as a polynomial in c -/
def rsqCoef (A2 A3 A4 A5 : ℝ) : ℕ → ℝ
  | 0 => (1/1:ℝ)*A2^2 + (-2/1:ℝ)*A2*A4 + (1/1:ℝ)*A4^2
  | 1 => (6/1:ℝ)*A2*A3 + (-10/1:ℝ)*A2*A5 + (-6/1:ℝ)*A3*A4 + (10/1:ℝ)*A4*A5
  | 2 => (-4/1:ℝ)*A2^2 + (20/1:ℝ)*A2*A4 + (-16/1:ℝ)*A4^2 + (9/1:ℝ)*A3^2 + (-30/1:ℝ)*A3*A5 + (25/1:ℝ)*A5^2
  | 3 => (-20/1:ℝ)*A2*A3 + (60/1:ℝ)*A2*A5 + (56/1:ℝ)*A3*A4 + (-120/1:ℝ)*A4*A5
  | 4 => (-48/1:ℝ)*A2*A4 + (80/1:ℝ)*A4^2 + (-24/1:ℝ)*A3^2 + (160/1:ℝ)*A3*A5 + (-200/1:ℝ)*A5^2 + (4/1:ℝ)*A2^2
  | 5 => (-112/1:ℝ)*A2*A5 + (432/1:ℝ)*A4*A5 + (-112/1:ℝ)*A3*A4 + (16/1:ℝ)*A2*A3
  | 6 => (-256/1:ℝ)*A3*A5 + (560/1:ℝ)*A5^2 + (32/1:ℝ)*A2*A4 + (-128/1:ℝ)*A4^2 + (16/1:ℝ)*A3^2
  | 7 => (64/1:ℝ)*A2*A5 + (-576/1:ℝ)*A4*A5 + (64/1:ℝ)*A3*A4
  | 8 => (128/1:ℝ)*A3*A5 + (-640/1:ℝ)*A5^2 + (64/1:ℝ)*A4^2
  | 9 => (256/1:ℝ)*A4*A5
  | 10 => (256/1:ℝ)*A5^2
  | _ => 0

/-- avg[(A₂T₂ + A₃T₃ + A₄T₄ + A₅T₅)(c)²] = ½(A₂² + A₃² + A₄² + A₅²) (orthogonality of Chebyshev polynomials) -/
theorem avg_R_sq (A2 A3 A4 A5 : ℝ) :
    avg (fun x => (A2 * Prop31Alg.T2 (cos x) + A3 * Prop31Alg.T3 (cos x)
      + A4 * Prop31Alg.T4 (cos x) + A5 * Prop31Alg.T5 (cos x)) ^ 2)
      = 1 / 2 * (A2 ^ 2 + A3 ^ 2 + A4 ^ 2 + A5 ^ 2) := by
  have e : (fun x => (A2 * Prop31Alg.T2 (cos x) + A3 * Prop31Alg.T3 (cos x)
      + A4 * Prop31Alg.T4 (cos x) + A5 * Prop31Alg.T5 (cos x)) ^ 2)
      = fun x => ∑ k ∈ range 11, rsqCoef A2 A3 A4 A5 k * cos x ^ k := by
    funext x
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, rsqCoef]
    unfold Prop31Alg.T2 Prop31Alg.T3 Prop31Alg.T4 Prop31Alg.T5; ring
  unfold avg
  rw [e, int_poly_cos]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, rsqCoef]
  rw [int_cos_pow_zero, int_cos_pow_one, mom2, mom3, mom4, mom5, mom6, mom7, mom8, mom9, mom10]
  field_simp
  ring

/-- Averages of Re θ^{2j}: avg cos = 0 -/
lemma avg_cos : avg (fun x => cos x) = 0 := by
  unfold avg; simp [integral_cos]

/-! ## §2.1: numerical values of the Bessel integrals α_{2n} (literature) -/

/-- Numerical part of OST17 Theorem 1.1(i): n ≥ 4 ⇒ 3/(8π²n) + 1/(8000n⁴) < 19/1000 -/
theorem ost17_tail {n : ℝ} (hn : 4 ≤ n) : 3 / (8 * π ^ 2 * n) + 1 / (8000 * n ^ 4) < 19 / 1000 := by
  have hp := Real.pi_gt_three
  have h1 : 3 / (8 * π ^ 2 * n) ≤ 3 / (8 * 9 * 4) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    have : (9 : ℝ) ≤ π ^ 2 := by nlinarith
    nlinarith
  have h2 : 1 / (8000 * n ^ 4) ≤ 1 / (8000 * 4 ^ 4) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    have : (4 : ℝ) ^ 4 ≤ n ^ 4 := pow_le_pow_left₀ (by norm_num) hn 4
    linarith
  have : (3 : ℝ) / (8 * 9 * 4) + 1 / (8000 * 4 ^ 4) < 19 / 1000 := by norm_num
  linarith

/-- Numerical values from the literature (CFOT17 Table 1, OST17 Theorem 1.1(i)) as hypotheses; `α n` denotes α_{2n}. -/
structure AlphaLit (α : ℕ → ℝ) : Prop where
  table0 : 101 / 300 < α 0 ∧ α 0 < 337 / 1000
  table1 : α 1 < 37 / 1000
  table23 : α 2 < 19 / 1000 ∧ α 3 < 19 / 1000
  ost : ∀ n : ℕ, 4 ≤ n → α n ≤ 3 / (8 * π ^ 2 * n) + 1 / (8000 * (n : ℝ) ^ 4)

/-- eq:bessel-global -/
theorem bessel_global {α : ℕ → ℝ} (h : AlphaLit α) :
    101 / 300 < α 0 ∧ α 0 < 337 / 1000 ∧ α 1 < 37 / 1000 ∧ ∀ n, 2 ≤ n → α n < 19 / 1000 := by
  refine ⟨h.table0.1, h.table0.2, h.table1, ?_⟩
  intro n hn
  rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
  · exact h.table23.1
  · exact h.table23.2
  · exact lt_of_le_of_lt (h.ost n h4) (ost17_tail (by exact_mod_cast h4))

/-! ## eq:prop31-a and the upper bound for Σα_{2n}a_{2n}²
Notation: `a n` = a_{2(n+1)}, `α' n` = α_{2(n+1)} (n ≥ 0). -/

/-- eq:prop31-a: if α_{2n} < α₀/9 (n ≥ 1) and Σ a_{2n}² = 1 − a₀² > 0, then Σα_{2n}a_{2n}² < (α₀/9)(1−a₀²) -/
theorem prop31a {α' a : ℕ → ℝ} {α0 a0 S : ℝ} (hα : ∀ n, α' n < α0 / 9)
    (hpars : HasSum (fun n => a n ^ 2) (1 - a0 ^ 2)) (hpos : 0 < 1 - a0 ^ 2)
    (hS : HasSum (fun n => α' n * a n ^ 2) S) : S < α0 / 9 * (1 - a0 ^ 2) := by
  have hne : ∃ i, a i ≠ 0 := by
    by_contra h
    push_neg at h
    have : HasSum (fun n => a n ^ 2) 0 := by
      have e : (fun n => a n ^ 2) = fun _ => 0 := by funext n; rw [h n]; ring
      rw [e]; exact hasSum_zero
    have := this.unique hpars
    linarith
  obtain ⟨i, hi⟩ := hne
  have hg : HasSum (fun n => α0 / 9 * a n ^ 2) (α0 / 9 * (1 - a0 ^ 2)) := hpars.mul_left _
  refine hasSum_lt (f := fun n => α' n * a n ^ 2) (g := fun n => α0 / 9 * a n ^ 2) (i := i)
    (fun n => mul_le_mul_of_nonneg_right (hα n).le (sq_nonneg _)) ?_ hS hg
  exact mul_lt_mul_of_pos_right (hα i) (by positivity)

/-- From eq:a2-bound and eq:bessel-global: Σα_{2n}a_{2n}² ≤ (19/1000)(1−a₀²) + 9/1000 -/
theorem sum_alpha_bound {α' a : ℕ → ℝ} {a0 S : ℝ} (h1 : α' 0 < 37 / 1000)
    (h2 : ∀ n, 1 ≤ n → α' n < 19 / 1000) (ha2 : a 0 ^ 2 ≤ 1 / 2)
    (hpars : HasSum (fun n => a n ^ 2) (1 - a0 ^ 2))
    (hS : HasSum (fun n => α' n * a n ^ 2) S) : S ≤ 19 / 1000 * (1 - a0 ^ 2) + 9 / 1000 := by
  set g : ℕ → ℝ := fun n => 19 / 1000 * a n ^ 2 + if n = 0 then 18 / 1000 * a 0 ^ 2 else 0
  have hg : HasSum g (19 / 1000 * (1 - a0 ^ 2) + 18 / 1000 * a 0 ^ 2) :=
    (hpars.mul_left _).add (hasSum_ite_eq 0 _)
  have hle : ∀ n, α' n * a n ^ 2 ≤ g n := by
    intro n
    simp only [g]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [if_true]
      have := mul_le_mul_of_nonneg_right h1.le (sq_nonneg (a 0))
      linarith
    · rw [if_neg (by omega)]
      have := mul_le_mul_of_nonneg_right (h2 n hn).le (sq_nonneg (a n))
      linarith
  have := hasSum_le hle hS hg
  linarith

/-- γ(r) = √2·t·a₂·J₂/J₀ ≤ 1/3 (t = 5/12), from 0 ≤ J₂/J₀ < 4/5 and a₂ ≤ 1/√2 -/
theorem gamma_le {a2 q : ℝ} (ha2 : 0 ≤ a2) (ha2' : a2 ^ 2 ≤ 1 / 2) (hq0 : 0 ≤ q)
    (hq : q < 4 / 5) : 0 ≤ Real.sqrt 2 * (5 / 12) * a2 * q ∧ Real.sqrt 2 * (5 / 12) * a2 * q ≤ 1 / 3 := by
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  refine ⟨by positivity, ?_⟩
  have h2 : Real.sqrt 2 * a2 ≤ 1 := by
    have hsq : (Real.sqrt 2 * a2) ^ 2 ≤ 1 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]; linarith
    nlinarith [sq_nonneg (Real.sqrt 2 * a2 - 1), mul_nonneg hs ha2]
  have h3 : Real.sqrt 2 * a2 * q ≤ 4 / 5 := by
    have := mul_le_mul h2 hq.le hq0 (by norm_num)
    linarith
  nlinarith

/-! ## §2.2: the Φ-identity from the EL equation (algebraic part) -/

/-- If ∫(Ef)⁵Ee₀ = (2π)⁴μa₀ and ∫(Ef)⁶ = (2π)⁴μ, then for t > 0:
∫[(tEf)⁵Ee₀ − (tEf)⁶] = (2π)⁴μt⁵(a₀−t) -/
theorem phi_identity_alg {G G0 : ℝ × ℝ → ℝ} {μ a0 t : ℝ}
    (hi5 : Integrable (fun x => G x ^ 5 * G0 x)) (hi6 : Integrable (fun x => G x ^ 6))
    (h5 : ∫ x, G x ^ 5 * G0 x = (2 * π) ^ 4 * μ * a0) (h6 : ∫ x, G x ^ 6 = (2 * π) ^ 4 * μ) :
    ∫ x, ((t * G x) ^ 5 * G0 x - (t * G x) ^ 6) = (2 * π) ^ 4 * μ * t ^ 5 * (a0 - t) := by
  have e : (fun x => (t * G x) ^ 5 * G0 x - (t * G x) ^ 6)
      = fun x => t ^ 5 * (G x ^ 5 * G0 x) - t ^ 6 * G x ^ 6 := by funext x; ring
  rw [e, integral_sub (hi5.const_mul _) (hi6.const_mul _), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, h5, h6]
  ring

/-! ## §2.3: consequences of the Fourier formula for Q -/

/-- From eq:Q-Fourier: Q = (2/π)G² − (4/π)Σ_{n≥1}|ĝ_n|²/(4n²−1) (`c n` = |∫gω^{2(n+1)}|²)
we get Q ≤ (2/π)G² and Q ≤ (2/π)G² − (4/(3π))c₀ -/
theorem Q_bounds {c : ℕ → ℝ} {Q G s : ℝ} (hc : ∀ n, 0 ≤ c n)
    (hs : HasSum (fun n : ℕ => c n / (4 * ((n : ℝ) + 1) ^ 2 - 1)) s)
    (hQ : Q = 2 / π * G ^ 2 - 4 / π * s) :
    Q ≤ 2 / π * G ^ 2 ∧ Q ≤ 2 / π * G ^ 2 - 4 / (3 * π) * c 0 := by
  have hp := pi_pos
  have hterm : ∀ n : ℕ, 0 ≤ c n / (4 * ((n : ℝ) + 1) ^ 2 - 1) := by
    intro n
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact div_nonneg (hc n) (by nlinarith)
  have hs0 : c 0 / 3 ≤ s := by
    have := hs.nonneg hterm
    have h0 := le_hasSum hs 0 (fun j _ => hterm j)
    norm_num at h0
    linarith
  have hsnn : 0 ≤ s := hs.nonneg hterm
  constructor
  · rw [hQ]; have : 0 ≤ 4 / π * s := by positivity
    linarith
  · rw [hQ]
    have : 4 / (3 * π) * c 0 ≤ 4 / π * s := by
      have e : 4 / (3 * π) * c 0 = 4 / π * (c 0 / 3) := by field_simp
      rw [e]; exact mul_le_mul_of_nonneg_left hs0 (by positivity)
    linarith

/-! ## §2.3: upper bound for ρ = σ*³ (eq:density-upper) -/

/-- (r+1)³(3−r)/(16r) = 1 − (r−1)³(r+3)/(16r), and it lies in (0,1) for 1 < r < 3 -/
theorem k_sq_identity {r : ℝ} (hr1 : 1 < r) (hr3 : r < 3) :
    (r + 1) ^ 3 * (3 - r) / (16 * r) = 1 - (r - 1) ^ 3 * (r + 3) / (16 * r) ∧
    0 < (r + 1) ^ 3 * (3 - r) / (16 * r) ∧ (r + 1) ^ 3 * (3 - r) / (16 * r) < 1 := by
  have hr : 0 < r := by linarith
  refine ⟨by field_simp; ring, by positivity, ?_⟩
  rw [div_lt_one (by positivity)]
  nlinarith [pow_pos (sub_pos.2 hr1) 3, mul_pos (pow_pos (sub_pos.2 hr1) 3) (by linarith : (0:ℝ) < r + 3)]

/-- From ρ(r)² ≤ 16π²/√(r(r−1)³(r+3)) we get ρ(r) ≤ 4π/(√3(r−1)) for 1 < r < 3 -/
theorem rho_bound {r ρ : ℝ} (hr1 : 1 < r) (hr3 : r < 3) (hρ : 0 ≤ ρ)
    (h : ρ ^ 2 ≤ 16 * π ^ 2 / Real.sqrt (r * (r - 1) ^ 3 * (r + 3))) :
    ρ ≤ 4 * π / (Real.sqrt 3 * (r - 1)) := by
  have hp := pi_pos
  have hr1' : 0 < r - 1 := by linarith
  have hkey : 9 * (r - 1) ^ 4 ≤ r * (r - 1) ^ 3 * (r + 3) := by
    have : 9 * (r - 1) ≤ r * (r + 3) := by nlinarith [sq_nonneg (r - 3)]
    have h3 : 0 ≤ (r - 1) ^ 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h3]
  have hsq : 3 * (r - 1) ^ 2 ≤ Real.sqrt (r * (r - 1) ^ 3 * (r + 3)) := by
    rw [show 3 * (r - 1) ^ 2 = Real.sqrt ((3 * (r - 1) ^ 2) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt; nlinarith
  have h2 : ρ ^ 2 ≤ 16 * π ^ 2 / (3 * (r - 1) ^ 2) :=
    h.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hsq)
  have e : (4 * π / (Real.sqrt 3 * (r - 1))) ^ 2 = 16 * π ^ 2 / (3 * (r - 1) ^ 2) := by
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; ring
  rw [← e] at h2
  exact (pow_le_pow_iff_left₀ hρ (by positivity) two_ne_zero).mp h2

end

end SteinTomas.Section2

#print axioms SteinTomas.Section2.avg_R_sq
#print axioms SteinTomas.Section2.avg_phi_expand
#print axioms SteinTomas.Section2.cs_avg
