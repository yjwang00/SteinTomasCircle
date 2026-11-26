import Mathlib
import SteinTomasCircle.Basic.Elementary

/-!
# Analysis layer (I): analytic facts not depending on the definition of Bessel functions

* Σ_{n≥1} 1/(4n²−1) = 1/2 (used in the proof of Lemma 4.4)
* the three polynomial integrals at the end of Lemma 2.1 (exact values)
* the pointwise Bessel estimates of Lemma 2.1: assuming the power series DLMF 10.2.2 (in HasSum form),
  derived from truncation estimates for alternating series
* the tail estimate of Lemma 2.1: (r/2)^{2n}/(2n)! ≤ κ(r) for n ≥ 2, 0 ≤ r ≤ 7/4
-/

namespace SteinTomas.Analysis1

open Real Finset Filter Topology

/-! ## Σ 1/(4n²−1) = 1/2 -/

lemma partial_sum (N : ℕ) :
    ∑ n ∈ range N, (1 : ℝ) / (4 * ((n : ℝ) + 1) ^ 2 - 1) = (1 : ℝ) / 2 - 1 / (2 * (2 * (N : ℝ) + 1)) := by
  induction N with
  | zero => norm_num
  | succ k ih =>
    rw [sum_range_succ, ih]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 : (4 * ((k : ℝ) + 1) ^ 2 - 1) ≠ 0 := by nlinarith
    have h2 : (2 * (2 * (k : ℝ) + 1)) ≠ 0 := by positivity
    have h3 : (2 * (2 * ((k + 1 : ℕ) : ℝ) + 1)) ≠ 0 := by positivity
    push_cast at h3 ⊢
    field_simp
    try ring

theorem hasSum_inv_four_sq_sub_one :
    HasSum (fun n : ℕ => (1 : ℝ) / (4 * ((n : ℝ) + 1) ^ 2 - 1)) (1 / 2) := by
  have hnn : ∀ n : ℕ, 0 ≤ (1 : ℝ) / (4 * ((n : ℝ) + 1) ^ 2 - 1) := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact div_nonneg zero_le_one (by nlinarith)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  simp_rw [partial_sum]
  have hlim : Tendsto (fun N : ℕ => 1 / (2 * (2 * (N : ℝ) + 1))) atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    apply tendsto_atTop_mono (fun N => ?_) tendsto_natCast_atTop_atTop
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub hlim
  simpa using this

/-! ## Polynomial integrals in Lemma 2.1 (exact values) -/

theorem integral_V : ∫ t in (0:ℝ)..1, t ^ 2 * (1 - t) ^ 8 * (1 - t / 2) = 7/3960 := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun y : ℝ => (1/3:ℝ) * y ^ 3 + (-17/8:ℝ) * y ^ 4 + (32/5:ℝ) * y ^ 5 + (-35/3:ℝ) * y ^ 6 + (14:ℝ) * y ^ 7 + (-91/8:ℝ) * y ^ 8 + (56/9:ℝ) * y ^ 9 + (-11/5:ℝ) * y ^ 10 + (5/11:ℝ) * y ^ 11 + (-1/24:ℝ) * y ^ 12) (x ^ 2 * (1 - x) ^ 8 * (1 - x / 2)) x := by
    intro x _
    have h := (((((((((((hasDerivAt_pow 3 x).const_mul (1/3:ℝ)).add ((hasDerivAt_pow 4 x).const_mul (-17/8:ℝ))).add ((hasDerivAt_pow 5 x).const_mul (32/5:ℝ))).add ((hasDerivAt_pow 6 x).const_mul (-35/3:ℝ))).add ((hasDerivAt_pow 7 x).const_mul (14:ℝ))).add ((hasDerivAt_pow 8 x).const_mul (-91/8:ℝ))).add ((hasDerivAt_pow 9 x).const_mul (56/9:ℝ))).add ((hasDerivAt_pow 10 x).const_mul (-11/5:ℝ))).add ((hasDerivAt_pow 11 x).const_mul (5/11:ℝ))).add ((hasDerivAt_pow 12 x).const_mul (-1/24:ℝ)))
    convert h using 1
    norm_num
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t : ℝ => t ^ 2 * (1 - t) ^ 8 * (1 - t / 2)).intervalIntegrable _ _)]
  norm_num

theorem integral_U : ∫ t in (0:ℝ)..(2/5), t ^ 4 * (1 - t) ^ 8 = 157948768/1571044921875 := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) (2/5), HasDerivAt (fun y : ℝ => (1/5:ℝ) * y ^ 5 + (-4/3:ℝ) * y ^ 6 + (4:ℝ) * y ^ 7 + (-7:ℝ) * y ^ 8 + (70/9:ℝ) * y ^ 9 + (-28/5:ℝ) * y ^ 10 + (28/11:ℝ) * y ^ 11 + (-2/3:ℝ) * y ^ 12 + (1/13:ℝ) * y ^ 13) (x ^ 4 * (1 - x) ^ 8) x := by
    intro x _
    have h := ((((((((((hasDerivAt_pow 5 x).const_mul (1/5:ℝ)).add ((hasDerivAt_pow 6 x).const_mul (-4/3:ℝ))).add ((hasDerivAt_pow 7 x).const_mul (4:ℝ))).add ((hasDerivAt_pow 8 x).const_mul (-7:ℝ))).add ((hasDerivAt_pow 9 x).const_mul (70/9:ℝ))).add ((hasDerivAt_pow 10 x).const_mul (-28/5:ℝ))).add ((hasDerivAt_pow 11 x).const_mul (28/11:ℝ))).add ((hasDerivAt_pow 12 x).const_mul (-2/3:ℝ))).add ((hasDerivAt_pow 13 x).const_mul (1/13:ℝ)))
    convert h using 1
    norm_num
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t : ℝ => t ^ 4 * (1 - t) ^ 8).intervalIntegrable _ _)]
  norm_num

theorem integral_W : ∫ t in (0:ℝ)..(3/8), ((1 - t) ^ 12 - 4 / 3 * t ^ 3 * (1 - t) ^ 10) = 168338674201695/2201222278807552 := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) (3/8), HasDerivAt (fun y : ℝ => (1:ℝ) * y ^ 1 + (-6:ℝ) * y ^ 2 + (22:ℝ) * y ^ 3 + (-166/3:ℝ) * y ^ 4 + (305/3:ℝ) * y ^ 5 + (-142:ℝ) * y ^ 6 + (1084/7:ℝ) * y ^ 7 + (-134:ℝ) * y ^ 8 + (277/3:ℝ) * y ^ 9 + (-50:ℝ) * y ^ 10 + (226/11:ℝ) * y ^ 11 + (-6:ℝ) * y ^ 12 + (43/39:ℝ) * y ^ 13 + (-2/21:ℝ) * y ^ 14) (((1 - x) ^ 12 - 4 / 3 * x ^ 3 * (1 - x) ^ 10)) x := by
    intro x _
    have h := (((((((((((((((hasDerivAt_pow 1 x).const_mul (1:ℝ)).add ((hasDerivAt_pow 2 x).const_mul (-6:ℝ))).add ((hasDerivAt_pow 3 x).const_mul (22:ℝ))).add ((hasDerivAt_pow 4 x).const_mul (-166/3:ℝ))).add ((hasDerivAt_pow 5 x).const_mul (305/3:ℝ))).add ((hasDerivAt_pow 6 x).const_mul (-142:ℝ))).add ((hasDerivAt_pow 7 x).const_mul (1084/7:ℝ))).add ((hasDerivAt_pow 8 x).const_mul (-134:ℝ))).add ((hasDerivAt_pow 9 x).const_mul (277/3:ℝ))).add ((hasDerivAt_pow 10 x).const_mul (-50:ℝ))).add ((hasDerivAt_pow 11 x).const_mul (226/11:ℝ))).add ((hasDerivAt_pow 12 x).const_mul (-6:ℝ))).add ((hasDerivAt_pow 13 x).const_mul (43/39:ℝ))).add ((hasDerivAt_pow 14 x).const_mul (-2/21:ℝ)))
    convert h using 1
    norm_num
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t : ℝ => ((1 - t) ^ 12 - 4 / 3 * t ^ 3 * (1 - t) ^ 10)).intervalIntegrable _ _)]
  norm_num

theorem V_numeric : 4 * (7 / 3960 : ℝ) = 7 / 990 ∧ (7 / 990 : ℝ) < 3 / 400 := by norm_num
theorem U_numeric : (1 / 9 : ℝ) * (157948768 / 1571044921875) < 3 / 250000 := by norm_num
theorem W_numeric : (3059 / 10000 : ℝ) < 4 * (168338674201695 / 2201222278807552) := by norm_num

/-! ## Pointwise estimates of Lemma 2.1 (hypothesis: the power series DLMF 10.2.2) -/

/-- The terms of J₀(2√x) = Σ (−1)^m x^m/(m!)² are decreasing (0 ≤ x ≤ 1) -/
lemma antitone_J0_terms {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (fun m : ℕ => x ^ m / ((m.factorial : ℝ)) ^ 2) := by
  apply antitone_nat_of_succ_le
  intro m
  rw [Nat.factorial_succ]
  push_cast
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have key := mul_le_mul_of_nonneg_left (show x ≤ ((m : ℝ) + 1) ^ 2 by nlinarith)
    (by positivity : (0 : ℝ) ≤ x ^ m * (m.factorial : ℝ) ^ 2)
  rw [pow_succ]
  nlinarith [key]

/-- The terms of J₂(2√x) = Σ (−1)^m x^{m+1}/(m!(m+2)!) are decreasing (0 ≤ x ≤ 1) -/
lemma antitone_J2_terms {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (fun m : ℕ => x ^ (m + 1) / ((m.factorial : ℝ) * ((m + 2).factorial : ℝ))) := by
  apply antitone_nat_of_succ_le
  intro m
  rw [show m + 1 + 2 = (m + 2) + 1 by ring, Nat.factorial_succ (m + 2), Nat.factorial_succ m]
  push_cast
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hf2 : (0 : ℝ) < (m + 2).factorial := by exact_mod_cast Nat.factorial_pos (m + 2)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have key := mul_le_mul_of_nonneg_left
    (show x ≤ ((m : ℝ) + 1) * (((m + 2 : ℕ) : ℝ) + 1) by push_cast; nlinarith)
    (by positivity : (0 : ℝ) ≤ x ^ (m + 1) * ((m.factorial : ℝ) * ((m + 2).factorial : ℝ)))
  push_cast at key
  rw [pow_succ x (m + 1)]
  nlinarith [key]

/-- Bounds for J₀: 1 − x + x²/4 − x³/36 ≤ J₀ ≤ 1 − x + x²/4 -/
theorem J0_bounds {x j0 : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hs : HasSum (fun m : ℕ => (-1) ^ m * (x ^ m / ((m.factorial : ℝ)) ^ 2)) j0) :
    1 - x + x ^ 2 / 4 - x ^ 3 / 36 ≤ j0 ∧ j0 ≤ 1 - x + x ^ 2 / 4 := by
  have ht := hs.tendsto_sum_nat
  have ha := antitone_J0_terms hx0 hx1
  have lo := Antitone.alternating_series_le_tendsto ht ha 2
  have hi := Antitone.tendsto_le_alternating_series ht ha 1
  simp [Finset.sum_range_succ, Nat.factorial] at lo hi
  constructor <;> nlinarith [lo, hi]

/-- Bounds for J₂: x/2 − x²/6 ≤ J₂ ≤ x/2 − x²/6 + x³/48 -/
theorem J2_bounds {x j2 : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hs : HasSum (fun m : ℕ => (-1) ^ m *
      (x ^ (m + 1) / ((m.factorial : ℝ) * ((m + 2).factorial : ℝ)))) j2) :
    x / 2 - x ^ 2 / 6 ≤ j2 ∧ j2 ≤ x / 2 - x ^ 2 / 6 + x ^ 3 / 48 := by
  have ht := hs.tendsto_sum_nat
  have ha := antitone_J2_terms hx0 hx1
  have lo := Antitone.alternating_series_le_tendsto ht ha 1
  have hi := Antitone.tendsto_le_alternating_series ht ha 1
  simp [Finset.sum_range_succ, Nat.factorial] at lo hi
  constructor <;> nlinarith [lo, hi]

/-- Lemma 2.1 (eq:bessel-pointwise): J₀ > 0, 0 ≤ J₂/J₀ < 4/5, J₂² ≤ 10·J₀·κ, κ = x²/24 -/
theorem bessel_pointwise {x j0 j2 : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 49 / 64)
    (h0 : HasSum (fun m : ℕ => (-1) ^ m * (x ^ m / ((m.factorial : ℝ)) ^ 2)) j0)
    (h2 : HasSum (fun m : ℕ => (-1) ^ m *
      (x ^ (m + 1) / ((m.factorial : ℝ) * ((m + 2).factorial : ℝ)))) j2) :
    0 < j0 ∧ 0 ≤ j2 ∧ j2 < 4 / 5 * j0 ∧ j2 ^ 2 ≤ 10 * j0 * (x ^ 2 / 24) := by
  obtain ⟨l0, -⟩ := J0_bounds hx0 (by linarith) h0
  obtain ⟨l2, u2⟩ := J2_bounds hx0 (by linarith) h2
  have hp1 := p1_pos hx0 hx1
  have hratio := lem21_ratio hx0 hx1
  have h5 := lem21_pos hx0 hx1
  unfold p1 at hp1 hratio h5
  unfold p2 at hratio h5
  have hj0 : 0 < j0 := by linarith
  have hj2 : 0 ≤ j2 := by nlinarith
  refine ⟨hj0, hj2, by nlinarith, ?_⟩
  -- j2² ≤ (x p₂/2)² ≤ (5/12) x² p₁ ≤ (5/12) x² j₀
  have hp2 : 0 ≤ 1 - x / 3 + x ^ 2 / 24 := by nlinarith
  have hup : j2 ≤ x / 2 * (1 - x / 3 + x ^ 2 / 24) := by nlinarith
  have hsq : j2 ^ 2 ≤ (x / 2 * (1 - x / 3 + x ^ 2 / 24)) ^ 2 := pow_le_pow_left₀ hj2 hup 2
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  nlinarith [mul_le_mul_of_nonneg_left h5.le hx2, mul_le_mul_of_nonneg_left l0 hx2]

/-! ## Tail estimate of Lemma 2.1 -/

/-- For n ≥ 2, 0 ≤ y ≤ 1: y^{2n}/(2n)! ≤ y⁴/4! (in the paper y = r/2 ≤ 7/8) -/
theorem tail_le_kappa {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∀ n : ℕ, 2 ≤ n → y ^ (2 * n) / ((2 * n).factorial : ℝ) ≤ y ^ 4 / 24 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ k hk ih =>
    refine le_trans ?_ ih
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    have hf : (0 : ℝ) < (2 * k).factorial := by exact_mod_cast Nat.factorial_pos _
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hy2 : y ^ 2 ≤ 1 := by nlinarith
    have key := mul_le_mul_of_nonneg_left
      (show y ^ 2 ≤ (2 * (k : ℝ) + 1 + 1) * (2 * (k : ℝ) + 1) by nlinarith)
      (by positivity : (0 : ℝ) ≤ y ^ (2 * k) * ((2 * k).factorial : ℝ))
    rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring, pow_add]
    nlinarith [key]

end SteinTomas.Analysis1

#print axioms SteinTomas.Analysis1.hasSum_inv_four_sq_sub_one
#print axioms SteinTomas.Analysis1.integral_W
#print axioms SteinTomas.Analysis1.bessel_pointwise
#print axioms SteinTomas.Analysis1.tail_le_kappa
