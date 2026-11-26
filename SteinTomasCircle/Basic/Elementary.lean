import Mathlib

/-!
# Elementary and numerical parts of the paper (no literature input)

Corresponding to the paper: §2.2 (Φ), the polynomial part of Lemma 2.1, the polynomial H at the end of Prop 3.1,
the algebraic identity of Lemma 4.3 (lem:four-sign) and the values of ψ, the numerical contradiction in Prop 5.3 (prop:small-mean).
-/

namespace SteinTomas

open Real

noncomputable section

/-- Φ(x) = x⁵ − x⁶ -/
def Φ (x : ℝ) : ℝ := x ^ 5 - x ^ 6

/-- K(x) = 10x³ − 15x⁴ − 27/256 from the paper (inside the proof of Prop 3.1) -/
def Kp (x : ℝ) : ℝ := 10 * x ^ 3 - 15 * x ^ 4 - 27 / 256

/-- t = 5/12 -/
def tt : ℝ := 5 / 12

/-- The polynomial H at the end of Prop 3.1 -/
def H (x : ℝ) : ℝ :=
  3059 / 10000 * Φ (tt * x) - 337 / 1000 * tt ^ 5 * (x - tt) + 3 / 800 * tt ^ 2 * Kp (tt * x)
    + 27 / 256 * tt ^ 2 * (121 / 10000 * x ^ 2 + 7 / 250) + 1 / 125000

/-! ## §2.2: two inequalities for Φ -/

theorem phi_le (x : ℝ) : Φ x ≤ 27 / 256 * x ^ 2 := by
  unfold Φ
  have hq : 0 < x ^ 2 + x / 2 + 3 / 16 := by nlinarith [sq_nonneg (x + 1 / 4)]
  have h : 0 ≤ x ^ 2 * (x - 3 / 4) ^ 2 * (x ^ 2 + x / 2 + 3 / 16) :=
    mul_nonneg (mul_nonneg (sq_nonneg x) (sq_nonneg (x - 3 / 4))) hq.le
  nlinarith [h]

/-! ## Elementary steps in Prop 3.1 (prop:large-mean) -/

theorem prop31_identity (a : ℝ) :
    1 - 3 * a + 5 / 18 * (1 + 8 * a ^ 2) - a + 1 / 2 = 4 / 9 * (a - 1) * (5 * a - 4) := by
  ring

/-- From 0 < (4/9)(a₀−1)(5a₀−4) and a₀ < 1 we get a₀ < 4/5 -/
theorem prop31_step1 {a : ℝ} (ha : a < 1)
    (h : 0 < 1 - 3 * a + 5 / 18 * (1 + 8 * a ^ 2) - a + 1 / 2) : a < 4 / 5 := by
  rw [prop31_identity] at h
  by_contra hc
  have hc' := not_lt.mp hc
  nlinarith

theorem prop31_coef : (15 : ℝ) / 8 * (25 / 96) * (1 - 75 / 96) < 7 / 64 := by norm_num

theorem Kp_quarter : Kp (1 / 4) = -1 / 128 := by unfold Kp; norm_num

theorem prop31_U_coef :
    (175 : ℝ) / 512 + 53 / (256 * 9) + 10 * (3 / 40) * (1 / 2) * (4 / 5) < 2 / 3 := by norm_num

theorem prop31_t_facts :
    tt ^ 4 < 1 / 32 ∧ tt ^ 3 < 3 / 40 ∧ tt ^ 2 * (39 / 64) < 1 / 9 ∧ 0 < 27 / 256 - tt ^ 2 / 4 := by
  unfold tt; norm_num

theorem H_at_five_eighths : H (5 / 8) < 0 := by unfold H Φ Kp tt; norm_num
theorem H_at_four_fifths : H (4 / 5) < 0 := by unfold H Φ Kp tt; norm_num

/-- Auxiliary polynomial: H(x) − chord = (x−5/8)(x−4/5)·G(x), with G positive on the interval (equivalent to the convexity argument) -/
def G (x : ℝ) : ℝ :=
  3873932777 / 978447237120 + 16220687 / 4529848320 * x + 8347357 / 3057647616 * x ^ 2
    + 198835 / 127401984 * x ^ 3 - 76475 / 47775744 * x ^ 4

theorem H_decomp (x : ℝ) :
    H x = (1442261633731 / 6115295232000000 - 4967146517 / 13045963161600 * x)
      + (x - 5 / 8) * (x - 4 / 5) * G x := by
  unfold H Φ Kp tt G; ring

theorem G_pos {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 4 / 5) : 0 < G x := by
  have hx4 : x ^ 4 ≤ (4 / 5 : ℝ) ^ 4 := by gcongr
  unfold G
  nlinarith [pow_nonneg h0 2, pow_nonneg h0 3]

/-- Last step of Prop 3.1: H < 0 on [5/8, 4/5] -/
theorem H_neg {x : ℝ} (h0 : 5 / 8 ≤ x) (h1 : x ≤ 4 / 5) : H x < 0 := by
  rw [H_decomp]
  have hg := G_pos (by linarith) h1
  have hp : (x - 5 / 8) * (x - 4 / 5) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have := mul_nonpos_of_nonpos_of_nonneg hp hg.le
  linarith

/-! ## Polynomial part of Lemma 2.1 (lem:local-bessel), x = r²/4 ∈ [0, 49/64] -/

def p1 (x : ℝ) : ℝ := 1 - x + x ^ 2 / 4 - x ^ 3 / 36
def p2 (x : ℝ) : ℝ := 1 - x / 3 + x ^ 2 / 24

theorem lem21_identity (x : ℝ) :
    5 * p1 x - 3 * p2 x ^ 2 = 2 - 3 * x + 2 / 3 * x ^ 2 - x ^ 3 / 18 - x ^ 4 / 192 := by
  unfold p1 p2; ring

theorem lem21_pos {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 49 / 64) : 0 < 5 * p1 x - 3 * p2 x ^ 2 := by
  rw [lem21_identity]
  nlinarith [pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4, mul_nonneg h0 h0]

theorem p1_pos {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 49 / 64) : 0 < p1 x := by
  unfold p1; nlinarith [pow_nonneg h0 2, pow_nonneg h0 3]

/-- Polynomial inequality needed for J₂/J₀ < 4/5: x·p₂(x) < (8/5)·p₁(x) -/
theorem lem21_ratio {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 49 / 64) : x * p2 x < 8 / 5 * p1 x := by
  unfold p1 p2; nlinarith [pow_nonneg h0 2, pow_nonneg h0 3, mul_nonneg h0 (sub_nonneg.2 h1)]

/-! ## Lemma 4.3 (lem:four-sign) -/

/-- ψ(λ) = 1/8 + λ/(16(3+√(1+λ))) -/
noncomputable def ψ (l : ℝ) : ℝ := 1 / 8 + l / (16 * (3 + Real.sqrt (1 + l)))

theorem two_psi_eight : 2 * ψ 8 = 5 / 12 := by
  unfold ψ
  rw [show (1 : ℝ) + 8 = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

theorem three_psi_ten_thirds : 3 * ψ (10 / 3) < 1 / 2 := by
  unfold ψ
  have hs : (2 : ℝ) < Real.sqrt (1 + 10 / 3) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < 16 * (3 + Real.sqrt (1 + 10 / 3)) := by positivity
  have hq : (10 / 3 : ℝ) / (16 * (3 + Real.sqrt (1 + 10 / 3))) < 1 / 24 := by
    rw [div_lt_iff₀ hpos]; nlinarith
  linarith

/-- Values of λ in normalized coordinates: ω=(a,b), η=(a,−b), ζ=(c,d) -/
theorem lam_identities (a b c d : ℝ) (h1 : a ^ 2 + b ^ 2 = 1) (h2 : c ^ 2 + d ^ 2 = 1) :
    (2 * a + c) ^ 2 + d ^ 2 - 1 = 4 * a * (a + c) ∧
    c ^ 2 + (2 * b + d) ^ 2 - 1 = 4 * b * (b + d) ∧
    c ^ 2 + (d - 2 * b) ^ 2 - 1 = 4 * b * (b - d) ∧
    (c - 2 * a) ^ 2 + d ^ 2 - 1 = 4 * a * (a - c) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linear_combination h2

theorem lam_sum (a b c : ℝ) (h1 : a ^ 2 + b ^ 2 = 1) (d : ℝ) :
    4 * a * (a + c) + 4 * b * (b + d) + 4 * b * (b - d) = 8 + 4 * a * (c - a) := by
  linear_combination 8 * h1

theorem lam_pair_products (a b c d : ℝ) (h1 : a ^ 2 + b ^ 2 = 1) (h2 : c ^ 2 + d ^ 2 = 1) :
    (4 * a * (a + c)) * (4 * b * (b + d)) + (4 * a * (a + c)) * (4 * b * (b - d))
      + (4 * b * (b + d)) * (4 * b * (b - d)) = 4 * (2 * b * (a + c)) ^ 2 := by
  linear_combination (16 * b ^ 2) * (h1 - h2)

/-! ## Numerical contradiction in Prop 5.3 (prop:small-mean) -/

theorem small_mean_Q_numeric :
    75 * π ^ 2 / 8 * (25 * π / 32) * (75 / (404 * π ^ 4)) < 13 / 30 := by
  have hp := Real.pi_gt_d2
  have hpos : 0 < π := Real.pi_pos
  have e : 75 * π ^ 2 / 8 * (25 * π / 32) * (75 / (404 * π ^ 4)) = 140625 / (103424 * π) := by
    field_simp; ring
  rw [e, div_lt_iff₀ (by positivity)]
  nlinarith

theorem small_mean_final_numeric :
    19 / 16 * (20 / Real.sqrt 3) + 45 / 2 * (25 / 32 - π / (4 * Real.sqrt 3)) * (13 / 30)
      - 404 * π / 75 < 0 := by
  set s := Real.sqrt 3 with hs
  have hs3 : s * s = 3 := Real.mul_self_sqrt (by norm_num)
  have hsp : 0 < s := Real.sqrt_pos.2 (by norm_num)
  have hslo : (1.732 : ℝ) < s := by rw [hs, Real.lt_sqrt (by norm_num)]; norm_num
  have hshi : s < 1.7321 := by
    rw [hs, Real.sqrt_lt' (by norm_num)]; norm_num
  have hp := Real.pi_gt_d4
  have e1 : 20 / s = 20 * s / 3 := by
    rw [div_eq_div_iff (ne_of_gt hsp) (by norm_num)]; linarith
  have e2 : π / (4 * s) = π * s / 12 := by
    rw [div_eq_div_iff (by positivity) (by norm_num)]
    rw [show π * s * (4 * s) = 4 * π * (s * s) by ring, hs3]; ring
  rw [e1, e2]
  nlinarith [mul_pos (sub_pos.2 hp) (sub_pos.2 hslo)]

/-! ## Other small steps -/

/-- Brezis–Lieb step: a⁶ + b⁶ ≤ (a² + b²)³ -/
theorem six_le_cube (a b : ℝ) : a ^ 6 + b ^ 6 ≤ (a ^ 2 + b ^ 2) ^ 3 := by
  nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg b), sq_nonneg (a ^ 2 - b ^ 2),
    mul_nonneg (mul_nonneg (sq_nonneg a) (sq_nonneg b)) (add_nonneg (sq_nonneg a) (sq_nonneg b))]

/-- L¹ estimate for f♯: √((a²+b²)/2) ≤ (a+b)/√2 for a,b ≥ 0 (squared form) -/
theorem sharp_L1 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a ^ 2 + b ^ 2) / 2 ≤ (a + b) ^ 2 / 2 := by
  nlinarith [mul_nonneg ha hb]

end

end SteinTomas

#print axioms SteinTomas.H_neg
#print axioms SteinTomas.small_mean_final_numeric
#print axioms SteinTomas.three_psi_ten_thirds
