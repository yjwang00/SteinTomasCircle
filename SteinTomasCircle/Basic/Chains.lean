import Mathlib
import SteinTomasCircle.Basic.Elementary

/-!
# Bookkeeping layer: the analytic inequalities of the paper as real-number hypotheses; verification of constants and deduction chains

Each theorem abstracts the integral inequalities already obtained in the paper into hypotheses about real numbers and then formally derives the conclusion of the corresponding statement.
This checks all constants, directions of inequalities and algebraic eliminations first; afterwards each real-number hypothesis is discharged by an analytic argument (or a literature hypothesis).

-/

namespace SteinTomas.Chains

open Real

noncomputable section

/-! ## Prop 3.1 (prop:large-mean) -/

/-- Step 1: a₀ ≥ 5/8 ⇒ a₀ < 4/5.
`S` stands for Σ_{n≥1} α_{2n} a_{2n}², `hS` comes from α_{2n} < α₀/9 and Parseval (strict since f is nonconstant). -/
theorem large_mean_step1 {α0 μ a0 S : ℝ} (hα : 0 < α0) (hμ : α0 ≤ μ) (ha : 5 / 8 ≤ a0)
    (ha1 : a0 < 1) (hS : S < α0 / 9 * (1 - a0 ^ 2))
    (hmain : μ / 32 * (a0 - 1 / 2) ≤ α0 / 32 * (1 - 3 * a0) + 5 / 64 * (α0 * a0 ^ 2 + S)) :
    a0 < 4 / 5 := by
  have h1 : α0 / 32 * (a0 - 1 / 2) ≤ μ / 32 * (a0 - 1 / 2) := by nlinarith
  have h2 : 0 < α0 * (1 - 3 * a0 + 5 / 18 * (1 + 8 * a0 ^ 2) - a0 + 1 / 2) := by nlinarith
  have h3 : 0 < 1 - 3 * a0 + 5 / 18 * (1 + 8 * a0 ^ 2) - a0 + 1 / 2 := by
    by_contra h
    have h' := not_lt.mp h
    nlinarith
  exact prop31_step1 ha1 h3

/-- K(x) ≥ 0 on [25/96, 1/3] -/
theorem Kp_nonneg {x : ℝ} (h1 : 25 / 96 ≤ x) (h2 : x ≤ 1 / 3) : 0 ≤ Kp x := by
  unfold Kp
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2), sq_nonneg (x - 1 / 4),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (by linarith : (0 : ℝ) ≤ x)]

-- long derivation, needs more heartbeats
set_option maxHeartbeats 2000000 in
/-- Step 2: contradiction on [5/8, 4/5) from the combined estimate (after eq:total-integral-bound).
`S` = Σ_{n≥1} α_{2n}a_{2n}², `hS` is the estimate obtained in the paper from eq:a2-bound and eq:bessel-global;
`W V U` are the three integrals of Lemma 2.1. -/
theorem large_mean_step2 {α0 μ a0 a2 S W V U : ℝ}
    (hα0 : 0 < α0) (hα0u : α0 < 337 / 1000) (hμ : α0 ≤ μ)
    (ha0 : 5 / 8 ≤ a0) (ha0' : a0 < 4 / 5) (ha2 : 0 ≤ a2) (ha2' : a2 ^ 2 ≤ 1 / 2)
    (hsum : a0 ^ 2 + a2 ^ 2 ≤ 1)
    (hS : S ≤ 19 / 1000 * (1 - a0 ^ 2) + 9 / 1000)
    (hW : 3059 / 10000 < W) (hV0 : 0 ≤ V) (hV : V < 3 / 400) (hU0 : 0 ≤ U)
    (hU : U < 3 / 250000)
    (hmain : μ * tt ^ 5 * (a0 - tt) ≤ 27 * tt ^ 2 / 256 * (α0 * a0 ^ 2 + S)
      + W * (Φ (tt * a0) - 27 / 256 * tt ^ 2 * a0 ^ 2) + tt ^ 2 * a2 ^ 2 * Kp (tt * a0) * V
      + (175 / 4 * tt ^ 4 * a2 ^ 4 + 53 / 256 * tt ^ 2 * (1 - a0 ^ 2 - a2 ^ 2)
        + 10 * tt ^ 3 * a2 ^ 2 * Real.sqrt (1 - a0 ^ 2 - a2 ^ 2)) * U) :
    False := by
  have htt : tt = 5 / 12 := rfl
  have hH := H_neg ha0 ha0'.le
  unfold H at hH
  rw [htt] at hmain hH
  set x := 5 / 12 * a0 with hx
  have hx1 : 25 / 96 ≤ x := by rw [hx]; linarith
  have hx2 : x ≤ 1 / 3 := by rw [hx]; linarith
  have hK := Kp_nonneg hx1 hx2
  have hΦ : Φ x - 27 / 256 * x ^ 2 ≤ 0 := by have := phi_le x; linarith
  have hΦ' : Φ x - 27 / 256 * (5 / 12) ^ 2 * a0 ^ 2 ≤ 0 := by
    have e : 27 / 256 * (5 / 12) ^ 2 * a0 ^ 2 = 27 / 256 * x ^ 2 := by rw [hx]; ring
    rw [e]; exact hΦ
  -- W term
  have hWt : W * (Φ x - 27 / 256 * (5 / 12) ^ 2 * a0 ^ 2)
      ≤ 3059 / 10000 * (Φ x - 27 / 256 * (5 / 12) ^ 2 * a0 ^ 2) := by
    linarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ W - 3059 / 10000) hΦ']
  -- V term
  have ha2V : a2 ^ 2 * V ≤ 3 / 800 := by
    linarith [mul_le_mul ha2' hV.le hV0 (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hVt : (5 / 12) ^ 2 * a2 ^ 2 * Kp x * V ≤ 3 * (5 / 12) ^ 2 / 800 * Kp x := by
    have := mul_le_mul_of_nonneg_left ha2V (mul_nonneg (by norm_num : (0 : ℝ) ≤ (5 / 12) ^ 2) hK)
    linarith [this]
  -- U term
  have hrest : 1 - a0 ^ 2 - a2 ^ 2 ≤ 39 / 64 := by nlinarith [sq_nonneg a2]
  have hrest0 : 0 ≤ 1 - a0 ^ 2 - a2 ^ 2 := by linarith
  have hsqrt : Real.sqrt (1 - a0 ^ 2 - a2 ^ 2) ≤ 4 / 5 := by
    have h := Real.sqrt_le_sqrt (show 1 - a0 ^ 2 - a2 ^ 2 ≤ (4 / 5) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by norm_num)] at h
  have ha24 : a2 ^ 4 ≤ 1 / 4 := by nlinarith [sq_nonneg a2]
  have hbr : 175 / 4 * (5 / 12) ^ 4 * a2 ^ 4 + 53 / 256 * (5 / 12) ^ 2 * (1 - a0 ^ 2 - a2 ^ 2)
      + 10 * (5 / 12) ^ 3 * a2 ^ 2 * Real.sqrt (1 - a0 ^ 2 - a2 ^ 2) ≤ 2 / 3 := by
    have hs0 := Real.sqrt_nonneg (1 - a0 ^ 2 - a2 ^ 2)
    linarith [mul_le_mul ha2' hsqrt hs0 (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hUt : (175 / 4 * (5 / 12) ^ 4 * a2 ^ 4 + 53 / 256 * (5 / 12) ^ 2 * (1 - a0 ^ 2 - a2 ^ 2)
      + 10 * (5 / 12) ^ 3 * a2 ^ 2 * Real.sqrt (1 - a0 ^ 2 - a2 ^ 2)) * U ≤ 1 / 125000 := by
    have := mul_le_mul_of_nonneg_right hbr hU0
    linarith
  -- μ term and α₀ term
  have hμt : α0 * (5 / 12) ^ 5 * (a0 - 5 / 12) ≤ μ * (5 / 12) ^ 5 * (a0 - 5 / 12) := by
    have : 0 ≤ (5 / 12 : ℝ) ^ 5 * (a0 - 5 / 12) := by
      apply mul_nonneg (by norm_num); linarith
    linarith [mul_le_mul_of_nonneg_right hμ this]
  have hcoef : 0 < 27 / 256 * (5 / 12) ^ 2 * a0 ^ 2 - (5 / 12) ^ 5 * (a0 - 5 / 12) := by
    nlinarith [sq_nonneg (a0 - 1 / 3)]
  have hαt : α0 * (27 / 256 * (5 / 12) ^ 2 * a0 ^ 2 - (5 / 12) ^ 5 * (a0 - 5 / 12))
      ≤ 337 / 1000 * (27 / 256 * (5 / 12) ^ 2 * a0 ^ 2 - (5 / 12) ^ 5 * (a0 - 5 / 12)) :=
    mul_le_mul_of_nonneg_right hα0u.le hcoef.le
  have hSt : 27 * (5 / 12) ^ 2 / 256 * S
      ≤ 27 * (5 / 12) ^ 2 / 256 * (19 / 1000 * (1 - a0 ^ 2) + 9 / 1000) :=
    mul_le_mul_of_nonneg_left hS (by norm_num)
  linarith [hmain, hH, hWt, hVt, hUt, hμt, hαt, hSt]

/-! ## Theorem 1.2, prop:master and prop:convolution -/

/-- M_conc/16 = 5π³/(4√3): the coefficient in eq:global-split -/
theorem Mconc_div16 : 20 * π ^ 3 / Real.sqrt 3 / 16 = 5 * π ^ 3 / (4 * Real.sqrt 3) := by
  have : Real.sqrt 3 ≠ 0 := by positivity
  field_simp
  try ring

/-- eq:residual-simple: from R² ≤ (9/2)‖f‖₁²Q(f²)·R and R ≥ 0 we get R ≤ (9/2)‖f‖₁²Q(f²) -/
theorem residual_simple {R L Q : ℝ} (hR : 0 ≤ R) (hQ : 0 ≤ Q)
    (h : R ^ 2 ≤ 9 / 2 * L ^ 2 * Q * R) : R ≤ 9 / 2 * L ^ 2 * Q := by
  rcases eq_or_lt_of_le hR with h0 | hpos
  · rw [← h0]; positivity
  · nlinarith

/-- Assembly of prop:master: E ≤ (M/16)·X + 5π²R, X = 16B³ − 12B·I, R ≤ (9/2)L²Q -/
theorem master_assembly {E M B I L Q R : ℝ}
    (hsplit : E ≤ M / 16 * (16 * B ^ 3 - 12 * B * I) + 5 * π ^ 2 * R)
    (hR : R ≤ 9 / 2 * L ^ 2 * Q) :
    E ≤ M / 16 * (16 * B ^ 3 - 12 * B * I) + 45 * π ^ 2 / 2 * L ^ 2 * Q := by
  nlinarith [pi_pos, sq_nonneg π]

/-- eq:L1-remainder-sym: from master, I ≥ 0, Q ≤ (2/π)B² -/
theorem L1_sym {E M B I L Q : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hI : 0 ≤ I) (hQ : Q ≤ 2 / π * B ^ 2)
    (hmaster : E ≤ M / 16 * (16 * B ^ 3 - 12 * B * I) + 45 * π ^ 2 / 2 * L ^ 2 * Q) :
    E ≤ M * B ^ 3 + 45 * π * L ^ 2 * B ^ 2 := by
  have hp := pi_pos
  have h1 : M / 16 * (16 * B ^ 3 - 12 * B * I) ≤ M * B ^ 3 := by
    have : 0 ≤ M / 16 * (12 * B * I) := by positivity
    nlinarith
  have h2 : 45 * π ^ 2 / 2 * L ^ 2 * Q ≤ 45 * π * L ^ 2 * B ^ 2 := by
    have hL : 0 ≤ 45 * π ^ 2 / 2 * L ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hQ hL
    have e : 45 * π ^ 2 / 2 * L ^ 2 * (2 / π * B ^ 2) = 45 * π * L ^ 2 * B ^ 2 := by
      field_simp
    linarith
  linarith

/-- Theorem 1.2: from the symmetric case (constant 45π) via f♯ to the general case (constant 90π).
`E ≤ E♯` (CFOT17 Steps 1–2), ‖f♯‖₂ = ‖f‖₂, ‖f♯‖₁ ≤ √2‖f‖₁. -/
theorem L1_general {E Es M B L Ls : ℝ} (hE : E ≤ Es)
    (hs : Es ≤ M * B ^ 3 + 45 * π * Ls ^ 2 * B ^ 2) (hLs0 : 0 ≤ Ls)
    (hLs : Ls ≤ Real.sqrt 2 * L) :
    E ≤ M * B ^ 3 + 90 * π * L ^ 2 * B ^ 2 := by
  have h2 : Ls ^ 2 ≤ 2 * L ^ 2 := by
    have := pow_le_pow_left₀ hLs0 hLs 2
    rwa [mul_pow, Real.sq_sqrt (by norm_num)] at this
  have : 45 * π * Ls ^ 2 * B ^ 2 ≤ 45 * π * (2 * L ^ 2) * B ^ 2 := by
    have := pi_pos
    gcongr
  nlinarith

/-- eq:square-average: I ≥ (3π/8)Q − ¼B², where m = |∫f²ω²dσ|² -/
theorem square_average {I Q B m : ℝ} (hI : I = 1 / 2 * B ^ 2 - 1 / 2 * m)
    (hQ : Q ≤ 2 / π * B ^ 2 - 4 / (3 * π) * m) : 3 * π / 8 * Q - 1 / 4 * B ^ 2 ≤ I := by
  have hp := pi_pos
  have := mul_le_mul_of_nonneg_left hQ (by positivity : (0 : ℝ) ≤ 3 * π / 8)
  have e : 3 * π / 8 * (2 / π * B ^ 2 - 4 / (3 * π) * m) = 3 / 4 * B ^ 2 - 1 / 2 * m := by
    field_simp
    try ring
  linarith

/-- prop:convolution: from master and eq:square-average -/
theorem convolution {E B I L Q : ℝ} (hB : 0 ≤ B) (hI : 3 * π / 8 * Q - 1 / 4 * B ^ 2 ≤ I)
    (hmaster : E ≤ (20 * π ^ 3 / Real.sqrt 3) / 16 * (16 * B ^ 3 - 12 * B * I)
      + 45 * π ^ 2 / 2 * L ^ 2 * Q) :
    E ≤ 19 / 16 * (20 * π ^ 3 / Real.sqrt 3) * B ^ 3
      + 45 * π ^ 2 / 2 * (L ^ 2 - π ^ 2 / (4 * Real.sqrt 3) * B) * Q := by
  have hs : 0 < Real.sqrt 3 := by positivity
  have hp := pi_pos
  have hM : 0 ≤ (20 * π ^ 3 / Real.sqrt 3) / 16 * (12 * B) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hI hM
  have e : 19 / 16 * (20 * π ^ 3 / Real.sqrt 3) * B ^ 3
      + 45 * π ^ 2 / 2 * (L ^ 2 - π ^ 2 / (4 * Real.sqrt 3) * B) * Q
      = (20 * π ^ 3 / Real.sqrt 3) / 16 * (16 * B ^ 3 - 12 * B * (3 * π / 8 * Q - 1 / 4 * B ^ 2))
        + 45 * π ^ 2 / 2 * L ^ 2 * Q := by
    field_simp
    try ring
  rw [e]
  nlinarith [h1]

/-! ## Last step of the second variation lemma (lem:a second variation bound) -/

/-- From (1/(5π²))·E·Q ≤ ‖ν‖₂‖h*(fσ)‖₂, ‖ν‖₂ = E^{1/2}/(2π),
‖h*(fσ)‖₂ ≤ (√3/2)L‖h‖₂, ‖h‖₂² = 2Q we get E·Q ≤ (75π²/8)L² -/
theorem second_variation_final {E Q L nν nh nhf : ℝ} (hE : 0 < E) (hQ : 0 ≤ Q) (hL : 0 ≤ L)
    (hnν : nν ^ 2 = E / (4 * π ^ 2)) (hnν0 : 0 ≤ nν)
    (hnh : nh ^ 2 = 2 * Q) (hnh0 : 0 ≤ nh)
    (hnhf : nhf ≤ Real.sqrt 3 / 2 * L * nh) (hnhf0 : 0 ≤ nhf)
    (hpair : 1 / (5 * π ^ 2) * E * Q ≤ nν * nhf) :
    E * Q ≤ 75 * π ^ 2 / 8 * L ^ 2 := by
  have hp := pi_pos
  have h1 : 1 / (5 * π ^ 2) * E * Q ≤ nν * (Real.sqrt 3 / 2 * L * nh) :=
    hpair.trans (mul_le_mul_of_nonneg_left hnhf hnν0)
  have hlhs0 : 0 ≤ 1 / (5 * π ^ 2) * E * Q := by positivity
  have h2 : (1 / (5 * π ^ 2) * E * Q) ^ 2 ≤ (nν * (Real.sqrt 3 / 2 * L * nh)) ^ 2 :=
    pow_le_pow_left₀ hlhs0 h1 2
  have e : (nν * (Real.sqrt 3 / 2 * L * nh)) ^ 2 = E / (4 * π ^ 2) * (3 / 4) * L ^ 2 * (2 * Q) := by
    rw [show (nν * (Real.sqrt 3 / 2 * L * nh)) ^ 2
        = nν ^ 2 * (Real.sqrt 3 ^ 2 / 4) * L ^ 2 * nh ^ 2 by ring,
      hnν, hnh, Real.sq_sqrt (by norm_num)]
    try ring
  rw [e] at h2
  -- h2 : E²Q²/(25π⁴) ≤ (3/(8π²)) E L² Q
  rcases eq_or_lt_of_le hQ with hQ0 | hQp
  · rw [← hQ0]; simp; positivity
  have key : E * Q * (E * Q) ≤ 75 * π ^ 2 / 8 * L ^ 2 * (E * Q) := by
    have e2 : (1 / (5 * π ^ 2) * E * Q) ^ 2 = E * Q * (E * Q) / (25 * π ^ 4) := by
      field_simp
      try ring
    have e3 : E / (4 * π ^ 2) * (3 / 4) * L ^ 2 * (2 * Q)
        = 75 * π ^ 2 / 8 * L ^ 2 * (E * Q) / (25 * π ^ 4) := by
      field_simp
      try ring
    rw [e2, e3] at h2
    exact (div_le_div_iff_of_pos_right (by positivity)).mp h2
  exact le_of_mul_le_mul_right key (by positivity)

/-! ## prop:small-mean -/

/-- Contradiction from E ≥ (2π)⁴α₀ > 404π⁴/75, ‖f‖₁² = 2πa₀² ≤ 25π/32, the second variation lemma and prop:convolution. -/
theorem small_mean {E L Q : ℝ} (hE : 404 * π ^ 4 / 75 < E) (hL2 : L ^ 2 ≤ 25 * π / 32)
    (hQ0 : 0 ≤ Q) (hsv : E * Q ≤ 75 * π ^ 2 / 8 * L ^ 2)
    (hconv : E ≤ 19 / 16 * (20 * π ^ 3 / Real.sqrt 3)
      + 45 * π ^ 2 / 2 * (L ^ 2 - π ^ 2 / (4 * Real.sqrt 3)) * Q) : False := by
  have hp := pi_pos
  have hs : 0 < Real.sqrt 3 := by positivity
  have hEpos : 0 < E := lt_trans (by positivity) hE
  -- Q < 13/30
  have hQ : Q < 13 / 30 := by
    have h1 : E * Q ≤ 75 * π ^ 2 / 8 * (25 * π / 32) := by
      have := mul_le_mul_of_nonneg_left hL2 (by positivity : (0 : ℝ) ≤ 75 * π ^ 2 / 8)
      linarith
    have h2 : 404 * π ^ 4 / 75 * Q ≤ E * Q := mul_le_mul_of_nonneg_right hE.le hQ0
    have hnum := small_mean_Q_numeric
    have e : 75 * π ^ 2 / 8 * (25 * π / 32) * (75 / (404 * π ^ 4)) * (404 * π ^ 4 / 75)
        = 75 * π ^ 2 / 8 * (25 * π / 32) := by field_simp
    by_contra hc
    have hc' := not_lt.mp hc
    have h3 : 404 * π ^ 4 / 75 * (13 / 30) ≤ 404 * π ^ 4 / 75 * Q :=
      mul_le_mul_of_nonneg_left hc' (by positivity)
    have h4 : 75 * π ^ 2 / 8 * (25 * π / 32) * (75 / (404 * π ^ 4)) * (404 * π ^ 4 / 75)
        < 13 / 30 * (404 * π ^ 4 / 75) :=
      mul_lt_mul_of_pos_right hnum (by positivity)
    linarith
  -- the coefficient 25π/32 − π²/(4√3) is positive
  have hc : 0 < 25 * π / 32 - π ^ 2 / (4 * Real.sqrt 3) := by
    have hs1 : (1.732 : ℝ) < Real.sqrt 3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    have hp4 : π < 3.1416 := Real.pi_lt_d4
    rw [sub_pos, div_lt_iff₀ (by positivity)]
    nlinarith
  have hterm : (L ^ 2 - π ^ 2 / (4 * Real.sqrt 3)) * Q
      ≤ (25 * π / 32 - π ^ 2 / (4 * Real.sqrt 3)) * (13 / 30) := by
    have a1 : (L ^ 2 - π ^ 2 / (4 * Real.sqrt 3)) * Q
        ≤ (25 * π / 32 - π ^ 2 / (4 * Real.sqrt 3)) * Q :=
      mul_le_mul_of_nonneg_right (by linarith) hQ0
    have a2 : (25 * π / 32 - π ^ 2 / (4 * Real.sqrt 3)) * Q
        ≤ (25 * π / 32 - π ^ 2 / (4 * Real.sqrt 3)) * (13 / 30) :=
      mul_le_mul_of_nonneg_left hQ.le hc.le
    linarith
  have hfin : 404 * π ^ 4 / 75 < 19 / 16 * (20 * π ^ 3 / Real.sqrt 3)
      + 45 * π ^ 2 / 2 * (25 * π / 32 - π ^ 2 / (4 * Real.sqrt 3)) * (13 / 30) := by
    have := mul_le_mul_of_nonneg_left hterm (by positivity : (0 : ℝ) ≤ 45 * π ^ 2 / 2)
    nlinarith
  -- dividing by π³ gives an inequality contradicting small_mean_final_numeric
  have hnum := small_mean_final_numeric
  have e : 19 / 16 * (20 * π ^ 3 / Real.sqrt 3)
      + 45 * π ^ 2 / 2 * (25 * π / 32 - π ^ 2 / (4 * Real.sqrt 3)) * (13 / 30) - 404 * π ^ 4 / 75
      = π ^ 3 * (19 / 16 * (20 / Real.sqrt 3)
        + 45 / 2 * (25 / 32 - π / (4 * Real.sqrt 3)) * (13 / 30) - 404 * π / 75) := by
    field_simp
    try ring
  have : 0 < π ^ 3 * (19 / 16 * (20 / Real.sqrt 3)
      + 45 / 2 * (25 / 32 - π / (4 * Real.sqrt 3)) * (13 / 30) - 404 * π / 75) := by
    rw [← e]; linarith
  have := (pos_iff_pos_of_mul_pos this).mp (by positivity)
  linarith

/-! ## Compactness step in the proof of Theorem 1.1 (the elementary part after Brezis–Lieb) -/

/-- If M = lim(‖Ef‖₆⁶ + ‖E(f_j−f)‖₆⁶), ‖f‖₂² + ‖f_j − f‖₂² → 1 and f ≠ 0,
then necessarily ‖f_j − f‖₂ → 0. This is the algebraic core, term by term:
a,b ≥ 0, a² + b² = 1, M·(a⁶+b⁶) ≥ M, M > 0 ⇒ ab = 0. -/
theorem compactness_core {a b M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ^ 2 + b ^ 2 = 1)
    (hM : 0 < M) (h : M ≤ M * (a ^ 6 + b ^ 6)) : a * b = 0 := by
  have h1 : 1 ≤ a ^ 6 + b ^ 6 := by
    by_contra hc
    have hc' := not_le.mp hc
    nlinarith
  have e : (a ^ 2 + b ^ 2) ^ 3 = a ^ 6 + b ^ 6 + 3 * a ^ 2 * b ^ 2 * (a ^ 2 + b ^ 2) := by ring
  rw [hab] at e
  have h2 : a ^ 2 * b ^ 2 = 0 := by nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg b)]
  have : (a * b) ^ 2 = 0 := by rw [mul_pow]; exact h2
  exact pow_eq_zero_iff two_ne_zero |>.mp this

end

end SteinTomas.Chains

#print axioms SteinTomas.Chains.large_mean_step2
#print axioms SteinTomas.Chains.small_mean
#print axioms SteinTomas.Chains.second_variation_final
