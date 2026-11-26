import Mathlib
import SteinTomasCircle.Basic.Elementary

/-!
# The algebraic part of Prop 3.1

* eq:global-Taylor: Φ(v+w) ≤ Φ(v) + Φ'(v)w + (5/16)w² for all real v, w.
  Proof: 5/8 − Φ''(y) = 30(y−½)²(y² + y/3 + 1/12) ≥ 0, and a positive quadrature rule exact up to degree 4 for the weight (1−s)
  (nodes 0, ¼, ½, ¾; weights 7/90, 4/15, 1/15, 4/45) turns the integral remainder into a finite sum.
* Φ(x/2) ≤ 1/32 − 3x/32 + 5x²/64 (used in the first step of Prop 3.1)
* the expansion of Φ(v_r) − (27/256)v_r² (the long formula in the paper)
* the expansion of Φ'(v_r) in Re(θ^{2j}) = T_j(Re θ²) with coefficients A₂…A₅, the bounds for |A_j| and ½ΣA_j² ≤ γ⁴/4
-/

namespace SteinTomas.Prop31Alg

open Real

noncomputable section

/-- Nonnegative factor in the factorization of 5/8 − Φ''(y) -/
def q (y : ℝ) : ℝ := 30 * (y - 1 / 2) ^ 2 * (y ^ 2 + y / 3 + 1 / 12)

lemma q_nonneg (y : ℝ) : 0 ≤ q y := by
  unfold q
  have : 0 ≤ y ^ 2 + y / 3 + 1 / 12 := by nlinarith [sq_nonneg (y + 1 / 6)]
  positivity

lemma q_eq (y : ℝ) : q y = 5 / 8 - (20 * y ^ 3 - 30 * y ^ 4) := by unfold q; ring

/-- eq:global-Taylor -/
theorem phi_taylor (v w : ℝ) :
    Φ (v + w) ≤ Φ v + (5 * v ^ 4 - 6 * v ^ 5) * w + 5 / 16 * w ^ 2 := by
  have key : Φ v + (5 * v ^ 4 - 6 * v ^ 5) * w + 5 / 16 * w ^ 2 - Φ (v + w)
      = w ^ 2 * (7 / 90 * q v + 4 / 15 * q (v + w / 4) + 1 / 15 * q (v + w / 2)
        + 4 / 45 * q (v + 3 * w / 4)) := by
    unfold Φ q; ring
  have h : 0 ≤ w ^ 2 * (7 / 90 * q v + 4 / 15 * q (v + w / 4) + 1 / 15 * q (v + w / 2)
        + 4 / 45 * q (v + 3 * w / 4)) := by
    have := q_nonneg v; have := q_nonneg (v + w / 4); have := q_nonneg (v + w / 2)
    have := q_nonneg (v + 3 * w / 4)
    positivity
  linarith

/-- Φ(x/2) ≤ 1/32 − 3x/32 + 5x²/64 -/
theorem phi_half (x : ℝ) : Φ (x / 2) ≤ 1 / 32 - 3 / 32 * x + 5 / 64 * x ^ 2 := by
  have h := phi_taylor (1 / 2) ((x - 1) / 2)
  have e : (1 / 2 : ℝ) + (x - 1) / 2 = x / 2 := by ring
  rw [e] at h
  unfold Φ at h ⊢
  nlinarith [h]

/-- Expansion of Φ(v_r) − (27/256)v_r² from the paper (a = t a₀, c = Re θ²) -/
theorem phi_expand (a γ c : ℝ) :
    Φ (a + γ * c) - 27 / 256 * (a + γ * c) ^ 2
      = a ^ 5 - a ^ 6 - 27 / 256 * a ^ 2 + (5 * a ^ 4 - 6 * a ^ 5 - 27 / 128 * a) * γ * c
        + (10 * a ^ 3 - 15 * a ^ 4 - 27 / 256) * γ ^ 2 * c ^ 2
        + 10 * a ^ 2 * (1 - 2 * a) * γ ^ 3 * c ^ 3 + 5 * a * (1 - 3 * a) * γ ^ 4 * c ^ 4
        + (1 - 6 * a) * γ ^ 5 * c ^ 5 - γ ^ 6 * c ^ 6 := by
  unfold Φ; ring

/-- Chebyshev polynomials T₂…T₅ (cos(jφ) = T_j(cos φ)) -/
def T2 (c : ℝ) : ℝ := 2 * c ^ 2 - 1
def T3 (c : ℝ) : ℝ := 4 * c ^ 3 - 3 * c
def T4 (c : ℝ) : ℝ := 8 * c ^ 4 - 8 * c ^ 2 + 1
def T5 (c : ℝ) : ℝ := 16 * c ^ 5 - 20 * c ^ 3 + 5 * c

def A0 (a γ : ℝ) : ℝ := 5 * a ^ 4 - 6 * a ^ 5 + (30 * a ^ 2 - 60 * a ^ 3) * γ ^ 2 / 2
  + (5 - 30 * a) * γ ^ 4 * 3 / 8
def A1 (a γ : ℝ) : ℝ := (20 * a ^ 3 - 30 * a ^ 4) * γ + (20 * a - 60 * a ^ 2) * γ ^ 3 * 3 / 4
  - 6 * γ ^ 5 * 10 / 16
def A2 (a γ : ℝ) : ℝ := 15 * a ^ 2 * (1 - 2 * a) * γ ^ 2 + 5 / 2 * (1 - 6 * a) * γ ^ 4
def A3 (a γ : ℝ) : ℝ := 5 * a * (1 - 3 * a) * γ ^ 3 - 15 / 8 * γ ^ 5
def A4 (a γ : ℝ) : ℝ := 5 / 8 * (1 - 6 * a) * γ ^ 4
def A5 (γ : ℝ) : ℝ := -3 / 8 * γ ^ 5

/-- Φ'(v_r) = A₀ + A₁Re θ² + Σ_{j=2}^5 A_j Re θ^{2j} -/
theorem dphi_expand (a γ c : ℝ) :
    5 * (a + γ * c) ^ 4 - 6 * (a + γ * c) ^ 5
      = A0 a γ + A1 a γ * c + A2 a γ * T2 c + A3 a γ * T3 c + A4 a γ * T4 c + A5 γ * T5 c := by
  unfold A0 A1 A2 A3 A4 A5 T2 T3 T4 T5; ring

/-- Bounds for |A_j|: ¼ ≤ a ≤ ⅓, 0 ≤ γ ≤ ⅓ -/
theorem A_bounds {a γ : ℝ} (ha1 : 1 / 4 ≤ a) (ha2 : a ≤ 1 / 3) (hg0 : 0 ≤ γ) (hg1 : γ ≤ 1 / 3) :
    |A2 a γ| ≤ 5 / 9 * γ ^ 2 ∧ |A3 a γ| ≤ 5 / 16 * γ ^ 3 ∧ |A4 a γ| ≤ 5 / 8 * γ ^ 4
      ∧ |A5 γ| ≤ 3 / 8 * γ ^ 5 := by
  have g2 : 0 ≤ γ ^ 2 := sq_nonneg γ
  have g2' : γ ^ 2 ≤ 1 / 9 := by nlinarith
  -- 15a²(1−2a) ∈ [15/32, 5/9]
  have hh := mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 ha2)
  have f1 : 15 * a ^ 2 * (1 - 2 * a) ≤ 5 / 9 := by nlinarith [hh, sq_nonneg (a - 1 / 3)]
  have f1' : 15 / 32 ≤ 15 * a ^ 2 * (1 - 2 * a) := by
    nlinarith [hh, sq_nonneg (a - 1 / 4)]
  have f2 : 0 ≤ 5 * a * (1 - 3 * a) := by nlinarith
  have f2' : 5 * a * (1 - 3 * a) ≤ 5 / 16 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold A2
    rw [abs_le]; constructor
    · -- A₂ ≥ (15/32 − 5/18)γ² ≥ 0 ≥ −(5/9)γ²
      have h1 : 15 / 32 * γ ^ 2 ≤ 15 * a ^ 2 * (1 - 2 * a) * γ ^ 2 :=
        mul_le_mul_of_nonneg_right f1' g2
      have h2 : -(5 / 2) * γ ^ 2 * γ ^ 2 ≤ 5 / 2 * (1 - 6 * a) * γ ^ 4 := by
        have : -(5 / 2) * γ ^ 2 ≤ 5 / 2 * (1 - 6 * a) * γ ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) g2
        nlinarith
      nlinarith
    · have h1 : 15 * a ^ 2 * (1 - 2 * a) * γ ^ 2 ≤ 5 / 9 * γ ^ 2 :=
        mul_le_mul_of_nonneg_right f1 g2
      have h2 : 5 / 2 * (1 - 6 * a) * γ ^ 4 ≤ 0 := by
        have : 0 ≤ γ ^ 4 := by positivity
        nlinarith
      linarith
  · unfold A3
    have g3 : 0 ≤ γ ^ 3 := by positivity
    rw [abs_le]; constructor
    · have h1 : 0 ≤ 5 * a * (1 - 3 * a) * γ ^ 3 := mul_nonneg f2 g3
      have h2 : 15 / 8 * γ ^ 5 ≤ 15 / 8 * (1 / 9) * γ ^ 3 := by
        have : γ ^ 5 = γ ^ 2 * γ ^ 3 := by ring
        rw [this]; nlinarith [mul_le_mul_of_nonneg_right g2' g3]
      nlinarith
    · have h1 : 5 * a * (1 - 3 * a) * γ ^ 3 ≤ 5 / 16 * γ ^ 3 := mul_le_mul_of_nonneg_right f2' g3
      have : 0 ≤ γ ^ 5 := by positivity
      linarith
  · unfold A4
    have g4 : 0 ≤ γ ^ 4 := by positivity
    rw [abs_le]; constructor <;> nlinarith
  · unfold A5
    have g5 : 0 ≤ γ ^ 5 := by positivity
    rw [abs_le]; constructor <;> nlinarith

/-- ½ Σ_{j=2}^5 A_j² ≤ γ⁴/4 -/
theorem A_sq_sum {a γ : ℝ} (ha1 : 1 / 4 ≤ a) (ha2 : a ≤ 1 / 3) (hg0 : 0 ≤ γ) (hg1 : γ ≤ 1 / 3) :
    1 / 2 * (A2 a γ ^ 2 + A3 a γ ^ 2 + A4 a γ ^ 2 + A5 γ ^ 2) ≤ γ ^ 4 / 4 := by
  obtain ⟨b2, b3, b4, b5⟩ := A_bounds ha1 ha2 hg0 hg1
  have s2 : A2 a γ ^ 2 ≤ (5 / 9 * γ ^ 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) b2 2
  have s3 : A3 a γ ^ 2 ≤ (5 / 16 * γ ^ 3) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) b3 2
  have s4 : A4 a γ ^ 2 ≤ (5 / 8 * γ ^ 4) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) b4 2
  have s5 : A5 γ ^ 2 ≤ (3 / 8 * γ ^ 5) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) b5 2
  have g4 : 0 ≤ γ ^ 4 := by positivity
  have g2 : γ ^ 2 ≤ 1 / 9 := by nlinarith
  have e6 : γ ^ 6 ≤ γ ^ 4 / 9 := by
    have := mul_le_mul_of_nonneg_left g2 g4; nlinarith
  have e8 : γ ^ 8 ≤ γ ^ 4 / 81 := by
    have := mul_le_mul_of_nonneg_left e6 (sq_nonneg γ); nlinarith
  have e10 : γ ^ 10 ≤ γ ^ 4 / 729 := by
    have := mul_le_mul_of_nonneg_left e8 (sq_nonneg γ); nlinarith
  nlinarith

/-- Numerical fact used in eq:prop31-a: α_{2n} < α₀/9 (from eq:bessel-global) -/
theorem alpha_ratio {α0 : ℝ} (h : 101 / 300 < α0) :
    (37 : ℝ) / 1000 < α0 / 9 ∧ (19 : ℝ) / 1000 < α0 / 9 := by
  constructor <;> linarith

end

end SteinTomas.Prop31Alg

#print axioms SteinTomas.Prop31Alg.phi_taylor
#print axioms SteinTomas.Prop31Alg.A_sq_sum
