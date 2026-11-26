import Mathlib

/-!
# Formalization of Lemma 4.3 (lem:four-sign): the algebraic core

Let p = ω·η, q = ω·ζ, r = η·ζ, a₁ = det(ω,η), a₂ = det(ω,ζ), a₃ = det(η,ζ).
For ε,δ = ±1: λ_{εδ} = |εω+δη+ζ|² − 1 = 2(1+εδp+εq+δr),
|εω+δη+2ζ|² ≤ 4 ⇔ 1+εδp+2εq+2δr ≤ 0.

Differences from the proof in the paper (mathematically equivalent):
* the paper moves the three points to a standard position by rotations/reflections; here we flip the sign of ω or η to make a₁,a₂,a₃ of the same sign,
  and then the negative one is λ_{+,−}.
* the paper uses concavity of ψ; here we use a rational tangent-line upper bound ψ(λ) ≤ c + bλ on [0,8],
  with b = 259/25000, 3c + 10b = 1/2.
-/

namespace SteinTomas.FourSign

open Real

noncomputable section

def ψ (l : ℝ) : ℝ := 1 / 8 + l / (16 * (3 + Real.sqrt (1 + l)))

/-- 𝒫 as a function of λ = |x|² − 1 -/
def Pl (l : ℝ) : ℝ := if 0 < l ∧ l < 8 then l * (8 - l) * ψ l else 0

/-- Indicator function 1{I ≤ 0} -/
def ind (I : ℝ) : ℝ := if I ≤ 0 then 1 else 0

/-- Left-hand side of the lemma; the four terms are (ε,δ) = (+,+), (+,−), (−,+), (−,−) -/
def lhs (p q r : ℝ) : ℝ :=
  Pl (2 * (1 + p + q + r)) * (1 + ind (1 + p + 2 * q + 2 * r))
  + Pl (2 * (1 - p + q - r)) * (1 + ind (1 - p + 2 * q - 2 * r))
  + Pl (2 * (1 - p - q + r)) * (1 + ind (1 - p - 2 * q + 2 * r))
  + Pl (2 * (1 + p - q - r)) * (1 + ind (1 + p - 2 * q - 2 * r))

/-! ## Properties of ψ -/


lemma ψ_nonneg {l : ℝ} (h : 0 ≤ l) : 0 ≤ ψ l := by unfold ψ; positivity

lemma line_poly (s : ℝ) (hs : 0 ≤ s) :
    s ^ 2 - 1 ≤ (1 / 6 - 259 / 25000 * (10 / 3) - 1 / 8 + 259 / 25000 * (s ^ 2 - 1))
      * (16 * (3 + s)) := by
  nlinarith [mul_nonneg (sq_nonneg (s - 52 / 25)) hs, sq_nonneg (s - 52 / 25)]

/-- Rational tangent-line upper bound: ψ(λ) ≤ c + bλ -/
lemma ψ_line {l : ℝ} (hl : 0 ≤ l) : ψ l ≤ (1 / 6 - 259 / 25000 * (10 / 3)) + 259 / 25000 * l := by
  unfold ψ
  have hs0 : 0 ≤ Real.sqrt (1 + l) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (1 + l) ^ 2 = 1 + l := Real.sq_sqrt (by linarith)
  have key := line_poly (Real.sqrt (1 + l)) hs0
  rw [hs2] at key
  have hpos : (0 : ℝ) < 16 * (3 + Real.sqrt (1 + l)) := by positivity
  have : l / (16 * (3 + Real.sqrt (1 + l))) ≤ 1 / 6 - 259 / 25000 * (10 / 3) - 1 / 8 + 259 / 25000 * l := by
    rw [div_le_iff₀ hpos]; nlinarith [key]
  linarith

lemma Pl_le {l : ℝ} (h0 : 0 ≤ l) (h8 : l ≤ 8) : Pl l ≤ l * (8 - l) * ψ l := by
  unfold Pl
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (mul_nonneg h0 (by linarith)) (ψ_nonneg h0)

lemma Pl_nonpos {l : ℝ} (h : l ≤ 0) : Pl l = 0 := by
  unfold Pl; rw [if_neg]; rintro ⟨h1, -⟩; linarith

lemma ind_nonneg (I : ℝ) : 0 ≤ ind I := by unfold ind; split_ifs <;> norm_num

/-! ## Core: the case where a₁,a₂,a₃ have the same sign -/

set_option maxHeartbeats 4000000 in
theorem core (p q r a1 a2 a3 : ℝ)
    (h1 : a1 ^ 2 = 1 - p ^ 2) (h2 : a2 ^ 2 = 1 - q ^ 2) (h3 : a3 ^ 2 = 1 - r ^ 2)
    (h12 : a1 * a2 = r - p * q) (h13 : a1 * a3 = p * r - q) (h23 : a2 * a3 = p - q * r)
    (c1 : 0 ≤ a1 * a2) (c2 : 0 ≤ a1 * a3) (c3 : 0 ≤ a2 * a3) :
    lhs p q r ≤ 2 * (|a1| + |a2| + |a3|) ^ 2 := by
  have hD : (a1 + a2 + a3) ^ 2 ≤ (|a1| + |a2| + |a3|) ^ 2 := by
    have h := abs_add_three a1 a2 a3
    calc (a1 + a2 + a3) ^ 2 = |a1 + a2 + a3| ^ 2 := (sq_abs _).symm
      _ ≤ (|a1| + |a2| + |a3|) ^ 2 := by gcongr
  have hS : (a1 + a2 + a3) ^ 2
      = 3 - p ^ 2 - q ^ 2 - r ^ 2 + 2 * ((r - p * q) + (p * r - q) + (p - q * r)) := by
    linear_combination h1 + h2 + h3 + 2 * h12 + 2 * h13 + 2 * h23
  have hp1 : p ^ 2 ≤ 1 := by nlinarith [sq_nonneg a1]
  have hq1 : q ^ 2 ≤ 1 := by nlinarith [sq_nonneg a2]
  have hr1 : r ^ 2 ≤ 1 := by nlinarith [sq_nonneg a3]
  have hplo : -1 ≤ p := by nlinarith
  have hphi : p ≤ 1 := by nlinarith
  have hqlo : -1 ≤ q := by nlinarith
  have hqhi : q ≤ 1 := by nlinarith
  have hrlo : -1 ≤ r := by nlinarith
  have hrhi : r ≤ 1 := by nlinarith
  have e1 : (a2 * a3) ^ 2 = a2 ^ 2 * a3 ^ 2 := by ring
  rw [h23, h2, h3] at e1
  have gram : q ^ 2 + r ^ 2 = 1 + 2 * p * q * r - p ^ 2 := by linear_combination e1
  have hc1 : 0 ≤ r - p * q := h12 ▸ c1
  have hc2 : 0 ≤ p * r - q := h13 ▸ c2
  have hc3 : 0 ≤ p - q * r := h23 ▸ c3
  rcases eq_or_lt_of_le hplo with hpeq | hpgt
  · -- degenerate case p = −1: then r = −q, q = ±1, and all λ ∈ {0, 8}
    have hp : p = -1 := hpeq.symm
    subst hp
    have hqr2 : (q + r) ^ 2 = 0 := by nlinarith [gram]
    have hqr : q + r = 0 := (pow_eq_zero_iff two_ne_zero).mp hqr2
    have hr : r = -q := by linarith
    subst hr
    have hq2 : q ^ 2 = 1 := by nlinarith
    have hfac : (q - 1) * (q + 1) = 0 := by linear_combination hq2
    rcases mul_eq_zero.mp hfac with h | h
    · have hq : q = 1 := by linarith
      subst hq
      norm_num [lhs, Pl] <;> positivity
    · have hq : q = -1 := by linarith
      subst hq
      norm_num [lhs, Pl] <;> positivity
  · -- general case p > −1
    have hrq : q ≤ r := by
      by_contra h
      replace h := not_le.mp h
      nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 + p) (by linarith : (0 : ℝ) < q - r)]
    have key : (r - q) ^ 2 - (1 - p) ^ 2 = 2 * (1 - p) * (p - q * r) := by
      linear_combination gram
    have hsq : (1 - p) ^ 2 ≤ (r - q) ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - p) hc3]
    have hN : 1 - p + q - r ≤ 0 := by
      by_contra h
      replace h := not_le.mp h
      nlinarith [mul_pos (by linarith : (0 : ℝ) < (1 - p) - (r - q))
        (by linarith : (0 : ℝ) < (1 - p) + (r - q))]
    have hprod : (1 + p + q + r) * (1 + p - q - r) = 2 * (1 + p) * (p - q * r) := by
      linear_combination -gram
    have hAC : 0 ≤ (1 + p + q + r) * (1 + p - q - r) := by
      rw [hprod]; exact mul_nonneg (by linarith) hc3
    have hA0 : 0 ≤ 1 + p + q + r := by
      by_contra h; replace h := not_le.mp h; nlinarith
    have hC0 : 0 ≤ 1 + p - q - r := by
      by_contra h; replace h := not_le.mp h; nlinarith
    -- notation
    unfold lhs
    set LA := 2 * (1 + p + q + r) with hLA
    set LN := 2 * (1 - p + q - r) with hLN
    set LB := 2 * (1 - p - q + r) with hLB
    set LC := 2 * (1 + p - q - r) with hLC
    set IA := 1 + p + 2 * q + 2 * r with hIA
    set IN := 1 - p + 2 * q - 2 * r with hIN
    set IB := 1 - p - 2 * q + 2 * r with hIB
    set IC := 1 + p - 2 * q - 2 * r with hIC
    have hLA0 : 0 ≤ LA := by rw [hLA]; linarith
    have hLB0 : 0 ≤ LB := by rw [hLB]; linarith
    have hLC0 : 0 ≤ LC := by rw [hLC]; linarith
    have hLN0 : LN ≤ 0 := by rw [hLN]; linarith
    have hsum : LA + LB + LC + LN = 8 := by rw [hLA, hLB, hLC, hLN]; ring
    have hAB8 : LA + LB ≤ 8 := by rw [hLA, hLB]; linarith
    have hAC8 : LA + LC ≤ 8 := by rw [hLA, hLC]; linarith
    have hBC8 : LB + LC ≤ 8 := by rw [hLB, hLC]; linarith
    have he2 : LA * LB + LA * LC + LB * LC = 4 * (a1 + a2 + a3) ^ 2 := by
      rw [hS, hLA, hLB, hLC]; ring
    -- values of m
    set mA := 1 + ind IA with hmA
    set mB := 1 + ind IB with hmB
    set mC := 1 + ind IC with hmC
    have hmA1 : 1 ≤ mA := by have := ind_nonneg IA; linarith
    have hmB1 : 1 ≤ mB := by have := ind_nonneg IB; linarith
    have hmC1 : 1 ≤ mC := by have := ind_nonneg IC; linarith
    have hIBpos : ¬ IB ≤ 0 → mB = 1 := by intro h; rw [hmB]; unfold ind; rw [if_neg h]; ring
    -- single-term estimate: m·𝒫(λ) ≤ m ψ(λ) λ (sum of the other two λ)
    have tA : Pl LA * mA ≤ mA * ψ LA * LA * (LB + LC) := by
      have h := Pl_le hLA0 (by linarith)
      have h8 : 8 - LA = LB + LC + LN := by linarith
      have hneg : LA * LN * ψ LA ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hLA0 hLN0) (ψ_nonneg hLA0)
      have h' : LA * (8 - LA) * ψ LA ≤ LA * (LB + LC) * ψ LA := by
        rw [h8]
        have e : LA * (LB + LC + LN) * ψ LA = LA * (LB + LC) * ψ LA + LA * LN * ψ LA := by ring
        rw [e]; linarith
      calc Pl LA * mA ≤ (LA * (LB + LC) * ψ LA) * mA :=
            mul_le_mul_of_nonneg_right (h.trans h') (by linarith)
        _ = mA * ψ LA * LA * (LB + LC) := by ring
    have tB : Pl LB * mB ≤ mB * ψ LB * LB * (LA + LC) := by
      have h := Pl_le hLB0 (by linarith)
      have h8 : 8 - LB = LA + LC + LN := by linarith
      have hneg : LB * LN * ψ LB ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hLB0 hLN0) (ψ_nonneg hLB0)
      have h' : LB * (8 - LB) * ψ LB ≤ LB * (LA + LC) * ψ LB := by
        rw [h8]
        have e : LB * (LA + LC + LN) * ψ LB = LB * (LA + LC) * ψ LB + LB * LN * ψ LB := by ring
        rw [e]; linarith
      calc Pl LB * mB ≤ (LB * (LA + LC) * ψ LB) * mB :=
            mul_le_mul_of_nonneg_right (h.trans h') (by linarith)
        _ = mB * ψ LB * LB * (LA + LC) := by ring
    have tC : Pl LC * mC ≤ mC * ψ LC * LC * (LA + LB) := by
      have h := Pl_le hLC0 (by linarith)
      have h8 : 8 - LC = LA + LB + LN := by linarith
      have hneg : LC * LN * ψ LC ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hLC0 hLN0) (ψ_nonneg hLC0)
      have h' : LC * (8 - LC) * ψ LC ≤ LC * (LA + LB) * ψ LC := by
        rw [h8]
        have e : LC * (LA + LB + LN) * ψ LC = LC * (LA + LB) * ψ LC + LC * LN * ψ LC := by ring
        rw [e]; linarith
      calc Pl LC * mC ≤ (LC * (LA + LB) * ψ LC) * mC :=
            mul_le_mul_of_nonneg_right (h.trans h') (by linarith)
        _ = mC * ψ LC * LC * (LA + LB) := by ring
    have tN : Pl LN = 0 := Pl_nonpos hLN0
    -- linear upper bound for ψ
    have lA := ψ_line hLA0
    have lB := ψ_line hLB0
    have lC := ψ_line hLC0
    -- properties of the indicator
    have mB_eq : 0 < LB → mB = 1 := by
      intro hpos; apply hIBpos; intro h; rw [hIB] at h; rw [hLB] at hpos; linarith
    have mA_cases : mA = 1 ∨ (mA = 2 ∧ LA ≤ 2) := by
      by_cases h : IA ≤ 0
      · right; refine ⟨?_, ?_⟩
        · rw [hmA]; unfold ind; rw [if_pos h]; norm_num
        · rw [hIA] at h; rw [hLA]; linarith
      · left; rw [hmA]; unfold ind; rw [if_neg h]; norm_num
    have mC_cases : mC = 1 ∨ (mC = 2 ∧ LC ≤ 2) := by
      by_cases h : IC ≤ 0
      · right; refine ⟨?_, ?_⟩
        · rw [hmC]; unfold ind; rw [if_pos h]; norm_num
        · rw [hIC] at h; rw [hLC]; linarith
      · left; rw [hmC]; unfold ind; rw [if_neg h]; norm_num
    have notboth : ¬ (IA ≤ 0 ∧ IC ≤ 0) := by
      rintro ⟨h1', h2'⟩; rw [hIA] at h1'; rw [hIC] at h2'; linarith
    have mAC : mA = 1 ∨ mC = 1 := by
      by_cases h : IA ≤ 0
      · right; rw [hmC]; unfold ind
        rw [if_neg (fun h' => notboth ⟨h, h'⟩)]; norm_num
      · left; rw [hmA]; unfold ind; rw [if_neg h]; norm_num
    -- pairwise estimates
    have pair : ∀ X Y mX mY : ℝ, 0 ≤ X → 0 ≤ Y →
        (0 < X → 0 < Y → mX * ψ X + mY * ψ Y ≤ 1 / 2) →
        (mX * ψ X + mY * ψ Y) * (X * Y) ≤ 1 / 2 * (X * Y) := by
      intro X Y mX mY hX hY h
      rcases eq_or_lt_of_le hX with hX0 | hXp
      · rw [← hX0]; simp
      rcases eq_or_lt_of_le hY with hY0 | hYp
      · rw [← hY0]; simp
      exact mul_le_mul_of_nonneg_right (h hXp hYp) (by positivity)
    have pAB := pair LA LB mA mB hLA0 hLB0 (by
      intro _ hb
      rw [mB_eq hb]
      rcases mA_cases with h | ⟨h, h2'⟩
      · rw [h]; linarith
      · rw [h]; linarith)
    have pBC := pair LB LC mB mC hLB0 hLC0 (by
      intro hb _
      rw [mB_eq hb]
      rcases mC_cases with h | ⟨h, h2'⟩
      · rw [h]; linarith
      · rw [h]; linarith)
    have pAC := pair LA LC mA mC hLA0 hLC0 (by
      intro _ _
      rcases mAC with h | h
      · rw [h]
        rcases mC_cases with h' | ⟨h', h2'⟩
        · rw [h']; linarith
        · rw [h']; linarith
      · rw [h]
        rcases mA_cases with h' | ⟨h', h2'⟩
        · rw [h']; linarith
        · rw [h']; linarith)
    -- combine
    rw [tN]
    have hfin : mA * ψ LA * LA * (LB + LC) + mB * ψ LB * LB * (LA + LC)
        + mC * ψ LC * LC * (LA + LB)
        = (mA * ψ LA + mB * ψ LB) * (LA * LB) + (mA * ψ LA + mC * ψ LC) * (LA * LC)
          + (mB * ψ LB + mC * ψ LC) * (LB * LC) := by ring
    linarith [tA, tB, tC, pAB, pBC, pAC, hfin, he2, hD]

/-! ## Removing the same-sign assumption: flipping ω or η -/

lemma lhs_flip_u (p q r : ℝ) : lhs (-p) (-q) r = lhs p q r := by
  unfold lhs; ring_nf

lemma lhs_flip_v (p q r : ℝ) : lhs (-p) q (-r) = lhs p q r := by
  unfold lhs; ring_nf

set_option maxHeartbeats 1000000 in
theorem four_sign_alg (p q r a1 a2 a3 : ℝ)
    (h1 : a1 ^ 2 = 1 - p ^ 2) (h2 : a2 ^ 2 = 1 - q ^ 2) (h3 : a3 ^ 2 = 1 - r ^ 2)
    (h12 : a1 * a2 = r - p * q) (h13 : a1 * a3 = p * r - q) (h23 : a2 * a3 = p - q * r) :
    lhs p q r ≤ 2 * (|a1| + |a2| + |a3|) ^ 2 := by
  -- flip ω: (p,q,r,a₁,a₂,a₃) ↦ (−p,−q,r,−a₁,−a₂,a₃)
  have fu : lhs p q r ≤ 2 * (|a1| + |a2| + |a3|) ^ 2 ↔
      lhs (-p) (-q) r ≤ 2 * (|-a1| + |-a2| + |a3|) ^ 2 := by
    rw [lhs_flip_u, abs_neg, abs_neg]
  have fv : lhs p q r ≤ 2 * (|a1| + |a2| + |a3|) ^ 2 ↔
      lhs (-p) q (-r) ≤ 2 * (|-a1| + |a2| + |-a3|) ^ 2 := by
    rw [lhs_flip_v, abs_neg, abs_neg]
  have fuv : lhs p q r ≤ 2 * (|a1| + |a2| + |a3|) ^ 2 ↔
      lhs p (-q) (-r) ≤ 2 * (|a1| + |-a2| + |-a3|) ^ 2 := by
    rw [show lhs p (-q) (-r) = lhs (-(-p)) (-q) (-r) by rw [neg_neg], lhs_flip_v, lhs_flip_u,
      abs_neg, abs_neg]
  have cu := core (-p) (-q) r (-a1) (-a2) a3 (by linear_combination h1) (by linear_combination h2)
    (by linear_combination h3) (by linear_combination h12) (by linear_combination -h13)
    (by linear_combination -h23)
  have cv := core (-p) q (-r) (-a1) a2 (-a3) (by linear_combination h1) (by linear_combination h2)
    (by linear_combination h3) (by linear_combination -h12) (by linear_combination h13)
    (by linear_combination -h23)
  have cuv := core p (-q) (-r) a1 (-a2) (-a3) (by linear_combination h1)
    (by linear_combination h2) (by linear_combination h3) (by linear_combination -h12)
    (by linear_combination -h13) (by linear_combination h23)
  have c0 := core p q r a1 a2 a3 h1 h2 h3 h12 h13 h23
  rcases le_total 0 a1 with s1 | s1 <;> rcases le_total 0 a2 with s2 | s2 <;>
    rcases le_total 0 a3 with s3 | s3
  -- (+,+,+)
  · exact c0 (mul_nonneg s1 s2) (mul_nonneg s1 s3) (mul_nonneg s2 s3)
  -- (+,+,−): flip ω → (−,−,−)
  · exact fu.2 (cu (by nlinarith) (by nlinarith) (by nlinarith))
  -- (+,−,+): flip η → (−,−,−)
  · exact fv.2 (cv (by nlinarith) (by nlinarith) (by nlinarith))
  -- (+,−,−): flip both → (+,+,+)
  · exact fuv.2 (cuv (by nlinarith) (by nlinarith) (by nlinarith))
  -- (−,+,+): flip both → (−,−,−)
  · exact fuv.2 (cuv (by nlinarith) (by nlinarith) (by nlinarith))
  -- (−,+,−): flip η → (+,+,+)
  · exact fv.2 (cv (by nlinarith) (by nlinarith) (by nlinarith))
  -- (−,−,+): flip ω → (+,+,+)
  · exact fu.2 (cu (by nlinarith) (by nlinarith) (by nlinarith))
  -- (−,−,−)
  · exact c0 (by nlinarith) (by nlinarith) (by nlinarith)

end

end SteinTomas.FourSign

#print axioms SteinTomas.FourSign.four_sign_alg
