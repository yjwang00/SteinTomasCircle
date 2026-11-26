import Mathlib
import SteinTomasCircle.Basic.Elementary
import SteinTomasCircle.Section2.Analysis

/-!
# Integral estimates U, V, W in Lemma 2.1 (lem:local-bessel)

Literature hypotheses (stated explicitly as premises of the theorems):
* DLMF 10.2.2: on [0, 7/4], J₀ and J₂ are given by their power series (`SeriesHyp`);
* J₀ and J₂ are continuous on [0, 7/4] (DLMF 10.2: J_ν is entire).

Conclusions:
* V = ∫₀^{7/4} J₀⁴J₂² r dr < 3/400
* U = ∫₀^{7/4} J₀⁴κ² r dr < 3/250000, κ(r) = (r/2)⁴/4!
* W = ∫₀^{7/4} J₀⁶ r dr > 3059/10000
-/

namespace SteinTomas.Lemma21

open Real Set MeasureTheory intervalIntegral SteinTomas.Analysis1

/-- DLMF 10.2.2 for J₀ and J₂ on [0, 7/4] (x = r²/4) -/
def SeriesHyp (J0 J2 : ℝ → ℝ) : Prop :=
  (∀ r ∈ Icc (0 : ℝ) (7 / 4), HasSum (fun m : ℕ => (-1) ^ m *
      ((r ^ 2 / 4) ^ m / ((m.factorial : ℝ)) ^ 2)) (J0 r)) ∧
  (∀ r ∈ Icc (0 : ℝ) (7 / 4), HasSum (fun m : ℕ => (-1) ^ m *
      ((r ^ 2 / 4) ^ (m + 1) / ((m.factorial : ℝ) * ((m + 2).factorial : ℝ)))) (J2 r))

variable {J0 J2 : ℝ → ℝ}

/-- Pointwise estimates (t = r²/8): 0 ≤ J₀ ≤ (1−t)², J₀ ≥ (1−t)² − (2/9)t³, 0 ≤ J₂ ≤ t(1 − t/2) -/
theorem pointwise (hs : SeriesHyp J0 J2) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (7 / 4)) :
    0 ≤ J0 r ∧ J0 r ≤ (1 - r ^ 2 / 8) ^ 2 ∧ (1 - r ^ 2 / 8) ^ 2 - 2 / 9 * (r ^ 2 / 8) ^ 3 ≤ J0 r
      ∧ 0 ≤ J2 r ∧ J2 r ≤ r ^ 2 / 8 * (1 - r ^ 2 / 8 / 2) := by
  obtain ⟨hr0, hr1⟩ := hr
  have hx0 : 0 ≤ r ^ 2 / 4 := by positivity
  have hx1 : r ^ 2 / 4 ≤ 49 / 64 := by nlinarith
  obtain ⟨l0, u0⟩ := J0_bounds hx0 (by linarith) (hs.1 r ⟨hr0, hr1⟩)
  obtain ⟨l2, u2⟩ := J2_bounds hx0 (by linarith) (hs.2 r ⟨hr0, hr1⟩)
  obtain ⟨p0, p2, -, -⟩ := bessel_pointwise hx0 hx1 (hs.1 r ⟨hr0, hr1⟩) (hs.2 r ⟨hr0, hr1⟩)
  have ht : r ^ 2 / 8 ≤ 1 := by nlinarith
  have ht0 : 0 ≤ r ^ 2 / 8 := by positivity
  refine ⟨p0.le, by nlinarith, by nlinarith, p2, ?_⟩
  have : (r ^ 2 / 8) ^ 3 / 6 ≤ (r ^ 2 / 8) ^ 2 / 6 := by
    have := mul_le_mul_of_nonneg_left ht (sq_nonneg (r ^ 2 / 8))
    nlinarith
  nlinarith

/-- Substitution t = r²/8: ∫₀^b g(r²/8)·r dr = 4∫₀^{b²/8} g(t) dt -/
theorem subst (g : ℝ → ℝ) (hg : Continuous g) (b : ℝ) :
    ∫ r in (0 : ℝ)..b, g (r ^ 2 / 8) * r = 4 * ∫ t in (0 : ℝ)..(b ^ 2 / 8), g t := by
  have h := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := b)
    (f := fun r : ℝ => r ^ 2 / 8) (f' := fun r : ℝ => r / 4) (g := g)
    (fun x _ => by
      have := (hasDerivAt_pow 2 x).div_const 8
      convert this using 1
      push_cast; ring)
    (by fun_prop) hg
  have e : (fun r : ℝ => g (r ^ 2 / 8) * r)
      = fun r : ℝ => 4 * ((g ∘ fun r : ℝ => r ^ 2 / 8) r * (r / 4)) := by
    funext r; simp only [Function.comp]; ring
  rw [e, intervalIntegral.integral_const_mul, h]
  norm_num

/-- Tangent-line inequality (convexity of s ↦ s⁶): 0 ≤ c ≤ a ⇒ a⁶ − 6a⁵(a−c) ≤ c⁶ -/
theorem tangent6 {a c : ℝ} (hc : 0 ≤ c) (hca : c ≤ a) : a ^ 6 - 6 * a ^ 5 * (a - c) ≤ c ^ 6 := by
  have ha : 0 ≤ a := le_trans hc hca
  have e : a ^ 6 - c ^ 6
      = (a - c) * (a ^ 5 + a ^ 4 * c + a ^ 3 * c ^ 2 + a ^ 2 * c ^ 3 + a * c ^ 4 + c ^ 5) := by ring
  have t1 : a ^ 4 * c ≤ a ^ 4 * a := mul_le_mul_of_nonneg_left hca (by positivity)
  have t2 : a ^ 3 * c ^ 2 ≤ a ^ 3 * a ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc hca 2) (by positivity)
  have t3 : a ^ 2 * c ^ 3 ≤ a ^ 2 * a ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc hca 3) (by positivity)
  have t4 : a * c ^ 4 ≤ a * a ^ 4 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc hca 4) ha
  have t5 : c ^ 5 ≤ a ^ 5 := pow_le_pow_left₀ hc hca 5
  have hs : a ^ 5 + a ^ 4 * c + a ^ 3 * c ^ 2 + a ^ 2 * c ^ 3 + a * c ^ 4 + c ^ 5 ≤ 6 * a ^ 5 := by
    nlinarith
  have := mul_le_mul_of_nonneg_left hs (sub_nonneg.2 hca)
  nlinarith

lemma Icc_uIcc {b : ℝ} (hb : 0 ≤ b) : uIcc (0 : ℝ) b = Icc 0 b := uIcc_of_le hb

set_option maxHeartbeats 1000000 in
/-- (eq:local-V) V < 3/400 -/
theorem V_lt (hs : SeriesHyp J0 J2) (hc0 : ContinuousOn J0 (Icc 0 (7 / 4)))
    (hc2 : ContinuousOn J2 (Icc 0 (7 / 4))) :
    ∫ r in (0 : ℝ)..(7 / 4), J0 r ^ 4 * J2 r ^ 2 * r < 3 / 400 := by
  set g : ℝ → ℝ := fun t => t ^ 2 * (1 - t) ^ 8 * (1 - t / 2) with hg
  have hgc : Continuous g := by fun_prop
  have hint1 : IntervalIntegrable (fun r => J0 r ^ 4 * J2 r ^ 2 * r) volume 0 (7 / 4) := by
    apply ContinuousOn.intervalIntegrable
    rw [Icc_uIcc (by norm_num)]
    exact ((hc0.pow 4).mul (hc2.pow 2)).mul continuousOn_id
  have hint2 : IntervalIntegrable (fun r : ℝ => g (r ^ 2 / 8) * r) volume 0 (7 / 4) :=
    (by fun_prop : Continuous fun r : ℝ => g (r ^ 2 / 8) * r).intervalIntegrable _ _
  have step1 : ∫ r in (0 : ℝ)..(7 / 4), J0 r ^ 4 * J2 r ^ 2 * r
      ≤ ∫ r in (0 : ℝ)..(7 / 4), g (r ^ 2 / 8) * r := by
    apply intervalIntegral.integral_mono_on (by norm_num) hint1 hint2
    intro r hr
    obtain ⟨p0, u0, -, p2, u2⟩ := pointwise hs hr
    have hr0 : 0 ≤ r := hr.1
    set t := r ^ 2 / 8 with ht
    have ht1 : t ≤ 1 := by rw [ht]; nlinarith [hr.2]
    have ht0 : 0 ≤ t := by rw [ht]; positivity
    have a := pow_le_pow_left₀ p0 u0 4
    have b := pow_le_pow_left₀ p2 u2 2
    have b' : (t * (1 - t / 2)) ^ 2 ≤ t ^ 2 * (1 - t / 2) := by
      have := mul_le_mul_of_nonneg_left (show (1 - t / 2) ^ 2 ≤ 1 - t / 2 by nlinarith)
        (sq_nonneg t)
      nlinarith
    have c := mul_le_mul a (b.trans b') (sq_nonneg _) (by positivity)
    have d := mul_le_mul_of_nonneg_right c hr0
    calc J0 r ^ 4 * J2 r ^ 2 * r ≤ ((1 - t) ^ 2) ^ 4 * (t ^ 2 * (1 - t / 2)) * r := d
      _ = g t * r := by simp only [hg]; ring
  have step2 : ∫ r in (0 : ℝ)..(7 / 4), g (r ^ 2 / 8) * r = 4 * ∫ t in (0 : ℝ)..(49 / 128), g t := by
    rw [subst g hgc]; norm_num
  have step3 : ∫ t in (0 : ℝ)..(49 / 128), g t ≤ ∫ t in (0 : ℝ)..1, g t := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hgc.intervalIntegrable (μ := volume) 0 (49 / 128)) (hgc.intervalIntegrable (μ := volume) (49 / 128) 1)
    have hnn : 0 ≤ ∫ t in (49 / 128 : ℝ)..1, g t := by
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro t ht; simp only [hg]
      have : 0 ≤ 1 - t := by linarith [ht.2]
      have : 0 ≤ 1 - t / 2 := by linarith [ht.2]
      have : 0 ≤ t := by linarith [ht.1]
      positivity
    linarith
  have hval : ∫ t in (0 : ℝ)..1, g t = 7 / 3960 := by rw [hg]; exact integral_V
  rw [hval] at step3
  linarith

set_option maxHeartbeats 1000000 in
/-- (eq:local-E) U < 3/250000, κ(r) = (r/2)⁴/24 -/
theorem U_lt (hs : SeriesHyp J0 J2) (hc0 : ContinuousOn J0 (Icc 0 (7 / 4))) :
    ∫ r in (0 : ℝ)..(7 / 4), J0 r ^ 4 * ((r / 2) ^ 4 / 24) ^ 2 * r < 3 / 250000 := by
  set g : ℝ → ℝ := fun t => t ^ 4 * (1 - t) ^ 8 / 36 with hg
  have hgc : Continuous g := by fun_prop
  have hint1 : IntervalIntegrable (fun r => J0 r ^ 4 * ((r / 2) ^ 4 / 24) ^ 2 * r) volume 0 (7 / 4) := by
    apply ContinuousOn.intervalIntegrable
    rw [Icc_uIcc (by norm_num)]
    exact ((hc0.pow 4).mul (Continuous.continuousOn (by fun_prop))).mul continuousOn_id
  have hint2 : IntervalIntegrable (fun r : ℝ => g (r ^ 2 / 8) * r) volume 0 (7 / 4) :=
    (by fun_prop : Continuous fun r : ℝ => g (r ^ 2 / 8) * r).intervalIntegrable _ _
  have step1 : ∫ r in (0 : ℝ)..(7 / 4), J0 r ^ 4 * ((r / 2) ^ 4 / 24) ^ 2 * r
      ≤ ∫ r in (0 : ℝ)..(7 / 4), g (r ^ 2 / 8) * r := by
    apply intervalIntegral.integral_mono_on (by norm_num) hint1 hint2
    intro r hr
    obtain ⟨p0, u0, -, -, -⟩ := pointwise hs hr
    have hr0 : 0 ≤ r := hr.1
    have a := pow_le_pow_left₀ p0 u0 4
    have c := mul_le_mul_of_nonneg_right a (by positivity : (0 : ℝ) ≤ ((r / 2) ^ 4 / 24) ^ 2)
    have d := mul_le_mul_of_nonneg_right c hr0
    calc J0 r ^ 4 * ((r / 2) ^ 4 / 24) ^ 2 * r
        ≤ ((1 - r ^ 2 / 8) ^ 2) ^ 4 * ((r / 2) ^ 4 / 24) ^ 2 * r := d
      _ = g (r ^ 2 / 8) * r := by simp only [hg]; ring
  have step2 : ∫ r in (0 : ℝ)..(7 / 4), g (r ^ 2 / 8) * r = 4 * ∫ t in (0 : ℝ)..(49 / 128), g t := by
    rw [subst g hgc]; norm_num
  have step3 : ∫ t in (0 : ℝ)..(49 / 128), g t ≤ ∫ t in (0 : ℝ)..(2 / 5), g t := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hgc.intervalIntegrable (μ := volume) 0 (49 / 128))
      (hgc.intervalIntegrable (μ := volume) (49 / 128) (2 / 5))
    have hnn : 0 ≤ ∫ t in (49 / 128 : ℝ)..(2 / 5), g t := by
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro t _; simp only [hg]; positivity
    linarith
  have hval : ∫ t in (0 : ℝ)..(2 / 5), g t = 157948768 / 1571044921875 / 36 := by
    simp only [hg]; rw [intervalIntegral.integral_div, integral_U]
  rw [hval] at step3
  have := U_numeric
  linarith

set_option maxHeartbeats 1000000 in
/-- (eq:local-W) W > 3059/10000 -/
theorem W_gt (hs : SeriesHyp J0 J2) (hc0 : ContinuousOn J0 (Icc 0 (7 / 4))) :
    3059 / 10000 < ∫ r in (0 : ℝ)..(7 / 4), J0 r ^ 6 * r := by
  set g : ℝ → ℝ := fun t => (1 - t) ^ 12 - 4 / 3 * t ^ 3 * (1 - t) ^ 10 with hg
  have hgc : Continuous g := by fun_prop
  have hs3 : Real.sqrt 3 ≤ 7 / 4 := by
    rw [show (7 / 4 : ℝ) = Real.sqrt ((7 / 4) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs30 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hcont : ContinuousOn (fun r => J0 r ^ 6 * r) (Icc 0 (7 / 4)) :=
    (hc0.pow 6).mul continuousOn_id
  have hintA : IntervalIntegrable (fun r => J0 r ^ 6 * r) volume 0 (Real.sqrt 3) := by
    apply ContinuousOn.intervalIntegrable
    rw [Icc_uIcc hs30]
    exact hcont.mono (Icc_subset_Icc le_rfl hs3)
  have hintB : IntervalIntegrable (fun r => J0 r ^ 6 * r) volume (Real.sqrt 3) (7 / 4) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hs3]
    exact hcont.mono (Icc_subset_Icc hs30 le_rfl)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hintA hintB
  have hnnB : 0 ≤ ∫ r in (Real.sqrt 3)..(7 / 4), J0 r ^ 6 * r := by
    apply intervalIntegral.integral_nonneg hs3
    intro r hr
    have : 0 ≤ r := le_trans hs30 hr.1
    positivity
  have hint2 : IntervalIntegrable (fun r : ℝ => g (r ^ 2 / 8) * r) volume 0 (Real.sqrt 3) :=
    (by fun_prop : Continuous fun r : ℝ => g (r ^ 2 / 8) * r).intervalIntegrable _ _
  have step1 : ∫ r in (0 : ℝ)..(Real.sqrt 3), g (r ^ 2 / 8) * r
      ≤ ∫ r in (0 : ℝ)..(Real.sqrt 3), J0 r ^ 6 * r := by
    apply intervalIntegral.integral_mono_on hs30 hint2 hintA
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) (7 / 4) := ⟨hr.1, le_trans hr.2 hs3⟩
    obtain ⟨-, -, l0, -, -⟩ := pointwise hs hr'
    have hr0 : 0 ≤ r := hr.1
    set t := r ^ 2 / 8 with ht
    have ht38 : t ≤ 3 / 8 := by
      have h3 : r ^ 2 ≤ 3 := by
        have := pow_le_pow_left₀ hr0 hr.2 2
        rwa [Real.sq_sqrt (by norm_num)] at this
      rw [ht]; linarith
    have ht0 : 0 ≤ t := by rw [ht]; positivity
    have hc : 0 ≤ (1 - t) ^ 2 - 2 / 9 * t ^ 3 := by
      nlinarith [pow_le_pow_left₀ ht0 ht38 3, pow_nonneg ht0 3]
    have hpow := pow_le_pow_left₀ hc l0 6
    have htan := tangent6 hc (show (1 - t) ^ 2 - 2 / 9 * t ^ 3 ≤ (1 - t) ^ 2 by nlinarith [pow_nonneg ht0 3])
    have key : g t ≤ J0 r ^ 6 := by
      simp only [hg]
      have e : ((1 - t) ^ 2) ^ 6 - 6 * ((1 - t) ^ 2) ^ 5 * ((1 - t) ^ 2 - ((1 - t) ^ 2 - 2 / 9 * t ^ 3))
          = (1 - t) ^ 12 - 4 / 3 * t ^ 3 * (1 - t) ^ 10 := by ring
      linarith
    exact mul_le_mul_of_nonneg_right key hr0
  have step2 : ∫ r in (0 : ℝ)..(Real.sqrt 3), g (r ^ 2 / 8) * r
      = 4 * ∫ t in (0 : ℝ)..(3 / 8), g t := by
    rw [subst g hgc, Real.sq_sqrt (by norm_num)]
    try norm_num
  have hval : ∫ t in (0 : ℝ)..(3 / 8), g t = 168338674201695 / 2201222278807552 := by
    rw [hg]; exact integral_W
  have := W_numeric
  rw [step2, hval] at step1
  linarith

end SteinTomas.Lemma21

#print axioms SteinTomas.Lemma21.V_lt
#print axioms SteinTomas.Lemma21.U_lt
#print axioms SteinTomas.Lemma21.W_gt
