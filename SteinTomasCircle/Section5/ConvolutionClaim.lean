import Mathlib
import SteinTomasCircle.Basic.Defs
import SteinTomasCircle.Section2.PairChangeOfVariables
import SteinTomasCircle.Section4.Residual

/-!
# Section 5 (II): Claim ‖h*(fσ)‖₂² ≤ (3/4)‖f‖₁²‖h‖₂²

Everything is stated with ℝ≥0∞-valued Lebesgue integrals (f, h ≥ 0).
* `pair_bound`: strip argument ‖h(·−e)+h(·+e)‖₂² ≤ 3‖h‖₂² (supp h ⊂ {|y|<2})
* `conv_sym`: antipodal ⇒ 2(h*fσ)(x) = ∫ f(θ)[h(x−ω)+h(x+ω)]
* `cs_w`, `cs2`: Cauchy–Schwarz
* `conv_bound`: 4‖h*fσ‖₂² ≤ 3‖f‖₁²‖h‖₂²
-/

namespace SteinTomas.S5B

open Real MeasureTheory Set Function
open scoped ENNReal

noncomputable section

/-- ω(θ) = (cos θ, sin θ) -/
def om (θ : ℝ) : ℝ × ℝ := (Real.cos θ, Real.sin θ)

/-- x·ω(θ) -/
def dt (x : ℝ × ℝ) (θ : ℝ) : ℝ := x.1 * Real.cos θ + x.2 * Real.sin θ

lemma om_meas : Measurable om :=
  (show Continuous fun θ : ℝ => (Real.cos θ, Real.sin θ) by fun_prop).measurable

lemma om_add_pi (θ : ℝ) : om (π + θ) = -om θ := by
  rw [add_comm]; unfold om; rw [Real.cos_add_pi, Real.sin_add_pi]; rfl

lemma om_two_pi (θ : ℝ) : om (θ + 2 * π) = om θ := by
  unfold om; rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

lemma top_sq : (⊤ : ℝ≥0∞) ^ 2 = ⊤ := by rw [sq, ENNReal.top_mul_top]

lemma two_mul_le_sq (a b : ℝ≥0∞) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · rw [top_sq, top_add]; exact le_top
  rcases eq_or_ne b ⊤ with rfl | hb
  · rw [top_sq, add_top]; exact le_top
  lift a to NNReal using ha
  lift b to NNReal using hb
  have h : (2 * a * b : NNReal) ≤ a ^ 2 + b ^ 2 := by
    rw [← NNReal.coe_le_coe]; push_cast; nlinarith [sq_nonneg ((a : ℝ) - b)]
  exact_mod_cast h

lemma dt_sq_le (x : ℝ × ℝ) (θ : ℝ) : dt x θ ^ 2 ≤ nsq x := by
  have h1 := Real.sin_sq_add_cos_sq θ
  have e : dt x θ ^ 2 + (x.1 * Real.sin θ - x.2 * Real.cos θ) ^ 2
      = nsq x * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by unfold dt nsq; ring
  rw [h1, mul_one] at e
  nlinarith [sq_nonneg (x.1 * Real.sin θ - x.2 * Real.cos θ)]

lemma nsq_sub_om (x : ℝ × ℝ) (θ : ℝ) : nsq (x - om θ) = nsq x - 2 * dt x θ + 1 := by
  have h1 := Real.sin_sq_add_cos_sq θ
  unfold nsq om dt; simp only [Prod.fst_sub, Prod.snd_sub]; linear_combination h1

lemma nsq_add_om (x : ℝ × ℝ) (θ : ℝ) : nsq (x + om θ) = nsq x + 2 * dt x θ + 1 := by
  have h1 := Real.sin_sq_add_cos_sq θ
  unfold nsq om dt; simp only [Prod.fst_add, Prod.snd_add]; linear_combination h1

lemma dt_add_om (y : ℝ × ℝ) (θ : ℝ) : dt (y + om θ) θ = dt y θ + 1 := by
  have h1 := Real.sin_sq_add_cos_sq θ
  unfold dt om; simp only [Prod.fst_add, Prod.snd_add]; linear_combination h1

lemma dt_sub_om (y : ℝ × ℝ) (θ : ℝ) : dt (y - om θ) θ = dt y θ - 1 := by
  have h1 := Real.sin_sq_add_cos_sq θ
  unfold dt om; simp only [Prod.fst_sub, Prod.snd_sub]; linear_combination (-1 : ℝ) * h1

lemma strip (x : ℝ × ℝ) (θ : ℝ) (h1 : nsq (x - om θ) < 4) (h2 : nsq (x + om θ) < 4) :
    |dt x θ| < 1 := by
  rw [nsq_sub_om] at h1; rw [nsq_add_om] at h2
  have h3 := dt_sq_le x θ
  rw [abs_lt]; constructor <;> nlinarith

/-- Strip indicator 1{|x·e|<1} -/
def ind (θ : ℝ) (x : ℝ × ℝ) : ℝ≥0∞ := if |dt x θ| < 1 then 1 else 0

lemma ind_meas (θ : ℝ) : Measurable (ind θ) := by
  unfold ind
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_lt (f := fun x : ℝ × ℝ => |dt x θ|)
    (Continuous.measurable (by unfold dt; fun_prop)) measurable_const

lemma ind_sum (y : ℝ × ℝ) (θ : ℝ) : ind θ (y + om θ) + ind θ (y - om θ) ≤ 1 := by
  unfold ind; rw [dt_add_om, dt_sub_om]
  by_cases h1 : |dt y θ + 1| < 1
  · have h2 : ¬ |dt y θ - 1| < 1 := by
      intro h2; rw [abs_lt] at h1 h2; linarith
    rw [if_pos h1, if_neg h2, add_zero]
  · rw [if_neg h1, zero_add]; split_ifs <;> simp

variable {H : ℝ × ℝ → ℝ≥0∞}

lemma pt (hH : ∀ y, 4 ≤ nsq y → H y = 0) (x : ℝ × ℝ) (θ : ℝ) :
    2 * H (x - om θ) * H (x + om θ)
      ≤ H (x - om θ) ^ 2 * ind θ x + H (x + om θ) ^ 2 * ind θ x := by
  by_cases h1 : nsq (x - om θ) < 4
  · by_cases h2 : nsq (x + om θ) < 4
    · have : ind θ x = 1 := by unfold ind; rw [if_pos (strip x θ h1 h2)]
      rw [this, mul_one, mul_one]; exact two_mul_le_sq _ _
    · rw [hH _ (not_lt.1 h2)]; simp
  · rw [hH _ (not_lt.1 h1)]; simp

/-- Strip argument: ‖h(·−e)+h(·+e)‖₂² ≤ 3‖h‖₂² -/
theorem pair_bound (hHm : Measurable H) (hH : ∀ y, 4 ≤ nsq y → H y = 0) (θ : ℝ) :
    ∫⁻ x, (H (x - om θ) + H (x + om θ)) ^ 2 ≤ 3 * ∫⁻ y, H y ^ 2 := by
  have hA : Measurable fun x : ℝ × ℝ => H (x - om θ) ^ 2 :=
    (hHm.comp (measurable_id.sub_const _)).pow_const 2
  have hB : Measurable fun x : ℝ × ℝ => H (x + om θ) ^ 2 :=
    (hHm.comp (measurable_id.add_const _)).pow_const 2
  have hAB : Measurable fun x : ℝ × ℝ => H (x - om θ) ^ 2 + H (x + om θ) ^ 2 := hA.add hB
  have hAi : Measurable fun x : ℝ × ℝ => H (x - om θ) ^ 2 * ind θ x := hA.mul (ind_meas θ)
  have step1 : ∫⁻ x, (H (x - om θ) + H (x + om θ)) ^ 2
      ≤ ∫⁻ x, (H (x - om θ) ^ 2 + H (x + om θ) ^ 2
          + (H (x - om θ) ^ 2 * ind θ x + H (x + om θ) ^ 2 * ind θ x)) := by
    refine lintegral_mono (fun x => ?_)
    have := pt hH x θ
    calc (H (x - om θ) + H (x + om θ)) ^ 2
        = H (x - om θ) ^ 2 + H (x + om θ) ^ 2 + 2 * H (x - om θ) * H (x + om θ) := by ring
      _ ≤ _ := add_le_add le_rfl this
  rw [lintegral_add_left hAB, lintegral_add_left hA, lintegral_add_left hAi] at step1
  have tA : ∫⁻ x, H (x - om θ) ^ 2 = ∫⁻ y, H y ^ 2 :=
    lintegral_sub_right_eq_self (fun y => H y ^ 2) (om θ)
  have tB : ∫⁻ x, H (x + om θ) ^ 2 = ∫⁻ y, H y ^ 2 :=
    lintegral_add_right_eq_self (fun y => H y ^ 2) (om θ)
  have tAi : ∫⁻ x, H (x - om θ) ^ 2 * ind θ x = ∫⁻ y, H y ^ 2 * ind θ (y + om θ) := by
    have := lintegral_add_right_eq_self (μ := (volume : Measure (ℝ × ℝ)))
      (fun x : ℝ × ℝ => H (x - om θ) ^ 2 * ind θ x) (om θ)
    simp only [add_sub_cancel_right] at this
    exact this.symm
  have tBi : ∫⁻ x, H (x + om θ) ^ 2 * ind θ x = ∫⁻ y, H y ^ 2 * ind θ (y - om θ) := by
    have := lintegral_sub_right_eq_self (μ := (volume : Measure (ℝ × ℝ)))
      (fun x : ℝ × ℝ => H (x + om θ) ^ 2 * ind θ x) (om θ)
    simp only [sub_add_cancel] at this
    exact this.symm
  have hm1 : Measurable fun y : ℝ × ℝ => H y ^ 2 * ind θ (y + om θ) :=
    (hHm.pow_const 2).mul ((ind_meas θ).comp (measurable_id.add_const _))
  have hsum : (∫⁻ y, H y ^ 2 * ind θ (y + om θ)) + ∫⁻ y, H y ^ 2 * ind θ (y - om θ)
      ≤ ∫⁻ y, H y ^ 2 := by
    rw [← lintegral_add_left hm1]
    refine lintegral_mono (fun y => ?_)
    calc H y ^ 2 * ind θ (y + om θ) + H y ^ 2 * ind θ (y - om θ)
        = H y ^ 2 * (ind θ (y + om θ) + ind θ (y - om θ)) := by ring
      _ ≤ H y ^ 2 * 1 := mul_le_mul_of_nonneg_left (ind_sum y θ) (by positivity)
      _ = H y ^ 2 := mul_one _
  rw [tA, tB, tAi, tBi] at step1
  calc _ ≤ _ := step1
    _ ≤ (∫⁻ y, H y ^ 2) + (∫⁻ y, H y ^ 2) + ∫⁻ y, H y ^ 2 := add_le_add le_rfl hsum
    _ = 3 * ∫⁻ y, H y ^ 2 := by ring

/-- Weighted Cauchy–Schwarz: (∫FG)² ≤ (∫F)(∫FG²) -/
lemma cs_w {α : Type*} [MeasurableSpace α] (μ : Measure α) {F G : α → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) :
    (∫⁻ a, F a * G a ∂μ) ^ 2 ≤ (∫⁻ a, F a ∂μ) * ∫⁻ a, F a * G a ^ 2 ∂μ := by
  have hFG : Measurable fun a => F a * G a := hF.mul hG
  have hFG2 : Measurable fun a => F a * G a ^ 2 := hF.mul (hG.pow_const 2)
  have e1 : (∫⁻ a, F a * G a ∂μ) ^ 2 = ∫⁻ a, ∫⁻ b, (F a * G a) * (F b * G b) ∂μ ∂μ := by
    rw [sq, ← lintegral_mul_const _ hFG]
    refine lintegral_congr (fun a => ?_)
    rw [lintegral_const_mul _ hFG]
  have i1 : ∀ a, ∫⁻ b, (F a * F b * G a ^ 2 + F a * F b * G b ^ 2) ∂μ
      = (F a * G a ^ 2) * (∫⁻ b, F b ∂μ) + F a * ∫⁻ b, F b * G b ^ 2 ∂μ := by
    intro a
    rw [show (fun b => F a * F b * G a ^ 2 + F a * F b * G b ^ 2)
        = fun b => (F a * G a ^ 2) * F b + F a * (F b * G b ^ 2) by funext b; ring]
    rw [lintegral_add_left (hF.const_mul _), lintegral_const_mul _ hF, lintegral_const_mul _ hFG2]
  have e2 : ∫⁻ a, ∫⁻ b, (F a * F b * G a ^ 2 + F a * F b * G b ^ 2) ∂μ ∂μ
      = 2 * ((∫⁻ a, F a ∂μ) * ∫⁻ a, F a * G a ^ 2 ∂μ) := by
    simp_rw [i1]
    rw [lintegral_add_left (hFG2.mul_const _), lintegral_mul_const _ hFG2, lintegral_mul_const _ hF]
    ring
  have key : 2 * (∫⁻ a, F a * G a ∂μ) ^ 2 ≤ 2 * ((∫⁻ a, F a ∂μ) * ∫⁻ a, F a * G a ^ 2 ∂μ) := by
    rw [e1, ← e2, ← lintegral_const_mul' 2 _ (by norm_num)]
    refine lintegral_mono (fun a => ?_)
    rw [← lintegral_const_mul' 2 _ (by norm_num)]
    refine lintegral_mono (fun b => ?_)
    calc 2 * ((F a * G a) * (F b * G b)) = F a * F b * (2 * G a * G b) := by ring
      _ ≤ F a * F b * (G a ^ 2 + G b ^ 2) :=
          mul_le_mul_of_nonneg_left (two_mul_le_sq _ _) (by positivity)
      _ = F a * F b * G a ^ 2 + F a * F b * G b ^ 2 := by ring
  exact S4R.ecancel 2 (by norm_num) (by norm_num) key

/-- Cauchy–Schwarz: (∫uv)² ≤ (∫u²)(∫v²) -/
lemma cs2 {α : Type*} [MeasurableSpace α] (μ : Measure α) {u v : α → ℝ≥0∞}
    (hu : Measurable u) (hv : Measurable v) :
    (∫⁻ a, u a * v a ∂μ) ^ 2 ≤ (∫⁻ a, u a ^ 2 ∂μ) * ∫⁻ a, v a ^ 2 ∂μ := by
  have huv : Measurable fun a => u a * v a := hu.mul hv
  have hu2 : Measurable fun a => u a ^ 2 := hu.pow_const 2
  have hv2 : Measurable fun a => v a ^ 2 := hv.pow_const 2
  have e1 : (∫⁻ a, u a * v a ∂μ) ^ 2 = ∫⁻ a, ∫⁻ b, (u a * v a) * (u b * v b) ∂μ ∂μ := by
    rw [sq, ← lintegral_mul_const _ huv]
    refine lintegral_congr (fun a => ?_)
    rw [lintegral_const_mul _ huv]
  have i1 : ∀ a, ∫⁻ b, (u a ^ 2 * v b ^ 2 + u b ^ 2 * v a ^ 2) ∂μ
      = u a ^ 2 * (∫⁻ b, v b ^ 2 ∂μ) + v a ^ 2 * ∫⁻ b, u b ^ 2 ∂μ := by
    intro a
    rw [show (fun b => u a ^ 2 * v b ^ 2 + u b ^ 2 * v a ^ 2)
        = fun b => u a ^ 2 * v b ^ 2 + v a ^ 2 * u b ^ 2 by funext b; ring]
    rw [lintegral_add_left (hv2.const_mul _), lintegral_const_mul _ hv2, lintegral_const_mul _ hu2]
  have e2 : ∫⁻ a, ∫⁻ b, (u a ^ 2 * v b ^ 2 + u b ^ 2 * v a ^ 2) ∂μ ∂μ
      = 2 * ((∫⁻ a, u a ^ 2 ∂μ) * ∫⁻ a, v a ^ 2 ∂μ) := by
    simp_rw [i1]
    rw [lintegral_add_left (hu2.mul_const _), lintegral_mul_const _ hu2, lintegral_mul_const _ hv2]
    ring
  have key : 2 * (∫⁻ a, u a * v a ∂μ) ^ 2 ≤ 2 * ((∫⁻ a, u a ^ 2 ∂μ) * ∫⁻ a, v a ^ 2 ∂μ) := by
    rw [e1, ← e2, ← lintegral_const_mul' 2 _ (by norm_num)]
    refine lintegral_mono (fun a => ?_)
    rw [← lintegral_const_mul' 2 _ (by norm_num)]
    refine lintegral_mono (fun b => ?_)
    calc 2 * ((u a * v a) * (u b * v b)) = 2 * (u a * v b) * (u b * v a) := by ring
      _ ≤ (u a * v b) ^ 2 + (u b * v a) ^ 2 := two_mul_le_sq _ _
      _ = u a ^ 2 * v b ^ 2 + u b ^ 2 * v a ^ 2 := by ring
  exact S4R.ecancel 2 (by norm_num) (by norm_num) key

/-- (h*fσ)(x) = ∫ f(θ) h(x−ω(θ)) dθ -/
def conv (F : ℝ → ℝ≥0∞) (H : ℝ × ℝ → ℝ≥0∞) (x : ℝ × ℝ) : ℝ≥0∞ :=
  ∫⁻ θ in Ioc 0 (2 * π), F θ * H (x - om θ)

lemma conv_meas {F : ℝ → ℝ≥0∞} (hFm : Measurable F) (hHm : Measurable H) :
    Measurable (conv F H) := by
  have hm : Measurable fun p : (ℝ × ℝ) × ℝ => F p.2 * H (p.1 - om p.2) :=
    (hFm.comp measurable_snd).mul (hHm.comp (measurable_fst.sub (om_meas.comp measurable_snd)))
  exact hm.lintegral_prod_right'

lemma conv_sym {F : ℝ → ℝ≥0∞} (hFm : Measurable F) (hFp : Periodic F (2 * π))
    (hFa : ∀ θ, F (θ + π) = F θ) (hHm : Measurable H) (x : ℝ × ℝ) :
    2 * conv F H x = ∫⁻ θ in Ioc 0 (2 * π), F θ * (H (x - om θ) + H (x + om θ)) := by
  have hg : Periodic (fun θ => F θ * H (x - om θ)) (2 * π) := by
    intro θ; simp only [hFp θ, om_two_pi]
  have hgm : Measurable fun θ => F θ * H (x - om θ) :=
    hFm.mul (hHm.comp (measurable_const.sub om_meas))
  have hF' : ∀ θ, F (π + θ) = F θ := fun θ => by rw [add_comm]; exact hFa θ
  have h := S2V.lint_shift hg hgm π
  simp only [om_add_pi, sub_neg_eq_add, hF'] at h
  unfold conv
  rw [two_mul]
  nth_rewrite 2 [← h]
  rw [← lintegral_add_left hgm]
  exact lintegral_congr (fun θ => by ring)

/-- Claim: 4‖h*fσ‖₂² ≤ 3‖f‖₁²‖h‖₂² -/
theorem conv_bound {F : ℝ → ℝ≥0∞} (hFm : Measurable F) (hFp : Periodic F (2 * π))
    (hFa : ∀ θ, F (θ + π) = F θ) (hA : ∫⁻ θ in Ioc 0 (2 * π), F θ ≠ ∞)
    (hHm : Measurable H) (hH : ∀ y, 4 ≤ nsq y → H y = 0) :
    4 * ∫⁻ x, conv F H x ^ 2 ≤ 3 * (∫⁻ θ in Ioc 0 (2 * π), F θ) ^ 2 * ∫⁻ y, H y ^ 2 := by
  have hG : ∀ x : ℝ × ℝ, Measurable fun θ => H (x - om θ) + H (x + om θ) := fun x =>
    (hHm.comp (measurable_const.sub om_meas)).add (hHm.comp (measurable_const.add om_meas))
  have step : ∀ x, 4 * conv F H x ^ 2 ≤ (∫⁻ θ in Ioc 0 (2 * π), F θ)
      * ∫⁻ θ in Ioc 0 (2 * π), F θ * (H (x - om θ) + H (x + om θ)) ^ 2 := by
    intro x
    have h := cs_w (volume.restrict (Ioc (0 : ℝ) (2 * π))) hFm (hG x)
    rw [← conv_sym hFm hFp hFa hHm x] at h
    calc 4 * conv F H x ^ 2 = (2 * conv F H x) ^ 2 := by ring
      _ ≤ _ := h
  have hmeasU : Measurable fun p : (ℝ × ℝ) × ℝ =>
      F p.2 * (H (p.1 - om p.2) + H (p.1 + om p.2)) ^ 2 :=
    (hFm.comp measurable_snd).mul (((hHm.comp (measurable_fst.sub (om_meas.comp measurable_snd))).add
      (hHm.comp (measurable_fst.add (om_meas.comp measurable_snd)))).pow_const 2)
  calc 4 * ∫⁻ x, conv F H x ^ 2 = ∫⁻ x, 4 * conv F H x ^ 2 :=
        (lintegral_const_mul' 4 _ (by norm_num)).symm
    _ ≤ ∫⁻ x, (∫⁻ θ in Ioc 0 (2 * π), F θ)
          * ∫⁻ θ in Ioc 0 (2 * π), F θ * (H (x - om θ) + H (x + om θ)) ^ 2 :=
        lintegral_mono step
    _ = (∫⁻ θ in Ioc 0 (2 * π), F θ)
          * ∫⁻ x, ∫⁻ θ in Ioc 0 (2 * π), F θ * (H (x - om θ) + H (x + om θ)) ^ 2 :=
        lintegral_const_mul' _ _ hA
    _ = (∫⁻ θ in Ioc 0 (2 * π), F θ)
          * ∫⁻ θ in Ioc 0 (2 * π), ∫⁻ x, F θ * (H (x - om θ) + H (x + om θ)) ^ 2 := by
        rw [lintegral_lintegral_swap
          (f := fun (x : ℝ × ℝ) (θ : ℝ) => F θ * (H (x - om θ) + H (x + om θ)) ^ 2)
          hmeasU.aemeasurable]
    _ = (∫⁻ θ in Ioc 0 (2 * π), F θ)
          * ∫⁻ θ in Ioc 0 (2 * π), F θ * ∫⁻ x, (H (x - om θ) + H (x + om θ)) ^ 2 := by
        congr 1
        refine lintegral_congr (fun θ => ?_)
        exact lintegral_const_mul _ (((hHm.comp (measurable_id.sub_const _)).add
          (hHm.comp (measurable_id.add_const _))).pow_const 2)
    _ ≤ (∫⁻ θ in Ioc 0 (2 * π), F θ)
          * ∫⁻ θ in Ioc 0 (2 * π), F θ * (3 * ∫⁻ y, H y ^ 2) :=
        mul_le_mul_of_nonneg_left (lintegral_mono fun θ =>
          mul_le_mul_of_nonneg_left (pair_bound hHm hH θ) (by positivity)) (by positivity)
    _ = _ := by rw [lintegral_mul_const _ hFm]; ring

end

end SteinTomas.S5B

#print axioms SteinTomas.S5B.conv_bound
#print axioms SteinTomas.S5B.cs2
