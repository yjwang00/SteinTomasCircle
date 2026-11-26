import Mathlib
import SteinTomasCircle.Section2.QFourier
import SteinTomasCircle.Section2.PairChangeOfVariables

/-!
# Section 2 (§2.3): h and eq:pair-density

h(y) = (|y|√(4−|y|²)/2)(fσ*fσ)(y) satisfies h(ω+η) = 2f(ω)f(η). Here it is written directly in polar coordinates:
for 0 < |y| < 2, y = |y|e^{iφ}, α = arccos(|y|/2), h(y) = 2f(φ−α)f(φ+α) (f a 2π-periodic angular function);
h = 0 for |y| ≥ 2.

* `h_pair`: h(e^{is}+e^{it}) = 2f(s)f(t) when sin(t−s) ≠ 0
* `h_L2`: ∫|h|² = 2∫∫|sin(t−s)|f(s)²f(t)² ([0,∞]-valued, from eq:pair-change-of-variables)
* `h_L2_real`: for f ∈ L², h ∈ L² and ‖h‖₂² = 2Q(f²) (eq:pair-density)
-/

namespace SteinTomas.S2H

open Real MeasureTheory Set Function
open scoped ENNReal

noncomputable section

/-- h(y) (polar form) -/
def hfun (f : ℝ → ℝ) (y : ℝ × ℝ) : ℝ :=
  if y.1 ^ 2 + y.2 ^ 2 < 4 then
    2 * f (Complex.arg (((y.1 : ℝ) : ℂ) + ((y.2 : ℝ) : ℂ) * Complex.I)
        - Real.arccos (Real.sqrt (y.1 ^ 2 + y.2 ^ 2) / 2))
      * f (Complex.arg (((y.1 : ℝ) : ℂ) + ((y.2 : ℝ) : ℂ) * Complex.I)
        + Real.arccos (Real.sqrt (y.1 ^ 2 + y.2 ^ 2) / 2))
  else 0

variable {f : ℝ → ℝ}

lemma per_int (hper : Periodic f (2 * π)) (x : ℝ) (k : ℤ) : f (x + k * (2 * π)) = f x :=
  (hper.int_mul k) x

/-- If φ ≡ ψ (mod 2π) and cos α = cos δ, then f(φ−α)f(φ+α) = f(ψ−δ)f(ψ+δ) -/
lemma swap_eq (hper : Periodic f (2 * π)) {φ ψ α δ : ℝ} (n : ℤ) (hφ : φ = ψ - n * (2 * π))
    (hα : Real.cos α = Real.cos δ) : f (φ - α) * f (φ + α) = f (ψ - δ) * f (ψ + δ) := by
  obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.1 hα
  · have e1 : φ - α = (ψ - δ) + ((k - n : ℤ) : ℝ) * (2 * π) := by rw [hφ, hk]; push_cast; ring
    have e2 : φ + α = (ψ + δ) + ((-k - n : ℤ) : ℝ) * (2 * π) := by rw [hφ, hk]; push_cast; ring
    rw [e1, e2, per_int hper, per_int hper]
  · have e1 : φ - α = (ψ + δ) + ((-k - n : ℤ) : ℝ) * (2 * π) := by rw [hφ, hk]; push_cast; ring
    have e2 : φ + α = (ψ - δ) + ((k - n : ℤ) : ℝ) * (2 * π) := by rw [hφ, hk]; push_cast; ring
    rw [e1, e2, per_int hper, per_int hper, mul_comm]

/-- arg(r e^{iψ}) ≡ ψ (mod 2π) -/
lemma arg_polar {r ψ : ℝ} (hr : 0 < r) :
    ∃ n : ℤ, Complex.arg (((r * Real.cos ψ : ℝ) : ℂ) + ((r * Real.sin ψ : ℝ) : ℂ) * Complex.I)
      = ψ - n * (2 * π) := by
  have hz : ((r * Real.cos ψ : ℝ) : ℂ) + ((r * Real.sin ψ : ℝ) : ℂ) * Complex.I
      = (r : ℂ) * Complex.exp (ψ * Complex.I) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
      ring
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
      ring
  refine ⟨toIocDiv Real.two_pi_pos (-π) ψ, ?_⟩
  rw [hz, Complex.arg_real_mul _ hr, Complex.arg_exp_mul_I, ← self_sub_toIocDiv_zsmul,
    zsmul_eq_mul]

/-- h(e^{is}+e^{it}) = 2f(s)f(t) (sin(t−s) ≠ 0) -/
theorem h_pair (hper : Periodic f (2 * π)) (s t : ℝ) (hst : Real.sin (t - s) ≠ 0) :
    hfun f (Real.cos s + Real.cos t, Real.sin s + Real.sin t) = 2 * f s * f t := by
  have hsd : Real.sin (t - s) = 2 * Real.sin ((t - s) / 2) * Real.cos ((t - s) / 2) := by
    have := Real.sin_two_mul ((t - s) / 2)
    rw [show 2 * ((t - s) / 2) = t - s by ring] at this
    exact this
  have hc : Real.cos ((t - s) / 2) ≠ 0 := by
    intro h; apply hst; rw [hsd, h, mul_zero]
  have hs : Real.sin ((t - s) / 2) ≠ 0 := by
    intro h; apply hst; rw [hsd, h]; ring
  have hy1 : Real.cos s + Real.cos t
      = 2 * Real.cos ((t - s) / 2) * Real.cos ((s + t) / 2) := by
    have e1 : Real.cos s = Real.cos ((s + t) / 2) * Real.cos ((t - s) / 2)
        + Real.sin ((s + t) / 2) * Real.sin ((t - s) / 2) := by
      rw [← Real.cos_sub]; congr 1; ring
    have e2 : Real.cos t = Real.cos ((s + t) / 2) * Real.cos ((t - s) / 2)
        - Real.sin ((s + t) / 2) * Real.sin ((t - s) / 2) := by
      rw [← Real.cos_add]; congr 1; ring
    linear_combination e1 + e2
  have hy2 : Real.sin s + Real.sin t
      = 2 * Real.cos ((t - s) / 2) * Real.sin ((s + t) / 2) := by
    have e1 : Real.sin s = Real.sin ((s + t) / 2) * Real.cos ((t - s) / 2)
        - Real.cos ((s + t) / 2) * Real.sin ((t - s) / 2) := by
      rw [← Real.sin_sub]; congr 1; ring
    have e2 : Real.sin t = Real.sin ((s + t) / 2) * Real.cos ((t - s) / 2)
        + Real.cos ((s + t) / 2) * Real.sin ((t - s) / 2) := by
      rw [← Real.sin_add]; congr 1; ring
    linear_combination e1 + e2
  have hsq : (Real.cos s + Real.cos t) ^ 2 + (Real.sin s + Real.sin t) ^ 2
      = (2 * Real.cos ((t - s) / 2)) ^ 2 := by
    rw [hy1, hy2]
    linear_combination (2 * Real.cos ((t - s) / 2)) ^ 2 * Real.sin_sq_add_cos_sq ((s + t) / 2)
  have hlt : (2 * Real.cos ((t - s) / 2)) ^ 2 < 4 := by
    have h1 := Real.sin_sq_add_cos_sq ((t - s) / 2)
    have h2 : 0 < Real.sin ((t - s) / 2) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hs))
    nlinarith
  unfold hfun
  dsimp only
  rw [hsq, if_pos hlt, Real.sqrt_sq_eq_abs, abs_mul, abs_two,
    show 2 * |Real.cos ((t - s) / 2)| / 2 = |Real.cos ((t - s) / 2)| by ring]
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · rw [abs_of_neg hneg]
    have hz1 : Real.cos s + Real.cos t
        = (-2 * Real.cos ((t - s) / 2)) * Real.cos ((s + t) / 2 + π) := by
      rw [Real.cos_add_pi, hy1]; ring
    have hz2 : Real.sin s + Real.sin t
        = (-2 * Real.cos ((t - s) / 2)) * Real.sin ((s + t) / 2 + π) := by
      rw [Real.sin_add_pi, hy2]; ring
    obtain ⟨n, hn⟩ := arg_polar (r := -2 * Real.cos ((t - s) / 2)) (ψ := (s + t) / 2 + π)
      (by linarith)
    have hcos : Real.cos (Real.arccos (-Real.cos ((t - s) / 2)))
        = Real.cos ((t - s) / 2 + π) := by
      rw [Real.cos_arccos (by linarith [Real.cos_le_one ((t - s) / 2)])
        (by linarith [Real.neg_one_le_cos ((t - s) / 2)]), Real.cos_add_pi]
    rw [hz1, hz2, hn, mul_assoc, swap_eq hper n rfl hcos,
      show (s + t) / 2 + π - ((t - s) / 2 + π) = s by ring,
      show (s + t) / 2 + π + ((t - s) / 2 + π) = t + ((1 : ℤ) : ℝ) * (2 * π) by push_cast; ring,
      per_int hper]
    ring
  · rw [abs_of_pos hpos]
    obtain ⟨n, hn⟩ := arg_polar (r := 2 * Real.cos ((t - s) / 2)) (ψ := (s + t) / 2)
      (by linarith)
    have hcos : Real.cos (Real.arccos (Real.cos ((t - s) / 2))) = Real.cos ((t - s) / 2) :=
      Real.cos_arccos (Real.neg_one_le_cos _) (Real.cos_le_one _)
    rw [hy1, hy2, hn, mul_assoc, swap_eq hper n rfl hcos,
      show (s + t) / 2 - (t - s) / 2 = s by ring, show (s + t) / 2 + (t - s) / 2 = t by ring]
    ring

lemma hfun_meas (hfm : Measurable f) : Measurable (hfun f) := by
  have hφ : Measurable fun y : ℝ × ℝ =>
      Complex.arg (((y.1 : ℝ) : ℂ) + ((y.2 : ℝ) : ℂ) * Complex.I) :=
    Complex.measurable_arg.comp (Continuous.measurable (by fun_prop))
  have hα : Measurable fun y : ℝ × ℝ => Real.arccos (Real.sqrt (y.1 ^ 2 + y.2 ^ 2) / 2) :=
    (Real.continuous_arccos.comp
      ((Real.continuous_sqrt.comp (by fun_prop : Continuous fun y : ℝ × ℝ => y.1 ^ 2 + y.2 ^ 2)).div_const
        2)).measurable
  unfold hfun
  refine Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) ?_ measurable_const
  exact (measurable_const.mul (hfm.comp (hφ.sub hα))).mul (hfm.comp (hφ.add hα))

/-- ∫|h|² = 2∫∫|sin(t−s)|f(s)²f(t)² ([0,∞]-valued) -/
theorem h_L2 (hfm : Measurable f) (hper : Periodic f (2 * π)) :
    ∫⁻ y, ENNReal.ofReal (hfun f y ^ 2)
      = 2 * ∫⁻ s in Ioc 0 (2 * π), ∫⁻ t in Ioc 0 (2 * π),
          ENNReal.ofReal (|Real.sin (t - s)| * f s ^ 2 * f t ^ 2) := by
  have hm : Measurable fun y => ENNReal.ofReal (hfun f y ^ 2) :=
    ENNReal.measurable_ofReal.comp ((hfun_meas hfm).pow_const 2)
  have hpc := S2V.pair_cov hm
  have hpt : ∀ s t : ℝ, ENNReal.ofReal |Real.sin (t - s)|
      * ENNReal.ofReal (hfun f (Real.cos s + Real.cos t, Real.sin s + Real.sin t) ^ 2)
      = 4 * ENNReal.ofReal (|Real.sin (t - s)| * f s ^ 2 * f t ^ 2) := by
    intro s t
    by_cases hst : Real.sin (t - s) = 0
    · simp [hst]
    · rw [h_pair hper s t hst, ← ENNReal.ofReal_mul (abs_nonneg _),
        show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring
  simp_rw [hpt] at hpc
  have e1 : ∀ s : ℝ, ∫⁻ t in Ioc 0 (2 * π), 4 * ENNReal.ofReal (|Real.sin (t - s)| * f s ^ 2 * f t ^ 2)
      = 4 * ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (|Real.sin (t - s)| * f s ^ 2 * f t ^ 2) :=
    fun s => lintegral_const_mul' _ _ (by norm_num)
  simp_rw [e1] at hpc
  rw [lintegral_const_mul' _ _ (by norm_num)] at hpc
  have hD : MeasurableSet {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 4} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hDint : ∫⁻ y in {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 4}, ENNReal.ofReal (hfun f y ^ 2)
      = ∫⁻ y, ENNReal.ofReal (hfun f y ^ 2) := by
    rw [← lintegral_indicator hD]
    apply lintegral_congr
    intro y
    by_cases hy : y ∈ {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 4}
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy]
      have : hfun f y = 0 := by unfold hfun; rw [if_neg (show ¬ (y.1 ^ 2 + y.2 ^ 2 < 4) from hy)]
      rw [this]; simp
  rw [hDint] at hpc
  set I := ∫⁻ s in Ioc 0 (2 * π), ∫⁻ t in Ioc 0 (2 * π),
    ENNReal.ofReal (|Real.sin (t - s)| * f s ^ 2 * f t ^ 2)
  set L := ∫⁻ y, ENNReal.ofReal (hfun f y ^ 2)
  have hpc' : 2 * (2 * I) = 2 * L := by
    rw [← mul_assoc, show (2 : ℝ≥0∞) * 2 = 4 by norm_num]; exact hpc
  have h2 : (2 : ℝ≥0∞)⁻¹ * 2 = 1 := ENNReal.inv_mul_cancel two_ne_zero (by norm_num)
  calc L = ((2 : ℝ≥0∞)⁻¹ * 2) * L := by rw [h2, one_mul]
    _ = (2 : ℝ≥0∞)⁻¹ * (2 * L) := by rw [mul_assoc]
    _ = (2 : ℝ≥0∞)⁻¹ * (2 * (2 * I)) := by rw [← hpc']
    _ = 2 * I := by rw [← mul_assoc, h2, one_mul]

/-- For g ∈ L¹, g ≥ 0: ∫∫ |sin(t−s)| g(s)g(t) ([0,∞]-valued) = Q(g) -/
lemma Qa_lint {g : ℝ → ℝ} (hg : Integrable g (volume.restrict (Ioc 0 (2 * π))))
    (hg0 : ∀ x, 0 ≤ g x) :
    ∫⁻ s in Ioc 0 (2 * π), ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (|Real.sin (t - s)| * g s * g t)
      = ENNReal.ofReal (S2C.Qa g) := by
  set μ := volume.restrict (Ioc (0 : ℝ) (2 * π)) with hμ
  set J : ℝ → ℝ := fun s => ∫ t, |Real.sin (t - s)| * g t ∂μ with hJ
  have hsg : ∀ s, Integrable (fun t => |Real.sin (t - s)| * g t) μ := by
    intro s
    exact S2C.bmul hg (φ := fun t => |Real.sin (t - s)|) (by fun_prop) (C := 1)
      (fun x => by rw [Real.norm_eq_abs, abs_abs]; exact abs_sin_le_one _)
  have hJc : Continuous J := by
    apply continuous_of_dominated (bound := fun t => ‖g t‖)
    · intro s; exact (hsg s).aestronglyMeasurable
    · intro s
      filter_upwards with t
      rw [norm_mul, Real.norm_eq_abs (|Real.sin _|), abs_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_sin_le_one _)
    · exact hg.norm
    · filter_upwards with t
      fun_prop
  have hJb : ∀ s, ‖J s‖ ≤ ∫ t, ‖g t‖ ∂μ := by
    intro s
    refine norm_integral_le_of_norm_le hg.norm (Filter.Eventually.of_forall (fun t => ?_))
    rw [norm_mul, Real.norm_eq_abs (|Real.sin _|), abs_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_sin_le_one _)
  have hJg : Integrable (fun s => J s * g s) μ := S2C.bmul hg hJc hJb
  have hJ0 : ∀ s, 0 ≤ J s := fun s =>
    integral_nonneg (fun t => mul_nonneg (abs_nonneg _) (hg0 t))
  have hin : ∀ s, ∫⁻ t, ENNReal.ofReal (|Real.sin (t - s)| * g s * g t) ∂μ
      = ENNReal.ofReal (J s * g s) := by
    intro s
    have hi : Integrable (fun t => |Real.sin (t - s)| * g s * g t) μ := by
      refine ((hsg s).const_mul (g s)).congr (Filter.Eventually.of_forall (fun t => ?_))
      simp only; ring
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun t => by
      have := hg0 s; have := hg0 t; simp only [Pi.zero_apply]; positivity))]
    congr 1
    simp only [hJ]
    rw [← MeasureTheory.integral_mul_const]
    congr 1; funext t; ring
  rw [lintegral_congr hin, ← ofReal_integral_eq_lintegral_ofReal hJg
    (Filter.Eventually.of_forall (fun s => mul_nonneg (hJ0 s) (hg0 s)))]
  congr 1
  unfold S2C.Qa
  refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
  simp only [hJ]
  rw [← MeasureTheory.integral_mul_const]
  congr 1; funext t; ring

/-- eq:pair-density: f ∈ L² ⇒ h ∈ L², ‖h‖₂² = 2Q(f²) -/
theorem h_L2_real (hf : MemLp f 2 (volume.restrict (Ioc 0 (2 * π)))) (hfm : Measurable f)
    (hper : Periodic f (2 * π)) :
    Integrable (fun y => hfun f y ^ 2) ∧
      ∫ y, hfun f y ^ 2 = 2 * S2C.Qa (fun θ => f θ ^ 2) := by
  have hg : Integrable (fun θ => f θ ^ 2) (volume.restrict (Ioc 0 (2 * π))) := hf.integrable_sq
  have hg0 : ∀ x, 0 ≤ (fun θ => f θ ^ 2) x := fun x => sq_nonneg _
  have hL := h_L2 hfm hper
  rw [Qa_lint hg hg0] at hL
  have hQ0 : 0 ≤ S2C.Qa (fun θ => f θ ^ 2) := by
    unfold S2C.Qa
    refine integral_nonneg (fun s => integral_nonneg (fun t => ?_))
    have := sq_nonneg (f s); have := sq_nonneg (f t)
    positivity
  have hfin : ∫⁻ y, ENNReal.ofReal (hfun f y ^ 2)
      = ENNReal.ofReal (2 * S2C.Qa (fun θ => f θ ^ 2)) := by
    rw [hL, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hnn : 0 ≤ᵐ[volume] fun y => hfun f y ^ 2 :=
    Filter.Eventually.of_forall (fun y => sq_nonneg _)
  have hmeas := ((hfun_meas hfm).pow_const 2).aestronglyMeasurable (μ := volume)
  refine ⟨⟨hmeas, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hnn, hfin]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas, hfin, ENNReal.toReal_ofReal (by positivity)]

end

end SteinTomas.S2H

#print axioms SteinTomas.S2H.h_pair
#print axioms SteinTomas.S2H.h_L2_real
