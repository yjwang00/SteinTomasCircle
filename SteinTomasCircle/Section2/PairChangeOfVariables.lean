import Mathlib

/-!
# Section 2 (§2.3): the pair change of variables (eq:pair-change-of-variables)

Angular variables ω = e^{is}, η = e^{it}, |det(ω,η)| = |sin(t−s)|. For measurable Ψ : ℝ² → [0,∞]:

  ∫₀^{2π}∫₀^{2π} |sin(t−s)| Ψ(ω+η) ds dt = 2 ∫_{|y|<2} Ψ(y) dy.

Proof: inner translation t = s + w, exchange of the order of integration, outer translation s = φ − w/2, using
ω + η = 2cos(w/2)·e^{i(s+w/2)}; then split w ∈ (0,π), (π,2π) and substitute ρ = 2|cos(w/2)|;
both sides become 2∫₀² ρ A(ρ) dρ, A(ρ) = ∫₀^{2π} Ψ(ρcos φ, ρ sin φ) dφ; the right-hand side by polar coordinates.
No external input.
-/

namespace SteinTomas.S2V

open Real MeasureTheory Set Function
open scoped ENNReal

noncomputable section

/-- The lintegral of a periodic function over an interval of length 2π does not depend on the starting point -/
lemma lint_periodic {g : ℝ → ℝ≥0∞} (hg : Periodic g (2 * π)) (t : ℝ) :
    ∫⁻ a in Ioc t (t + 2 * π), g a = ∫⁻ a in Ioc 0 (2 * π), g a := by
  haveI : Fact (0 < 2 * π) := ⟨by positivity⟩
  have h1 : ∫⁻ a in Ioc t (t + 2 * π), g a = ∫⁻ b : AddCircle (2 * π), hg.lift b :=
    AddCircle.lintegral_preimage (2 * π) t hg.lift
  have h2 : ∫⁻ a in Ioc 0 (0 + 2 * π), g a = ∫⁻ b : AddCircle (2 * π), hg.lift b :=
    AddCircle.lintegral_preimage (2 * π) 0 hg.lift
  rw [zero_add] at h2
  rw [h1, h2]

/-- Translation invariance: ∫₀^{2π} g(a + x) dx = ∫₀^{2π} g -/
lemma lint_shift {g : ℝ → ℝ≥0∞} (hg : Periodic g (2 * π)) (hgm : Measurable g) (a : ℝ) :
    ∫⁻ x in Ioc 0 (2 * π), g (a + x) = ∫⁻ x in Ioc 0 (2 * π), g x := by
  have hmp := measurePreserving_add_left (volume : Measure ℝ) a
  have h := hmp.setLIntegral_comp_preimage (s := Ioc a (a + 2 * π)) measurableSet_Ioc hgm
  have hpre : (fun x => a + x) ⁻¹' Ioc a (a + 2 * π) = Ioc 0 (2 * π) := by
    ext x
    simp only [mem_preimage, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  rw [hpre] at h
  rw [h, lint_periodic hg a]

variable {Ψ : ℝ × ℝ → ℝ≥0∞}

/-- Circular average A(ρ) = ∫₀^{2π} Ψ(ρcos φ, ρ sin φ) dφ -/
def A (Ψ : ℝ × ℝ → ℝ≥0∞) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ φ in Ioc 0 (2 * π), Ψ (R * Real.cos φ, R * Real.sin φ)

lemma A_per (R : ℝ) : Periodic (fun φ => Ψ (R * Real.cos φ, R * Real.sin φ)) (2 * π) := by
  intro φ; simp only [Real.cos_add_two_pi, Real.sin_add_two_pi]

lemma A_meas (hΨ : Measurable Ψ) (R : ℝ) :
    Measurable (fun φ => Ψ (R * Real.cos φ, R * Real.sin φ)) :=
  hΨ.comp (Continuous.measurable (by fun_prop))

/-- A(−ρ) = A(ρ) -/
lemma A_even (hΨ : Measurable Ψ) (R : ℝ) : A Ψ (-R) = A Ψ R := by
  unfold A
  rw [← lint_shift (A_per R) (A_meas hΨ R) π]
  refine lintegral_congr (fun φ => ?_)
  rw [add_comm π φ, Real.cos_add_pi, Real.sin_add_pi]
  simp only [neg_mul, mul_neg]

/-- The left-hand side becomes ∫₀^{2π} |sin w| A(2cos(w/2)) dw -/
lemma lhs_eq (hΨ : Measurable Ψ) :
    ∫⁻ s in Ioc 0 (2 * π), ∫⁻ t in Ioc 0 (2 * π),
        ENNReal.ofReal |Real.sin (t - s)| * Ψ (Real.cos s + Real.cos t, Real.sin s + Real.sin t)
      = ∫⁻ w in Ioc 0 (2 * π), ENNReal.ofReal |Real.sin w| * A Ψ (2 * Real.cos (w / 2)) := by
  have step1 : ∀ s, ∫⁻ t in Ioc 0 (2 * π),
        ENNReal.ofReal |Real.sin (t - s)| * Ψ (Real.cos s + Real.cos t, Real.sin s + Real.sin t)
      = ∫⁻ w in Ioc 0 (2 * π), ENNReal.ofReal |Real.sin w|
        * Ψ (Real.cos s + Real.cos (s + w), Real.sin s + Real.sin (s + w)) := by
    intro s
    have hper : Periodic (fun t => ENNReal.ofReal |Real.sin (t - s)|
        * Ψ (Real.cos s + Real.cos t, Real.sin s + Real.sin t)) (2 * π) := by
      intro t
      simp only
      rw [show t + 2 * π - s = (t - s) + 2 * π by ring, Real.sin_add_two_pi, Real.cos_add_two_pi,
        Real.sin_add_two_pi]
    have hm : Measurable (fun t => ENNReal.ofReal |Real.sin (t - s)|
        * Ψ (Real.cos s + Real.cos t, Real.sin s + Real.sin t)) :=
      (ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))).mul
        (hΨ.comp (Continuous.measurable (by fun_prop)))
    rw [← lint_shift hper hm s]
    refine lintegral_congr (fun w => ?_)
    simp only [add_sub_cancel_left]
  have hmeas : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal |Real.sin p.2|
      * Ψ (Real.cos p.1 + Real.cos (p.1 + p.2), Real.sin p.1 + Real.sin (p.1 + p.2))) :=
    (ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))).mul
      (hΨ.comp (Continuous.measurable (by fun_prop)))
  have step3 : ∀ w, ∫⁻ s in Ioc 0 (2 * π), ENNReal.ofReal |Real.sin w|
        * Ψ (Real.cos s + Real.cos (s + w), Real.sin s + Real.sin (s + w))
      = ENNReal.ofReal |Real.sin w| * A Ψ (2 * Real.cos (w / 2)) := by
    intro w
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    unfold A
    rw [← lint_shift (A_per (Ψ := Ψ) (2 * Real.cos (w / 2))) (A_meas hΨ _) (w / 2)]
    refine lintegral_congr (fun s => ?_)
    have h1 : Real.cos s + Real.cos (s + w) = 2 * Real.cos (w / 2) * Real.cos (w / 2 + s) := by
      have e1 : Real.cos s = Real.cos (w / 2 + s) * Real.cos (w / 2)
          + Real.sin (w / 2 + s) * Real.sin (w / 2) := by
        rw [← Real.cos_sub]; congr 1; ring
      have e2 : Real.cos (s + w) = Real.cos (w / 2 + s) * Real.cos (w / 2)
          - Real.sin (w / 2 + s) * Real.sin (w / 2) := by
        rw [← Real.cos_add]; congr 1; ring
      linear_combination e1 + e2
    have h2 : Real.sin s + Real.sin (s + w) = 2 * Real.cos (w / 2) * Real.sin (w / 2 + s) := by
      have e1 : Real.sin s = Real.sin (w / 2 + s) * Real.cos (w / 2)
          - Real.cos (w / 2 + s) * Real.sin (w / 2) := by
        rw [← Real.sin_sub]; congr 1; ring
      have e2 : Real.sin (s + w) = Real.sin (w / 2 + s) * Real.cos (w / 2)
          + Real.cos (w / 2 + s) * Real.sin (w / 2) := by
        rw [← Real.sin_add]; congr 1; ring
      linear_combination e1 + e2
    rw [h1, h2]
  calc _ = ∫⁻ s in Ioc 0 (2 * π), ∫⁻ w in Ioc 0 (2 * π), ENNReal.ofReal |Real.sin w|
        * Ψ (Real.cos s + Real.cos (s + w), Real.sin s + Real.sin (s + w)) :=
        lintegral_congr (fun s => step1 s)
    _ = ∫⁻ w in Ioc 0 (2 * π), ∫⁻ s in Ioc 0 (2 * π), ENNReal.ofReal |Real.sin w|
        * Ψ (Real.cos s + Real.cos (s + w), Real.sin s + Real.sin (s + w)) :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = _ := lintegral_congr (fun w => step3 w)

/-- w ∈ (0,π): ρ = 2cos(w/2) -/
lemma piece1 :
    ∫⁻ w in Ioo 0 π, ENNReal.ofReal |Real.sin w| * A Ψ (2 * Real.cos (w / 2))
      = ∫⁻ ρ in Ioo 0 2, ENNReal.ofReal ρ * A Ψ ρ := by
  have hd : ∀ w, HasDerivAt (fun w => 2 * Real.cos (w / 2)) (-Real.sin (w / 2)) w := by
    intro w
    have := ((hasDerivAt_id' w).div_const 2).cos.const_mul 2
    convert this using 1; ring
  have hinj : InjOn (fun w => 2 * Real.cos (w / 2)) (Ioo 0 π) := by
    intro a ha b hb hab
    simp only at hab
    have := Real.injOn_cos (show a / 2 ∈ Icc 0 π from ⟨by linarith [ha.1], by linarith [ha.2, pi_pos]⟩)
      (show b / 2 ∈ Icc 0 π from ⟨by linarith [hb.1], by linarith [hb.2, pi_pos]⟩) (by linarith)
    linarith
  have himg : (fun w => 2 * Real.cos (w / 2)) '' Ioo 0 π = Ioo 0 2 := by
    ext ρ
    simp only [mem_image, mem_Ioo]
    constructor
    · rintro ⟨w, ⟨h0, h1⟩, rfl⟩
      have hc : 0 < Real.cos (w / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
      have hc1 : Real.cos (w / 2) < 1 := by
        have := Real.strictAntiOn_cos (show (0 : ℝ) ∈ Icc 0 π from ⟨le_refl _, pi_pos.le⟩)
          (show w / 2 ∈ Icc 0 π from ⟨by linarith, by linarith⟩) (by linarith)
        rwa [Real.cos_zero] at this
      constructor <;> linarith
    · rintro ⟨h0, h2⟩
      refine ⟨2 * Real.arccos (ρ / 2), ⟨?_, ?_⟩, ?_⟩
      · have := Real.arccos_pos.2 (by linarith : ρ / 2 < 1); linarith
      · have := Real.arccos_lt_pi_div_two.2 (by linarith : 0 < ρ / 2); linarith
      · rw [show 2 * Real.arccos (ρ / 2) / 2 = Real.arccos (ρ / 2) by ring,
          Real.cos_arccos (by linarith) (by linarith)]
        ring
  have hcov := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioo 0 π)
    (f := fun w => 2 * Real.cos (w / 2)) (f' := fun w => -Real.sin (w / 2)) measurableSet_Ioo
    (fun w _ => (hd w).hasDerivWithinAt) hinj (fun ρ => ENNReal.ofReal ρ * A Ψ ρ)
  rw [himg] at hcov
  rw [hcov]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun w hw => ?_)
  have hc : 0 < Real.cos (w / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, hw.1], by linarith [hw.2]⟩
  have hs : Real.sin w = 2 * Real.sin (w / 2) * Real.cos (w / 2) := by
    have := Real.sin_two_mul (w / 2)
    rw [show 2 * (w / 2) = w by ring] at this
    exact this
  have habs : |Real.sin w| = |-Real.sin (w / 2)| * (2 * Real.cos (w / 2)) := by
    rw [hs, abs_neg, abs_mul, abs_mul, abs_of_pos hc, abs_two]; ring
  rw [habs, ENNReal.ofReal_mul (abs_nonneg _), mul_assoc]

/-- w ∈ (π,2π): ρ = −2cos(w/2) -/
lemma piece2 (hΨ : Measurable Ψ) :
    ∫⁻ w in Ioo π (2 * π), ENNReal.ofReal |Real.sin w| * A Ψ (2 * Real.cos (w / 2))
      = ∫⁻ ρ in Ioo 0 2, ENNReal.ofReal ρ * A Ψ ρ := by
  have hd : ∀ w, HasDerivAt (fun w => -2 * Real.cos (w / 2)) (Real.sin (w / 2)) w := by
    intro w
    have := ((hasDerivAt_id' w).div_const 2).cos.const_mul (-2)
    convert this using 1; ring
  have hinj : InjOn (fun w => -2 * Real.cos (w / 2)) (Ioo π (2 * π)) := by
    intro a ha b hb hab
    simp only at hab
    have := Real.injOn_cos (show a / 2 ∈ Icc 0 π from ⟨by linarith [ha.1, pi_pos], by linarith [ha.2]⟩)
      (show b / 2 ∈ Icc 0 π from ⟨by linarith [hb.1, pi_pos], by linarith [hb.2]⟩) (by linarith)
    linarith
  have himg : (fun w => -2 * Real.cos (w / 2)) '' Ioo π (2 * π) = Ioo 0 2 := by
    ext ρ
    simp only [mem_image, mem_Ioo]
    constructor
    · rintro ⟨w, ⟨h0, h1⟩, rfl⟩
      have hc : Real.cos (w / 2) < 0 :=
        Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [pi_pos])
      have hc1 : -1 < Real.cos (w / 2) := by
        have := Real.strictAntiOn_cos (show w / 2 ∈ Icc 0 π from ⟨by linarith [pi_pos], by linarith⟩)
          (show π ∈ Icc 0 π from ⟨pi_pos.le, le_refl _⟩) (by linarith)
        rwa [Real.cos_pi] at this
      constructor <;> linarith
    · rintro ⟨h0, h2⟩
      refine ⟨2 * (π - Real.arccos (ρ / 2)), ⟨?_, ?_⟩, ?_⟩
      · have := Real.arccos_lt_pi_div_two.2 (by linarith : 0 < ρ / 2); linarith
      · have := Real.arccos_pos.2 (by linarith : ρ / 2 < 1); linarith
      · rw [show 2 * (π - Real.arccos (ρ / 2)) / 2 = π - Real.arccos (ρ / 2) by ring,
          Real.cos_pi_sub, Real.cos_arccos (by linarith) (by linarith)]
        ring
  have hcov := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioo π (2 * π))
    (f := fun w => -2 * Real.cos (w / 2)) (f' := fun w => Real.sin (w / 2)) measurableSet_Ioo
    (fun w _ => (hd w).hasDerivWithinAt) hinj (fun ρ => ENNReal.ofReal ρ * A Ψ ρ)
  rw [himg] at hcov
  rw [hcov]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun w hw => ?_)
  have hc : Real.cos (w / 2) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith [hw.1]) (by linarith [hw.2, pi_pos])
  have hs : Real.sin w = 2 * Real.sin (w / 2) * Real.cos (w / 2) := by
    have := Real.sin_two_mul (w / 2)
    rw [show 2 * (w / 2) = w by ring] at this
    exact this
  have habs : |Real.sin w| = |Real.sin (w / 2)| * (-2 * Real.cos (w / 2)) := by
    rw [hs, abs_mul, abs_mul, abs_of_neg hc, abs_two]; ring
  rw [show 2 * Real.cos (w / 2) = -(-2 * Real.cos (w / 2)) by ring, A_even hΨ, habs,
    ENNReal.ofReal_mul (abs_nonneg _), mul_assoc]

/-- Right-hand side: ∫_{|y|<2} Ψ = ∫₀² ρ A(ρ) dρ (polar coordinates) -/
lemma rhs_eq (hΨ : Measurable Ψ) :
    ∫⁻ y in {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 4}, Ψ y
      = ∫⁻ ρ in Ioo 0 2, ENNReal.ofReal ρ * A Ψ ρ := by
  have hD : MeasurableSet {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 4} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hps : Measurable (fun p : ℝ × ℝ => polarCoord.symm p) := by
    have e : (fun p : ℝ × ℝ => polarCoord.symm p)
        = fun p => (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := funext polarCoord_symm_apply
    rw [e]; exact Continuous.measurable (by fun_prop)
  rw [← lintegral_indicator hD, ← lintegral_comp_polarCoord_symm, polarCoord_target,
    Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ ?_]
  swap
  · exact ((ENNReal.measurable_ofReal.comp measurable_fst).smul
        ((hΨ.indicator hD).comp hps)).aemeasurable
  refine (setLIntegral_congr_fun (g := fun ρ => (Iio (2 : ℝ)).indicator
      (fun ρ => ENNReal.ofReal ρ * A Ψ ρ) ρ) measurableSet_Ioi (fun ρ hρ => ?_)).trans ?_
  · have hρ0 : (0 : ℝ) < ρ := hρ
    simp only [polarCoord_symm_apply, smul_eq_mul]
    have hnorm : ∀ φ : ℝ, (ρ * Real.cos φ) ^ 2 + (ρ * Real.sin φ) ^ 2 = ρ ^ 2 := by
      intro φ; linear_combination ρ ^ 2 * Real.sin_sq_add_cos_sq φ
    by_cases h2 : ρ < 2
    · rw [indicator_of_mem (show ρ ∈ Iio (2 : ℝ) from h2)]
      have e : ∀ φ : ℝ, {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 4}.indicator Ψ
          (ρ * Real.cos φ, ρ * Real.sin φ) = Ψ (ρ * Real.cos φ, ρ * Real.sin φ) := by
        intro φ
        apply indicator_of_mem
        simp only [mem_ofPred_eq]
        rw [hnorm φ]; nlinarith
      simp_rw [e]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      unfold A
      rw [setLIntegral_congr (Ioo_ae_eq_Ioc (μ := volume) (a := -π) (b := π))]
      have := lint_periodic (A_per (Ψ := Ψ) ρ) (-π)
      rw [show -π + 2 * π = π by ring] at this
      exact this
    · rw [indicator_of_notMem (show ρ ∉ Iio (2 : ℝ) from h2)]
      have e : ∀ φ : ℝ, {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 4}.indicator Ψ
          (ρ * Real.cos φ, ρ * Real.sin φ) = 0 := by
        intro φ
        apply indicator_of_notMem
        simp only [mem_ofPred_eq, not_lt]
        rw [hnorm φ]; nlinarith
      simp_rw [e, mul_zero, lintegral_zero]
  · rw [setLIntegral_indicator measurableSet_Iio, inter_comm, Ioi_inter_Iio]

/-- eq:pair-change-of-variables -/
theorem pair_cov (hΨ : Measurable Ψ) :
    ∫⁻ s in Ioc 0 (2 * π), ∫⁻ t in Ioc 0 (2 * π),
        ENNReal.ofReal |Real.sin (t - s)| * Ψ (Real.cos s + Real.cos t, Real.sin s + Real.sin t)
      = 2 * ∫⁻ y in {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 4}, Ψ y := by
  rw [lhs_eq hΨ, rhs_eq hΨ,
    ← Ioc_union_Ioc_eq_Ioc pi_pos.le (by linarith [pi_pos] : π ≤ 2 * π),
    lintegral_union measurableSet_Ioc (by rw [Set.disjoint_left]; intro x h1 h2; linarith [h1.2, h2.1]),
    ← setLIntegral_congr (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := π)),
    ← setLIntegral_congr (Ioo_ae_eq_Ioc (μ := volume) (a := π) (b := 2 * π)),
    piece1, piece2 hΨ, ← two_mul]

end

end SteinTomas.S2V

#print axioms SteinTomas.S2V.pair_cov
