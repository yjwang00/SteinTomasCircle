import Mathlib
import SteinTomasCircle.Section2.PairChangeOfVariables
import SteinTomasCircle.Section2.PairDensity
import SteinTomasCircle.Section2.HFourier

/-!
# h agrees with the definition of the paper (eq:def h by f)

Paper: h(y) = (|y|√(4−|y|²)/2)(fσ*fσ)(y) for 0<|y|<2, and 0 otherwise.
Here we prove (for f ≥ 0) that `kap f y = 2h(y)/(|y|√(4−|y|²))` (for 0<|y|²<4, and 0 otherwise) is exactly the density of fσ*fσ:
  ∫∫ Ψ(ω+η) f(ω)f(η) dσdσ = ∫ Ψ(y) kap(y) dy (for all measurable Ψ ≥ 0).
Hence every density g of fσ*fσ agrees a.e. with kap, and the h of the paper agrees a.e. with `S2H.hfun f`.
-/

namespace SteinTomas.S2HC

open Real MeasureTheory Set Function
open scoped ENNReal

noncomputable section

variable {f : ℝ → ℝ}

/-- Density of fσ*fσ (expressed through h) -/
def kap (f : ℝ → ℝ) (y : ℝ × ℝ) : ℝ :=
  if 0 < y.1 ^ 2 + y.2 ^ 2 ∧ y.1 ^ 2 + y.2 ^ 2 < 4 then
    2 * S2H.hfun f y / (Real.sqrt (y.1 ^ 2 + y.2 ^ 2) * Real.sqrt (4 - (y.1 ^ 2 + y.2 ^ 2)))
  else 0

/-- The h of the paper (defined from a density g of fσ*fσ) -/
def hpaper (g : ℝ × ℝ → ℝ) (y : ℝ × ℝ) : ℝ :=
  if 0 < y.1 ^ 2 + y.2 ^ 2 ∧ y.1 ^ 2 + y.2 ^ 2 < 4 then
    Real.sqrt (y.1 ^ 2 + y.2 ^ 2) * Real.sqrt (4 - (y.1 ^ 2 + y.2 ^ 2)) / 2 * g y
  else 0

lemma kap_meas (hfm : Measurable f) : Measurable (kap f) := by
  unfold kap
  have hs : MeasurableSet ({y : ℝ × ℝ | (0 : ℝ) < y.1 ^ 2 + y.2 ^ 2}
      ∩ {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 4}) :=
    (measurableSet_lt measurable_const (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) measurable_const)
  refine Measurable.ite (p := fun y : ℝ × ℝ => 0 < y.1 ^ 2 + y.2 ^ 2 ∧ y.1 ^ 2 + y.2 ^ 2 < 4)
    hs ?_ measurable_const
  refine (measurable_const.mul (S2H.hfun_meas hfm)).div ?_
  exact Continuous.measurable (by fun_prop)

/-- |ω+η|², 4−|ω+η|² and |sin(t−s)| -/
lemma sg_facts (s t : ℝ) :
    (Real.cos s + Real.cos t) ^ 2 + (Real.sin s + Real.sin t) ^ 2
        = (2 * Real.cos ((t - s) / 2)) ^ 2 ∧
    4 - ((Real.cos s + Real.cos t) ^ 2 + (Real.sin s + Real.sin t) ^ 2)
        = (2 * Real.sin ((t - s) / 2)) ^ 2 ∧
    Real.sqrt ((Real.cos s + Real.cos t) ^ 2 + (Real.sin s + Real.sin t) ^ 2)
      * Real.sqrt (4 - ((Real.cos s + Real.cos t) ^ 2 + (Real.sin s + Real.sin t) ^ 2))
        = 2 * |Real.sin (t - s)| := by
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
  have h1 : (Real.cos s + Real.cos t) ^ 2 + (Real.sin s + Real.sin t) ^ 2
      = (2 * Real.cos ((t - s) / 2)) ^ 2 := by
    rw [hy1, hy2]
    linear_combination (2 * Real.cos ((t - s) / 2)) ^ 2 * Real.sin_sq_add_cos_sq ((s + t) / 2)
  have h2 : 4 - ((Real.cos s + Real.cos t) ^ 2 + (Real.sin s + Real.sin t) ^ 2)
      = (2 * Real.sin ((t - s) / 2)) ^ 2 := by
    rw [h1]; linear_combination (-4) * Real.sin_sq_add_cos_sq ((t - s) / 2)
  refine ⟨h1, h2, ?_⟩
  rw [h2, h1, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, ← abs_mul]
  have hsd : Real.sin (t - s) = 2 * Real.sin ((t - s) / 2) * Real.cos ((t - s) / 2) := by
    have := Real.sin_two_mul ((t - s) / 2)
    rw [show 2 * ((t - s) / 2) = t - s by ring] at this
    exact this
  rw [hsd, show 2 * Real.cos ((t - s) / 2) * (2 * Real.sin ((t - s) / 2))
      = 2 * (2 * Real.sin ((t - s) / 2) * Real.cos ((t - s) / 2)) by ring, abs_mul, abs_two]

/-- For sin(t−s) ≠ 0: kap(ω+η)/2 = f(s)f(t)/|sin(t−s)| -/
lemma kap_sg (hper : Periodic f (2 * π)) (s t : ℝ) (hst : Real.sin (t - s) ≠ 0) :
    kap f (Real.cos s + Real.cos t, Real.sin s + Real.sin t) / 2
      = f s * f t / |Real.sin (t - s)| := by
  obtain ⟨h1, h2, h3⟩ := sg_facts s t
  have hsd : Real.sin (t - s) = 2 * Real.sin ((t - s) / 2) * Real.cos ((t - s) / 2) := by
    have := Real.sin_two_mul ((t - s) / 2)
    rw [show 2 * ((t - s) / 2) = t - s by ring] at this
    exact this
  have hc : Real.cos ((t - s) / 2) ≠ 0 := by intro h; apply hst; rw [hsd, h, mul_zero]
  have hs : Real.sin ((t - s) / 2) ≠ 0 := by intro h; apply hst; rw [hsd, h]; ring
  have hpos : 0 < (Real.cos s + Real.cos t) ^ 2 + (Real.sin s + Real.sin t) ^ 2 := by
    rw [h1]; exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (mul_ne_zero two_ne_zero hc)))
  have hlt : (Real.cos s + Real.cos t) ^ 2 + (Real.sin s + Real.sin t) ^ 2 < 4 := by
    have : 0 < (2 * Real.sin ((t - s) / 2)) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (mul_ne_zero two_ne_zero hs)))
    linarith
  have habs : 0 < |Real.sin (t - s)| := abs_pos.2 hst
  have habs' := habs.ne'
  unfold kap
  dsimp only
  rw [if_pos ⟨hpos, hlt⟩, h3, S2H.h_pair hper s t hst]
  field_simp

/-- {sin(t−s) = 0} is a null set for σ×σ -/
lemma ae_sin_ne : ∀ᵐ p ∂S2HF.ν, Real.sin (p.2 - p.1) ≠ 0 := by
  rw [ae_iff]
  simp only [not_not]
  unfold S2HF.ν
  rw [Measure.measure_prod_null (measurableSet_eq_fun (by fun_prop) measurable_const)]
  refine Filter.Eventually.of_forall (fun s => ?_)
  have hc : (Prod.mk s ⁻¹' {p : ℝ × ℝ | Real.sin (p.2 - p.1) = 0}).Countable := by
    have hsub : Prod.mk s ⁻¹' {p : ℝ × ℝ | Real.sin (p.2 - p.1) = 0}
        ⊆ Set.range (fun n : ℤ => (n : ℝ) * π + s) := by
      intro t ht
      have ht' : Real.sin (t - s) = 0 := ht
      obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 ht'
      exact ⟨n, by simp only; linarith⟩
    exact (Set.countable_range _).mono hsub
  show (volume.restrict (Ioc 0 (2 * π))) (Prod.mk s ⁻¹' {p : ℝ × ℝ | Real.sin (p.2 - p.1) = 0}) = 0
  exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans
    (le_of_eq (hc.measure_zero volume)))

/-- kap is the density of fσ*fσ -/
theorem kap_density (hfm : Measurable f) (hper : Periodic f (2 * π)) (hf0 : ∀ θ, 0 ≤ f θ)
    {Ψ : ℝ × ℝ → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ s in Ioc 0 (2 * π), ∫⁻ t in Ioc 0 (2 * π),
        Ψ (Real.cos s + Real.cos t, Real.sin s + Real.sin t) * ENNReal.ofReal (f s * f t)
      = ∫⁻ y, Ψ y * ENNReal.ofReal (kap f y) := by
  have hΨ' : Measurable fun y => Ψ y * ENNReal.ofReal (kap f y / 2) :=
    hΨ.mul (ENNReal.measurable_ofReal.comp ((kap_meas hfm).div_const 2))
  have key := S2V.pair_cov hΨ'
  -- left-hand side: pass to the product measure and compare pointwise
  have hm1 : AEMeasurable (fun p : ℝ × ℝ => Ψ (Real.cos p.1 + Real.cos p.2, Real.sin p.1 + Real.sin p.2)
      * ENNReal.ofReal (f p.1 * f p.2)) S2HF.ν :=
    ((hΨ.comp (Continuous.measurable (by fun_prop))).mul
      (ENNReal.measurable_ofReal.comp ((hfm.comp measurable_fst).mul (hfm.comp measurable_snd)))).aemeasurable
  have hm2 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal |Real.sin (p.2 - p.1)|
      * (Ψ (Real.cos p.1 + Real.cos p.2, Real.sin p.1 + Real.sin p.2)
        * ENNReal.ofReal (kap f (Real.cos p.1 + Real.cos p.2, Real.sin p.1 + Real.sin p.2) / 2)))
      S2HF.ν :=
    ((ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))).mul
      (hΨ'.comp (Continuous.measurable (by fun_prop)))).aemeasurable
  have hL1 := lintegral_prod _ hm1
  have hL2 := lintegral_prod _ hm2
  unfold S2HF.ν at hL1 hL2
  have hae : (fun p : ℝ × ℝ => Ψ (Real.cos p.1 + Real.cos p.2, Real.sin p.1 + Real.sin p.2)
      * ENNReal.ofReal (f p.1 * f p.2))
      =ᵐ[S2HF.ν] fun p => ENNReal.ofReal |Real.sin (p.2 - p.1)|
        * (Ψ (Real.cos p.1 + Real.cos p.2, Real.sin p.1 + Real.sin p.2)
          * ENNReal.ofReal (kap f (Real.cos p.1 + Real.cos p.2, Real.sin p.1 + Real.sin p.2) / 2)) := by
    filter_upwards [ae_sin_ne] with p hp
    have hne : |Real.sin (p.2 - p.1)| ≠ 0 := abs_ne_zero.2 hp
    rw [kap_sg hper p.1 p.2 hp, mul_left_comm, ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 2
    field_simp
  have hprod := lintegral_congr_ae hae
  unfold S2HF.ν at hprod
  rw [← hL1, hprod, hL2, key]
  -- right-hand side: 2∫_D Ψ·kap/2 = ∫ Ψ·kap
  have hD : MeasurableSet {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 4} :=
    measurableSet_lt (by fun_prop) measurable_const
  rw [← lintegral_indicator hD, ← lintegral_const_mul' 2 _ (by norm_num)]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 4}
  · rw [indicator_of_mem hy]
    have hk : ENNReal.ofReal (kap f y) = 2 * ENNReal.ofReal (kap f y / 2) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring
    rw [hk]; ring
  · rw [indicator_of_notMem hy]
    have : kap f y = 0 := by
      unfold kap
      rw [if_neg (fun h => hy h.2)]
    rw [this]; simp

/-- Uniqueness: every (measurable, nonnegative) density g of fσ*fσ agrees a.e. with kap;
hence the h of the paper (defined from g) agrees a.e. with hfun. -/
theorem hpaper_eq (hfm : Measurable f) (hper : Periodic f (2 * π)) (hf0 : ∀ θ, 0 ≤ f θ)
    {g : ℝ × ℝ → ℝ} (hgm : Measurable g) (hg0 : ∀ y, 0 ≤ g y)
    (hg : ∀ Ψ : ℝ × ℝ → ℝ≥0∞, Measurable Ψ →
      ∫⁻ s in Ioc 0 (2 * π), ∫⁻ t in Ioc 0 (2 * π),
        Ψ (Real.cos s + Real.cos t, Real.sin s + Real.sin t) * ENNReal.ofReal (f s * f t)
      = ∫⁻ y, Ψ y * ENNReal.ofReal (g y)) :
    ∀ᵐ y, hpaper g y = S2H.hfun f y := by
  -- g = kap a.e.
  have hgk : (fun y => ENNReal.ofReal (g y)) =ᵐ[volume] fun y => ENNReal.ofReal (kap f y) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
      (ENNReal.measurable_ofReal.comp hgm) (ENNReal.measurable_ofReal.comp (kap_meas hfm)) ?_
    intro A hA _
    have h1 := hg (A.indicator 1) (measurable_one.indicator hA)
    have h2 := kap_density hfm hper hf0 (Ψ := A.indicator 1) (measurable_one.indicator hA)
    rw [h1] at h2
    have e : ∀ (u : ℝ × ℝ → ℝ≥0∞), ∫⁻ y, A.indicator 1 y * u y = ∫⁻ y in A, u y := by
      intro u
      rw [← lintegral_indicator hA]
      apply lintegral_congr; intro y
      by_cases hy : y ∈ A
      · simp [indicator_of_mem hy]
      · simp [indicator_of_notMem hy]
    rw [e, e] at h2
    exact h2
  have hkap0 : ∀ y, 0 ≤ kap f y := by
    intro y
    unfold kap
    split_ifs
    · have : 0 ≤ S2H.hfun f y := by
        unfold S2H.hfun
        split_ifs
        · have := hf0 (Complex.arg (((y.1 : ℝ) : ℂ) + ((y.2 : ℝ) : ℂ) * Complex.I)
              - Real.arccos (Real.sqrt (y.1 ^ 2 + y.2 ^ 2) / 2))
          have := hf0 (Complex.arg (((y.1 : ℝ) : ℂ) + ((y.2 : ℝ) : ℂ) * Complex.I)
              + Real.arccos (Real.sqrt (y.1 ^ 2 + y.2 ^ 2) / 2))
          positivity
        · exact le_refl _
      positivity
    · exact le_refl _
  -- {0} is a null set
  have h0 : ∀ᵐ y : ℝ × ℝ, y ≠ 0 := by
    rw [ae_iff]; simp only [ne_eq, not_not, setOf_eq_eq_singleton]
    exact measure_singleton 0
  filter_upwards [hgk, h0] with y hy hy0
  have hgy : g y = kap f y := by
    have := congrArg ENNReal.toReal hy
    simpa [ENNReal.toReal_ofReal (hg0 y), ENNReal.toReal_ofReal (hkap0 y)] using this
  unfold hpaper
  split_ifs with hc
  · rw [hgy]
    unfold kap
    rw [if_pos hc]
    have hs1 : 0 < Real.sqrt (y.1 ^ 2 + y.2 ^ 2) := Real.sqrt_pos.2 hc.1
    have hs2 : 0 < Real.sqrt (4 - (y.1 ^ 2 + y.2 ^ 2)) := Real.sqrt_pos.2 (by linarith [hc.2])
    field_simp
  · -- |y|² = 0 or ≥ 4
    have hy2 : ¬ (y.1 ^ 2 + y.2 ^ 2 < 4) := by
      intro h4
      apply hc
      refine ⟨?_, h4⟩
      rcases lt_or_eq_of_le (add_nonneg (sq_nonneg y.1) (sq_nonneg y.2)) with h | h
      · exact h
      · exfalso; apply hy0
        have h1 : y.1 = 0 := by nlinarith [sq_nonneg y.1, sq_nonneg y.2]
        have h2 : y.2 = 0 := by nlinarith [sq_nonneg y.1, sq_nonneg y.2]
        exact Prod.ext h1 h2
    unfold S2H.hfun
    rw [if_neg hy2]

end

end SteinTomas.S2HC

#print axioms SteinTomas.S2HC.kap_density
#print axioms SteinTomas.S2HC.hpaper_eq
