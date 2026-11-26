import Mathlib
import SteinTomasCircle.Basic.Elementary
import SteinTomasCircle.Section2.FourierSeries
import SteinTomasCircle.Section2.PolarKernel
import SteinTomasCircle.Section2.BesselGlobal
import SteinTomasCircle.Section2.NormalizedExtension

/-!
# Section 2 (§2.1): eq:quadratic-spectral (radial integral)

∫₀^∞ J₀⁶ [avg F(r,·)²] r dr = α₀a₀² + Σ_{n≥1} α_{2n} a_{2n}², α_{2n} = ∫₀^∞ J₀⁴J_{2n}² r dr.
External input: J_{2n} is continuous; J₀⁴J_{2n}² r is integrable on (0,∞) and α_{2n} is uniformly bounded (decay from DLMF 10.17;
numerical values from CFOT17, OST17).
-/

namespace SteinTomas.S2Q

open Real MeasureTheory Set Filter Topology SteinTomas.S2F SteinTomas.S2K SteinTomas.Section2
  SteinTomas.S2E

noncomputable section

/-- α_{2n} = ∫₀^∞ J₀⁴ J_{2n}² r dr -/
def alpha (Jb : ℕ → ℝ → ℝ) (n : ℕ) : ℝ := ∫ r in Ioi (0 : ℝ), Jb 0 r ^ 4 * Jb n r ^ 2 * r

/-- Integrability of a sum of nonnegative integrable functions -/
lemma integrable_tsum_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : ℕ → α → ℝ}
    (hF : ∀ k, Integrable (F k) μ) (hnn : ∀ k, 0 ≤ᵐ[μ] F k)
    (hsum : Summable (fun k => ∫ a, F k a ∂μ))
    (hmeas : AEStronglyMeasurable (fun a => ∑' k, F k a) μ)
    (hpt : ∀ᵐ a ∂μ, Summable (fun k => F k a)) :
    Integrable (fun a => ∑' k, F k a) μ := by
  have hnn' : ∀ᵐ a ∂μ, ∀ k, 0 ≤ F k a := ae_all_iff.2 hnn
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal]
  · have h1 : ∫⁻ a, ENNReal.ofReal (∑' k, F k a) ∂μ = ∑' k, ∫⁻ a, ENNReal.ofReal (F k a) ∂μ := by
      rw [← lintegral_tsum (fun k => (hF k).1.aemeasurable.ennreal_ofReal)]
      apply lintegral_congr_ae
      filter_upwards [hpt, hnn'] with a ha hn
      exact ENNReal.ofReal_tsum_of_nonneg hn ha
    rw [h1]
    have e : ∀ k, ∫⁻ a, ENNReal.ofReal (F k a) ∂μ = ENNReal.ofReal (∫ a, F k a ∂μ) :=
      fun k => (ofReal_integral_eq_lintegral_ofReal (hF k) (hnn k)).symm
    simp_rw [e]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => integral_nonneg_of_ae (hnn k)) hsum]
    exact ENNReal.ofReal_lt_top
  · filter_upwards [hpt, hnn'] with a ha hn
    exact tsum_nonneg hn

variable {f : ℝ → ℝ} {Jb : ℕ → ℝ → ℝ}

/-- Pointwise identity: J₀⁶·avg F²·r = a₀²J₀⁶r + Σ_k a_{2(k+1)}² J₀⁴J_{2(k+1)}² r -/
lemma pointwise_sum (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π))))
    (hanti : ∀ θ, f (θ + π) = f θ) (hB : BesselKernel Jb) (r : ℝ) :
    HasSum (fun k => asq f k * (Jb 0 r ^ 4 * Jb (k + 1) r ^ 2 * r))
      (Jb 0 r ^ 6 * avg (fun ψ => F Jb f r ψ ^ 2) * r - a0 f ^ 2 * (Jb 0 r ^ 6 * r)) := by
  have h := (avg_G_sq hf hanti hB r).mul_right (Jb 0 r ^ 4 * r)
  convert h using 1
  · funext k; ring
  · by_cases hJ : Jb 0 r = 0
    · simp [hJ]
    · rw [avg_F_sq hf hJ]
      have hp : (2 * π) ≠ 0 := by positivity
      field_simp

/-- eq:quadratic-spectral -/
theorem quad_spectral (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π))))
    (hanti : ∀ θ, f (θ + π) = f θ) (hB : BesselKernel Jb)
    (hcont : ∀ n, Continuous (Jb n))
    (hint : ∀ n, IntegrableOn (fun r => Jb 0 r ^ 4 * Jb n r ^ 2 * r) (Ioi 0))
    (hbd : ∃ C, ∀ n, alpha Jb n ≤ C) :
    ∃ S, HasSum (fun k => alpha Jb (k + 1) * asq f k) S ∧
      IntegrableOn (fun r => Jb 0 r ^ 6 * avg (fun ψ => F Jb f r ψ ^ 2) * r) (Ioi 0) ∧
      ∫ r in Ioi 0, Jb 0 r ^ 6 * avg (fun ψ => F Jb f r ψ ^ 2) * r = alpha Jb 0 * a0 f ^ 2 + S := by
  obtain ⟨C, hC⟩ := hbd
  set μ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set Fk : ℕ → ℝ → ℝ := fun k r => asq f k * (Jb 0 r ^ 4 * Jb (k + 1) r ^ 2 * r) with hFk
  have hasq : ∀ k, 0 ≤ asq f k := fun k => by unfold asq; positivity
  have hFi : ∀ k, Integrable (Fk k) μ := fun k => (hint (k + 1)).const_mul _
  have hFnn : ∀ k, 0 ≤ᵐ[μ] Fk k := by
    intro k
    rw [hμ, EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with r hr
    have : (0 : ℝ) < r := hr
    simp only [hFk, Pi.zero_apply]
    exact mul_nonneg (hasq k) (by positivity)
  have hFint : ∀ k, ∫ r, Fk k r ∂μ = asq f k * alpha Jb (k + 1) := by
    intro k
    simp only [hFk, hμ, alpha]
    rw [MeasureTheory.integral_const_mul]
  have hαnn : ∀ n, 0 ≤ alpha Jb n := by
    intro n
    apply setIntegral_nonneg measurableSet_Ioi
    intro r hr
    have : (0 : ℝ) < r := hr
    positivity
  have hpar := parseval_even hf hanti
  have hsum : Summable (fun k => asq f k * alpha Jb (k + 1)) := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (hasq k) (hαnn _))
      (fun k => mul_le_mul_of_nonneg_left (hC (k + 1)) (hasq k)) ?_
    exact (hpar.summable.mul_right C)
  have hsum' : Summable (fun k => ∫ r, Fk k r ∂μ) := by simp_rw [hFint]; exact hsum
  have hsumn : Summable (fun k => ∫ r, ‖Fk k r‖ ∂μ) := by
    refine hsum'.congr (fun k => ?_)
    apply integral_congr_ae
    filter_upwards [hFnn k] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg hr]
  have hpt : ∀ r, HasSum (fun k => Fk k r)
      (Jb 0 r ^ 6 * avg (fun ψ => F Jb f r ψ ^ 2) * r - a0 f ^ 2 * (Jb 0 r ^ 6 * r)) :=
    fun r => pointwise_sum hf hanti hB r
  -- measurability
  have hmeasF : ∀ k, Measurable (Fk k) := by
    intro k
    have := (hcont 0).pow 4 |>.mul ((hcont (k + 1)).pow 2) |>.mul continuous_id
    exact (this.const_mul (asq f k)).measurable
  have hmeas : Measurable (fun r => ∑' k, Fk k r) := by
    apply measurable_of_tendsto_metrizable (f := fun n r => ∑ k ∈ Finset.range n, Fk k r)
    · intro n; exact Finset.measurable_sum _ (fun k _ => hmeasF k)
    · rw [tendsto_pi_nhds]
      intro r
      exact (hpt r).summable.hasSum.tendsto_sum_nat
  have hGi : Integrable (fun r => ∑' k, Fk k r) μ :=
    integrable_tsum_nonneg hFi hFnn hsum' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun r => (hpt r).summable))
  have hGint := hasSum_integral_of_summable_integral_norm hFi hsumn
  simp_rw [hFint] at hGint
  -- J₀⁶ r is integrable
  have h0i : Integrable (fun r => Jb 0 r ^ 6 * r) μ := by
    refine (hint 0).congr ?_
    filter_upwards with r
    ring
  have htsum : ∀ r, ∑' k, Fk k r
      = Jb 0 r ^ 6 * avg (fun ψ => F Jb f r ψ ^ 2) * r - a0 f ^ 2 * (Jb 0 r ^ 6 * r) :=
    fun r => (hpt r).tsum_eq
  have hgi : Integrable (fun r => Jb 0 r ^ 6 * avg (fun ψ => F Jb f r ψ ^ 2) * r) μ := by
    refine (hGi.add (h0i.const_mul (a0 f ^ 2))).congr ?_
    filter_upwards with r
    simp only [Pi.add_apply]
    rw [htsum r]; ring
  refine ⟨∫ r, ∑' k, Fk k r ∂μ, ?_, hgi, ?_⟩
  · refine hGint.congr_fun (fun k => ?_)
    ring
  · have e : (fun r => Jb 0 r ^ 6 * avg (fun ψ => F Jb f r ψ ^ 2) * r)
        = fun r => (∑' k, Fk k r) + a0 f ^ 2 * (Jb 0 r ^ 6 * r) := by
      funext r; rw [htsum r]; ring
    have hα0 : alpha Jb 0 = ∫ r, Jb 0 r ^ 6 * r ∂μ := by
      simp only [alpha, hμ]
      apply integral_congr_ae
      filter_upwards with r
      ring
    rw [e, MeasureTheory.integral_add hGi (h0i.const_mul _), MeasureTheory.integral_const_mul, hα0]
    ring

end

end SteinTomas.S2Q

#print axioms SteinTomas.S2Q.quad_spectral
