import Mathlib
import SteinTomasCircle.Basic.Chains
import SteinTomasCircle.Section4.Pointwise
import SteinTomasCircle.Section4.CauchySchwarz
import SteinTomasCircle.Section4.SquareIdentity
import SteinTomasCircle.Section4.ResidualBound

/-!
# Section 4: Proposition 4.4 (prop:master) and Theorem 1.2 (symmetric and general case)

External inputs (cited in the paper itself):
* density property of ν = (fσ)*³ (definition) and ν ∈ L² (CO15);
* density property of ρ = σ*³, radiality ρ(x) = ρ_r(|x|), the BSWZ12/Becker25 formula for ρ_r;
* magic identity ‖Ef‖₆⁶ = 5π²∫(|x|²−1)ν² (CFOT17);
* the Fourier series of |sin| (for Q ≤ (2/π)‖f‖₂⁴);
* general case: ‖Ef‖₆ ≤ ‖Ef♯‖₆ (CFOT17 Steps 1–2).
-/

namespace SteinTomas.S4M

open Real MeasureTheory Set Function
open scoped ENNReal
open SteinTomas.S4R

noncomputable section

local notation "μI" => (volume.restrict (Ioc (0 : ℝ) (2 * π)))

variable {f : ℝ → ℝ} {ν ρ : ℝ × ℝ → ℝ} {ρr : ℝ → ℝ}

/-- |ω₁+ω₂+ω₃|² = 9 − Σ|ωᵢ−ωⱼ|²; ≥ 9 ⇒ sin(θ₂−θ₁) = 0 -/
lemma nsq_ss_le (p : ℝ × ℝ × ℝ) (h : 9 ≤ nsq (ss p)) : Real.sin (p.2.1 - p.1) = 0 := by
  unfold nsq ss om at h
  simp only [Prod.fst_add, Prod.snd_add] at h
  have h1 := Real.sin_sq_add_cos_sq p.1
  have h2 := Real.sin_sq_add_cos_sq p.2.1
  have h3 := Real.sin_sq_add_cos_sq p.2.2
  have hc : Real.cos p.1 = Real.cos p.2.1 := by
    nlinarith [sq_nonneg (Real.cos p.1 - Real.cos p.2.1), sq_nonneg (Real.cos p.1 - Real.cos p.2.2),
      sq_nonneg (Real.cos p.2.1 - Real.cos p.2.2), sq_nonneg (Real.sin p.1 - Real.sin p.2.1),
      sq_nonneg (Real.sin p.1 - Real.sin p.2.2), sq_nonneg (Real.sin p.2.1 - Real.sin p.2.2)]
  have hs : Real.sin p.1 = Real.sin p.2.1 := by
    nlinarith [sq_nonneg (Real.cos p.1 - Real.cos p.2.1), sq_nonneg (Real.cos p.1 - Real.cos p.2.2),
      sq_nonneg (Real.cos p.2.1 - Real.cos p.2.2), sq_nonneg (Real.sin p.1 - Real.sin p.2.1),
      sq_nonneg (Real.sin p.1 - Real.sin p.2.2), sq_nonneg (Real.sin p.2.1 - Real.sin p.2.2)]
  rw [Real.sin_sub, ← hc, ← hs]; ring

/-- ν vanishes almost everywhere on {|x| ≥ 3} -/
lemma nu_supp (hνm : Measurable ν) (hν0 : ∀ y, 0 ≤ ν y)
    (hν : ∀ Ψ : ℝ × ℝ → ℝ≥0∞, Measurable Ψ →
      ∫⁻ y, Ψ y * ENNReal.ofReal (ν y) = ∫⁻ p, Ψ (ss p) * ENNReal.ofReal (FF f p) ∂M3) :
    ∀ᵐ x, 9 ≤ nsq x → ν x = 0 := by
  have hA : MeasurableSet {x : ℝ × ℝ | 9 ≤ nsq x} :=
    measurableSet_le measurable_const (by unfold nsq; fun_prop)
  have h := hν ({x : ℝ × ℝ | 9 ≤ nsq x}.indicator 1) (measurable_one.indicator hA)
  have hz : ∫⁻ p, {x : ℝ × ℝ | 9 ≤ nsq x}.indicator 1 (ss p) * ENNReal.ofReal (FF f p) ∂M3 = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero (μ := M3)
    filter_upwards [ae_J12] with p hp
    have : ss p ∉ {x : ℝ × ℝ | 9 ≤ nsq x} := by
      intro hm
      have := nsq_ss_le p hm
      unfold J12 at hp; rw [this, abs_zero] at hp; exact lt_irrefl _ hp
    simp [indicator_of_notMem this]
  rw [hz] at h
  have h' : ∫⁻ y in {x : ℝ × ℝ | 9 ≤ nsq x}, ENNReal.ofReal (ν y) = 0 := by
    rw [← lintegral_indicator hA, ← h]
    refine lintegral_congr (fun y => ?_)
    by_cases hy : y ∈ {x : ℝ × ℝ | 9 ≤ nsq x}
    · simp [indicator_of_mem hy]
    · simp [indicator_of_notMem hy]
  have := (lintegral_eq_zero_iff (ENNReal.measurable_ofReal.comp hνm)).1 h'
  rw [Filter.EventuallyEq, ae_restrict_iff' hA] at this
  filter_upwards [this] with x hx hx9
  have h0 : ENNReal.ofReal (ν x) = 0 := hx hx9
  exact le_antisymm (ENNReal.ofReal_eq_zero.1 h0) (hν0 x)

/-- ofReal(∫F) ≤ ∫ofReal(F) -/
lemma ofReal_int_le {F : ℝ × ℝ → ℝ} (hF : Integrable F) :
    ENNReal.ofReal (∫ x, F x) ≤ ∫⁻ x, ENNReal.ofReal (F x) := by
  have h1 : ∫ x, F x ≤ ∫ x, max (F x) 0 :=
    integral_mono hF hF.pos_part (fun x => le_max_left _ _)
  have h2 : ENNReal.ofReal (∫ x, max (F x) 0) = ∫⁻ x, ENNReal.ofReal (max (F x) 0) :=
    ofReal_integral_eq_lintegral_ofReal hF.pos_part
      (Filter.Eventually.of_forall (fun x => le_max_right _ _))
  have h3 : ∀ x, ENNReal.ofReal (max (F x) 0) = ENNReal.ofReal (F x) := by
    intro x
    rcases le_total 0 (F x) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  calc ENNReal.ofReal (∫ x, F x) ≤ ENNReal.ofReal (∫ x, max (F x) 0) := ENNReal.ofReal_le_ofReal h1
    _ = _ := h2
    _ = _ := lintegral_congr h3

/-- prop:master -/
theorem master (hfm : Measurable f) (hf0 : ∀ θ, 0 ≤ f θ) (hper : Periodic f (2 * π))
    (hanti : ∀ θ, f (θ + π) = f θ) (hf : MemLp f 2 μI)
    -- ν = (fσ)*³ (CO15)
    (hνm : Measurable ν) (hν0 : ∀ y, 0 ≤ ν y)
    (hν : ∀ Ψ : ℝ × ℝ → ℝ≥0∞, Measurable Ψ →
      ∫⁻ y, Ψ y * ENNReal.ofReal (ν y) = ∫⁻ p, Ψ (ss p) * ENNReal.ofReal (FF f p) ∂M3)
    (hνL2 : ∫⁻ x, ENNReal.ofReal (ν x ^ 2) < ∞)
    -- ρ = σ*³ (BSWZ12, Becker25)
    (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρd : ∀ Ψ : ℝ × ℝ → ℝ≥0∞, Measurable Ψ →
      ∫⁻ y, Ψ y * ENNReal.ofReal (ρ y) = ∫⁻ p, Ψ (ss p) ∂M3)
    (hrad : ∀ y, ρ y = ρr (Real.sqrt (nsq y))) (hρr0 : ∀ r, 0 ≤ ρr r)
    (hρr : ∀ r, 1 < r → r < 3 → ρr r = 4 / Real.sqrt r * S2R.Kl ((r + 1) ^ 3 * (3 - r) / (16 * r)))
    -- magic identity (CFOT17)
    {E6 : ℝ} (hmint : Integrable (fun x => (nsq x - 1) * ν x ^ 2))
    (hmagic : E6 = 5 * π ^ 2 * ∫ x, (nsq x - 1) * ν x ^ 2) :
    E6 ≤ Mconc / 16 * (16 * (∫ t in Ioc 0 (2 * π), f t ^ 2) ^ 3
        - 12 * (∫ t in Ioc 0 (2 * π), f t ^ 2) * S45.Ia f)
      + 45 * π ^ 2 / 2 * (∫ θ in Ioc 0 (2 * π), f θ) ^ 2 * S2C.Qa (fun θ => f θ ^ 2) := by
  have hp := pi_pos
  set B := ∫ t in Ioc 0 (2 * π), f t ^ 2 with hB
  set L := ∫ θ in Ioc 0 (2 * π), f θ with hL
  set Q := S2C.Qa (fun θ => f θ ^ 2) with hQ
  set X := 16 * B ^ 3 - 12 * B * S45.Ia f with hX
  have hfi : Integrable f μI := hf.integrable one_le_two
  have hg : Integrable (fun θ => f θ ^ 2) μI := hf.integrable_sq
  have hssm : Measurable ss := ss_meas
  have hFFm : Measurable (FF f) := (hfm.comp measurable_fst).mul
    ((hfm.comp (measurable_fst.comp measurable_snd)).mul (hfm.comp (measurable_snd.comp measurable_snd)))
  have hFF0 : ∀ p, 0 ≤ FF f p := fun p => by
    unfold FF; have := hf0 p.1; have := hf0 p.2.1; have := hf0 p.2.2; positivity
  -- ∫ν < ∞
  have hνfin : ∫⁻ y, ENNReal.ofReal (ν y) < ∞ := by
    have h := hν (fun _ => 1) measurable_const
    simp only [one_mul] at h
    rw [h]
    have e : ∀ p : ℝ × ℝ × ℝ, ENNReal.ofReal (FF f p)
        = ENNReal.ofReal (f p.1) * (ENNReal.ofReal (f p.2.1) * ENNReal.ofReal (f p.2.2)) := by
      intro p; unfold FF
      rw [ENNReal.ofReal_mul (hf0 _), ENNReal.ofReal_mul (hf0 _)]
    simp_rw [e]
    unfold M3
    have hfa : AEMeasurable (fun θ => ENNReal.ofReal (f θ)) μI :=
      (ENNReal.measurable_ofReal.comp hfm).aemeasurable
    rw [lintegral_prod_mul (f := fun θ => ENNReal.ofReal (f θ))
        (g := fun q : ℝ × ℝ => ENNReal.ofReal (f q.1) * ENNReal.ofReal (f q.2)) hfa
        ((ENNReal.measurable_ofReal.comp (hfm.comp measurable_fst)).mul
          (ENNReal.measurable_ofReal.comp (hfm.comp measurable_snd))).aemeasurable,
      lintegral_prod_mul (f := fun θ => ENNReal.ofReal (f θ)) (g := fun θ => ENNReal.ofReal (f θ))
        hfa hfa,
      ← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ENNReal.ofReal_lt_top)
  -- (a) Cauchy–Schwarz + eq:square-identity
  have hT := S4CS.cs_density (w := fun y => nsq y - 1) hssm hFFm hFF0 hνm hν0 hρm hρ0
    (Continuous.measurable (by unfold nsq; fun_prop)) hν hρd hνfin
  have hsq := S4Sq.square_identity hf hanti
  have hwb : ∀ p : ℝ × ℝ × ℝ, (nsq (ss p) - 1) ^ 2 * FF f p ^ 2
      = ((Real.cos p.1 + Real.cos p.2.1 + Real.cos p.2.2) ^ 2
        + (Real.sin p.1 + Real.sin p.2.1 + Real.sin p.2.2) ^ 2 - 1) ^ 2
        * (f p.1 ^ 2 * (f p.2.1 ^ 2 * f p.2.2 ^ 2)) := by
    intro p; unfold nsq ss om FF; simp only [Prod.fst_add, Prod.snd_add]; ring
  have hint3 : Integrable (fun p : ℝ × ℝ × ℝ => ((Real.cos p.1 + Real.cos p.2.1 + Real.cos p.2.2) ^ 2
        + (Real.sin p.1 + Real.sin p.2.1 + Real.sin p.2.2) ^ 2 - 1) ^ 2
        * (f p.1 ^ 2 * (f p.2.1 ^ 2 * f p.2.2 ^ 2))) M3 := by
    have hG : Integrable (fun p : ℝ × ℝ × ℝ => f p.1 ^ 2 * (f p.2.1 ^ 2 * f p.2.2 ^ 2)) M3 :=
      hg.mul_prod (hg.mul_prod hg)
    refine hG.bdd_mul (c := 64) (Continuous.aestronglyMeasurable (by fun_prop))
      (Filter.Eventually.of_forall (fun p => ?_))
    have h1 := Real.sin_sq_add_cos_sq p.1; have h2 := Real.sin_sq_add_cos_sq p.2.1
    have h3 := Real.sin_sq_add_cos_sq p.2.2
    have hu : 0 ≤ (Real.cos p.1 + Real.cos p.2.1 + Real.cos p.2.2) ^ 2
        + (Real.sin p.1 + Real.sin p.2.1 + Real.sin p.2.2) ^ 2 := by positivity
    have hl : (Real.cos p.1 + Real.cos p.2.1 + Real.cos p.2.2) ^ 2
        + (Real.sin p.1 + Real.sin p.2.1 + Real.sin p.2.2) ^ 2 ≤ 9 := by
      nlinarith [sq_nonneg (Real.cos p.1 - Real.cos p.2.1), sq_nonneg (Real.cos p.2.1 - Real.cos p.2.2),
        sq_nonneg (Real.cos p.1 - Real.cos p.2.2), sq_nonneg (Real.sin p.1 - Real.sin p.2.1),
        sq_nonneg (Real.sin p.2.1 - Real.sin p.2.2), sq_nonneg (Real.sin p.1 - Real.sin p.2.2)]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hX0 : 0 ≤ X := by
    rw [hX, ← hsq]
    exact integral_nonneg (fun p => by positivity)
  have hTX : ∫⁻ y, ENNReal.ofReal ((nsq y - 1) ^ 2 * ν y ^ 2 / ρ y) ≤ ENNReal.ofReal X := by
    refine hT.trans (le_of_eq ?_)
    simp_rw [hwb]
    unfold M3 at hint3 ⊢
    rw [← ofReal_integral_eq_lintegral_ofReal hint3 (Filter.Eventually.of_forall (fun p => by
      simp only [Pi.zero_apply]; positivity)), hsq]
  -- (b) R
  have hRfin : ∫⁻ x, ENNReal.ofReal (Pw x * ν x ^ 2) < ∞ := by
    calc ∫⁻ x, ENNReal.ofReal (Pw x * ν x ^ 2)
        ≤ ∫⁻ x, ENNReal.ofReal 16 * ENNReal.ofReal (ν x ^ 2) := by
          refine lintegral_mono (fun x => ?_)
          rw [← ENNReal.ofReal_mul (by norm_num)]
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (Pw_le x) (sq_nonneg _))
      _ = ENNReal.ofReal 16 * ∫⁻ x, ENNReal.ofReal (ν x ^ 2) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hνL2
  have hRb := R_bound hfm hf0 hper hanti hf hνm hν0 hν hRfin
  -- (c) pointwise eq:scalar-majorant
  set c := π / (4 * Real.sqrt 3) with hc
  have hc0 : 0 ≤ c := by positivity
  have hmaj : ∀ᵐ x, (nsq x - 1) * ν x ^ 2
      ≤ c * ((nsq x - 1) ^ 2 * ν x ^ 2 / ρ x) + Pw x * ν x ^ 2 := by
    filter_upwards [nu_supp hνm hν0 hν] with x hx
    by_cases h9 : 9 ≤ nsq x
    · rw [hx h9]; simp
    · have hm := S45.scalar_majorant hρr hρr0 x (not_le.mp h9)
      rw [← hrad x] at hm
      have hν2 := sq_nonneg (ν x)
      have e : π / (4 * Real.sqrt 3 * ρ x) * (nsq x - 1) ^ 2 * ν x ^ 2
          = c * ((nsq x - 1) ^ 2 * ν x ^ 2 / ρ x) := by
        rw [hc]
        rcases eq_or_ne (ρ x) 0 with h0 | h0
        · rw [h0]; simp
        · field_simp
      have := mul_le_mul_of_nonneg_right hm hν2
      nlinarith [this, e]
  -- (d) assembly
  have hle : ENNReal.ofReal (∫ x, (nsq x - 1) * ν x ^ 2)
      ≤ ENNReal.ofReal c * ENNReal.ofReal X
        + ENNReal.ofReal (9 / 2 * L ^ 2 * Q) := by
    calc ENNReal.ofReal (∫ x, (nsq x - 1) * ν x ^ 2)
        ≤ ∫⁻ x, ENNReal.ofReal ((nsq x - 1) * ν x ^ 2) := ofReal_int_le hmint
      _ ≤ ∫⁻ x, (ENNReal.ofReal c * ENNReal.ofReal ((nsq x - 1) ^ 2 * ν x ^ 2 / ρ x)
            + ENNReal.ofReal (Pw x * ν x ^ 2)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hmaj] with x hx
          rw [← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_add (by
            have := hρ0 x; positivity) (by have := Pw_nonneg x; positivity)]
          exact ENNReal.ofReal_le_ofReal hx
      _ = (ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal ((nsq x - 1) ^ 2 * ν x ^ 2 / ρ x))
            + ∫⁻ x, ENNReal.ofReal (Pw x * ν x ^ 2) := by
          rw [lintegral_add_right _ (show Measurable fun x => ENNReal.ofReal (Pw x * ν x ^ 2) from
              ENNReal.measurable_ofReal.comp (Pw_meas.mul (hνm.pow_const 2))),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := add_le_add (by gcongr) hRb
  have hL0 : 0 ≤ L := integral_nonneg hf0
  have hQ0 : 0 ≤ Q := by
    simp only [hQ]; unfold S2C.Qa
    refine integral_nonneg (fun s => integral_nonneg (fun t => ?_))
    have := sq_nonneg (f s); have := sq_nonneg (f t); positivity
  rw [← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_add (by positivity) (by positivity)] at hle
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle
  rw [hmagic]
  have hM : Mconc / 16 = 5 * π ^ 3 / (4 * Real.sqrt 3) := Chains.Mconc_div16
  rw [hM]
  have e : 5 * π ^ 3 / (4 * Real.sqrt 3) = 5 * π ^ 2 * c := by rw [hc]; ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hreal (by positivity : (0 : ℝ) ≤ 5 * π ^ 2)]

/-- eq:L1-remainder-sym: ‖Ef‖₆⁶ ≤ M‖f‖₂⁶ + 45π‖f‖₁²‖f‖₂⁴ (f ≥ 0 antipodal) -/
theorem L1_remainder_sym (hsin : S2C.SinSeries) (hfm : Measurable f) (hf0 : ∀ θ, 0 ≤ f θ)
    (hper : Periodic f (2 * π)) (hanti : ∀ θ, f (θ + π) = f θ) (hf : MemLp f 2 μI)
    (hνm : Measurable ν) (hν0 : ∀ y, 0 ≤ ν y)
    (hν : ∀ Ψ : ℝ × ℝ → ℝ≥0∞, Measurable Ψ →
      ∫⁻ y, Ψ y * ENNReal.ofReal (ν y) = ∫⁻ p, Ψ (ss p) * ENNReal.ofReal (FF f p) ∂M3)
    (hνL2 : ∫⁻ x, ENNReal.ofReal (ν x ^ 2) < ∞)
    (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρd : ∀ Ψ : ℝ × ℝ → ℝ≥0∞, Measurable Ψ →
      ∫⁻ y, Ψ y * ENNReal.ofReal (ρ y) = ∫⁻ p, Ψ (ss p) ∂M3)
    (hrad : ∀ y, ρ y = ρr (Real.sqrt (nsq y))) (hρr0 : ∀ r, 0 ≤ ρr r)
    (hρr : ∀ r, 1 < r → r < 3 → ρr r = 4 / Real.sqrt r * S2R.Kl ((r + 1) ^ 3 * (3 - r) / (16 * r)))
    {E6 : ℝ} (hmint : Integrable (fun x => (nsq x - 1) * ν x ^ 2))
    (hmagic : E6 = 5 * π ^ 2 * ∫ x, (nsq x - 1) * ν x ^ 2) :
    E6 ≤ Mconc * (∫ t in Ioc 0 (2 * π), f t ^ 2) ^ 3
      + 45 * π * (∫ θ in Ioc 0 (2 * π), f θ) ^ 2 * (∫ t in Ioc 0 (2 * π), f t ^ 2) ^ 2 := by
  have hm := master hfm hf0 hper hanti hf hνm hν0 hν hνL2 hρm hρ0 hρd hrad hρr0 hρr hmint hmagic
  have hg : Integrable (fun θ => f θ ^ 2) μI := hf.integrable_sq
  have hQ := (S2C.Q_bounds' hsin hg (fun x => sq_nonneg _)).2
  have hI : 0 ≤ S45.Ia f := by
    unfold S45.Ia
    refine integral_nonneg (fun s => integral_nonneg (fun t => ?_))
    positivity
  have hM : 0 ≤ Mconc := by unfold Mconc; positivity
  have hB : 0 ≤ ∫ t in Ioc 0 (2 * π), f t ^ 2 := integral_nonneg (fun t => sq_nonneg _)
  exact Chains.L1_sym hM hB hI hQ hm

/-! ## f♯ and the general case of Theorem 1.2 -/

/-- f♯(θ) = ((a(θ)² + a(θ+π)²)/2)^{1/2}, a = |f| -/
def sharp (a : ℝ → ℝ) (θ : ℝ) : ℝ := Real.sqrt ((a θ ^ 2 + a (θ + π) ^ 2) / 2)

lemma sharp_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt ((x ^ 2 + y ^ 2) / 2) ≤ (x + y) / Real.sqrt 2 := by
  rw [le_div_iff₀ (by positivity), ← Real.sqrt_mul (by positivity)]
  rw [show (x ^ 2 + y ^ 2) / 2 * 2 = x ^ 2 + y ^ 2 by ring]
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [mul_nonneg hx hy]

/-- ∫_{(0,2π]} g(θ+π) = ∫ g (g 2π-periodic) -/
lemma int_shift_pi {g : ℝ → ℝ} (hg : Periodic g (2 * π)) :
    ∫ θ in Ioc 0 (2 * π), g (θ + π) = ∫ θ in Ioc 0 (2 * π), g θ := by
  have h2 : (0 : ℝ) ≤ 2 * π := by positivity
  rw [← intervalIntegral.integral_of_le h2, ← intervalIntegral.integral_of_le h2,
    intervalIntegral.integral_comp_add_right (f := g), zero_add,
    show 2 * π + π = π + 2 * π by ring, hg.intervalIntegral_add_eq π 0, zero_add]

/-- ‖f♯‖₂ = ‖f‖₂, ‖f♯‖₁ ≤ √2‖f‖₁ -/
theorem sharp_norms {a : ℝ → ℝ} (ham : Measurable a) (ha0 : ∀ θ, 0 ≤ a θ)
    (haper : Periodic a (2 * π)) (ha : MemLp a 2 μI) :
    ∫ θ in Ioc 0 (2 * π), sharp a θ ^ 2 = ∫ θ in Ioc 0 (2 * π), a θ ^ 2 ∧
    ∫ θ in Ioc 0 (2 * π), sharp a θ ≤ Real.sqrt 2 * ∫ θ in Ioc 0 (2 * π), a θ := by
  have hp := pi_pos
  have hai : Integrable a μI := ha.integrable one_le_two
  have ha2 : Integrable (fun θ => a θ ^ 2) μI := ha.integrable_sq
  have hper2 : Periodic (fun θ => a θ ^ 2) (2 * π) := fun θ => by simp only [haper θ]
  -- integrability after translation: by periodicity of the interval integral
  have hsh : ∀ {g : ℝ → ℝ}, Periodic g (2 * π) → Integrable g μI →
      Integrable (fun θ => g (θ + π)) μI := by
    intro g hg hgi
    have h2 : (0 : ℝ) ≤ 2 * π := by positivity
    have hII : IntervalIntegrable g volume 0 (2 * π) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le h2).2 hgi
    have h3 : IntervalIntegrable g volume π (π + 2 * π) := by
      have hII' : IntervalIntegrable g volume 0 (0 + 2 * π) := by rw [zero_add]; exact hII
      exact hg.intervalIntegrable (by positivity) hII' π (π + 2 * π)
    have h4 := h3.comp_add_right π
    rw [show π - π = 0 by ring, show π + 2 * π - π = 2 * π by ring] at h4
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h2).1 h4
  have hsq : ∀ θ, sharp a θ ^ 2 = (a θ ^ 2 + a (θ + π) ^ 2) / 2 := by
    intro θ; unfold sharp; rw [Real.sq_sqrt (by positivity)]
  have hi2 := hsh hper2 ha2
  constructor
  · simp_rw [hsq]
    rw [integral_div, integral_add ha2 hi2, int_shift_pi hper2]; ring
  · have hb : ∀ θ, sharp a θ ≤ (a θ + a (θ + π)) / Real.sqrt 2 :=
      fun θ => sharp_le (ha0 θ) (ha0 _)
    have hi1 := hsh haper hai
    have hsm : Integrable (sharp a) μI := by
      refine ((hai.add hi1).div_const (Real.sqrt 2)).mono'
        (Continuous.measurable (f := fun p : ℝ × ℝ => Real.sqrt ((p.1 ^ 2 + p.2 ^ 2) / 2))
          (by fun_prop) |>.comp (ham.prodMk (ham.comp (measurable_id.add measurable_const)))
          |>.aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun θ => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ sharp a θ from Real.sqrt_nonneg _)]
      exact hb θ
    calc ∫ θ in Ioc 0 (2 * π), sharp a θ
        ≤ ∫ θ in Ioc 0 (2 * π), (a θ + a (θ + π)) / Real.sqrt 2 :=
          integral_mono hsm ((hai.add hi1).div_const _) hb
      _ = Real.sqrt 2 * ∫ θ in Ioc 0 (2 * π), a θ := by
          rw [integral_div, integral_add hai hi1, int_shift_pi haper]
          have : Real.sqrt 2 ≠ 0 := by positivity
          field_simp
          rw [Real.sq_sqrt (by norm_num)]; ring

/-- Theorem 1.2: ‖Ef‖₆⁶ ≤ M‖f‖₂⁶ + 90π‖f‖₁²‖f‖₂⁴.
`E ≤ E♯` (CFOT17) is an external input; the symmetric case is applied to f♯. -/
theorem thm_L1 {E Es : ℝ} {a : ℝ → ℝ} (ham : Measurable a) (ha0 : ∀ θ, 0 ≤ a θ)
    (haper : Periodic a (2 * π)) (ha : MemLp a 2 μI)
    (hE : E ≤ Es)
    (hs : Es ≤ Mconc * (∫ t in Ioc 0 (2 * π), sharp a t ^ 2) ^ 3
      + 45 * π * (∫ θ in Ioc 0 (2 * π), sharp a θ) ^ 2 * (∫ t in Ioc 0 (2 * π), sharp a t ^ 2) ^ 2) :
    E ≤ Mconc * (∫ t in Ioc 0 (2 * π), a t ^ 2) ^ 3
      + 90 * π * (∫ θ in Ioc 0 (2 * π), a θ) ^ 2 * (∫ t in Ioc 0 (2 * π), a t ^ 2) ^ 2 := by
  obtain ⟨h2, h1⟩ := sharp_norms ham ha0 haper ha
  rw [h2] at hs
  exact Chains.L1_general hE hs (integral_nonneg (fun θ => Real.sqrt_nonneg _)) h1

end

end SteinTomas.S4M

#print axioms SteinTomas.S4M.master
#print axioms SteinTomas.S4M.L1_remainder_sym
#print axioms SteinTomas.S4M.thm_L1
