import Mathlib
import SteinTomasCircle.Basic.Defs
import SteinTomasCircle.Section2.QFourier
import SteinTomasCircle.Section2.PairChangeOfVariables
import SteinTomasCircle.Section2.PairDensity

/-!
# Section 4: eq:residual-simple, R ≤ (9/2)‖f‖₁²Q(f²)

Notation (angular variables, p = (θ₁,(θ₂,θ₃)), M3 = σ×σ×σ):
`ss p = ω₁+ω₂+ω₃`, `J12 = |det(ω₁,ω₂)| = |sin(θ₂−θ₁)|` etc., `Dd = J12+J13+J23`,
`chi p = 1{|ω₁+ω₂+2ω₃| ≤ 2}`, `FF p = f(θ₁)f(θ₂)f(θ₃)`.
ν is used only through the density property ∫Ψν = ∫_{M3} Ψ(s)FF (ν = (fσ)*³, CO15), and ∫ν² < ∞ is assumed.
R := ∫ 𝒫 ν².
Steps: (R2) symmetrization R = 3∫(J12/D)𝒫(s)ν(s)FF; (R3) pointwise weighted AM–GM;
(R4) averaging over the four signs + Lemma 4.3: ∫ J12𝒫(1+χ)/D² f₁²f₂²f₃ ≤ ½‖f‖₁Q(f²);
(R5) eq:pair-change-of-variables in (ω₁,ω₂), translation, averaging over ±ω₃: ∫ J12 f₃𝒫ν²/(1+χ) ≤ ‖f‖₁R.
-/

namespace SteinTomas.S4R

open Real MeasureTheory Set Function
open scoped ENNReal

noncomputable section

local notation "μI" => (volume.restrict (Ioc (0 : ℝ) (2 * π)))

/-- M3 = σ × σ × σ -/
def M3 : Measure (ℝ × ℝ × ℝ) := Measure.prod μI (Measure.prod μI μI)

def om (θ : ℝ) : ℝ × ℝ := (Real.cos θ, Real.sin θ)
def ss (p : ℝ × ℝ × ℝ) : ℝ × ℝ := om p.1 + om p.2.1 + om p.2.2
def J12 (p : ℝ × ℝ × ℝ) : ℝ := |Real.sin (p.2.1 - p.1)|
def J13 (p : ℝ × ℝ × ℝ) : ℝ := |Real.sin (p.2.2 - p.1)|
def J23 (p : ℝ × ℝ × ℝ) : ℝ := |Real.sin (p.2.2 - p.2.1)|
def Dd (p : ℝ × ℝ × ℝ) : ℝ := J12 p + J13 p + J23 p
def chi (p : ℝ × ℝ × ℝ) : ℝ :=
  if nsq (om p.1 + om p.2.1 + (2 : ℝ) • om p.2.2) ≤ 4 then 1 else 0
def FF (f : ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ := f p.1 * (f p.2.1 * f p.2.2)

lemma om_cont : Continuous om := by unfold om; fun_prop
lemma om_pi (θ : ℝ) : om (θ + π) = (-1 : ℝ) • om θ := by
  unfold om; ext <;> simp [Real.cos_add_pi, Real.sin_add_pi]
lemma om_two_pi (θ : ℝ) : om (θ + 2 * π) = om θ := by
  unfold om; simp [Real.cos_add_two_pi, Real.sin_add_two_pi]
lemma nsq_om (θ : ℝ) : nsq (om θ) = 1 := by
  unfold nsq om; simp only; linear_combination Real.sin_sq_add_cos_sq θ
lemma det_om (a b : ℝ) : det2 (om a) (om b) = Real.sin (b - a) := by
  unfold det2 om; simp only; rw [Real.sin_sub]; ring
lemma abs_sin_pi (x : ℝ) : |Real.sin (x + π)| = |Real.sin x| := by
  rw [Real.sin_add_pi, abs_neg]
lemma abs_sin_sub_pi (x : ℝ) : |Real.sin (x - π)| = |Real.sin x| := by
  rw [Real.sin_sub_pi, abs_neg]

lemma J_nonneg (p : ℝ × ℝ × ℝ) : 0 ≤ J12 p ∧ 0 ≤ J13 p ∧ 0 ≤ J23 p :=
  ⟨abs_nonneg _, abs_nonneg _, abs_nonneg _⟩

lemma Pw_nonneg (x : ℝ × ℝ) : 0 ≤ Pw x := by
  rw [Pw_eq]; unfold FourSign.Pl
  split_ifs with h
  · have := FourSign.ψ_nonneg h.1.le
    have : 0 ≤ 8 - (nsq x - 1) := by linarith [h.2]
    have := h.1.le
    positivity
  · exact le_refl _

lemma Pw_le (x : ℝ × ℝ) : Pw x ≤ 16 := by
  rw [Pw_eq]; unfold FourSign.Pl
  split_ifs with h
  · set l := nsq x - 1
    have h1 : l * (8 - l) ≤ 16 := by nlinarith [sq_nonneg (l - 4)]
    have h3 : 0 ≤ l * (8 - l) := by nlinarith [h.1, h.2]
    have h2 : FourSign.ψ l ≤ 1 := by
      unfold FourSign.ψ
      have hs : 0 ≤ Real.sqrt (1 + l) := Real.sqrt_nonneg _
      have : l / (16 * (3 + Real.sqrt (1 + l))) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith [h.2]
      linarith
    calc l * (8 - l) * FourSign.ψ l ≤ 16 * 1 :=
          mul_le_mul h1 h2 (FourSign.ψ_nonneg h.1.le) (by norm_num)
      _ = 16 := by norm_num
  · norm_num

lemma nsq_cont : Continuous nsq := by unfold nsq; fun_prop

lemma Pl_meas : Measurable FourSign.Pl := by
  unfold FourSign.Pl
  have hs : MeasurableSet {l : ℝ | 0 < l ∧ l < 8} := by
    have : {l : ℝ | 0 < l ∧ l < 8} = Ioo 0 8 := rfl
    rw [this]; exact measurableSet_Ioo
  refine Measurable.ite hs ?_ measurable_const
  unfold FourSign.ψ
  fun_prop

lemma Pw_meas : Measurable Pw := by
  have : Pw = fun x => FourSign.Pl (nsq x - 1) := funext Pw_eq
  rw [this]
  exact Pl_meas.comp ((nsq_cont.sub continuous_const).measurable)

lemma chi_arg_cont : Continuous fun p : ℝ × ℝ × ℝ => om p.1 + om p.2.1 + (2 : ℝ) • om p.2.2 := by
  unfold om; fun_prop

lemma chi_meas : Measurable chi := by
  unfold chi
  exact Measurable.ite (measurableSet_le (nsq_cont.comp chi_arg_cont).measurable measurable_const)
    measurable_const measurable_const

lemma J12_cont : Continuous J12 := by unfold J12; fun_prop
lemma Dd_cont : Continuous Dd := by unfold Dd J12 J13 J23; fun_prop
lemma ss_cont : Continuous ss := by
  unfold ss
  exact ((om_cont.comp continuous_fst).add (om_cont.comp (continuous_fst.comp continuous_snd))).add
    (om_cont.comp (continuous_snd.comp continuous_snd))

lemma per1 (x y : ℝ) : |Real.sin (y - (x + 2 * π))| = |Real.sin (y - x)| := by
  rw [show y - (x + 2 * π) = (y - x) - 2 * π by ring, Real.sin_sub_two_pi]
lemma per2 (x y : ℝ) : |Real.sin (y + 2 * π - x)| = |Real.sin (y - x)| := by
  rw [show y + 2 * π - x = (y - x) + 2 * π by ring, Real.sin_add_two_pi]
lemma L1 (x y : ℝ) : |Real.sin (y - (x + π))| = |Real.sin (y - x)| := by
  rw [show y - (x + π) = (y - x) - π by ring, abs_sin_sub_pi]
lemma L2 (x y : ℝ) : |Real.sin (y + π - x)| = |Real.sin (y - x)| := by
  rw [show y + π - x = (y - x) + π by ring, abs_sin_pi]
lemma L3 (x y : ℝ) : Real.sin (y + π - (x + π)) = Real.sin (y - x) := by ring_nf

lemma chi_nonneg (p : ℝ × ℝ × ℝ) : 0 ≤ chi p := by unfold chi; split_ifs <;> norm_num

variable {f : ℝ → ℝ}

/-- Cancelling a nonzero finite constant -/
lemma ecancel {a b : ℝ≥0∞} (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ⊤) (h : c * a ≤ c * b) : a ≤ b := by
  calc a = c⁻¹ * (c * a) := by rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
    _ ≤ c⁻¹ * (c * b) := by gcongr
    _ = b := by rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

/-! ## Translation invariance in the first coordinate -/

lemma shift_fst {β : Type*} [MeasurableSpace β] {ν : Measure β} [SFinite ν]
    {G : ℝ × β → ℝ≥0∞} (hG : Measurable G) (hper : ∀ a b, G (a + 2 * π, b) = G (a, b))
    (c : ℝ) :
    ∫⁻ p, G (c + p.1, p.2) ∂(Measure.prod μI ν) = ∫⁻ p, G p ∂(Measure.prod μI ν) := by
  have hm : Measurable fun p : ℝ × β => G (c + p.1, p.2) :=
    hG.comp (by fun_prop : Measurable fun p : ℝ × β => (c + p.1, p.2))
  rw [lintegral_prod _ hm.aemeasurable, lintegral_prod _ hG.aemeasurable]
  exact S2V.lint_shift (g := fun a => ∫⁻ b, G (a, b) ∂ν) (fun a => by simp only [hper])
    hG.lintegral_prod_right' c

lemma shift1 {G : ℝ × ℝ × ℝ → ℝ≥0∞} (hG : Measurable G)
    (hper : ∀ a b, G (a + 2 * π, b) = G (a, b)) :
    ∫⁻ p, G (p.1 + π, p.2) ∂M3 = ∫⁻ p, G p ∂M3 := by
  unfold M3
  have := shift_fst (ν := Measure.prod μI μI) hG hper π
  simp only [add_comm π] at this
  exact this

lemma shift2 {G : ℝ × ℝ × ℝ → ℝ≥0∞} (hG : Measurable G)
    (hper : ∀ a b c, G (a, b + 2 * π, c) = G (a, b, c)) :
    ∫⁻ p, G (p.1, p.2.1 + π, p.2.2) ∂M3 = ∫⁻ p, G p ∂M3 := by
  unfold M3
  have hm : Measurable fun p : ℝ × ℝ × ℝ => G (p.1, p.2.1 + π, p.2.2) :=
    hG.comp (by fun_prop : Measurable fun p : ℝ × ℝ × ℝ => (p.1, p.2.1 + π, p.2.2))
  rw [lintegral_prod _ hm.aemeasurable, lintegral_prod _ hG.aemeasurable]
  refine lintegral_congr (fun a => ?_)
  have hGa : Measurable fun q : ℝ × ℝ => G (a, q) := hG.comp (by fun_prop)
  have := shift_fst (ν := μI) hGa (fun b c => hper a b c) π
  simp only [add_comm π] at this
  exact this

/-! ## Permutation invariance -/

lemma mp_swap23 : MeasurePreserving (fun p : ℝ × ℝ × ℝ => (p.1, p.2.2, p.2.1)) M3 M3 := by
  unfold M3
  exact (MeasurePreserving.id μI).prod (Measure.measurePreserving_swap (μ := μI) (ν := μI))

lemma mp_swap12 : MeasurePreserving (fun p : ℝ × ℝ × ℝ => (p.2.1, p.1, p.2.2)) M3 M3 := by
  unfold M3
  have e := measurePreserving_prodAssoc μI μI μI
  have h1 := e.symm
  have h2 : MeasurePreserving (Prod.map Prod.swap id)
      (Measure.prod (Measure.prod μI μI) μI) (Measure.prod (Measure.prod μI μI) μI) :=
    (Measure.measurePreserving_swap (μ := μI) (ν := μI)).prod (MeasurePreserving.id μI)
  exact (e.comp (h2.comp h1))

/-! ## The null set {sin(θ₂−θ₁) = 0} -/

lemma ae_J12 : ∀ᵐ p ∂M3, 0 < J12 p := by
  have hs : ∀ a : ℝ, (volume.restrict (Ioc (0 : ℝ) (2 * π))) {b | Real.sin (b - a) = 0} = 0 := by
    intro a
    have hc : {b : ℝ | Real.sin (b - a) = 0}.Countable := by
      have hsub : {b : ℝ | Real.sin (b - a) = 0} ⊆ Set.range (fun n : ℤ => (n : ℝ) * π + a) := by
        intro t ht
        obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 (show Real.sin (t - a) = 0 from ht)
        exact ⟨n, by simp only; linarith⟩
      exact (Set.countable_range _).mono hsub
    exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans
      (le_of_eq (hc.measure_zero volume)))
  rw [ae_iff]
  have hset : {p : ℝ × ℝ × ℝ | ¬ 0 < J12 p} = {p | Real.sin (p.2.1 - p.1) = 0} := by
    ext p; simp only [mem_setOf_eq, J12, not_lt]
    constructor
    · intro h; exact abs_eq_zero.1 (le_antisymm h (abs_nonneg _))
    · intro h; rw [h, abs_zero]
  rw [hset]
  unfold M3
  rw [Measure.measure_prod_null (measurableSet_eq_fun (by fun_prop) measurable_const)]
  refine Filter.Eventually.of_forall (fun a => ?_)
  have : Prod.mk a ⁻¹' {p : ℝ × ℝ × ℝ | Real.sin (p.2.1 - p.1) = 0}
      = {b : ℝ | Real.sin (b - a) = 0} ×ˢ (univ : Set ℝ) := by
    ext q; simp
  show (Measure.prod μI μI) (Prod.mk a ⁻¹' {p : ℝ × ℝ × ℝ | Real.sin (p.2.1 - p.1) = 0}) = 0
  rw [this, Measure.prod_prod, hs a, zero_mul]

/-! ## (R4) the four signs -/

/-- Integrand of the first factor -/
def G2 (f : ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  J12 p * Pw (ss p) * (1 + chi p) / Dd p ^ 2 * (f p.1 ^ 2 * f p.2.1 ^ 2 * f p.2.2)

lemma G2_meas (hfm : Measurable f) : Measurable (G2 f) := by
  unfold G2
  have h1 : Measurable fun p : ℝ × ℝ × ℝ => J12 p * Pw (ss p) * (1 + chi p) / Dd p ^ 2 :=
    ((J12_cont.measurable.mul (Pw_meas.comp ss_cont.measurable)).mul
      (measurable_const.add chi_meas)).div (Dd_cont.measurable.pow_const 2)
  have h2 : Measurable fun p : ℝ × ℝ × ℝ => f p.1 ^ 2 * f p.2.1 ^ 2 * f p.2.2 :=
    (((hfm.comp measurable_fst).pow_const 2).mul
      ((hfm.comp (measurable_fst.comp measurable_snd)).pow_const 2)).mul
      (hfm.comp (measurable_snd.comp measurable_snd))
  exact h1.mul h2

lemma G2_nonneg (hf0 : ∀ θ, 0 ≤ f θ) (p : ℝ × ℝ × ℝ) : 0 ≤ G2 f p := by
  unfold G2
  have := J_nonneg p; have := Pw_nonneg (ss p); have := chi_nonneg p
  have := hf0 p.2.2
  have : 0 ≤ J12 p := abs_nonneg _
  positivity

theorem R4 (hfm : Measurable f) (hf0 : ∀ θ, 0 ≤ f θ) (hper : Periodic f (2 * π))
    (hanti : ∀ θ, f (θ + π) = f θ) (hf : MemLp f 2 μI) :
    ∫⁻ p, ENNReal.ofReal (G2 f p) ∂M3
      ≤ ENNReal.ofReal (1 / 2 * (∫ θ in Ioc 0 (2 * π), f θ) * S2C.Qa (fun θ => f θ ^ 2)) := by
  set Φ : ℝ × ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (G2 f p) with hΦ
  have hΦm : Measurable Φ := ENNReal.measurable_ofReal.comp (G2_meas hfm)
  -- J, D, f² are invariant under translation, s ↦ s_{εδ}
  have hp1 : ∀ a b, Φ (a + 2 * π, b) = Φ (a, b) := by
    intro a b
    simp only [hΦ, G2, ss, J12, J13, J23, Dd, chi, om_two_pi, hper a, per1]
  have hp2 : ∀ a b c, Φ (a, b + 2 * π, c) = Φ (a, b, c) := by
    intro a b c
    simp only [hΦ, G2, ss, J12, J23, J13, Dd, chi, om_two_pi, hper b, per1, per2]
  have hT1 := shift1 hΦm hp1
  have hT2 := shift2 hΦm hp2
  have hT12 := shift2 (G := fun p => Φ (p.1 + π, p.2))
    (hΦm.comp (by fun_prop : Measurable fun p : ℝ × ℝ × ℝ => (p.1 + π, p.2)))
    (fun a b c => by simp only; exact hp2 (a + π) b c)
  simp only at hT12
  rw [hT1] at hT12
  -- pointwise: the sum of the four terms is ≤ 2 J12 f₁²f₂²f₃
  have hsum : ∀ p : ℝ × ℝ × ℝ, Φ p + Φ (p.1 + π, p.2) + Φ (p.1, p.2.1 + π, p.2.2)
      + Φ (p.1 + π, p.2.1 + π, p.2.2)
      ≤ ENNReal.ofReal (2 * (J12 p * (f p.1 ^ 2 * f p.2.1 ^ 2 * f p.2.2))) := by
    intro p
    obtain ⟨a, b, c⟩ := p
    simp only [hΦ]
    rw [← ENNReal.ofReal_add (G2_nonneg hf0 _) (G2_nonneg hf0 _),
      ← ENNReal.ofReal_add (add_nonneg (G2_nonneg hf0 _) (G2_nonneg hf0 _)) (G2_nonneg hf0 _),
      ← ENNReal.ofReal_add (add_nonneg (add_nonneg (G2_nonneg hf0 _) (G2_nonneg hf0 _))
        (G2_nonneg hf0 _)) (G2_nonneg hf0 _)]
    apply ENNReal.ofReal_le_ofReal
    -- reduce to Lemma 4.3
    have hlem := lem_four_sign (om a) (om b) (om c) (nsq_om a) (nsq_om b) (nsq_om c)
    have hne : (-1 : ℝ) ≠ 1 := by norm_num
    rw [Finset.sum_pair hne, Finset.sum_pair hne, Finset.sum_pair hne] at hlem
    simp only [one_smul, ← om_pi, det_om] at hlem
    set j := |Real.sin (b - a)| with hj
    set d := |Real.sin (b - a)| + |Real.sin (c - a)| + |Real.sin (c - b)| with hd
    set w := f a ^ 2 * f b ^ 2 * f c with hw
    have hj0 : 0 ≤ j := abs_nonneg _
    have hw0 : 0 ≤ w := by have := hf0 c; positivity
    have hd0 : 0 ≤ d := by positivity
    have hchi : ∀ x y : ℝ, chi (x, y, c)
        = if nsq (om x + om y + (2 : ℝ) • om c) ≤ 4 then 1 else 0 := fun x y => rfl
    have e1 : G2 f (a, b, c) = j * (Pw (om a + om b + om c)
        * (1 + if nsq (om a + om b + (2 : ℝ) • om c) ≤ 4 then 1 else 0)) / d ^ 2 * w := by
      simp only [hj, hd, hw, G2, ss, J12, J13, J23, Dd, hchi]; ring
    have e2 : G2 f (a + π, b, c) = j * (Pw (om (a + π) + om b + om c)
        * (1 + if nsq (om (a + π) + om b + (2 : ℝ) • om c) ≤ 4 then 1 else 0)) / d ^ 2 * w := by
      simp only [hj, hd, hw, G2, ss, J12, J13, J23, Dd, hchi, L1, hanti a]; ring
    have e3 : G2 f (a, b + π, c) = j * (Pw (om a + om (b + π) + om c)
        * (1 + if nsq (om a + om (b + π) + (2 : ℝ) • om c) ≤ 4 then 1 else 0)) / d ^ 2 * w := by
      simp only [hj, hd, hw, G2, ss, J12, J13, J23, Dd, hchi, L1, L2, hanti b]; ring
    have e4 : G2 f (a + π, b + π, c) = j * (Pw (om (a + π) + om (b + π) + om c)
        * (1 + if nsq (om (a + π) + om (b + π) + (2 : ℝ) • om c) ≤ 4 then 1 else 0)) / d ^ 2 * w := by
      simp only [hj, hd, hw, G2, ss, J12, J13, J23, Dd, hchi, L1, L3, hanti a, hanti b]; ring
    show G2 f (a, b, c) + G2 f (a + π, b, c) + G2 f (a, b + π, c) + G2 f (a + π, b + π, c)
      ≤ 2 * (J12 (a, b, c) * (f a ^ 2 * f b ^ 2 * f c))
    rw [e1, e2, e3, e4, show J12 (a, b, c) = j from rfl, ← hw]
    rcases eq_or_lt_of_le hd0 with hd' | hd'
    · rw [← hd']; simp
      positivity
    · have hjw : 0 ≤ j * w / d ^ 2 := by positivity
      have hsum4 := mul_le_mul_of_nonneg_left hlem hjw
      have e5 : j * w / d ^ 2 * (2 * d ^ 2) = 2 * (j * w) := by field_simp
      rw [e5] at hsum4
      refine le_of_eq_of_le ?_ hsum4
      ring
  -- combine
  have h4 : 4 * ∫⁻ p, Φ p ∂M3 ≤ ∫⁻ p, ENNReal.ofReal (2 * (J12 p * (f p.1 ^ 2 * f p.2.1 ^ 2 * f p.2.2))) ∂M3 := by
    have hm1 : Measurable fun p : ℝ × ℝ × ℝ => Φ (p.1 + π, p.2) := hΦm.comp (by fun_prop)
    have hm2 : Measurable fun p : ℝ × ℝ × ℝ => Φ (p.1, p.2.1 + π, p.2.2) := hΦm.comp (by fun_prop)
    have hm3 : Measurable fun p : ℝ × ℝ × ℝ => Φ (p.1 + π, p.2.1 + π, p.2.2) := hΦm.comp (by fun_prop)
    calc 4 * ∫⁻ p, Φ p ∂M3
        = ∫⁻ p, Φ p ∂M3 + ∫⁻ p, Φ (p.1 + π, p.2) ∂M3 + ∫⁻ p, Φ (p.1, p.2.1 + π, p.2.2) ∂M3
          + ∫⁻ p, Φ (p.1 + π, p.2.1 + π, p.2.2) ∂M3 := by
          rw [hT1, hT2, hT12]; ring
      _ = ∫⁻ p, (Φ p + Φ (p.1 + π, p.2) + Φ (p.1, p.2.1 + π, p.2.2)
          + Φ (p.1 + π, p.2.1 + π, p.2.2)) ∂M3 := by
          rw [lintegral_add_left (show Measurable fun p : ℝ × ℝ × ℝ => Φ p + Φ (p.1 + π, p.2)
              + Φ (p.1, p.2.1 + π, p.2.2) from (hΦm.add hm1).add hm2),
            lintegral_add_left (show Measurable fun p : ℝ × ℝ × ℝ => Φ p + Φ (p.1 + π, p.2)
              from hΦm.add hm1),
            lintegral_add_left hΦm]
      _ ≤ _ := lintegral_mono hsum
  -- right-hand side = 2 L Q
  have hg : Integrable (fun θ => f θ ^ 2) μI := hf.integrable_sq
  have hfi : Integrable f μI := hf.integrable one_le_two
  have hRHS : ∫⁻ p, ENNReal.ofReal (2 * (J12 p * (f p.1 ^ 2 * f p.2.1 ^ 2 * f p.2.2))) ∂M3
      = ENNReal.ofReal (2 * ((∫ θ in Ioc 0 (2 * π), f θ) * S2C.Qa (fun θ => f θ ^ 2))) := by
    set A : ℝ × ℝ → ℝ≥0∞ := fun q => ENNReal.ofReal (|Real.sin (q.2 - q.1)| * f q.1 ^ 2 * f q.2 ^ 2)
      with hA
    set Bf : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (2 * f t) with hBf
    have hAm : Measurable A := ENNReal.measurable_ofReal.comp
      (((Continuous.measurable (show Continuous fun q : ℝ × ℝ => |Real.sin (q.2 - q.1)| by fun_prop)).mul
        ((hfm.comp measurable_fst).pow_const 2)).mul ((hfm.comp measurable_snd).pow_const 2))
    have hBm : Measurable Bf := ENNReal.measurable_ofReal.comp (measurable_const.mul hfm)
    have hpt : ∀ p : ℝ × ℝ × ℝ, ENNReal.ofReal (2 * (J12 p * (f p.1 ^ 2 * f p.2.1 ^ 2 * f p.2.2)))
        = A (p.1, p.2.1) * Bf p.2.2 := by
      intro p
      simp only [hA, hBf, J12]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1; ring
    simp_rw [hpt]
    have hmp := measurePreserving_prodAssoc μI μI μI
    unfold M3
    rw [← hmp.lintegral_comp (show Measurable fun p : ℝ × ℝ × ℝ => A (p.1, p.2.1) * Bf p.2.2 from
      (hAm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
        (hBm.comp (measurable_snd.comp measurable_snd)))]
    have e : ∀ z : (ℝ × ℝ) × ℝ, A ((MeasurableEquiv.prodAssoc z).1, (MeasurableEquiv.prodAssoc z).2.1)
        * Bf (MeasurableEquiv.prodAssoc z).2.2 = A z.1 * Bf z.2 := fun z => rfl
    simp_rw [e]
    rw [lintegral_prod_mul hAm.aemeasurable hBm.aemeasurable, lintegral_prod _ hAm.aemeasurable]
    simp only [hA, hBf]
    rw [S2H.Qa_lint hg (fun x => sq_nonneg _),
      ← ofReal_integral_eq_lintegral_ofReal (hfi.const_mul 2)
        (Filter.Eventually.of_forall (fun t => by have := hf0 t; simp only [Pi.zero_apply]; positivity)),
      integral_const_mul,
      ← ENNReal.ofReal_mul (by
        unfold S2C.Qa
        refine integral_nonneg (fun s => integral_nonneg (fun t => ?_))
        have := sq_nonneg (f s); have := sq_nonneg (f t); positivity)]
    congr 1; ring
  rw [hRHS] at h4
  have hQ0 : 0 ≤ S2C.Qa (fun θ => f θ ^ 2) := by
    unfold S2C.Qa
    refine integral_nonneg (fun s => integral_nonneg (fun t => ?_))
    have := sq_nonneg (f s); have := sq_nonneg (f t); positivity
  have hL0 : 0 ≤ ∫ θ in Ioc 0 (2 * π), f θ := integral_nonneg hf0
  have h4' : 4 * ∫⁻ p, Φ p ∂M3 ≤ 4 * ENNReal.ofReal (1 / 2 * (∫ θ in Ioc 0 (2 * π), f θ)
      * S2C.Qa (fun θ => f θ ^ 2)) := by
    refine h4.trans (le_of_eq ?_)
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; ring
  exact ecancel 4 (by norm_num) (by norm_num) h4'

end

end SteinTomas.S4R

#print axioms SteinTomas.S4R.R4
