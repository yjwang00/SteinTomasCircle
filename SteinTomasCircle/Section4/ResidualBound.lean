import Mathlib
import SteinTomasCircle.Section4.Residual

/-!
# Section 4: the remaining steps of the estimate for R

* `R5`: ∫ J12 f₃ 𝒫(s)ν(s)²/(1+χ) ≤ ‖f‖₁·R
* `R2`: R = 3∫ (J12/D)𝒫(s)ν(s)FF
* `R_bound`: eq:residual-simple, R ≤ (9/2)‖f‖₁²Q(f²)
-/

namespace SteinTomas.S4R

open Real MeasureTheory Set Function
open scoped ENNReal

noncomputable section

local notation "μI" => (volume.restrict (Ioc (0 : ℝ) (2 * π)))

variable {f : ℝ → ℝ} {ν : ℝ × ℝ → ℝ}

def H2 (f : ℝ → ℝ) (ν : ℝ × ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  J12 p * f p.2.2 * Pw (ss p) * ν (ss p) ^ 2 / (1 + chi p)

def kk (c : ℝ) (x : ℝ × ℝ) : ℝ :=
  (if nsq (x - om c) < 4 then 1 else 0) / (1 + if nsq (x + om c) ≤ 4 then 1 else 0)

lemma kk_sum (c : ℝ) (x : ℝ × ℝ) : kk c x + kk (π + c) x ≤ 1 := by
  have e1 : x - om (π + c) = x + om c := by
    rw [show π + c = c + π by ring, om_pi]; ext <;> simp
  have e2 : x + om (π + c) = x - om c := by
    rw [show π + c = c + π by ring, om_pi]; ext <;> simp [sub_eq_add_neg]
  unfold kk; rw [e1, e2]
  by_cases h1 : nsq (x - om c) < 4 <;> by_cases h2 : nsq (x + om c) < 4 <;>
    by_cases h3 : nsq (x + om c) ≤ 4 <;> by_cases h4 : nsq (x - om c) ≤ 4 <;>
    simp only [h1, h2, h3, h4, if_true, if_false] <;> norm_num <;>
    first | linarith | (exfalso; linarith)

lemma kk_nonneg (c : ℝ) (x : ℝ × ℝ) : 0 ≤ kk c x := by
  unfold kk; split_ifs <;> norm_num

lemma kk_meas (c : ℝ) : Measurable (kk c) := by
  unfold kk
  have c1 : Continuous fun x : ℝ × ℝ => nsq (x - om c) := nsq_cont.comp (continuous_id.sub continuous_const)
  have c2 : Continuous fun x : ℝ × ℝ => nsq (x + om c) := nsq_cont.comp (continuous_id.add continuous_const)
  exact Measurable.div (Measurable.ite (measurableSet_lt c1.measurable measurable_const)
    measurable_const measurable_const)
    (measurable_const.add (Measurable.ite (measurableSet_le c2.measurable measurable_const)
      measurable_const measurable_const))

lemma ss_meas : Measurable ss := by
  apply Continuous.measurable; unfold ss
  exact ((om_cont.comp continuous_fst).add (om_cont.comp (continuous_fst.comp continuous_snd))).add
    (om_cont.comp (continuous_snd.comp continuous_snd))

set_option maxHeartbeats 1000000 in
theorem R5 (hfm : Measurable f) (hf0 : ∀ θ, 0 ≤ f θ) (hper : Periodic f (2 * π))
    (hanti : ∀ θ, f (θ + π) = f θ) (hfi : Integrable f μI)
    (hνm : Measurable ν) :
    ∫⁻ p, ENNReal.ofReal (H2 f ν p) ∂M3
      ≤ ENNReal.ofReal (∫ θ in Ioc 0 (2 * π), f θ) * ∫⁻ x, ENNReal.ofReal (Pw x * ν x ^ 2) := by
  set R := ∫⁻ x, ENNReal.ofReal (Pw x * ν x ^ 2) with hR
  have hHm : Measurable fun p => ENNReal.ofReal (H2 f ν p) := by
    unfold H2
    exact ENNReal.measurable_ofReal.comp
      (((((Continuous.measurable (by unfold J12; fun_prop)).mul (hfm.comp (measurable_snd.comp measurable_snd))).mul
        (Pw_meas.comp ss_meas)).mul ((hνm.comp ss_meas).pow_const 2)).div (measurable_const.add chi_meas))
  -- change the order: θ₃ outermost
  have hord : ∫⁻ p, ENNReal.ofReal (H2 f ν p) ∂M3
      = ∫⁻ c in Ioc 0 (2 * π), ∫⁻ a in Ioc 0 (2 * π), ∫⁻ b in Ioc 0 (2 * π),
          ENNReal.ofReal (H2 f ν (a, b, c)) := by
    unfold M3
    rw [lintegral_prod _ hHm.aemeasurable]
    have h1 : ∀ a : ℝ, ∫⁻ q, ENNReal.ofReal (H2 f ν (a, q)) ∂(Measure.prod μI μI)
        = ∫⁻ c in Ioc 0 (2 * π), ∫⁻ b in Ioc 0 (2 * π), ENNReal.ofReal (H2 f ν (a, b, c)) := by
      intro a
      have hma : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (H2 f ν (a, q)) :=
        hHm.comp (by fun_prop)
      rw [lintegral_prod _ hma.aemeasurable]
      exact lintegral_lintegral_swap (hHm.comp
        (show Measurable fun q : ℝ × ℝ => (a, q.1, q.2) by fun_prop)).aemeasurable
    simp_rw [h1]
    exact lintegral_lintegral_swap (Measurable.lintegral_prod_right'
      (f := fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal (H2 f ν (q.1.1, q.2, q.1.2)))
      (hHm.comp (show Measurable fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.2, q.1.2) by fun_prop))).aemeasurable
  -- eq:pair-change-of-variables for fixed θ₃
  have hinner : ∀ c : ℝ, ∫⁻ a in Ioc 0 (2 * π), ∫⁻ b in Ioc 0 (2 * π),
        ENNReal.ofReal (H2 f ν (a, b, c))
      = 2 * ∫⁻ x, ENNReal.ofReal (f c * (Pw x * ν x ^ 2) * kk c x) := by
    intro c
    set Kc : ℝ × ℝ → ℝ := fun y => f c * Pw (y + om c) * ν (y + om c) ^ 2
      / (1 + if nsq (y + (2 : ℝ) • om c) ≤ 4 then 1 else 0) with hKc
    have hKm : Measurable Kc := by
      simp only [hKc]
      refine (((measurable_const.mul (Pw_meas.comp (measurable_id.add measurable_const))).mul
        ((hνm.comp (measurable_id.add measurable_const)).pow_const 2))).div
        (measurable_const.add (Measurable.ite (measurableSet_le (by unfold nsq; fun_prop)
          measurable_const) measurable_const measurable_const))
    have hpt : ∀ a b : ℝ, ENNReal.ofReal (H2 f ν (a, b, c))
        = ENNReal.ofReal |Real.sin (b - a)| * (fun y => ENNReal.ofReal (Kc y))
          (Real.cos a + Real.cos b, Real.sin a + Real.sin b) := by
      intro a b
      rw [← ENNReal.ofReal_mul (abs_nonneg _)]
      congr 1
      have hom : (Real.cos a + Real.cos b, Real.sin a + Real.sin b) = om a + om b := rfl
      simp only [hKc, hom, H2, J12, ss, chi]
      ring
    simp_rw [hpt]
    rw [S2V.pair_cov (Ψ := fun y => ENNReal.ofReal (Kc y)) (ENNReal.measurable_ofReal.comp hKm)]
    congr 1
    -- translation x = y + ω₃
    have hD : MeasurableSet {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 4} :=
      measurableSet_lt (by fun_prop) measurable_const
    rw [← lintegral_indicator hD]
    set W : ℝ × ℝ → ℝ≥0∞ := fun x =>
      {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 4}.indicator (fun y => ENNReal.ofReal (Kc y)) (x - om c) with hW
    have hW' : ∀ y, {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 4}.indicator (fun y => ENNReal.ofReal (Kc y)) y
        = W (y + om c) := by
      intro y; simp only [hW, add_sub_cancel_right]
    simp_rw [hW']
    rw [lintegral_add_right_eq_self W (om c)]
    refine lintegral_congr (fun x => ?_)
    simp only [hW]
    have e2 : x - om c + (2 : ℝ) • om c = x + om c := by
      ext <;> simp <;> ring
    by_cases hx : x - om c ∈ {y : ℝ × ℝ | y.1 ^ 2 + y.2 ^ 2 < 4}
    · rw [indicator_of_mem hx]
      have hx' : nsq (x - om c) < 4 := hx
      congr 1
      simp only [hKc, kk, if_pos hx', sub_add_cancel, e2]
      ring
    · rw [indicator_of_notMem hx]
      have hx' : ¬ nsq (x - om c) < 4 := hx
      simp only [kk, if_neg hx']
      simp
  rw [hord]
  simp_rw [hinner]
  -- averaging over ±ω₃
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ → ℝ≥0∞,
      Y = fun c => 2 * ∫⁻ x, ENNReal.ofReal (f c * (Pw x * ν x ^ 2) * kk c x) := ⟨_, rfl⟩
  rw [show (fun c => 2 * ∫⁻ x, ENNReal.ofReal (f c * (Pw x * ν x ^ 2) * kk c x)) = Y from hY.symm]
  have hkk : Measurable fun q : ℝ × (ℝ × ℝ) => kk q.1 q.2 := by
    unfold kk
    have c1 : Continuous fun q : ℝ × (ℝ × ℝ) => nsq (q.2 - om q.1) :=
      nsq_cont.comp (continuous_snd.sub (om_cont.comp continuous_fst))
    have c2 : Continuous fun q : ℝ × (ℝ × ℝ) => nsq (q.2 + om q.1) :=
      nsq_cont.comp (continuous_snd.add (om_cont.comp continuous_fst))
    exact Measurable.div (Measurable.ite (measurableSet_lt c1.measurable measurable_const)
      measurable_const measurable_const)
      (measurable_const.add (Measurable.ite (measurableSet_le c2.measurable measurable_const)
        measurable_const measurable_const))
  have hYm : Measurable Y := by
    simp only [hY]
    refine measurable_const.mul (Measurable.lintegral_prod_right' (f := fun q : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (f q.1 * (Pw q.2 * ν q.2 ^ 2) * kk q.1 q.2)) ?_)
    exact ENNReal.measurable_ofReal.comp (((hfm.comp measurable_fst).mul
      ((Pw_meas.comp measurable_snd).mul ((hνm.comp measurable_snd).pow_const 2))).mul hkk)
  have hYper : Periodic Y (2 * π) := by
    intro c; simp only [hY, hper c, kk, om_two_pi]
  have hsh := S2V.lint_shift hYper hYm π
  have hpt2 : ∀ c, Y c + Y (π + c) ≤ 2 * (ENNReal.ofReal (f c) * R) := by
    intro c
    simp only [hY]
    have hmc : Measurable fun x : ℝ × ℝ => ENNReal.ofReal (f c * (Pw x * ν x ^ 2) * kk c x) :=
      ENNReal.measurable_ofReal.comp
        ((measurable_const.mul (Pw_meas.mul (hνm.pow_const 2))).mul (kk_meas c))
    rw [← mul_add, ← lintegral_add_left hmc]
    gcongr 2 * ?_
    rw [hR, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono (fun x => ?_)
    have hfc : f (π + c) = f c := by rw [add_comm]; exact hanti c
    have hA0 : 0 ≤ f c * (Pw x * ν x ^ 2) := by
      have := hf0 c; have := Pw_nonneg x; positivity
    rw [hfc, ← ENNReal.ofReal_add (mul_nonneg hA0 (kk_nonneg c x)) (mul_nonneg hA0 (kk_nonneg _ x)),
      ← ENNReal.ofReal_mul (hf0 c)]
    apply ENNReal.ofReal_le_ofReal
    have hk := kk_sum c x
    have hA : 0 ≤ f c * (Pw x * ν x ^ 2) := by
      have := hf0 c; have := Pw_nonneg x; positivity
    nlinarith
  have h2 : 2 * ∫⁻ c in Ioc 0 (2 * π), Y c ≤ 2 * (ENNReal.ofReal (∫ θ in Ioc 0 (2 * π), f θ) * R) := by
    calc 2 * ∫⁻ c in Ioc 0 (2 * π), Y c
        = (∫⁻ c in Ioc 0 (2 * π), Y c) + ∫⁻ c in Ioc 0 (2 * π), Y (π + c) := by
          rw [two_mul]; congr 1; exact hsh.symm
      _ = ∫⁻ c in Ioc 0 (2 * π), (Y c + Y (π + c)) :=
          (lintegral_add_left hYm _).symm
      _ ≤ ∫⁻ c in Ioc 0 (2 * π), 2 * (ENNReal.ofReal (f c) * R) := lintegral_mono hpt2
      _ = 2 * (ENNReal.ofReal (∫ θ in Ioc 0 (2 * π), f θ) * R) := by
          rw [lintegral_const_mul' 2 _ (by norm_num),
            lintegral_mul_const (f := fun a => ENNReal.ofReal (f a)) R
              (ENNReal.measurable_ofReal.comp hfm),
            ← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0)]
  exact ecancel 2 (by norm_num) (by norm_num) h2


/-! ## (R2) symmetrization -/

lemma abs_sin_comm (a b : ℝ) : |Real.sin (a - b)| = |Real.sin (b - a)| := by
  rw [← neg_sub, Real.sin_neg, abs_neg]

def Xf (f : ℝ → ℝ) (ν : ℝ × ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ := Pw (ss p) * ν (ss p) * FF f p

lemma Xf_nonneg (hf0 : ∀ θ, 0 ≤ f θ) (hν0 : ∀ y, 0 ≤ ν y) (p : ℝ × ℝ × ℝ) : 0 ≤ Xf f ν p := by
  unfold Xf FF
  have := Pw_nonneg (ss p); have := hν0 (ss p)
  have := hf0 p.1; have := hf0 p.2.1; have := hf0 p.2.2
  positivity

theorem R2 (hfm : Measurable f) (hf0 : ∀ θ, 0 ≤ f θ) (hνm : Measurable ν) (hν0 : ∀ y, 0 ≤ ν y)
    (hν : ∀ Ψ : ℝ × ℝ → ℝ≥0∞, Measurable Ψ →
      ∫⁻ y, Ψ y * ENNReal.ofReal (ν y) = ∫⁻ p, Ψ (ss p) * ENNReal.ofReal (FF f p) ∂M3) :
    ∫⁻ x, ENNReal.ofReal (Pw x * ν x ^ 2)
      = 3 * ∫⁻ p, ENNReal.ofReal (J12 p / Dd p * Xf f ν p) ∂M3 := by
  have hXm : Measurable (Xf f ν) := by
    unfold Xf FF
    exact ((Pw_meas.comp ss_meas).mul (hνm.comp ss_meas)).mul
      ((hfm.comp measurable_fst).mul ((hfm.comp (measurable_fst.comp measurable_snd)).mul
        (hfm.comp (measurable_snd.comp measurable_snd))))
  have hDm : Measurable Dd := Continuous.measurable (by unfold Dd J12 J13 J23; fun_prop)
  have mJ : ∀ J : ℝ × ℝ × ℝ → ℝ, Continuous J →
      Measurable fun p => ENNReal.ofReal (J p / Dd p * Xf f ν p) :=
    fun J hJ => ENNReal.measurable_ofReal.comp ((hJ.measurable.div hDm).mul hXm)
  have c12 : Continuous J12 := by unfold J12; fun_prop
  have c13 : Continuous J13 := by unfold J13; fun_prop
  have c23 : Continuous J23 := by unfold J23; fun_prop
  -- (a)
  have ha : ∫⁻ x, ENNReal.ofReal (Pw x * ν x ^ 2) = ∫⁻ p, ENNReal.ofReal (Xf f ν p) ∂M3 := by
    have h := hν (fun y => ENNReal.ofReal (Pw y * ν y))
      (ENNReal.measurable_ofReal.comp (Pw_meas.mul hνm))
    have e1 : ∀ y, ENNReal.ofReal (Pw y * ν y) * ENNReal.ofReal (ν y) = ENNReal.ofReal (Pw y * ν y ^ 2) := by
      intro y; rw [← ENNReal.ofReal_mul (by have := Pw_nonneg y; have := hν0 y; positivity)]; ring_nf
    have e2 : ∀ p, ENNReal.ofReal (Pw (ss p) * ν (ss p)) * ENNReal.ofReal (FF f p)
        = ENNReal.ofReal (Xf f ν p) := by
      intro p; rw [← ENNReal.ofReal_mul (by have := Pw_nonneg (ss p); have := hν0 (ss p); positivity)]
      rfl
    simp only [e1, e2] at h
    exact h
  -- (b)
  have hb : ∀ᵐ p ∂M3, ENNReal.ofReal (Xf f ν p)
      = ENNReal.ofReal (J12 p / Dd p * Xf f ν p) + ENNReal.ofReal (J13 p / Dd p * Xf f ν p)
        + ENNReal.ofReal (J23 p / Dd p * Xf f ν p) := by
    filter_upwards [ae_J12] with p hp
    have hX := Xf_nonneg hf0 hν0 p
    obtain ⟨h1, h2, h3⟩ := J_nonneg p
    have hD : 0 < Dd p := by unfold Dd; linarith
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    have : J12 p / Dd p + J13 p / Dd p + J23 p / Dd p = 1 := by
      have hs : J12 p + J13 p + J23 p = Dd p := rfl
      rw [← add_div, ← add_div, hs, div_self hD.ne']
    calc Xf f ν p = (J12 p / Dd p + J13 p / Dd p + J23 p / Dd p) * Xf f ν p := by rw [this, one_mul]
      _ = _ := by ring
  rw [ha, lintegral_congr_ae hb, lintegral_add_left (show Measurable fun p =>
      ENNReal.ofReal (J12 p / Dd p * Xf f ν p) + ENNReal.ofReal (J13 p / Dd p * Xf f ν p)
      from (mJ J12 c12).add (mJ J13 c13)),
    lintegral_add_left (mJ J12 c12)]
  -- (c) J13 ↔ J12 (swap θ₂, θ₃)
  have hXs23 : ∀ p : ℝ × ℝ × ℝ, Xf f ν (p.1, p.2.2, p.2.1) = Xf f ν p := by
    intro p; unfold Xf FF ss; simp only
    rw [add_right_comm (om p.1)]; ring_nf
  have hDs23 : ∀ p : ℝ × ℝ × ℝ, Dd (p.1, p.2.2, p.2.1) = Dd p := by
    intro p; unfold Dd J12 J13 J23; simp only
    rw [abs_sin_comm p.2.1 p.2.2]; ring
  have hc : ∫⁻ p, ENNReal.ofReal (J13 p / Dd p * Xf f ν p) ∂M3
      = ∫⁻ p, ENNReal.ofReal (J12 p / Dd p * Xf f ν p) ∂M3 := by
    rw [← mp_swap23.lintegral_comp (mJ J12 c12)]
    refine lintegral_congr (fun p => ?_)
    simp only [hXs23, hDs23]
    rfl
  -- (d) J23 ↔ J13 (swap θ₁, θ₂)
  have hXs12 : ∀ p : ℝ × ℝ × ℝ, Xf f ν (p.2.1, p.1, p.2.2) = Xf f ν p := by
    intro p; unfold Xf FF ss; simp only
    rw [add_comm (om p.2.1) (om p.1)]; ring_nf
  have hDs12 : ∀ p : ℝ × ℝ × ℝ, Dd (p.2.1, p.1, p.2.2) = Dd p := by
    intro p; unfold Dd J12 J13 J23; simp only
    rw [abs_sin_comm p.1 p.2.1]; ring
  have hd : ∫⁻ p, ENNReal.ofReal (J23 p / Dd p * Xf f ν p) ∂M3
      = ∫⁻ p, ENNReal.ofReal (J13 p / Dd p * Xf f ν p) ∂M3 := by
    rw [← mp_swap12.lintegral_comp (mJ J13 c13)]
    refine lintegral_congr (fun p => ?_)
    simp only [hXs12, hDs12]
    rfl
  rw [hd, hc]; ring

/-! ## eq:residual-simple -/

theorem R_bound (hfm : Measurable f) (hf0 : ∀ θ, 0 ≤ f θ) (hper : Periodic f (2 * π))
    (hanti : ∀ θ, f (θ + π) = f θ) (hf : MemLp f 2 μI)
    (hνm : Measurable ν) (hν0 : ∀ y, 0 ≤ ν y)
    (hν : ∀ Ψ : ℝ × ℝ → ℝ≥0∞, Measurable Ψ →
      ∫⁻ y, Ψ y * ENNReal.ofReal (ν y) = ∫⁻ p, Ψ (ss p) * ENNReal.ofReal (FF f p) ∂M3)
    (hfin : ∫⁻ x, ENNReal.ofReal (Pw x * ν x ^ 2) < ∞) :
    ∫⁻ x, ENNReal.ofReal (Pw x * ν x ^ 2)
      ≤ ENNReal.ofReal (9 / 2 * (∫ θ in Ioc 0 (2 * π), f θ) ^ 2 * S2C.Qa (fun θ => f θ ^ 2)) := by
  have hfi : Integrable f μI := hf.integrable one_le_two
  set R := ∫⁻ x, ENNReal.ofReal (Pw x * ν x ^ 2) with hR
  set L := ∫ θ in Ioc 0 (2 * π), f θ with hL
  set Q := S2C.Qa (fun θ => f θ ^ 2) with hQ
  have hL0 : 0 ≤ L := integral_nonneg hf0
  have hQ0 : 0 ≤ Q := by
    simp only [hQ]; unfold S2C.Qa
    refine integral_nonneg (fun s => integral_nonneg (fun t => ?_))
    have := sq_nonneg (f s); have := sq_nonneg (f t); positivity
  have hDm : Measurable Dd := Continuous.measurable (by unfold Dd J12 J13 J23; fun_prop)
  have hXm : Measurable (Xf f ν) := by
    unfold Xf FF
    exact ((Pw_meas.comp ss_meas).mul (hνm.comp ss_meas)).mul
      ((hfm.comp measurable_fst).mul ((hfm.comp (measurable_fst.comp measurable_snd)).mul
        (hfm.comp (measurable_snd.comp measurable_snd))))
  have hIm : Measurable fun p => ENNReal.ofReal (J12 p / Dd p * Xf f ν p) :=
    ENNReal.measurable_ofReal.comp (((Continuous.measurable (by unfold J12; fun_prop)).div hDm).mul hXm)
  have hGm : Measurable fun p => ENNReal.ofReal (G2 f p) := ENNReal.measurable_ofReal.comp (G2_meas hfm)
  have hHm : Measurable fun p => ENNReal.ofReal (H2 f ν p) := by
    unfold H2
    exact ENNReal.measurable_ofReal.comp
      (((((Continuous.measurable (by unfold J12; fun_prop)).mul (hfm.comp (measurable_snd.comp measurable_snd))).mul
        (Pw_meas.comp ss_meas)).mul ((hνm.comp ss_meas).pow_const 2)).div (measurable_const.add chi_meas))
  have h4 := R4 hfm hf0 hper hanti hf
  have h5 := R5 hfm hf0 hper hanti hfi hνm
  have h2 := R2 hfm hf0 hνm hν0 hν
  -- pointwise weighted AM–GM
  have hamgm : ∀ lam : ℝ, 0 < lam → ∀ p, 2 * ENNReal.ofReal (J12 p / Dd p * Xf f ν p)
      ≤ ENNReal.ofReal lam * ENNReal.ofReal (G2 f p) + ENNReal.ofReal lam⁻¹ * ENNReal.ofReal (H2 f ν p) := by
    intro lam hlam p
    have hX := Xf_nonneg hf0 hν0 p
    obtain ⟨j0, j13, j23⟩ := J_nonneg p
    have hP := Pw_nonneg (ss p)
    have hn := hν0 (ss p)
    have hc := chi_nonneg p
    have hf1 := hf0 p.1; have hf2 := hf0 p.2.1; have hf3 := hf0 p.2.2
    have hG0 : 0 ≤ G2 f p := by unfold G2; positivity
    have hH0 : 0 ≤ H2 f ν p := by unfold H2; positivity
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul hlam.le, ← ENNReal.ofReal_mul (inv_nonneg.2 hlam.le),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rcases eq_or_lt_of_le (show 0 ≤ Dd p by unfold Dd; positivity) with hD | hD
    · rw [← hD, div_zero, zero_mul, mul_zero]; positivity
    · have hw : 0 < 1 + chi p := by linarith
      have key : lam * G2 f p + lam⁻¹ * H2 f ν p - 2 * (J12 p / Dd p * Xf f ν p)
          = J12 p * Pw (ss p) * f p.2.2 / ((1 + chi p) * lam)
            * (lam * (1 + chi p) * (f p.1 * f p.2.1) / Dd p - ν (ss p)) ^ 2 := by
        unfold G2 H2 Xf FF
        field_simp
        ring
      have : 0 ≤ J12 p * Pw (ss p) * f p.2.2 / ((1 + chi p) * lam)
          * (lam * (1 + chi p) * (f p.1 * f p.2.1) / Dd p - ν (ss p)) ^ 2 := by positivity
      linarith
  have hgen : ∀ lam : ℝ, 0 < lam → 2 * R ≤ 3 * (ENNReal.ofReal (lam * (1 / 2 * L * Q))
      + ENNReal.ofReal (lam⁻¹ * L) * R) := by
    intro lam hlam
    have hI : 2 * ∫⁻ p, ENNReal.ofReal (J12 p / Dd p * Xf f ν p) ∂M3
        ≤ ENNReal.ofReal lam * ∫⁻ p, ENNReal.ofReal (G2 f p) ∂M3
          + ENNReal.ofReal lam⁻¹ * ∫⁻ p, ENNReal.ofReal (H2 f ν p) ∂M3 := by
      rw [← lintegral_const_mul' _ _ (by norm_num), ← lintegral_const_mul _ hGm,
        ← lintegral_const_mul _ hHm, ← lintegral_add_left (hGm.const_mul _)]
      exact lintegral_mono (hamgm lam hlam)
    have hI2 : 2 * ∫⁻ p, ENNReal.ofReal (J12 p / Dd p * Xf f ν p) ∂M3
        ≤ ENNReal.ofReal (lam * (1 / 2 * L * Q)) + ENNReal.ofReal (lam⁻¹ * L) * R := by
      refine hI.trans (add_le_add ?_ ?_)
      · rw [ENNReal.ofReal_mul hlam.le]; gcongr
      · rw [ENNReal.ofReal_mul (inv_nonneg.2 hlam.le), mul_assoc]; gcongr
    rw [show 2 * R = 3 * (2 * ∫⁻ p, ENNReal.ofReal (J12 p / Dd p * Xf f ν p) ∂M3) by
      rw [hR, h2]; ring]
    gcongr
  -- convert to real numbers
  set r := R.toReal with hr
  have hRr : R = ENNReal.ofReal r := (ENNReal.ofReal_toReal hfin.ne).symm
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hreal : ∀ lam : ℝ, 0 < lam → 2 * r ≤ 3 * (lam * (1 / 2 * L * Q) + lam⁻¹ * L * r) := by
    intro lam hlam
    have h := hgen lam hlam
    rw [hRr, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
  have hfinal : r ≤ 9 / 2 * L ^ 2 * Q := by
    rcases eq_or_lt_of_le hL0 with hL | hL
    · have := hreal 1 one_pos
      rw [← hL] at this ⊢
      nlinarith
    · have := hreal (3 * L) (by positivity)
      have e : 3 * (3 * L * (1 / 2 * L * Q) + (3 * L)⁻¹ * L * r) = 9 / 2 * L ^ 2 * Q + r := by
        field_simp; ring
      rw [e] at this
      linarith
  rw [hRr]
  exact ENNReal.ofReal_le_ofReal hfinal

#print axioms SteinTomas.S4R.R_bound

end

end SteinTomas.S4R
