import SteinTomasCircle.MainProof.Prep

namespace SteinTomas.S6

open Real MeasureTheory Set Function Filter
open scoped ENNReal ComplexConjugate

noncomputable section

local notation "Plane" => (ℝ × ℝ)

attribute [local instance] isFin

/-- Density of the triple convolution, with the Plancherel norm and the CFOT17 magic identity. -/
structure NuData (g : ℝ → ℝ) (ν : Plane → ℝ) : Prop where
  meas : Measurable ν
  nonneg : ∀ y, 0 ≤ ν y
  dens : ∀ Ψ : Plane → ℝ≥0∞, Measurable Ψ →
    ∫⁻ y, Ψ y * ENNReal.ofReal (ν y) =
      ∫⁻ p, Ψ (S4R.ss p) * ENNReal.ofReal (S4R.FF g p) ∂S4R.M3
  l2 : ∫⁻ x, ENNReal.ofReal (ν x ^ 2) =
    ENNReal.ofReal ((∫ x, S2P.Ec g x ^ 6) / (4 * π ^ 2))
  magic : (∫ x, S2P.Ec g x ^ 6) = 5 * π ^ 2 * ∫ x, (nsq x - 1) * ν x ^ 2

/-- Fourier transform on the plane with kernel exp(−i x·y). -/
def planeFourier (a : Plane → ℝ) (x : Plane) : ℂ :=
  ∫ y, (a y : ℂ) * S2HF.ex2 x y

/-- The real part of the usual Plancherel pairing for L¹ ∩ L² functions on the plane. -/
def PlanePlancherel : Prop :=
  ∀ a b : Plane → ℝ, Integrable a → MemLp a 2 volume →
    Integrable b → MemLp b 2 volume →
    (∫ x, a x * b x) = (1 / (4 * π ^ 2)) *
      ∫ x, (conj (planeFourier a x) * planeFourier b x).re

lemma NuData.memLp {g : ℝ → ℝ} {ν : Plane → ℝ} (hν : NuData g ν) :
    MemLp ν 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm hν.meas.aestronglyMeasurable).mpr
  simp only [Real.norm_eq_abs, sq_abs]
  refine ⟨(hν.meas.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => sq_nonneg (ν x)), hν.l2]
  exact ENNReal.ofReal_lt_top

lemma NuData.mint {g : ℝ → ℝ} {ν : Plane → ℝ} (hν : NuData g ν) :
    Integrable (fun x => (nsq x - 1) * ν x ^ 2) := by
  refine ((hν.memLp.integrable_sq).const_mul 8).mono'
    (((S4R.nsq_cont.measurable.sub_const 1).mul (hν.meas.pow_const 2)).aestronglyMeasurable)
    ?_
  filter_upwards [S4M.nu_supp hν.meas hν.nonneg hν.dens] with x hx
  by_cases h : 9 ≤ nsq x
  · simp [hx h]
  · change ‖(nsq x - 1) * ν x ^ 2‖ ≤ 8 * ν x ^ 2
    have h0 : 0 ≤ nsq x := by unfold nsq; positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (ν x))]
    exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩) (sq_nonneg _)

private lemma ex2_add (x y z : Plane) :
    S2HF.ex2 x (y + z) = S2HF.ex2 x y * S2HF.ex2 x z := by
  unfold S2HF.ex2
  rw [← Complex.exp_add]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  push_cast
  ring

private lemma ex2_pt (x : Plane) (θ : ℝ) :
    S2HF.ex2 x (S4R.om θ) = S2HF.ex x θ := rfl

private lemma ν_fourier {g : ℝ → ℝ} (hg : Adm g) {ν : Plane → ℝ} (hν : NuData g ν) :
    Integrable ν ∧ ∀ x, planeFourier ν x = (S2P.Ec g x : ℂ) ^ 3 := by
  have hFF : Measurable (S4R.FF g) :=
    (hg.meas.comp measurable_fst).mul
      ((hg.meas.comp (measurable_fst.comp measurable_snd)).mul
        (hg.meas.comp (measurable_snd.comp measurable_snd)))
  have hFF0 (p) : 0 ≤ S4R.FF g p :=
    mul_nonneg (hg.nonneg _) (mul_nonneg (hg.nonneg _) (hg.nonneg _))
  have hg1 := hg.memLp.integrable one_le_two
  have hiFF : Integrable (S4R.FF g) S4R.M3 := hg1.mul_prod (hg1.mul_prod hg1)
  have hmass := hν.dens 1 measurable_one
  simp only [Pi.one_apply, one_mul] at hmass
  have hiν : Integrable ν := by
    refine ⟨hν.meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hν.nonneg), hmass,
      ← ofReal_integral_eq_lintegral_ofReal hiFF (Eventually.of_forall hFF0)]
    exact ENNReal.ofReal_lt_top
  refine ⟨hiν, fun x => ?_⟩
  have hss : Measurable S4R.ss := by
    unfold S4R.ss
    exact ((S4R.om_cont.measurable.comp measurable_fst).add
      (S4R.om_cont.measurable.comp (measurable_fst.comp measurable_snd))).add
      (S4R.om_cont.measurable.comp (measurable_snd.comp measurable_snd))
  have hpush :
      volume.withDensity (fun y => ENNReal.ofReal (ν y)) =
        (S4R.M3.withDensity (fun p => ENNReal.ofReal (S4R.FF g p))).map S4R.ss := by
    ext s hs
    rw [Measure.map_apply hss hs, withDensity_apply _ hs, withDensity_apply _ (hss hs)]
    have h := hν.dens (s.indicator 1) (measurable_one.indicator hs)
    rw [← lintegral_indicator hs, ← lintegral_indicator (hss hs)]
    convert h using 1
    · apply lintegral_congr
      intro y
      by_cases hy : y ∈ s <;> simp [hy]
    · apply lintegral_congr
      intro p
      by_cases hp : S4R.ss p ∈ s <;> simp [hp]
  have hsmul : (∫ y, S2HF.ex2 x y ∂volume.withDensity (fun y => ENNReal.ofReal (ν y))) =
      planeFourier ν x := by
    rw [integral_withDensity_eq_integral_toReal_smul (f := fun y => ENNReal.ofReal (ν y))
      (ENNReal.measurable_ofReal.comp hν.meas)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) (S2HF.ex2 x)]
    unfold planeFourier
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only
      rw [ENNReal.toReal_ofReal (hν.nonneg y), Complex.real_smul]
  rw [← hsmul, hpush, integral_map hss.aemeasurable (S2HF.ex2_cont x).aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (f := fun p => ENNReal.ofReal (S4R.FF g p))
      (ENNReal.measurable_ofReal.comp hFF)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) (fun p => S2HF.ex2 x (S4R.ss p))]
  let G := S2HF.uf g x
  have hG : (∫ θ, G θ ∂σ) = (S2P.Ec g x : ℂ) := by
    rw [← E_toC hg.memLp hg.per hg.anti]
    rfl
  calc
    _ = ∫ p : ℝ × ℝ × ℝ, G p.1 * (G p.2.1 * G p.2.2) ∂S4R.M3 := by
      apply integral_congr_ae
      refine Eventually.of_forall fun p => ?_
      dsimp only
      rw [ENNReal.toReal_ofReal (hFF0 p), Complex.real_smul,
        S4R.ss, ex2_add, ex2_add, ex2_pt, ex2_pt, ex2_pt]
      dsimp only [G, S2HF.uf, S4R.FF]
      push_cast
      ring
    _ = (∫ θ, G θ ∂σ) * (∫ p : ℝ × ℝ, G p.1 * G p.2 ∂σ.prod σ) :=
      integral_prod_mul (μ := σ) (ν := σ.prod σ) G (fun p : ℝ × ℝ => G p.1 * G p.2)
    _ = _ := by
      rw [integral_prod_mul G G, hG]
      ring

private lemma real_conv_integrable {g : ℝ → ℝ} (hgm : Measurable g) (hg : Integrable g σ)
    {H : Plane → ℝ} (hHm : Measurable H) (hH : Integrable H) :
    Integrable (fun p : ℝ × Plane => g p.1 * H (p.2 - S5B.om p.1)) (σ.prod volume) := by
  have hm : Measurable (fun p : ℝ × Plane => g p.1 * H (p.2 - S5B.om p.1)) :=
    (hgm.comp measurable_fst).mul
      (hHm.comp (measurable_snd.sub (S5B.om_meas.comp measurable_fst)))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall fun θ => ?_, ?_⟩
  · have h := ((measurePreserving_add_right (volume : Measure Plane) (-S5B.om θ)).integrable_comp_emb
      (MeasurableEquiv.addRight (-S5B.om θ)).measurableEmbedding).2 hH
    change Integrable (fun y => H (y + -S5B.om θ)) volume at h
    simpa only [sub_eq_add_neg] using h.const_mul (g θ)
  · convert hg.norm.mul_const (∫ y, ‖H y‖) using 1
    ext θ
    simp_rw [norm_mul, integral_const_mul]
    rw [integral_sub_right_eq_self (fun y => ‖H y‖)]

private lemma conv_fourier {g : ℝ → ℝ} (hgm : Measurable g) (hg : Integrable g σ)
    {H : Plane → ℝ} (hHm : Measurable H) (hH : Integrable H) (x : Plane) :
    planeFourier (fun y => ∫ θ, g θ * H (y - S5B.om θ) ∂σ) x =
      E (toC g) x * planeFourier H x := by
  have hi := real_conv_integrable hgm hg hHm hH
  let T (p : ℝ × Plane) : ℂ := ((g p.1 * H (p.2 - S5B.om p.1) : ℝ) : ℂ) * S2HF.ex2 x p.2
  have hT : Integrable T (σ.prod volume) := by
    refine hi.norm.mono' (hi.ofReal.aestronglyMeasurable.mul
      ((S2HF.ex2_cont x).measurable.comp measurable_snd).aestronglyMeasurable) ?_
    refine Eventually.of_forall fun p => ?_
    change ‖T p‖ ≤ ‖g p.1 * H (p.2 - S5B.om p.1)‖
    simp [T, norm_mul, S2HF.norm_ex2, Real.norm_eq_abs]
  have hFub := integral_integral_swap (f := fun θ y => T (θ, y)) hT
  unfold planeFourier
  calc
    _ = ∫ y : Plane, (∫ θ, T (θ, y) ∂σ) := by
      apply integral_congr_ae
      refine Eventually.of_forall fun y => ?_
      simp only [T, integral_mul_const, integral_complex_ofReal]
    _ = ∫ θ, (∫ y, T (θ, y)) ∂σ := hFub.symm
    _ = _ := by
      have hθ (θ : ℝ) :
          (∫ y, T (θ, y)) = S2HF.uf g x θ * (∫ y, (H y : ℂ) * S2HF.ex2 x y) := by
        rw [← integral_add_right_eq_self (fun y => T (θ, y)) (S5B.om θ), ← integral_const_mul]
        apply integral_congr_ae
        refine Eventually.of_forall fun y => ?_
        change T (θ, y + S5B.om θ) = _
        simp only [T, add_sub_cancel_right, ex2_add]
        change _ = S2HF.uf g x θ * _
        rw [show S2HF.ex2 x (S5B.om θ) = S2HF.ex x θ from rfl]
        unfold S2HF.uf
        push_cast
        ring
      simp_rw [hθ, integral_mul_const]
      rfl

/-- The Plancherel step in Lemma 5.2, specialized after proving the convolution formulas. -/
theorem NuData.plan {g : ℝ → ℝ} (hg : Adm g) {ν : Plane → ℝ} (hν : NuData g ν)
    (hP : PlanePlancherel) :
    ∫⁻ x, ENNReal.ofReal (ν x) * S5B.conv (fun θ => ENNReal.ofReal (g θ))
      (fun y => ENNReal.ofReal (S2H.hfun g y)) x
    = ENNReal.ofReal (1 / (4 * π ^ 2) * ∫ x, S2P.Ec g x ^ 4 * (S2HF.hhat g x).re) := by
  let H := S2H.hfun g
  let w (y : Plane) := ∫ θ, g θ * H (y - S5B.om θ) ∂σ
  let W := S5B.conv (fun θ => ENNReal.ofReal (g θ)) (fun y => ENNReal.ofReal (H y))
  have hH0 : ∀ y, 0 ≤ H y := fun y => by
    unfold H S2H.hfun
    split <;> first | positivity | exact mul_nonneg (mul_nonneg (by norm_num) (hg.nonneg _)) (hg.nonneg _)
  have hHs : ∀ y, 4 ≤ nsq y → H y = 0 := fun y hy => by
    unfold H S2H.hfun
    rw [if_neg (not_lt.mpr (show 4 ≤ y.1 ^ 2 + y.2 ^ 2 from hy))]
  have hHm : Measurable H := S2H.hfun_meas hg.meas
  have hHi : Integrable H := by
    rw [← integrableOn_iff_integrable_of_support_subset (s := S2HF.D)]
    · exact S2HF.h_intOn hg.memLp hg.meas hg.per
    · intro y hy
      contrapose! hy
      simpa only [Function.mem_support, not_not] using hHs y (le_of_not_gt hy)
  have hH2 := (S2H.h_L2_real hg.memLp hg.meas hg.per).1
  have hg1 := hg.memLp.integrable one_le_two
  have hi := real_conv_integrable hg.meas hg1 hHm hHi
  have hw1 : Integrable w := hi.integral_prod_right
  have hw0 : ∀ y, 0 ≤ w y := fun y => integral_nonneg fun θ => mul_nonneg (hg.nonneg θ) (hH0 _)
  have hwW : ∀ᵐ y, ENNReal.ofReal (w y) = W y := by
    filter_upwards [hi.prod_left_ae] with y hy
    rw [show w y = ∫ θ, g θ * H (y - S5B.om θ) ∂σ from rfl,
      ofReal_integral_eq_lintegral_ofReal hy
        (Eventually.of_forall fun θ => mul_nonneg (hg.nonneg θ) (hH0 _))]
    unfold W S5B.conv σ
    simp only [ENNReal.ofReal_mul (hg.nonneg _)]
  have hW2 : (∫⁻ y, W y ^ 2) < ∞ := by
    have hgfin : (∫⁻ θ, ENNReal.ofReal (g θ) ∂σ) < ∞ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hg1 (Eventually.of_forall hg.nonneg)]
      exact ENNReal.ofReal_lt_top
    have hHfin : (∫⁻ y, ENNReal.ofReal (H y) ^ 2) < ∞ := by
      simp_rw [← ENNReal.ofReal_pow (hH0 _)]
      rw [← ofReal_integral_eq_lintegral_ofReal hH2 (Eventually.of_forall fun _ => by positivity)]
      exact ENNReal.ofReal_lt_top
    have h := S5B.conv_bound (F := fun θ => ENNReal.ofReal (g θ))
      (H := fun y => ENNReal.ofReal (H y)) (ENNReal.measurable_ofReal.comp hg.meas)
      (fun θ => congrArg ENNReal.ofReal (hg.per θ))
      (fun θ => congrArg ENNReal.ofReal (hg.anti θ)) hgfin.ne
      (ENNReal.measurable_ofReal.comp hHm) (fun y hy => by simp [hHs y hy])
    have hf : 4 * (∫⁻ y, W y ^ 2) < ∞ :=
      lt_of_le_of_lt h (ENNReal.mul_lt_top
        (ENNReal.mul_lt_top (by norm_num) (ENNReal.pow_lt_top hgfin)) hHfin)
    rcases ENNReal.mul_lt_top_iff.mp hf with h | h | h
    · exact h.2
    · norm_num at h
    · simp [h]
  have hw2 : MemLp w 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm hw1.aestronglyMeasurable).mpr
    simp only [Real.norm_eq_abs, sq_abs]
    refine ⟨hw1.aestronglyMeasurable.pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => by positivity)]
    rw [lintegral_congr_ae (hwW.mono fun y hy => by
      change ENNReal.ofReal (w y ^ 2) = W y ^ 2
      rw [ENNReal.ofReal_pow (hw0 y), hy])]
    exact hW2
  obtain ⟨hν1, hνF⟩ := ν_fourier hg hν
  have hiProd : Integrable (fun y => ν y * w y) := by
    refine (((hν.memLp.integrable_sq.add hw2.integrable_sq).div_const 2).mono'
      (hν.meas.aestronglyMeasurable.mul hw1.aestronglyMeasurable) (Eventually.of_forall fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hν.nonneg y) (hw0 y))]
    change ν y * w y ≤ (ν y ^ 2 + w y ^ 2) / 2
    nlinarith [sq_nonneg (ν y - w y)]
  calc
    _ = ENNReal.ofReal (∫ y, ν y * w y) := by
      rw [ofReal_integral_eq_lintegral_ofReal hiProd
        (Eventually.of_forall fun y => mul_nonneg (hν.nonneg y) (hw0 y))]
      exact lintegral_congr_ae (hwW.mono fun y hy => by
        change ENNReal.ofReal (ν y) * W y = ENNReal.ofReal (ν y * w y)
        rw [ENNReal.ofReal_mul (hν.nonneg y), hy])
    _ = _ := by
      rw [hP _ _ hν1 hν.memLp hw1 hw2]
      congr 2
      apply integral_congr_ae
      refine Eventually.of_forall fun x => ?_
      dsimp only
      rw [hνF x, conv_fourier hg.meas hg1 hHm hHi, E_toC hg.memLp hg.per hg.anti]
      change (conj ((S2P.Ec g x : ℂ) ^ 3) *
        ((S2P.Ec g x : ℂ) * S2HF.hhat g x)).re = _
      rw [map_pow, Complex.conj_ofReal, ← mul_assoc, ← pow_succ]
      simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]

end

end SteinTomas.S6
