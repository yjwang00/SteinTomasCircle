import Mathlib
import SteinTomasCircle.Section5.SecondVariation

namespace SteinTomas.S6

open Real MeasureTheory Set Function Filter Topology
open scoped ENNReal RealInnerProductSpace

noncomputable section

/-- A nonnegative, antipodally symmetric representative on the circle. -/
structure Adm (g : ℝ → ℝ) : Prop where
  meas : Measurable g
  nonneg : ∀ θ, 0 ≤ g θ
  per : Periodic g (2 * π)
  anti : ∀ θ, g (θ + π) = g θ
  memLp : MemLp g 2 σ

lemma isFin : IsFiniteMeasure σ := isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne

attribute [local instance] isFin

/-- A measurable periodic representative of an angular function. -/
theorem periodic_representative {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F]
    [BorelSpace F] {f : ℝ → F} (hf : AEStronglyMeasurable f σ) :
    ∃ g : ℝ → F, Measurable g ∧ Periodic g (2 * π) ∧ g =ᵐ[σ] f := by
  let r := toIocMod (show 0 < 2 * π by positivity) 0
  have hr : Measurable r := by
    have hd : ∀ x, toIocDiv (show 0 < 2 * π by positivity) 0 x = ⌈x / (2 * π)⌉ - 1 := by
      intro x
      apply toIocDiv_eq_of_sub_zsmul_mem_Ioc
      have hL := Int.ceil_lt_add_one (x / (2 * π))
      have hU := Int.le_ceil (x / (2 * π))
      have hp : 0 < 2 * π := by positivity
      constructor
      · simp only [zsmul_eq_mul, Int.cast_sub, Int.cast_one]
        have h : (⌈x / (2 * π)⌉ : ℝ) - 1 < x / (2 * π) := by linarith
        linarith [(lt_div_iff₀ hp).mp h]
      · simp only [zero_add, zsmul_eq_mul, Int.cast_sub, Int.cast_one]
        linarith [(div_le_iff₀ hp).mp hU]
    change Measurable (toIocMod _ 0)
    unfold toIocMod
    simp_rw [hd, zsmul_eq_mul, Int.cast_sub, Int.cast_one]
    have hcast : Measurable (fun n : ℤ => (n : ℝ)) := measurable_of_countable _
    exact measurable_id.sub (((hcast.comp (measurable_id.div_const _).ceil).sub_const _).mul_const _)
  refine ⟨hf.mk f ∘ r, hf.stronglyMeasurable_mk.measurable.comp hr,
    (toIocMod_periodic (show 0 < 2 * π by positivity) 0).comp _, ?_⟩
  have hi : ∀ᵐ x ∂σ, x ∈ Ioc 0 (2 * π) := ae_restrict_mem measurableSet_Ioc
  filter_upwards [hi, hf.ae_eq_mk] with x hx he
  have hx' : r x = x := (toIocMod_eq_self _).mpr (by simpa only [zero_add] using hx)
  simpa only [Function.comp_apply, hx'] using he.symm

lemma Ec_congr_ae {f g : ℝ → ℝ} (h : f =ᵐ[σ] g) : S2P.Ec f = S2P.Ec g := by
  funext x
  rw [S5C.Ec_set, S5C.Ec_set]
  apply integral_congr_ae
  exact h.mono fun θ ht => by simpa only [ht]

lemma E_congr_ae {f g : ℝ → ℂ} (h : f =ᵐ[σ] g) : E f = E g := by
  funext x
  apply integral_congr_ae
  exact h.mono fun θ ht => by simpa only [ht]

/-- The complex extension is real on real antipodal data. -/
lemma E_toC {f : ℝ → ℝ} (hf : MemLp f 2 σ) (hp : Periodic f (2 * π))
    (ha : ∀ θ, f (θ + π) = f θ) (x : ℝ × ℝ) : E (toC f) x = (S2P.Ec f x : ℂ) := by
  rw [← S5A.ek_zero hf hp ha]
  simp only [S2HF.Ek, S2HF.uf, S2HF.ex, E, toC, σ, dotθ, zero_mul,
    Complex.ofReal_zero, Complex.exp_zero, one_mul, Complex.ofReal_neg]

lemma ext6_toC {f : ℝ → ℝ} (hf : MemLp f 2 σ) (hp : Periodic f (2 * π))
    (ha : ∀ θ, f (θ + π) = f θ) (hi : Integrable (fun x => S2P.Ec f x ^ 6)) :
    ext6 (toC f) = ENNReal.ofReal (∫ x, S2P.Ec f x ^ 6) := by
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun x => by positivity)]
  unfold ext6
  apply lintegral_congr
  intro x
  rw [E_toC hf hp ha, ← ofReal_norm_eq_enorm, Complex.norm_real,
    ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, pow_abs]
  · rw [abs_of_nonneg (by positivity)]

lemma integral_sq_ae_zero {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} (hi : Integrable (fun x => f x ^ 2) μ)
    (h : ∫ x, f x ^ 2 ∂μ = 0) : f =ᵐ[μ] 0 := by
  filter_upwards [(integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f x)) hi).mp h] with x hx
  simpa using hx

lemma int_mul2 {g h : ℝ → ℝ} (hg : MemLp g 2 σ) (hh : MemLp h 2 σ) :
    Integrable (fun θ => g θ * h θ) σ := by
  refine Integrable.mono' ((hg.integrable_sq.add hh.integrable_sq).div_const 2)
    (hg.aestronglyMeasurable.mul hh.aestronglyMeasurable) (Eventually.of_forall fun θ => ?_)
  change ‖g θ * h θ‖ ≤ (g θ ^ 2 + h θ ^ 2) / 2
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|g θ| - |h θ|), sq_abs (g θ), sq_abs (h θ)]

lemma memLp_shift_pi {f : ℝ → ℝ} (hfm : Measurable f) (hf : MemLp f 2 σ)
    (hp : Periodic f (2 * π)) : MemLp (fun θ => f (θ + π)) 2 σ := by
  have h2 : 0 ≤ 2 * π := by positivity
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le h2).2 hf.integrable_sq
  have hp2 : Periodic (fun θ => f θ ^ 2) (2 * π) := fun θ => by simp only [hp θ]
  have hshift := (hp2.intervalIntegrable (by positivity)
    (show IntervalIntegrable (fun θ => f θ ^ 2) volume 0 (0 + 2 * π) by simpa only [zero_add] using hi)
    π (2 * π + π)).comp_add_right π
  rw [sub_self, add_sub_cancel_right] at hshift
  have hm := (hfm.comp (measurable_id.add_const π)).aestronglyMeasurable (μ := σ)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  simpa only [Real.norm_eq_abs, sq_abs, Function.comp_apply, id_eq, σ, IntegrableOn] using
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2).mp hshift

/-- A bounded sequence in real L² has a subsequence converging against all L² tests. -/
theorem weak_subsequence {u : ℕ → ℝ → ℝ} (hu : ∀ j, MemLp (u j) 2 σ)
    (hB : ∀ j, ∫ θ, u j θ ^ 2 ∂σ = 1) :
    ∃ (φ : ℕ → ℕ) (f : ℝ → ℝ), StrictMono φ ∧ MemLp f 2 σ ∧
      ∀ g, MemLp g 2 σ → Tendsto (fun j => ∫ θ, u (φ j) θ * g θ ∂σ) atTop
        (𝓝 (∫ θ, f θ * g θ ∂σ)) := by
  let H := Lp ℝ 2 σ
  haveI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  haveI : TopologicalSpace.SeparableSpace H := by dsimp [H]; infer_instance
  let U (j : ℕ) : H := (hu j).toLp (u j)
  let V (j : ℕ) : WeakDual ℝ H := (InnerProductSpace.toDual ℝ H (U j)).toWeakDual
  have hU : ∀ j, ‖U j‖ = 1 := by
    intro j
    have h := real_inner_self_eq_norm_sq (U j)
    rw [L2.inner_def] at h
    have hi : (∫ θ, inner ℝ (U j θ) (U j θ) ∂σ) = 1 := by
      rw [← hB j]
      apply integral_congr_ae
      filter_upwards [(hu j).coeFn_toLp] with θ hθ
      change inner ℝ (U j θ) (U j θ) = u j θ ^ 2
      rw [hθ, Real.inner_apply, sq]
    rw [hi] at h
    nlinarith [norm_nonneg (U j)]
  obtain ⟨v, -, φ, hφ, hv⟩ :=
    (WeakDual.isSeqCompact_closedBall ℝ H 0 1).subseq_of_frequently_in (x := V)
      ((Eventually.of_forall fun j => by
        change (V j).toStrongDual ∈ Metric.closedBall 0 1
        rw [Metric.mem_closedBall, dist_zero_right, StrongDual.toStrongDual_toWeakDual,
          LinearIsometryEquiv.norm_map, hU]).frequently)
  let f : H := (InnerProductSpace.toDual ℝ H).symm v.toStrongDual
  refine ⟨φ, f, hφ, Lp.memLp f, fun g hg => ?_⟩
  let G : H := hg.toLp g
  have ht := ((WeakDual.eval_continuous G).tendsto v).comp hv
  have hseq : (fun j => V (φ j) G) = fun j => ∫ θ, u (φ j) θ * g θ ∂σ := by
    funext j
    rw [show V (φ j) G = inner ℝ (U (φ j)) G from rfl, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hu (φ j)).coeFn_toLp, hg.coeFn_toLp] with θ h1 h2
    change inner ℝ (U (φ j) θ) (G θ) = u (φ j) θ * g θ
    rw [h1, h2, Real.inner_apply]
  have hlim : v G = ∫ θ, f θ * g θ ∂σ := by
    rw [show v G = inner ℝ f G from (InnerProductSpace.toDual_symm_apply).symm,
      L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with θ hθ
    change inner ℝ (f θ) (G θ) = f θ * g θ
    rw [hθ, Real.inner_apply]
  change Tendsto (fun j => V (φ j) G) atTop (𝓝 (v G)) at ht
  rwa [hseq, hlim] at ht

/-- A weak limit of admissible functions has an admissible representative. -/
theorem admissible_weak_subsequence {u : ℕ → ℝ → ℝ} (hu : ∀ j, Adm (u j))
    (hB : ∀ j, ∫ θ, u j θ ^ 2 ∂σ = 1) :
    ∃ (φ : ℕ → ℕ) (f : ℝ → ℝ), StrictMono φ ∧ Adm f ∧
      ∀ g, MemLp g 2 σ → Tendsto (fun j => ∫ θ, u (φ j) θ * g θ ∂σ) atTop
        (𝓝 (∫ θ, f θ * g θ ∂σ)) := by
  obtain ⟨φ, f, hφ, hf, hweak⟩ := weak_subsequence (fun j => (hu j).memLp) hB
  obtain ⟨z, hzm, hzp, hzf⟩ := periodic_representative hf.aestronglyMeasurable
  have hz := hf.ae_eq hzf.symm
  have hwz : ∀ g, MemLp g 2 σ → Tendsto (fun j => ∫ θ, u (φ j) θ * g θ ∂σ) atTop
      (𝓝 (∫ θ, z θ * g θ ∂σ)) := fun g hg => by
    rw [integral_congr_ae (hzf.mono fun θ h => by rw [h])]
    exact hweak g hg
  -- Test the weak limit against its negative part.
  let n : ℝ → ℝ := fun θ => min (z θ) 0
  have hnm : Measurable n := hzm.min measurable_const
  have hn : MemLp n 2 σ := hz.of_le hnm.aestronglyMeasurable
    (Eventually.of_forall fun θ => by
      change |min (z θ) 0| ≤ |z θ|
      rcases le_total (z θ) 0 with h | h <;> simp [min_eq_left, min_eq_right, h, abs_nonneg])
  have hni : (∫ θ, n θ ^ 2 ∂σ) ≤ 0 := by
    have ht := le_of_tendsto' (hwz n hn) (fun j => integral_nonpos fun θ =>
      mul_nonpos_of_nonneg_of_nonpos ((hu (φ j)).nonneg θ) (min_le_right _ _))
    rwa [integral_congr_ae (Eventually.of_forall fun θ => show z θ * n θ = n θ ^ 2 by
      dsimp only [n]
      rcases le_total (z θ) 0 with h | h <;> simp [min_eq_left, min_eq_right, h, sq])] at ht
  have hn0 := integral_sq_ae_zero hn.integrable_sq
    (le_antisymm hni (integral_nonneg fun θ => sq_nonneg (n θ)))
  let w : ℝ → ℝ := fun θ => max (z θ) 0
  have hwm : Measurable w := hzm.max measurable_const
  have hwp : Periodic w (2 * π) := fun θ => by simp only [w, hzp θ]
  have hw0 : ∀ θ, 0 ≤ w θ := fun θ => le_max_right _ _
  have hwz' : w =ᵐ[σ] z := hn0.mono fun θ h => by
    change min (z θ) 0 = 0 at h
    exact max_eq_left (min_eq_right_iff.mp h)
  have hw := hz.ae_eq hwz'.symm
  have hww : ∀ g, MemLp g 2 σ → Tendsto (fun j => ∫ θ, u (φ j) θ * g θ ∂σ) atTop
      (𝓝 (∫ θ, w θ * g θ ∂σ)) := fun g hg => by
    rw [integral_congr_ae (hwz'.mono fun θ h => by rw [h])]
    exact hwz g hg
  -- The half-turn preserves the pairing with a half-turn of the test function.
  let d : ℝ → ℝ := fun θ => w θ - w (θ + π)
  have hdm : Measurable d := hwm.sub (hwm.comp (measurable_id.add_const π))
  have hdp : Periodic d (2 * π) := fun θ => by
    dsimp only [d]
    rw [hwp θ, add_right_comm θ (2 * π) π, hwp (θ + π)]
  have hd : MemLp d 2 σ := hw.sub (memLp_shift_pi hwm hw hwp)
  have hds := memLp_shift_pi hdm hd hdp
  have hshift (g : ℝ → ℝ) (hgp : Periodic g (2 * π)) :
      (∫ θ, g θ * d (θ + π) ∂σ) = ∫ θ, g (θ + π) * d θ ∂σ := by
    have he := S4M.int_shift_pi (g := fun θ => g θ * d (θ + π))
      (fun θ => by dsimp only; rw [hgp θ, add_right_comm θ (2 * π) π, hdp (θ + π)])
    have he' : ∀ θ, g (θ + π) * d (θ + π + π) = g (θ + π) * d θ := fun θ => by
      rw [show θ + π + π = θ + 2 * π by ring, hdp θ]
    simpa only [he', σ] using he.symm
  have hpair : (∫ θ, w θ * d θ ∂σ) = ∫ θ, w (θ + π) * d θ ∂σ := by
    have ht := hww _ hds
    simp_rw [hshift _ (hu _).per, (hu _).anti, hshift w hwp] at ht
    exact tendsto_nhds_unique (hww d hd) ht
  have hd0 : ∫ θ, d θ ^ 2 ∂σ = 0 := by
    calc
      _ = ∫ θ, w θ * d θ - w (θ + π) * d θ ∂σ :=
        integral_congr_ae (Eventually.of_forall fun θ => by dsimp only [d]; ring)
      _ = 0 := by
        rw [integral_sub (int_mul2 hw hd) (int_mul2 (memLp_shift_pi hwm hw hwp) hd),
          hpair, sub_self]
  let v : ℝ → ℝ := fun θ => (w θ + w (θ + π)) / 2
  have hvw : v =ᵐ[σ] w := (integral_sq_ae_zero hd.integrable_sq hd0).mono fun θ h => by
    change w θ - w (θ + π) = 0 at h
    dsimp only [v]
    linarith
  have hv : Adm v := by
    refine ⟨(hwm.add (hwm.comp (measurable_id.add_const π))).div_const _,
      fun θ => div_nonneg (add_nonneg (hw0 θ) (hw0 (θ + π))) (by norm_num),
      ?_, ?_, hw.ae_eq hvw.symm⟩
    · intro θ
      dsimp only [v]
      rw [hwp θ, add_right_comm θ (2 * π) π, hwp (θ + π)]
    · intro θ
      dsimp only [v]
      rw [show θ + π + π = θ + 2 * π by ring, hwp θ, add_comm]
  refine ⟨φ, v, hφ, hv, fun g hg => ?_⟩
  rw [integral_congr_ae (hvw.mono fun θ h => by rw [h])]
  exact hww g hg

end

end SteinTomas.S6
