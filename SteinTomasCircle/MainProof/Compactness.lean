import SteinTomasCircle.Section5.SmallMean
import SteinTomasCircle.MainProof.Plancherel
import SteinTomasCircle.MainProof.Variation

/-!
# Sharp extension on the circle

The first theorem constructs the best constant and a maximizing sequence, takes a weakly
convergent subsequence, and uses the mean estimates to evaluate the best constant.
The normalized constant and every nonzero complex constant are maximizers.
The second theorem supplies the L¹ remainder estimate on all of L².

The classical extension bound, Brezis–Lieb, CFOT17 symmetrization and magic identity,
Plancherel, the classical Fourier series of |sin|, and the special-function inputs
are explicit hypotheses.
-/

namespace SteinTomas.S6

open Real MeasureTheory Set Function Filter Topology
open scoped ENNReal

noncomputable section

local notation "μI" => (volume.restrict (Ioc (0 : ℝ) (2 * π)))

/-- ρ = σ*³ (BSWZ12, Becker25) -/
structure RhoData (ρ : ℝ × ℝ → ℝ) (ρr : ℝ → ℝ) : Prop where
  meas : Measurable ρ
  nonneg : ∀ y, 0 ≤ ρ y
  dens : ∀ Ψ : ℝ × ℝ → ℝ≥0∞, Measurable Ψ →
    ∫⁻ y, Ψ y * ENNReal.ofReal (ρ y) = ∫⁻ p, Ψ (S4R.ss p) ∂S4R.M3
  rad : ∀ y, ρ y = ρr (Real.sqrt (nsq y))
  r0 : ∀ r, 0 ≤ ρr r
  formula : ∀ r, 1 < r → r < 3 →
    ρr r = 4 / Real.sqrt r * S2R.Kl ((r + 1) ^ 3 * (3 - r) / (16 * r))

/-- Literature input on Bessel functions (DLMF, CFOT17 Table 1, OST17) -/
structure BesselLit (Jb : ℕ → ℝ → ℝ) : Prop where
  kern : S2E.BesselKernel Jb
  cont : ∀ n, Continuous (Jb n)
  zero : volume {r : ℝ | 0 < r ∧ Jb 0 r = 0} = 0
  ser : Lemma21.SeriesHyp (Jb 0) (Jb 1)
  dlmf : ∀ (k : ℕ) (r : ℝ), 0 ≤ r → |Jb k r| ≤ (r / 2) ^ (2 * k) / ((2 * k).factorial : ℝ)
  int : ∀ n, IntegrableOn (fun r => Jb 0 r ^ 4 * Jb n r ^ 2 * r) (Ioi 0)
  lit : Section2.AlphaLit (S2Q.alpha Jb)

/-- The Bessel family indexed by half the order. -/
def evenBessel (n : ℕ) (r : ℝ) : ℝ := J (2 * (n : ℤ)) r

lemma alpha_evenBessel (n : ℕ) : S2Q.alpha evenBessel n = α n := rfl

/-- The sharp sixth-power constant in the arc-length normalization. -/
def M0 : ℝ := (2 * π) ^ 4 * α 0

/-- Classical Stein–Tomas boundedness, restricted to the real cosine transform. -/
def ClassicalSteinTomas : Prop :=
  ∃ C : ℝ, ∀ f : ℝ → ℝ, MemLp f 2 σ →
    Integrable (fun x => S2P.Ec f x ^ 6) ∧ energy f ≤ C * sqNorm f ^ 3

/-- Brezis–Lieb for p = 6, with measurability of the functions before taking powers. -/
def BrezisLieb6 : Prop :=
  ∀ (u : ℕ → ℝ × ℝ → ℝ) (v : ℝ × ℝ → ℝ),
    (∀ j, AEStronglyMeasurable (u j) volume) → AEStronglyMeasurable v volume →
    (∀ j, Integrable (fun x => u j x ^ 6)) → Integrable (fun x => v x ^ 6) →
    (∃ C, ∀ j, ∫ x, u j x ^ 6 ≤ C) →
    (∀ᵐ x ∂volume, Tendsto (fun j => u j x) atTop (𝓝 (v x))) →
    Tendsto (fun j => (∫ x, u j x ^ 6) - (∫ x, v x ^ 6) -
      ∫ x, (u j x - v x) ^ 6) atTop (𝓝 0)

/-- CFOT17, §1 Steps 1–2 in angular coordinates. -/
def CFOTReduction : Prop :=
  ∀ F : ℝ → ℂ, MemLp F 2 σ → Measurable F → Periodic F (2 * π) →
    ext6 F ≤ ENNReal.ofReal (energy (S4M.sharp (fun θ => ‖F θ‖)))

lemma e0_adm : Adm S2P.e0 := by
  haveI : IsFiniteMeasure σ := isFin
  exact ⟨measurable_const, fun _ => by unfold S2P.e0; positivity,
    fun _ => rfl, fun _ => rfl, memLp_const _⟩

lemma pow6_nonneg (y : ℝ) : 0 ≤ y ^ 6 := by positivity

/-- Real-number core of the compactness argument (the Brezis–Lieb step in the proof of Theorem 1.1) -/
theorem bl_limit {M s a : ℝ} {A b t ε : ℕ → ℝ} (hM : 0 < M) (hs : 0 < s)
    (hA : Tendsto A atTop (𝓝 M)) (ht : Tendsto t atTop (𝓝 (1 - s))) (ht0 : ∀ j, 0 ≤ t j)
    (hBL : ∀ j, A j = a + b j + ε j) (hε : Tendsto ε atTop (𝓝 0))
    (ha : a ≤ M * s ^ 3) (hb : ∀ j, b j ≤ M * t j ^ 3) (hb0 : ∀ j, 0 ≤ b j) :
    s = 1 ∧ a = M ∧ Tendsto t atTop (𝓝 0) := by
  have h1s : 0 ≤ 1 - s := ge_of_tendsto' ht ht0
  have hR : Tendsto (fun j => M * s ^ 3 + M * t j ^ 3 + ε j) atTop
      (𝓝 (M * s ^ 3 + M * (1 - s) ^ 3 + 0)) :=
    (tendsto_const_nhds.add ((ht.pow 3).const_mul M)).add hε
  have key : M ≤ M * s ^ 3 + M * (1 - s) ^ 3 + 0 :=
    le_of_tendsto_of_tendsto' hA hR (fun j => by rw [hBL j]; linarith [hb j])
  have e : M * s ^ 3 + M * (1 - s) ^ 3 + 0 = M - 3 * (M * s * (1 - s)) := by ring
  rw [e] at key
  have hs1 : s = 1 := by
    by_contra hne
    have : 0 < 1 - s := lt_of_le_of_ne h1s (fun h => hne (by linarith))
    have : 0 < M * s * (1 - s) := mul_pos (mul_pos hM hs) this
    linarith
  rw [hs1, sub_self] at ht
  have hbt : Tendsto b atTop (𝓝 0) := by
    have hu : Tendsto (fun j => M * t j ^ 3) atTop (𝓝 (M * 0 ^ 3)) := (ht.pow 3).const_mul M
    rw [show M * (0 : ℝ) ^ 3 = 0 by ring] at hu
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu hb0 hb
  have hconst : (fun j => A j - b j - ε j) = fun _ => a := funext fun j => by rw [hBL j]; ring
  have hlim : Tendsto (fun j => A j - b j - ε j) atTop (𝓝 (M - 0 - 0)) := (hA.sub hbt).sub hε
  rw [hconst, sub_zero, sub_zero] at hlim
  exact ⟨hs1, tendsto_nhds_unique tendsto_const_nhds hlim, ht⟩

lemma int_const (c : ℝ) : ∫ θ in Ioc 0 (2 * π), c = 2 * π * c := by
  rw [← intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_const,
    smul_eq_mul, sub_zero]

lemma Mconc_lt : Mconc < 404 * π ^ 4 / 75 := by
  unfold Mconc
  have hp := Real.pi_gt_three
  have h3 : (1.7 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs : 0 < Real.sqrt 3 := by positivity
  have hπ3 : 0 < π ^ 3 := by positivity
  rw [div_lt_iff₀ hs]
  nlinarith [mul_lt_mul_of_pos_left h3 (show (0 : ℝ) < 404 * π ^ 4 / 75 by positivity),
    mul_lt_mul_of_pos_left hp hπ3]

variable {Jb : ℕ → ℝ → ℝ} {ρ : ℝ × ℝ → ℝ} {ρr : ℝ → ℝ} {M : ℝ}

set_option maxHeartbeats 2000000 in
/-- **Theorem 1.1 (real form)**: the weak limit of a maximizing sequence is a normalized maximizer, hence constant, and M = (2π)⁴α₀ -/
theorem thm_main_real (hsin : S2C.SinSeries) (hJ : BesselLit Jb) (hρ : RhoData ρ ρr)
    (hST : ∀ h : ℝ → ℝ, MemLp h 2 σ → Integrable (fun x => S2P.Ec h x ^ 6))
    (hMall : ∀ h : ℝ → ℝ, MemLp h 2 σ → Periodic h (2 * π) →
      (∀ θ, h (θ + π) = h θ) → energy h ≤ M * sqNorm h ^ 3)
    (hnu : ∀ g, Adm g → ∃ ν, NuData g ν) (hP : PlanePlancherel)
    (hBLlem : BrezisLieb6)
    {fs : ℕ → ℝ → ℝ} (hfs : ∀ j, Adm (fs j)) (hfs1 : ∀ j, sqNorm (fs j) = 1)
    (hA : Tendsto (fun j => energy (fs j)) atTop (𝓝 M))
    {f : ℝ → ℝ} (hf : Adm f)
    (hweak : ∀ g, MemLp g 2 σ → Tendsto (fun j => ∫ θ, fs j θ * g θ ∂σ) atTop
      (𝓝 (∫ θ, f θ * g θ ∂σ))) :
    M = (2 * π) ^ 4 * S2Q.alpha Jb 0 ∧ sqNorm f = 1 ∧ energy f = M ∧
      Tendsto (fun j => sqNorm (fun θ => fs j θ - f θ)) atTop (𝓝 0) := by
  have hp := pi_pos
  haveI := isFin
  -- e₀
  have he0L : MemLp S2P.e0 2 μI := memLp_const _
  have he0v : ∀ θ, S2P.e0 θ ^ 2 = 1 / (2 * π) := fun θ => by
    simp only [S2P.e0]; rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
  have he0sq : ∫ θ in Ioc 0 (2 * π), S2P.e0 θ ^ 2 = 1 := by
    simp_rw [he0v]; rw [int_const]; field_simp
  have hext : ∫ x, S2P.Ec S2P.e0 x ^ 6 ≤ M := by
    have := hMall S2P.e0 he0L (fun θ => rfl) (fun θ => rfl)
    rwa [show sqNorm S2P.e0 = 1 from he0sq, one_pow, mul_one] at this
  have he0E := S2W.energy_e0 hJ.kern (hST _ he0L)
  have hα := (Section2.bessel_global hJ.lit).1
  have hM0 : 404 * π ^ 4 / 75 < M := by
    have h1 : (2 * π) ^ 4 * (101 / 300) < (2 * π) ^ 4 * S2Q.alpha Jb 0 :=
      mul_lt_mul_of_pos_left hα (by positivity)
    have h2 : 404 * π ^ 4 / 75 = (2 * π) ^ 4 * (101 / 300) := by ring
    linarith
  have hMc : Mconc < M := lt_trans Mconc_lt hM0
  have hMpos : 0 < M := lt_trans (by positivity) hM0
  -- L¹ remainder (eq:L1-remainder-sym) for each fⱼ
  have hL1 : ∀ j, ∫ x, S2P.Ec (fs j) x ^ 6
      ≤ Mconc + 45 * π * (∫ θ in Ioc 0 (2 * π), fs j θ) ^ 2 := by
    intro j
    obtain ⟨ν, hν⟩ := hnu (fs j) (hfs j)
    have := S4M.L1_remainder_sym hsin (hfs j).meas (hfs j).nonneg (hfs j).per (hfs j).anti
      (hfs j).memLp hν.meas hν.nonneg hν.dens (by rw [hν.l2]; exact ENNReal.ofReal_lt_top)
      hρ.meas hρ.nonneg hρ.dens hρ.rad hρ.r0 hρ.formula hν.mint hν.magic
    rw [show (∫ θ in Ioc 0 (2 * π), fs j θ ^ 2) = 1 from hfs1 j] at this
    simp only [one_pow, mul_one] at this
    exact this
  -- weak limit
  have hcos : ∀ x : ℝ × ℝ, MemLp (fun θ => Real.cos (S5A.dd x θ)) 2 μI := fun x =>
    MemLp.of_bound (Continuous.aestronglyMeasurable (by unfold S5A.dd; fun_prop)) 1
      (Eventually.of_forall fun θ => by rw [Real.norm_eq_abs]; exact abs_cos_le_one _)
  have hLlim : Tendsto (fun j => ∫ θ in Ioc 0 (2 * π), fs j θ) atTop
      (𝓝 (∫ θ in Ioc 0 (2 * π), f θ)) := by
    have := hweak _ (memLp_const (1 : ℝ))
    simp only [mul_one] at this
    exact this
  have hLsq : (M - Mconc) / (45 * π) ≤ (∫ θ in Ioc 0 (2 * π), f θ) ^ 2 :=
    le_of_tendsto_of_tendsto' (((show Tendsto (fun j => ∫ x, S2P.Ec (fs j) x ^ 6) atTop (𝓝 M) from hA).sub_const Mconc).div_const (45 * π)) (hLlim.pow 2)
      (fun j => by rw [div_le_iff₀ (by positivity)]; nlinarith [hL1 j])
  have hpos : 0 < (∫ θ in Ioc 0 (2 * π), f θ) ^ 2 :=
    lt_of_lt_of_le (div_pos (by linarith) (by positivity)) hLsq
  have hs : 0 < ∫ θ in Ioc 0 (2 * π), f θ ^ 2 := by
    by_contra hs
    push_neg at hs
    have hs0 : ∫ θ in Ioc 0 (2 * π), f θ ^ 2 = 0 :=
      le_antisymm hs (integral_nonneg fun _ => sq_nonneg _)
    have hae := (integral_eq_zero_iff_of_nonneg (fun θ => sq_nonneg (f θ))
      hf.memLp.integrable_sq).1 hs0
    have hf0 : ∫ θ in Ioc 0 (2 * π), f θ = 0 :=
      integral_eq_zero_of_ae (hae.mono fun θ h => by simpa using h)
    rw [hf0] at hpos
    simp at hpos
  -- ‖fⱼ − f‖² → 1 − ‖f‖²
  have htj : ∀ j, ∫ θ in Ioc 0 (2 * π), (fs j θ - f θ) ^ 2
      = 1 - 2 * (∫ θ in Ioc 0 (2 * π), fs j θ * f θ) + ∫ θ in Ioc 0 (2 * π), f θ ^ 2 := by
    intro j
    have hA2 : Integrable (fun θ => fs j θ ^ 2) μI := (hfs j).memLp.integrable_sq
    have hAB : Integrable (fun θ => fs j θ * f θ) μI := int_mul2 (hfs j).memLp hf.memLp
    have hB2 : Integrable (fun θ => f θ ^ 2) μI := hf.memLp.integrable_sq
    have hS : Integrable (fun θ => fs j θ ^ 2 - 2 * (fs j θ * f θ)) μI := hA2.sub (hAB.const_mul 2)
    rw [← show (∫ θ in Ioc 0 (2 * π), fs j θ ^ 2) = 1 from hfs1 j, ← integral_const_mul, ← integral_sub hA2 (hAB.const_mul 2),
      ← integral_add hS hB2]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    beta_reduce
    ring
  have hwf : Tendsto (fun j => ∫ θ in Ioc 0 (2 * π), fs j θ * f θ) atTop
      (𝓝 (∫ θ in Ioc 0 (2 * π), f θ ^ 2)) := by
    have := hweak f hf.memLp
    simp only [← sq] at this
    exact this
  have htlim : Tendsto (fun j => ∫ θ in Ioc 0 (2 * π), (fs j θ - f θ) ^ 2) atTop
      (𝓝 (1 - ∫ θ in Ioc 0 (2 * π), f θ ^ 2)) := by
    rw [show (fun j => ∫ θ in Ioc 0 (2 * π), (fs j θ - f θ) ^ 2) = fun j =>
      1 - 2 * (∫ θ in Ioc 0 (2 * π), fs j θ * f θ) + ∫ θ in Ioc 0 (2 * π), f θ ^ 2 from funext htj]
    have := ((hwf.const_mul 2).const_sub 1).add_const (∫ θ in Ioc 0 (2 * π), f θ ^ 2)
    convert this using 2
    ring
  -- Brezis–Lieb
  have hptw : ∀ x, Tendsto (fun j => S2P.Ec (fs j) x) atTop (𝓝 (S2P.Ec f x)) := fun x => by
    simp only [S5C.Ec_set]; exact hweak _ (hcos x)
  have hbl := hBLlem (fun j => S2P.Ec (fs j)) (S2P.Ec f)
    (fun j => (S5C.Ec_cont (hfs j).memLp).aestronglyMeasurable)
    (S5C.Ec_cont hf.memLp).aestronglyMeasurable
    (fun j => hST _ (hfs j).memLp) (hST _ hf.memLp) ⟨M, fun j => by
      have := hMall _ (hfs j).memLp (hfs j).per (hfs j).anti
      rwa [hfs1 j, one_pow, mul_one] at this⟩ (Eventually.of_forall hptw)
  have hlin : ∀ j x, S2P.Ec (fs j) x - S2P.Ec f x = S2P.Ec (fun θ => fs j θ - f θ) x := by
    intro j x
    have hdC : Continuous fun θ => Real.cos (S5A.dd x θ) := by unfold S5A.dd; fun_prop
    rw [S5C.Ec_set, S5C.Ec_set, S5C.Ec_set,
      ← integral_sub (S5C.imul ((hfs j).memLp.integrable one_le_two) hdC (fun t => abs_cos_le_one _))
        (S5C.imul (hf.memLp.integrable one_le_two) hdC (fun t => abs_cos_le_one _))]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    beta_reduce
    ring
  beta_reduce at hbl
  simp only [hlin] at hbl
  have hdiff : ∀ j, ∫ x, S2P.Ec (fun θ => fs j θ - f θ) x ^ 6
      ≤ M * (∫ θ in Ioc 0 (2 * π), (fs j θ - f θ) ^ 2) ^ 3 := by
    intro j
    have := hMall (fun θ => fs j θ - f θ) ((hfs j).memLp.sub hf.memLp)
      (fun θ => by simp only [(hfs j).per θ, hf.per θ])
      (fun θ => by simp only [(hfs j).anti θ, hf.anti θ])
    exact this
  have ha : (∫ x, S2P.Ec f x ^ 6) ≤ M * (∫ θ in Ioc 0 (2 * π), f θ ^ 2) ^ 3 :=
    hMall f hf.memLp hf.per hf.anti
  obtain ⟨hs1, haM, hstrong⟩ := bl_limit (A := fun j => ∫ x, S2P.Ec (fs j) x ^ 6)
    (b := fun j => ∫ x, S2P.Ec (fun θ => fs j θ - f θ) x ^ 6)
    (t := fun j => ∫ θ in Ioc 0 (2 * π), (fs j θ - f θ) ^ 2)
    (ε := fun j => (∫ x, S2P.Ec (fs j) x ^ 6) - (∫ x, S2P.Ec f x ^ 6)
      - ∫ x, S2P.Ec (fun θ => fs j θ - f θ) x ^ 6)
    hMpos hs hA htlim (fun j => integral_nonneg fun _ => sq_nonneg _) (fun j => by ring) hbl ha hdiff
    (fun j => integral_nonneg fun _ => pow6_nonneg _)
  -- f is a normalized nonnegative antipodal maximizer ⇒ constant
  obtain ⟨ν, hν⟩ := hnu f hf
  have ml := maximizer_variations hf hs1 haM hST hMall
  obtain ⟨c, hc⟩ := S5D.maximizer_const hsin hf.meas hf.nonneg hf.per hf.anti hf.memLp hs1
    (by rw [haM]; exact hext) (hST _ he0L) ml.i5 (hST _ hf.memLp) ml.el hJ.kern hJ.cont hJ.zero
    hJ.ser hJ.dlmf hJ.int hJ.lit ml.sv hν.meas hν.nonneg hν.dens hν.l2 (hν.plan hf hP) hρ.meas hρ.nonneg
    hρ.dens hρ.rad hρ.r0 hρ.formula hν.mint hν.magic
  have hne : μI ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioc, ENNReal.ofReal_eq_zero]; linarith
  haveI : (ae μI).NeBot := ae_neBot.2 hne
  obtain ⟨θ0, h1, h2⟩ := (hc.and (Eventually.of_forall hf.nonneg)).exists
  have hc0 : 0 ≤ c := h1 ▸ h2
  have hcsq : 2 * π * c ^ 2 = 1 := by
    rw [← int_const, ← hs1]
    exact integral_congr_ae (hc.mono fun θ h => by simp only [h])
  have hd : (1 / Real.sqrt (2 * π)) ^ 2 = c ^ 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]; field_simp; linarith
  have hcd : c = 1 / Real.sqrt (2 * π) := by
    rw [← Real.sqrt_sq hc0, ← hd, Real.sqrt_sq (by positivity)]
  have hEf : S2P.Ec f = S2P.Ec S2P.e0 := by
    funext x
    rw [S5C.Ec_set, S5C.Ec_set]
    exact integral_congr_ae (hc.mono fun θ h => by simp only [h, hcd, S2P.e0])
  refine ⟨?_, hs1, haM, hstrong⟩
  rw [← haM, hEf, he0E]

/-- ‖F‖_{L²(σ)} = (∫|F|²)^{1/2} -/
lemma L2n_eq {F : ℝ → ℂ} (hF : MemLp F 2 σ) :
    L2n F = ENNReal.ofReal (Real.sqrt (∫ θ in Ioc 0 (2 * π), ‖F θ‖ ^ 2)) := by
  unfold L2n
  rw [hF.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  unfold σ
  congr 1
  rw [Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  norm_num

/-- ‖F‖_{L¹(σ)} = ∫|F| -/
lemma L1n_eq {F : ℝ → ℂ} (hF : MemLp F 2 σ) :
    L1n F = ENNReal.ofReal (∫ θ in Ioc 0 (2 * π), ‖F θ‖) := by
  haveI : IsFiniteMeasure σ := isFin
  have h1 : MemLp F 1 σ := hF.mono_exponent (by norm_num)
  unfold L1n
  rw [h1.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top]
  unfold σ
  simp only [ENNReal.toReal_one, Real.rpow_one, inv_one]

lemma ofReal_sqrt_pow {B : ℝ} (hB : 0 ≤ B) (k : ℕ) :
    ENNReal.ofReal (Real.sqrt B) ^ (2 * k) = ENNReal.ofReal (B ^ k) := by
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), pow_mul, Real.sq_sqrt hB]

/-- f♯ is admissible -/
lemma sharp_adm {a : ℝ → ℝ} (ham : Measurable a) (ha0 : ∀ θ, 0 ≤ a θ)
    (haper : Periodic a (2 * π)) (ha : MemLp a 2 μI) : Adm (S4M.sharp a) := by
  have hp := pi_pos
  have hsm : Measurable (S4M.sharp a) := by
    unfold S4M.sharp
    exact Real.continuous_sqrt.measurable.comp
      (((ham.pow_const 2).add ((ham.comp (measurable_id.add_const π)).pow_const 2)).div_const 2)
  have ha2 : Integrable (fun θ => a θ ^ 2) μI := ha.integrable_sq
  have hi2 := (memLp_shift_pi ham ha haper).integrable_sq
  refine ⟨hsm, fun θ => Real.sqrt_nonneg _, fun θ => ?_, fun θ => ?_, ?_⟩
  · unfold S4M.sharp
    rw [show θ + 2 * π + π = θ + π + 2 * π by ring, haper, haper]
  · unfold S4M.sharp
    rw [show θ + π + π = θ + 2 * π by ring, haper, add_comm (a (θ + π) ^ 2)]
  · refine (memLp_two_iff_integrable_sq hsm.aestronglyMeasurable).2 ?_
    refine ((ha2.add hi2).div_const 2).congr (Eventually.of_forall fun θ => ?_)
    show (a θ ^ 2 + a (θ + π) ^ 2) / 2 = S4M.sharp a θ ^ 2
    unfold S4M.sharp; rw [Real.sq_sqrt (by positivity)]

lemma e0_sqNorm : sqNorm S2P.e0 = 1 := by
  have h : ∀ θ, S2P.e0 θ ^ 2 = 1 / (2 * π) := fun θ => by
    simp only [S2P.e0]
    rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
  unfold sqNorm σ
  simp_rw [h, int_const]
  field_simp

lemma M0_pos (hJ : BesselLit evenBessel) : 0 < M0 := by
  have h := (Section2.bessel_global hJ.lit).1
  rw [alpha_evenBessel] at h
  unfold M0
  exact mul_pos (by positivity) (lt_trans (by norm_num) h)

private lemma reduce_to_adm (hred : CFOTReduction) {F : ℝ → ℂ} (hF : MemLp F 2 σ) :
    ∃ g : ℝ → ℝ, Adm g ∧ sqNorm g = (∫ θ, ‖F θ‖ ^ 2 ∂σ) ∧
      ext6 F ≤ ENNReal.ofReal (energy g) := by
  obtain ⟨G, hGm, hGp, hGF⟩ := periodic_representative hF.aestronglyMeasurable
  have hG := hF.ae_eq hGF.symm
  have hnorm : Periodic (fun θ => ‖G θ‖) (2 * π) := fun θ => congrArg norm (hGp θ)
  have hnorm0 : ∀ θ, 0 ≤ ‖G θ‖ := fun θ => norm_nonneg _
  refine ⟨S4M.sharp (fun θ => ‖G θ‖), sharp_adm hGm.norm hnorm0 hnorm hG.norm, ?_, ?_⟩
  · exact (S4M.sharp_norms hGm.norm hnorm0 hnorm hG.norm).1.trans
      (integral_congr_ae (hGF.mono fun θ h => by simpa only [h]))
  · have h := hred G hG hGm hGp
    simpa only [ext6, E_congr_ae hGF] using h

private lemma adm_upper_bound {M : ℝ} (hM : ∀ g, Adm g → sqNorm g = 1 → energy g ≤ M)
    {g : ℝ → ℝ} (hg : Adm g) : energy g ≤ M * sqNorm g ^ 3 := by
  by_cases hB : sqNorm g = 0
  · have hg0 := integral_sq_ae_zero hg.memLp.integrable_sq hB
    rw [energy, Ec_congr_ae hg0]
    simp [S2P.Ec, hB]
  · let c := (Real.sqrt (sqNorm g))⁻¹
    have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr
      (lt_of_le_of_ne (sqNorm_nonneg _) (Ne.symm hB)))
    have h : c ^ 2 * sqNorm g = 1 := by
      dsimp [c]
      rw [inv_pow, Real.sq_sqrt (sqNorm_nonneg _), inv_mul_cancel₀ hB]
    have hg' : Adm (fun θ => c * g θ) :=
      ⟨hg.meas.const_mul _, fun θ => mul_nonneg hc.le (hg.nonneg θ),
        fun θ => congrArg (c * ·) (hg.per θ), fun θ => congrArg (c * ·) (hg.anti θ),
        hg.memLp.const_mul _⟩
    have hle := hM _ hg' ((sqNorm_const_mul g c).trans h)
    rw [energy_const_mul] at hle
    apply le_of_mul_le_mul_left _ (pow_pos hc 6)
    calc
      c ^ 6 * energy g ≤ M := hle
      _ = c ^ 6 * (M * sqNorm g ^ 3) := by
        rw [show c ^ 6 * (M * sqNorm g ^ 3) = M * (c ^ 2 * sqNorm g) ^ 3 by ring, h]
        simp

private theorem best_constant_real (hsin : S2C.SinSeries) (hJ : BesselLit evenBessel)
    (hρ : RhoData ρ ρr) (hST : ClassicalSteinTomas)
    (hnu : ∀ g, Adm g → ∃ ν, NuData g ν) (hP : PlanePlancherel)
    (hBLlem : BrezisLieb6) (hred : CFOTReduction) :
    ∀ f : ℝ → ℝ, MemLp f 2 σ → Periodic f (2 * π) → (∀ θ, f (θ + π) = f θ) →
      energy f ≤ M0 * sqNorm f ^ 3 := by
  obtain ⟨C, hC⟩ := hST
  have hInt : ∀ f, MemLp f 2 σ → Integrable (fun x => S2P.Ec f x ^ 6) :=
    fun f hf => (hC f hf).1
  let S : Set ℝ := {a | ∃ g : ℝ → ℝ, Adm g ∧ sqNorm g = 1 ∧ energy g = a}
  have hS : S.Nonempty := ⟨energy S2P.e0, S2P.e0, e0_adm, e0_sqNorm, rfl⟩
  have hBd : BddAbove S := by
    refine ⟨C, fun a ha => ?_⟩
    obtain ⟨g, hg, hB, rfl⟩ := ha
    simpa only [hB, one_pow, mul_one] using (hC g hg.memLp).2
  let M := sSup S
  have hUnit : ∀ g, Adm g → sqNorm g = 1 → energy g ≤ M := fun g hg hg1 =>
    le_csSup hBd ⟨g, hg, hg1, rfl⟩
  have hMall : ∀ h : ℝ → ℝ, MemLp h 2 σ → Periodic h (2 * π) →
      (∀ θ, h (θ + π) = h θ) → energy h ≤ M * sqNorm h ^ 3 := by
    intro h hh hp ha
    obtain ⟨g, hg, hgB, hgE⟩ := reduce_to_adm hred (F := toC h) hh.ofReal
    have hB : sqNorm g = sqNorm h := by
      simpa only [toC, Complex.norm_real, Real.norm_eq_abs, sq_abs, sqNorm] using hgB
    have hE : energy h ≤ energy g := by
      rw [ext6_toC hh hp ha (hInt h hh)] at hgE
      exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun x => pow6_nonneg _)).mp hgE
    exact hE.trans (hB ▸ adm_upper_bound hUnit hg)
  obtain ⟨a, -, hlim, ha⟩ := exists_seq_tendsto_sSup hS hBd
  have ha' : ∀ j, ∃ g : ℝ → ℝ, Adm g ∧ sqNorm g = 1 ∧ energy g = a j := ha
  choose u hu huB huE using ha'
  have huLim : Tendsto (fun j => energy (u j)) atTop (𝓝 M) := by
    simpa only [huE] using hlim
  obtain ⟨φ, f, hφ, hf, hweak⟩ := admissible_weak_subsequence hu huB
  have hM := (thm_main_real hsin hJ hρ hInt hMall hnu hP hBLlem
    (fun j => hu (φ j)) (fun j => huB (φ j)) (huLim.comp hφ.tendsto_atTop) hf hweak).1
  simpa only [hM, alpha_evenBessel, M0] using hMall

set_option maxHeartbeats 2000000 in
/-- The sharp upper bound of Theorem 1.1 for complex-valued circle data. -/
theorem thm_main (hsin : S2C.SinSeries) (hJ : BesselLit evenBessel) (hρ : RhoData ρ ρr)
    (hST : ClassicalSteinTomas) (hnu : ∀ g, Adm g → ∃ ν, NuData g ν)
    (hP : PlanePlancherel) (hBLlem : BrezisLieb6) (hred : CFOTReduction)
    (F : ℝ → ℂ) (hF : MemLp F 2 σ) :
    ext6 F ≤ ENNReal.ofReal M0 * L2n F ^ 6 := by
  obtain ⟨g, hg, hg2, hle⟩ := reduce_to_adm hred hF
  have hb := best_constant_real hsin hJ hρ hST hnu hP hBLlem hred g hg.memLp hg.per hg.anti
  rw [hg2] at hb
  have hB0 : 0 ≤ ∫ θ in Ioc 0 (2 * π), ‖F θ‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  rw [L2n_eq hF, show (6 : ℕ) = 2 * 3 from rfl, ofReal_sqrt_pow hB0,
    ← ENNReal.ofReal_mul (M0_pos hJ).le]
  exact hle.trans (ENNReal.ofReal_le_ofReal hb)

/-- The normalized constant attains the stated sixth-power extension energy. -/
theorem e0_ext6 (hJ : BesselLit evenBessel) (hST : ClassicalSteinTomas) :
    ext6 (toC S2P.e0) = ENNReal.ofReal M0 := by
  obtain ⟨C, hC⟩ := hST
  have hi := (hC _ e0_adm.memLp).1
  rw [ext6_toC e0_adm.memLp e0_adm.per e0_adm.anti hi, S2W.energy_e0 hJ.kern hi,
    alpha_evenBessel, M0]

lemma e0_L2n : L2n (toC S2P.e0) = 1 := by
  rw [L2n_eq (F := toC S2P.e0) e0_adm.memLp.ofReal]
  change ENNReal.ofReal (Real.sqrt (∫ θ, ‖(S2P.e0 θ : ℂ)‖ ^ 2 ∂σ)) = 1
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [show (∫ θ, S2P.e0 θ ^ 2 ∂σ) = 1 from e0_sqNorm, Real.sqrt_one, ENNReal.ofReal_one]

private lemma E_const_mul (c : ℂ) (f : ℝ → ℂ) (x : ℝ × ℝ) :
    E (fun θ => c * f θ) x = c * E f x := by
  unfold E
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun θ => by ring)

private lemma ext6_const_mul (c : ℂ) (f : ℝ → ℂ) :
    ext6 (fun θ => c * f θ) = ‖c‖ₑ ^ 6 * ext6 f := by
  simp_rw [ext6, E_const_mul, enorm_mul, mul_pow]
  exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top (by simp))

private lemma L2n_const_mul (c : ℂ) (f : ℝ → ℂ) :
    L2n (fun θ => c * f θ) = ‖c‖ₑ * L2n f :=
  eLpNorm_const_smul c f 2 σ

/-- All complex constants attain equality in the sharp bound. -/
theorem const_attains (hJ : BesselLit evenBessel) (hST : ClassicalSteinTomas) (c : ℂ) :
    ext6 (fun _ => c) = ENNReal.ofReal M0 * L2n (fun _ => c) ^ 6 := by
  let a := (1 / Real.sqrt (2 * π) : ℝ)
  have ha : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by unfold a; positivity))
  have h : (fun _ : ℝ => c) = (fun θ => (c / (a : ℂ)) * toC S2P.e0 θ) := by
    funext θ
    change c = c / (a : ℂ) * (a : ℂ)
    exact (div_mul_cancel₀ _ ha).symm
  rw [h, ext6_const_mul, L2n_const_mul, e0_ext6 hJ hST, e0_L2n, mul_one, mul_comm]

/-- A nonzero constant is a maximizer of the extension functional. -/
theorem const_isMaximizer (hsin : S2C.SinSeries) (hJ : BesselLit evenBessel)
    (hρ : RhoData ρ ρr) (hST : ClassicalSteinTomas) (hnu : ∀ g, Adm g → ∃ ν, NuData g ν)
    (hP : PlanePlancherel) (hBLlem : BrezisLieb6) (hred : CFOTReduction)
    {c : ℂ} (hc : c ≠ 0) : IsMaximizer (fun _ => c) := by
  haveI : IsFiniteMeasure σ := isFin
  have hfc : MemLp (fun _ : ℝ => c) 2 σ := memLp_const _
  refine ⟨hfc, ?_, fun f hf => ?_⟩
  · rw [L2n_eq hfc]
    have he : (∫ θ in Ioc (0 : ℝ) (2 * π), ‖c‖ ^ 2) = 2 * π * ‖c‖ ^ 2 := int_const _
    rw [he]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr
      (mul_pos (by positivity) (pow_pos (norm_pos_iff.mpr hc) 2))))
  · rw [const_attains hJ hST]
    calc
      _ ≤ (ENNReal.ofReal M0 * L2n f ^ 6) * L2n (fun _ => c) ^ 6 :=
        mul_le_mul' (thm_main hsin hJ hρ hST hnu hP hBLlem hred f hf) le_rfl
      _ = _ := by ac_rfl

set_option maxHeartbeats 1000000 in
/-- **Theorem 1.2** (thm:L1-remainder): for complex-valued F ∈ L²(σ),
‖EF‖₆⁶ ≤ M_conc‖F‖₂⁶ + 90π‖F‖₁²‖F‖₂⁴ -/
private theorem thm_L1_remainder_periodic (hsin : S2C.SinSeries) (hρ : RhoData ρ ρr)
    (hnu : ∀ g, Adm g → ∃ ν, NuData g ν)
    (F : ℝ → ℂ) (hF : MemLp F 2 σ) (hFm : Measurable F) (hFper : Periodic F (2 * π))
    -- [CFOT17, §1 Steps 1–2]: ‖EF‖₆ ≤ ‖EF♯‖₆
    (hred1 : ext6 F ≤ ENNReal.ofReal (∫ x, S2P.Ec (S4M.sharp (fun θ => ‖F θ‖)) x ^ 6)) :
    ext6 F ≤ ENNReal.ofReal Mconc * L2n F ^ 6 + ENNReal.ofReal (90 * π) * L1n F ^ 2 * L2n F ^ 4 := by
  have hp := pi_pos
  have ham : Measurable fun θ => ‖F θ‖ := hFm.norm
  have ha0 : ∀ θ, 0 ≤ ‖F θ‖ := fun θ => norm_nonneg _
  have haper : Periodic (fun θ => ‖F θ‖) (2 * π) := fun θ => by simp only [hFper θ]
  have ha : MemLp (fun θ => ‖F θ‖) 2 μI := hF.norm
  have hadm := sharp_adm ham ha0 haper ha
  obtain ⟨ν, hν⟩ := hnu _ hadm
  have hs := S4M.L1_remainder_sym hsin hadm.meas hadm.nonneg hadm.per hadm.anti hadm.memLp
    hν.meas hν.nonneg hν.dens (by rw [hν.l2]; exact ENNReal.ofReal_lt_top)
    hρ.meas hρ.nonneg hρ.dens hρ.rad hρ.r0 hρ.formula hν.mint hν.magic
  have hEs : (ext6 F).toReal ≤ ∫ x, S2P.Ec (S4M.sharp (fun θ => ‖F θ‖)) x ^ 6 :=
    ENNReal.toReal_le_of_le_ofReal (integral_nonneg fun x => pow6_nonneg _) hred1
  have hthm := S4M.thm_L1 ham ha0 haper ha hEs hs
  have hne : ext6 F ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hred1
  obtain ⟨B, hB⟩ : ∃ B, B = ∫ θ in Ioc 0 (2 * π), ‖F θ‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = ∫ θ in Ioc 0 (2 * π), ‖F θ‖ := ⟨_, rfl⟩
  rw [← hB, ← hL] at hthm
  have hB0 : 0 ≤ B := hB ▸ integral_nonneg fun _ => sq_nonneg _
  have hL0 : 0 ≤ L := hL ▸ integral_nonneg fun _ => norm_nonneg _
  have hMc0 : 0 ≤ Mconc := by unfold Mconc; positivity
  rw [L2n_eq hF, L1n_eq hF, ← hB, ← hL, show (6 : ℕ) = 2 * 3 from rfl, show (4 : ℕ) = 2 * 2 from rfl,
    ofReal_sqrt_pow hB0, ofReal_sqrt_pow hB0, ← ENNReal.ofReal_pow hL0]
  have hR : ENNReal.ofReal (Mconc * B ^ 3 + 90 * π * L ^ 2 * B ^ 2)
      = ENNReal.ofReal Mconc * ENNReal.ofReal (B ^ 3)
        + ENNReal.ofReal (90 * π) * ENNReal.ofReal (L ^ 2) * ENNReal.ofReal (B ^ 2) := by
    rw [ENNReal.ofReal_add (mul_nonneg hMc0 (pow_nonneg hB0 3))
        (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg L)) (sq_nonneg B)),
      ENNReal.ofReal_mul hMc0,
      ENNReal.ofReal_mul (show (0 : ℝ) ≤ 90 * π * L ^ 2 from mul_nonneg (by positivity) (sq_nonneg L)),
      ENNReal.ofReal_mul (show (0 : ℝ) ≤ 90 * π by positivity)]
  rw [← hR, ← ENNReal.ofReal_toReal hne]
  exact ENNReal.ofReal_le_ofReal hthm


/-- Theorem 1.2's upper bound, for every circle L² equivalence class. -/
theorem thm_L1_remainder (hsin : S2C.SinSeries) (hρ : RhoData ρ ρr)
    (hnu : ∀ g, Adm g → ∃ ν, NuData g ν) (hred : CFOTReduction)
    (F : ℝ → ℂ) (hF : MemLp F 2 σ) :
    ext6 F ≤ ENNReal.ofReal Mconc * L2n F ^ 6 +
      ENNReal.ofReal (90 * π) * L1n F ^ 2 * L2n F ^ 4 := by
  obtain ⟨G, hGm, hGp, hGF⟩ := periodic_representative hF.aestronglyMeasurable
  have hG := hF.ae_eq hGF.symm
  have h := thm_L1_remainder_periodic hsin hρ hnu G hG hGm hGp (hred G hG hGm hGp)
  simpa only [ext6, E_congr_ae hGF, L2n, L1n, eLpNorm_congr_ae hGF] using h

end

end SteinTomas.S6

#print axioms SteinTomas.S6.thm_main_real
#print axioms SteinTomas.S6.thm_main
#print axioms SteinTomas.S6.const_isMaximizer
#print axioms SteinTomas.S6.thm_L1_remainder
