import Mathlib
import SteinTomasCircle.Section2.QFourier
import SteinTomasCircle.Section2.PairChangeOfVariables
import SteinTomasCircle.Section2.PairDensity

/-!
# Section 2 (§2.3): eq:h-Fourier

* `pair_real` / `pair_complex`: Bochner version of eq:pair-change-of-variables (integrable real/complex Φ),
  written as an integral over the product measure: ∫_{[0,2π]²} |sin(t−s)| Φ(ω+η) = 2∫_{|y|<2} Φ.
* `hhat_eq`: ĥ(x) = ∫∫ |sin(t−s)| f(s)f(t) e^{−ix·(ω+η)}.
* `h_fourier`: ĥ(x) = (2/π)(Ef(x))² − Σ_{n≥1} c_n E(fθ^{2n})(x) E(fθ^{−2n})(x), c_n = (4/π)/(4n²−1).

Notation: e^{−ix·ω(θ)} = `ex x θ`, E(fθ^k)(x) = `Ek f k x` = ∫₀^{2π} e^{ikθ} e^{−ix·ω(θ)} f(θ) dθ.
External input: only the classical Fourier series of |sin u| (`S2C.SinSeries`).
-/

namespace SteinTomas.S2HF

open Real MeasureTheory Set Function
open scoped ENNReal

noncomputable section

/-- Weight |det(ω,η)| = |sin(t−s)| -/
def wt (p : ℝ × ℝ) : ℝ := |Real.sin (p.2 - p.1)|

/-- (s,t) ↦ ω + η -/
def sg (p : ℝ × ℝ) : ℝ × ℝ := (Real.cos p.1 + Real.cos p.2, Real.sin p.1 + Real.sin p.2)

/-- Disk |y| < 2 -/
def D : Set (ℝ × ℝ) := {y | y.1 ^ 2 + y.2 ^ 2 < 4}

/-- Product measure σ × σ (angular variables) -/
def ν : Measure (ℝ × ℝ) := (volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict (Ioc 0 (2 * π)))

lemma wt_cont : Continuous wt := by unfold wt; fun_prop
lemma sg_cont : Continuous sg := by unfold sg; fun_prop
lemma D_meas : MeasurableSet D := measurableSet_lt (by fun_prop) measurable_const

lemma wt_le (p : ℝ × ℝ) : ‖wt p‖ ≤ 1 := by
  unfold wt; rw [Real.norm_eq_abs, abs_abs]; exact abs_sin_le_one _

lemma pair_lint_prod {Ψ : ℝ × ℝ → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ p, ENNReal.ofReal (wt p) * Ψ (sg p) ∂ν = 2 * ∫⁻ y in D, Ψ y := by
  unfold ν
  rw [lintegral_prod _ ?_]
  · exact S2V.pair_cov hΨ
  · exact ((ENNReal.measurable_ofReal.comp wt_cont.measurable).mul
      (hΨ.comp sg_cont.measurable)).aemeasurable

/-- Nonnegative case -/
lemma pair_nonneg {G : ℝ × ℝ → ℝ} (hGm : Measurable G) (hG0 : ∀ y, 0 ≤ G y)
    (hGi : IntegrableOn G D) :
    Integrable (fun p => wt p * G (sg p)) ν ∧ ∫ p, wt p * G (sg p) ∂ν = 2 * ∫ y in D, G y := by
  have hm : Measurable fun p => wt p * G (sg p) :=
    wt_cont.measurable.mul (hGm.comp sg_cont.measurable)
  have hnn : 0 ≤ᵐ[ν] fun p => wt p * G (sg p) :=
    Filter.Eventually.of_forall (fun p => mul_nonneg (abs_nonneg _) (hG0 _))
  have hl : ∫⁻ p, ENNReal.ofReal (wt p * G (sg p)) ∂ν = ENNReal.ofReal (2 * ∫ y in D, G y) := by
    have e : ∀ p, ENNReal.ofReal (wt p * G (sg p))
        = ENNReal.ofReal (wt p) * ENNReal.ofReal (G (sg p)) :=
      fun p => ENNReal.ofReal_mul (abs_nonneg _)
    simp_rw [e]
    rw [pair_lint_prod (Ψ := fun y => ENNReal.ofReal (G y)) (ENNReal.measurable_ofReal.comp hGm),
      ← ofReal_integral_eq_lintegral_ofReal hGi (Filter.Eventually.of_forall hG0),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hI0 : 0 ≤ ∫ y in D, G y := integral_nonneg hG0
  refine ⟨⟨hm.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hnn, hl]; exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hm.aestronglyMeasurable, hl,
      ENNReal.toReal_ofReal (by positivity)]

lemma pos_neg_decomp (z : ℝ) : z = max z 0 - max (-z) 0 := by
  rcases le_total 0 z with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

/-- Real-valued integrable case -/
theorem pair_real {Φ : ℝ × ℝ → ℝ} (hΦm : Measurable Φ) (hΦi : IntegrableOn Φ D) :
    Integrable (fun p => wt p * Φ (sg p)) ν ∧ ∫ p, wt p * Φ (sg p) ∂ν = 2 * ∫ y in D, Φ y := by
  have hP := pair_nonneg (G := fun y => max (Φ y) 0) (hΦm.max measurable_const)
    (fun y => le_max_right _ _) hΦi.pos_part
  have hN := pair_nonneg (G := fun y => max (-Φ y) 0) (hΦm.neg.max measurable_const)
    (fun y => le_max_right _ _) hΦi.neg_part
  have hfun : (fun p => wt p * Φ (sg p))
      = fun p => wt p * max (Φ (sg p)) 0 - wt p * max (-Φ (sg p)) 0 := by
    funext p; rw [← mul_sub, ← pos_neg_decomp]
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact hP.1.sub hN.1
  · rw [hfun, integral_sub hP.1 hN.1, hP.2, hN.2, ← mul_sub,
      ← integral_sub hΦi.pos_part hΦi.neg_part]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    exact (pos_neg_decomp (Φ y)).symm

/-- Complex-valued integrable case -/
theorem pair_complex {Φ : ℝ × ℝ → ℂ} (hΦm : Measurable Φ) (hΦi : IntegrableOn Φ D) :
    Integrable (fun p => (wt p : ℂ) * Φ (sg p)) ν ∧
      ∫ p, (wt p : ℂ) * Φ (sg p) ∂ν = 2 * ∫ y in D, Φ y := by
  have hre : IntegrableOn (fun y => (Φ y).re) D := by
    simpa only [RCLike.re_to_complex] using hΦi.re
  have him : IntegrableOn (fun y => (Φ y).im) D := by
    simpa only [RCLike.im_to_complex] using hΦi.im
  have R := pair_real (Φ := fun y => (Φ y).re) (Complex.measurable_re.comp hΦm) hre
  have Im := pair_real (Φ := fun y => (Φ y).im) (Complex.measurable_im.comp hΦm) him
  have hfun : (fun p => (wt p : ℂ) * Φ (sg p))
      = fun p => ((wt p * (Φ (sg p)).re : ℝ) : ℂ) + ((wt p * (Φ (sg p)).im : ℝ) : ℂ) * Complex.I := by
    funext p
    apply Complex.ext <;> simp
  have hi1 : Integrable (fun p => ((wt p * (Φ (sg p)).re : ℝ) : ℂ)) ν := R.1.ofReal
  have hi2 : Integrable (fun p => ((wt p * (Φ (sg p)).im : ℝ) : ℂ) * Complex.I) ν :=
    Im.1.ofReal.mul_const _
  have hD1 : Integrable (fun y => ((Φ y).re : ℂ)) (volume.restrict D) := hre.ofReal
  have hD2 : Integrable (fun y => ((Φ y).im : ℂ) * Complex.I) (volume.restrict D) :=
    him.ofReal.mul_const _
  have hrhs : ∫ y in D, Φ y = ∫ y in D, (((Φ y).re : ℂ) + ((Φ y).im : ℂ) * Complex.I) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    exact (Complex.re_add_im (Φ y)).symm
  refine ⟨by rw [hfun]; exact hi1.add hi2, ?_⟩
  rw [hfun, integral_add hi1 hi2, integral_mul_const, integral_complex_ofReal,
    integral_complex_ofReal, R.2, Im.2, hrhs, integral_add hD1 hD2, integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal]
  push_cast; ring

/-! ## ĥ -/

/-- e^{−ix·ω(θ)} -/
def ex (x : ℝ × ℝ) (θ : ℝ) : ℂ :=
  Complex.exp (((-(x.1 * Real.cos θ + x.2 * Real.sin θ) : ℝ) : ℂ) * Complex.I)

/-- e^{−ix·y} -/
def ex2 (x y : ℝ × ℝ) : ℂ := Complex.exp (((-(x.1 * y.1 + x.2 * y.2) : ℝ) : ℂ) * Complex.I)

/-- ĥ(x) = ∫ h(y) e^{−ix·y} dy -/
def hhat (f : ℝ → ℝ) (x : ℝ × ℝ) : ℂ := ∫ y, (S2H.hfun f y : ℂ) * ex2 x y

/-- e^{−ix·ω(θ)} f(θ) -/
def uf (f : ℝ → ℝ) (x : ℝ × ℝ) (θ : ℝ) : ℂ := ex x θ * (f θ : ℂ)

/-- E(fθ^k)(x) = ∫₀^{2π} e^{ikθ} e^{−ix·ω(θ)} f(θ) dθ -/
def Ek (f : ℝ → ℝ) (k : ℝ) (x : ℝ × ℝ) : ℂ :=
  ∫ θ in Ioc 0 (2 * π), Complex.exp (((k * θ : ℝ) : ℂ) * Complex.I) * uf f x θ

lemma norm_ex (x : ℝ × ℝ) (θ : ℝ) : ‖ex x θ‖ = 1 := by unfold ex; exact Complex.norm_exp_ofReal_mul_I _
lemma norm_ex2 (x y : ℝ × ℝ) : ‖ex2 x y‖ = 1 := by unfold ex2; exact Complex.norm_exp_ofReal_mul_I _
lemma ex_cont (x : ℝ × ℝ) : Continuous (ex x) := by unfold ex; fun_prop
lemma ex2_cont (x : ℝ × ℝ) : Continuous (ex2 x) := by unfold ex2; fun_prop

lemma ex2_sg (x : ℝ × ℝ) (p : ℝ × ℝ) : ex2 x (sg p) = ex x p.1 * ex x p.2 := by
  unfold ex2 ex sg
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

lemma D_bounded : Bornology.IsBounded D := by
  refine (Metric.isBounded_closedBall (x := (0 : ℝ × ℝ)) (r := 2)).subset (fun y hy => ?_)
  have hy' : y.1 ^ 2 + y.2 ^ 2 < 4 := hy
  rw [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  have h1 : |y.1 - (0 : ℝ × ℝ).1| ≤ 2 := by
    simp only [Prod.fst_zero, sub_zero]
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg y.2]
  have h2 : |y.2 - (0 : ℝ × ℝ).2| ≤ 2 := by
    simp only [Prod.snd_zero, sub_zero]
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg y.1]
  exact max_le h1 h2

variable {f : ℝ → ℝ}

lemma h_intOn (hf : MemLp f 2 (volume.restrict (Ioc 0 (2 * π)))) (hfm : Measurable f)
    (hper : Periodic f (2 * π)) : IntegrableOn (S2H.hfun f) D := by
  have h2 := (S2H.h_L2_real hf hfm hper).1
  have hfin : volume D < ∞ := D_bounded.measure_lt_top
  haveI : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.2 hfin.ne
  have hb : IntegrableOn (fun y => (1 + S2H.hfun f y ^ 2) / 2) D :=
    ((integrable_const (1 : ℝ)).add h2.integrableOn).div_const 2
  refine hb.mono' (S2H.hfun_meas hfm).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => ?_))
  rw [Real.norm_eq_abs]
  show |S2H.hfun f y| ≤ (1 + S2H.hfun f y ^ 2) / 2
  nlinarith [sq_nonneg (|S2H.hfun f y| - 1), sq_abs (S2H.hfun f y)]

/-- ĥ(x) = ∫∫ |sin(t−s)| (e^{−ix·ω}f)(s)(e^{−ix·η}f)(t) -/
theorem hhat_eq (hf : MemLp f 2 (volume.restrict (Ioc 0 (2 * π)))) (hfm : Measurable f)
    (hper : Periodic f (2 * π)) (x : ℝ × ℝ) :
    Integrable (fun p => (wt p : ℂ) * (uf f x p.1 * uf f x p.2)) ν ∧
    hhat f x = ∫ p, (wt p : ℂ) * (uf f x p.1 * uf f x p.2) ∂ν := by
  set Φ : ℝ × ℝ → ℂ := fun y => (S2H.hfun f y : ℂ) * ex2 x y with hΦ
  have hΦm : Measurable Φ :=
    (Complex.measurable_ofReal.comp (S2H.hfun_meas hfm)).mul (ex2_cont x).measurable
  have hΦi : IntegrableOn Φ D := by
    have hh := h_intOn hf hfm hper
    refine (hh.norm).mono' hΦm.aestronglyMeasurable (Filter.Eventually.of_forall (fun y => ?_))
    simp only [hΦ, norm_mul, norm_ex2, mul_one, Complex.norm_real, le_refl]
  obtain ⟨hint, heq⟩ := pair_complex hΦm hΦi
  have hpt : ∀ p : ℝ × ℝ, (wt p : ℂ) * Φ (sg p)
      = 2 * ((wt p : ℂ) * (uf f x p.1 * uf f x p.2)) := by
    intro p
    simp only [hΦ]
    rw [ex2_sg]
    by_cases hs : Real.sin (p.2 - p.1) = 0
    · have : wt p = 0 := by unfold wt; rw [hs, abs_zero]
      rw [this]; simp
    · have := S2H.h_pair hper p.1 p.2 hs
      unfold sg
      rw [this]
      unfold uf
      push_cast; ring
  have hfun : (fun p => (wt p : ℂ) * Φ (sg p))
      = fun p => 2 * ((wt p : ℂ) * (uf f x p.1 * uf f x p.2)) :=
    funext hpt
  rw [hfun] at hint heq
  have hint' := hint.const_mul (1 / 2 : ℂ)
  refine ⟨hint'.congr (Filter.Eventually.of_forall (fun p => by simp only; ring)), ?_⟩
  have hzero : ∀ y, y ∉ D → Φ y = 0 := by
    intro y hy
    simp only [hΦ]
    have : S2H.hfun f y = 0 := by
      unfold S2H.hfun; rw [if_neg (show ¬ (y.1 ^ 2 + y.2 ^ 2 < 4) from hy)]
    rw [this]; simp
  have hD : ∫ y in D, Φ y = hhat f x := setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  rw [integral_const_mul, hD] at heq
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  exact (mul_left_cancel₀ h2 heq).symm

set_option maxHeartbeats 2000000 in
/-- eq:h-Fourier -/
theorem h_fourier (hsin : S2C.SinSeries) (hf : MemLp f 2 (volume.restrict (Ioc 0 (2 * π))))
    (hfm : Measurable f) (hper : Periodic f (2 * π)) (x : ℝ × ℝ) :
    HasSum (fun n => (S2C.cQ n : ℂ) * (Ek f (S2C.kf n) x * Ek f (-S2C.kf n) x))
      (((2 / π : ℝ) : ℂ) * Ek f 0 x ^ 2 - hhat f x) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hf1 : Integrable f (volume.restrict (Ioc 0 (2 * π))) := hf.integrable one_le_two
  have hui : Integrable (uf f x) (volume.restrict (Ioc 0 (2 * π))) := by
    have : Integrable (fun θ => ex x θ * (f θ : ℂ)) (volume.restrict (Ioc 0 (2 * π))) :=
      hf1.ofReal.bdd_mul (c := 1) (ex_cont x).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun θ => (norm_ex x θ).le))
    exact this
  have hexpk : ∀ k : ℝ, Integrable (fun θ => Complex.exp (((k * θ : ℝ) : ℂ) * Complex.I) * uf f x θ)
      (volume.restrict (Ioc 0 (2 * π))) := by
    intro k
    exact hui.bdd_mul (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
      (Filter.Eventually.of_forall (fun θ => (Complex.norm_exp_ofReal_mul_I _).le))
  have hUi : Integrable (fun p : ℝ × ℝ => uf f x p.1 * uf f x p.2) ν := hui.mul_prod hui
  obtain ⟨hKi, hK⟩ := hhat_eq hf hfm hper x
  have hcs : Summable S2C.cQ := by
    have := (hsin 0).summable
    simpa using this
  -- terms of the series
  have hFi : ∀ n, Integrable (fun p : ℝ × ℝ =>
      ((S2C.cQ n * Real.cos (S2C.kf n * (p.2 - p.1)) : ℝ) : ℂ) * (uf f x p.1 * uf f x p.2)) ν := by
    intro n
    exact hUi.bdd_mul (c := S2C.cQ n) (Continuous.aestronglyMeasurable (by fun_prop))
      (Filter.Eventually.of_forall (fun p => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (S2C.cQ_nonneg n)]
        exact mul_le_of_le_one_right (S2C.cQ_nonneg n) (abs_cos_le_one _)))
  have hle : ∀ n, ∫ p, ‖((S2C.cQ n * Real.cos (S2C.kf n * (p.2 - p.1)) : ℝ) : ℂ)
      * (uf f x p.1 * uf f x p.2)‖ ∂ν ≤ S2C.cQ n * ∫ p, ‖uf f x p.1 * uf f x p.2‖ ∂ν := by
    intro n
    rw [← integral_const_mul]
    refine integral_mono (hFi n).norm (hUi.norm.const_mul _) (fun p => ?_)
    simp only
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (S2C.cQ_nonneg n)]
    have := abs_cos_le_one (S2C.kf n * (p.2 - p.1))
    have h0 := S2C.cQ_nonneg n
    have h1 := norm_nonneg (uf f x p.1 * uf f x p.2)
    nlinarith [mul_nonneg h0 h1]
  have hsum : Summable (fun n => ∫ p, ‖((S2C.cQ n * Real.cos (S2C.kf n * (p.2 - p.1)) : ℝ) : ℂ)
      * (uf f x p.1 * uf f x p.2)‖ ∂ν) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg (fun p => norm_nonneg _)) hle
      (hcs.mul_right _)
  have hHS := hasSum_integral_of_summable_integral_norm hFi hsum
  -- complex exponential form of cos
  have hcos : ∀ (k s t : ℝ), ((Real.cos (k * (t - s)) : ℝ) : ℂ)
      = (Complex.exp (((-k * s : ℝ) : ℂ) * Complex.I) * Complex.exp (((k * t : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((k * s : ℝ) : ℂ) * Complex.I)
          * Complex.exp (((-k * t : ℝ) : ℂ) * Complex.I)) / 2 := by
    intro k s t
    rw [← Complex.exp_add, ← Complex.exp_add, Complex.ofReal_cos]
    have h2 := Complex.two_cos (((k * (t - s) : ℝ) : ℂ))
    have e1 : ((-k * s : ℝ) : ℂ) * Complex.I + ((k * t : ℝ) : ℂ) * Complex.I
        = ((k * (t - s) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have e2 : ((k * s : ℝ) : ℂ) * Complex.I + ((-k * t : ℝ) : ℂ) * Complex.I
        = -((k * (t - s) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [e1, e2]
    linear_combination h2 / 2
  -- termwise integration
  have hFint : ∀ n, ∫ p, ((S2C.cQ n * Real.cos (S2C.kf n * (p.2 - p.1)) : ℝ) : ℂ)
      * (uf f x p.1 * uf f x p.2) ∂ν
      = (S2C.cQ n : ℂ) * (Ek f (S2C.kf n) x * Ek f (-S2C.kf n) x) := by
    intro n
    have e : (fun p : ℝ × ℝ => ((S2C.cQ n * Real.cos (S2C.kf n * (p.2 - p.1)) : ℝ) : ℂ)
        * (uf f x p.1 * uf f x p.2)) = fun p =>
        ((S2C.cQ n / 2 : ℝ) : ℂ)
          * ((Complex.exp (((-S2C.kf n * p.1 : ℝ) : ℂ) * Complex.I) * uf f x p.1)
            * (Complex.exp (((S2C.kf n * p.2 : ℝ) : ℂ) * Complex.I) * uf f x p.2))
        + ((S2C.cQ n / 2 : ℝ) : ℂ)
          * ((Complex.exp (((S2C.kf n * p.1 : ℝ) : ℂ) * Complex.I) * uf f x p.1)
            * (Complex.exp (((-S2C.kf n * p.2 : ℝ) : ℂ) * Complex.I) * uf f x p.2)) := by
      funext p
      rw [Complex.ofReal_mul, hcos (S2C.kf n) p.1 p.2]
      push_cast; ring
    have i1 : Integrable (fun p : ℝ × ℝ =>
        (Complex.exp (((-S2C.kf n * p.1 : ℝ) : ℂ) * Complex.I) * uf f x p.1)
        * (Complex.exp (((S2C.kf n * p.2 : ℝ) : ℂ) * Complex.I) * uf f x p.2)) ν :=
      Integrable.mul_prod
        (f := fun s => Complex.exp (((-S2C.kf n * s : ℝ) : ℂ) * Complex.I) * uf f x s)
        (g := fun t => Complex.exp (((S2C.kf n * t : ℝ) : ℂ) * Complex.I) * uf f x t)
        (hexpk (-S2C.kf n)) (hexpk (S2C.kf n))
    have i2 : Integrable (fun p : ℝ × ℝ =>
        (Complex.exp (((S2C.kf n * p.1 : ℝ) : ℂ) * Complex.I) * uf f x p.1)
        * (Complex.exp (((-S2C.kf n * p.2 : ℝ) : ℂ) * Complex.I) * uf f x p.2)) ν :=
      Integrable.mul_prod
        (f := fun s => Complex.exp (((S2C.kf n * s : ℝ) : ℂ) * Complex.I) * uf f x s)
        (g := fun t => Complex.exp (((-S2C.kf n * t : ℝ) : ℂ) * Complex.I) * uf f x t)
        (hexpk (S2C.kf n)) (hexpk (-S2C.kf n))
    rw [e, integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]
    unfold ν
    rw [integral_prod_mul (fun s => Complex.exp (((-S2C.kf n * s : ℝ) : ℂ) * Complex.I) * uf f x s)
        (fun t => Complex.exp (((S2C.kf n * t : ℝ) : ℂ) * Complex.I) * uf f x t),
      integral_prod_mul (fun s => Complex.exp (((S2C.kf n * s : ℝ) : ℂ) * Complex.I) * uf f x s)
        (fun t => Complex.exp (((-S2C.kf n * t : ℝ) : ℂ) * Complex.I) * uf f x t)]
    have hE1 : ∀ k : ℝ, ∫ θ in Ioc 0 (2 * π), Complex.exp (((k * θ : ℝ) : ℂ) * Complex.I) * uf f x θ
        = Ek f k x := fun k => rfl
    simp only [hE1]
    push_cast; ring
  have htsum : (fun p : ℝ × ℝ => ∑' n, ((S2C.cQ n * Real.cos (S2C.kf n * (p.2 - p.1)) : ℝ) : ℂ)
      * (uf f x p.1 * uf f x p.2))
      = fun p => (((2 / π - wt p : ℝ) : ℂ)) * (uf f x p.1 * uf f x p.2) := by
    funext p
    exact ((Complex.hasSum_ofReal.2 (hsin (p.2 - p.1))).mul_right (uf f x p.1 * uf f x p.2)).tsum_eq
  rw [funext hFint, htsum] at hHS
  -- ∫ (2/π − w) U = (2/π)(Ef)² − ĥ
  have e2 : (fun p : ℝ × ℝ => (((2 / π - wt p : ℝ) : ℂ)) * (uf f x p.1 * uf f x p.2))
      = fun p => ((2 / π : ℝ) : ℂ) * (uf f x p.1 * uf f x p.2)
        - (wt p : ℂ) * (uf f x p.1 * uf f x p.2) := by
    funext p; push_cast; ring
  rw [e2, integral_sub (hUi.const_mul _) hKi, integral_const_mul, ← hK] at hHS
  have hE0 : Ek f 0 x = ∫ θ in Ioc 0 (2 * π), uf f x θ := by
    unfold Ek
    refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    simp
  have hUint : ∫ p, uf f x p.1 * uf f x p.2 ∂ν = Ek f 0 x ^ 2 := by
    unfold ν
    rw [integral_prod_mul (uf f x) (uf f x), hE0, sq]
  rw [hUint] at hHS
  exact hHS

end

end SteinTomas.S2HF

#print axioms SteinTomas.S2HF.pair_complex
#print axioms SteinTomas.S2HF.hhat_eq
#print axioms SteinTomas.S2HF.h_fourier
