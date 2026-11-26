import Mathlib
import SteinTomasCircle.Section5.GlobalSimple
import SteinTomasCircle.Section5.ConvolutionClaim
import SteinTomasCircle.Section2.PairDensity
import SteinTomasCircle.Section2.Analysis

/-!
# Section 5 (III): Lemma 5.2 (lem:a second variation bound)

External inputs (as hypotheses):
* `hsv`: the second variation inequality for maximizers [GN22, Appendix], for real antipodal g ∈ L²:
  5∫(Ef)⁴(Eg)² ≤ ‖Ef‖₆⁶(‖g‖² + 4⟨f,g⟩²)
* `hνL2`: ‖ν‖₂² = ‖Ef‖₆⁶/(4π²) (ν = (fσ)*³)
* `hpl`: Plancherel ⟨ν, h*(fσ)⟩ = (1/4π²)∫(Ef)⁴ĥ

All arguments of the paper itself are proved:
* `ek_decomp`: E(fθ^{2n}) = E(f Re θ^{2n}) + i E(f Im θ^{2n})
* `lower`: ∫(Ef)⁴ĥ ≥ (4/5)‖Ef‖₆⁶ Q(f²) (termwise summation, exchange of sum and integral)
* `lemma52`: ‖Ef‖₆⁶ Q(f²) ≤ (75π²/8)‖f‖₁²
-/

namespace SteinTomas.S5C

open Real MeasureTheory Set Function
open scoped ENNReal

noncomputable section

local notation "μI" => (volume.restrict (Ioc (0 : ℝ) (2 * π)))

variable {f : ℝ → ℝ}

lemma imul {g : ℝ → ℝ} (hgi : Integrable g μI) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hb : ∀ t, |φ t| ≤ 1) : Integrable (fun θ => g θ * φ θ) μI :=
  (S2C.bmul hgi hφ (C := 1) (fun t => by rw [Real.norm_eq_abs]; exact hb t)).congr
    (Filter.Eventually.of_forall (fun t => by simp only; ring))

lemma memLp_mul {g : ℝ → ℝ} (hg : MemLp g 2 μI) (hgm : Measurable g) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hb : ∀ t, |φ t| ≤ 1) : MemLp (fun θ => g θ * φ θ) 2 μI :=
  hg.of_le (hgm.mul hφ.measurable).aestronglyMeasurable (Filter.Eventually.of_forall (fun t => by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (by rw [Real.norm_eq_abs]; exact hb t)))

/-- f·Re θ^{2n} -/
def g1 (f : ℝ → ℝ) (n : ℕ) (θ : ℝ) : ℝ := f θ * Real.cos (S2C.kf n * θ)
/-- f·Im θ^{2n} -/
def g2 (f : ℝ → ℝ) (n : ℕ) (θ : ℝ) : ℝ := f θ * Real.sin (S2C.kf n * θ)

lemma kf_pi (n : ℕ) (θ : ℝ) :
    S2C.kf n * (θ + π) = S2C.kf n * θ + ((n + 1 : ℕ) : ℝ) * (2 * π) := by
  unfold S2C.kf; push_cast; ring

lemma kf_2pi (n : ℕ) (θ : ℝ) :
    S2C.kf n * (θ + 2 * π) = S2C.kf n * θ + ((2 * (n + 1) : ℕ) : ℝ) * (2 * π) := by
  unfold S2C.kf; push_cast; ring

lemma g1_anti (hanti : ∀ θ, f (θ + π) = f θ) (n : ℕ) (θ : ℝ) : g1 f n (θ + π) = g1 f n θ := by
  unfold g1; rw [hanti, kf_pi, Real.cos_add_nat_mul_two_pi]

lemma g2_anti (hanti : ∀ θ, f (θ + π) = f θ) (n : ℕ) (θ : ℝ) : g2 f n (θ + π) = g2 f n θ := by
  unfold g2; rw [hanti, kf_pi, Real.sin_add_nat_mul_two_pi]

lemma g1_per (hper : Periodic f (2 * π)) (n : ℕ) : Periodic (g1 f n) (2 * π) := fun θ => by
  unfold g1; rw [hper θ, kf_2pi, Real.cos_add_nat_mul_two_pi]

lemma g2_per (hper : Periodic f (2 * π)) (n : ℕ) : Periodic (g2 f n) (2 * π) := fun θ => by
  unfold g2; rw [hper θ, kf_2pi, Real.sin_add_nat_mul_two_pi]

lemma Ec_set (g : ℝ → ℝ) (x : ℝ × ℝ) :
    S2P.Ec g x = ∫ θ in Ioc 0 (2 * π), g θ * Real.cos (S5A.dd x θ) := by
  unfold S2P.Ec
  rw [intervalIntegral.integral_of_le (by positivity)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
  simp only [S5A.dd]; ring

lemma Ec_cont {g : ℝ → ℝ} (hg : MemLp g 2 μI) : Continuous (S2P.Ec g) := by
  have hgi : Integrable g μI := hg.integrable one_le_two
  have e : S2P.Ec g = fun x : ℝ × ℝ =>
      ∫ θ in Ioc 0 (2 * π), Real.cos (x.1 * Real.cos θ + x.2 * Real.sin θ) * g θ := by
    funext x; rw [S2P.Ec, intervalIntegral.integral_of_le (by positivity)]
  rw [e]
  apply continuous_of_dominated (bound := fun θ => ‖g θ‖)
  · intro x
    exact (Continuous.aestronglyMeasurable (by fun_prop)).mul hgi.aestronglyMeasurable
  · intro x
    filter_upwards with θ
    rw [norm_mul]
    have : ‖Real.cos (x.1 * Real.cos θ + x.2 * Real.sin θ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
    nlinarith [norm_nonneg (g θ)]
  · exact hgi.norm
  · filter_upwards with θ
    fun_prop

/-- Antipodal g: ∫ g sin(x·ω) = 0 -/
lemma sin_zero {g : ℝ → ℝ} (hp : Periodic g (2 * π)) (ha : ∀ θ, g (θ + π) = g θ) (x : ℝ × ℝ) :
    ∫ θ in Ioc 0 (2 * π), g θ * Real.sin (S5A.dd x θ) = 0 := by
  have hp' : Periodic (fun θ => g θ * Real.sin (S5A.dd x θ)) (2 * π) := by
    intro θ; simp only [S5A.dd, hp θ, S5A.dot_two_pi]
  have h := S4M.int_shift_pi hp'
  have e : ∀ θ, g (θ + π) * Real.sin (S5A.dd x (θ + π)) = -(g θ * Real.sin (S5A.dd x θ)) := by
    intro θ; simp only [S5A.dd, ha θ, S5A.dot_pi, Real.sin_neg]; ring
  simp only [e, integral_neg] at h
  linarith

set_option maxHeartbeats 1000000 in
/-- E(fθ^{2n}) = E(g₁) + i E(g₂) -/
theorem ek_decomp (hf : MemLp f 2 μI) (hper : Periodic f (2 * π)) (hanti : ∀ θ, f (θ + π) = f θ)
    (n : ℕ) (x : ℝ × ℝ) :
    S2HF.Ek f (S2C.kf n) x = (S2P.Ec (g1 f n) x : ℂ) + (S2P.Ec (g2 f n) x : ℂ) * Complex.I := by
  have hfi : Integrable f μI := hf.integrable one_le_two
  have h1i : Integrable (g1 f n) μI :=
    imul hfi (by fun_prop : Continuous fun θ => Real.cos (S2C.kf n * θ)) (fun t => abs_cos_le_one _)
  have h2i : Integrable (g2 f n) μI :=
    imul hfi (by fun_prop : Continuous fun θ => Real.sin (S2C.kf n * θ)) (fun t => abs_sin_le_one _)
  have hdC : Continuous fun θ => Real.cos (S5A.dd x θ) := by unfold S5A.dd; fun_prop
  have hdS : Continuous fun θ => Real.sin (S5A.dd x θ) := by unfold S5A.dd; fun_prop
  have h1C : Integrable (fun θ => g1 f n θ * Real.cos (S5A.dd x θ)) μI :=
    imul h1i hdC (fun t => abs_cos_le_one _)
  have h1S : Integrable (fun θ => g1 f n θ * Real.sin (S5A.dd x θ)) μI :=
    imul h1i hdS (fun t => abs_sin_le_one _)
  have h2C : Integrable (fun θ => g2 f n θ * Real.cos (S5A.dd x θ)) μI :=
    imul h2i hdC (fun t => abs_cos_le_one _)
  have h2S : Integrable (fun θ => g2 f n θ * Real.sin (S5A.dd x θ)) μI :=
    imul h2i hdS (fun t => abs_sin_le_one _)
  have hpt : ∀ θ, Complex.exp (((S2C.kf n * θ : ℝ) : ℂ) * Complex.I) * S2HF.uf f x θ
      = (((g1 f n θ * Real.cos (S5A.dd x θ) + g2 f n θ * Real.sin (S5A.dd x θ)) : ℝ) : ℂ)
        + (((g2 f n θ * Real.cos (S5A.dd x θ) - g1 f n θ * Real.sin (S5A.dd x θ)) : ℝ) : ℂ)
          * Complex.I := by
    intro θ
    unfold S2HF.uf S2HF.ex g1 g2
    rw [Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    simp only [S5A.dd, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_neg]
    linear_combination (-(((Real.sin (S2C.kf n * θ)) : ℂ)
      * ((Real.sin (x.1 * Real.cos θ + x.2 * Real.sin θ)) : ℂ) * (f θ : ℂ))) * Complex.I_sq
  unfold S2HF.Ek
  simp_rw [hpt]
  have hAi : Integrable (fun θ => g1 f n θ * Real.cos (S5A.dd x θ)
      + g2 f n θ * Real.sin (S5A.dd x θ)) μI := h1C.add h2S
  have hBi : Integrable (fun θ => g2 f n θ * Real.cos (S5A.dd x θ)
      - g1 f n θ * Real.sin (S5A.dd x θ)) μI := h2C.sub h1S
  rw [integral_add hAi.ofReal (hBi.ofReal.mul_const _), integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal, integral_add h1C h2S, integral_sub h2C h1S,
    sin_zero (g2_per hper n) (g2_anti hanti n) x, sin_zero (g1_per hper n) (g1_anti hanti n) x,
    add_zero, sub_zero, ← Ec_set, ← Ec_set]

lemma normSq_eq (hf : MemLp f 2 μI) (hper : Periodic f (2 * π)) (hanti : ∀ θ, f (θ + π) = f θ)
    (n : ℕ) (x : ℝ × ℝ) :
    Complex.normSq (S2HF.Ek f (S2C.kf n) x) = S2P.Ec (g1 f n) x ^ 2 + S2P.Ec (g2 f n) x ^ 2 := by
  rw [ek_decomp hf hper hanti, Complex.normSq_add_mul_I]

lemma g1_memLp (hf : MemLp f 2 μI) (hfm : Measurable f) (n : ℕ) : MemLp (g1 f n) 2 μI :=
  memLp_mul hf hfm (by fun_prop : Continuous fun θ => Real.cos (S2C.kf n * θ))
    (fun t => abs_cos_le_one _)

lemma g2_memLp (hf : MemLp f 2 μI) (hfm : Measurable f) (n : ℕ) : MemLp (g2 f n) 2 μI :=
  memLp_mul hf hfm (by fun_prop : Continuous fun θ => Real.sin (S2C.kf n * θ))
    (fun t => abs_sin_le_one _)

lemma sq_sum (hf : MemLp f 2 μI) (hfm : Measurable f) (n : ℕ) :
    (∫ θ in Ioc 0 (2 * π), g1 f n θ ^ 2) + (∫ θ in Ioc 0 (2 * π), g2 f n θ ^ 2)
      = ∫ θ in Ioc 0 (2 * π), f θ ^ 2 := by
  rw [← integral_add (g1_memLp hf hfm n).integrable_sq (g2_memLp hf hfm n).integrable_sq]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
  simp only [g1, g2]
  have := Real.sin_sq_add_cos_sq (S2C.kf n * θ)
  linear_combination (f θ) ^ 2 * this

lemma fg1 (n : ℕ) : ∫ θ in Ioc 0 (2 * π), f θ * g1 f n θ = S2C.Cm (fun θ => f θ ^ 2) n := by
  unfold S2C.Cm
  refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
  simp only [g1]; ring

lemma fg2 (n : ℕ) : ∫ θ in Ioc 0 (2 * π), f θ * g2 f n θ = S2C.Sm (fun θ => f θ ^ 2) n := by
  unfold S2C.Sm
  refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
  simp only [g2]; ring

/-- n-th term: the second variation for g₁ and g₂, added -/
lemma per_n (hf : MemLp f 2 μI) (hfm : Measurable f) (hper : Periodic f (2 * π))
    (hanti : ∀ θ, f (θ + π) = f θ) (hB1 : ∫ θ in Ioc 0 (2 * π), f θ ^ 2 = 1)
    {E6 : ℝ} (hE0 : 0 ≤ E6)
    (hsv : ∀ g : ℝ → ℝ, MemLp g 2 μI → Periodic g (2 * π) → (∀ θ, g (θ + π) = g θ) →
      ∫⁻ x, ENNReal.ofReal (5 * (S2P.Ec f x ^ 4 * S2P.Ec g x ^ 2))
        ≤ ENNReal.ofReal (E6 * ((∫ θ in Ioc 0 (2 * π), g θ ^ 2)
          + 4 * (∫ θ in Ioc 0 (2 * π), f θ * g θ) ^ 2)))
    (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal (S2P.Ec f x ^ 4 * (S2C.cQ n
        * (S2P.Ec (g1 f n) x ^ 2 + S2P.Ec (g2 f n) x ^ 2)))
      ≤ ENNReal.ofReal (S2C.cQ n * (E6 * (1 + 4 * (S2C.Cm (fun θ => f θ ^ 2) n ^ 2
          + S2C.Sm (fun θ => f θ ^ 2) n ^ 2)) / 5)) := by
  have hc0 := S2C.cQ_nonneg n
  have hc5 : 0 ≤ S2C.cQ n / 5 := div_nonneg hc0 (by norm_num)
  have hm1 := g1_memLp hf hfm n
  have hm2 := g2_memLp hf hfm n
  have hEc := Ec_cont hf
  have hE1 := Ec_cont hm1
  have hE2 := Ec_cont hm2
  have e : ∀ x, ENNReal.ofReal (S2P.Ec f x ^ 4 * (S2C.cQ n
        * (S2P.Ec (g1 f n) x ^ 2 + S2P.Ec (g2 f n) x ^ 2)))
      = ENNReal.ofReal (S2C.cQ n / 5) * (ENNReal.ofReal (5 * (S2P.Ec f x ^ 4 * S2P.Ec (g1 f n) x ^ 2))
        + ENNReal.ofReal (5 * (S2P.Ec f x ^ 4 * S2P.Ec (g2 f n) x ^ 2))) := by
    intro x
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hc5]
    congr 1; ring
  have hmeas1 : Measurable fun x => ENNReal.ofReal (5 * (S2P.Ec f x ^ 4 * S2P.Ec (g1 f n) x ^ 2)) :=
    ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))
  rw [lintegral_congr e, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_add_left hmeas1]
  have b1 := hsv (g1 f n) hm1 (g1_per hper n) (g1_anti hanti n)
  have b2 := hsv (g2 f n) hm2 (g2_per hper n) (g2_anti hanti n)
  rw [fg1] at b1
  rw [fg2] at b2
  have hs := sq_sum hf hfm n
  rw [hB1] at hs
  have n1 : 0 ≤ E6 * ((∫ θ in Ioc 0 (2 * π), g1 f n θ ^ 2)
      + 4 * S2C.Cm (fun θ => f θ ^ 2) n ^ 2) :=
    mul_nonneg hE0 (add_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (by positivity))
  have n2 : 0 ≤ E6 * ((∫ θ in Ioc 0 (2 * π), g2 f n θ ^ 2)
      + 4 * S2C.Sm (fun θ => f θ ^ 2) n ^ 2) :=
    mul_nonneg hE0 (add_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (by positivity))
  calc ENNReal.ofReal (S2C.cQ n / 5) * ((∫⁻ x, ENNReal.ofReal
          (5 * (S2P.Ec f x ^ 4 * S2P.Ec (g1 f n) x ^ 2)))
        + ∫⁻ x, ENNReal.ofReal (5 * (S2P.Ec f x ^ 4 * S2P.Ec (g2 f n) x ^ 2)))
      ≤ ENNReal.ofReal (S2C.cQ n / 5) * (ENNReal.ofReal (E6 * ((∫ θ in Ioc 0 (2 * π), g1 f n θ ^ 2)
          + 4 * S2C.Cm (fun θ => f θ ^ 2) n ^ 2))
        + ENNReal.ofReal (E6 * ((∫ θ in Ioc 0 (2 * π), g2 f n θ ^ 2)
          + 4 * S2C.Sm (fun θ => f θ ^ 2) n ^ 2))) :=
        mul_le_mul_of_nonneg_left (add_le_add b1 b2) (by positivity)
    _ = _ := by
        rw [← ENNReal.ofReal_add n1 n2, ← ENNReal.ofReal_mul hc5]
        congr 1
        linear_combination (S2C.cQ n / 5 * E6) * hs

set_option maxHeartbeats 1000000 in
/-- ∫(Ef)⁴ĥ ≥ (4/5)‖Ef‖₆⁶ Q(f²) -/
theorem lower (hsin : S2C.SinSeries) (hfm : Measurable f) (hf0 : ∀ θ, 0 ≤ f θ)
    (hper : Periodic f (2 * π)) (hanti : ∀ θ, f (θ + π) = f θ) (hf : MemLp f 2 μI)
    (hB1 : ∫ θ in Ioc 0 (2 * π), f θ ^ 2 = 1)
    {E6 : ℝ} (hE0 : 0 ≤ E6) (hE6 : E6 = ∫ x, S2P.Ec f x ^ 6)
    (hi6 : Integrable (fun x => S2P.Ec f x ^ 6))
    (hsv : ∀ g : ℝ → ℝ, MemLp g 2 μI → Periodic g (2 * π) → (∀ θ, g (θ + π) = g θ) →
      ∫⁻ x, ENNReal.ofReal (5 * (S2P.Ec f x ^ 4 * S2P.Ec g x ^ 2))
        ≤ ENNReal.ofReal (E6 * ((∫ θ in Ioc 0 (2 * π), g θ ^ 2)
          + 4 * (∫ θ in Ioc 0 (2 * π), f θ * g θ) ^ 2))) :
    4 / 5 * E6 * S2C.Qa (fun θ => f θ ^ 2) ≤ ∫ x, S2P.Ec f x ^ 4 * (S2HF.hhat f x).re := by
  have hp := pi_pos
  have hg : Integrable (fun θ => f θ ^ 2) μI := hf.integrable_sq
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = S2C.Qa (fun θ => f θ ^ 2) := ⟨_, rfl⟩
  rw [← hQ]
  have hQle : Q ≤ 2 / π := by
    have := (S2C.Q_bounds' hsin hg (fun x => sq_nonneg _)).2
    rw [hB1, one_pow, mul_one, ← hQ] at this; exact this
  have hEc := Ec_cont hf
  -- pointwise HasSum
  have hT : ∀ x, HasSum (fun n => S2C.cQ n * (S2P.Ec (g1 f n) x ^ 2 + S2P.Ec (g2 f n) x ^ 2))
      (2 / π * S2P.Ec f x ^ 2 - (S2HF.hhat f x).re) := by
    intro x
    have h := (S5A.hhat_real hsin hf hfm hper hanti x).1
    simp only [normSq_eq hf hper hanti] at h
    exact h
  have htn : ∀ n x, 0 ≤ S2P.Ec f x ^ 4 * (S2C.cQ n
      * (S2P.Ec (g1 f n) x ^ 2 + S2P.Ec (g2 f n) x ^ 2)) := fun n x =>
    mul_nonneg (by positivity) (mul_nonneg (S2C.cQ_nonneg n) (by positivity))
  have hterm_meas : ∀ n, Measurable fun x => ENNReal.ofReal (S2P.Ec f x ^ 4 * (S2C.cQ n
      * (S2P.Ec (g1 f n) x ^ 2 + S2P.Ec (g2 f n) x ^ 2))) := by
    intro n
    have hE1 := Ec_cont (g1_memLp hf hfm n)
    have hE2 := Ec_cont (g2_memLp hf hfm n)
    exact ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))
  have hpt : ∀ x, ENNReal.ofReal (S2P.Ec f x ^ 4 * (2 / π * S2P.Ec f x ^ 2 - (S2HF.hhat f x).re))
      = ∑' n, ENNReal.ofReal (S2P.Ec f x ^ 4 * (S2C.cQ n
          * (S2P.Ec (g1 f n) x ^ 2 + S2P.Ec (g2 f n) x ^ 2))) := by
    intro x
    have h4 := (hT x).mul_left (S2P.Ec f x ^ 4)
    rw [← h4.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => htn n x) h4.summable]
  have hT0 : ∀ x, 0 ≤ S2P.Ec f x ^ 4 * (2 / π * S2P.Ec f x ^ 2 - (S2HF.hhat f x).re) :=
    fun x => ((hT x).mul_left (S2P.Ec f x ^ 4)).nonneg (fun n => htn n x)
  -- Σ c_n = 2/π, Σ c_n(C_n²+S_n²) = 2/π − Q
  have hc : HasSum S2C.cQ (2 / π) := by
    have := Analysis1.hasSum_inv_four_sq_sub_one.mul_left (4 / π)
    convert this using 1
    · funext n; unfold S2C.cQ; ring
    · ring
  have hW := S2C.Q_fourier hsin hg
  rw [hB1, one_pow, mul_one, ← hQ] at hW
  have hs : HasSum (fun n => S2C.cQ n * (E6 * (1 + 4 * (S2C.Cm (fun θ => f θ ^ 2) n ^ 2
      + S2C.Sm (fun θ => f θ ^ 2) n ^ 2)) / 5)) (E6 / 5 * (10 / π - 4 * Q)) := by
    have := (hc.mul_left (E6 / 5)).add (hW.mul_left (4 * E6 / 5))
    convert this using 1
    · funext n; ring
    · ring
  have hsn : ∀ n, 0 ≤ S2C.cQ n * (E6 * (1 + 4 * (S2C.Cm (fun θ => f θ ^ 2) n ^ 2
      + S2C.Sm (fun θ => f θ ^ 2) n ^ 2)) / 5) := fun n =>
    mul_nonneg (S2C.cQ_nonneg n) (div_nonneg (mul_nonneg hE0 (by positivity)) (by norm_num))
  have hlint : ∫⁻ x, ENNReal.ofReal (S2P.Ec f x ^ 4 * (2 / π * S2P.Ec f x ^ 2 - (S2HF.hhat f x).re))
      ≤ ENNReal.ofReal (E6 / 5 * (10 / π - 4 * Q)) := by
    calc _ = ∫⁻ x, ∑' n, ENNReal.ofReal (S2P.Ec f x ^ 4 * (S2C.cQ n
            * (S2P.Ec (g1 f n) x ^ 2 + S2P.Ec (g2 f n) x ^ 2))) := lintegral_congr hpt
      _ = ∑' n, ∫⁻ x, ENNReal.ofReal (S2P.Ec f x ^ 4 * (S2C.cQ n
            * (S2P.Ec (g1 f n) x ^ 2 + S2P.Ec (g2 f n) x ^ 2))) :=
          lintegral_tsum (fun n => (hterm_meas n).aemeasurable)
      _ ≤ ∑' n, ENNReal.ofReal (S2C.cQ n * (E6 * (1 + 4 * (S2C.Cm (fun θ => f θ ^ 2) n ^ 2
            + S2C.Sm (fun θ => f θ ^ 2) n ^ 2)) / 5)) :=
          ENNReal.tsum_le_tsum (fun n => per_n hf hfm hper hanti hB1 hE0 hsv n)
      _ = _ := by rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg hsn hs.summable]
  -- integrability
  have hmeasT : Measurable fun x => S2P.Ec f x ^ 4 * (2 / π * S2P.Ec f x ^ 2 - (S2HF.hhat f x).re) := by
    refine measurable_of_tendsto_metrizable (f := fun N x => ∑ n ∈ Finset.range N,
      S2P.Ec f x ^ 4 * (S2C.cQ n * (S2P.Ec (g1 f n) x ^ 2 + S2P.Ec (g2 f n) x ^ 2)))
      (fun N => ?_) (tendsto_pi_nhds.2 fun x => ((hT x).mul_left (S2P.Ec f x ^ 4)).tendsto_sum_nat)
    refine Finset.measurable_sum _ (fun n _ => ?_)
    have hE1 := Ec_cont (g1_memLp hf hfm n)
    have hE2 := Ec_cont (g2_memLp hf hfm n)
    exact Continuous.measurable (by fun_prop)
  have hTi : Integrable (fun x => S2P.Ec f x ^ 4 * (2 / π * S2P.Ec f x ^ 2 - (S2HF.hhat f x).re)) :=
    ⟨hmeasT.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall hT0)).2 (lt_of_le_of_lt hlint ENNReal.ofReal_lt_top)⟩
  have hnn : 0 ≤ E6 / 5 * (10 / π - 4 * Q) := by
    have h2 : 0 < 2 / π := by positivity
    have : 10 / π = 5 * (2 / π) := by ring
    exact mul_nonneg (div_nonneg hE0 (by norm_num)) (by linarith)
  have hint : ∫ x, S2P.Ec f x ^ 4 * (2 / π * S2P.Ec f x ^ 2 - (S2HF.hhat f x).re)
      ≤ E6 / 5 * (10 / π - 4 * Q) := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hT0)
      hmeasT.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hnn hlint
  have eint : ∫ x, S2P.Ec f x ^ 4 * (S2HF.hhat f x).re
      = 2 / π * E6 - ∫ x, S2P.Ec f x ^ 4 * (2 / π * S2P.Ec f x ^ 2 - (S2HF.hhat f x).re) := by
    rw [hE6, ← integral_const_mul, ← integral_sub (hi6.const_mul _) hTi]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    beta_reduce
    ring
  have : E6 / 5 * (10 / π - 4 * Q) = 2 / π * E6 - 4 / 5 * E6 * Q := by ring
  linarith

set_option maxHeartbeats 1000000 in
/-- **Lemma 5.2**: ‖Ef‖₆⁶ Q(f²) ≤ (75π²/8)‖f‖₁² -/
theorem lemma52 (hsin : S2C.SinSeries) (hfm : Measurable f) (hf0 : ∀ θ, 0 ≤ f θ)
    (hper : Periodic f (2 * π)) (hanti : ∀ θ, f (θ + π) = f θ) (hf : MemLp f 2 μI)
    (hB1 : ∫ θ in Ioc 0 (2 * π), f θ ^ 2 = 1)
    {E6 : ℝ} (hEpos : 0 < E6) (hE6 : E6 = ∫ x, S2P.Ec f x ^ 6)
    (hi6 : Integrable (fun x => S2P.Ec f x ^ 6))
    -- second variation [GN22]
    (hsv : ∀ g : ℝ → ℝ, MemLp g 2 μI → Periodic g (2 * π) → (∀ θ, g (θ + π) = g θ) →
      ∫⁻ x, ENNReal.ofReal (5 * (S2P.Ec f x ^ 4 * S2P.Ec g x ^ 2))
        ≤ ENNReal.ofReal (E6 * ((∫ θ in Ioc 0 (2 * π), g θ ^ 2)
          + 4 * (∫ θ in Ioc 0 (2 * π), f θ * g θ) ^ 2)))
    -- ν = (fσ)*³, ‖ν‖₂² = ‖Ef‖₆⁶/(4π²)
    {ν : ℝ × ℝ → ℝ} (hνm : Measurable ν) (hν0 : ∀ y, 0 ≤ ν y)
    (hνL2 : ∫⁻ x, ENNReal.ofReal (ν x ^ 2) = ENNReal.ofReal (E6 / (4 * π ^ 2)))
    -- Plancherel: ⟨ν, h*(fσ)⟩ = (1/4π²)∫(Ef)⁴ĥ
    (hpl : ∫⁻ x, ENNReal.ofReal (ν x) * S5B.conv (fun θ => ENNReal.ofReal (f θ))
        (fun y => ENNReal.ofReal (S2H.hfun f y)) x
      = ENNReal.ofReal (1 / (4 * π ^ 2) * ∫ x, S2P.Ec f x ^ 4 * (S2HF.hhat f x).re)) :
    E6 * S2C.Qa (fun θ => f θ ^ 2) ≤ 75 * π ^ 2 / 8 * (∫ θ in Ioc 0 (2 * π), f θ) ^ 2 := by
  have hp := pi_pos
  have hfi : Integrable f μI := hf.integrable one_le_two
  have hg : Integrable (fun θ => f θ ^ 2) μI := hf.integrable_sq
  have hlow := lower hsin hfm hf0 hper hanti hf hB1 hEpos.le hE6 hi6 hsv
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = S2C.Qa (fun θ => f θ ^ 2) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = ∫ θ in Ioc 0 (2 * π), f θ := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = 1 / (4 * π ^ 2) * ∫ x, S2P.Ec f x ^ 4 * (S2HF.hhat f x).re :=
    ⟨_, rfl⟩
  rw [← hQ, ← hL]
  rw [← hQ] at hlow
  rw [← hP] at hpl
  have hQ0 : 0 ≤ Q := hQ ▸ (S2C.Q_bounds' hsin hg (fun x => sq_nonneg _)).1
  have hL0 : 0 ≤ L := hL ▸ integral_nonneg hf0
  -- Claim
  have hFm : Measurable fun θ => ENNReal.ofReal (f θ) := ENNReal.measurable_ofReal.comp hfm
  have hHm : Measurable fun y => ENNReal.ofReal (S2H.hfun f y) :=
    ENNReal.measurable_ofReal.comp (S2H.hfun_meas hfm)
  have hFp : Periodic (fun θ => ENNReal.ofReal (f θ)) (2 * π) := fun θ => by
    simp only [hper θ]
  have hFa : ∀ θ, (fun θ => ENNReal.ofReal (f θ)) (θ + π) = (fun θ => ENNReal.ofReal (f θ)) θ :=
    fun θ => by simp only [hanti θ]
  have hFL : ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (f θ) = ENNReal.ofReal L := by
    rw [hL, ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0)]
  have hHsupp : ∀ y, 4 ≤ nsq y → (fun y => ENNReal.ofReal (S2H.hfun f y)) y = 0 := by
    intro y hy
    show ENNReal.ofReal (S2H.hfun f y) = 0
    unfold S2H.hfun
    rw [if_neg (show ¬ (y.1 ^ 2 + y.2 ^ 2 < 4) by unfold nsq at hy; linarith)]
    simp
  have hh0 : ∀ y, 0 ≤ S2H.hfun f y := by
    intro y; unfold S2H.hfun
    split_ifs
    · exact mul_nonneg (mul_nonneg (by norm_num) (hf0 _)) (hf0 _)
    · exact le_refl 0
  have hHL : ∫⁻ y, ENNReal.ofReal (S2H.hfun f y) ^ 2 = ENNReal.ofReal (2 * Q) := by
    obtain ⟨hint, heq⟩ := S2H.h_L2_real hf hfm hper
    rw [← hQ] at heq
    rw [← heq, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun y => sq_nonneg _)]
    refine lintegral_congr (fun y => ?_)
    rw [ENNReal.ofReal_pow (hh0 y)]
  have hcb := S5B.conv_bound hFm hFp hFa (by rw [hFL]; exact ENNReal.ofReal_ne_top) hHm hHsupp
  rw [hFL, hHL] at hcb
  have hV : (3 : ℝ≥0∞) * ENNReal.ofReal L ^ 2 * ENNReal.ofReal (2 * Q)
      = ENNReal.ofReal (3 * L ^ 2 * (2 * Q)) := by
    rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 3 * L ^ 2 by positivity),
      ENNReal.ofReal_mul (show (0 : ℝ) ≤ 3 by norm_num), ENNReal.ofReal_pow hL0, ENNReal.ofReal_ofNat]
  rw [hV] at hcb
  obtain ⟨X, hX⟩ : ∃ X, X = ∫⁻ x, S5B.conv (fun θ => ENNReal.ofReal (f θ))
      (fun y => ENNReal.ofReal (S2H.hfun f y)) x ^ 2 := ⟨_, rfl⟩
  rw [← hX] at hcb
  have hXt : X ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((le_mul_of_one_le_left (by positivity) (by norm_num)).trans hcb)
  obtain ⟨T, hT⟩ : ∃ T, T = X.toReal := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := hT ▸ ENNReal.toReal_nonneg
  have hXT : X = ENNReal.ofReal T := by rw [hT, ENNReal.ofReal_toReal hXt]
  have h4T : 4 * T ≤ 3 * L ^ 2 * (2 * Q) := by
    have := ENNReal.toReal_le_of_le_ofReal (by positivity) hcb
    rw [ENNReal.toReal_mul, ← hT] at this
    have h4 : (4 : ℝ≥0∞).toReal = 4 := by norm_num
    rw [h4] at this; exact this
  -- Cauchy–Schwarz
  have hcs : (∫⁻ x, ENNReal.ofReal (ν x) * S5B.conv (fun θ => ENNReal.ofReal (f θ))
        (fun y => ENNReal.ofReal (S2H.hfun f y)) x) ^ 2
      ≤ (∫⁻ x, ENNReal.ofReal (ν x) ^ 2) * ∫⁻ x, S5B.conv (fun θ => ENNReal.ofReal (f θ))
        (fun y => ENNReal.ofReal (S2H.hfun f y)) x ^ 2 :=
    S5B.cs2 volume (ENNReal.measurable_ofReal.comp hνm) (S5B.conv_meas hFm hHm)
  have hν2 : ∫⁻ x, ENNReal.ofReal (ν x) ^ 2 = ENNReal.ofReal (E6 / (4 * π ^ 2)) := by
    rw [← hνL2]; refine lintegral_congr (fun x => ?_); rw [ENNReal.ofReal_pow (hν0 x)]
  rw [hpl, hν2, ← hX, hXT] at hcs
  have hP0' : 1 / (5 * π ^ 2) * E6 * Q ≤ P := by
    rw [hP]
    have : 1 / (5 * π ^ 2) * E6 * Q = 1 / (4 * π ^ 2) * (4 / 5 * E6 * Q) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left hlow (by positivity)
  have hPnn : 0 ≤ P := le_trans (by positivity) hP0'
  have hE4 : 0 ≤ E6 / (4 * π ^ 2) := div_nonneg hEpos.le (by positivity)
  have hP2 : P ^ 2 ≤ E6 / (4 * π ^ 2) * T := by
    rw [← ENNReal.ofReal_pow hPnn, ← ENNReal.ofReal_mul hE4] at hcs
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hE4 hT0)).1 hcs
  have hpair : 1 / (5 * π ^ 2) * E6 * Q ≤ Real.sqrt (E6 / (4 * π ^ 2)) * Real.sqrt T := by
    calc _ ≤ P := hP0'
      _ = Real.sqrt (P ^ 2) := (Real.sqrt_sq hPnn).symm
      _ ≤ Real.sqrt (E6 / (4 * π ^ 2) * T) := Real.sqrt_le_sqrt hP2
      _ = _ := Real.sqrt_mul hE4 T
  have hR : (Real.sqrt 3 / 2 * L * Real.sqrt (2 * Q)) ^ 2 = 3 / 4 * L ^ 2 * (2 * Q) := by
    rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by linarith)]; ring
  have hnhf : Real.sqrt T ≤ Real.sqrt 3 / 2 * L * Real.sqrt (2 * Q) := by
    calc Real.sqrt T ≤ Real.sqrt ((Real.sqrt 3 / 2 * L * Real.sqrt (2 * Q)) ^ 2) :=
          Real.sqrt_le_sqrt (by rw [hR]; linarith)
      _ = _ := Real.sqrt_sq (mul_nonneg (mul_nonneg (by positivity) hL0) (Real.sqrt_nonneg _))
  exact Chains.second_variation_final hEpos hQ0 hL0 (Real.sq_sqrt hE4) (Real.sqrt_nonneg _)
    (Real.sq_sqrt (by linarith)) (Real.sqrt_nonneg _) hnhf (Real.sqrt_nonneg _) hpair

end

end SteinTomas.S5C

#print axioms SteinTomas.S5C.lower
#print axioms SteinTomas.S5C.lemma52
