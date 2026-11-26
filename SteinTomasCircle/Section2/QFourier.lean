import Mathlib

/-!
# Section 2 (§2.3): eq:Q-Fourier

In angular variables Q(g) = ∫₀^{2π}∫₀^{2π} |sin(t−s)| g(s)g(t) ds dt, and
Q(g) = (2/π)(∫g)² − Σ_{n≥1} c_n |∫ g(s)e^{2ins} ds|², c_n = (4/π)/(4n²−1);
in particular 0 ≤ Q(g) ≤ (2/π)‖g‖₁² (g ≥ 0).
External input: the classical Fourier expansion |sin u| = 2/π − Σ c_n cos(2nu).
-/

namespace SteinTomas.S2C

open Real MeasureTheory Set

noncomputable section

/-- Frequency 2(n+1) -/
def kf (n : ℕ) : ℝ := 2 * ((n : ℝ) + 1)

/-- c_{n+1} = (4/π)/(4(n+1)²−1) -/
def cQ (n : ℕ) : ℝ := 4 / π / (4 * ((n : ℝ) + 1) ^ 2 - 1)

/-- ∫ g(t) cos(2(n+1)t) -/
def Cm (g : ℝ → ℝ) (n : ℕ) : ℝ := ∫ t in Ioc 0 (2 * π), g t * Real.cos (kf n * t)

/-- ∫ g(t) sin(2(n+1)t) -/
def Sm (g : ℝ → ℝ) (n : ℕ) : ℝ := ∫ t in Ioc 0 (2 * π), g t * Real.sin (kf n * t)

/-- Q(g) (angular variables) -/
def Qa (g : ℝ → ℝ) : ℝ :=
  ∫ s in Ioc 0 (2 * π), ∫ t in Ioc 0 (2 * π), |Real.sin (t - s)| * g s * g t

/-- Classical Fourier series |sin u| = 2/π − Σ c_n cos(2nu) (external input) -/
def SinSeries : Prop := ∀ u : ℝ, HasSum (fun n => cQ n * Real.cos (kf n * u)) (2 / π - |Real.sin u|)

lemma cQ_nonneg (n : ℕ) : 0 ≤ cQ n := by
  unfold cQ
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := n.cast_nonneg (α := ℝ); linarith
  apply div_nonneg (by positivity)
  nlinarith

variable {g : ℝ → ℝ}

lemma bmul (hg : Integrable g (volume.restrict (Ioc 0 (2 * π)))) {φ : ℝ → ℝ} (hφ : Continuous φ)
    {C : ℝ} (hb : ∀ x, ‖φ x‖ ≤ C) :
    Integrable (fun x => φ x * g x) (volume.restrict (Ioc 0 (2 * π))) :=
  hg.bdd_mul (c := C) hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb)

lemma int_gcos (hg : Integrable g (volume.restrict (Ioc 0 (2 * π)))) (a : ℝ) :
    Integrable (fun t => g t * Real.cos (a * t)) (volume.restrict (Ioc 0 (2 * π))) := by
  have := bmul hg (φ := fun t => Real.cos (a * t)) (by fun_prop) (C := 1)
    (fun x => by rw [Real.norm_eq_abs]; exact abs_cos_le_one _)
  refine this.congr (Filter.Eventually.of_forall (fun t => ?_))
  simp only; ring

lemma int_gsin (hg : Integrable g (volume.restrict (Ioc 0 (2 * π)))) (a : ℝ) :
    Integrable (fun t => g t * Real.sin (a * t)) (volume.restrict (Ioc 0 (2 * π))) := by
  have := bmul hg (φ := fun t => Real.sin (a * t)) (by fun_prop) (C := 1)
    (fun x => by rw [Real.norm_eq_abs]; exact abs_sin_le_one _)
  refine this.congr (Filter.Eventually.of_forall (fun t => ?_))
  simp only; ring

lemma abs_int_le (hg : Integrable g (volume.restrict (Ioc 0 (2 * π)))) {φ : ℝ → ℝ}
    (hb : ∀ x, |φ x| ≤ 1) :
    |∫ t in Ioc 0 (2 * π), g t * φ t| ≤ ∫ t in Ioc 0 (2 * π), ‖g t‖ := by
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hg.norm (Filter.Eventually.of_forall (fun t => ?_))
  rw [norm_mul, Real.norm_eq_abs (φ t)]
  exact mul_le_of_le_one_right (norm_nonneg _) (hb t)

/-- Inner integral: ∫ₜ (2/π − |sin(t−s)|) g(t) = Σ c_n (cos(k s) C_n + sin(k s) S_n) -/
lemma inner_sum (hsin : SinSeries) (hg : Integrable g (volume.restrict (Ioc 0 (2 * π)))) (s : ℝ) :
    HasSum (fun n => cQ n * (Real.cos (kf n * s) * Cm g n + Real.sin (kf n * s) * Sm g n))
      (∫ t in Ioc 0 (2 * π), (2 / π - |Real.sin (t - s)|) * g t) := by
  set μ := volume.restrict (Ioc (0 : ℝ) (2 * π)) with hμ
  have hcs : Summable cQ := by
    have := (hsin 0).summable
    simpa using this
  have hFi : ∀ n, Integrable (fun t => cQ n * Real.cos (kf n * (t - s)) * g t) μ := by
    intro n
    refine bmul hg (φ := fun t => cQ n * Real.cos (kf n * (t - s))) (by fun_prop) (C := cQ n)
      (fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (cQ_nonneg n)]
    exact mul_le_of_le_one_right (cQ_nonneg n) (abs_cos_le_one _)
  have hle : ∀ n, ∫ t, ‖cQ n * Real.cos (kf n * (t - s)) * g t‖ ∂μ ≤ cQ n * ∫ t, ‖g t‖ ∂μ := by
    intro n
    rw [← MeasureTheory.integral_const_mul]
    refine integral_mono (hFi n).norm (hg.norm.const_mul _) (fun t => ?_)
    simp only
    rw [norm_mul, norm_mul, Real.norm_eq_abs (cQ n), abs_of_nonneg (cQ_nonneg n),
      Real.norm_eq_abs (Real.cos _)]
    have := abs_cos_le_one (kf n * (t - s))
    have h0 := cQ_nonneg n
    have h1 := norm_nonneg (g t)
    nlinarith [mul_nonneg h0 h1]
  have hsum : Summable (fun n => ∫ t, ‖cQ n * Real.cos (kf n * (t - s)) * g t‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg (fun t => norm_nonneg _)) hle
      (hcs.mul_right _)
  have hHS := hasSum_integral_of_summable_integral_norm hFi hsum
  have htsum : (fun t => ∑' n, cQ n * Real.cos (kf n * (t - s)) * g t)
      = fun t => (2 / π - |Real.sin (t - s)|) * g t := by
    funext t; exact ((hsin (t - s)).mul_right (g t)).tsum_eq
  have hint : (fun n => ∫ t, cQ n * Real.cos (kf n * (t - s)) * g t ∂μ)
      = fun n => cQ n * (Real.cos (kf n * s) * Cm g n + Real.sin (kf n * s) * Sm g n) := by
    funext n
    have e : (fun t => cQ n * Real.cos (kf n * (t - s)) * g t)
        = fun t => cQ n * Real.cos (kf n * s) * (g t * Real.cos (kf n * t))
          + cQ n * Real.sin (kf n * s) * (g t * Real.sin (kf n * t)) := by
      funext t; rw [mul_sub, Real.cos_sub]; ring
    rw [e, MeasureTheory.integral_add ((int_gcos hg _).const_mul _) ((int_gsin hg _).const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    unfold Cm Sm
    ring
  rw [hint, htsum] at hHS
  exact hHS

set_option maxHeartbeats 1000000 in
/-- Outer integral: ∫ₛ (∫ₜ (2/π−|sin(t−s)|)g(t)) g(s) = Σ c_n (C_n² + S_n²) -/
lemma outer_sum (hsin : SinSeries) (hg : Integrable g (volume.restrict (Ioc 0 (2 * π)))) :
    HasSum (fun n => cQ n * (Cm g n ^ 2 + Sm g n ^ 2))
      (∫ s in Ioc 0 (2 * π), (∫ t in Ioc 0 (2 * π), (2 / π - |Real.sin (t - s)|) * g t) * g s) := by
  set μ := volume.restrict (Ioc (0 : ℝ) (2 * π)) with hμ
  obtain ⟨A, hA⟩ : ∃ A, A = ∫ t, ‖g t‖ ∂μ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; exact integral_nonneg (fun t => norm_nonneg _)
  have hcs : Summable cQ := by
    have := (hsin 0).summable
    simpa using this
  have hC : ∀ n, |Cm g n| ≤ A := fun n => by rw [hA]; exact abs_int_le hg (fun x => abs_cos_le_one _)
  have hS : ∀ n, |Sm g n| ≤ A := fun n => by rw [hA]; exact abs_int_le hg (fun x => abs_sin_le_one _)
  have hb : ∀ n x, ‖cQ n * (Real.cos (kf n * x) * Cm g n + Real.sin (kf n * x) * Sm g n)‖
      ≤ cQ n * (2 * A) := by
    intro n x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cQ_nonneg n)]
    apply mul_le_mul_of_nonneg_left _ (cQ_nonneg n)
    have h1 : |Real.cos (kf n * x) * Cm g n| ≤ A := by
      rw [abs_mul]
      exact le_trans (mul_le_of_le_one_left (abs_nonneg _) (abs_cos_le_one _)) (hC n)
    have h2 : |Real.sin (kf n * x) * Sm g n| ≤ A := by
      rw [abs_mul]
      exact le_trans (mul_le_of_le_one_left (abs_nonneg _) (abs_sin_le_one _)) (hS n)
    linarith [abs_add_le (Real.cos (kf n * x) * Cm g n) (Real.sin (kf n * x) * Sm g n)]
  have hGi : ∀ n, Integrable (fun s => cQ n * (Real.cos (kf n * s) * Cm g n
      + Real.sin (kf n * s) * Sm g n) * g s) μ :=
    fun n => bmul hg (φ := fun s => cQ n * (Real.cos (kf n * s) * Cm g n
      + Real.sin (kf n * s) * Sm g n)) (by fun_prop) (hb n)
  have hle : ∀ n, ∫ s, ‖cQ n * (Real.cos (kf n * s) * Cm g n
      + Real.sin (kf n * s) * Sm g n) * g s‖ ∂μ ≤ cQ n * (2 * A * A) := by
    intro n
    calc ∫ s, ‖cQ n * (Real.cos (kf n * s) * Cm g n
          + Real.sin (kf n * s) * Sm g n) * g s‖ ∂μ
        ≤ ∫ s, cQ n * (2 * A) * ‖g s‖ ∂μ := by
          refine integral_mono (hGi n).norm (hg.norm.const_mul _) (fun s => ?_)
          simp only
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hb n s) (norm_nonneg _)
      _ = cQ n * (2 * A * A) := by
          rw [MeasureTheory.integral_const_mul, ← hA]; ring
  have hsum : Summable (fun n => ∫ s, ‖cQ n * (Real.cos (kf n * s) * Cm g n
      + Real.sin (kf n * s) * Sm g n) * g s‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg (fun t => norm_nonneg _)) hle
      (hcs.mul_right _)
  have hHS := hasSum_integral_of_summable_integral_norm hGi hsum
  have htsum : (fun s => ∑' n, cQ n * (Real.cos (kf n * s) * Cm g n
      + Real.sin (kf n * s) * Sm g n) * g s)
      = fun s => (∫ t, (2 / π - |Real.sin (t - s)|) * g t ∂μ) * g s := by
    funext s; exact ((inner_sum hsin hg s).mul_right (g s)).tsum_eq
  have hint : (fun n => ∫ s, cQ n * (Real.cos (kf n * s) * Cm g n
      + Real.sin (kf n * s) * Sm g n) * g s ∂μ) = fun n => cQ n * (Cm g n ^ 2 + Sm g n ^ 2) := by
    funext n
    have e : (fun s => cQ n * (Real.cos (kf n * s) * Cm g n + Real.sin (kf n * s) * Sm g n) * g s)
        = fun s => cQ n * Cm g n * (g s * Real.cos (kf n * s))
          + cQ n * Sm g n * (g s * Real.sin (kf n * s)) := by
      funext s; ring
    rw [e, MeasureTheory.integral_add ((int_gcos hg _).const_mul _) ((int_gsin hg _).const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    unfold Cm Sm
    ring
  rw [hint, htsum] at hHS
  exact hHS

/-- eq:Q-Fourier: Σ c_n |ĝ(2n)|² = (2/π)(∫g)² − Q(g) -/
theorem Q_fourier (hsin : SinSeries) (hg : Integrable g (volume.restrict (Ioc 0 (2 * π)))) :
    HasSum (fun n => cQ n * (Cm g n ^ 2 + Sm g n ^ 2))
      (2 / π * (∫ t in Ioc 0 (2 * π), g t) ^ 2 - Qa g) := by
  set μ := volume.restrict (Ioc (0 : ℝ) (2 * π)) with hμ
  set J : ℝ → ℝ := fun s => ∫ t, |Real.sin (t - s)| * g t ∂μ with hJ
  have hsg : ∀ s, Integrable (fun t => |Real.sin (t - s)| * g t) μ := by
    intro s
    exact bmul hg (φ := fun t => |Real.sin (t - s)|) (by fun_prop) (C := 1)
      (fun x => by rw [Real.norm_eq_abs, abs_abs]; exact abs_sin_le_one _)
  have hJc : Continuous J := by
    apply continuous_of_dominated (bound := fun t => ‖g t‖)
    · intro s; exact (hsg s).aestronglyMeasurable
    · intro s
      filter_upwards with t
      rw [norm_mul, Real.norm_eq_abs (|Real.sin _|), abs_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_sin_le_one _)
    · exact hg.norm
    · filter_upwards with t
      fun_prop
  have hJb : ∀ s, ‖J s‖ ≤ ∫ t, ‖g t‖ ∂μ := by
    intro s
    refine norm_integral_le_of_norm_le hg.norm (Filter.Eventually.of_forall (fun t => ?_))
    rw [norm_mul, Real.norm_eq_abs (|Real.sin _|), abs_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_sin_le_one _)
  have hJg : Integrable (fun s => J s * g s) μ := bmul hg hJc hJb
  have hinner : ∀ s, ∫ t, (2 / π - |Real.sin (t - s)|) * g t ∂μ
      = 2 / π * (∫ t, g t ∂μ) - J s := by
    intro s
    have e : (fun t => (2 / π - |Real.sin (t - s)|) * g t)
        = fun t => 2 / π * g t - |Real.sin (t - s)| * g t := by funext t; ring
    rw [e, MeasureTheory.integral_sub (hg.const_mul _) (hsg s), MeasureTheory.integral_const_mul]
  have hQ : Qa g = ∫ s, J s * g s ∂μ := by
    unfold Qa
    refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
    simp only [hJ]
    have e : (fun t => |Real.sin (t - s)| * g s * g t) = fun t => g s * (|Real.sin (t - s)| * g t) := by
      funext t; ring
    rw [e, MeasureTheory.integral_const_mul]; ring
  have h := outer_sum hsin hg
  have e2 : (∫ s, (∫ t, (2 / π - |Real.sin (t - s)|) * g t ∂μ) * g s ∂μ)
      = 2 / π * (∫ t, g t ∂μ) ^ 2 - Qa g := by
    have e : (fun s => (∫ t, (2 / π - |Real.sin (t - s)|) * g t ∂μ) * g s)
        = fun s => (2 / π * (∫ t, g t ∂μ)) * g s - J s * g s := by
      funext s; rw [hinner s]; ring
    rw [e, MeasureTheory.integral_sub (hg.const_mul _) hJg, MeasureTheory.integral_const_mul, hQ]
    ring
  rw [e2] at h
  exact h

/-- Corollary: 0 ≤ Q(g) ≤ (2/π)‖g‖₁² (g ≥ 0) -/
theorem Q_bounds' (hsin : SinSeries) (hg : Integrable g (volume.restrict (Ioc 0 (2 * π))))
    (hg0 : ∀ x, 0 ≤ g x) :
    0 ≤ Qa g ∧ Qa g ≤ 2 / π * (∫ t in Ioc 0 (2 * π), g t) ^ 2 := by
  constructor
  · unfold Qa
    refine integral_nonneg (fun s => integral_nonneg (fun t => ?_))
    have := hg0 s; have := hg0 t
    positivity
  · have h := Q_fourier hsin hg
    have := h.nonneg (fun n => mul_nonneg (cQ_nonneg n) (by positivity))
    linarith

end

end SteinTomas.S2C

#print axioms SteinTomas.S2C.Q_fourier
#print axioms SteinTomas.S2C.Q_bounds'
