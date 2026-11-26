import Mathlib
import SteinTomasCircle.Section2.FourierSeries

/-!
# Section 2 (§2.1): Fourier coefficients of Ef in polar coordinates

For real-valued antipodal f, Ef(x) = ∫ e^{−ix·ω} f(ω)dσ(ω) is real; in polar coordinates x = r(cos φ, sin φ),
Ef(r,φ) = ∫₀^{2π} cos(r cos(θ−φ)) f(θ) dθ (`Ep`).
* `coef_Ep`: the Fourier coefficients of φ ↦ Ef(r,φ) are 2π·f̂(n)·κ_{−n}(r), where κ_n(r) are the coefficients of the kernel cos(r cos u)
  (by DLMF 10.9.2, κ_{2m}(r) = (−1)^m J_{2m}(r), used later as external input)
* `Ep_continuous`, `Ep_memLp`, `parseval_Ep`: φ ↦ Ef(r,φ) is continuous, so Parseval applies
-/

namespace SteinTomas.S2K

open Real MeasureTheory Complex SteinTomas.S2F

noncomputable section

/-- Ef in polar coordinates -/
def Ep (f : ℝ → ℝ) (r φ : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * π), Real.cos (r * Real.cos (θ - φ)) * f θ

/-- Fourier coefficients κ_n(r) of the kernel cos(r cos u) -/
def kc (r : ℝ) (n : ℤ) : ℂ := coef (fun u => Real.cos (r * Real.cos u)) n

lemma norm_exp_mul_I (n : ℤ) (x : ℝ) : ‖Complex.exp (-(n : ℂ) * x * I)‖ = 1 := by
  have : -(n : ℂ) * x * I = ((-(n : ℝ) * x : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-- Fourier coefficients of φ ↦ Ef(r,φ) -/
theorem coef_Ep {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) (r : ℝ)
    (n : ℤ) : coef (Ep f r) n = 2 * π * coef f n * kc r (-n) := by
  set K : ℝ → ℝ := fun u => Real.cos (r * Real.cos u) with hK
  have hKper : ∀ u, K (u + 2 * π) = K u := by intro u; simp only [hK, Real.cos_add_two_pi]
  have hfi := intervalIntegrable_of_memLp hf
  have hp : (0 : ℝ) ≤ 2 * π := by positivity
  set G : ℝ → ℝ → ℂ := fun φ θ => Complex.exp (-(n : ℂ) * φ * I) * ((K (θ - φ) * f θ : ℝ) : ℂ)
    with hG
  -- step 1: write as a double integral
  have step1 : coef (Ep f r) n
      = ((1 / (2 * π) : ℝ) : ℂ) * ∫ φ in (0 : ℝ)..(2 * π), ∫ θ in (0 : ℝ)..(2 * π), G φ θ := by
    rw [coef_eq]
    congr 1
    apply intervalIntegral.integral_congr
    intro φ _
    simp only [hG, Ep]
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
  -- step 2: exchange the order of integration
  set s := Set.uIoc (0 : ℝ) (2 * π) with hs
  have hs' : s = Set.Ioc 0 (2 * π) := Set.uIoc_of_le hp
  have hfin : IsFiniteMeasure (volume.restrict s) := by
    rw [hs']; exact isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hfs : Integrable (fun θ => ((f θ : ℝ) : ℂ)) (volume.restrict s) := by
    rw [hs']; exact Integrable.ofReal hfi.1
  have h1 : Integrable (fun p : ℝ × ℝ => ((f p.2 : ℝ) : ℂ))
      ((volume.restrict s).prod (volume.restrict s)) := hfs.comp_snd _
  have h2 : Integrable (fun p : ℝ × ℝ => (Complex.exp (-(n : ℂ) * p.1 * I) * ((K (p.2 - p.1) : ℝ) : ℂ))
      * ((f p.2 : ℝ) : ℂ)) ((volume.restrict s).prod (volume.restrict s)) := by
    refine h1.bdd_mul (c := 1) ?_ ?_
    · exact (Continuous.aestronglyMeasurable (by simp only [hK]; fun_prop))
    · filter_upwards with p
      rw [norm_mul, norm_exp_mul_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
      exact Real.abs_cos_le_one _
  have hint : IntegrableOn (Function.uncurry G) (s ×ˢ s) := by
    show Integrable _ (volume.restrict (s ×ˢ s))
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    refine h2.congr ?_
    filter_upwards with p
    simp only [Function.uncurry, hG]
    push_cast; ring
  have step2 := MeasureTheory.intervalIntegral_intervalIntegral_swap hint
  -- step 3: inner integral
  have step3 : ∀ θ : ℝ, ∫ φ in (0 : ℝ)..(2 * π), G φ θ
      = ((f θ : ℝ) : ℂ) * (Complex.exp (-(n : ℂ) * θ * I) * ((2 * π : ℝ) : ℂ) * kc r (-n)) := by
    intro θ
    set g : ℝ → ℂ := fun u => Complex.exp (-(n : ℂ) * ((θ - u : ℝ) : ℂ) * I) * ((K u : ℝ) : ℂ)
      with hg
    have hgper : Function.Periodic g (2 * π) := by
      intro u
      simp only [hg, hKper u]
      have e : -(n : ℂ) * ((θ - (u + 2 * π) : ℝ) : ℂ) * I
          = -(n : ℂ) * ((θ - u : ℝ) : ℂ) * I + (n : ℂ) * (2 * π * I) := by push_cast; ring
      rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have hsub : ∫ φ in (0 : ℝ)..(2 * π), G φ θ
        = ((f θ : ℝ) : ℂ) * ∫ φ in (0 : ℝ)..(2 * π), g (θ - φ) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro φ _
      simp only [hG, hg]
      have : θ - (θ - φ) = φ := by ring
      rw [this]
      push_cast; ring
    rw [hsub, intervalIntegral.integral_comp_sub_left (fun u => g u) θ, sub_zero]
    have hshift := hgper.intervalIntegral_add_eq (θ - 2 * π) 0
    rw [show θ - 2 * π + 2 * π = θ by ring, zero_add] at hshift
    rw [hshift]
    have hk : kc r (-n) = ((1 / (2 * π) : ℝ) : ℂ)
        * ∫ u in (0 : ℝ)..(2 * π), Complex.exp (-((-n : ℤ) : ℂ) * u * I) * ((K u : ℝ) : ℂ) := by
      rw [kc, coef_eq]
    have hgu : ∀ u : ℝ, g u = Complex.exp (-(n : ℂ) * θ * I)
        * (Complex.exp (-((-n : ℤ) : ℂ) * u * I) * ((K u : ℝ) : ℂ)) := by
      intro u
      simp only [hg]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast; ring
    simp_rw [hgu]
    rw [intervalIntegral.integral_const_mul, hk]
    have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
    push_cast
    field_simp
  -- combine
  rw [step1, step2]
  simp_rw [step3]
  have hcoef := coef_eq f n
  have e : ∀ θ : ℝ, ((f θ : ℝ) : ℂ) * (Complex.exp (-(n : ℂ) * θ * I) * ((2 * π : ℝ) : ℂ) * kc r (-n))
      = (((2 * π : ℝ) : ℂ) * kc r (-n)) * (Complex.exp (-(n : ℂ) * θ * I) * ((f θ : ℝ) : ℂ)) := by
    intro θ; ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, hcoef]
  push_cast
  ring

/-- φ ↦ Ef(r,φ) is continuous -/
theorem Ep_continuous {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) (r : ℝ) :
    Continuous (Ep f r) := by
  have hfi := intervalIntegrable_of_memLp hf
  have e : Ep f r = fun φ => ∫ θ in Set.Ioc 0 (2 * π), Real.cos (r * Real.cos (θ - φ)) * f θ := by
    funext φ
    rw [Ep, intervalIntegral.integral_of_le (by positivity)]
  rw [e]
  apply continuous_of_dominated (bound := fun θ => ‖f θ‖)
  · intro φ
    exact (Continuous.aestronglyMeasurable (by fun_prop)).mul hfi.1.aestronglyMeasurable
  · intro φ
    filter_upwards with θ
    rw [norm_mul]
    have : ‖Real.cos (r * Real.cos (θ - φ))‖ ≤ 1 := by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
    nlinarith [norm_nonneg (f θ)]
  · exact hfi.1.norm
  · filter_upwards with θ
    fun_prop

/-- |Ef(r,φ)| ≤ ∫|f| -/
theorem Ep_bound {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) (r φ : ℝ) :
    ‖Ep f r φ‖ ≤ ∫ θ in (0 : ℝ)..(2 * π), ‖f θ‖ := by
  have hfi := intervalIntegrable_of_memLp hf
  rw [Ep]
  refine (intervalIntegral.norm_integral_le_integral_norm (by positivity)).trans ?_
  apply intervalIntegral.integral_mono_on (by positivity)
  · exact (hfi.continuousOn_mul (Continuous.continuousOn (by fun_prop))).norm
  · exact hfi.norm
  · intro θ _
    rw [norm_mul]
    have : ‖Real.cos (r * Real.cos (θ - φ))‖ ≤ 1 := by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
    nlinarith [norm_nonneg (f θ)]

/-- φ ↦ Ef(r,φ) ∈ L²(0,2π] -/
theorem Ep_memLp {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) (r : ℝ) :
    MemLp (Ep f r) 2 (volume.restrict (Set.Ioc 0 (2 * π))) := by
  have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  exact MemLp.of_bound (Ep_continuous hf r).aestronglyMeasurable _
    (Filter.Eventually.of_forall (fun φ => Ep_bound hf r φ))

/-- Parseval: Σ_n |2π f̂(n) κ_{−n}(r)|² = (1/2π)∫₀^{2π} Ef(r,φ)² dφ -/
theorem parseval_Ep {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) (r : ℝ) :
    HasSum (fun n => ‖2 * π * coef f n * kc r (-n)‖ ^ 2)
      ((1 / (2 * π)) * ∫ φ in (0 : ℝ)..(2 * π), Ep f r φ ^ 2) := by
  have h := parseval (Ep_memLp hf r)
  simp_rw [coef_Ep hf r] at h
  exact h

end

end SteinTomas.S2K

#print axioms SteinTomas.S2K.coef_Ep
#print axioms SteinTomas.S2K.parseval_Ep
