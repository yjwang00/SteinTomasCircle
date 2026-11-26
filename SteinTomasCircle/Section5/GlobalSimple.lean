import Mathlib
import SteinTomasCircle.Basic.Chains
import SteinTomasCircle.Section4.Pointwise
import SteinTomasCircle.Section4.Master
import SteinTomasCircle.Section2.HFourier
import SteinTomasCircle.Section2.PhiIdentity

/-!
# Section 5 (I): the real form of ĥ and Proposition 5.1

For real-valued antipodal (2π-periodic) f:
* `ek_zero`: E(fθ⁰)(x) = Ef(x) = ∫cos(x·ω)f (real, `S2P.Ec`)
* `ek_conj`: E(fθ^{−2n}) = conj E(fθ^{2n})
* `hhat_real`: ĥ(x) = (2/π)(Ef(x))² − Σ c_n |E(fθ^{2n})(x)|² (real)
* `prop_convolution`: eq:global-simple
-/

namespace SteinTomas.S5A

open Real MeasureTheory Set Function
open scoped ENNReal ComplexConjugate

noncomputable section

local notation "μI" => (volume.restrict (Ioc (0 : ℝ) (2 * π)))

variable {f : ℝ → ℝ}

/-- Translation by π of the integral of a periodic function (values in any normed space) -/
lemma int_shift_pi_c {g : ℝ → ℂ} (hg : Periodic g (2 * π)) :
    ∫ θ in Ioc 0 (2 * π), g (θ + π) = ∫ θ in Ioc 0 (2 * π), g θ := by
  have h2 : (0 : ℝ) ≤ 2 * π := by positivity
  rw [← intervalIntegral.integral_of_le h2, ← intervalIntegral.integral_of_le h2,
    intervalIntegral.integral_comp_add_right (f := g), zero_add,
    show 2 * π + π = π + 2 * π by ring, hg.intervalIntegral_add_eq π 0, zero_add]

lemma dot_pi (x : ℝ × ℝ) (θ : ℝ) :
    x.1 * Real.cos (θ + π) + x.2 * Real.sin (θ + π) = -(x.1 * Real.cos θ + x.2 * Real.sin θ) := by
  rw [Real.cos_add_pi, Real.sin_add_pi]; ring

lemma dot_two_pi (x : ℝ × ℝ) (θ : ℝ) :
    x.1 * Real.cos (θ + 2 * π) + x.2 * Real.sin (θ + 2 * π) = x.1 * Real.cos θ + x.2 * Real.sin θ := by
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- x·ω(θ) -/
def dd (x : ℝ × ℝ) (θ : ℝ) : ℝ := x.1 * Real.cos θ + x.2 * Real.sin θ

set_option maxHeartbeats 1000000 in
/-- Ef = E(fθ⁰) is the real number Ec f -/
theorem ek_zero (hf : MemLp f 2 μI) (hper : Periodic f (2 * π)) (hanti : ∀ θ, f (θ + π) = f θ)
    (x : ℝ × ℝ) : S2HF.Ek f 0 x = (S2P.Ec f x : ℂ) := by
  have hfi : Integrable f μI := hf.integrable one_le_two
  have hcos : Integrable (fun θ => f θ * Real.cos (dd x θ)) μI := by
    have := S2C.bmul hfi (φ := fun θ => Real.cos (dd x θ)) (by unfold dd; fun_prop) (C := 1)
      (fun t => by rw [Real.norm_eq_abs]; exact abs_cos_le_one _)
    exact this.congr (Filter.Eventually.of_forall (fun t => by simp only; ring))
  have hsin : Integrable (fun θ => f θ * Real.sin (dd x θ)) μI := by
    have := S2C.bmul hfi (φ := fun θ => Real.sin (dd x θ)) (by unfold dd; fun_prop) (C := 1)
      (fun t => by rw [Real.norm_eq_abs]; exact abs_sin_le_one _)
    exact this.congr (Filter.Eventually.of_forall (fun t => by simp only; ring))
  -- ∫ f sin(x·ω) = 0
  have hs0 : ∫ θ in Ioc 0 (2 * π), f θ * Real.sin (dd x θ) = 0 := by
    have hp : Periodic (fun θ => f θ * Real.sin (dd x θ)) (2 * π) := by
      intro θ; simp only [dd, hper θ, dot_two_pi]
    have h := S4M.int_shift_pi hp
    have e : ∀ θ, f (θ + π) * Real.sin (dd x (θ + π)) = -(f θ * Real.sin (dd x θ)) := by
      intro θ; simp only [dd, hanti θ, dot_pi, Real.sin_neg]; ring
    simp only [e, integral_neg] at h
    linarith
  have hpt : ∀ θ, Complex.exp (((0 * θ : ℝ) : ℂ) * Complex.I) * S2HF.uf f x θ
      = ((f θ * Real.cos (dd x θ) : ℝ) : ℂ) - ((f θ * Real.sin (dd x θ) : ℝ) : ℂ) * Complex.I := by
    intro θ
    unfold S2HF.uf S2HF.ex
    rw [zero_mul, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    simp only [dd]; push_cast; ring
  unfold S2HF.Ek
  simp_rw [hpt]
  rw [integral_sub hcos.ofReal (hsin.ofReal.mul_const _), integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal, hs0]
  simp only [Complex.ofReal_zero, zero_mul, sub_zero]
  congr 1
  unfold S2P.Ec
  rw [intervalIntegral.integral_of_le (by positivity)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
  simp only [dd]; ring

/-- E(fθ^{−2n}) = conj E(fθ^{2n}) -/
theorem ek_conj (hper : Periodic f (2 * π)) (hanti : ∀ θ, f (θ + π) = f θ) (n : ℕ) (x : ℝ × ℝ) :
    S2HF.Ek f (-S2C.kf n) x = conj (S2HF.Ek f (S2C.kf n) x) := by
  set k := S2C.kf n with hk
  unfold S2HF.Ek
  rw [← integral_conj]
  -- the integrand of conj
  set G : ℝ → ℂ := fun θ => conj (Complex.exp (((k * θ : ℝ) : ℂ) * Complex.I) * S2HF.uf f x θ) with hG
  have hGp : Periodic G (2 * π) := by
    intro θ
    simp only [hG, S2HF.uf, S2HF.ex, hper θ, dot_two_pi]
    congr 2
    rw [show (k * (θ + 2 * π) : ℝ) = k * θ + ((n : ℝ) + 1) * (2 * (2 * π)) by simp only [hk, S2C.kf]; ring]
    rw [show (((k * θ + ((n : ℝ) + 1) * (2 * (2 * π)) : ℝ) : ℂ) * Complex.I)
        = ((k * θ : ℝ) : ℂ) * Complex.I + ((2 * ((n : ℤ) + 1) : ℤ) : ℂ) * (2 * π * Complex.I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [← int_shift_pi_c hGp]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
  simp only [hG, S2HF.uf, S2HF.ex, hanti θ, dot_pi]
  rw [map_mul, map_mul, ← Complex.exp_conj, ← Complex.exp_conj, Complex.conj_ofReal]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [show ((k * (θ + π) : ℝ) : ℂ) * -Complex.I
      = ((-k * θ : ℝ) : ℂ) * Complex.I + ((-((n : ℤ) + 1) : ℤ) : ℂ) * (2 * π * Complex.I) by
    simp only [hk, S2C.kf]; push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  congr 2
  push_cast; ring

/-- Real form of ĥ -/
theorem hhat_real (hsin : S2C.SinSeries) (hf : MemLp f 2 μI) (hfm : Measurable f)
    (hper : Periodic f (2 * π)) (hanti : ∀ θ, f (θ + π) = f θ) (x : ℝ × ℝ) :
    HasSum (fun n => S2C.cQ n * Complex.normSq (S2HF.Ek f (S2C.kf n) x))
      (2 / π * S2P.Ec f x ^ 2 - (S2HF.hhat f x).re) ∧ (S2HF.hhat f x).im = 0 := by
  have h := S2HF.h_fourier hsin hf hfm hper x
  have e : ∀ n, (S2C.cQ n : ℂ) * (S2HF.Ek f (S2C.kf n) x * S2HF.Ek f (-S2C.kf n) x)
      = ((S2C.cQ n * Complex.normSq (S2HF.Ek f (S2C.kf n) x) : ℝ) : ℂ) := by
    intro n
    rw [ek_conj hper hanti n x, Complex.mul_conj]; push_cast; ring
  simp_rw [e, ek_zero hf hper hanti x] at h
  have hre := Complex.reCLM.hasSum h
  have him := Complex.imCLM.hasSum h
  simp only [Complex.reCLM_apply, Complex.imCLM_apply, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im] at hre him
  constructor
  · convert hre using 1
    simp only [sq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
  · have h0 : HasSum (fun _ : ℕ => (0 : ℝ)) 0 := hasSum_zero
    have := h0.unique him
    simp only [sq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at this
    linarith

/-- Proposition 5.1 (prop:convolution, eq:global-simple) -/
theorem prop_convolution (hsin : S2C.SinSeries) {E6 B L Q : ℝ}
    (hf : MemLp f 2 μI) (hB : B = ∫ t in Ioc 0 (2 * π), f t ^ 2)
    (hQ : Q = S2C.Qa (fun θ => f θ ^ 2))
    (hmaster : E6 ≤ Mconc / 16 * (16 * B ^ 3 - 12 * B * S45.Ia f) + 45 * π ^ 2 / 2 * L ^ 2 * Q) :
    E6 ≤ 19 / 16 * Mconc * B ^ 3 + 45 * π ^ 2 / 2 * (L ^ 2 - π ^ 2 / (4 * Real.sqrt 3) * B) * Q := by
  have hB0 : 0 ≤ B := by rw [hB]; exact integral_nonneg (fun t => sq_nonneg _)
  have hI := S45.square_average' hsin hf
  rw [← hB, ← hQ] at hI
  exact Chains.convolution hB0 hI hmaster

end

end SteinTomas.S5A

#print axioms SteinTomas.S5A.hhat_real
#print axioms SteinTomas.S5A.prop_convolution
