import Mathlib
import SteinTomasCircle.Basic.Elementary
import SteinTomasCircle.Section4.FourSign

/-!
# Sharp endpoint Stein–Tomas inequality on the circle: definitions

Conventions (as in the paper):
* Functions on the circle are parametrized by the angle: `f : ℝ → ℂ`, only values on `(0, 2π]` are used; `σ` is Lebesgue measure on this interval
  (the pull-back of arc length dσ under θ ↦ e^{iθ}).
* `Ef(x) = ∫ e^{-i x·ω} f(ω) dσ(ω)`, x ∈ ℝ² (as `ℝ × ℝ`; note that Mathlib's norm on `ℝ × ℝ` is the sup norm,
  so the squared Euclidean length is always written `x.1^2 + x.2^2`).
* The sixth-power norm and the L² norm are `ℝ≥0∞`-valued (lintegral / eLpNorm), avoiding the convention that a non-integrable function has integral 0.
* Bessel functions are defined by the integral representation DLMF 10.9.2; the power series, the bound 10.14.4 etc. are literature hypotheses.
-/

namespace SteinTomas

open Real MeasureTheory Complex
open scoped ENNReal

noncomputable section

/-! ## Basic objects -/

/-- The point ω(θ) = (cos θ, sin θ) of the circle with parameter θ -/
def pt (θ : ℝ) : ℝ × ℝ := (Real.cos θ, Real.sin θ)

/-- Arc-length measure (angular parameter) -/
def σ : Measure ℝ := volume.restrict (Set.Ioc 0 (2 * π))

/-- Euclidean inner product x · ω(θ) -/
def dotθ (x : ℝ × ℝ) (θ : ℝ) : ℝ := x.1 * Real.cos θ + x.2 * Real.sin θ

/-- Squared Euclidean length |x|² -/
def nsq (x : ℝ × ℝ) : ℝ := x.1 ^ 2 + x.2 ^ 2

/-- det(ω, η) -/
def det2 (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

/-- Extension operator Ef(x) = ∫ e^{-i x·ω} f(ω) dσ(ω) -/
def E (f : ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  ∫ θ, Complex.exp (-(dotθ x θ : ℂ) * I) * f θ ∂σ

/-- ‖Ef‖₆⁶ (with values in [0, ∞]) -/
def ext6 (f : ℝ → ℂ) : ℝ≥0∞ := ∫⁻ x : ℝ × ℝ, ‖E f x‖ₑ ^ 6

/-- ‖f‖_{L²(σ)} -/
def L2n (f : ℝ → ℂ) : ℝ≥0∞ := eLpNorm f 2 σ

/-- ‖f‖_{L¹(σ)} -/
def L1n (f : ℝ → ℂ) : ℝ≥0∞ := eLpNorm f 1 σ

/-- Antipodal symmetry: f(θ + π) = f(θ) -/
def Antipodal (f : ℝ → ℂ) : Prop := ∀ θ, f (θ + π) = f θ

/-- Real-valued and nonnegative -/
def NonnegReal (f : ℝ → ℂ) : Prop := ∀ θ, (f θ).im = 0 ∧ 0 ≤ (f θ).re

/-- f is a maximizer: f ∈ L², f ≠ 0, and ‖Eg‖₆⁶‖f‖₂⁶ ≤ ‖Ef‖₆⁶‖g‖₂⁶ for all g ∈ L² -/
def IsMaximizer (f : ℝ → ℂ) : Prop :=
  MemLp f 2 σ ∧ L2n f ≠ 0 ∧ ∀ g, MemLp g 2 σ → ext6 g * L2n f ^ 6 ≤ ext6 f * L2n g ^ 6

/-- Bessel function J_n (defined by the integral representation DLMF 10.9.2) -/
def J (n : ℤ) (r : ℝ) : ℝ := (1 / π) * ∫ θ in (0 : ℝ)..π, Real.cos (r * Real.sin θ - n * θ)

/-- α_{2n} = ∫₀^∞ J₀⁴ J_{2n}² r dr -/
def α (n : ℕ) : ℝ := ∫ r in Set.Ioi (0 : ℝ), J 0 r ^ 4 * J (2 * n) r ^ 2 * r

/-- M_conc = 20π³/√3 -/
def Mconc : ℝ := 20 * π ^ 3 / Real.sqrt 3

/-- Q(g) = ∬ |det(ω,η)| g(ω) g(η) dσ dσ (g ≥ 0 real-valued) -/
def Qf (g : ℝ → ℝ) : ℝ := ∫ s, ∫ t, |Real.sin (t - s)| * g s * g t ∂σ ∂σ

/-- I(f) = ∬ |det(ω,η)|² f(ω)² f(η)² dσ dσ -/
def If (f : ℝ → ℝ) : ℝ := ∫ s, ∫ t, Real.sin (t - s) ^ 2 * f s ^ 2 * f t ^ 2 ∂σ ∂σ

/-- Mean a₀ = ⟨f, e₀⟩ = (2π)^{-1/2} ∫ f dσ -/
def a0 (f : ℝ → ℝ) : ℝ := (1 / Real.sqrt (2 * π)) * ∫ θ, f θ ∂σ

/-- A real function regarded as a complex function -/
def toC (f : ℝ → ℝ) : ℝ → ℂ := fun θ => (f θ : ℂ)

/-- 𝒫 (§4, eq:P-definition); ψ is taken from Elementary.lean -/
def Pw (x : ℝ × ℝ) : ℝ :=
  if 1 < Real.sqrt (nsq x) ∧ Real.sqrt (nsq x) < 3 then
    (nsq x - 1) * (9 - nsq x) * ψ (nsq x - 1) else 0

/-! ## Main results
The complete statements with literature hypotheses, and their proofs, are in:
* Theorem 1.1: `S6.thm_main` (complex-valued), `S6.thm_main_real` (compactness argument)
* Theorem 1.2: `S6.thm_L1_remainder` (complex-valued), `S4M.L1_remainder_sym` (nonnegative antipodal)
* Proposition 3.1: `S2W.prop_large_mean_full`; Proposition 5.3: `S5D.prop_small_mean'`
-/

/-! ### Vector form of Lemma 4.3: reduction to the algebraic form proved in FourSign.lean -/

lemma ψ_same (l : ℝ) : FourSign.ψ l = ψ l := rfl

lemma Pw_eq (x : ℝ × ℝ) : Pw x = FourSign.Pl (nsq x - 1) := by
  have iff : (1 < Real.sqrt (nsq x) ∧ Real.sqrt (nsq x) < 3) ↔
      (0 < nsq x - 1 ∧ nsq x - 1 < 8) := by
    rw [Real.lt_sqrt (by norm_num), Real.sqrt_lt' (by norm_num)]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith
  unfold Pw FourSign.Pl
  by_cases h : 1 < Real.sqrt (nsq x) ∧ Real.sqrt (nsq x) < 3
  · rw [if_pos h, if_pos (iff.mp h), ψ_same]; ring
  · rw [if_neg h, if_neg (fun h' => h (iff.mpr h'))]

lemma term_eq (u v w : ℝ × ℝ) (hu : nsq u = 1) (hv : nsq v = 1) (hw : nsq w = 1)
    (ε δ : ℝ) (hε : ε ^ 2 = 1) (hδ : δ ^ 2 = 1) :
    Pw (ε • u + δ • v + w) * (1 + if nsq (ε • u + δ • v + (2 : ℝ) • w) ≤ 4 then 1 else 0)
      = FourSign.Pl (2 * (1 + ε * δ * (u.1 * v.1 + u.2 * v.2) + ε * (u.1 * w.1 + u.2 * w.2)
          + δ * (v.1 * w.1 + v.2 * w.2)))
        * (1 + FourSign.ind (1 + ε * δ * (u.1 * v.1 + u.2 * v.2)
          + 2 * ε * (u.1 * w.1 + u.2 * w.2) + 2 * δ * (v.1 * w.1 + v.2 * w.2))) := by
  unfold nsq at hu hv hw
  have hx : nsq (ε • u + δ • v + w) - 1 = 2 * (1 + ε * δ * (u.1 * v.1 + u.2 * v.2)
      + ε * (u.1 * w.1 + u.2 * w.2) + δ * (v.1 * w.1 + v.2 * w.2)) := by
    simp only [nsq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination ε ^ 2 * hu + hε + δ ^ 2 * hv
      + hδ + hw
  have hy : nsq (ε • u + δ • v + (2 : ℝ) • w) = 4 + 2 * (1 + ε * δ * (u.1 * v.1 + u.2 * v.2)
      + 2 * ε * (u.1 * w.1 + u.2 * w.2) + 2 * δ * (v.1 * w.1 + v.2 * w.2)) := by
    simp only [nsq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination ε ^ 2 * hu + hε + δ ^ 2 * hv
      + hδ + 4 * hw
  rw [Pw_eq, hx, hy]
  congr 2
  unfold FourSign.ind
  by_cases h : 1 + ε * δ * (u.1 * v.1 + u.2 * v.2) + 2 * ε * (u.1 * w.1 + u.2 * w.2)
      + 2 * δ * (v.1 * w.1 + v.2 * w.2) ≤ 0
  · rw [if_pos h, if_pos (by linarith)]
  · rw [if_neg h, if_neg (by intro h'; apply h; linarith)]

/-- Lemma 4.3 (lem:four-sign), purely geometric, no literature input. Fully proved. -/
theorem lem_four_sign (u v w : ℝ × ℝ) (hu : nsq u = 1) (hv : nsq v = 1) (hw : nsq w = 1) :
    (∑ ε ∈ ({-1, 1} : Finset ℝ), ∑ δ ∈ ({-1, 1} : Finset ℝ),
      Pw (ε • u + δ • v + w) *
        (1 + if nsq (ε • u + δ • v + (2 : ℝ) • w) ≤ 4 then 1 else 0))
      ≤ 2 * (|det2 u v| + |det2 u w| + |det2 v w|) ^ 2 := by
  have hne : (-1 : ℝ) ≠ 1 := by norm_num
  rw [Finset.sum_pair hne, Finset.sum_pair hne, Finset.sum_pair hne]
  rw [term_eq u v w hu hv hw (-1) (-1) (by norm_num) (by norm_num),
    term_eq u v w hu hv hw (-1) 1 (by norm_num) (by norm_num),
    term_eq u v w hu hv hw 1 (-1) (by norm_num) (by norm_num),
    term_eq u v w hu hv hw 1 1 (by norm_num) (by norm_num)]
  unfold nsq at hu hv hw
  have key := FourSign.four_sign_alg (u.1 * v.1 + u.2 * v.2) (u.1 * w.1 + u.2 * w.2)
    (v.1 * w.1 + v.2 * w.2) (det2 u v) (det2 u w) (det2 v w)
    (by unfold det2; linear_combination (v.1 ^ 2 + v.2 ^ 2) * hu + hv)
    (by unfold det2; linear_combination (w.1 ^ 2 + w.2 ^ 2) * hu + hw)
    (by unfold det2; linear_combination (w.1 ^ 2 + w.2 ^ 2) * hv + hw)
    (by unfold det2; linear_combination (v.1 * w.1 + v.2 * w.2) * hu)
    (by unfold det2; linear_combination (-(u.1 * w.1 + u.2 * w.2)) * hv)
    (by unfold det2; linear_combination (u.1 * v.1 + u.2 * v.2) * hw)
  unfold FourSign.lhs at key
  convert key using 1
  ring_nf

end

end SteinTomas
