import SteinTomasCircle.MainProof.Optimality

/-!
# Inputs from the literature

The formalization follows the convention that results quoted from the literature are
*hypotheses*, while every argument of the paper itself is proved in Lean.
This file bundles all such hypotheses used by the main theorems into one structure,
`LiteratureInputs`. Each field is a `Prop` defined elsewhere in the project; the comment
next to each field states the result it encodes and where it comes from.

To audit the formalization it suffices to read
* this file and the definitions it refers to, and
* the statements in `SteinTomasCircle/MainTheorems.lean`.
-/

namespace SteinTomasCircle

open MeasureTheory SteinTomas

/-- All results from the literature used in the proofs of Theorems 1.1 and 1.2. -/
structure LiteratureInputs : Prop where
  /-- Classical Fourier series of `|sin u|`:
  `|sin u| = 2/π − Σ_{n≥1} (4/π) cos(2nu)/(4n²−1)`. -/
  sinSeries : S2C.SinSeries
  /-- Properties of the Bessel functions `J_{2n}` (defined in `Basic/Defs.lean` by the integral
  representation DLMF 10.9.2): the kernel identity, continuity, the zero set of `J₀` is null,
  the series bounds behind Lemma 2.1, DLMF 10.14.4, integrability of `J₀⁴J_{2n}²r`, and the
  numerical values of `α_{2n}` from [CFOT17, Table 1] and [OT17]. -/
  bessel : S6.BesselLit S6.evenBessel
  /-- The density `ρ` of `σ*σ*σ` and its closed form in terms of the complete elliptic
  integral [BSWZ12], [Bec25]. -/
  rho : ∃ (ρ : ℝ × ℝ → ℝ) (ρr : ℝ → ℝ), S6.RhoData ρ ρr
  /-- The Tomas–Stein inequality `‖Ef‖₆ ≲ ‖f‖₂` (for the real cosine transform). -/
  steinTomas : S6.ClassicalSteinTomas
  /-- For admissible `g`, the density `ν` of `(gσ)*³`, its `L²` norm `‖ν‖₂² = ‖Eg‖₆⁶/(4π²)`,
  and the "magic identity" of [CFOT17]. -/
  nu : ∀ g, S6.Adm g → ∃ ν, S6.NuData g ν
  /-- Plancherel's identity on `ℝ²` for real `L¹ ∩ L²` functions. -/
  plancherel : S6.PlanePlancherel
  /-- The Brezis–Lieb lemma [BL83] for `p = 6`. -/
  brezisLieb : S6.BrezisLieb6
  /-- The reduction to nonnegative antipodal functions, `‖Ef‖₆ ≤ ‖Ef♯‖₆`
  [CFOT17, §1, Steps 1–2]. -/
  cfot : S6.CFOTReduction

end SteinTomasCircle
