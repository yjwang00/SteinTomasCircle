import SteinTomasCircle.LiteratureInputs

/-!
# Main theorems

Lean statements of the main results of

  Yaojun Wang, *Sharp endpoint Stein–Tomas inequality on the circle*.

Notation (see `SteinTomasCircle/Basic/Defs.lean`):
* functions on `𝕊¹` are parametrized by the angle, `F : ℝ → ℂ`, and `σ` is Lebesgue measure on
  `(0, 2π]` (arc length);
* `E F x = ∫ e^{−i x·ω(θ)} F(θ) dσ(θ)` is the extension operator, `ext6 F = ‖EF‖₆⁶`;
* `L2n F = ‖F‖_{L²(σ)}`, `L1n F = ‖F‖_{L¹(σ)}`;
* `α 0 = ∫₀^∞ J₀(r)⁶ r dr`, with `J₀` defined by its integral representation, and
  `S6.M0 = (2π)⁴ α 0`;
* `Mconc = 20π³/√3`.

The theorem names follow the numbering of the paper.
-/

namespace SteinTomasCircle

open MeasureTheory Real SteinTomas
open scoped ENNReal

/-- The constant of Theorem 1.1. -/
theorem M0_eq : S6.M0 = (2 * π) ^ 4 * α 0 := rfl

/-- **Theorem 1.1** (sharp inequality): `‖EF‖₆⁶ ≤ (2π)⁴ α₀ ‖F‖₂⁶` for every `F ∈ L²(𝕊¹)`. -/
theorem theorem_1_1 (L : LiteratureInputs) (F : ℝ → ℂ) (hF : MemLp F 2 σ) :
    ext6 F ≤ ENNReal.ofReal S6.M0 * L2n F ^ 6 := by
  obtain ⟨ρ, ρr, hρ⟩ := L.rho
  exact S6.thm_main L.sinSeries L.bessel hρ L.steinTomas L.nu L.plancherel L.brezisLieb
    L.cfot F hF

/-- **Theorem 1.1** (equality): constants attain the bound. -/
theorem theorem_1_1_constants (L : LiteratureInputs) (c : ℂ) :
    ext6 (fun _ => c) = ENNReal.ofReal S6.M0 * L2n (fun _ => c) ^ 6 :=
  S6.const_attains L.bessel L.steinTomas c

/-- **Theorem 1.1** (maximizers): every nonzero constant is a maximizer. -/
theorem theorem_1_1_maximizer (L : LiteratureInputs) {c : ℂ} (hc : c ≠ 0) :
    IsMaximizer (fun _ => c) := by
  obtain ⟨ρ, ρr, hρ⟩ := L.rho
  exact S6.const_isMaximizer L.sinSeries L.bessel hρ L.steinTomas L.nu L.plancherel
    L.brezisLieb L.cfot hc

/-- **Theorem 1.2** (`L¹` remainder):
`‖EF‖₆⁶ ≤ M_conc ‖F‖₂⁶ + 90π ‖F‖₁² ‖F‖₂⁴` for every `F ∈ L²(𝕊¹)`. -/
theorem theorem_1_2 (L : LiteratureInputs) (F : ℝ → ℂ) (hF : MemLp F 2 σ) :
    ext6 F ≤ ENNReal.ofReal Mconc * L2n F ^ 6
      + ENNReal.ofReal (90 * π) * L1n F ^ 2 * L2n F ^ 4 := by
  obtain ⟨ρ, ρr, hρ⟩ := L.rho
  exact S6.thm_L1_remainder L.sinSeries hρ L.nu L.cfot F hF

/-- **Theorem 1.2** (optimality of `M_conc`), using the Gaussian trial sequence of
[FLS16, §7, Prop. 7.1] as an additional input. -/
theorem theorem_1_2_optimal (L : LiteratureInputs) (hFLS : S6.FLSGaussianTrial) :
    IsLeast {A : ℝ≥0∞ | ∀ F : ℝ → ℂ, MemLp F 2 σ →
      ext6 F ≤ A * L2n F ^ 6 + ENNReal.ofReal (90 * π) * L1n F ^ 2 * L2n F ^ 4}
      (ENNReal.ofReal Mconc) := by
  obtain ⟨ρ, ρr, hρ⟩ := L.rho
  exact S6.thm_L1_remainder_optimal L.sinSeries hρ L.nu L.cfot hFLS

end SteinTomasCircle
