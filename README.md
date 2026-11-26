# SteinTomasCircle

A Lean 4 / Mathlib formalization of

> Yaojun Wang, *Sharp endpoint Stein–Tomas inequality on the circle*, arXiv:XXXX.XXXXX.

The formalization proves the main results of the paper:

* **Theorem 1.1.** For every `f ∈ L²(𝕊¹)`, `‖Ef‖₆⁶ ≤ (2π)⁴ α₀ ‖f‖₂⁶`, where
  `α₀ = ∫₀^∞ J₀(r)⁶ r dr`. Equality holds for constants, and nonzero constants are maximizers.
* **Theorem 1.2.** For every `f ∈ L²(𝕊¹)`, `‖Ef‖₆⁶ ≤ M_conc ‖f‖₂⁶ + 90π ‖f‖₁² ‖f‖₂⁴` with
  `M_conc = 20π³/√3`, and `M_conc` cannot be lowered.

## Scope of the formalization

Results quoted from the literature enter as **explicit hypotheses**; every argument of the paper
itself is proved in Lean. All hypotheses are collected in a single structure
[`LiteratureInputs`](SteinTomasCircle/LiteratureInputs.lean):

| Field | Content | Source |
|---|---|---|
| `sinSeries` | Fourier series of `\|sin u\|` | classical |
| `bessel` | Properties of `J_{2n}` (kernel identity, continuity, null zero set, series bounds, DLMF 10.14.4, integrability) and the numerical values of `α_{2n}` | DLMF; [CFOT17, Table 1]; [OT17] |
| `rho` | Density of `σ*σ*σ` and its closed form | [BSWZ12]; [Bec25] |
| `steinTomas` | Tomas–Stein inequality `‖Ef‖₆ ≲ ‖f‖₂` | Tomas, Stein |
| `nu` | Density `ν` of `(gσ)*³`, `‖ν‖₂² = ‖Eg‖₆⁶/(4π²)`, magic identity | [CFOT17] |
| `plancherel` | Plancherel on `ℝ²` | classical |
| `brezisLieb` | Brezis–Lieb lemma, `p = 6` | [BL83] |
| `cfot` | Reduction `‖Ef‖₆ ≤ ‖Ef♯‖₆` | [CFOT17, §1, Steps 1–2] |

The optimality statement `theorem_1_2_optimal` additionally assumes the Gaussian trial sequence
`S6.FLSGaussianTrial` of [FLS16, §7, Prop. 7.1].

In particular, the existence of a weakly convergent subsequence, the Euler–Lagrange equation and
the second variation inequality for maximizers, and the Plancherel pairing used in Lemma 5.2 are
**proved**, not assumed.

## What to check

The kernel checks all proofs. A reader only needs to compare the following with the paper:

1. [`SteinTomasCircle/MainTheorems.lean`](SteinTomasCircle/MainTheorems.lean): the statements
   of the main theorems (about 80 lines);
2. [`SteinTomasCircle/LiteratureInputs.lean`](SteinTomasCircle/LiteratureInputs.lean): the
   hypotheses from the literature;
3. the definitions these refer to, mainly in
   [`SteinTomasCircle/Basic/Defs.lean`](SteinTomasCircle/Basic/Defs.lean) (`σ`, `E`, `ext6`,
   `L2n`, `L1n`, `J`, `α`, `Mconc`, `IsMaximizer`) and in `SteinTomasCircle/MainProof/`.

## Correspondence with the paper

| Paper | Lean declaration | File |
|---|---|---|
| Theorem 1.1 | `SteinTomasCircle.theorem_1_1`, `theorem_1_1_constants`, `theorem_1_1_maximizer` | `MainTheorems.lean` |
| Theorem 1.2 | `SteinTomasCircle.theorem_1_2`, `theorem_1_2_optimal` | `MainTheorems.lean` |
| Lemma 2.1 | `SteinTomas.Lemma21.U_lt`, `V_lt`, `W_gt` | `Section2/LocalBessel.lean` |
| eq. (bessel-global) | `SteinTomas.Section2.bessel_global` | `Section2/BesselGlobal.lean` |
| eq. (Phi-identity) | `SteinTomas.S2P.phi_identity` | `Section2/PhiIdentity.lean` |
| eq. (quadratic-spectral) | `SteinTomas.S2Q.quad_spectral` | `Section2/QuadraticSpectral.lean` |
| eq. (Q-Fourier) | `SteinTomas.S2C.Q_fourier` | `Section2/QFourier.lean` |
| eq. (density-upper) | `SteinTomas.S2R.density_upper` | `Section2/DensityUpper.lean` |
| eq. (pair-change-of-variables) | `SteinTomas.S2V.pair_cov` | `Section2/PairChangeOfVariables.lean` |
| eq. (pair-density) | `SteinTomas.S2H.h_L2_real` | `Section2/PairDensity.lean` |
| eq. (h-Fourier) | `SteinTomas.S2HF.h_fourier` | `Section2/HFourier.lean` |
| eq. (def h by f) | `SteinTomas.S2HC.hpaper_eq` | `Section2/HDefinition.lean` |
| Proposition 3.1 | `SteinTomas.S2W.prop_large_mean_full` | `Section3/LargeMean.lean` |
| Lemma 4.3 | `SteinTomas.lem_four_sign` | `Basic/Defs.lean`, `Section4/FourSign.lean` |
| eq. (square-identity) | `SteinTomas.S4Sq.square_identity` | `Section4/SquareIdentity.lean` |
| eq. (residual-simple) | `SteinTomas.S4R.R_bound` | `Section4/ResidualBound.lean` |
| Proposition 4.4 | `SteinTomas.S4M.master` | `Section4/Master.lean` |
| eq. (L1-remainder-sym) | `SteinTomas.S4M.L1_remainder_sym` | `Section4/Master.lean` |
| Proposition 5.1 | `SteinTomas.S5A.prop_convolution` | `Section5/GlobalSimple.lean` |
| eq. (square-average) | `SteinTomas.S45.square_average'` | `Section4/Pointwise.lean` |
| Claim in Lemma 5.2 | `SteinTomas.S5B.conv_bound` | `Section5/ConvolutionClaim.lean` |
| Lemma 5.2 | `SteinTomas.S5C.lemma52` | `Section5/SecondVariation.lean` |
| Proposition 5.3 | `SteinTomas.S5D.prop_small_mean'` | `Section5/SmallMean.lean` |
| Normalized maximizers are constant | `SteinTomas.S5D.maximizer_const` | `Section5/SmallMean.lean` |
| Proof of Theorem 1.1 (compactness) | `SteinTomas.S6.thm_main_real`, `S6.bl_limit` | `MainProof/Compactness.lean` |
| Euler–Lagrange and second variation | `SteinTomas.S6.maximizer_variations` | `MainProof/Variation.lean` |
| Weak compactness | `SteinTomas.S6.weak_subsequence` | `MainProof/Prep.lean` |
| Optimality of `M_conc` | `SteinTomas.S6.thm_L1_remainder_optimal` | `MainProof/Optimality.lean` |

## Project layout

```
SteinTomasCircle/
  LiteratureInputs.lean   hypotheses from the literature
  MainTheorems.lean       statements of the main theorems
  Axioms.lean             prints the axioms used by the main theorems
  Basic/                  definitions, elementary and numerical facts
  Section2/               §2 Preliminaries
  Section3/               §3 Maximizers with large mean (Prop. 3.1)
  Section4/               §4 Proof of Theorem 1.2 (Prop. 4.4)
  Section5/               §5 Maximizers with small mean (Prop. 5.1, Lemma 5.2, Prop. 5.3)
  MainProof/              proof of Theorem 1.1 (compactness) and optimality in Theorem 1.2
Challenge.lean            the statements of MainTheorems.lean with `sorry`, for `lake check`
comparator.json           configuration for comparator
```

## Building

The project uses Lean `v4.37.0-rc1` and Mathlib `v4.37.0-rc1` (pinned in `lean-toolchain`
and `lake-manifest.json`). With [elan](https://github.com/leanprover/elan) installed:

```
lake exe cache get
lake build
lake build SteinTomasCircle.Axioms
```

The last command prints the axioms of the main theorems; each should be
`[propext, Classical.choice, Quot.sound]`.

To check with comparator that the proved theorems have exactly the statements in
`Challenge.lean`, run `lake check` (Lean ≥ v4.35) or comparator with `comparator.json`.

## Release and arXiv ancillary files

The version accompanying the paper is tagged `v1.0.0`. The same files (this folder without
`.lake/`) are attached to the arXiv submission as ancillary files; `SHA256SUMS.txt` lists
their checksums (`sha256sum -c SHA256SUMS.txt`).

## References

* [Bec25] L. Becker, *Sharp Fourier extension for functions with localized support on the circle*,
  Rev. Mat. Iberoam. 41 (2025), 2145–2166.
* [BL83] H. Brezis, E. H. Lieb, *A relation between pointwise convergence of functions and
  convergence of functionals*, Proc. Amer. Math. Soc. 88 (1983), 486–490.
* [BSWZ12] J. M. Borwein, A. Straub, J. Wan, W. Zudilin, *Densities of short uniform random
  walks*, Canad. J. Math. 64 (2012), 961–990.
* [CFOT17] E. Carneiro, D. Foschi, D. Oliveira e Silva, C. Thiele, *A sharp trilinear inequality
  related to Fourier restriction on the circle*, Rev. Mat. Iberoam. 33 (2017), 1463–1486.
* [FLS16] R. L. Frank, E. H. Lieb, J. Sabin, *Maximizers for the Stein–Tomas inequality*,
  Geom. Funct. Anal. 26 (2016), 1095–1134.
* [OT17] D. Oliveira e Silva, C. Thiele, *Estimates for certain integrals of products of six
  Bessel functions*, Rev. Mat. Iberoam. 33 (2017), 1423–1462.

See the paper for the complete bibliography.
