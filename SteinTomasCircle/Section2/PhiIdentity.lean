import Mathlib
import SteinTomasCircle.Basic.Elementary
import SteinTomasCircle.Section2.FourierSeries
import SteinTomasCircle.Section2.PolarKernel
import SteinTomasCircle.Section2.BesselGlobal
import SteinTomasCircle.Section2.NormalizedExtension

/-!
# Section 2 (§2.2): the Φ-identity from the Euler–Lagrange equation (eq:Phi-identity)

* `Ec f x` = Ef(x) (x ∈ ℝ²; for real-valued antipodal f, Ef is real)
* `polar_integral`: polar coordinates on ℝ² (Mathlib's `integral_comp_polarCoord_symm`)
* `Ep_e0`: Ee₀(r,φ) = √(2π)J₀(r)
* `phi_identity`: if ∫(Ef)⁵Ee₀ = ‖Ef‖₆⁶·a₀ (the EL equation paired with e₀, external input [CQ14, OQ21b]),
  then for every t: μt⁵(a₀−t) = ∫₀^∞ J₀(r)⁶ [avg Φ(tF(r,·))] r dr, μ = (2π)^{-4}‖Ef‖₆⁶.
  External input: the zero set of J₀ is a null set (DLMF 10.21).
-/

namespace SteinTomas.S2P

open Real MeasureTheory Set SteinTomas.S2F SteinTomas.S2K SteinTomas.Section2 SteinTomas.S2E

noncomputable section

/-- Ef on ℝ² (real-valued form) -/
def Ec (f : ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * π), Real.cos (x.1 * Real.cos θ + x.2 * Real.sin θ) * f θ

/-- e₀ = 1/√(2π) -/
def e0 : ℝ → ℝ := fun _ => 1 / Real.sqrt (2 * π)

lemma Ec_polar (f : ℝ → ℝ) (r φ : ℝ) : Ec f (r * Real.cos φ, r * Real.sin φ) = Ep f r φ := by
  simp only [Ec, Ep]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  rw [show r * Real.cos φ * Real.cos θ + r * Real.sin φ * Real.sin θ = r * Real.cos (θ - φ) by
    rw [Real.cos_sub]; ring]

/-! ## Polar coordinates -/

lemma integrableOn_polar {h : ℝ × ℝ → ℝ} (hh : Integrable h) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * h (polarCoord.symm p)) polarCoord.target := by
  have key := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (μ := volume)
    polarCoord.open_target.measurableSet
    (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt) polarCoord.symm.injOn h).mp
  rw [polarCoord.symm_image_target_eq_source] at key
  have h2 := key hh.integrableOn
  refine h2.congr_fun (fun p hp => ?_) polarCoord.open_target.measurableSet
  simp only [det_fderivPolarCoordSymm, smul_eq_mul]
  rw [abs_of_pos hp.1]

/-- Integration in polar coordinates -/
lemma polar_integral {h : ℝ × ℝ → ℝ} (hh : Integrable h) :
    ∫ x, h x = ∫ r in Ioi (0 : ℝ), (∫ φ in Ioo (-π) π, h (r * Real.cos φ, r * Real.sin φ)) * r := by
  rw [← integral_comp_polarCoord_symm]
  have hi := integrableOn_polar hh
  simp only [polarCoord_target] at hi ⊢
  rw [Measure.volume_eq_prod] at hi ⊢
  simp only [smul_eq_mul]
  rw [setIntegral_prod _ hi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  simp only [polarCoord_symm_apply, smul_eq_mul]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- Integrability of the radial function: r ↦ (∫_{(−π,π)} h(polar))·r ∈ L¹(0,∞) -/
lemma polar_radial_integrable {h : ℝ × ℝ → ℝ} (hh : Integrable h) :
    IntegrableOn (fun r => (∫ φ in Ioo (-π) π, h (r * Real.cos φ, r * Real.sin φ)) * r) (Ioi 0) := by
  have hi := integrableOn_polar hh
  simp only [polarCoord_target] at hi
  rw [Measure.volume_eq_prod, IntegrableOn, ← Measure.prod_restrict] at hi
  have h2 := hi.integral_prod_left
  refine h2.congr ?_
  filter_upwards with r
  simp only [polarCoord_symm_apply]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- An integral over (−π, π) becomes an integral over (0, 2π) (2π-periodic) -/
lemma angle_range {g : ℝ → ℝ} (hper : ∀ φ, g (φ + 2 * π) = g φ) :
    ∫ φ in Ioo (-π) π, g φ = ∫ φ in (0 : ℝ)..(2 * π), g φ := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos])]
  have := (show Function.Periodic g (2 * π) from hper).intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at this
  exact this

/-! ## Ee₀ -/

lemma int_kernel {Jb : ℕ → ℝ → ℝ} (hB : BesselKernel Jb) (r : ℝ) :
    ∫ u in (0 : ℝ)..(2 * π), Real.cos (r * Real.cos u) = 2 * π * Jb 0 r := by
  have h := hB.kc_even r 0
  rw [kc, mul_zero, coef_zero] at h
  simp only [Int.natAbs_zero, pow_zero, one_mul] at h
  have h2 := Complex.ofReal_injective h
  have hp : (2 * π) ≠ 0 := by positivity
  calc ∫ u in (0 : ℝ)..(2 * π), Real.cos (r * Real.cos u)
      = 2 * π * ((1 / (2 * π)) * ∫ u in (0 : ℝ)..(2 * π), Real.cos (r * Real.cos u)) := by
        field_simp
    _ = 2 * π * Jb 0 r := by rw [h2]

lemma Ep_e0 {Jb : ℕ → ℝ → ℝ} (hB : BesselKernel Jb) (r φ : ℝ) :
    Ep e0 r φ = Real.sqrt (2 * π) * Jb 0 r := by
  simp only [Ep, e0]
  rw [intervalIntegral.integral_mul_const]
  have hK : Function.Periodic (fun u => Real.cos (r * Real.cos u)) (2 * π) := by
    intro u; simp only [Real.cos_add_two_pi]
  have h1 := intervalIntegral.integral_comp_sub_right (f := fun u => Real.cos (r * Real.cos u))
    (a := 0) (b := 2 * π) φ
  rw [show (0 : ℝ) - φ = -φ by ring, show 2 * π - φ = -φ + 2 * π by ring,
    hK.intervalIntegral_add_eq (-φ) 0, zero_add] at h1
  rw [h1, int_kernel hB]
  have hs : Real.sqrt (2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  have hs0 : Real.sqrt (2 * π) ≠ 0 := by positivity
  field_simp
  rw [hs]
  ring

lemma Ec_e0_polar {Jb : ℕ → ℝ → ℝ} (hB : BesselKernel Jb) (r φ : ℝ) :
    Ec e0 (r * Real.cos φ, r * Real.sin φ) = Real.sqrt (2 * π) * Jb 0 r := by
  rw [Ec_polar, Ep_e0 hB]

/-! ## Averages under ψ = 2φ + β -/

lemma avg_half {H : ℝ → ℝ} (hH : Continuous H) (hper : ∀ φ, H (φ + π) = H φ) {q : ℝ → ℝ}
    (hq : Continuous q) (β : ℝ) :
    avg (fun ψ => q (H ((ψ - β) / 2))) = avg (fun φ => q (H φ)) := by
  have h := coef_half (H := fun φ => q (H φ)) (hq.comp hH) (fun φ => by simp only [hper φ]) β 0
  rw [mul_zero] at h
  simp only [Int.cast_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul] at h
  apply Complex.ofReal_injective
  rw [avg_eq_coef0, avg_eq_coef0]
  exact h

/-! ## The Φ-identity -/

theorem phi_identity {f : ℝ → ℝ} {Jb : ℕ → ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) (hB : BesselKernel Jb)
    (hz : volume {r : ℝ | 0 < r ∧ Jb 0 r = 0} = 0)
    (hi5 : Integrable (fun x => Ec f x ^ 5 * Ec e0 x)) (hi6 : Integrable (fun x => Ec f x ^ 6))
    (hEL : ∫ x, Ec f x ^ 5 * Ec e0 x = (∫ x, Ec f x ^ 6) * a0 f) (t : ℝ) :
    IntegrableOn (fun r => Jb 0 r ^ 6 * avg (fun ψ => Φ (t * F Jb f r ψ)) * r) (Ioi 0) ∧
    ((1 / (2 * π) ^ 4) * ∫ x, Ec f x ^ 6) * t ^ 5 * (a0 f - t)
      = ∫ r in Ioi 0, Jb 0 r ^ 6 * avg (fun ψ => Φ (t * F Jb f r ψ)) * r := by
  set μ := (1 / (2 * π) ^ 4) * ∫ x, Ec f x ^ 6 with hμ
  have hp4 : (2 * π) ^ 4 ≠ 0 := by positivity
  have h6 : ∫ x, Ec f x ^ 6 = (2 * π) ^ 4 * μ := by rw [hμ]; field_simp
  have h5 : ∫ x, Ec f x ^ 5 * Ec e0 x = (2 * π) ^ 4 * μ * a0 f := by rw [hEL, h6]
  have hmain := phi_identity_alg (t := t) hi5 hi6 h5 h6
  set Hx : ℝ × ℝ → ℝ := fun x => (t * Ec f x) ^ 5 * Ec e0 x - (t * Ec f x) ^ 6 with hHx
  have hHi : Integrable Hx := by
    refine ((hi5.const_mul (t ^ 5)).sub (hi6.const_mul (t ^ 6))).congr ?_
    filter_upwards with x
    simp only [hHx, Pi.sub_apply]; ring
  have hpol := polar_integral hHi
  have hrad := polar_radial_integrable hHi
  -- inner integral
  have hs : Real.sqrt (2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  have hs0 : Real.sqrt (2 * π) ≠ 0 := by positivity
  have inner : ∀ r, Jb 0 r ≠ 0 →
      (∫ φ in Ioo (-π) π, Hx (r * Real.cos φ, r * Real.sin φ))
        = (2 * π) ^ 4 * (Jb 0 r ^ 6 * avg (fun ψ => Φ (t * F Jb f r ψ))) := by
    intro r hJ
    set q : ℝ → ℝ := fun x => (t * x) ^ 5 * (Real.sqrt (2 * π) * Jb 0 r) - (t * x) ^ 6 with hq
    have hqc : Continuous q := by simp only [hq]; fun_prop
    have e1 : ∀ φ, Hx (r * Real.cos φ, r * Real.sin φ) = q (Ep f r φ) := by
      intro φ; simp only [hHx, hq, Ec_polar, Ec_e0_polar hB]
    simp_rw [e1]
    have hEc := Ep_continuous hf r
    have hper2 : ∀ φ, q (Ep f r (φ + 2 * π)) = q (Ep f r φ) := by
      intro φ
      rw [show φ + 2 * π = (φ + π) + π by ring, Ep_periodic, Ep_periodic]
    rw [angle_range hper2]
    have havg := avg_half hEc (Ep_periodic f r) hqc (β f)
    have e2 : ∫ φ in (0 : ℝ)..(2 * π), q (Ep f r φ) = 2 * π * avg (fun φ => q (Ep f r φ)) := by
      rw [avg]; field_simp
    rw [e2, ← havg]
    -- q(G) = (2π)³J₀⁶Φ(tF)
    have e3 : (fun ψ => q (Ep f r ((ψ - β f) / 2)))
        = fun ψ => ((2 * π) ^ 3 * Jb 0 r ^ 6) * Φ (t * F Jb f r ψ) := by
      funext ψ
      have hG : SteinTomas.S2E.G f r ψ = Ep f r ((ψ - β f) / 2) := rfl
      simp only [hq, F, Φ]
      rw [hG]
      rw [show (2 * π) ^ 3 = Real.sqrt (2 * π) ^ 6 by
        rw [show Real.sqrt (2 * π) ^ 6 = (Real.sqrt (2 * π) ^ 2) ^ 3 by ring, hs]]
      field_simp
    rw [e3, avg_const_mul]
    ring
  -- equality almost everywhere
  have hae : ∀ᵐ r ∂volume, ¬(0 < r ∧ Jb 0 r = 0) := by
    have := measure_eq_zero_iff_ae_notMem.mp hz
    filter_upwards [this] with r hr
    simpa using hr
  have hcongr : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      (∫ φ in Ioo (-π) π, Hx (r * Real.cos φ, r * Real.sin φ)) * r
        = (2 * π) ^ 4 * (Jb 0 r ^ 6 * avg (fun ψ => Φ (t * F Jb f r ψ)) * r) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hae] with r hr hr0
    have hJ : Jb 0 r ≠ 0 := fun h => hr ⟨hr0, h⟩
    rw [inner r hJ]; ring
  have hint : IntegrableOn (fun r => Jb 0 r ^ 6 * avg (fun ψ => Φ (t * F Jb f r ψ)) * r) (Ioi 0) := by
    have h1 : IntegrableOn (fun r => (2 * π) ^ 4 * (Jb 0 r ^ 6 * avg (fun ψ => Φ (t * F Jb f r ψ)) * r))
        (Ioi 0) := hrad.congr hcongr
    have h2 := h1.const_mul (1 / (2 * π) ^ 4)
    refine h2.congr ?_
    filter_upwards with r
    field_simp
  refine ⟨hint, ?_⟩
  have hI : ∫ x, Hx x = (2 * π) ^ 4 * ∫ r in Ioi 0, Jb 0 r ^ 6 * avg (fun ψ => Φ (t * F Jb f r ψ)) * r := by
    rw [hpol, integral_congr_ae hcongr, MeasureTheory.integral_const_mul]
  have hmain' : ∫ x, Hx x = (2 * π) ^ 4 * μ * t ^ 5 * (a0 f - t) := by
    rw [← hmain]
  rw [hI] at hmain'
  have h' : (2 * π) ^ 4 * (∫ r in Ioi 0, Jb 0 r ^ 6 * avg (fun ψ => Φ (t * F Jb f r ψ)) * r)
      = (2 * π) ^ 4 * (μ * t ^ 5 * (a0 f - t)) := by rw [hmain']; ring
  have := mul_left_cancel₀ hp4 h'
  linarith

end

end SteinTomas.S2P

#print axioms SteinTomas.S2P.phi_identity
