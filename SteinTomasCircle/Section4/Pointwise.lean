import Mathlib
import SteinTomasCircle.Basic.Elementary
import SteinTomasCircle.Section4.FourSign
import SteinTomasCircle.Basic.Defs
import SteinTomasCircle.Basic.Chains
import SteinTomasCircle.Section2.QFourier
import SteinTomasCircle.Section2.DensityUpper

/-!
# Sections 4 and 5: pointwise and Fourier parts

* `Pl_formula`: 𝒫 = (|x|²−1) − (|x|−1)(|x|²−1)²/16 (1 < |x| < 3)
* `scalar_majorant`: eq:scalar-majorant (from eq:density-upper)
* `I_formula`: I(f) = ½‖f‖₂⁴ − ½|∫f²ω²dσ|² (first formula in the proof of prop:convolution)
* `Q_drop`: Q(f²) ≤ (2/π)‖f‖₂⁴ − (4/(3π))|∫f²ω²dσ|² (dropping the terms n ≥ 2 in eq:Q-Fourier)
* `square_average'`: eq:square-average
-/

namespace SteinTomas.S45

open Real MeasureTheory Set

noncomputable section

/-! ## eq:scalar-majorant -/

/-- λ(8−λ)ψ(λ) = λ − (r−1)λ²/16, λ = r² − 1 -/
lemma Pl_formula {r : ℝ} (hr : 0 ≤ r) :
    (r ^ 2 - 1) * (8 - (r ^ 2 - 1)) * FourSign.ψ (r ^ 2 - 1)
      = (r ^ 2 - 1) - (r - 1) / 16 * (r ^ 2 - 1) ^ 2 := by
  unfold FourSign.ψ
  rw [show 1 + (r ^ 2 - 1) = r ^ 2 by ring, Real.sqrt_sq hr]
  have h3 : (3 + r) ≠ 0 := by linarith
  field_simp
  ring

lemma Kl_pos {m : ℝ} (hm1 : m < 1) : 0 < S2R.Kl m := by
  unfold S2R.Kl
  have hpos : ∀ θ : ℝ, 0 < 1 - m * Real.sin θ ^ 2 := by
    intro θ
    have := Real.sin_sq_le_one θ
    rcases le_total 0 m with h | h
    · nlinarith
    · nlinarith [sq_nonneg (Real.sin θ)]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact (continuous_const.div (Real.continuous_sqrt.comp (by fun_prop))
      (fun θ => (Real.sqrt_pos.2 (hpos θ)).ne')).intervalIntegrable _ _
  · intro θ _
    exact div_pos one_pos (Real.sqrt_pos.2 (hpos θ))
  · positivity

/-- eq:scalar-majorant: for |x| < 3 (|x| ≠ 1),
|x|² − 1 ≤ (π/(4√3 ρ(|x|)))(|x|² − 1)² + 𝒫(x). ρ satisfies the BSWZ12 formula (external input), ρ ≥ 0. -/
theorem scalar_majorant {ρ : ℝ → ℝ}
    (hρ : ∀ r, 1 < r → r < 3 → ρ r = 4 / Real.sqrt r * S2R.Kl ((r + 1) ^ 3 * (3 - r) / (16 * r)))
    (hρ0 : ∀ r, 0 ≤ ρ r) (x : ℝ × ℝ) (hx3 : nsq x < 9) :
    nsq x - 1 ≤ π / (4 * Real.sqrt 3 * ρ (Real.sqrt (nsq x))) * (nsq x - 1) ^ 2 + Pw x := by
  have hn0 : 0 ≤ nsq x := by unfold nsq; positivity
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt (nsq x) := ⟨_, rfl⟩
  rw [← hr]
  have hr0 : 0 ≤ r := by rw [hr]; exact Real.sqrt_nonneg _
  have hr2 : r ^ 2 = nsq x := by rw [hr]; exact Real.sq_sqrt hn0
  have hP0 : 0 ≤ Pw x := by
    rw [Pw_eq]; unfold FourSign.Pl
    split_ifs with h
    · have := FourSign.ψ_nonneg h.1.le
      have : 0 ≤ 8 - (nsq x - 1) := by linarith [h.2]
      have := h.1.le
      positivity
    · exact le_refl _
  have hc0 : 0 ≤ π / (4 * Real.sqrt 3 * ρ r) := by
    have := hρ0 r; positivity
  rcases le_or_gt r 1 with h1 | h1
  · -- |x| ≤ 1
    have : nsq x ≤ 1 := by rw [← hr2]; nlinarith
    nlinarith [mul_nonneg hc0 (sq_nonneg (nsq x - 1))]
  · have h3 : r < 3 := by
      rw [hr, Real.sqrt_lt' (by norm_num)]; linarith
    have hPw : Pw x = (nsq x - 1) - (r - 1) / 16 * (nsq x - 1) ^ 2 := by
      unfold Pw
      rw [← hr, if_pos ⟨h1, h3⟩, ← hr2, show (9 : ℝ) - r ^ 2 = 8 - (r ^ 2 - 1) by ring]
      exact Pl_formula hr0
    have hρle := (S2R.density_upper hρ h1 h3).2
    have hρpos : 0 < ρ r := by
      rw [hρ r h1 h3]
      have hm := (Section2.k_sq_identity h1 h3).2.2
      have := Kl_pos hm
      have : 0 < Real.sqrt r := Real.sqrt_pos.2 (by linarith)
      positivity
    have hcoef : (r - 1) / 16 ≤ π / (4 * Real.sqrt 3 * ρ r) := by
      have hs3 : 0 < Real.sqrt 3 := by positivity
      have hr1 : 0 < r - 1 := by linarith
      rw [le_div_iff₀ (by positivity)]
      have h := (le_div_iff₀ (by positivity : 0 < Real.sqrt 3 * (r - 1))).1 hρle
      nlinarith [h]
    rw [hPw]
    nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg (nsq x - 1))]

/-! ## I(f) and Q(f²) -/

variable {f : ℝ → ℝ}

/-- I(f) (angular variables) -/
def Ia (f : ℝ → ℝ) : ℝ :=
  ∫ s in Ioc 0 (2 * π), ∫ t in Ioc 0 (2 * π), Real.sin (t - s) ^ 2 * f s ^ 2 * f t ^ 2

lemma kf0 : S2C.kf 0 = 2 := by unfold S2C.kf; norm_num

/-- I(f) = ½(∫f²)² − ½(C² + S²), C + iS = ∫ f² ω² dσ -/
theorem I_formula (hf : MemLp f 2 (volume.restrict (Ioc 0 (2 * π)))) :
    Ia f = 1 / 2 * (∫ t in Ioc 0 (2 * π), f t ^ 2) ^ 2
      - 1 / 2 * (S2C.Cm (fun θ => f θ ^ 2) 0 ^ 2 + S2C.Sm (fun θ => f θ ^ 2) 0 ^ 2) := by
  set g : ℝ → ℝ := fun θ => f θ ^ 2 with hg
  have hgi : Integrable g (volume.restrict (Ioc 0 (2 * π))) := hf.integrable_sq
  set G := ∫ t in Ioc 0 (2 * π), g t with hG
  set C := S2C.Cm g 0 with hC
  set S := S2C.Sm g 0 with hS
  have hpt : ∀ s t : ℝ, Real.sin (t - s) ^ 2 * f s ^ 2 * f t ^ 2
      = g s * (1 / 2 * g t - 1 / 2 * Real.cos (S2C.kf 0 * s) * (g t * Real.cos (S2C.kf 0 * t))
        - 1 / 2 * Real.sin (S2C.kf 0 * s) * (g t * Real.sin (S2C.kf 0 * t))) := by
    intro s t
    rw [kf0]
    have h1 := Real.sin_sq_eq_half_sub (t - s)
    have h2 : Real.cos (2 * (t - s)) = Real.cos (2 * t) * Real.cos (2 * s)
        + Real.sin (2 * t) * Real.sin (2 * s) := by
      rw [show 2 * (t - s) = 2 * t - 2 * s by ring, Real.cos_sub]
    simp only [hg]
    rw [h1, h2]; ring
  have hin : ∀ s, ∫ t in Ioc 0 (2 * π), Real.sin (t - s) ^ 2 * f s ^ 2 * f t ^ 2
      = g s * (1 / 2 * G - 1 / 2 * (Real.cos (S2C.kf 0 * s) * C + Real.sin (S2C.kf 0 * s) * S)) := by
    intro s
    simp_rw [hpt s]
    have i1 : Integrable (fun t => 1 / 2 * g t) (volume.restrict (Ioc 0 (2 * π))) :=
      hgi.const_mul _
    have i2 : Integrable (fun t => 1 / 2 * Real.cos (S2C.kf 0 * s)
        * (g t * Real.cos (S2C.kf 0 * t))) (volume.restrict (Ioc 0 (2 * π))) :=
      (S2C.int_gcos hgi _).const_mul _
    have i3 : Integrable (fun t => 1 / 2 * Real.sin (S2C.kf 0 * s)
        * (g t * Real.sin (S2C.kf 0 * t))) (volume.restrict (Ioc 0 (2 * π))) :=
      (S2C.int_gsin hgi _).const_mul _
    have i12 : Integrable (fun t => 1 / 2 * g t - 1 / 2 * Real.cos (S2C.kf 0 * s)
        * (g t * Real.cos (S2C.kf 0 * t))) (volume.restrict (Ioc 0 (2 * π))) := i1.sub i2
    rw [MeasureTheory.integral_const_mul, integral_sub i12 i3, integral_sub i1 i2,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
    simp only [hC, hS, hG, S2C.Cm, S2C.Sm]
    ring
  unfold Ia
  simp_rw [hin]
  have e : (fun s => g s * (1 / 2 * G - 1 / 2 * (Real.cos (S2C.kf 0 * s) * C
      + Real.sin (S2C.kf 0 * s) * S)))
      = fun s => (1 / 2 * G) * g s - (1 / 2 * C) * (g s * Real.cos (S2C.kf 0 * s))
        - (1 / 2 * S) * (g s * Real.sin (S2C.kf 0 * s)) := by
    funext s; ring
  have j1 : Integrable (fun s => 1 / 2 * G * g s) (volume.restrict (Ioc 0 (2 * π))) :=
    hgi.const_mul _
  have j2 : Integrable (fun s => 1 / 2 * C * (g s * Real.cos (S2C.kf 0 * s)))
      (volume.restrict (Ioc 0 (2 * π))) := (S2C.int_gcos hgi _).const_mul _
  have j3 : Integrable (fun s => 1 / 2 * S * (g s * Real.sin (S2C.kf 0 * s)))
      (volume.restrict (Ioc 0 (2 * π))) := (S2C.int_gsin hgi _).const_mul _
  have j12 : Integrable (fun s => 1 / 2 * G * g s - 1 / 2 * C * (g s * Real.cos (S2C.kf 0 * s)))
      (volume.restrict (Ioc 0 (2 * π))) := j1.sub j2
  rw [e, integral_sub j12 j3, integral_sub j1 j2,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul]
  simp only [hC, hS, hG, S2C.Cm, S2C.Sm]
  ring

/-- Dropping the terms n ≥ 2 in eq:Q-Fourier -/
theorem Q_drop (hsin : S2C.SinSeries) (hf : MemLp f 2 (volume.restrict (Ioc 0 (2 * π)))) :
    S2C.Qa (fun θ => f θ ^ 2) ≤ 2 / π * (∫ t in Ioc 0 (2 * π), f t ^ 2) ^ 2
      - 4 / (3 * π) * (S2C.Cm (fun θ => f θ ^ 2) 0 ^ 2 + S2C.Sm (fun θ => f θ ^ 2) 0 ^ 2) := by
  have hgi : Integrable (fun θ => f θ ^ 2) (volume.restrict (Ioc 0 (2 * π))) := hf.integrable_sq
  have hQ := S2C.Q_fourier hsin hgi
  have h0 := le_hasSum hQ 0 (fun j _ => mul_nonneg (S2C.cQ_nonneg j) (by positivity))
  have hc0 : S2C.cQ 0 = 4 / (3 * π) := by
    unfold S2C.cQ
    rw [div_div]
    congr 1
    push_cast; ring
  rw [hc0] at h0
  linarith

/-- eq:square-average: I(f) ≥ (3π/8)Q(f²) − ¼‖f‖₂⁴ -/
theorem square_average' (hsin : S2C.SinSeries) (hf : MemLp f 2 (volume.restrict (Ioc 0 (2 * π)))) :
    3 * π / 8 * S2C.Qa (fun θ => f θ ^ 2) - 1 / 4 * (∫ t in Ioc 0 (2 * π), f t ^ 2) ^ 2 ≤ Ia f := by
  rw [I_formula hf]
  have hQ := Q_drop hsin hf
  have hp := Real.pi_pos
  set m := S2C.Cm (fun θ => f θ ^ 2) 0 ^ 2 + S2C.Sm (fun θ => f θ ^ 2) 0 ^ 2
  set B := ∫ t in Ioc 0 (2 * π), f t ^ 2
  have h := mul_le_mul_of_nonneg_left hQ (by positivity : (0 : ℝ) ≤ 3 * π / 8)
  have e : 3 * π / 8 * (2 / π * B ^ 2 - 4 / (3 * π) * m) = 3 / 4 * B ^ 2 - 1 / 2 * m := by
    field_simp; ring
  rw [e] at h
  linarith

end

end SteinTomas.S45

#print axioms SteinTomas.S45.scalar_majorant
#print axioms SteinTomas.S45.I_formula
#print axioms SteinTomas.S45.square_average'
