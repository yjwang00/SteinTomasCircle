import Mathlib
import SteinTomasCircle.Section2.QFourier
import SteinTomasCircle.Section4.Pointwise

/-!
# Section 4: eq:square-identity

For g = f² (integrable, antipodal g(θ+π) = g(θ)), on (S¹)³:
  ∫ (|ω₁+ω₂+ω₃|² − 1)² g(ω₁)g(ω₂)g(ω₃) = 16B³ − 12B·I(f), B = ∫g = ‖f‖₂².
Proof: integrate one variable at a time; each step reduces to the moments ∫g·{1, cos², cos·sin, sin²} of g (the first moments vanish by antipodal symmetry).
-/

namespace SteinTomas.S4Sq

open Real MeasureTheory Set

noncomputable section

local notation "μI" => (volume.restrict (Ioc (0 : ℝ) (2 * π)))

variable {g : ℝ → ℝ}

/-- g·φ is integrable (φ continuous, |φ| ≤ C) -/
lemma intB (hg : Integrable g μI) {φ : ℝ → ℝ} (hφ : Continuous φ) {C : ℝ} (hb : ∀ x, |φ x| ≤ C) :
    Integrable (fun θ => g θ * φ θ) μI := by
  have := S2C.bmul hg hφ (C := C) (fun x => by rw [Real.norm_eq_abs]; exact hb x)
  refine this.congr (Filter.Eventually.of_forall (fun t => ?_))
  simp only; ring

/-- Antipodal ⇒ the first moments vanish -/
lemma first_zero (hg : Integrable g μI) (hanti : ∀ θ, g (θ + π) = g θ) {φ : ℝ → ℝ}
    (hφ : Continuous φ) {C : ℝ} (hb : ∀ x, |φ x| ≤ C) (hodd : ∀ x, φ (x + π) = -φ x) :
    ∫ θ in Ioc 0 (2 * π), g θ * φ θ = 0 := by
  have hp := pi_pos
  have h2 : (0 : ℝ) ≤ 2 * π := by positivity
  set F : ℝ → ℝ := fun θ => g θ * φ θ with hF
  have hFi : IntervalIntegrable F volume 0 (2 * π) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2).2 (intB hg hφ hb)
  have hF1 : IntervalIntegrable F volume 0 π := hFi.mono_set (by
    rw [uIcc_of_le hp.le, uIcc_of_le h2]; exact Icc_subset_Icc le_rfl (by linarith))
  have hF2 : IntervalIntegrable F volume π (2 * π) := hFi.mono_set (by
    rw [uIcc_of_le (by linarith), uIcc_of_le h2]; exact Icc_subset_Icc hp.le le_rfl)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hF1 hF2
  have hshift : ∫ x in π..(2 * π), F x = ∫ x in (0 : ℝ)..π, F (x + π) := by
    rw [intervalIntegral.integral_comp_add_right (f := F)]
    rw [zero_add, show π + π = 2 * π by ring]
  have hneg : ∫ x in (0 : ℝ)..π, F (x + π) = -∫ x in (0 : ℝ)..π, F x := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [hF, hanti, hodd]; ring
  rw [← intervalIntegral.integral_of_le h2]
  show ∫ x in (0 : ℝ)..(2 * π), F x = 0
  rw [← hadd, hshift, hneg]; ring

/-- Moments -/
def mB (g : ℝ → ℝ) : ℝ := ∫ θ in Ioc 0 (2 * π), g θ
def mcc (g : ℝ → ℝ) : ℝ := ∫ θ in Ioc 0 (2 * π), g θ * Real.cos θ ^ 2
def mcs (g : ℝ → ℝ) : ℝ := ∫ θ in Ioc 0 (2 * π), g θ * (Real.cos θ * Real.sin θ)
def mss (g : ℝ → ℝ) : ℝ := ∫ θ in Ioc 0 (2 * π), g θ * Real.sin θ ^ 2

lemma abs_cos_sq_le (x : ℝ) : |Real.cos x ^ 2| ≤ 1 := by
  rw [abs_of_nonneg (sq_nonneg _)]; exact Real.cos_sq_le_one x
lemma abs_sin_sq_le (x : ℝ) : |Real.sin x ^ 2| ≤ 1 := by
  rw [abs_of_nonneg (sq_nonneg _)]; exact Real.sin_sq_le_one x
lemma abs_cs_le (x : ℝ) : |Real.cos x * Real.sin x| ≤ 1 := by
  rw [abs_mul]
  exact mul_le_one₀ (abs_cos_le_one x) (abs_nonneg _) (abs_sin_le_one x)

/-- Integrals of quadratic trigonometric polynomials -/
lemma quad_int (hg : Integrable g μI) (hanti : ∀ θ, g (θ + π) = g θ) (α β γ δ ε ζ : ℝ) :
    ∫ θ in Ioc 0 (2 * π), g θ * (α + β * Real.cos θ + γ * Real.sin θ + δ * Real.cos θ ^ 2
        + ε * (Real.cos θ * Real.sin θ) + ζ * Real.sin θ ^ 2)
      = α * mB g + δ * mcc g + ε * mcs g + ζ * mss g := by
  have i0 : Integrable (fun θ => α * g θ) μI := hg.const_mul _
  have i1 : Integrable (fun θ => β * (g θ * Real.cos θ)) μI :=
    (intB hg Real.continuous_cos (fun x => abs_cos_le_one x)).const_mul _
  have i2 : Integrable (fun θ => γ * (g θ * Real.sin θ)) μI :=
    (intB hg Real.continuous_sin (fun x => abs_sin_le_one x)).const_mul _
  have i3 : Integrable (fun θ => δ * (g θ * Real.cos θ ^ 2)) μI :=
    (intB hg (by fun_prop) abs_cos_sq_le).const_mul _
  have i4 : Integrable (fun θ => ε * (g θ * (Real.cos θ * Real.sin θ))) μI :=
    (intB hg (by fun_prop) abs_cs_le).const_mul _
  have i5 : Integrable (fun θ => ζ * (g θ * Real.sin θ ^ 2)) μI :=
    (intB hg (by fun_prop) abs_sin_sq_le).const_mul _
  have p1 : Integrable (fun θ => α * g θ + β * (g θ * Real.cos θ)) μI := i0.add i1
  have p2 : Integrable (fun θ => α * g θ + β * (g θ * Real.cos θ) + γ * (g θ * Real.sin θ)) μI :=
    p1.add i2
  have p3 : Integrable (fun θ => α * g θ + β * (g θ * Real.cos θ) + γ * (g θ * Real.sin θ)
      + δ * (g θ * Real.cos θ ^ 2)) μI := p2.add i3
  have p4 : Integrable (fun θ => α * g θ + β * (g θ * Real.cos θ) + γ * (g θ * Real.sin θ)
      + δ * (g θ * Real.cos θ ^ 2) + ε * (g θ * (Real.cos θ * Real.sin θ))) μI := p3.add i4
  have e : (fun θ => g θ * (α + β * Real.cos θ + γ * Real.sin θ + δ * Real.cos θ ^ 2
        + ε * (Real.cos θ * Real.sin θ) + ζ * Real.sin θ ^ 2))
      = fun θ => α * g θ + β * (g θ * Real.cos θ) + γ * (g θ * Real.sin θ)
        + δ * (g θ * Real.cos θ ^ 2) + ε * (g θ * (Real.cos θ * Real.sin θ))
        + ζ * (g θ * Real.sin θ ^ 2) := by
    funext θ; ring
  have hc := first_zero hg hanti Real.continuous_cos (fun x => abs_cos_le_one x)
    (fun x => Real.cos_add_pi x)
  have hs := first_zero hg hanti Real.continuous_sin (fun x => abs_sin_le_one x)
    (fun x => Real.sin_add_pi x)
  rw [e, integral_add p4 i5, integral_add p3 i4, integral_add p2 i3, integral_add p1 i2,
    integral_add i0 i1, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul, hc, hs]
  unfold mB mcc mcs mss
  ring

/-- Third variable -/
lemma stage3 (hg : Integrable g μI) (hanti : ∀ θ, g (θ + π) = g θ) (a b : ℝ) :
    ∫ c in Ioc 0 (2 * π), ((Real.cos a + Real.cos b + Real.cos c) ^ 2
        + (Real.sin a + Real.sin b + Real.sin c) ^ 2 - 1) ^ 2 * (g a * (g b * g c))
      = g a * g b * ((2 + 2 * (Real.cos a * Real.cos b + Real.sin a * Real.sin b)) ^ 2 * mB g
        + 4 * (Real.cos a + Real.cos b) ^ 2 * mcc g
        + 8 * (Real.cos a + Real.cos b) * (Real.sin a + Real.sin b) * mcs g
        + 4 * (Real.sin a + Real.sin b) ^ 2 * mss g) := by
  have hpt : ∀ c : ℝ, ((Real.cos a + Real.cos b + Real.cos c) ^ 2
        + (Real.sin a + Real.sin b + Real.sin c) ^ 2 - 1) ^ 2 * (g a * (g b * g c))
      = g a * g b * (g c * ((2 + 2 * (Real.cos a * Real.cos b + Real.sin a * Real.sin b)) ^ 2 + 4 * (2 + 2 * (Real.cos a * Real.cos b + Real.sin a * Real.sin b)) * (Real.cos a + Real.cos b) * Real.cos c + 4 * (2 + 2 * (Real.cos a * Real.cos b + Real.sin a * Real.sin b)) * (Real.sin a + Real.sin b) * Real.sin c
        + 4 * (Real.cos a + Real.cos b) ^ 2 * Real.cos c ^ 2 + 8 * (Real.cos a + Real.cos b) * (Real.sin a + Real.sin b) * (Real.cos c * Real.sin c)
        + 4 * (Real.sin a + Real.sin b) ^ 2 * Real.sin c ^ 2)) := by
    intro c
    have hw : (Real.cos a + Real.cos b + Real.cos c) ^ 2
        + (Real.sin a + Real.sin b + Real.sin c) ^ 2 - 1
        = (2 + 2 * (Real.cos a * Real.cos b + Real.sin a * Real.sin b)) + 2 * (Real.cos a + Real.cos b) * Real.cos c + 2 * (Real.sin a + Real.sin b) * Real.sin c := by
      linear_combination Real.sin_sq_add_cos_sq a + Real.sin_sq_add_cos_sq b
        + Real.sin_sq_add_cos_sq c
    rw [hw]; ring
  simp_rw [hpt]
  rw [integral_const_mul, quad_int hg hanti]

/-- Second variable -/
lemma stage2 (hg : Integrable g μI) (hanti : ∀ θ, g (θ + π) = g θ) (a : ℝ) :
    ∫ b in Ioc 0 (2 * π), g a * g b * ((2 + 2 * (Real.cos a * Real.cos b + Real.sin a * Real.sin b)) ^ 2
        * mB g + 4 * (Real.cos a + Real.cos b) ^ 2 * mcc g
        + 8 * (Real.cos a + Real.cos b) * (Real.sin a + Real.sin b) * mcs g
        + 4 * (Real.sin a + Real.sin b) ^ 2 * mss g)
      = g a * ((4 * mB g + 4 * mcc g * Real.cos a ^ 2 + 8 * mcs g * (Real.cos a * Real.sin a)
          + 4 * mss g * Real.sin a ^ 2) * mB g
        + (4 * mB g * Real.cos a ^ 2 + 4 * mcc g) * mcc g
        + (8 * mB g * (Real.cos a * Real.sin a) + 8 * mcs g) * mcs g
        + (4 * mB g * Real.sin a ^ 2 + 4 * mss g) * mss g) := by
  have hpt : ∀ b : ℝ, g a * g b * ((2 + 2 * (Real.cos a * Real.cos b + Real.sin a * Real.sin b)) ^ 2 * mB g
        + 4 * (Real.cos a + Real.cos b) ^ 2 * mcc g + 8 * (Real.cos a + Real.cos b) * (Real.sin a + Real.sin b) * mcs g
        + 4 * (Real.sin a + Real.sin b) ^ 2 * mss g)
      = g a * (g b * ((4 * mB g + 4 * mcc g * Real.cos a ^ 2 + 8 * mcs g * (Real.cos a * Real.sin a) + 4 * mss g * Real.sin a ^ 2)
        + (8 * mB g * Real.cos a + 8 * mcc g * Real.cos a + 8 * mcs g * Real.sin a) * Real.cos b
        + (8 * mB g * Real.sin a + 8 * mcs g * Real.cos a + 8 * mss g * Real.sin a) * Real.sin b
        + (4 * mB g * Real.cos a ^ 2 + 4 * mcc g) * Real.cos b ^ 2
        + (8 * mB g * (Real.cos a * Real.sin a) + 8 * mcs g) * (Real.cos b * Real.sin b)
        + (4 * mB g * Real.sin a ^ 2 + 4 * mss g) * Real.sin b ^ 2)) := by
    intro b; ring
  simp_rw [hpt]
  rw [integral_const_mul, quad_int hg hanti]

/-- First variable -/
lemma stage1 (hg : Integrable g μI) (hanti : ∀ θ, g (θ + π) = g θ) :
    ∫ a in Ioc 0 (2 * π), g a * ((4 * mB g + 4 * mcc g * Real.cos a ^ 2
          + 8 * mcs g * (Real.cos a * Real.sin a) + 4 * mss g * Real.sin a ^ 2) * mB g
        + (4 * mB g * Real.cos a ^ 2 + 4 * mcc g) * mcc g
        + (8 * mB g * (Real.cos a * Real.sin a) + 8 * mcs g) * mcs g
        + (4 * mB g * Real.sin a ^ 2 + 4 * mss g) * mss g)
      = 4 * mB g ^ 3 + 12 * mB g * (mcc g ^ 2 + 2 * mcs g ^ 2 + mss g ^ 2) := by
  have hpt : ∀ a : ℝ, g a * ((4 * mB g + 4 * mcc g * Real.cos a ^ 2 + 8 * mcs g * (Real.cos a * Real.sin a)
        + 4 * mss g * Real.sin a ^ 2) * mB g + (4 * mB g * Real.cos a ^ 2 + 4 * mcc g) * mcc g
        + (8 * mB g * (Real.cos a * Real.sin a) + 8 * mcs g) * mcs g + (4 * mB g * Real.sin a ^ 2 + 4 * mss g) * mss g)
      = g a * ((4 * mB g ^ 2 + 4 * mcc g ^ 2 + 8 * mcs g ^ 2 + 4 * mss g ^ 2) + 0 * Real.cos a + 0 * Real.sin a
        + (8 * mB g * mcc g) * Real.cos a ^ 2 + (16 * mB g * mcs g) * (Real.cos a * Real.sin a)
        + (8 * mB g * mss g) * Real.sin a ^ 2) := by
    intro a; ring
  simp_rw [hpt]
  rw [quad_int hg hanti]
  ring

/-- Triple integral (product measure) -/
theorem triple (hg : Integrable g μI) (hanti : ∀ θ, g (θ + π) = g θ) :
    ∫ p, ((Real.cos p.1 + Real.cos p.2.1 + Real.cos p.2.2) ^ 2
        + (Real.sin p.1 + Real.sin p.2.1 + Real.sin p.2.2) ^ 2 - 1) ^ 2
        * (g p.1 * (g p.2.1 * g p.2.2)) ∂(Measure.prod μI (Measure.prod μI μI))
      = 4 * mB g ^ 3 + 12 * mB g * (mcc g ^ 2 + 2 * mcs g ^ 2 + mss g ^ 2) := by
  have hw : ∀ x y z : ℝ, |((Real.cos x + Real.cos y + Real.cos z) ^ 2
      + (Real.sin x + Real.sin y + Real.sin z) ^ 2 - 1) ^ 2| ≤ 64 := by
    intro x y z
    have h1 := Real.sin_sq_add_cos_sq x; have h2 := Real.sin_sq_add_cos_sq y
    have h3 := Real.sin_sq_add_cos_sq z
    have hu : 0 ≤ (Real.cos x + Real.cos y + Real.cos z) ^ 2
        + (Real.sin x + Real.sin y + Real.sin z) ^ 2 := by positivity
    have hl : (Real.cos x + Real.cos y + Real.cos z) ^ 2
        + (Real.sin x + Real.sin y + Real.sin z) ^ 2 ≤ 9 := by
      nlinarith [sq_nonneg (Real.cos x - Real.cos y), sq_nonneg (Real.cos y - Real.cos z),
        sq_nonneg (Real.cos x - Real.cos z), sq_nonneg (Real.sin x - Real.sin y),
        sq_nonneg (Real.sin y - Real.sin z), sq_nonneg (Real.sin x - Real.sin z)]
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hG : Integrable (fun p : ℝ × ℝ × ℝ => g p.1 * (g p.2.1 * g p.2.2)) (Measure.prod μI (Measure.prod μI μI)) :=
    hg.mul_prod (hg.mul_prod hg)
  have hint : Integrable (fun p : ℝ × ℝ × ℝ => ((Real.cos p.1 + Real.cos p.2.1 + Real.cos p.2.2) ^ 2
        + (Real.sin p.1 + Real.sin p.2.1 + Real.sin p.2.2) ^ 2 - 1) ^ 2
        * (g p.1 * (g p.2.1 * g p.2.2))) (Measure.prod μI (Measure.prod μI μI)) :=
    hG.bdd_mul (c := 64) (Continuous.aestronglyMeasurable (by fun_prop))
      (Filter.Eventually.of_forall (fun p => by rw [Real.norm_eq_abs]; exact hw _ _ _))
  rw [integral_prod _ hint]
  have hin : ∀ a : ℝ, ∫ q, ((Real.cos a + Real.cos q.1 + Real.cos q.2) ^ 2
        + (Real.sin a + Real.sin q.1 + Real.sin q.2) ^ 2 - 1) ^ 2
        * (g a * (g q.1 * g q.2)) ∂(Measure.prod μI μI)
      = g a * ((4 * mB g + 4 * mcc g * Real.cos a ^ 2 + 8 * mcs g * (Real.cos a * Real.sin a)
          + 4 * mss g * Real.sin a ^ 2) * mB g
        + (4 * mB g * Real.cos a ^ 2 + 4 * mcc g) * mcc g
        + (8 * mB g * (Real.cos a * Real.sin a) + 8 * mcs g) * mcs g
        + (4 * mB g * Real.sin a ^ 2 + 4 * mss g) * mss g) := by
    intro a
    have hGa : Integrable (fun q : ℝ × ℝ => g a * (g q.1 * g q.2)) (Measure.prod μI μI) :=
      (hg.mul_prod hg).const_mul _
    have hia : Integrable (fun q : ℝ × ℝ => ((Real.cos a + Real.cos q.1 + Real.cos q.2) ^ 2
        + (Real.sin a + Real.sin q.1 + Real.sin q.2) ^ 2 - 1) ^ 2
        * (g a * (g q.1 * g q.2))) (Measure.prod μI μI) :=
      hGa.bdd_mul (c := 64) (Continuous.aestronglyMeasurable (by fun_prop))
        (Filter.Eventually.of_forall (fun q => by rw [Real.norm_eq_abs]; exact hw _ _ _))
    rw [integral_prod _ hia]
    simp_rw [stage3 hg hanti a]
    exact stage2 hg hanti a
  simp_rw [hin]
  exact stage1 hg hanti

/-- eq:square-identity: = 16B³ − 12B·I(f), g = f² -/
theorem square_identity {f : ℝ → ℝ} (hf : MemLp f 2 μI) (hanti : ∀ θ, f (θ + π) = f θ) :
    ∫ p, ((Real.cos p.1 + Real.cos p.2.1 + Real.cos p.2.2) ^ 2
        + (Real.sin p.1 + Real.sin p.2.1 + Real.sin p.2.2) ^ 2 - 1) ^ 2
        * (f p.1 ^ 2 * (f p.2.1 ^ 2 * f p.2.2 ^ 2)) ∂(Measure.prod μI (Measure.prod μI μI))
      = 16 * (∫ t in Ioc 0 (2 * π), f t ^ 2) ^ 3
        - 12 * (∫ t in Ioc 0 (2 * π), f t ^ 2) * S45.Ia f := by
  have hg : Integrable (fun θ => f θ ^ 2) μI := hf.integrable_sq
  have hga : ∀ θ, (fun θ => f θ ^ 2) (θ + π) = (fun θ => f θ ^ 2) θ := by
    intro θ; simp only [hanti]
  have ht := triple hg hga
  rw [ht, S45.I_formula hf]
  -- B = P + S, Cm₀ = P − S, Sm₀ = 2R
  have hB : mB (fun θ => f θ ^ 2) = mcc (fun θ => f θ ^ 2) + mss (fun θ => f θ ^ 2) := by
    unfold mB mcc mss
    rw [← integral_add (intB hg (by fun_prop) abs_cos_sq_le) (intB hg (by fun_prop) abs_sin_sq_le)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    simp only
    linear_combination (-(f θ ^ 2)) * Real.sin_sq_add_cos_sq θ
  have hC : S2C.Cm (fun θ => f θ ^ 2) 0 = mcc (fun θ => f θ ^ 2) - mss (fun θ => f θ ^ 2) := by
    unfold S2C.Cm mcc mss
    rw [← integral_sub (intB hg (by fun_prop) abs_cos_sq_le) (intB hg (by fun_prop) abs_sin_sq_le)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    simp only
    rw [S45.kf0, Real.cos_two_mul, Real.cos_sq']; ring
  have hS : S2C.Sm (fun θ => f θ ^ 2) 0 = 2 * mcs (fun θ => f θ ^ 2) := by
    unfold S2C.Sm mcs
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    simp only
    rw [S45.kf0, Real.sin_two_mul]; ring
  have hBint : ∫ t in Ioc 0 (2 * π), f t ^ 2 = mB (fun θ => f θ ^ 2) := rfl
  rw [hC, hS, hBint, hB]
  ring

end

end SteinTomas.S4Sq

#print axioms SteinTomas.S4Sq.square_identity
