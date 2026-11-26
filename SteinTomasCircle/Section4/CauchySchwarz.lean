import Mathlib

/-!
# Section 4: the Cauchy–Schwarz step (integral form of ν² ≤ ρ·(f²σ)*³ in the proof of prop:master)

Abstract form: F ≥ 0 on (Ω, m), sm : Ω → ℝ². If ν is the density of (sm)_*(F·m), ρ the density of (sm)_*m,
and ∫ν < ∞, then for every measurable w:
  ∫ w² ν²/ρ ≤ ∫_Ω w(sm)² F² dm.
(Ω = (S¹)³, F = f(ω₁)f(ω₂)f(ω₃), ν = (fσ)*³, ρ = σ*³.)
Proof: truncation a_n = min(w²ν/ρ, n), pointwise 2GH ≤ G² + H², then monotone convergence; no external input.
-/

namespace SteinTomas.S4CS

open Real MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {m : Measure Ω} {sm : Ω → ℝ × ℝ}
  {F : Ω → ℝ} {ν ρ w : ℝ × ℝ → ℝ}

lemma pt_bound {a w ν ρ : ℝ} (ha0 : 0 ≤ a) (ham : a ≤ w ^ 2 * ν / ρ) (hν0 : 0 ≤ ν) (hρ0 : 0 ≤ ρ) :
    (a / |w|) ^ 2 * ρ ≤ a * ν := by
  rcases eq_or_ne w 0 with hw | hw
  · rw [hw, abs_zero, div_zero]; simp; positivity
  rcases eq_or_lt_of_le hρ0 with hρ | hρ
  · rw [← hρ]; simp; positivity
  have hw2 : 0 < w ^ 2 := by positivity
  have h1 : a * a * ρ ≤ a * (w ^ 2 * ν / ρ) * ρ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ham ha0) hρ0
  have h2 : a * (w ^ 2 * ν / ρ) * ρ = a * ν * w ^ 2 := by field_simp
  rw [div_pow, sq_abs, div_mul_eq_mul_div, div_le_iff₀ hw2]
  nlinarith [h1, h2]

theorem cs_density (hsm : Measurable sm) (hFm : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω)
    (hνm : Measurable ν) (hν0 : ∀ y, 0 ≤ ν y) (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hwm : Measurable w)
    (hν : ∀ Ψ : ℝ × ℝ → ℝ≥0∞, Measurable Ψ →
      ∫⁻ y, Ψ y * ENNReal.ofReal (ν y) = ∫⁻ ω, Ψ (sm ω) * ENNReal.ofReal (F ω) ∂m)
    (hρ : ∀ Ψ : ℝ × ℝ → ℝ≥0∞, Measurable Ψ →
      ∫⁻ y, Ψ y * ENNReal.ofReal (ρ y) = ∫⁻ ω, Ψ (sm ω) ∂m)
    (hfin : ∫⁻ y, ENNReal.ofReal (ν y) < ∞) :
    ∫⁻ y, ENNReal.ofReal (w y ^ 2 * ν y ^ 2 / ρ y)
      ≤ ∫⁻ ω, ENNReal.ofReal (w (sm ω) ^ 2 * F ω ^ 2) ∂m := by
  set A : ℝ × ℝ → ℝ := fun y => w y ^ 2 * ν y / ρ y with hA
  have hA0 : ∀ y, 0 ≤ A y := fun y => by
    have := hν0 y; have := hρ0 y; simp only [hA]; positivity
  have hAm : Measurable A := ((hwm.pow_const 2).mul hνm).div hρm
  set X := ∫⁻ ω, ENNReal.ofReal (w (sm ω) ^ 2 * F ω ^ 2) ∂m with hX
  -- truncation
  have hTn : ∀ n : ℕ, ∫⁻ y, ENNReal.ofReal (min (A y) n * ν y) ≤ X := by
    intro n
    set a : ℝ × ℝ → ℝ := fun y => min (A y) n with ha
    have ha0 : ∀ y, 0 ≤ a y := fun y => le_min (hA0 y) (Nat.cast_nonneg n)
    have ham : Measurable a := hAm.min measurable_const
    set T := ∫⁻ y, ENNReal.ofReal (a y * ν y) with hT
    have hTe : T = ∫⁻ ω, ENNReal.ofReal (a (sm ω)) * ENNReal.ofReal (F ω) ∂m := by
      rw [hT, ← hν (fun y => ENNReal.ofReal (a y)) (ENNReal.measurable_ofReal.comp ham)]
      refine lintegral_congr (fun y => ?_)
      rw [ENNReal.ofReal_mul (ha0 y)]
    have hTfin : T < ∞ := by
      have : T ≤ ∫⁻ y, (n : ℝ≥0∞) * ENNReal.ofReal (ν y) := by
        refine lintegral_mono (fun y => ?_)
        rw [ENNReal.ofReal_mul (ha0 y)]
        gcongr
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
      refine lt_of_le_of_lt this ?_
      rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n)]
      exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top n) hfin
    -- G = a/|w|
    set G : ℝ × ℝ → ℝ := fun y => a y / |w y| with hG
    have hGm : Measurable G := ham.div hwm.abs
    have haG : ∀ y, a y = G y * |w y| := by
      intro y
      rcases eq_or_ne (w y) 0 with hw | hw
      · have : A y = 0 := by simp only [hA, hw]; ring
        simp only [ha, hG, this, hw, abs_zero, mul_zero]
        exact min_eq_left (Nat.cast_nonneg n)
      · simp only [hG]; field_simp
    -- pointwise 2GH ≤ G² + H²
    have hpt : ∀ ω, 2 * (ENNReal.ofReal (a (sm ω)) * ENNReal.ofReal (F ω))
        ≤ ENNReal.ofReal (G (sm ω) ^ 2) + ENNReal.ofReal (w (sm ω) ^ 2 * F ω ^ 2) := by
      intro ω
      rw [← ENNReal.ofReal_mul (ha0 _), show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (sq_nonneg _)
          (by have := hF0 ω; positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [haG (sm ω)]
      nlinarith [sq_nonneg (G (sm ω) - |w (sm ω)| * F ω), sq_abs (w (sm ω))]
    have h2T : 2 * T ≤ ∫⁻ ω, ENNReal.ofReal (G (sm ω) ^ 2) ∂m + X := by
      rw [hTe, ← lintegral_const_mul' _ _ (by norm_num), hX,
        ← lintegral_add_right _ (show Measurable fun ω => ENNReal.ofReal (w (sm ω) ^ 2 * F ω ^ 2)
          from ENNReal.measurable_ofReal.comp (((hwm.comp hsm).pow_const 2).mul (hFm.pow_const 2)))]
      exact lintegral_mono hpt
    have hG2 : ∫⁻ ω, ENNReal.ofReal (G (sm ω) ^ 2) ∂m ≤ T := by
      rw [← hρ (fun y => ENNReal.ofReal (G y ^ 2)) (ENNReal.measurable_ofReal.comp (hGm.pow_const 2)), hT]
      refine lintegral_mono (fun y => ?_)
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      exact pt_bound (ha0 y) (min_le_left _ _) (hν0 y) (hρ0 y)
    have h3 : T + T ≤ T + X := by
      rw [← two_mul]; exact h2T.trans (add_le_add hG2 le_rfl)
    exact (ENNReal.add_le_add_iff_left hTfin.ne).1 h3
  -- monotone convergence
  have hsup : ∀ y, ⨆ n : ℕ, ENNReal.ofReal (min (A y) n * ν y)
      = ENNReal.ofReal (w y ^ 2 * ν y ^ 2 / ρ y) := by
    intro y
    have he : w y ^ 2 * ν y ^ 2 / ρ y = A y * ν y := by simp only [hA]; ring
    rw [he]
    apply le_antisymm
    · refine iSup_le (fun n => ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) (hν0 y)
    · refine le_iSup_of_le ⌈A y⌉₊ (le_of_eq ?_)
      rw [min_eq_left (Nat.le_ceil _)]
  have hmono : Monotone (fun (n : ℕ) (y : ℝ × ℝ) => ENNReal.ofReal (min (A y) n * ν y)) := by
    intro n k hnk y
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (hν0 y))
    exact min_le_min_left _ (by exact_mod_cast hnk)
  have hmeas : ∀ n : ℕ, Measurable (fun y => ENNReal.ofReal (min (A y) n * ν y)) :=
    fun n => ENNReal.measurable_ofReal.comp ((hAm.min measurable_const).mul hνm)
  calc ∫⁻ y, ENNReal.ofReal (w y ^ 2 * ν y ^ 2 / ρ y)
      = ∫⁻ y, ⨆ n : ℕ, ENNReal.ofReal (min (A y) n * ν y) := by
        refine lintegral_congr (fun y => (hsup y).symm)
    _ = ⨆ n : ℕ, ∫⁻ y, ENNReal.ofReal (min (A y) n * ν y) := lintegral_iSup hmeas hmono
    _ ≤ X := iSup_le hTn

end

end SteinTomas.S4CS

#print axioms SteinTomas.S4CS.cs_density
