import Mathlib
import SteinTomasCircle.Basic.Elementary
import SteinTomasCircle.Section3.Algebra
import SteinTomasCircle.Section2.BesselGlobal
import SteinTomasCircle.Basic.Chains
import SteinTomasCircle.Section2.Analysis
import SteinTomasCircle.Section2.LocalBessel

/-!
# Section 3: Proposition 3.1 (prop:large-mean)

The angular variable is ψ = 2φ (see the convention in Section2), c = cos ψ = Re θ².

Structure:
1. `step1`: from the Φ-identity (t = ½), avg F = a₀, eq:quadratic-spectral and the quadratic upper bound for Φ(x/2),
   we get μ/32·(a₀−½) ≤ α₀/32·(1−3a₀) + 5/64·(α₀a₀² + S), hence a₀ < 4/5.
2. `angular_bound`: for fixed r ≤ 7/4, tF = v + w, v = ta₀ + γ cos ψ,
   under avg w = 0, avg(cos·w) = 0 (eq:prop31-b),
   avg[Φ(tF) − (27/256)(tF)²] ≤ Φ(ta₀) − (27/256)(ta₀)² + ½K γ² + (15/8)x(1−3x)γ⁴ − (5/16)γ⁶
                               + (γ²/2)√(avg w²) + (53/256) avg w².
3. `radial_pointwise`: combined with eq:tail-L2 and eq:bessel-pointwise, multiplying by J₀⁶ reduces the above to
   the integrands of the three integrals W, V, U.
4. `radial_assembly`: integration in r (split into (0,7/4] and (7/4,∞)) gives the main inequality of Chains.large_mean_step2.
5. `prop_large_mean`: assembly, proving a₀ < 5/8 from the given analytic data.
-/

namespace SteinTomas.Section3

open Real Set MeasureTheory SteinTomas.Section2 SteinTomas.Prop31Alg

noncomputable section

/-! ## Step 1 -/

lemma avg_quad {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 (2 * π))
    (hf2 : IntervalIntegrable (fun x => f x ^ 2) volume 0 (2 * π)) :
    avg (fun x => 1 / 32 - 3 / 32 * f x + 5 / 64 * f x ^ 2)
      = 1 / 32 - 3 / 32 * avg f + 5 / 64 * avg (fun x => f x ^ 2) := by
  have hc : IntervalIntegrable (fun _ : ℝ => (1 / 32 : ℝ)) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun _ : ℝ => (1 / 32 : ℝ)).intervalIntegrable 0 (2 * π)
  have h1 : IntervalIntegrable (fun x => 1 / 32 - 3 / 32 * f x) volume 0 (2 * π) :=
    hc.sub (hf.const_mul _)
  rw [avg_add h1 (hf2.const_mul _), avg_sub hc (hf.const_mul _), avg_const, avg_const_mul,
    avg_const_mul]

/-- Step 1 (first half of the proof of Prop 3.1). `F r ψ` is the F of eq:normalized-extension. -/
theorem step1 {J0 : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {μ α0 a0 S : ℝ}
    (hF : ∀ r, IntervalIntegrable (F r) volume 0 (2 * π))
    (hF2 : ∀ r, IntervalIntegrable (fun x => F r x ^ 2) volume 0 (2 * π))
    (hΦ : ∀ r, IntervalIntegrable (fun x => Φ (F r x / 2)) volume 0 (2 * π))
    (iΦ : IntegrableOn (fun r => J0 r ^ 6 * avg (fun x => Φ (F r x / 2)) * r) (Ioi 0))
    (i2 : IntegrableOn (fun r => J0 r ^ 6 * avg (fun x => F r x ^ 2) * r) (Ioi 0))
    (i0 : IntegrableOn (fun r => J0 r ^ 6 * r) (Ioi 0))
    (hid : μ * (1 / 2) ^ 5 * (a0 - 1 / 2)
      = ∫ r in Ioi 0, J0 r ^ 6 * avg (fun x => Φ (F r x / 2)) * r)
    (hmean : ∀ r, 0 < r → J0 r ≠ 0 → avg (F r) = a0)
    (hquad : ∫ r in Ioi 0, J0 r ^ 6 * avg (fun x => F r x ^ 2) * r = α0 * a0 ^ 2 + S)
    (hα : ∫ r in Ioi 0, J0 r ^ 6 * r = α0) :
    μ / 32 * (a0 - 1 / 2) ≤ α0 / 32 * (1 - 3 * a0) + 5 / 64 * (α0 * a0 ^ 2 + S) := by
  set g : ℝ → ℝ := fun r => (1 / 32 - 3 / 32 * a0) * (J0 r ^ 6 * r)
    + 5 / 64 * (J0 r ^ 6 * avg (fun x => F r x ^ 2) * r) with hg
  have hpt : ∀ r ∈ Ioi (0 : ℝ), J0 r ^ 6 * avg (fun x => Φ (F r x / 2)) * r ≤ g r := by
    intro r hr
    have hr0 : 0 < r := hr
    by_cases hJ : J0 r = 0
    · simp [hg, hJ]
    · have hc : IntervalIntegrable (fun _ : ℝ => (1 / 32 : ℝ)) volume 0 (2 * π) :=
        (by fun_prop : Continuous fun _ : ℝ => (1 / 32 : ℝ)).intervalIntegrable 0 (2 * π)
      have hR : IntervalIntegrable (fun x => 1 / 32 - 3 / 32 * F r x + 5 / 64 * F r x ^ 2)
          volume 0 (2 * π) := (hc.sub ((hF r).const_mul _)).add ((hF2 r).const_mul _)
      have hle : avg (fun x => Φ (F r x / 2))
          ≤ avg (fun x => 1 / 32 - 3 / 32 * F r x + 5 / 64 * F r x ^ 2) :=
        avg_mono (hΦ r) hR (fun x _ => phi_half (F r x))
      rw [avg_quad (hF r) (hF2 r), hmean r hr0 hJ] at hle
      have hw : 0 ≤ J0 r ^ 6 * r := by positivity
      have := mul_le_mul_of_nonneg_left hle hw
      simp only [hg]
      linarith
  have hgi : IntegrableOn g (Ioi 0) := (Integrable.const_mul i0 _).add (Integrable.const_mul i2 _)
  have hmono := setIntegral_mono_on iΦ hgi measurableSet_Ioi hpt
  have hgint : ∫ r in Ioi 0, g r = (1 / 32 - 3 / 32 * a0) * α0 + 5 / 64 * (α0 * a0 ^ 2 + S) := by
    simp only [hg]
    rw [MeasureTheory.integral_add (Integrable.const_mul i0 _) (Integrable.const_mul i2 _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hα, hquad]
  rw [← hid, hgint] at hmono
  linarith

/-! ## Step 2: angular estimate -/

/-- Remainder Σ_{j=2}^5 A_j Re θ^{2j} -/
def Rfun (x γ ψ : ℝ) : ℝ :=
  A2 x γ * T2 (cos ψ) + A3 x γ * T3 (cos ψ) + A4 x γ * T4 (cos ψ) + A5 γ * T5 (cos ψ)

lemma Rfun_cont (x γ : ℝ) : Continuous (fun ψ => Rfun x γ ψ) := by
  unfold Rfun T2 T3 T4 T5; fun_prop

/-- |avg(R·w)| ≤ (γ²/2)√(avg w²) -/
lemma cross_bound {x γ : ℝ} {w : ℝ → ℝ} (hx1 : 1 / 4 ≤ x) (hx2 : x ≤ 1 / 3) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1 / 3) (hw : IntervalIntegrable w volume 0 (2 * π))
    (hw2 : IntervalIntegrable (fun ψ => w ψ ^ 2) volume 0 (2 * π)) :
    avg (fun ψ => Rfun x γ ψ * w ψ) ≤ γ ^ 2 / 2 * Real.sqrt (avg (fun ψ => w ψ ^ 2)) := by
  have hRc := Rfun_cont x γ
  have hR2 : IntervalIntegrable (fun ψ => Rfun x γ ψ ^ 2) volume 0 (2 * π) :=
    (hRc.pow 2).intervalIntegrable _ _
  have hRw : IntervalIntegrable (fun ψ => Rfun x γ ψ * w ψ) volume 0 (2 * π) :=
    hw.continuousOn_mul hRc.continuousOn
  have cs := cs_avg hR2 hw2 hRw
  have hsq : avg (fun ψ => Rfun x γ ψ ^ 2)
      = 1 / 2 * (A2 x γ ^ 2 + A3 x γ ^ 2 + A4 x γ ^ 2 + A5 γ ^ 2) :=
    avg_R_sq (A2 x γ) (A3 x γ) (A4 x γ) (A5 γ)
  have hA := A_sq_sum hx1 hx2 hγ0 hγ1
  have hW0 : 0 ≤ avg (fun ψ => w ψ ^ 2) := avg_nonneg (fun ψ _ => sq_nonneg _)
  have h2 : avg (fun ψ => Rfun x γ ψ * w ψ) ^ 2 ≤ γ ^ 4 / 4 * avg (fun ψ => w ψ ^ 2) := by
    rw [hsq] at cs
    exact cs.trans (mul_le_mul_of_nonneg_right hA hW0)
  have h3 := Real.abs_le_sqrt h2
  have e : Real.sqrt (γ ^ 4 / 4 * avg (fun ψ => w ψ ^ 2))
      = γ ^ 2 / 2 * Real.sqrt (avg (fun ψ => w ψ ^ 2)) := by
    rw [show γ ^ 4 / 4 * avg (fun ψ => w ψ ^ 2) = (γ ^ 2 / 2) ^ 2 * avg (fun ψ => w ψ ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [e] at h3
  exact (le_abs_self _).trans h3

/-- Main angular estimate (fixed r) -/
theorem angular_bound {x γ : ℝ} {w : ℝ → ℝ} (hx1 : 1 / 4 ≤ x) (hx2 : x ≤ 1 / 3) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1 / 3) (hw : IntervalIntegrable w volume 0 (2 * π))
    (hw2 : IntervalIntegrable (fun ψ => w ψ ^ 2) volume 0 (2 * π))
    (hΦ : IntervalIntegrable (fun ψ => Φ (x + γ * cos ψ + w ψ)) volume 0 (2 * π))
    (hsq : IntervalIntegrable (fun ψ => (x + γ * cos ψ + w ψ) ^ 2) volume 0 (2 * π))
    (hm0 : avg w = 0) (hm1 : avg (fun ψ => cos ψ * w ψ) = 0) :
    avg (fun ψ => Φ (x + γ * cos ψ + w ψ) - 27 / 256 * (x + γ * cos ψ + w ψ) ^ 2)
      ≤ Φ x - 27 / 256 * x ^ 2 + 1 / 2 * Kp x * γ ^ 2 + 15 / 8 * x * (1 - 3 * x) * γ ^ 4
        - 5 / 16 * γ ^ 6 + γ ^ 2 / 2 * Real.sqrt (avg (fun ψ => w ψ ^ 2))
        + 53 / 256 * avg (fun ψ => w ψ ^ 2) := by
  -- integrability
  have hP : IntervalIntegrable (fun ψ => Φ (x + γ * cos ψ) - 27 / 256 * (x + γ * cos ψ) ^ 2)
      volume 0 (2 * π) := (by unfold Φ; fun_prop : Continuous fun ψ =>
        Φ (x + γ * cos ψ) - 27 / 256 * (x + γ * cos ψ) ^ 2).intervalIntegrable _ _
  have hcw : IntervalIntegrable (fun ψ => cos ψ * w ψ) volume 0 (2 * π) :=
    hw.continuousOn_mul continuous_cos.continuousOn
  have hRw : IntervalIntegrable (fun ψ => Rfun x γ ψ * w ψ) volume 0 (2 * π) :=
    hw.continuousOn_mul (Rfun_cont x γ).continuousOn
  set c0 := A0 x γ - 27 / 128 * x with hc0
  set c1 := A1 x γ - 27 / 128 * γ with hc1
  have i1 := hP.add (hw.const_mul c0)
  have i2 := i1.add (hcw.const_mul c1)
  have i3 := i2.add hRw
  have i4 := i3.add (hw2.const_mul (53 / 256))
  have iH : IntervalIntegrable
      (fun ψ => Φ (x + γ * cos ψ + w ψ) - 27 / 256 * (x + γ * cos ψ + w ψ) ^ 2)
      volume 0 (2 * π) := hΦ.sub (hsq.const_mul _)
  -- pointwise estimate
  have hpt : ∀ ψ ∈ Icc (0 : ℝ) (2 * π),
      Φ (x + γ * cos ψ + w ψ) - 27 / 256 * (x + γ * cos ψ + w ψ) ^ 2
        ≤ (Φ (x + γ * cos ψ) - 27 / 256 * (x + γ * cos ψ) ^ 2) + c0 * w ψ
          + c1 * (cos ψ * w ψ) + Rfun x γ ψ * w ψ + 53 / 256 * w ψ ^ 2 := by
    intro ψ _
    have t := phi_taylor (x + γ * cos ψ) (w ψ)
    rw [dphi_expand x γ (cos ψ)] at t
    simp only [hc0, hc1, Rfun]
    linarith [t]
  have hmono := avg_mono iH i4 hpt
  rw [avg_add i3 (hw2.const_mul _), avg_add i2 hRw, avg_add i1 (hcw.const_mul _),
    avg_add hP (hw.const_mul _), avg_const_mul, avg_const_mul, avg_const_mul, hm0, hm1,
    avg_phi_expand] at hmono
  have hcross := cross_bound hx1 hx2 hγ0 hγ1 hw hw2
  linarith

/-! ## Step 2: radial pointwise estimate -/

-- long derivation, needs more heartbeats
set_option maxHeartbeats 4000000 in
/-- For fixed r ∈ (0, 7/4]: multiply the angular estimate by J₀⁶ and reduce to the integrands of W, V, U.
Notation: j0 = J₀(r) > 0, j2 = J₂(r), κ = κ(r), R = 1 − a₀² − a₂², Aw = avg w²,
γ·j0 = √2·t·a₂·j2, eq:tail-L2: Aw·j0² ≤ t²Rκ². -/
theorem radial_pointwise {j0 j2 κ a0 a2 γ Aw Hv : ℝ} (hj0 : 0 < j0) (hj2 : 0 ≤ j2)
    (hj2k : j2 ^ 2 ≤ 10 * j0 * κ) (hκ : 0 ≤ κ) (ha2 : 0 ≤ a2) (hR : 0 ≤ 1 - a0 ^ 2 - a2 ^ 2)
    (hγ : γ * j0 = Real.sqrt 2 * tt * a2 * j2) (hγ0 : 0 ≤ γ)
    (hAw0 : 0 ≤ Aw) (hAw : Aw * j0 ^ 2 ≤ tt ^ 2 * (1 - a0 ^ 2 - a2 ^ 2) * κ ^ 2)
    (hx1 : 25 / 96 ≤ tt * a0) (hx2 : tt * a0 ≤ 1 / 3)
    (hH : Hv ≤ Φ (tt * a0) - 27 / 256 * (tt * a0) ^ 2 + 1 / 2 * Kp (tt * a0) * γ ^ 2
        + 15 / 8 * (tt * a0) * (1 - 3 * (tt * a0)) * γ ^ 4 - 5 / 16 * γ ^ 6
        + γ ^ 2 / 2 * Real.sqrt Aw + 53 / 256 * Aw) :
    j0 ^ 6 * Hv ≤ (Φ (tt * a0) - 27 / 256 * tt ^ 2 * a0 ^ 2) * j0 ^ 6
      + tt ^ 2 * a2 ^ 2 * Kp (tt * a0) * (j0 ^ 4 * j2 ^ 2)
      + (175 / 4 * tt ^ 4 * a2 ^ 4 + 53 / 256 * tt ^ 2 * (1 - a0 ^ 2 - a2 ^ 2)
        + 10 * tt ^ 3 * a2 ^ 2 * Real.sqrt (1 - a0 ^ 2 - a2 ^ 2)) * (j0 ^ 4 * κ ^ 2) := by
  have htt : tt = 5 / 12 := rfl
  have htt0 : 0 < tt := by rw [htt]; norm_num
  set x := tt * a0 with hx
  set R := 1 - a0 ^ 2 - a2 ^ 2 with hRdef
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- (γ j0)² = 2t²a₂²j2²
  have hg2 : (γ * j0) ^ 2 = 2 * tt ^ 2 * a2 ^ 2 * j2 ^ 2 := by
    rw [hγ, mul_pow, mul_pow, mul_pow, hs2]
  have hK : 0 ≤ Kp x := Chains.Kp_nonneg hx1 hx2
  -- term 1: j0⁶·½Kγ² = t²a₂²K j0⁴j2²
  have T1 : j0 ^ 6 * (1 / 2 * Kp x * γ ^ 2) = tt ^ 2 * a2 ^ 2 * Kp x * (j0 ^ 4 * j2 ^ 2) := by
    have : j0 ^ 6 * (1 / 2 * Kp x * γ ^ 2) = 1 / 2 * Kp x * j0 ^ 4 * (γ * j0) ^ 2 := by ring
    rw [this, hg2]; ring
  -- term 2: j0⁶·(15/8)x(1−3x)γ⁴ ≤ (175/4)t⁴a₂⁴ j0⁴κ²
  have hc2 : 0 ≤ 15 / 8 * x * (1 - 3 * x) := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ 1 - 3 * x by linarith)]
  have hc2' : 15 / 8 * x * (1 - 3 * x) ≤ 7 / 64 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hx1) (show (0 : ℝ) ≤ 3 * (x + 25 / 96) - 1 by linarith)]
  have hj24 : j2 ^ 4 ≤ 100 * j0 ^ 2 * κ ^ 2 := by
    have := pow_le_pow_left₀ (sq_nonneg j2) hj2k 2
    calc j2 ^ 4 = (j2 ^ 2) ^ 2 := by ring
      _ ≤ (10 * j0 * κ) ^ 2 := this
      _ = 100 * j0 ^ 2 * κ ^ 2 := by ring
  have T2' : j0 ^ 6 * (15 / 8 * x * (1 - 3 * x) * γ ^ 4)
      ≤ 175 / 4 * tt ^ 4 * a2 ^ 4 * (j0 ^ 4 * κ ^ 2) := by
    have e : j0 ^ 6 * γ ^ 4 = j0 ^ 2 * ((γ * j0) ^ 2) ^ 2 := by ring
    have h1 : j0 ^ 6 * γ ^ 4 ≤ j0 ^ 2 * (2 * tt ^ 2 * a2 ^ 2) ^ 2 * (100 * j0 ^ 2 * κ ^ 2) := by
      rw [e, hg2]
      have : 0 ≤ j0 ^ 2 * (2 * tt ^ 2 * a2 ^ 2) ^ 2 := by positivity
      linarith [mul_le_mul_of_nonneg_left hj24 this]
    have hpos : 0 ≤ j0 ^ 6 * γ ^ 4 := by positivity
    have h2 : j0 ^ 6 * (15 / 8 * x * (1 - 3 * x) * γ ^ 4) ≤ 7 / 64 * (j0 ^ 6 * γ ^ 4) := by
      have := mul_le_mul_of_nonneg_right hc2' hpos
      linarith [this]
    linarith [h1, h2]
  -- term 3: −(5/16)j0⁶γ⁶ ≤ 0
  have T3 : j0 ^ 6 * (5 / 16 * γ ^ 6) ≥ 0 := by positivity
  -- term 4: j0⁶(γ²/2)√Aw ≤ 10t³a₂²√R j0⁴κ²
  have hsAw : j0 * Real.sqrt Aw ≤ tt * Real.sqrt R * κ := by
    have h1 : Real.sqrt (Aw * j0 ^ 2) ≤ Real.sqrt (tt ^ 2 * R * κ ^ 2) := Real.sqrt_le_sqrt hAw
    rw [Real.sqrt_mul hAw0, Real.sqrt_sq hj0.le] at h1
    rw [show tt ^ 2 * R * κ ^ 2 = tt ^ 2 * (R * κ ^ 2) by ring, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq htt0.le, Real.sqrt_mul hR, Real.sqrt_sq hκ] at h1
    linarith [h1]
  have T4 : j0 ^ 6 * (γ ^ 2 / 2 * Real.sqrt Aw)
      ≤ 10 * tt ^ 3 * a2 ^ 2 * Real.sqrt R * (j0 ^ 4 * κ ^ 2) := by
    have e : j0 ^ 6 * (γ ^ 2 / 2 * Real.sqrt Aw)
        = 1 / 2 * (γ * j0) ^ 2 * j0 ^ 3 * (j0 * Real.sqrt Aw) := by ring
    rw [e, hg2]
    have hsR : 0 ≤ Real.sqrt R := Real.sqrt_nonneg _
    have hA : 0 ≤ 1 / 2 * (2 * tt ^ 2 * a2 ^ 2 * j2 ^ 2) * j0 ^ 3 := by positivity
    have s1 := mul_le_mul_of_nonneg_left hsAw hA
    have s2 : (tt ^ 2 * a2 ^ 2 * j2 ^ 2) * (j0 ^ 3 * (tt * Real.sqrt R * κ))
        ≤ (tt ^ 2 * a2 ^ 2 * (10 * j0 * κ)) * (j0 ^ 3 * (tt * Real.sqrt R * κ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hj2k (by positivity : (0 : ℝ) ≤ tt ^ 2 * a2 ^ 2)) (by positivity)
    linarith [s1, s2]
  -- term 5: j0⁶·(53/256)Aw ≤ (53/256)t²R j0⁴κ²
  have T5 : j0 ^ 6 * (53 / 256 * Aw) ≤ 53 / 256 * tt ^ 2 * R * (j0 ^ 4 * κ ^ 2) := by
    have := mul_le_mul_of_nonneg_left hAw (by positivity : (0 : ℝ) ≤ 53 / 256 * j0 ^ 4)
    linarith [this]
  have hmul := mul_le_mul_of_nonneg_left hH (by positivity : (0 : ℝ) ≤ j0 ^ 6)
  have eE : (Φ x - 27 / 256 * x ^ 2) = Φ x - 27 / 256 * tt ^ 2 * a0 ^ 2 := by rw [hx]; ring
  rw [eE] at hmul
  linarith [hmul, T1, T2', T3, T4, T5]

/-! ## Step 2: radial integral -/

/-- Integration in r. `PhiA r` = avg Φ(tF(r,·)), `Fsq r` = avg F(r,·)², `Hr r` = avg[Φ(tF) − (27/256)(tF)²],
`κ r` = (r/2)⁴/4!. -/
theorem radial_assembly {J0 J2 PhiA Fsq Hr : ℝ → ℝ} {μ α0 a0 a2 S : ℝ}
    (iP : IntegrableOn (fun r => J0 r ^ 6 * PhiA r * r) (Ioi 0))
    (iF : IntegrableOn (fun r => J0 r ^ 6 * Fsq r * r) (Ioi 0))
    (iH : IntegrableOn (fun r => J0 r ^ 6 * Hr r * r) (Ioi 0))
    (iW : IntervalIntegrable (fun r => J0 r ^ 6 * r) volume 0 (7 / 4))
    (iV : IntervalIntegrable (fun r => J0 r ^ 4 * J2 r ^ 2 * r) volume 0 (7 / 4))
    (iU : IntervalIntegrable (fun r => J0 r ^ 4 * ((r / 2) ^ 4 / 24) ^ 2 * r) volume 0 (7 / 4))
    (hid : μ * tt ^ 5 * (a0 - tt) = ∫ r in Ioi 0, J0 r ^ 6 * PhiA r * r)
    (hdec : ∀ r ∈ Ioi (0 : ℝ), PhiA r = 27 / 256 * (tt ^ 2 * Fsq r) + Hr r)
    (hquad : ∫ r in Ioi 0, J0 r ^ 6 * Fsq r * r = α0 * a0 ^ 2 + S)
    (hnear : ∀ r ∈ Ioc (0 : ℝ) (7 / 4), J0 r ^ 6 * Hr r
      ≤ (Φ (tt * a0) - 27 / 256 * tt ^ 2 * a0 ^ 2) * J0 r ^ 6
        + tt ^ 2 * a2 ^ 2 * Kp (tt * a0) * (J0 r ^ 4 * J2 r ^ 2)
        + (175 / 4 * tt ^ 4 * a2 ^ 4 + 53 / 256 * tt ^ 2 * (1 - a0 ^ 2 - a2 ^ 2)
          + 10 * tt ^ 3 * a2 ^ 2 * Real.sqrt (1 - a0 ^ 2 - a2 ^ 2)) * (J0 r ^ 4 * ((r / 2) ^ 4 / 24) ^ 2))
    (hfar : ∀ r ∈ Ioi (7 / 4 : ℝ), Hr r ≤ 0) :
    μ * tt ^ 5 * (a0 - tt) ≤ 27 * tt ^ 2 / 256 * (α0 * a0 ^ 2 + S)
      + (∫ r in (0 : ℝ)..(7 / 4), J0 r ^ 6 * r) * (Φ (tt * a0) - 27 / 256 * tt ^ 2 * a0 ^ 2)
      + tt ^ 2 * a2 ^ 2 * Kp (tt * a0) * (∫ r in (0 : ℝ)..(7 / 4), J0 r ^ 4 * J2 r ^ 2 * r)
      + (175 / 4 * tt ^ 4 * a2 ^ 4 + 53 / 256 * tt ^ 2 * (1 - a0 ^ 2 - a2 ^ 2)
        + 10 * tt ^ 3 * a2 ^ 2 * Real.sqrt (1 - a0 ^ 2 - a2 ^ 2))
        * (∫ r in (0 : ℝ)..(7 / 4), J0 r ^ 4 * ((r / 2) ^ 4 / 24) ^ 2 * r) := by
  set E0 := Φ (tt * a0) - 27 / 256 * tt ^ 2 * a0 ^ 2
  set c2 := tt ^ 2 * a2 ^ 2 * Kp (tt * a0)
  set c3 := 175 / 4 * tt ^ 4 * a2 ^ 4 + 53 / 256 * tt ^ 2 * (1 - a0 ^ 2 - a2 ^ 2)
    + 10 * tt ^ 3 * a2 ^ 2 * Real.sqrt (1 - a0 ^ 2 - a2 ^ 2)
  -- (1) decompose ∫ J₀⁶ PhiA r
  have hsplit1 : ∫ r in Ioi 0, J0 r ^ 6 * PhiA r * r
      = 27 / 256 * tt ^ 2 * (α0 * a0 ^ 2 + S) + ∫ r in Ioi 0, J0 r ^ 6 * Hr r * r := by
    have e : ∫ r in Ioi 0, J0 r ^ 6 * PhiA r * r
        = ∫ r in Ioi 0, (27 / 256 * tt ^ 2 * (J0 r ^ 6 * Fsq r * r) + J0 r ^ 6 * Hr r * r) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [hdec r hr]; ring
    rw [e, MeasureTheory.integral_add (Integrable.const_mul iF _) iH,
      MeasureTheory.integral_const_mul, hquad]
  -- (2) split (0,7/4] ∪ (7/4,∞)
  have hunion : Ioc (0 : ℝ) (7 / 4) ∪ Ioi (7 / 4) = Ioi 0 := Ioc_union_Ioi_eq_Ioi (by norm_num)
  have iH1 : IntegrableOn (fun r => J0 r ^ 6 * Hr r * r) (Ioc 0 (7 / 4)) :=
    iH.mono_set Ioc_subset_Ioi_self
  have iH2 : IntegrableOn (fun r => J0 r ^ 6 * Hr r * r) (Ioi (7 / 4)) :=
    iH.mono_set (Ioi_subset_Ioi (by norm_num))
  have hsplit2 : ∫ r in Ioi 0, J0 r ^ 6 * Hr r * r
      = (∫ r in Ioc 0 (7 / 4), J0 r ^ 6 * Hr r * r) + ∫ r in Ioi (7 / 4), J0 r ^ 6 * Hr r * r := by
    rw [← hunion, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi iH1 iH2]
  -- (3) the far part is ≤ 0
  have hfar' : ∫ r in Ioi (7 / 4), J0 r ^ 6 * Hr r * r ≤ 0 := by
    have := setIntegral_mono_on iH2 (integrableOn_zero) measurableSet_Ioi (fun r hr => by
      have hr0 : 0 ≤ r := by have : (7 / 4 : ℝ) < r := hr; linarith
      have h1 : J0 r ^ 6 * Hr r ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (hfar r hr)
      exact mul_nonpos_of_nonpos_of_nonneg h1 hr0)
    simpa using this
  -- (4) the near part is ≤ E0·W + c2·V + c3·U
  set B : ℝ → ℝ := fun r => E0 * (J0 r ^ 6 * r) + c2 * (J0 r ^ 4 * J2 r ^ 2 * r)
    + c3 * (J0 r ^ 4 * ((r / 2) ^ 4 / 24) ^ 2 * r) with hB
  have iB : IntegrableOn B (Ioc 0 (7 / 4)) :=
    ((Integrable.const_mul iW.1 _).add (Integrable.const_mul iV.1 _)).add
      (Integrable.const_mul iU.1 _)
  have hnear' : ∫ r in Ioc 0 (7 / 4), J0 r ^ 6 * Hr r * r ≤ ∫ r in Ioc 0 (7 / 4), B r := by
    apply setIntegral_mono_on iH1 iB measurableSet_Ioc
    intro r hr
    have hr0 : 0 ≤ r := hr.1.le
    have := mul_le_mul_of_nonneg_right (hnear r hr) hr0
    simp only [hB]
    linarith [this]
  have hBint : ∫ r in Ioc 0 (7 / 4), B r
      = E0 * (∫ r in (0 : ℝ)..(7 / 4), J0 r ^ 6 * r)
        + c2 * (∫ r in (0 : ℝ)..(7 / 4), J0 r ^ 4 * J2 r ^ 2 * r)
        + c3 * (∫ r in (0 : ℝ)..(7 / 4), J0 r ^ 4 * ((r / 2) ^ 4 / 24) ^ 2 * r) := by
    simp only [hB]
    have jW : Integrable (fun r => E0 * (J0 r ^ 6 * r)) (volume.restrict (Ioc 0 (7 / 4))) :=
      Integrable.const_mul iW.1 _
    have jV : Integrable (fun r => c2 * (J0 r ^ 4 * J2 r ^ 2 * r)) (volume.restrict (Ioc 0 (7 / 4))) :=
      Integrable.const_mul iV.1 _
    have jU : Integrable (fun r => c3 * (J0 r ^ 4 * ((r / 2) ^ 4 / 24) ^ 2 * r))
        (volume.restrict (Ioc 0 (7 / 4))) := Integrable.const_mul iU.1 _
    have jWV : Integrable (fun r => E0 * (J0 r ^ 6 * r) + c2 * (J0 r ^ 4 * J2 r ^ 2 * r))
        (volume.restrict (Ioc 0 (7 / 4))) := jW.add jV
    rw [MeasureTheory.integral_add jWV jU, MeasureTheory.integral_add jW jV,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 7 / 4),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 7 / 4),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 7 / 4)]
  rw [hid, hsplit1, hsplit2]
  rw [hBint] at hnear'
  linarith [hnear', hfar']

/-! ## Assembly: Proposition 3.1 -/

/-- Complete derivation of Proposition 3.1 (prop:large-mean) from the given analytic data.
The premises come in three groups:
* literature: the DLMF hypotheses of Lemma 2.1 (`hs`, continuity), the tabulated bounds for α₀;
* data for step 1 (t = ½): Φ-identity, avg F = a₀, eq:quadratic-spectral;
* data for step 2 (t = 5/12): Φ-identity, decomposition and eq:prop31-b, eq:tail-L2, Φ ≤ (27/256)x² for r > 7/4. -/
theorem prop_large_mean
    {J0 J2 : ℝ → ℝ} {F w : ℝ → ℝ → ℝ} {γ : ℝ → ℝ} {μ α0 a0 a2 S : ℝ}
    -- literature
    (hs : Lemma21.SeriesHyp J0 J2) (hc0 : ContinuousOn J0 (Icc 0 (7 / 4)))
    (hc2 : ContinuousOn J2 (Icc 0 (7 / 4)))
    (hα0lo : 101 / 300 < α0) (hα0hi : α0 < 337 / 1000)
    -- basic information about f
    (hμ : α0 ≤ μ) (ha0lt : a0 < 1) (ha2 : 0 ≤ a2) (ha2' : a2 ^ 2 ≤ 1 / 2)
    (hsum : a0 ^ 2 + a2 ^ 2 ≤ 1)
    (hS1 : S < α0 / 9 * (1 - a0 ^ 2)) (hS2 : S ≤ 19 / 1000 * (1 - a0 ^ 2) + 9 / 1000)
    -- angular integrability
    (hF : ∀ r, IntervalIntegrable (F r) volume 0 (2 * π))
    (hF2 : ∀ r, IntervalIntegrable (fun x => F r x ^ 2) volume 0 (2 * π))
    (hΦ1 : ∀ r, IntervalIntegrable (fun x => Φ (F r x / 2)) volume 0 (2 * π))
    (hΦ2 : ∀ r, IntervalIntegrable (fun x => Φ (tt * F r x)) volume 0 (2 * π))
    (hw : ∀ r, IntervalIntegrable (w r) volume 0 (2 * π))
    (hw2 : ∀ r, IntervalIntegrable (fun x => w r x ^ 2) volume 0 (2 * π))
    -- radial integrability
    (i1 : IntegrableOn (fun r => J0 r ^ 6 * avg (fun x => Φ (F r x / 2)) * r) (Ioi 0))
    (i2 : IntegrableOn (fun r => J0 r ^ 6 * avg (fun x => F r x ^ 2) * r) (Ioi 0))
    (i0 : IntegrableOn (fun r => J0 r ^ 6 * r) (Ioi 0))
    (i3 : IntegrableOn (fun r => J0 r ^ 6 * avg (fun x => Φ (tt * F r x)) * r) (Ioi 0))
    (i4 : IntegrableOn (fun r => J0 r ^ 6
      * avg (fun x => Φ (tt * F r x) - 27 / 256 * (tt * F r x) ^ 2) * r) (Ioi 0))
    -- Φ-identity (eq:Phi-identity) and eq:quadratic-spectral
    (hid1 : μ * (1 / 2) ^ 5 * (a0 - 1 / 2)
      = ∫ r in Ioi 0, J0 r ^ 6 * avg (fun x => Φ (F r x / 2)) * r)
    (hid2 : μ * tt ^ 5 * (a0 - tt) = ∫ r in Ioi 0, J0 r ^ 6 * avg (fun x => Φ (tt * F r x)) * r)
    (hmean : ∀ r, 0 < r → J0 r ≠ 0 → avg (F r) = a0)
    (hquad : ∫ r in Ioi 0, J0 r ^ 6 * avg (fun x => F r x ^ 2) * r = α0 * a0 ^ 2 + S)
    (hα : ∫ r in Ioi 0, J0 r ^ 6 * r = α0)
    -- decomposition for r ≤ 7/4 (eq:normalized-extension), eq:prop31-b, eq:tail-L2
    (hdecomp : ∀ r ∈ Ioc (0 : ℝ) (7 / 4), ∀ x, tt * F r x = tt * a0 + γ r * cos x + w r x)
    (hγdef : ∀ r ∈ Ioc (0 : ℝ) (7 / 4), γ r * J0 r = Real.sqrt 2 * tt * a2 * J2 r)
    (hm0 : ∀ r ∈ Ioc (0 : ℝ) (7 / 4), avg (w r) = 0)
    (hm1 : ∀ r ∈ Ioc (0 : ℝ) (7 / 4), avg (fun x => cos x * w r x) = 0)
    (htail : ∀ r ∈ Ioc (0 : ℝ) (7 / 4), avg (fun x => w r x ^ 2) * J0 r ^ 2
      ≤ tt ^ 2 * (1 - a0 ^ 2 - a2 ^ 2) * ((r / 2) ^ 4 / 24) ^ 2) :
    a0 < 5 / 8 := by
  by_contra hcon
  have ha0 : 5 / 8 ≤ a0 := not_lt.mp hcon
  have hα0 : 0 < α0 := by linarith
  have iq : ∀ r, IntervalIntegrable (fun x => 27 / 256 * (tt * F r x) ^ 2) volume 0 (2 * π) := by
    intro r
    have e : (fun x => 27 / 256 * (tt * F r x) ^ 2) = fun x => 27 / 256 * (tt ^ 2 * F r x ^ 2) := by
      funext x; ring
    rw [e]; exact ((hF2 r).const_mul _).const_mul _
  -- step 1
  have hstep1 := step1 hF hF2 hΦ1 i1 i2 i0 hid1 hmean hquad hα
  have ha45 : a0 < 4 / 5 := Chains.large_mean_step1 hα0 hμ ha0 ha0lt hS1 hstep1
  have htt : tt = 5 / 12 := rfl
  have hx1 : 25 / 96 ≤ tt * a0 := by rw [htt]; linarith
  have hx2 : tt * a0 ≤ 1 / 3 := by rw [htt]; linarith
  -- step 2: pointwise estimate
  have hnear : ∀ r ∈ Ioc (0 : ℝ) (7 / 4),
      J0 r ^ 6 * avg (fun x => Φ (tt * F r x) - 27 / 256 * (tt * F r x) ^ 2)
      ≤ (Φ (tt * a0) - 27 / 256 * tt ^ 2 * a0 ^ 2) * J0 r ^ 6
        + tt ^ 2 * a2 ^ 2 * Kp (tt * a0) * (J0 r ^ 4 * J2 r ^ 2)
        + (175 / 4 * tt ^ 4 * a2 ^ 4 + 53 / 256 * tt ^ 2 * (1 - a0 ^ 2 - a2 ^ 2)
          + 10 * tt ^ 3 * a2 ^ 2 * Real.sqrt (1 - a0 ^ 2 - a2 ^ 2))
          * (J0 r ^ 4 * ((r / 2) ^ 4 / 24) ^ 2) := by
    intro r hr
    have hrI : r ∈ Icc (0 : ℝ) (7 / 4) := ⟨hr.1.le, hr.2⟩
    have hx0 : 0 ≤ r ^ 2 / 4 := by positivity
    have hxx : r ^ 2 / 4 ≤ 49 / 64 := by nlinarith [hr.1, hr.2]
    obtain ⟨hj0, hj2, hratio, hj2k⟩ :=
      Analysis1.bessel_pointwise hx0 hxx (hs.1 r hrI) (hs.2 r hrI)
    have hκeq : (r ^ 2 / 4) ^ 2 / 24 = (r / 2) ^ 4 / 24 := by ring
    rw [hκeq] at hj2k
    -- range of γ
    have hj0' : J0 r ≠ 0 := hj0.ne'
    have hγeq : γ r = Real.sqrt 2 * tt * a2 * (J2 r / J0 r) := by
      have := hγdef r hr
      field_simp
      linarith
    have hq0 : 0 ≤ J2 r / J0 r := div_nonneg hj2 hj0.le
    have hq : J2 r / J0 r < 4 / 5 := by rw [div_lt_iff₀ hj0]; linarith
    obtain ⟨hγ0, hγ1⟩ := gamma_le ha2 ha2' hq0 hq
    rw [← htt] at hγ0 hγ1
    rw [← hγeq] at hγ0 hγ1
    -- angular estimate
    have hdec := hdecomp r hr
    have eH : (fun x => Φ (tt * F r x) - 27 / 256 * (tt * F r x) ^ 2)
        = fun x => Φ (tt * a0 + γ r * cos x + w r x)
          - 27 / 256 * (tt * a0 + γ r * cos x + w r x) ^ 2 := by
      funext x; rw [hdec x]
    have hΦr : IntervalIntegrable (fun x => Φ (tt * a0 + γ r * cos x + w r x)) volume 0 (2 * π) := by
      have e : (fun x => Φ (tt * a0 + γ r * cos x + w r x)) = fun x => Φ (tt * F r x) := by
        funext x; rw [hdec x]
      rw [e]; exact hΦ2 r
    have hsqr : IntervalIntegrable (fun x => (tt * a0 + γ r * cos x + w r x) ^ 2) volume 0 (2 * π) := by
      have e : (fun x => (tt * a0 + γ r * cos x + w r x) ^ 2) = fun x => tt ^ 2 * F r x ^ 2 := by
        funext x; rw [← hdec x]; ring
      rw [e]; exact (hF2 r).const_mul _
    have hang := angular_bound (by linarith) hx2 hγ0 hγ1 (hw r) (hw2 r) hΦr hsqr (hm0 r hr) (hm1 r hr)
    rw [← eH] at hang
    have hR : 0 ≤ 1 - a0 ^ 2 - a2 ^ 2 := by linarith
    exact radial_pointwise hj0 hj2 hj2k (by positivity) ha2 hR (hγdef r hr) hγ0
      (avg_nonneg (fun x _ => sq_nonneg _)) (htail r hr) hx1 hx2 hang
  -- step 2: r > 7/4
  have hfar : ∀ r ∈ Ioi (7 / 4 : ℝ),
      avg (fun x => Φ (tt * F r x) - 27 / 256 * (tt * F r x) ^ 2) ≤ 0 := by
    intro r _
    have h0 : avg (fun x => Φ (tt * F r x) - 27 / 256 * (tt * F r x) ^ 2) ≤ avg (fun _ => (0 : ℝ)) := by
      apply avg_mono ((hΦ2 r).sub (iq r))
        ((by fun_prop : Continuous fun _ : ℝ => (0 : ℝ)).intervalIntegrable _ _)
      intro x _
      have := phi_le (tt * F r x)
      linarith
    rwa [avg_const] at h0
  -- step 2: radial integral
  have hdec' : ∀ r ∈ Ioi (0 : ℝ), avg (fun x => Φ (tt * F r x))
      = 27 / 256 * (tt ^ 2 * avg (fun x => F r x ^ 2))
        + avg (fun x => Φ (tt * F r x) - 27 / 256 * (tt * F r x) ^ 2) := by
    intro r _
    rw [avg_sub (hΦ2 r) (iq r)]
    have e : avg (fun x => 27 / 256 * (tt * F r x) ^ 2) = 27 / 256 * (tt ^ 2 * avg (fun x => F r x ^ 2)) := by
      rw [show (fun x => 27 / 256 * (tt * F r x) ^ 2) = fun x => 27 / 256 * (tt ^ 2 * F r x ^ 2) by
        funext x; ring, avg_const_mul, avg_const_mul]
    rw [e]; ring
  have iW : IntervalIntegrable (fun r => J0 r ^ 6 * r) volume 0 (7 / 4) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num)]
    exact (hc0.pow 6).mul continuousOn_id
  have iV : IntervalIntegrable (fun r => J0 r ^ 4 * J2 r ^ 2 * r) volume 0 (7 / 4) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num)]
    exact ((hc0.pow 4).mul (hc2.pow 2)).mul continuousOn_id
  have iU : IntervalIntegrable (fun r => J0 r ^ 4 * ((r / 2) ^ 4 / 24) ^ 2 * r) volume 0 (7 / 4) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num)]
    exact ((hc0.pow 4).mul (Continuous.continuousOn (by fun_prop))).mul continuousOn_id
  have hmain := radial_assembly i3 i2 i4 iW iV iU hid2 hdec' hquad hnear hfar
  -- the three integrals of Lemma 2.1
  have hW := Lemma21.W_gt hs hc0
  have hV := Lemma21.V_lt hs hc0 hc2
  have hU := Lemma21.U_lt hs hc0
  have hV0 : 0 ≤ ∫ r in (0 : ℝ)..(7 / 4), J0 r ^ 4 * J2 r ^ 2 * r := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro r hr; have := hr.1; positivity
  have hU0 : 0 ≤ ∫ r in (0 : ℝ)..(7 / 4), J0 r ^ 4 * ((r / 2) ^ 4 / 24) ^ 2 * r := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro r hr; have := hr.1; positivity
  exact Chains.large_mean_step2 hα0 hα0hi hμ ha0 ha45 ha2 ha2' hsum hS2 hW hV0 hV hU0 hU
    (by linarith [hmain])

end

end SteinTomas.Section3

#print axioms SteinTomas.Section3.prop_large_mean
