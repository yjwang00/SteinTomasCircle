import SteinTomasCircle.MainProof.Prep

namespace SteinTomas.S6

open Real MeasureTheory Set Function Filter Topology
open scoped ENNReal

noncomputable section

/-- The sixth-power extension energy on real antipodal data. -/
def energy (f : ℝ → ℝ) : ℝ := ∫ x, S2P.Ec f x ^ 6

/-- Squared L² norm on the circle. -/
def sqNorm (f : ℝ → ℝ) : ℝ := ∫ θ, f θ ^ 2 ∂σ

lemma sqNorm_nonneg (f : ℝ → ℝ) : 0 ≤ sqNorm f :=
  integral_nonneg fun _ => sq_nonneg _

lemma Ec_const_mul (f : ℝ → ℝ) (c : ℝ) (x : ℝ × ℝ) :
    S2P.Ec (fun θ => c * f θ) x = c * S2P.Ec f x := by
  rw [S5C.Ec_set, S5C.Ec_set, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun θ => by ring)

lemma energy_const_mul (f : ℝ → ℝ) (c : ℝ) :
    energy (fun θ => c * f θ) = c ^ 6 * energy f := by
  simp only [energy, Ec_const_mul, mul_pow, integral_const_mul]

lemma sqNorm_const_mul (f : ℝ → ℝ) (c : ℝ) :
    sqNorm (fun θ => c * f θ) = c ^ 2 * sqNorm f := by
  simp only [sqNorm, mul_pow, integral_const_mul]

private lemma Ec_add_scaled {f h : ℝ → ℝ} (hf : MemLp f 2 σ) (hh : MemLp h 2 σ)
    (t : ℝ) (x : ℝ × ℝ) :
    S2P.Ec (fun θ => f θ + t * h θ) x = S2P.Ec f x + t * S2P.Ec h x := by
  haveI : IsFiniteMeasure σ := isFin
  have hcos : Continuous (fun θ => cos (S5A.dd x θ)) := by unfold S5A.dd; fun_prop
  have hbd : ∀ θ, |cos (S5A.dd x θ)| ≤ 1 := fun θ => abs_cos_le_one _
  have hfi := S5C.imul (hf.integrable one_le_two) hcos hbd
  have hhi := S5C.imul (hh.integrable one_le_two) hcos hbd
  rw [S5C.Ec_set, S5C.Ec_set, S5C.Ec_set, ← integral_const_mul,
    ← integral_add hfi (hhi.const_mul t)]
  exact integral_congr_ae (Eventually.of_forall fun θ => by dsimp only; ring)

private lemma integrable_mixed_six {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u v : X → ℝ} (hum : AEStronglyMeasurable u μ) (hvm : AEStronglyMeasurable v μ)
    (hu : Integrable (fun x => u x ^ 6) μ) (hv : Integrable (fun x => v x ^ 6) μ)
    {k : ℕ} (hk : k ≤ 6) : Integrable (fun x => u x ^ (6 - k) * v x ^ k) μ := by
  refine Integrable.mono' (hu.add hv) ((hum.pow _).mul (hvm.pow _))
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, ← pow_abs, ← pow_abs]
  calc
    _ ≤ max |u x| |v x| ^ (6 - k) * max |u x| |v x| ^ k :=
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ _) _)
        (pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) _) (by positivity) (by positivity)
    _ = max |u x| |v x| ^ 6 := by rw [← pow_add, Nat.sub_add_cancel hk]
    _ ≤ u x ^ 6 + v x ^ 6 := by
      rcases le_total |u x| |v x| with h | h
      · rw [max_eq_right h, pow_abs, abs_of_nonneg (show 0 ≤ v x ^ 6 by positivity)]
        exact le_add_of_nonneg_left (by positivity)
      · rw [max_eq_left h, pow_abs, abs_of_nonneg (show 0 ≤ u x ^ 6 by positivity)]
        exact le_add_of_nonneg_right (by positivity)

private lemma integral_pow_six_add {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u v : X → ℝ} (hum : AEStronglyMeasurable u μ) (hvm : AEStronglyMeasurable v μ)
    (hu : Integrable (fun x => u x ^ 6) μ) (hv : Integrable (fun x => v x ^ 6) μ) (t : ℝ) :
    ∫ x, (u x + t * v x) ^ 6 ∂μ =
      (∫ x, u x ^ 6 ∂μ) + 6 * t * (∫ x, u x ^ 5 * v x ∂μ) +
        15 * t ^ 2 * (∫ x, u x ^ 4 * v x ^ 2 ∂μ) +
        t ^ 3 * (20 * (∫ x, u x ^ 3 * v x ^ 3 ∂μ) +
          t * (15 * (∫ x, u x ^ 2 * v x ^ 4 ∂μ) +
            t * (6 * (∫ x, u x * v x ^ 5 ∂μ) + t * ∫ x, v x ^ 6 ∂μ))) := by
  have e (x : X) : (u x + t * v x) ^ 6 =
      ∑ k ∈ Finset.range 7, (Nat.choose 6 k : ℝ) * t ^ k * (u x ^ (6 - k) * v x ^ k) := by
    norm_num [Finset.sum_range_succ, Nat.choose]
    ring
  simp_rw [e]
  rw [integral_finsetSum _ (fun k hk => (integrable_mixed_six hum hvm hu hv
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).const_mul _)]
  norm_num [Finset.sum_range_succ, Nat.choose, integral_const_mul]
  ring

/-- First and second coefficients of a nonnegative polynomial at a zero. -/
private lemma quadratic_coefficients {a b : ℝ} {R : ℝ → ℝ} (hR : Continuous R)
    (h : ∀ t : ℝ, 0 ≤ t * a + t ^ 2 * b + t ^ 3 * R t) : a = 0 ∧ 0 ≤ b := by
  have ht : Tendsto (fun t : ℝ => a + t * b + t ^ 2 * R t) (𝓝 0) (𝓝 a) := by
    simpa using
      ((tendsto_const_nhds.add ((continuous_id.tendsto (0 : ℝ)).mul_const b)).add
        (((continuous_id.tendsto (0 : ℝ)).pow 2).mul (hR.tendsto 0)))
  have hpos : 0 ≤ a := by
    apply ge_of_tendsto (ht.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
    filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with t ht'
    have ht0 : 0 < t := ht'
    apply nonneg_of_mul_nonneg_right _ ht0
    convert h t using 1 <;> ring
  have hneg : a ≤ 0 := by
    haveI : (𝓝[<] (0 : ℝ)).NeBot := nhdsLT_neBot_of_exists_lt ⟨-1, by norm_num⟩
    apply le_of_tendsto (ht.mono_left (nhdsWithin_le_nhds (s := Iio (0 : ℝ))))
    filter_upwards [self_mem_nhdsWithin (s := Iio (0 : ℝ))] with t ht'
    have ht0 : t < 0 := ht'
    apply nonpos_of_mul_nonneg_right _ ht0
    convert h t using 1 <;> ring
  have ha := le_antisymm hneg hpos
  refine ⟨ha, ?_⟩
  have hb : Tendsto (fun t : ℝ => b + t * R t) (𝓝 0) (𝓝 b) := by
    simpa using tendsto_const_nhds.add ((continuous_id.tendsto (0 : ℝ)).mul (hR.tendsto 0))
  apply ge_of_tendsto (hb.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with t ht'
  have ht0 : 0 < t := ht'
  apply nonneg_of_mul_nonneg_right _ (pow_pos ht0 2)
  simp only [ha, mul_zero, zero_add] at h
  convert h t using 1 <;> ring

/-- Euler–Lagrange pairing and second variation for the normalized maximizer. -/
structure MaxLit (g : ℝ → ℝ) : Prop where
  i5 : Integrable (fun x => S2P.Ec g x ^ 5 * S2P.Ec S2P.e0 x)
  el : ∫ x, S2P.Ec g x ^ 5 * S2P.Ec S2P.e0 x =
    energy g * S2F.a0 g
  sv : ∀ h : ℝ → ℝ, MemLp h 2 σ → Periodic h (2 * π) → (∀ θ, h (θ + π) = h θ) →
    ∫⁻ x, ENNReal.ofReal (5 * (S2P.Ec g x ^ 4 * S2P.Ec h x ^ 2)) ≤
      ENNReal.ofReal (energy g * (sqNorm h + 4 * (∫ θ, g θ * h θ ∂σ) ^ 2))

theorem maximizer_variations {f : ℝ → ℝ} {M : ℝ} (hf : Adm f)
    (hB : sqNorm f = 1) (hE : energy f = M)
    (hST : ∀ h, MemLp h 2 σ → Integrable (fun x => S2P.Ec h x ^ 6))
    (hMall : ∀ h, MemLp h 2 σ → Periodic h (2 * π) → (∀ θ, h (θ + π) = h θ) →
      energy h ≤ M * sqNorm h ^ 3) : MaxLit f := by
  have hvar (h : ℝ → ℝ) (hh : MemLp h 2 σ) (hp : Periodic h (2 * π))
      (ha : ∀ θ, h (θ + π) = h θ) :
      (∫ x, S2P.Ec f x ^ 5 * S2P.Ec h x) = M * (∫ θ, f θ * h θ ∂σ) ∧
        5 * (∫ x, S2P.Ec f x ^ 4 * S2P.Ec h x ^ 2) ≤
          M * (sqNorm h + 4 * (∫ θ, f θ * h θ ∂σ) ^ 2) := by
    let u := S2P.Ec f
    let v := S2P.Ec h
    let A : ℝ := ∫ θ, f θ * h θ ∂σ
    let B := sqNorm h
    let C : ℝ := ∫ x, u x ^ 5 * v x
    let D : ℝ := ∫ x, u x ^ 4 * v x ^ 2
    let R (t : ℝ) :=
      M * (8 * A ^ 3 + 12 * A * B + t * (3 * B ^ 2 + 12 * A ^ 2 * B +
        t * (6 * A * B ^ 2 + t * B ^ 3))) -
        (20 * (∫ x, u x ^ 3 * v x ^ 3) + t * (15 * (∫ x, u x ^ 2 * v x ^ 4) +
          t * (6 * (∫ x, u x * v x ^ 5) + t * ∫ x, v x ^ 6)))
    have hR : Continuous R := by unfold R; fun_prop
    have hcoef : ∀ t : ℝ, 0 ≤ t * (6 * (M * A - C)) +
        t ^ 2 * (3 * M * (B + 4 * A ^ 2) - 15 * D) + t ^ 3 * R t := by
      intro t
      have hi := hf.memLp.integrable_sq
      have hj := (int_mul2 hf.memLp hh).const_mul (2 * t)
      have hij : Integrable (fun θ => f θ ^ 2 + (2 * t) * (f θ * h θ)) σ := hi.add hj
      have hk := hh.integrable_sq.const_mul (t ^ 2)
      have hn : sqNorm (fun θ => f θ + t * h θ) = 1 + 2 * t * A + t ^ 2 * B := by
        unfold sqNorm
        rw [show (fun θ => (f θ + t * h θ) ^ 2) =
          (fun θ => (f θ ^ 2 + (2 * t) * (f θ * h θ)) + t ^ 2 * h θ ^ 2) from
          funext fun θ => by ring]
        rw [integral_add hij hk, integral_add hi hj, integral_const_mul,
          integral_const_mul, show (∫ θ, f θ ^ 2 ∂σ) = 1 from hB]
        rfl
      have hle := hMall (fun θ => f θ + t * h θ) (hf.memLp.add (hh.const_mul t))
        (fun θ => by simp only [hf.per θ, hp θ])
        (fun θ => by simp only [hf.anti θ, ha θ])
      rw [hn, energy] at hle
      simp_rw [Ec_add_scaled hf.memLp hh] at hle
      rw [integral_pow_six_add (S5C.Ec_cont hf.memLp).aestronglyMeasurable
        (S5C.Ec_cont hh).aestronglyMeasurable (hST _ hf.memLp) (hST _ hh),
        show (∫ x, S2P.Ec f x ^ 6) = M from hE] at hle
      have hnonneg := sub_nonneg.mpr hle
      convert hnonneg using 1 <;> dsimp only [R, A, B, C, D, u, v] <;> ring
    obtain ⟨h1, h2⟩ := quadratic_coefficients hR hcoef
    exact ⟨by change C = M * A; linarith, by change 5 * D ≤ M * (B + 4 * A ^ 2); linarith⟩
  haveI : IsFiniteMeasure σ := isFin
  have he0 : MemLp S2P.e0 2 σ := memLp_const _
  have hmixed (h : ℝ → ℝ) (hh : MemLp h 2 σ) {k : ℕ} (hk : k ≤ 6) :=
    integrable_mixed_six (S5C.Ec_cont hf.memLp).aestronglyMeasurable
      (S5C.Ec_cont hh).aestronglyMeasurable (hST _ hf.memLp) (hST _ hh) hk
  refine ⟨?_, ?_, ?_⟩
  · simpa only [pow_one, show 6 - 1 = 5 by decide] using hmixed _ he0 (k := 1) (by decide)
  · have h := (hvar S2P.e0 he0 (fun _ => rfl) (fun _ => rfl)).1
    have ha0 : S2F.a0 f = ∫ θ, f θ * S2P.e0 θ ∂σ := by
      unfold S2F.a0 S2P.e0
      rw [intervalIntegral.integral_of_le (by positivity), integral_mul_const, σ]
      exact mul_comm _ _
    rw [h, ha0, hE]
  · intro h hh hp ha
    have hi : Integrable (fun x => S2P.Ec f x ^ 4 * S2P.Ec h x ^ 2) := by
      simpa only [show 6 - 2 = 4 by decide] using hmixed _ hh (k := 2) (by decide)
    rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul 5)
      (Eventually.of_forall fun x => by positivity), integral_const_mul, hE]
    exact ENNReal.ofReal_le_ofReal (hvar h hh hp ha).2

end

end SteinTomas.S6
