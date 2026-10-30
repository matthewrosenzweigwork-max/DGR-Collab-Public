import DGPS.Lipschitz.EquilibriumPotential
import SharpSymmetricLSI.Paper.Prop21Assembly1

/-!
# Second variation along bounded continuous mean-zero density tilts

The cubic scalar entropy remainder gives the exact quadratic limit in the uniform
perturbation domain. No spatial second derivative of either potential is used.
-/

open MeasureTheory Filter Topology InformationTheory

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- The second-order free-energy potential along a continuous mean-zero perturbation. -/
theorem t01_potential_second_variation (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (h : C(Torus d, ℝ))
    (hmean : ∫ x, h x ∂(μ : Measure (Torus d)) = 0) :
    Tendsto (fun t : ℝ => lip034_potential (A := A) (μ : Measure (Torus d)) (t • h) / t ^ 2)
      (𝓝[≠] 0) (𝓝 (((∫ x, h x ^ 2 ∂(μ : Measure (Torus d))) +
        ∫ x, h x * centeredOperatorC A (μ : Measure (Torus d)) h x
          ∂(μ : Measure (Torus d))) / 2)) := by
  obtain ⟨B, hB0, hB⟩ := exists_abs_bound h.continuous
  have hi := integrable_cts (μ : Measure (Torus d)) h
  have hh2 : Integrable (fun x => h x ^ 2) (μ : Measure (Torus d)) :=
    (h.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let Q := ∫ x, h x * centeredOperatorC A (μ : Measure (Torus d)) h x
    ∂(μ : Measure (Torus d))
  have hsmall : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 ∧ |t| * B ≤ 1 / 2 := by
    have ht : Tendsto (fun t : ℝ => |t| * B) (𝓝 0) (𝓝 0) := by
      simpa only [abs_zero, zero_mul] using (continuous_abs.tendsto (0 : ℝ)).mul_const B
    filter_upwards [(ht.mono_left nhdsWithin_le_nhds).eventually
      (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)), self_mem_nhdsWithin] with t ht ht0
    exact ⟨ht0, ht⟩
  have hformula (t : ℝ) (ht : |t| * B ≤ 1 / 2) :
      lip034_potential (A := A) (μ : Measure (Torus d)) (t • h) =
        (∫ x, klFun (1 + t * h x) ∂(μ : Measure (Torus d))) + t ^ 2 / 2 * Q := by
    have hpos : t • h ∈ posSet (Torus d) := by
      intro x
      have hx : |t * h x| ≤ 1 / 2 := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left (hB x) (abs_nonneg t)).trans ht
      change 0 < 1 + t * h x
      linarith [(abs_le.mp hx).1]
    have hk : Integrable (fun x => klFun (1 + t * h x)) (μ : Measure (Torus d)) :=
      (continuous_klFun.comp (continuous_const.add
        (continuous_const.mul h.continuous))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hentropy : (∫ x, (1 + t * h x) * Real.log (1 + t * h x)
        ∂(μ : Measure (Torus d))) = ∫ x, klFun (1 + t * h x) ∂(μ : Measure (Torus d)) := by
      have he : (fun x => (1 + t * h x) * Real.log (1 + t * h x)) =
          fun x => klFun (1 + t * h x) + t * h x := by
        funext x
        rw [klFun_apply]
        ring
      rw [he, integral_add hk (hi.const_mul t), integral_const_mul, hmean]
      ring
    unfold lip034_potential
    rw [map_add, map_smul, intCLM_apply, intCLM_apply]
    simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply, ContinuousMap.one_apply,
      ContinuousMap.smul_apply, smul_eq_mul, map_smul]
    simp_rw [nemLog_apply hpos]
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    rw [hentropy]
    have hquad : (∫ x, (t * h x) *
        (t * centeredOperatorC A (μ : Measure (Torus d)) h x)
          ∂(μ : Measure (Torus d))) = t ^ 2 * Q := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only [Q]; ring
    rw [hquad]
    ring
  have hbound : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      |lip034_potential (A := A) (μ : Measure (Torus d)) (t • h) / t ^ 2 -
        (((∫ x, h x ^ 2 ∂(μ : Measure (Torus d))) + Q) / 2)| ≤ 4 * B ^ 3 * |t| := by
    filter_upwards [hsmall] with t ⟨ht0, ht⟩
    rw [hformula t ht]
    have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht0
    have hth : ∀ x, |t * h x| ≤ 1 / 2 := fun x => by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hB x) (abs_nonneg t)).trans ht
    have hint : Integrable (fun x => klFun (1 + t * h x)) (μ : Measure (Torus d)) :=
      (continuous_klFun.comp (continuous_const.add
        (continuous_const.mul h.continuous))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have he : ((∫ x, klFun (1 + t * h x) ∂(μ : Measure (Torus d))) + t ^ 2 / 2 * Q) / t ^ 2 -
        (((∫ x, h x ^ 2 ∂(μ : Measure (Torus d))) + Q) / 2) =
        (∫ x, (klFun (1 + t * h x) - (t * h x) ^ 2 / 2)
          ∂(μ : Measure (Torus d))) / t ^ 2 := by
      rw [integral_sub hint (hh2.const_mul (t ^ 2 / 2) |>.congr
        (Eventually.of_forall fun x => by simp only; ring))]
      have hsq : (∫ x, (t * h x) ^ 2 / 2 ∂(μ : Measure (Torus d))) =
          t ^ 2 / 2 * ∫ x, h x ^ 2 ∂(μ : Measure (Torus d)) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      rw [hsq]
      field_simp
      <;> ring
    rw [he, abs_div, abs_of_pos ht2, div_le_iff₀ ht2]
    refine (abs_integral_le_integral_abs).trans ?_
    calc
      (∫ x, |klFun (1 + t * h x) - (t * h x) ^ 2 / 2|
          ∂(μ : Measure (Torus d))) ≤ ∫ _x, 4 * (|t| * B) ^ 3 ∂(μ : Measure (Torus d)) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (integrable_const _) (Eventually.of_forall fun x => ?_)
        refine (SharpLSI.abs_klFun_one_add_sub_le (hth x)).trans ?_
        have hx : |t * h x| ≤ |t| * B := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hB x) (abs_nonneg t)
        nlinarith [pow_le_pow_left₀ (abs_nonneg _) hx 3]
      _ = 4 * (|t| * B) ^ 3 := by simp
      _ = 4 * B ^ 3 * |t| * t ^ 2 := by rw [mul_pow, ← sq_abs t]; ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun t : ℝ => 4 * B ^ 3 * |t|)
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [hbound] with t ht
    simpa only [Real.norm_eq_abs] using ht
  · have ht := (continuous_abs.tendsto (0 : ℝ)).const_mul (4 * B ^ 3)
    simpa only [abs_zero, mul_zero] using ht.mono_left nhdsWithin_le_nhds

end DGPS.Lipschitz
