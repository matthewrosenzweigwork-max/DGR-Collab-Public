import LeanResearch.PeriodicAttractiveLogGas.ConditionalKernelL2
import LeanResearch.PeriodicAttractiveLogGas.CenteredL2
import LeanResearch.PeriodicAttractiveLogGas.DobrushinSpectralGap

/-! The actual L2 assembly of the source column-sum variance argument.
The kernel hypotheses are genuine coordinate independence and preservation
of the actual joint law by resampling. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators InnerProductSpace

namespace PeriodicAttractiveLogGas.DobrushinVariance

open CoordinateOscillation ConditionalL2Projections ConditionalKernelL2 CenteredL2

variable {ι : Type*} {E : ι → Type*} [DecidableEq ι]
variable [∀ i, MeasurableSpace (E i)] [Fintype ι] [Nonempty ι]
variable (μ : Measure (∀ k, E k)) [IsProbabilityMeasure μ]

omit [DecidableEq ι] in
theorem coordinateAverage_mem_centered (f : Lp ℝ 2 μ)
    (hf : f ∈ centeredSubspace μ) : coordinateAverage E μ f ∈ centeredSubspace μ := by
  rw [mem_centeredSubspace_iff, integral_coordinateAverage]
  exact (mem_centeredSubspace_iff μ f).mp hf

def centeredAverage : Centered μ →L[ℝ] Centered μ :=
  (coordinateAverage E μ).restrict (coordinateAverage_mem_centered μ)

omit [DecidableEq ι] in
theorem coe_centeredAverage (f : Centered μ) :
    (centeredAverage μ f : Lp ℝ 2 μ) = coordinateAverage E μ (f : Lp ℝ 2 μ) := rfl

omit [DecidableEq ι] in
theorem centeredAverage_isSelfAdjoint : IsSelfAdjoint (centeredAverage μ) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change ⟪coordinateAverage E μ (f : Lp ℝ 2 μ), (g : Lp ℝ 2 μ)⟫_ℝ =
    ⟪(f : Lp ℝ 2 μ), coordinateAverage E μ (g : Lp ℝ 2 μ)⟫_ℝ
  exact average_inner_symm μ (outsideSigma E) (outsideSigma_le E) _ _

omit [DecidableEq ι] in
theorem centeredAverage_defect (f : Lp ℝ 2 μ) :
    ⟪center μ f, (1 - centeredAverage μ) (center μ f)⟫_ℝ =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i,
        ∫ x, ProbabilityTheory.condVar (outsideSigma E i) (f : (∀ k, E k) → ℝ) μ x ∂μ := by
  change ⟪(center μ f : Lp ℝ 2 μ),
    (center μ f : Lp ℝ 2 μ) - coordinateAverage E μ (center μ f : Lp ℝ 2 μ)⟫_ℝ = _
  rw [coe_center, mean_eq_integral]
  exact centered_coordinateAverage_defect_eq_average_condVar E μ f

theorem coeFn_sum {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    {J : Type*} (s : Finset J) (v : J → Lp ℝ 2 ν) :
    ((∑ i ∈ s, v i : Lp ℝ 2 ν) : Ω → ℝ) =ᵐ[ν] fun x ↦ ∑ i ∈ s, v i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Pi.zero_def] using Lp.coeFn_zero ℝ 2 ν
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (v j) (∑ i ∈ s, v i), ih] with x ha hs
    change (v j + ∑ i ∈ s, v i) x = v j x + ∑ i ∈ s, v i x
    simpa only [Pi.add_apply, hs] using ha

variable (κ : ∀ i, Kernel (∀ k, E k) (E i)) [∀ i, IsMarkovKernel (κ i)]

omit [Nonempty ι] in
theorem coordinateAverage_ae_eq_randomScan (hind : IndependentSite κ)
    (hstat : PreservesLaw κ μ) (f : Lp ℝ 2 μ) {g : (∀ k, E k) → ℝ} {B : ℝ}
    (hm : Measurable g) (hg : ∀ x, |g x| ≤ B) (hfg : (f : (∀ k, E k) → ℝ) =ᵐ[μ] g) :
    (coordinateAverage E μ f : (∀ k, E k) → ℝ) =ᵐ[μ] randomScan κ g := by
  have hp : ∀ᵐ x ∂μ, ∀ i, coordinateProjection E μ i f x = siteAverage κ g i x :=
    ae_all_iff.mpr fun i ↦ coordinateProjection_ae_eq_siteAverage κ μ hind hstat f hm hg hfg i
  rw [coordinateAverage, average_apply]
  change (((Fintype.card ι : ℝ)⁻¹ • ∑ i, coordinateProjection E μ i f : Lp ℝ 2 μ) :
    (∀ k, E k) → ℝ) =ᵐ[μ] randomScan κ g
  filter_upwards [Lp.coeFn_smul (Fintype.card ι : ℝ)⁻¹ (∑ i, coordinateProjection E μ i f),
    coeFn_sum μ Finset.univ (fun i ↦ coordinateProjection E μ i f), hp] with x hs hsum hx
  change ((Fintype.card ι : ℝ)⁻¹ • ∑ i, coordinateProjection E μ i f) x =
    (Fintype.card ι : ℝ)⁻¹ * ∑ i, siteAverage κ g i x
  change ((Fintype.card ι : ℝ)⁻¹ • ∑ i, coordinateProjection E μ i f) x =
    (Fintype.card ι : ℝ)⁻¹ * (∑ i, coordinateProjection E μ i f) x at hs
  rw [hs, hsum]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ hx i

theorem centeredAverage_pow_ae_eq_scanPower (hind : IndependentSite κ)
    (hstat : PreservesLaw κ μ) (f : Centered μ) {g : (∀ k, E k) → ℝ} {B : ℝ}
    (hm : Measurable g) (hg : ∀ x, |g x| ≤ B)
    (hfg : ((f : Lp ℝ 2 μ) : (∀ k, E k) → ℝ) =ᵐ[μ] g) (n : ℕ) :
    ((((centeredAverage μ ^ n) f : Centered μ) : Lp ℝ 2 μ) : (∀ k, E k) → ℝ)
      =ᵐ[μ] scanPower κ n g := by
  induction n with
  | zero => simpa only [pow_zero, one_apply_eq_self, scanPower] using hfg
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    change (coordinateAverage E μ ((centeredAverage μ ^ n) f : Lp ℝ 2 μ) :
      (∀ k, E k) → ℝ) =ᵐ[μ] randomScan κ (scanPower κ n g)
    exact coordinateAverage_ae_eq_randomScan μ κ hind hstat _
      (measurable_scanPower κ hm n) (scanPower_bound κ hg n) ih

theorem abs_le_of_zero_mean_pairwise {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {g : Ω → ℝ} (hi : Integrable g ν)
    (hz : (∫ x, g x ∂ν) = 0) {D : ℝ} (hD : ∀ x y, |g x - g y| ≤ D) (x : Ω) :
    |g x| ≤ D := by
  have h := norm_integral_le_of_norm_le_const (μ := ν)
    (Eventually.of_forall fun y ↦ show ‖g x - g y‖ ≤ D from by
      simpa only [Real.norm_eq_abs] using hD x y)
  rw [integral_sub (integrable_const _) hi, integral_const, probReal_univ, one_smul, hz,
    sub_zero, Real.norm_eq_abs, mul_one] at h
  exact h

theorem centered_exponential_bound (hind : IndependentSite κ) (hstat : PreservesLaw κ μ) :
    DobrushinSpectralGap.ExponentialBoundOn (centeredAverage μ) (boundedRepresentatives μ)
      (contractionRate (ι := ι) (maxColumnSum κ)) := by
  let := nonempty_of_isProbabilityMeasure μ
  intro f hf
  obtain ⟨g, B, hm, _, hb, hfg, _, _⟩ := exists_bounded_centered_representative μ hf
  have hg : ∀ x, |g x| ≤ B := by simpa only [Real.norm_eq_abs] using hb
  refine ⟨(Fintype.card ι : ℝ) * maxDelta g, ?_⟩
  intro n
  have hrep := centeredAverage_pow_ae_eq_scanPower μ κ hind hstat f hm hg hfg n
  have hzero : (∫ x, scanPower κ n g x ∂μ) = 0 :=
    (integral_congr_ae hrep).symm.trans (integral_coe_eq_zero μ ((centeredAverage μ ^ n) f))
  have hpair := abs_scanPower_sub_le κ hind hm hg n
  have hbound := abs_le_of_zero_mean_pairwise μ
    (integrable_bounded μ (measurable_scanPower κ hm n) (scanPower_bound κ hg n)) hzero hpair
  have hrate : 0 ≤ contractionRate (ι := ι) (maxColumnSum κ) :=
    contractionRate_nonneg (maxColumnSum_nonneg κ)
  have hD : 0 ≤ (Fintype.card ι : ℝ) *
      contractionRate (ι := ι) (maxColumnSum κ) ^ n * maxDelta g :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hrate _)) (maxDelta_nonneg hg)
  have haeb : ∀ᵐ x ∂μ, ‖((centeredAverage μ ^ n) f : Lp ℝ 2 μ) x‖ ≤
      (Fintype.card ι : ℝ) * contractionRate (ι := ι) (maxColumnSum κ) ^ n * maxDelta g := by
    filter_upwards [hrep] with x hx
    rw [hx, Real.norm_eq_abs]
    exact hbound x
  have hnorm := Lp.norm_le_of_ae_bound hD haeb
  change ‖((centeredAverage μ ^ n) f : Lp ℝ 2 μ)‖ ≤ _
  simpa only [measureUnivNNReal, measure_univ, ENNReal.toNNReal_one, NNReal.coe_one,
    Real.one_rpow, one_mul, mul_assoc, mul_comm, mul_left_comm] using hnorm

/-- Exact column-sum approximate tensorization for every actual L2 class.
All centered-space, bounded-density, conditional-operator and decay
properties used by the proof have been derived above. -/
theorem approximate_tensorization (hind : IndependentSite κ) (hstat : PreservesLaw κ μ)
    (hα : maxColumnSum κ < 1) (f : Lp ℝ 2 μ) :
    ProbabilityTheory.variance (f : (∀ k, E k) → ℝ) μ ≤
      (1 - maxColumnSum κ)⁻¹ * ∑ i,
        ∫ x, ProbabilityTheory.condVar (outsideSigma E i) (f : (∀ k, E k) → ℝ) μ x ∂μ := by
  let := nonempty_of_isProbabilityMeasure μ
  have hgap := DobrushinSpectralGap.quadratic_bound_of_dense_exponential
    (centeredAverage_isSelfAdjoint μ) (dense_boundedRepresentatives μ)
    (contractionRate_nonneg (maxColumnSum_nonneg κ))
    (centered_exponential_bound μ κ hind hstat) (center μ f)
  rw [centeredAverage_defect, ← variance_eq_norm_center_sq] at hgap
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h := mul_le_mul_of_nonneg_left hgap hn.le
  have hl : (Fintype.card ι : ℝ) * (1 - contractionRate (ι := ι) (maxColumnSum κ)) =
      1 - maxColumnSum κ := by
    unfold contractionRate
    field_simp [hn.ne']
    ring
  rw [← mul_assoc, hl, ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul] at h
  calc
    _ ≤ (∑ i, ∫ x, ProbabilityTheory.condVar (outsideSigma E i)
          (f : (∀ k, E k) → ℝ) μ x ∂μ) / (1 - maxColumnSum κ) :=
      (le_div_iff₀ (sub_pos.mpr hα)).mpr (by nlinarith [h])
    _ = _ := div_eq_inv_mul _ _

/-- The same inequality for every square-integrable representative,
including unbounded functions; no pointwise choice of an L2 class is imposed. -/
theorem approximate_tensorization_memLp (hind : IndependentSite κ)
    (hstat : PreservesLaw κ μ) (hα : maxColumnSum κ < 1)
    {f : (∀ k, E k) → ℝ} (hf : MemLp f 2 μ) :
    ProbabilityTheory.variance f μ ≤
      (1 - maxColumnSum κ)⁻¹ * ∑ i,
        ∫ x, ProbabilityTheory.condVar (outsideSigma E i) f μ x ∂μ := by
  have h := approximate_tensorization μ κ hind hstat hα (hf.toLp f)
  rw [ProbabilityTheory.variance_congr hf.coeFn_toLp] at h
  have he (i : ι) :
      (∫ x, ProbabilityTheory.condVar (outsideSigma E i) (hf.toLp f : (∀ k, E k) → ℝ) μ x ∂μ) =
        ∫ x, ProbabilityTheory.condVar (outsideSigma E i) f μ x ∂μ :=
    integral_congr_ae (ProbabilityTheory.condVar_congr_ae hf.coeFn_toLp)
  simp_rw [he] at h
  exact h

end PeriodicAttractiveLogGas.DobrushinVariance
