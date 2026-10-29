import DGRHS.Gaussian.PeriodicLogTruncationRemainder
import DGRHS.Gaussian.FeatureKernel
import DGRHS.Kernel.PositiveLimit

/-!
Packet P9g, unit 2 (part 4): canonical data and positivity of the truncated torus operators, and
positivity of the full centered periodic LOG operator `T_μ` as the `L²`-limit of the truncated
ones (TeX 487-489; the torus form of the LOG case of `gaussianRieszPhysicalOperator_positive`).
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology InnerProductSpace
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- The centered Fourier feature of the heat-shift truncation. -/
def periodicLogTruncFeature (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] (τ : ℝ)
    (hτ : 0 < τ) :
    PeriodicTorus ι → PeriodicHeatFeatureSpace ι :=
  periodicCenteredPositiveFourierFeature (periodicLogTruncCoeff (ι := ι) τ)
    (periodicLogTruncCoeff_nonneg (ι := ι) τ)
    (periodicLogTruncCoeff_summable (ι := ι) τ hτ) μ

lemma periodicLogTruncCentered_eq_featureKernel (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (τ : ℝ) (hτ : 0 < τ) :
    periodicLogTruncCentered μ τ = featureKernel (periodicLogTruncFeature μ τ hτ) := by
  funext p
  exact (periodicCenteredPositiveFourierFeature_gram _ _ _
    (periodicLogTruncCoeff_sqrt_summable (ι := ι) τ hτ) μ p.1 p.2).symm

lemma periodicLogTruncFeature_stronglyMeasurable (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (τ : ℝ) (hτ : 0 < τ) :
    StronglyMeasurable (periodicLogTruncFeature μ τ hτ) :=
  ((periodicPositiveFourierFeature_continuous _
    (periodicLogTruncCoeff_nonneg (ι := ι) τ)
    (periodicLogTruncCoeff_summable (ι := ι) τ hτ)
    (periodicLogTruncCoeff_sqrt_summable (ι := ι) τ hτ)).stronglyMeasurable).sub
      stronglyMeasurable_const

lemma periodicLogTruncFeature_memLp (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (τ : ℝ) (hτ : 0 < τ) (p : ℝ≥0∞) :
    MemLp (periodicLogTruncFeature μ τ hτ) p μ := by
  apply (memLp_const (2 * Real.sqrt (∑' j, periodicLogTruncCoeff (ι := ι) τ j))).of_le
    (periodicLogTruncFeature_stronglyMeasurable μ τ hτ).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_of_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))]
  exact periodicCenteredPositiveFourierFeature_norm_le _ _ _
    (periodicLogTruncCoeff_sqrt_summable (ι := ι) τ hτ) μ x

lemma periodicLogTruncFeature_integral (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (τ : ℝ) (hτ : 0 < τ) :
    (∫ x, periodicLogTruncFeature μ τ hτ x ∂μ) = 0 := by
  have hi := periodicPositiveFourierFeature_integrable _
    (periodicLogTruncCoeff_nonneg (ι := ι) τ)
    (periodicLogTruncCoeff_summable (ι := ι) τ hτ)
    (periodicLogTruncCoeff_sqrt_summable (ι := ι) τ hτ) μ
  show (∫ x, (periodicPositiveFourierFeature _
    (periodicLogTruncCoeff_nonneg (ι := ι) τ)
    (periodicLogTruncCoeff_summable (ι := ι) τ hτ) x -
      ∫ y, periodicPositiveFourierFeature _
    (periodicLogTruncCoeff_nonneg (ι := ι) τ)
    (periodicLogTruncCoeff_summable (ι := ι) τ hτ) y ∂μ) ∂μ) = 0
  rw [integral_sub hi (integrable_const _)]
  simp

lemma periodicLogTruncCentered_memLp (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (τ : ℝ) (hτ : 0 < τ) :
    MemLp (periodicLogTruncCentered μ τ) 2 (μ.prod μ) := by
  rw [periodicLogTruncCentered_eq_featureKernel μ τ hτ]
  exact memLp_featureKernel _ (periodicLogTruncFeature_stronglyMeasurable μ τ hτ)
    (periodicLogTruncFeature_memLp μ τ hτ 2)

/-- Torus form of `riesz_cutoff_canonical_data`. -/
lemma periodicLogTruncCentered_data (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (τ : ℝ) (hτ : 0 < τ) :
    Measurable (periodicLogTruncCentered μ τ) ∧
      (∀ᵐ p ∂μ.prod μ, periodicLogTruncCentered μ τ p.swap = periodicLogTruncCentered μ τ p) ∧
      (∀ᵐ x ∂μ, (∫ y, periodicLogTruncCentered μ τ (x, y) ∂μ) = 0) := by
  have hk := periodicLogTruncFeature_stronglyMeasurable μ τ hτ
  rw [periodicLogTruncCentered_eq_featureKernel μ τ hτ]
  refine ⟨((hk.comp_measurable measurable_fst).inner
    (hk.comp_measurable measurable_snd)).measurable,
    Filter.Eventually.of_forall (featureKernel_symmetric _), ?_⟩
  exact Filter.Eventually.of_forall (integral_featureKernel_right _
    (periodicLogTruncFeature_memLp μ τ hτ 2) (periodicLogTruncFeature_integral μ τ hτ))

lemma periodicLogTruncCentered_positive (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (τ : ℝ) (hτ : 0 < τ)
    (hq : MemLp (periodicLogTruncCentered μ τ) 2 (μ.prod μ)) :
    ∀ v : Lp ℝ 2 μ, 0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator (periodicLogTruncCentered μ τ) hq v) := by
  intro v
  have he := periodicLogTruncCentered_eq_featureKernel μ τ hτ
  have hp := integralOperator_featureKernel_nonneg _
    (periodicLogTruncFeature_stronglyMeasurable μ τ hτ)
    (periodicLogTruncFeature_memLp μ τ hτ 2) v
  have hc : DGRHS.Kernel.integralOperator (periodicLogTruncCentered μ τ) hq =
      DGRHS.Kernel.integralOperator (featureKernel (periodicLogTruncFeature μ τ hτ))
        (memLp_featureKernel _ (periodicLogTruncFeature_stronglyMeasurable μ τ hτ)
          (periodicLogTruncFeature_memLp μ τ hτ 2)) :=
    gaussian_integralOperator_congr μ _ _ _ _ (Filter.Eventually.of_forall (fun p => by rw [he]))
  rw [hc, real_inner_comm]
  exact hp

/-- Positivity of the full centered periodic LOG operator as the limit of the truncated ones. -/
theorem periodicLogOperator_positive (θ : ℝ) (hθ : 0 < θ)
    (hrem : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∫ x, periodicLogRemainder (ι := ι) τ x ^ 2 ∂periodicHaar ι ≤ C * τ ^ θ)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (hh : MemLp (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))) 2
          ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ))) :
    ∀ v : Lp ℝ 2 (periodicCappedDensityMeasure ρ), 0 ≤ inner ℝ v
      (DGRHS.Kernel.integralOperator (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))) hh v) := by
  set μ := periodicCappedDensityMeasure ρ with hμ
  obtain ⟨A, hA0, hA⟩ := periodicLogResidual_of_remainder θ hrem ρ M hM hρ
  let τ : ℕ → ℝ := fun N => 1 / ((N : ℝ) + 1)
  have hτ : ∀ N, 0 < τ N := fun N => by dsimp [τ]; positivity
  have hτ1 : ∀ N, τ N ≤ 1 := fun N => by
    dsimp [τ]
    rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hq : ∀ N, MemLp (periodicLogTruncCentered μ (τ N)) 2 (μ.prod μ) := fun N =>
    periodicLogTruncCentered_memLp μ (τ N) (hτ N)
  apply DGRHS.Kernel.integralOperator_nonnegative_of_toLp_limit _ hh
    (fun N => periodicLogTruncCentered μ (τ N)) hq
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hne : θ / 2 ≠ 0 := by positivity
    have hle : 0 ≤ θ / 2 := by positivity
    have hpow : Tendsto (fun N => (τ N) ^ (θ / 2)) atTop (𝓝 0) := by
      simpa only [τ, Function.comp_def, Real.zero_rpow hne] using
        ((Real.continuousAt_rpow_const 0 (θ / 2) (Or.inr hle)).tendsto.comp
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    apply squeeze_zero (fun N => norm_nonneg _) _ (by simpa using hpow.const_mul A)
    intro N
    have hb := hA (τ N) (hτ N) (hτ1 N) hh (hq N)
    calc _ = ‖hh.toLp _ - (hq N).toLp (periodicLogTruncCentered μ (τ N))‖ := norm_sub_rev _ _
      _ = ‖(hh.sub (hq N)).toLp (fun p => hoeffdingCentered μ
        (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2)) p -
        periodicLogTruncCentered μ (τ N) p)‖ := by
          exact congrArg norm (MemLp.toLp_sub hh (hq N)).symm
      _ ≤ _ := hb
  · intro N v
    exact periodicLogTruncCentered_positive μ (τ N) (hτ N) (hq N) v

/-- Unconditional positivity of the centered periodic LOG operator `T_μ` (any density `ρ ≤ M`). -/
theorem periodicLogOperator_positive_all (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (hh : MemLp (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))) 2
          ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ))) :
    ∀ v : Lp ℝ 2 (periodicCappedDensityMeasure ρ), 0 ≤ inner ℝ v
      (DGRHS.Kernel.integralOperator (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))) hh v) := by
  obtain ⟨θ, hθ, hrem⟩ := periodicLogRemainder_integral_sq_le_weak (ι := ι)
  exact periodicLogOperator_positive θ hθ hrem ρ M hM hρ hh

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicLogTruncFeature
#print axioms DGRHS.Periodic.periodicLogTruncCentered_eq_featureKernel
#print axioms DGRHS.Periodic.periodicLogTruncFeature_stronglyMeasurable
#print axioms DGRHS.Periodic.periodicLogTruncFeature_memLp
#print axioms DGRHS.Periodic.periodicLogTruncFeature_integral
#print axioms DGRHS.Periodic.periodicLogTruncCentered_memLp
#print axioms DGRHS.Periodic.periodicLogTruncCentered_data
#print axioms DGRHS.Periodic.periodicLogTruncCentered_positive
#print axioms DGRHS.Periodic.periodicLogOperator_positive
#print axioms DGRHS.Periodic.periodicLogOperator_positive_all
