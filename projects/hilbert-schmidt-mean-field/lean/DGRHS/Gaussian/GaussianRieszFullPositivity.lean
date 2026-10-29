/- The full physical Riesz operator is positive by the derived SAME cutoff
operator estimate and actual positive Gram cutoff. No spectral sign premise. -/
import DGRHS.Gaussian.GaussianRieszOperatorDifference
import DGRHS.Gaussian.RieszGaussianCutoffPositivity
import DGRHS.Kernel.PositiveLimit
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

theorem gaussianRieszTruncatedOperator_positive (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (ρ : EuclideanSpace ℝ ι → ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    ∀ v, 0 ≤ inner ℝ v (gaussianRieszTruncatedOperator s η hs hη ρ v) := by
  let μ := gaussianRieszDensityMeasure ρ
  have he := gaussianRieszCenteredTruncatedPair_eq_source s η hs hη μ
  have hsrc : MemLp (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2) 2 (μ.prod μ) :=
    (memLp_congr_ae (Eventually.of_forall he)).1
      (memLp_gaussianRieszCenteredTruncatedPair s η hs hη μ)
  rw [gaussianRieszTruncatedOperator_eq_source s η hs hη ρ hsrc]
  exact sourceGaussianRieszCutoff_positive s η hs hη μ hsrc

theorem gaussianRieszPhysicalOperator_positive (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ∀ v, 0 ≤ inner ℝ v (gaussianRieszPhysicalOperator s hs ha ρ M hM hρ v) := by
  let η : ℕ → ℝ := fun N => 1 / ((N : ℝ) + 1)
  have hη (N : ℕ) : 0 < η N := by dsimp [η]; positivity
  let A := fun N => gaussianRieszTruncatedOperator s (η N) hs (hη N) ρ
  let T := gaussianRieszPhysicalOperator s hs ha ρ M hM hρ
  have hpow : Tendsto (fun N => (η N) ^ ((Fintype.card ι : ℝ) / 2 - s)) atTop (𝓝 0) := by
    simpa only [η, Function.comp_def, Real.zero_rpow ha.ne'] using
      ((Real.continuousAt_rpow_const 0 _ (Or.inr ha.le)).tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hc : Tendsto (fun N => ‖A N - T‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun N => norm_nonneg _) _
      (by simpa using hpow.const_mul (4 * gaussianRieszShortRangeRateConstant s M ι))
    intro N
    rw [norm_sub_rev]
    exact norm_gaussianRieszPhysicalOperator_sub_cutoff_le s (η N) hs (hη N) ha ρ M hM hρ
  exact DGRHS.Kernel.nonnegative_operator_of_tendsto T A
    (tendsto_iff_norm_sub_tendsto_zero.mpr hc)
    (fun N => gaussianRieszTruncatedOperator_positive s (η N) hs (hη N) ρ)
end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.gaussianRieszTruncatedOperator_positive
#print axioms DGRHS.Gaussian.gaussianRieszPhysicalOperator_positive
#check @DGRHS.Gaussian.gaussianRieszPhysicalOperator_positive
