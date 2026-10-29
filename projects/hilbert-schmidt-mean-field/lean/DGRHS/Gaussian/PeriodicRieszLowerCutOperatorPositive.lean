import DGRHS.Gaussian.PeriodicRieszLowerCutLaplace
import DGRHS.Gaussian.FeatureKernel
import DGRHS.Kernel.PositiveLimit

/-!
Packet P9f, unit 3 (part 2): canonical data and positivity of the truncated torus operators of the
lower-cut family, and positivity of the full centered periodic Riesz operator `T_μ` as the
`L²`-limit of the truncated ones (TeX 487-489).  Verbatim analogue of `PeriodicRieszOperatorPositive`.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology InnerProductSpace
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- The centered Fourier feature of the lower-cut truncation. -/
def periodicLCFeature (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] (s τ : ℝ)
    (hs0 : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 < τ) :
    PeriodicTorus ι → PeriodicHeatFeatureSpace ι :=
  periodicCenteredPositiveFourierFeature (periodicRieszLCCoeff (ι := ι) s τ)
    (periodicRieszLCCoeff_nonneg (ι := ι) s τ hs0 hτ.le)
    (periodicRieszLCCoeff_summable (ι := ι) s τ hs0 hs2 hτ) μ

lemma periodicLCCentered_eq_featureKernel (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (s τ : ℝ) (hs0 : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 < τ) :
    periodicLCCentered μ s τ = featureKernel (periodicLCFeature μ s τ hs0 hs2 hτ) := by
  exact (periodicLCFamily s hs0 hs2).centered_eq_featureKernel μ τ hτ

lemma periodicLCFeature_stronglyMeasurable (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (s τ : ℝ) (hs0 : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 < τ) :
    StronglyMeasurable (periodicLCFeature μ s τ hs0 hs2 hτ) :=
  (periodicLCFamily s hs0 hs2).feature_stronglyMeasurable μ τ hτ

lemma periodicLCFeature_memLp (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (s τ : ℝ) (hs0 : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 < τ) (p : ℝ≥0∞) :
    MemLp (periodicLCFeature μ s τ hs0 hs2 hτ) p μ := by
  exact (periodicLCFamily s hs0 hs2).feature_memLp μ τ hτ p

lemma periodicLCFeature_integral (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (s τ : ℝ) (hs0 : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 < τ) :
    (∫ x, periodicLCFeature μ s τ hs0 hs2 hτ x ∂μ) = 0 := by
  exact (periodicLCFamily s hs0 hs2).feature_integral μ τ hτ

lemma periodicLCCentered_memLp (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (s τ : ℝ) (hs0 : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 < τ) :
    MemLp (periodicLCCentered μ s τ) 2 (μ.prod μ) := by
  exact (periodicLCFamily s hs0 hs2).centered_memLp μ τ hτ

/-- Torus form of `riesz_cutoff_canonical_data`. -/
lemma periodicLCCentered_data (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (s τ : ℝ) (hs0 : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 < τ) :
    Measurable (periodicLCCentered μ s τ) ∧
      (∀ᵐ p ∂μ.prod μ, periodicLCCentered μ s τ p.swap = periodicLCCentered μ s τ p) ∧
      (∀ᵐ x ∂μ, (∫ y, periodicLCCentered μ s τ (x, y) ∂μ) = 0) := by
  exact (periodicLCFamily s hs0 hs2).centered_data μ τ hτ

lemma periodicLCCentered_positive (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (s τ : ℝ) (hs0 : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 < τ)
    (hq : MemLp (periodicLCCentered μ s τ) 2 (μ.prod μ)) :
    ∀ v : Lp ℝ 2 μ, 0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator (periodicLCCentered μ s τ) hq v) := by
  exact (periodicLCFamily s hs0 hs2).centered_positive μ τ hτ hq

/-- Positivity of the full centered periodic Riesz operator as the limit of the truncated ones. -/
theorem periodicRieszOperator_positive_LC (s : ℝ) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (θ : ℝ) (hθ : 0 < θ)
    (hrem : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∫ x, periodicRieszLCRemainder s τ hs2 x ^ 2 ∂periodicHaar ι ≤ C * τ ^ θ)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (hh : MemLp (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))) 2
          ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ))) :
    ∀ v : Lp ℝ 2 (periodicCappedDensityMeasure ρ), 0 ≤ inner ℝ v
      (DGRHS.Kernel.integralOperator (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))) hh v) := by
  exact (periodicLCFamily s hs0 hs2).operator_positive hs2 θ hθ ρ
    (periodicRieszLCResidual_of_remainder s hs0 hs2 θ hrem ρ M hM hρ) hh

end DGRHS.Periodic
