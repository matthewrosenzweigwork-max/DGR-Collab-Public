import DGRHS.Gaussian.PeriodicRieszLowerCutRemainder
import DGRHS.Gaussian.PeriodicRieszTruncationFamily
import DGRHS.Gaussian.PeriodicHeatGaussianField
import DGRHS.Gaussian.OriginalFeatureProposition
import DGRHS.Concentration.SourcePartitionRate

/-!
Packet P9f, unit 3 (part 1): truncated feature-space Laplace estimate for the lower-cut family on the
torus (TeX Step 1 of Proposition 5.5, `eq:truncatedLaplaceRateEta` for `0 < s < d/2`), a direct
instance of the generic Proposition 5.4 `original_boundedFeatureQuadLaplace_of_memLp_top`.
Verbatim analogue of `PeriodicRieszTruncatedLaplace` with the coefficient family
`periodicRieszLCCoeff s τ` (lower cut at heat time `τ = η²`).
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- The lower-cut truncation family `τ ↦ periodicRieszLCCoeff s τ` as a generic
`PeriodicRieszTruncationFamily` (Packet P12c). -/
abbrev periodicLCFamily (s : ℝ) (hs0 : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    PeriodicRieszTruncationFamily ι s where
  coeff := periodicRieszLCCoeff (ι := ι) s
  coeff_nonneg τ hτ := periodicRieszLCCoeff_nonneg (ι := ι) s τ hs0 hτ.le
  coeff_summable τ hτ := periodicRieszLCCoeff_summable (ι := ι) s τ hs0 hs2 hτ
  coeff_sqrt_summable τ hτ := periodicRieszLCCoeff_sqrt_summable (ι := ι) s τ hs0 hs2 hτ
  coeff_tsum_le := periodicRieszLCCoeff_tsum_le (ι := ι) s hs0 hs2

theorem periodicRieszLCLaplace_diag (β s τ : ℝ) (hβ : 0 ≤ β) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 < τ)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] :
    ∃ (hh : MemLp (periodicLCCentered μ s τ) 2 (μ.prod μ))
      (σ : Type u) (eig : σ → ℝ) (e : HilbertBasis σ ℝ (Lp ℝ 2 μ)),
      Countable σ ∧
      (∀ i, DGRHS.Kernel.integralOperator (periodicLCCentered μ s τ) hh (e i) = eig i • e i) ∧
      (∀ i, 0 ≤ eig i) ∧ Summable eig ∧
      HasProd (fun i => (1 + β * eig i) * Real.exp (-(β * eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => β * eig i)) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (-β / 2 *
          DGRHS.CanonicalVariance.normalizedOffDiagonalSum (periodicLCCentered μ s τ) x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        |canonicalPartition μ β (periodicLCCentered μ s τ) N -
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          featureBoundedRateConstant β * Real.exp (featureBoundedRateConstant β * β *
            (4 * ∑' k, periodicRieszLCCoeff (ι := ι) s τ k)) / (N : ℝ) := by
  exact (periodicLCFamily s hs0 hs2).laplace_diag β τ hβ hτ μ

/-- Laplace constant of the periodic truncation: `L exp(L τ^{-s/2}) / N`. -/
theorem periodicRieszLCLaplace (β s : ℝ) (hβ : 0 ≤ β) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    ∃ L : ℝ, 0 < L ∧ ∀ (τ : ℝ), 0 < τ → τ ≤ 1 →
      ∀ (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ],
      ∃ (hh : MemLp (periodicLCCentered μ s τ) 2 (μ.prod μ))
        (σ : Type u) (eig : σ → ℝ) (e : HilbertBasis σ ℝ (Lp ℝ 2 μ)),
        Countable σ ∧
        (∀ i, DGRHS.Kernel.integralOperator (periodicLCCentered μ s τ) hh (e i) = eig i • e i) ∧
        0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
        Tendsto (canonicalPartition μ β (periodicLCCentered μ s τ)) atTop
          (𝓝 ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹)) ∧
        ∀ N : ℕ, 1 ≤ N →
          Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (-β / 2 *
            DGRHS.CanonicalVariance.normalizedOffDiagonalSum (periodicLCCentered μ s τ) x))
            (Measure.pi (fun _ : Fin N => μ)) ∧
          |canonicalPartition μ β (periodicLCCentered μ s τ) N -
            (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
            L * Real.exp (L * τ ^ (-s / 2)) / (N : ℝ) := by
  exact (periodicLCFamily s hs0 hs2).laplace β hβ

end DGRHS.Periodic
