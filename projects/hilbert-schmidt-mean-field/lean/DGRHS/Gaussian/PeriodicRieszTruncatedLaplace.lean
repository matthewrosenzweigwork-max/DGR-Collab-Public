import DGRHS.Gaussian.PeriodicRieszTruncatedFeature
import DGRHS.Gaussian.PeriodicRieszTruncationFamily
import DGRHS.Gaussian.PeriodicHeatGaussianField
import DGRHS.Gaussian.OriginalFeatureProposition
import DGRHS.Concentration.SourcePartitionRate

/-!
Packet P9d, unit 1 (part 2): truncated feature-space Laplace estimate on the torus
(TeX Step 1 of Proposition 5.5, `eq:truncatedLaplaceRateEta` for `0 < s < d/2`, with the heat-shifted
Fourier feature of the truncation `g_τ`), a direct instance of the generic Proposition 5.4
`original_boundedFeatureQuadLaplace_of_memLp_top`.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Hoeffding-centered truncated periodic kernel (continuous Fourier representative). -/
abbrev periodicTruncCentered (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] (s τ : ℝ) :
    PeriodicTorus ι × PeriodicTorus ι → ℝ :=
  hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszTruncKernel s τ (q.1 - q.2))

/-- The heat-shift truncation family `τ ↦ periodicRieszTruncCoeff s τ` as a generic
`PeriodicRieszTruncationFamily` (Packet P12c). -/
abbrev periodicTruncFamily (s : ℝ) (hs0 : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    PeriodicRieszTruncationFamily ι s where
  coeff := periodicRieszTruncCoeff (ι := ι) s
  coeff_nonneg τ _ := periodicRieszTruncCoeff_nonneg (ι := ι) s τ hs0 hs2
  coeff_summable τ hτ := periodicRieszTruncCoeff_summable (ι := ι) s τ hs0 hs2 hτ
  coeff_sqrt_summable τ hτ := periodicRieszTruncCoeff_sqrt_summable (ι := ι) s τ hs0 hs2 hτ
  coeff_tsum_le := periodicRieszTruncCoeff_tsum_le (ι := ι) s hs0 hs2

theorem periodicRieszTruncatedLaplace_diag (β s τ : ℝ) (hβ : 0 ≤ β) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 < τ)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] :
    ∃ (hh : MemLp (periodicTruncCentered μ s τ) 2 (μ.prod μ))
      (σ : Type u) (eig : σ → ℝ) (e : HilbertBasis σ ℝ (Lp ℝ 2 μ)),
      Countable σ ∧
      (∀ i, DGRHS.Kernel.integralOperator (periodicTruncCentered μ s τ) hh (e i) = eig i • e i) ∧
      (∀ i, 0 ≤ eig i) ∧ Summable eig ∧
      HasProd (fun i => (1 + β * eig i) * Real.exp (-(β * eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => β * eig i)) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (-β / 2 *
          DGRHS.CanonicalVariance.normalizedOffDiagonalSum (periodicTruncCentered μ s τ) x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        |canonicalPartition μ β (periodicTruncCentered μ s τ) N -
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          featureBoundedRateConstant β * Real.exp (featureBoundedRateConstant β * β *
            (4 * ∑' k, periodicRieszTruncCoeff (ι := ι) s τ k)) / (N : ℝ) := by
  exact (periodicTruncFamily s hs0 hs2).laplace_diag β τ hβ hτ μ

/-- Laplace constant of the periodic truncation: `L exp(L τ^{-s/2}) / N`. -/
theorem periodicRieszTruncatedLaplace (β s : ℝ) (hβ : 0 ≤ β) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    ∃ L : ℝ, 0 < L ∧ ∀ (τ : ℝ), 0 < τ → τ ≤ 1 →
      ∀ (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ],
      ∃ (hh : MemLp (periodicTruncCentered μ s τ) 2 (μ.prod μ))
        (σ : Type u) (eig : σ → ℝ) (e : HilbertBasis σ ℝ (Lp ℝ 2 μ)),
        Countable σ ∧
        (∀ i, DGRHS.Kernel.integralOperator (periodicTruncCentered μ s τ) hh (e i) = eig i • e i) ∧
        0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
        Tendsto (canonicalPartition μ β (periodicTruncCentered μ s τ)) atTop
          (𝓝 ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹)) ∧
        ∀ N : ℕ, 1 ≤ N →
          Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (-β / 2 *
            DGRHS.CanonicalVariance.normalizedOffDiagonalSum (periodicTruncCentered μ s τ) x))
            (Measure.pi (fun _ : Fin N => μ)) ∧
          |canonicalPartition μ β (periodicTruncCentered μ s τ) N -
            (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
            L * Real.exp (L * τ ^ (-s / 2)) / (N : ℝ) := by
  exact (periodicTruncFamily s hs0 hs2).laplace β hβ

end DGRHS.Periodic
