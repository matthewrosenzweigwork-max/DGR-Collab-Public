import DGRHS.Gaussian.PeriodicRieszCanonicalRate
import DGRHS.Gaussian.PeriodicRieszTruncationFamilyRate
import DGRHS.Concentration.SourceAffineLog
import DGRHS.Concentration.SourceCutoffRate
import DGRHS.CLT.SourceWeightCorrection
import DGRHS.Gaussian.SourceRepulsiveRieszRateSpectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Packet P9d, unit 1 (part 6): one-body reduction and the torus Riesz rate for the partition function
(TeX Lemma 5.6 and the assembly 2093-2159, `thm:partitionFunctionBound`(ii), 0 < s < d/2,
on the torus by Remark 2.1), mirroring `DGRHS.Concentration.gaussianRieszPhysical_affine_partition_rate`
and `DGRHS.CLT.sourceRieszSingularPartition_original_rate`.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology InnerProductSpace
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Torus affine (one-body) partition rate: the canonical rate transfers to the partition with the
affine one-body correction, with the extra `N^{-1/2}` error absorbed by `half_power_le_log_rate`. -/
theorem periodicRieszPhysical_affine_partition_rate (s β : ℝ) (hs0 : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (θ : ℝ) (hθ : 0 < θ)
    (hrem : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∫ x, periodicRieszRemainder s τ hs2 x ^ 2 ∂periodicHaar ι ≤ C * τ ^ θ)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (F : PeriodicTorus ι → ℝ) (hF : MemLp F 2 (periodicCappedDensityMeasure ρ))
    (K I : ℝ) (hK : ∀ᵐ x ∂periodicCappedDensityMeasure ρ, F x ≤ K) :
    let μ := periodicCappedDensityMeasure ρ
    let h := periodicRieszCentered s hs2 μ
    let c := β * (∫ y, F y ∂μ) - β * I
    ∃ (hh : MemLp h 2 (μ.prod μ))
      (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i, DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e i) = eig i • e i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      Tendsto (sourceAffinePartition μ β I h F) atTop
        (𝓝 (Real.exp c * (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹)) ∧
      Tendsto (fun N => Real.log (sourceAffinePartition μ β I h F N)) atTop
        (𝓝 (c + Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ N, 1 ≤ N →
        Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp
          (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        Real.exp c ≤ sourceAffinePartition μ β I h F N ∧
        |sourceAffinePartition μ β I h F N -
          Real.exp c * (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          C * (Real.log (Real.exp 1 + (N : ℝ))) ^ (-(θ / s)) ∧
        |Real.log (sourceAffinePartition μ β I h F N) -
          (c + Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹))| ≤
          C * (Real.log (Real.exp 1 + (N : ℝ))) ^ (-(θ / s)) := by
  have hres := periodicRieszResidual_of_remainder s hs0 hs2 θ hrem ρ M hM hρ
  have hunif := periodicTruncFamily_uniformExponential s (2 * β) hs0 (by positivity) hs2 ρ M hM hρ
  exact (periodicTruncFamily s hs0 hs2).affine_partition_rate β hs0 hβ hs2 θ hθ ρ M hM hρ hres hunif
    F hF K I hK

/-- Torus Theorem 2.2(ii) (Riesz branch) for the literal singular partition, with exponent
`θ/s` where `θ` is the exponent of the heat-shift remainder `‖g - g_τ‖_{L²}² ≲ τ^θ` (so that the
centered residual is `≲ η^θ` at scale `η = √τ`).  For `θ = (d - 2s)/2` this is the printed exponent
`(d-2s)/(2s)`. -/
theorem periodicRieszSingularPartition_rate_of_remainder (s β : ℝ) (hs0 : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (θ : ℝ) (hθ : 0 < θ)
    (hrem : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∫ x, periodicRieszRemainder s τ hs2 x ^ 2 ∂periodicHaar ι ≤ C * τ ^ θ)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)
    let h := hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))
    let I := DGRHS.interactionEnergy μ W
    ∃ (hh : MemLp h 2 (μ.prod μ))
      (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i, DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e i) = eig i • e i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      HasProd (fun i => (1 + β * eig i) * Real.exp (-(β * eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => β * eig i)) ∧
      Tendsto (fun N => (periodicRieszSingularPartition s β hs2 ρ N).toReal) atTop
        (𝓝 (Real.exp (β * I) * (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹)) ∧
      Tendsto (fun N => Real.log (periodicRieszSingularPartition s β hs2 ρ N).toReal) atTop
        (𝓝 (β * I + Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
        (0 < periodicRieszSingularPartition s β hs2 ρ N ∧
          periodicRieszSingularPartition s β hs2 ρ N < ⊤) ∧
        Real.exp (β * I) ≤ (periodicRieszSingularPartition s β hs2 ρ N).toReal ∧
        |(periodicRieszSingularPartition s β hs2 ρ N).toReal -
          Real.exp (β * I) * (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          C * (Real.log (Real.exp 1 + (N : ℝ))) ^ (-(θ / s)) ∧
        |Real.log (periodicRieszSingularPartition s β hs2 ρ N).toReal -
          (β * I + Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹))| ≤
          C * (Real.log (Real.exp 1 + (N : ℝ))) ^ (-(θ / s)) := by
  have hres := periodicRieszResidual_of_remainder s hs0 hs2 θ hrem ρ M hM hρ
  have hunif := periodicTruncFamily_uniformExponential s (2 * β) hs0 (by positivity) hs2 ρ M hM hρ
  exact (periodicTruncFamily s hs0 hs2).singular_rate β hs0 hβ hs2 θ hθ ρ M hM hρ hres hunif

end DGRHS.Periodic
