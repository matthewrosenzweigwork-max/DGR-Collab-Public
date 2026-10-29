/- Original positive-Riesz quantitative theorem for the literal collision-zero
ENNReal normalizer. Genuine proper/positive/finite identification precedes all
real-value rewrites. Same physical centered operator, returned eigenbasis,
regularized product, exact logarithmic exponent and source prefactor. -/
import DGRHS.CLT.SourceRieszSingularIdentification
import DGRHS.Gaussian.SourceRepulsiveRieszRate
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace DGRHS.CLT
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι]

theorem sourceRieszSingularPartition_original_rate (s β : ℝ)
    (hs : 0 < s) (hβ : 0 ≤ β) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (a,b)
    let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    let I := DGRHS.interactionEnergy μ W
    ∃ (hh : MemLp h 2 (μ.prod μ))
      (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap=h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y,h (x,y) ∂μ)=0)
      (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i, DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e i)=eig i • e i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β*eig i) ∧
      HasProd (fun i => (1+β*eig i)*Real.exp (-(β*eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => β*eig i)) ∧
      Tendsto (fun N => (sourceRieszSingularPartition s β ρ N).toReal) atTop
        (𝓝 (Real.exp (β*I)*(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β*eig i)))⁻¹)) ∧
      Tendsto (fun N => Real.log (sourceRieszSingularPartition s β ρ N).toReal) atTop
        (𝓝 (β*I+Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β*eig i)))⁻¹))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
        (0 < sourceRieszSingularPartition s β ρ N ∧ sourceRieszSingularPartition s β ρ N < ⊤) ∧
        Real.exp (β*I) ≤ (sourceRieszSingularPartition s β ρ N).toReal ∧
        |(sourceRieszSingularPartition s β ρ N).toReal-
          Real.exp (β*I)*(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β*eig i)))⁻¹| ≤
          C*(Real.log (Real.exp 1+(N:ℝ)))^(-(((Fintype.card ι:ℝ)-2*s)/(2*s))) ∧
        |Real.log (sourceRieszSingularPartition s β ρ N).toReal-
          (β*I+Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β*eig i)))⁻¹))| ≤
          C*(Real.log (Real.exp 1+(N:ℝ)))^(-(((Fintype.card ι:ℝ)-2*s)/(2*s))) := by
  dsimp only
  obtain ⟨hh,hSym,hCan,κ,eig,e,hκ,he,hD,hProd,hT,hLog,C,hC,hRate⟩ :=
    DGRHS.SourceRepulsiveRieszRate.exists_source_partition_rate s β hs hβ ha ρ M hM hρ
  have hEq (N : ℕ) : (sourceRieszSingularPartition s β ρ N).toReal =
      physicalRieszSourcePartition s β ρ N := by
    rw [sourceRieszSingularPartition_eq_integral s β hs hβ ha ρ M hM hρ N]
    exact ENNReal.toReal_ofReal (by
      unfold physicalRieszSourcePartition
      exact integral_nonneg fun x => (Real.exp_pos _).le)
  refine ⟨hh,hSym,hCan,κ,eig,e,hκ,he,hD,hProd,
    hT.congr' (Filter.Eventually.of_forall fun N => (hEq N).symm),
    hLog.congr' (Filter.Eventually.of_forall fun N => congrArg Real.log (hEq N).symm),
    C,hC,?_⟩
  intro N hN
  refine ⟨sourceRieszSingularPartition_pos_finite s β hs hβ ha ρ M hM hρ N, ?_⟩
  rw [hEq N]
  exact (hRate N hN).2

end DGRHS.CLT
#check @DGRHS.CLT.sourceRieszSingularPartition_original_rate
#print axioms DGRHS.CLT.sourceRieszSingularPartition_original_rate
