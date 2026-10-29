import DGRHS.Gaussian.SourceRepulsiveRieszRateSpectrum
import DGRHS.Concentration.SourceRieszRate

/-! Original positive-Riesz source quantitative logarithmic fallback.
Source1941-2087 / thm:partitionFunctionBound(ii)504-529; authoritative SHA256
6f52778d92aa534e2b5851ca0f6b0712dc56470259cb3efcb7146ac2384dac0c.
Narrow application of exact unchanged native physical factory after own replay;
proper feature/cutoff/interpolation/full moments and actual spectrum are derived
upstream from physical bounded density. Genuine HasProd for the SAME chosen
full mean-zero basis is derived here from actual full/mean-zero multiplicity.
No rate, moment, UI, feature, spectral matching or determinant continuity premise.
All beta>=0,N>=1; beta0 and N1 are retained by imported actual bodies. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace DGRHS.SourceRepulsiveRieszRate
open DGRHS.Gaussian DGRHS.Concentration
universe u
theorem exists_canonical_partition_rate {ι : Type u} [Fintype ι]
    (s β : ℝ) (hs : 0<s) (hβ : 0≤β)
    (ha : 0<(Fintype.card ι:ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    let μ := gaussianRieszDensityMeasure ρ
    let h := hoeffdingCentered μ (gaussianRieszPhysicalPair (ι := ι) s)
    ∃ (hh : MemLp h 2 (μ.prod μ))
      (hSym : ∀ᵐ p ∂μ.prod μ,h p.swap=h p)
      (hCan : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
      (κ : Type u) (eig : κ→ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i,DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e i)=eig i•e i) ∧
      0<DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i) ∧
      HasProd (fun i => (1+β*eig i)*Real.exp (-(β*eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => β*eig i)) ∧
      Tendsto (canonicalPartition μ β h) atTop (𝓝 ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹)) ∧
      Tendsto (fun N ↦ Real.log (canonicalPartition μ β h N)) atTop
        (𝓝 (Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹))) ∧
      ∃ C : ℝ,0≤C ∧ ∀ N,1≤N→
        Integrable (fun x : Fin N→EuclideanSpace ℝ ι ↦ Real.exp
          (-β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) (Measure.pi (fun _ : Fin N ↦ μ)) ∧
        |canonicalPartition μ β h N-(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹|≤
          C*(Real.log (Real.exp 1+(N:ℝ)))^(-(((Fintype.card ι:ℝ)-2*s)/(2*s))) ∧
        |Real.log (canonicalPartition μ β h N)-Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹)|≤
          C*(Real.log (Real.exp 1+(N:ℝ)))^(-(((Fintype.card ι:ℝ)-2*s)/(2*s))) := by
  dsimp only
  obtain ⟨hh,hsym,hcan,κ,eig,e,hκ,he,hD,hT,hLog,C,hC,hRate⟩ :=
    gaussianRieszPhysical_log_partition_rate s β hs hβ ha ρ M hM hρ
  have hpos : ∀ v : Lp ℝ 2 (gaussianRieszDensityMeasure ρ),0 ≤ inner ℝ v
      (DGRHS.Kernel.integralOperator (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
        (gaussianRieszPhysicalPair s)) hh v) :=
    gaussianRieszPhysicalOperator_positive s hs ha ρ M hM hρ
  have hP := hasProd_actual_meanZero_spectrum _ hh hsym hcan hpos eig e he β hβ
  exact ⟨hh,hsym,hcan,κ,eig,e,hκ,he,hD,hP,hT,hLog,C,hC,hRate⟩

theorem exists_source_partition_rate {ι : Type u} [Fintype ι]
    (s β : ℝ) (hs : 0<s) (hβ : 0≤β) (ha : 0<(Fintype.card ι:ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun x y : EuclideanSpace ℝ ι ↦ gaussianRieszPhysicalPair s (x,y)
    let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    let I := DGRHS.interactionEnergy μ W
    ∃ (hh : MemLp h 2 (μ.prod μ))
      (hSym : ∀ᵐ p ∂μ.prod μ,h p.swap=h p)
      (hCan : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
      (κ : Type u) (eig : κ→ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i,DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e i)=eig i•e i) ∧
      0<DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i) ∧
      HasProd (fun i => (1+β*eig i)*Real.exp (-(β*eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => β*eig i)) ∧
      Tendsto (physicalRieszSourcePartition s β ρ) atTop
        (𝓝 (Real.exp (β*I)*(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹)) ∧
      Tendsto (fun N ↦ Real.log (physicalRieszSourcePartition s β ρ N)) atTop
        (𝓝 (β*I+Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹))) ∧
      ∃ C : ℝ,0≤C ∧ ∀ N,1≤N→
        Integrable (fun x : Fin N→EuclideanSpace ℝ ι ↦ Real.exp
          (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy h (DGRHS.potential μ W) I N x))
          (Measure.pi (fun _ : Fin N ↦ μ)) ∧
        Real.exp (β*I)≤physicalRieszSourcePartition s β ρ N ∧
        |physicalRieszSourcePartition s β ρ N-
          Real.exp (β*I)*(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹|≤
          C*(Real.log (Real.exp 1+(N:ℝ)))^(-(((Fintype.card ι:ℝ)-2*s)/(2*s))) ∧
        |Real.log (physicalRieszSourcePartition s β ρ N)-
          (β*I+Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹))|≤
          C*(Real.log (Real.exp 1+(N:ℝ)))^(-(((Fintype.card ι:ℝ)-2*s)/(2*s))) := by
  dsimp only
  obtain ⟨hh,hsym,hcan,κ,eig,e,hκ,he,hD,hT,hLog,C,hC,hRate⟩ :=
    physicalRieszSource_partition_rate s β hs hβ ha ρ M hM hρ
  have hpos : ∀ v : Lp ℝ 2 (gaussianRieszDensityMeasure ρ),0 ≤ inner ℝ v
      (DGRHS.Kernel.integralOperator (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
        (gaussianRieszPhysicalPair s)) hh v) :=
    gaussianRieszPhysicalOperator_positive s hs ha ρ M hM hρ
  have hP := hasProd_actual_meanZero_spectrum _ hh hsym hcan hpos eig e he β hβ
  exact ⟨hh,hsym,hcan,κ,eig,e,hκ,he,hD,hP,hT,hLog,C,hC,hRate⟩

end DGRHS.SourceRepulsiveRieszRate
#check @DGRHS.SourceRepulsiveRieszRate.exists_source_partition_rate
#print axioms DGRHS.SourceRepulsiveRieszRate.exists_source_partition_rate

#check @DGRHS.SourceRepulsiveRieszRate.exists_canonical_partition_rate
#print axioms DGRHS.SourceRepulsiveRieszRate.exists_canonical_partition_rate
