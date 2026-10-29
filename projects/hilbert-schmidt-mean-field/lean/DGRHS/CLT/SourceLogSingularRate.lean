/- Explicit original singular-partition quantitative export. The same actual
mean-zero operator, determinant and physical four-beta tail are retained.
Collision-free density identification and properness precede every toReal. -/
import DGRHS.Gaussian.SourceRepulsiveLogRate
import DGRHS.CLT.SourceLogSingularIdentification
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace DGRHS.CLT
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι]

theorem sourceLogSingularPartition_original_rate (β : ℝ≥0)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (htail : Integrable (fun x=>Real.exp (-4*(β:ℝ)*
      logPhysicalPotential (gaussianRieszDensityMeasure ρ) x)) (gaussianRieszDensityMeasure ρ)) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
    let h := hoeffdingCentered μ logPhysicalPair
    let hh := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
    ∃ (hs : ∀ᵐ p ∂μ.prod μ,h p.swap=h p) (hc : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
      (κ : Type u) (eig : κ→ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧ (∀ i,DGRHS.Kernel.integralOperatorOnMeanZero h hh hs hc (e i)=eig i • e i) ∧
      0<DGRHS.Kernel.regularizedDet (fun i=>(β:ℝ)*eig i) ∧
      HasProd (fun i=>(1+(β:ℝ)*eig i)*Real.exp (-((β:ℝ)*eig i)))
        (DGRHS.Kernel.regularizedDet (fun i=>(β:ℝ)*eig i)) ∧
      Tendsto (fun N=>(sourceLogSingularPartition β ρ N).toReal) atTop
        (𝓝 (Real.exp ((β:ℝ)*DGRHS.interactionEnergy μ W)*
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i=>(β:ℝ)*eig i)))⁻¹)) ∧
      ∃ c C : ℝ,0<c ∧ c≤1/2 ∧ 0≤C ∧ ∀ N : ℕ,1≤N →
        (0<sourceLogSingularPartition β ρ N ∧ sourceLogSingularPartition β ρ N<∞) ∧
        |(sourceLogSingularPartition β ρ N).toReal-
          Real.exp ((β:ℝ)*DGRHS.interactionEnergy μ W)*
            (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i=>(β:ℝ)*eig i)))⁻¹|≤
          C*(Real.exp 1+(N:ℝ))^(-c) := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
  let h := hoeffdingCentered μ logPhysicalPair
  let E := fun N=>sourceCanonicalModulatedEnergy h (DGRHS.potential μ W)
    (DGRHS.interactionEnergy μ W) N
  obtain ⟨hs,hc,κ,eig,e,hκ,he,hD,hProd,hT,c,C,hc0,hc1,hC,hRate⟩ :=
    DGRHS.SourceRepulsiveLogRate.exists_source_partition_rate (β:ℝ) β.coe_nonneg
      hd ρ M hM hρ hpair htail
  have hEq (N : ℕ) : (sourceLogSingularPartition β ρ N).toReal=
      ∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp (-(β:ℝ)*(N:ℝ)*E N x) ∂Measure.pi (fun _ : Fin N=>μ) := by
    rw [sourceLogSingularPartition_eq_integral β hd ρ M hM hρ hpair N,
      ENNReal.toReal_ofReal (integral_nonneg fun x=>(Real.exp_pos _).le)]
  refine ⟨hs,hc,κ,eig,e,hκ,he,hD,hProd,?_,c,C,hc0,hc1,hC,?_⟩
  · have hFun : (fun N=>(sourceLogSingularPartition β ρ N).toReal)=
        (fun N=>∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp (-(β:ℝ)*(N:ℝ)*E N x)
          ∂Measure.pi (fun _ : Fin N=>μ)) := funext hEq
    rw [hFun]
    exact hT
  · intro N hN
    refine ⟨sourceLogSingularPartition_pos_finite β hd ρ M hM hρ hpair N,?_⟩
    rw [hEq]
    exact (hRate N hN).2

end DGRHS.CLT
#check @DGRHS.CLT.sourceLogSingularPartition_original_rate
#print axioms DGRHS.CLT.sourceLogSingularPartition_original_rate
