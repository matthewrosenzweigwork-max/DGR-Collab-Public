/- Positive-Riesz original static conclusion, with actual physical weights
and one uniquely identified source mean-zero covariance inverse throughout. -/
import DGRHS.CLT.SourceRieszKernelData
import DGRHS.CLT.SourceStaticCharacteristic
import DGRHS.CLT.SourceFiniteMGF
import DGRHS.Kernel.MeanZeroResolventUnique
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.CLT
open DGRHS.Gaussian
universe u
 theorem exists_sourceRieszStatic {ι : Type u} [Fintype ι]
    (m : ℕ) (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun (x y : EuclideanSpace ℝ ι) => gaussianRieszPhysicalPair s (x,y)
    let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    let hh := memLp_gaussianRieszCenteredPhysicalPair s hs ha ρ M hM hρ
    ∃ (hSym : ∀ᵐ p ∂μ.prod μ,h p.swap=h p)
      (hCan : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
      (R0 : DGRHS.Kernel.meanZeroL2 μ →L[ℝ] DGRHS.Kernel.meanZeroL2 μ),
      (∀ v,R0 v+β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (R0 v)=v) ∧
      (∀ v,R0 (v+β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan v)=v) ∧
      ∀ φ : Fin m → Lp ℝ 2 μ,
      ∃ (ν : Measure (ℕ → ℝ)) (Z : (ℕ → ℝ) → (Fin m → ℝ))
        (hν : IsProbabilityMeasure ν)
        (hPN : ∀ N,IsProbabilityMeasure ((Measure.pi (fun _ : Fin N => μ)).tilted
          (fun x => -β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N x))),
      letI := hν
      letI := hPN
      TendstoInDistribution (sourceObservableFluctuation φ) atTop Z
        (fun N => (Measure.pi (fun _ : Fin N => μ)).tilted
          (fun x => -β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N x)) ν ∧
      HasGaussianLaw Z ν ∧
      (∀ k,(∫ ω,Z ω k ∂ν)=0) ∧
      (∀ k l,Integrable (fun ω => Z ω k*Z ω l) ν ∧
        (∫ ω,Z ω k*Z ω l ∂ν)=inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
          (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l)))) ∧
      (∀ θ : Fin m → ℝ,Tendsto (fun N => ∫ x : Fin N → EuclideanSpace ℝ ι,
        Complex.exp ((∑ k : Fin m,θ k*sourceObservableFluctuation φ N x k : ℝ)*Complex.I)
        ∂(Measure.pi (fun _ : Fin N => μ)).tilted
          (fun x => -β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N x)) atTop
        (𝓝 (Complex.exp (-(∑ k : Fin m,∑ l : Fin m,θ k*θ l*
          inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
            (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l))) : ℝ)/2)))) ∧
      ∀ (K θ : Fin m → ℝ),(∀ k,∀ᵐ x ∂μ,|φ k x| ≤ K k) →
        (∀ N,Integrable (fun x : Fin N → EuclideanSpace ℝ ι =>
          Real.exp (∑ k : Fin m,θ k*sourceObservableFluctuation φ N x k))
          ((Measure.pi (fun _ : Fin N => μ)).tilted
            (fun x => -β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N x))) ∧
        Tendsto (fun N => ∫ x : Fin N → EuclideanSpace ℝ ι,
          Real.exp (∑ k : Fin m,θ k*sourceObservableFluctuation φ N x k)
          ∂(Measure.pi (fun _ : Fin N => μ)).tilted
            (fun x => -β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N x)) atTop
          (𝓝 (Real.exp ((∑ k : Fin m,∑ l : Fin m,θ k*θ l*
            inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
              (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l))))/2))) := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun (x y : EuclideanSpace ℝ ι) => gaussianRieszPhysicalPair s (x,y)
  let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  let F := DGRHS.potential μ W
  let I := DGRHS.interactionEnergy μ W
  let hh := memLp_gaussianRieszCenteredPhysicalPair s hs ha ρ M hM hρ
  obtain ⟨hSym,hCan,hPos⟩ := sourceRieszKernel_properties s hs ha ρ M hM hρ
  obtain ⟨R0,hR1,hR2,hStat⟩ := exists_sourceStaticCharacteristic m h hh hSym hCan hPos β hβ
  obtain ⟨T0,hT1,hT2,hMGF⟩ := exists_sourceFiniteMGF h hh hSym hCan hPos β hβ
  have hRT : R0=T0 := DGRHS.Kernel.meanZeroResolvent_unique h hh hSym hCan β R0 T0 hR1 hT2
  rw [←hRT] at hMGF
  obtain ⟨hF,C2,hC2⟩ := sourceRieszWeight_higher s β 2 hs hβ (by norm_num) ha ρ M hM hρ
  obtain ⟨_,C4,hC4⟩ := sourceRieszWeight_higher s β 4 hs hβ (by norm_num) ha ρ M hM hρ
  refine ⟨hSym,hCan,R0,hR1,hR2,fun φ => ?_⟩
  obtain ⟨ν,Z,hν,hPN,hw,hG,hMean,hCov,hCF⟩ := hStat φ F hF I 2 C2 (by norm_num)
    (fun N => (hC2 N).1) (fun N => (hC2 N).2)
  refine ⟨ν,Z,hν,hPN,hw,hG,hMean,hCov,hCF,fun K θ hK => ?_⟩
  exact hMGF m φ K θ hK F hF I 2 C4 (by norm_num)
    (fun N => by simpa only [show (2:ℝ)*2=4 by norm_num] using (hC4 N).1)
    (fun N => by simpa only [show (2:ℝ)*2=4 by norm_num] using (hC4 N).2)
end DGRHS.CLT
#print axioms DGRHS.CLT.exists_sourceRieszStatic
#check @DGRHS.CLT.exists_sourceRieszStatic
