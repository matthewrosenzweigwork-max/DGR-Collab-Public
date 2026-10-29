/- Repulsive-log original static conclusion, with actual physical weights
and one uniquely identified source mean-zero covariance inverse throughout. -/
import DGRHS.CLT.SourceLogStatic
import DGRHS.CLT.SourceLogSingularIdentification
import DGRHS.CLT.SourceStaticCharacteristic
import DGRHS.CLT.SourceFiniteMGF
import DGRHS.Kernel.MeanZeroResolventUnique
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators InnerProductSpace NNReal
namespace DGRHS.CLT
open DGRHS.Gaussian
universe u
 theorem exists_sourceLogSingularStatic {ι : Type u} [Fintype ι]
    (m : ℕ) (β : ℝ≥0)
    (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun (x y : EuclideanSpace ℝ ι) => logPhysicalPair (x,y)
    let h := hoeffdingCentered μ (logPhysicalPair)
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    let hh := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
    ∃ (hSym : ∀ᵐ p ∂μ.prod μ,h p.swap=h p)
      (hCan : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
      (R0 : DGRHS.Kernel.meanZeroL2 μ →L[ℝ] DGRHS.Kernel.meanZeroL2 μ),
      (∀ v,R0 v+β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (R0 v)=v) ∧
      (∀ v,R0 (v+β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan v)=v) ∧
      ∀ φ : Fin m → Lp ℝ 2 μ,
      ∃ (ν : Measure (ℕ → ℝ)) (Z : (ℕ → ℝ) → (Fin m → ℝ))
        (hν : IsProbabilityMeasure ν)
        (hPN : ∀ N,IsProbabilityMeasure (sourceLogSingularGibbs β ρ N)),
      letI := hν
      letI := hPN
      TendstoInDistribution (sourceObservableFluctuation φ) atTop Z
        (fun N => sourceLogSingularGibbs β ρ N) ν ∧
      HasGaussianLaw Z ν ∧
      (∀ k,(∫ ω,Z ω k ∂ν)=0) ∧
      (∀ k l,Integrable (fun ω => Z ω k*Z ω l) ν ∧
        (∫ ω,Z ω k*Z ω l ∂ν)=inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
          (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l)))) ∧
      (∀ θ : Fin m → ℝ,Tendsto (fun N => ∫ x : Fin N → EuclideanSpace ℝ ι,
        Complex.exp ((∑ k : Fin m,θ k*sourceObservableFluctuation φ N x k : ℝ)*Complex.I)
        ∂sourceLogSingularGibbs β ρ N) atTop
        (𝓝 (Complex.exp (-(∑ k : Fin m,∑ l : Fin m,θ k*θ l*
          inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
            (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l))) : ℝ)/2)))) ∧
      ∀ (K θ : Fin m → ℝ),(∀ k,∀ᵐ x ∂μ,|φ k x| ≤ K k) →
        (∀ N,Integrable (fun x : Fin N → EuclideanSpace ℝ ι =>
          Real.exp (∑ k : Fin m,θ k*sourceObservableFluctuation φ N x k))
          (sourceLogSingularGibbs β ρ N)) ∧
        Tendsto (fun N => ∫ x : Fin N → EuclideanSpace ℝ ι,
          Real.exp (∑ k : Fin m,θ k*sourceObservableFluctuation φ N x k)
          ∂sourceLogSingularGibbs β ρ N) atTop
          (𝓝 (Real.exp ((∑ k : Fin m,∑ l : Fin m,θ k*θ l*
            inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
              (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l))))/2))) := by
  dsimp only
  obtain ⟨hSym,hCan,R0,hR1,hR2,hStat⟩ :=
    exists_sourceLogStatic m (β:ℝ) β.coe_nonneg hd ρ M hM hρ hpair
  refine ⟨hSym,hCan,R0,hR1,hR2,fun φ => ?_⟩
  obtain ⟨ν,Z,hν,hPN,hw,hG,hMean,hCov,hCF,hMGF⟩ := hStat φ
  have he (N : ℕ) : sourceLogSingularGibbs β ρ N =
      (Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ)).tilted
        (fun x => -(β:ℝ)*(N:ℝ)*sourceCanonicalModulatedEnergy
          (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair)
          (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b=>logPhysicalPair (a,b)))
          (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b=>logPhysicalPair (a,b))) N x) := by
    rw [sourceLogSingularGibbs_eq β hd ρ M hM hρ hpair N,
      ←sourceEnergyTilt_eq _ _ _ (β:ℝ) N]
  have hPN' (N : ℕ) : IsProbabilityMeasure (sourceLogSingularGibbs β ρ N) :=
    sourceLogSingularGibbs_probability β hd ρ M hM hρ hpair N
  refine ⟨ν,Z,hν,hPN',?_⟩
  simpa only [he] using ⟨hw,hG,hMean,hCov,hCF,hMGF⟩
end DGRHS.CLT
#check @DGRHS.CLT.exists_sourceLogSingularStatic
#print axioms DGRHS.CLT.exists_sourceLogSingularStatic
