/- Original positive-Riesz static fluctuation theorem under the literal singular
Gibbs law. Full L2 tests, the SAME actual mean-zero covariance inverse,
characteristic functions and bounded-test MGFs are all retained. -/
import DGRHS.CLT.SourceRieszStatic
import DGRHS.CLT.SourceRieszSingularGibbs
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.CLT
open DGRHS.Gaussian
universe u
 theorem exists_sourceRieszSingularStatic {ι : Type u} [Fintype ι]
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
        (hPN : ∀ N,IsProbabilityMeasure (sourceRieszSingularGibbs s β ρ N)),
      letI := hν
      letI := hPN
      TendstoInDistribution (sourceObservableFluctuation φ) atTop Z
        (fun N => sourceRieszSingularGibbs s β ρ N) ν ∧
      HasGaussianLaw Z ν ∧
      (∀ k,(∫ ω,Z ω k ∂ν)=0) ∧
      (∀ k l,Integrable (fun ω => Z ω k*Z ω l) ν ∧
        (∫ ω,Z ω k*Z ω l ∂ν)=inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
          (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l)))) ∧
      (∀ θ : Fin m → ℝ,Tendsto (fun N => ∫ x : Fin N → EuclideanSpace ℝ ι,
        Complex.exp ((∑ k : Fin m,θ k*sourceObservableFluctuation φ N x k : ℝ)*Complex.I)
        ∂sourceRieszSingularGibbs s β ρ N) atTop
        (𝓝 (Complex.exp (-(∑ k : Fin m,∑ l : Fin m,θ k*θ l*
          inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
            (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l))) : ℝ)/2)))) ∧
      ∀ (K θ : Fin m → ℝ),(∀ k,∀ᵐ x ∂μ,|φ k x| ≤ K k) →
        (∀ N,Integrable (fun x : Fin N → EuclideanSpace ℝ ι =>
          Real.exp (∑ k : Fin m,θ k*sourceObservableFluctuation φ N x k))
          (sourceRieszSingularGibbs s β ρ N)) ∧
        Tendsto (fun N => ∫ x : Fin N → EuclideanSpace ℝ ι,
          Real.exp (∑ k : Fin m,θ k*sourceObservableFluctuation φ N x k)
          ∂sourceRieszSingularGibbs s β ρ N) atTop
          (𝓝 (Real.exp ((∑ k : Fin m,∑ l : Fin m,θ k*θ l*
            inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
              (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l))))/2))) := by
  dsimp only
  obtain ⟨hSym,hCan,R0,hR1,hR2,hStat⟩ := exists_sourceRieszStatic m s β hs hβ ha ρ M hM hρ
  refine ⟨hSym,hCan,R0,hR1,hR2,fun φ => ?_⟩
  obtain ⟨ν,Z,hν,hPN,hw,hG,hMean,hCov,hCF,hMGF⟩ := hStat φ
  have he (N : ℕ) : sourceRieszSingularGibbs s β ρ N =
      (Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ)).tilted
        (fun x => -β*(N : ℝ)*sourceCanonicalModulatedEnergy
          (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
          (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b => gaussianRieszPhysicalPair s (a,b)))
          (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b => gaussianRieszPhysicalPair s (a,b))) N x) := by
    rw [sourceRieszSingularGibbs_eq s β hs hβ ha ρ M hM hρ N, ←sourceEnergyTilt_eq _ _ _ β N]
  have hPN' (N : ℕ) : IsProbabilityMeasure (sourceRieszSingularGibbs s β ρ N) :=
    sourceRieszSingularGibbs_probability s β hs hβ ha ρ M hM hρ N
  refine ⟨ν,Z,hν,hPN',?_⟩
  simpa only [he] using ⟨hw,hG,hMean,hCov,hCF,hMGF⟩
end DGRHS.CLT
#check @DGRHS.CLT.exists_sourceRieszSingularStatic
#print axioms DGRHS.CLT.exists_sourceRieszSingularStatic
