/- Source finite-observable static conclusion assembled with the SAME chosen
Gaussian process, genuine L2_0 inverse, and literal normalized energy measure.
The only remaining physical obligations are actual higher weight moments. -/
import DGRHS.CLT.FiniteGaussianCharacteristic
import DGRHS.CLT.SourceEnergyTilt
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.CLT
universe u
variable {S : Type u} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

theorem exists_sourceStaticCharacteristic [MeasurableSpace.CountablyGenerated S]
    (m : ℕ) (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ z ∂μ.prod μ,h z.swap = h z)
    (hc : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ) = 0)
    (hpos : ∀ v : Lp ℝ 2 μ,0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator h hh v))
    (β : ℝ) (hβ : 0 ≤ β) :
    ∃ R0 : DGRHS.Kernel.meanZeroL2 μ →L[ℝ] DGRHS.Kernel.meanZeroL2 μ,
      (∀ v,R0 v+β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hs hc (R0 v) = v) ∧
      (∀ v,R0 (v+β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hs hc v) = v) ∧
    ∀ (φ : Fin m → Lp ℝ 2 μ) (F : S → ℝ),Integrable F μ → ∀ (I p C : ℝ),1 < p →
      (∀ N,Integrable (fun x : Fin N → S => Real.exp (p*sourceParticleExponent h F I β N x))
        (Measure.pi (fun _ : Fin N => μ))) →
      (∀ N,(∫ x : Fin N → S,Real.exp (p*sourceParticleExponent h F I β N x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ C) →
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
      (∀ k,(∫ ω,Z ω k ∂ν) = 0) ∧
      (∀ k l,Integrable (fun ω => Z ω k*Z ω l) ν ∧
        (∫ ω,Z ω k*Z ω l ∂ν) = inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
          (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l)))) ∧
      ∀ θ : Fin m → ℝ,Tendsto (fun N => ∫ x : Fin N → S,
        Complex.exp ((∑ k : Fin m,θ k*sourceObservableFluctuation φ N x k : ℝ)*Complex.I)
        ∂(Measure.pi (fun _ : Fin N => μ)).tilted
          (fun x => -β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N x)) atTop
        (𝓝 (Complex.exp (-(∑ k : Fin m,∑ l : Fin m,θ k*θ l*
          inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
            (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l))) : ℝ)/2))) := by
  obtain ⟨ι,eig,b,f,hf,hcount,hb,hfactory⟩ := exists_sourceKernelGibbsGaussian m h hh hs hc hpos
  obtain ⟨R0,hR1,hR2,hstat⟩ := hfactory β hβ
  refine ⟨R0,hR1,hR2,fun φ F hF I p C hp hm hC => ?_⟩
  obtain ⟨hPN,hν,hw,hG,hmean,hcov⟩ := hstat (fun k => DGRHS.Kernel.sourceCenteredL2 (φ k))
    F hF I p C hp hm hC
  let ν := IsonormalProcess.iidStdGaussian.tilted
    (fun ω => -(β/2)*DGRHS.Gaussian.centeredGaussianChaos eig f ω)
  let Z := fun ω k => DGRHS.Gaussian.indexedGaussianIsometry b f hf
    (DGRHS.Kernel.sourceCenteredL2 (φ k)) ω
  have hPN' : ∀ N,IsProbabilityMeasure ((Measure.pi (fun _ : Fin N => μ)).tilted
      (fun x => -β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N x)) := by
    intro N
    rw [sourceEnergyTilt_eq]
    exact hPN N
  refine ⟨ν,Z,hν,hPN',?_⟩
  letI := hPN
  letI := hPN'
  letI := hν
  have hweak := sourceObservableFluctuation_tendsto φ
    (fun N => sourceParticleExponent h F I β N) Z hw
  have hweak' : TendstoInDistribution (sourceObservableFluctuation φ) atTop Z
      (fun N => (Measure.pi (fun _ : Fin N => μ)).tilted
        (fun x => -β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N x)) ν := by
    simpa only [sourceEnergyTilt_eq] using hweak
  refine ⟨hweak',hG,hmean,hcov,fun θ => ?_⟩
  exact finiteGaussian_characteristic_tendsto (sourceObservableFluctuation φ) Z hweak' hG hmean
    (fun k l => inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
      (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l)))) (fun k l => (hcov k l).2) θ
end DGRHS.CLT
#print axioms DGRHS.CLT.exists_sourceStaticCharacteristic
#check @DGRHS.CLT.exists_sourceStaticCharacteristic
