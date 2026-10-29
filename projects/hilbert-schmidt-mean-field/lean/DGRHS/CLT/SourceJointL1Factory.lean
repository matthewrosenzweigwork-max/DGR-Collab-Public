/- Actual source-kernel joint law with the source's only-L1 one-body term.
The untilted law is derived here from the true HS kernel, not assumed. -/
import DGRHS.CLT.HilbertSchmidtVectorFactory
import DGRHS.CLT.L1JointSlutsky
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators
namespace DGRHS.CLT
universe u
variable {S : Type u} [MeasurableSpace S] {j : Type*} [Fintype j]
  {μ : Measure S} [IsProbabilityMeasure μ]

theorem exists_originalKernelVectorJointL1CLT [MeasurableSpace.CountablyGenerated S]
    (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0) :
    ∃ (ι : Type u) (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
      (f : ι → ℕ) (hf : Function.Injective f),
      Countable ι ∧
      (∀ i, DGRHS.Kernel.integralOperator h hh (b i) = eig i • b i) ∧
      ∀ (v : j → Lp ℝ 2 μ), (∀ l, (∫ x, v l x ∂μ) = 0) →
      ∀ (F : S → ℝ), Integrable F μ →
      TendstoInDistribution
        (fun N (x : Fin N → S) =>
          (jointReadoutVector (fun l => (Real.sqrt N)⁻¹*∑ i : Fin N, v l (x i))
            (DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x),
           (N : ℝ)⁻¹*∑ i : Fin N, F (x i))) atTop
        (fun ω =>
          (jointReadoutVector
            (fun l => DGRHS.Gaussian.indexedGaussianIsometry b f hf (v l) ω)
            (DGRHS.Gaussian.centeredGaussianChaos eig f ω),∫ x, F x ∂μ))
        (fun N => Measure.pi (fun _ : Fin N => μ)) IsonormalProcess.iidStdGaussian := by
  obtain ⟨ι,eig,b,f,hf,hcount,hb,hlimit⟩ := exists_originalKernelVectorJointCLT (j := j) h hh hs hc
  letI := hcount
  refine ⟨ι,eig,b,f,hf,hcount,hb,fun v hv F hi => ?_⟩
  exact finiteParticle_joint_with_L1_average _ _ (hlimit v hv) F hi

end DGRHS.CLT
#print axioms DGRHS.CLT.exists_originalKernelVectorJointL1CLT
#check @DGRHS.CLT.exists_originalKernelVectorJointL1CLT
