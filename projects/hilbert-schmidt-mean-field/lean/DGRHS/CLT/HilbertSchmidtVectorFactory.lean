/- Actual source-kernel factory for the full same-process joint limit. -/
import DGRHS.CLT.HilbertSchmidtVectorJointCLT
import DGRHS.CLT.KernelRepresentativeTransfer
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.CLT
universe u
variable {S : Type u} [MeasurableSpace S] {j : Type*} [Fintype j] {μ : Measure S} [IsProbabilityMeasure μ]

theorem exists_hilbertSchmidtParticleVectorJointCLT [MeasurableSpace.CountablyGenerated S]
    (h : S × S → ℝ) (hhm : Measurable h) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0) :
    ∃ (ι : Type u) (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
      (f : ι → ℕ) (hf : Function.Injective f),
      Countable ι ∧
      (∀ i, DGRHS.Kernel.integralOperator h hh (b i) = eig i • b i) ∧
      ∀ v : j → Lp ℝ 2 μ, (∀ l, (∫ x, v l x ∂μ) = 0) →
      TendstoInDistribution
        (fun N (x : Fin N → S) => jointReadoutVector (fun l => (Real.sqrt N)⁻¹*∑ i : Fin N, v l (x i))
          (DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) atTop
        (fun ω => jointReadoutVector (fun l => DGRHS.Gaussian.indexedGaussianIsometry b f hf (v l) ω)
          (DGRHS.Gaussian.centeredGaussianChaos eig f ω))
        (fun N => Measure.pi (fun _ : Fin N => μ)) IsonormalProcess.iidStdGaussian := by
  obtain ⟨ι,eig,b,hcount,hb⟩ := DGRHS.Kernel.exists_integralOperator_eigenbasis h hh hs
  letI := hcount
  let f := DGRHS.Gaussian.countableGaussianIndex (ι := ι)
  exact ⟨ι,eig,b,f,f.injective,hcount,hb,fun v hv =>
    hilbertSchmidtParticleVectorJointCLT h hhm hh hs hc eig b hb f f.injective v hv⟩

theorem exists_originalKernelVectorJointCLT [MeasurableSpace.CountablyGenerated S]
    (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0) :
    ∃ (ι : Type u) (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
      (f : ι → ℕ) (hf : Function.Injective f),
      Countable ι ∧
      (∀ i, DGRHS.Kernel.integralOperator h hh (b i) = eig i • b i) ∧
      ∀ v : j → Lp ℝ 2 μ, (∀ l, (∫ x, v l x ∂μ) = 0) →
      TendstoInDistribution
        (fun N (x : Fin N → S) => jointReadoutVector (fun l => (Real.sqrt N)⁻¹*∑ i : Fin N, v l (x i))
          (DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) atTop
        (fun ω => jointReadoutVector (fun l => DGRHS.Gaussian.indexedGaussianIsometry b f hf (v l) ω)
          (DGRHS.Gaussian.centeredGaussianChaos eig f ω))
        (fun N => Measure.pi (fun _ : Fin N => μ)) IsonormalProcess.iidStdGaussian := by
  let κ := hh.toLp h
  have he : (κ : S × S → ℝ) =ᵐ[μ.prod μ] h := hh.coeFn_toLp
  have hswap : ∀ᵐ p ∂μ.prod μ, κ p.swap = κ p := by
    filter_upwards [he,(Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae he,hs]
      with p h1 h2 h3
    exact h2.trans (h3.trans h1.symm)
  have hcan : ∀ᵐ x ∂μ, (∫ y, κ (x,y) ∂μ) = 0 := by
    filter_upwards [Measure.ae_ae_of_ae_prod he,hc] with x hx hc
    exact (integral_congr_ae hx).trans hc
  obtain ⟨ι,eig,b,f,hf,hcount,hb,hlimit⟩ := exists_hilbertSchmidtParticleVectorJointCLT (j := j)
    (κ : S × S → ℝ) (Lp.stronglyMeasurable κ).measurable (Lp.memLp κ) hswap hcan
  letI := hcount
  have hOp := integralOperator_Lp_representative h hh
  have hb' : ∀ i, DGRHS.Kernel.integralOperator h hh (b i) = eig i • b i := by
    intro i
    rw [← hOp]
    exact hb i
  refine ⟨ι,eig,b,f,hf,hcount,hb',fun v hv => ?_⟩
  refine (hlimit v hv).congr (fun N => ?_) (ae_eq_refl _)
  filter_upwards [normalizedOffDiagonalSum_congr_ae (J := Fin N) he] with x hx
  exact congrArg (fun q : ℝ => jointReadoutVector (fun l => (Real.sqrt N)⁻¹*∑ i : Fin N, v l (x i)) q) hx
end DGRHS.CLT
#print axioms DGRHS.CLT.exists_hilbertSchmidtParticleVectorJointCLT
#print axioms DGRHS.CLT.exists_originalKernelVectorJointCLT
#check @DGRHS.CLT.exists_originalKernelVectorJointCLT
