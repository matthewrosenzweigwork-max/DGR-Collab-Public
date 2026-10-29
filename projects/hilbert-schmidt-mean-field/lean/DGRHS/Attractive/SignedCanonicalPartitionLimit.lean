/- Concrete attractive canonical partition limit. The source factorial rows
derive both the actual operator margin and the proper higher particle moment.
The spectral data belong to the actual kernel operator and are not premises. -/
import DGRHS.CLT.SignedSourcePartitionFactory
import DGRHS.Attractive.FactorialCanonicalComparison
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology InnerProductSpace
namespace DGRHS.Attractive
universe u
variable {S : Type u} [MeasurableSpace S] [MeasurableSpace.CountablyGenerated S]
  {μ : Measure S} [IsProbabilityMeasure μ]

lemma sourceParticleExponent_zero_negative (h : S×S→ℝ) (β : ℝ)
    (N : ℕ) (x : Fin N→S) :
    DGRHS.CLT.sourceParticleExponent h (fun _=>0) 0 (-β) N x =
      β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x := by
  simp only [DGRHS.CLT.sourceParticleExponent,Finset.sum_const_zero,mul_zero,
    sub_zero,add_zero,neg_neg]

theorem exists_factorialCanonical_positive_partition_limit
    (h : S×S→ℝ) (hh : Measurable h) (C : ℝ)
    (hC : RowFactorialMoments μ h C)
    (hs : ∀ x y,h (x,y)=h (y,x))
    (hc : ∀ᵐ y ∂μ,∫ x,h (x,y) ∂μ=0) :
    let h2 := joint_memLp μ h hh C hC 2 (by omega)
    ∃ (ι : Type u) (eig : ι→ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
      (f : ι→ℕ) (hf : Function.Injective f),
      Countable ι ∧
      (∀ i,DGRHS.Kernel.integralOperator h h2 (b i)=eig i • b i) ∧
      ∀ β : ℝ,0≤β → β*(attractiveMomentConstant*C)<1 →
      Tendsto (fun N=>∫ x : Fin N→S,
        Real.exp (β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
        ∂Measure.pi (fun _ : Fin N=>μ)) atTop
        (𝓝 ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i=>-β*eig i)))⁻¹)) := by
  dsimp only
  let h2 := joint_memLp μ h hh C hC 2 (by omega)
  have hcr : ∀ᵐ x ∂μ,∫ y,h (x,y) ∂μ=0 := by
    filter_upwards [hc] with x hx
    simpa only [hs] using hx
  obtain ⟨ι,eig,b,f,hf,hcount,hb,hlimit⟩ :=
    DGRHS.CLT.exists_originalKernelSignedPartitionLimit h h2
      (Filter.Eventually.of_forall fun z=>hs z.2 z.1) hcr
  refine ⟨ι,eig,b,f,hf,hcount,hb,fun β hβ hsmall=>?_⟩
  have hmargin : |-β| * ‖DGRHS.Kernel.integralOperator h h2‖<1 := by
    simpa only [abs_neg,abs_of_nonneg hβ] using
      rowMoment_actual_operator_weak_margin h hh C β hC hβ hsmall
  have hexponent : ∀ N (x : Fin N→S),
      (2:ℝ)*DGRHS.CLT.sourceParticleExponent h (fun _=>0) 0 (-β) N x =
        β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x := by
    intro N x
    rw [sourceParticleExponent_zero_negative]
    ring
  have hm : ∀ N,Integrable (fun x : Fin N→S=>Real.exp
      ((2:ℝ)*DGRHS.CLT.sourceParticleExponent h (fun _=>0) 0 (-β) N x))
      (Measure.pi (fun _ : Fin N=>μ)) := by
    intro N
    simpa only [hexponent] using
      (factorialCanonical_positive_uniform h hh C β hC hs hc hβ hsmall N).1
  have hbound : ∀ N,(∫ x : Fin N→S,Real.exp
      ((2:ℝ)*DGRHS.CLT.sourceParticleExponent h (fun _=>0) 0 (-β) N x)
      ∂Measure.pi (fun _ : Fin N=>μ))≤2/(1-(β*(attractiveMomentConstant*C))^2) := by
    intro N
    simpa only [hexponent] using
      (factorialCanonical_positive_uniform h hh C β hC hs hc hβ hsmall N).2
  have ht := hlimit (fun _=>0) (integrable_const (0:ℝ))
    0 (-β) 2 (2/(1-(β*(attractiveMomentConstant*C))^2))
    hmargin (by norm_num) hm hbound
  simpa only [sourceParticleExponent_zero_negative,integral_zero,mul_zero,
    sub_zero,Real.exp_zero,one_mul] using ht
end DGRHS.Attractive
#check @DGRHS.Attractive.exists_factorialCanonical_positive_partition_limit
#print axioms DGRHS.Attractive.sourceParticleExponent_zero_negative
#print axioms DGRHS.Attractive.exists_factorialCanonical_positive_partition_limit
