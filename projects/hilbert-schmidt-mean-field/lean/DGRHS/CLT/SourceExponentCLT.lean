/- Exact source affine exponent, N*F_N = U_N/2 - average(F) + I.
The source one-body LLN and actual kernel CLT are instantiated, with no higher
moment or tilted convergence premise. This is the untilted exponent law only. -/
import DGRHS.CLT.SourceJointL1Factory
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators
namespace DGRHS.CLT
universe u
variable {S : Type u} [MeasurableSpace S] {j : Type*} [Fintype j]
  {μ : Measure S} [IsProbabilityMeasure μ]

def sourceCanonicalModulatedEnergy (h : S × S → ℝ) (F : S → ℝ) (I : ℝ)
    (N : ℕ) (x : Fin N → S) : ℝ :=
  (N : ℝ)⁻¹ * (DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x / 2 -
    (N : ℝ)⁻¹*∑ i : Fin N, F (x i) + I)

lemma sourceCanonicalModulatedEnergy_FNdef (h : S × S → ℝ) (F : S → ℝ)
    (I : ℝ) (N : ℕ) (x : Fin N → S) :
    sourceCanonicalModulatedEnergy h F I N x =
      (2*(N : ℝ)^2)⁻¹ * DGRHS.CanonicalVariance.offDiagonalSum h x -
      ((N : ℝ)^2)⁻¹ * (∑ i : Fin N, F (x i)) + (N : ℝ)⁻¹ * I := by
  by_cases hn : N = 0
  · subst N
    simp [sourceCanonicalModulatedEnergy,DGRHS.CanonicalVariance.normalizedOffDiagonalSum]
  · have hn' : (N : ℝ) ≠ 0 := by exact_mod_cast hn
    simp only [sourceCanonicalModulatedEnergy,DGRHS.CanonicalVariance.normalizedOffDiagonalSum,
      Fintype.card_fin]
    field_simp
    <;> ring

lemma sourceCanonicalModulatedEnergy_exponent (h : S × S → ℝ) (F : S → ℝ)
    (I β : ℝ) {N : ℕ} (hn : 0 < N) (x : Fin N → S) :
    -β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N x =
      -β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x +
        β*((N : ℝ)⁻¹*∑ i : Fin N, F (x i)) - β*I := by
  have hn' : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  dsimp [sourceCanonicalModulatedEnergy]
  field_simp
  <;> ring

theorem exists_originalKernelSourceExponentCLT [MeasurableSpace.CountablyGenerated S]
    (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0) :
    ∃ (ι : Type u) (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
      (f : ι → ℕ) (hf : Function.Injective f),
      Countable ι ∧
      (∀ i, DGRHS.Kernel.integralOperator h hh (b i) = eig i • b i) ∧
      ∀ (v : j → Lp ℝ 2 μ), (∀ l, (∫ x, v l x ∂μ) = 0) →
      ∀ (F : S → ℝ), Integrable F μ → ∀ β I : ℝ,
      TendstoInDistribution
        (fun N (x : Fin N → S) =>
          (jointReadoutVector (fun l => (Real.sqrt N)⁻¹*∑ i : Fin N, v l (x i))
            (DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x),
           -β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x +
             β*((N : ℝ)⁻¹*∑ i : Fin N, F (x i)) - β*I)) atTop
        (fun ω =>
          (jointReadoutVector
            (fun l => DGRHS.Gaussian.indexedGaussianIsometry b f hf (v l) ω)
            (DGRHS.Gaussian.centeredGaussianChaos eig f ω),
           -β/2*DGRHS.Gaussian.centeredGaussianChaos eig f ω + β*(∫ x,F x ∂μ) - β*I))
        (fun N => Measure.pi (fun _ : Fin N => μ)) IsonormalProcess.iidStdGaussian := by
  obtain ⟨ι,eig,b,f,hf,hcount,hb,hlimit⟩ := exists_originalKernelVectorJointL1CLT (j := j) h hh hs hc
  letI := hcount
  refine ⟨ι,eig,b,f,hf,hcount,hb,fun v hv F hi β I => ?_⟩
  let A := fun z : EuclideanSpace ℝ (j ⊕ Unit) × ℝ =>
    (z.1,-β/2*z.1 (Sum.inr ()) + β*z.2 - β*I)
  have ha : Continuous A := by fun_prop
  convert (hlimit v hv F hi).continuous_comp (g := A) ha using 1 <;> rfl

end DGRHS.CLT
#print axioms DGRHS.CLT.sourceCanonicalModulatedEnergy_FNdef
#print axioms DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent
#print axioms DGRHS.CLT.exists_originalKernelSourceExponentCLT
#check @DGRHS.CLT.exists_originalKernelSourceExponentCLT
