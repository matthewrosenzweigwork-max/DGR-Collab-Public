/- Actual kernel determinant is independent of a complete eigenbasis.
The nonzero label equivalence comes from true compact eigenspace dimensions;
the regularized products are genuine convergent positive products. -/
import DGRHS.Kernel.SpectralHilbertSchmidt
import DGRHS.Kernel.SpectralMultiplicityLabels
import DGRHS.Gaussian.FeatureMultiplicity
noncomputable section
open MeasureTheory
namespace DGRHS.Kernel
variable {S ι κ : Type*} [MeasurableSpace S]
    {μ : Measure S} [IsProbabilityMeasure μ]

theorem exists_sameKernel_nonzero_eigenbasis_equiv (h : S × S → ℝ)
    (hh : MemLp h 2 (μ.prod μ)) (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (a : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (hb : ∀ i, integralOperator h hh (b i) = a i • b i)
    (c : κ → ℝ) (e : HilbertBasis κ ℝ (Lp ℝ 2 μ))
    (he : ∀ i, integralOperator h hh (e i) = c i • e i) :
    ∃ f : {i // a i ≠ 0} ≃ {j // c j ≠ 0}, ∀ i : {i // a i ≠ 0}, a i.val = c (f i).val := by
  have hT := integralOperator_isSymmetric h hh hs
  have hF : ∀ r, r ≠ 0 → FiniteDimensional ℝ
      (Module.End.eigenspace (integralOperator h hh).toLinearMap r) :=
    fun r hr => (integralOperator h hh).finite_dimensional_eigenspace
      (integralOperator_isCompact h hh) r hr
  exact exists_nonzeroSpectralLabelEquiv (integralOperator h hh).toLinearMap hT
    (integralOperator h hh).toLinearMap hT a b hb c e he hF hF (fun _ _ => rfl)

theorem sameKernel_regularizedDet_basis_independent (h : S × S → ℝ)
    (hh : MemLp h 2 (μ.prod μ)) (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (a : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (hb : ∀ i, integralOperator h hh (b i) = a i • b i)
    (c : κ → ℝ) (e : HilbertBasis κ ℝ (Lp ℝ 2 μ))
    (he : ∀ i, integralOperator h hh (e i) = c i • e i)
    (β : ℝ) (hm : ∀ i, 0 < 1+β*a i) :
    HasProd (fun i => (1+β*a i)*Real.exp (-(β*a i))) (regularizedDet (fun i => β*a i)) ∧
    HasProd (fun j => (1+β*c j)*Real.exp (-(β*c j))) (regularizedDet (fun i => β*a i)) ∧
    regularizedDet (fun i => β*a i) = regularizedDet (fun j => β*c j) ∧
    0 < regularizedDet (fun i => β*a i) := by
  have hsquare := summable_scaled_eigenvalue_sq
    a (summable_integralOperator_eigenvalue_sq h hh a b hb) β
  have hp := hasProd_regularizedDet hsquare hm
  rw [←regularizedDet_eq_exp hsquare hm] at hp
  obtain ⟨f,hf⟩ := exists_sameKernel_nonzero_eigenbasis_equiv h hh hs a b hb c e he
  have hp' := (hasProd_regularizedFactors_iff_nonzero_equiv a c β _ f hf).mp hp
  exact ⟨hp,hp',hp'.tprod_eq.symm,regularizedDet_pos hsquare hm⟩
end DGRHS.Kernel
#print axioms DGRHS.Kernel.exists_sameKernel_nonzero_eigenbasis_equiv
#print axioms DGRHS.Kernel.sameKernel_regularizedDet_basis_independent
#check @DGRHS.Kernel.sameKernel_regularizedDet_basis_independent
