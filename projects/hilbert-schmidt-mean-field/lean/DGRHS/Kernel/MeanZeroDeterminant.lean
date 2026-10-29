/- The original determinant acts on genuine L2_0. Every nonzero eigenspace
of a canonical kernel is identified with its actual restriction's eigenspace.
Constants and other zero modes contribute unit determinant factors. -/
import DGRHS.Kernel.MeanZeroSpace
import DGRHS.Kernel.DeterminantBasisIndependence
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace DGRHS.Kernel
universe u
variable {S : Type u} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

instance meanZeroL2_completeSpace : CompleteSpace (meanZeroL2 μ) := by
  unfold meanZeroL2
  infer_instance

def nonzeroMeanZeroEigenspaceEquiv (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0) (r : ℝ) (hr : r ≠ 0) :
    Module.End.eigenspace (integralOperator h hh).toLinearMap r ≃ₗ[ℝ]
      Module.End.eigenspace (integralOperatorOnMeanZero h hh hs hc).toLinearMap r where
  toFun v := ⟨⟨v, (mem_meanZeroL2_iff _).mpr (integral_eigenfunction_eq_zero
    h hh hs hc v hr (Module.End.mem_eigenspace_iff.mp v.property))⟩,
    Module.End.mem_eigenspace_iff.mpr (Subtype.ext (Module.End.mem_eigenspace_iff.mp v.property))⟩
  invFun v := ⟨v.val.val, Module.End.mem_eigenspace_iff.mpr
    (congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp v.property))⟩
  left_inv v := by rfl
  right_inv v := by rfl
  map_add' v w := by rfl
  map_smul' c v := by rfl

lemma integralOperatorOnMeanZero_isSymmetric (h : S × S → ℝ)
    (hh : MemLp h 2 (μ.prod μ)) (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0) :
    (integralOperatorOnMeanZero h hh hs hc).toLinearMap.IsSymmetric := by
  intro v w
  exact integralOperator_isSymmetric h hh hs v w

lemma integralOperatorOnMeanZero_isCompact (h : S × S → ℝ)
    (hh : MemLp h 2 (μ.prod μ)) (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0) :
    IsCompactOperator (integralOperatorOnMeanZero h hh hs hc) := by
  exact (integralOperator_isCompact h hh).restrict
    (fun v _ => integralOperator_mem_meanZeroL2 h hh hs hc v)
    (ContinuousLinearMap.isClosed_ker (innerSL ℝ (oneL2 (μ := μ))))

theorem exists_integralOperatorOnMeanZero_eigenbasis [MeasurableSpace.CountablyGenerated S]
    (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0) :
    ∃ (κ : Type u) (c : κ → ℝ) (e : HilbertBasis κ ℝ (meanZeroL2 μ)),
      Countable κ ∧ ∀ j, integralOperatorOnMeanZero h hh hs hc (e j) = c j • e j := by
  letI : TopologicalSpace.SeparableSpace (Lp ℝ 2 μ) := separable_L2
  obtain ⟨κ,c,e,he⟩ :=
    Spectral.exists_hilbertBasis_hasEigenvector_of_isCompactOperator_of_isSelfAdjoint
      (integralOperatorOnMeanZero h hh hs hc)
      ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr
        (integralOperatorOnMeanZero_isSymmetric h hh hs hc))
      (integralOperatorOnMeanZero_isCompact h hh hs hc)
  exact ⟨κ,c,e,countable_of_separable_index e,fun j => (he j).apply_eq_smul⟩

theorem exists_full_meanZero_nonzero_label_equiv {ι κ : Type*}
    (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0)
    (a : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (hb : ∀ i, integralOperator h hh (b i) = a i • b i)
    (c : κ → ℝ) (e : HilbertBasis κ ℝ (meanZeroL2 μ))
    (he : ∀ j, integralOperatorOnMeanZero h hh hs hc (e j) = c j • e j) :
    ∃ f : {i // a i ≠ 0} ≃ {j // c j ≠ 0}, ∀ i : {i // a i ≠ 0}, a i.val = c (f i).val := by
  have hf : ∀ r, r ≠ 0 → FiniteDimensional ℝ
      (Module.End.eigenspace (integralOperator h hh).toLinearMap r) :=
    fun r hr => (integralOperator h hh).finite_dimensional_eigenspace
      (integralOperator_isCompact h hh) r hr
  have hg : ∀ r, r ≠ 0 → FiniteDimensional ℝ
      (Module.End.eigenspace (integralOperatorOnMeanZero h hh hs hc).toLinearMap r) := by
    intro r hr
    letI := hf r hr
    let E := nonzeroMeanZeroEigenspaceEquiv h hh hs hc r hr
    exact FiniteDimensional.of_injective E.symm.toLinearMap E.symm.injective
  exact exists_nonzeroSpectralLabelEquiv (integralOperator h hh).toLinearMap
    (integralOperator_isSymmetric h hh hs)
    (integralOperatorOnMeanZero h hh hs hc).toLinearMap
    (integralOperatorOnMeanZero_isSymmetric h hh hs hc)
    a b hb c e he hf hg (fun r hr => (nonzeroMeanZeroEigenspaceEquiv h hh hs hc r hr).finrank_eq)

theorem regularizedDet_full_eq_meanZero {ι κ : Type*}
    (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0)
    (a : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (hb : ∀ i, integralOperator h hh (b i) = a i • b i)
    (c : κ → ℝ) (e : HilbertBasis κ ℝ (meanZeroL2 μ))
    (he : ∀ j, integralOperatorOnMeanZero h hh hs hc (e j) = c j • e j)
    (β : ℝ) (hm : ∀ i, 0 < 1+β*a i) :
    HasProd (fun j => (1+β*c j)*Real.exp (-(β*c j))) (regularizedDet (fun i => β*a i)) ∧
      regularizedDet (fun i => β*a i) = regularizedDet (fun j => β*c j) ∧
      0 < regularizedDet (fun j => β*c j) := by
  have hsquare := summable_scaled_eigenvalue_sq
    a (summable_integralOperator_eigenvalue_sq h hh a b hb) β
  have hp := hasProd_regularizedDet hsquare hm
  rw [←regularizedDet_eq_exp hsquare hm] at hp
  obtain ⟨f,hf⟩ := exists_full_meanZero_nonzero_label_equiv h hh hs hc a b hb c e he
  have hp' := (hasProd_regularizedFactors_iff_nonzero_equiv a c β _ f hf).mp hp
  have heq : regularizedDet (fun i => β*a i) = regularizedDet (fun j => β*c j) :=
    hp'.tprod_eq.symm
  refine ⟨hp',heq,?_⟩
  rw [←heq]
  exact regularizedDet_pos hsquare hm
end DGRHS.Kernel
#print axioms DGRHS.Kernel.nonzeroMeanZeroEigenspaceEquiv
#print axioms DGRHS.Kernel.integralOperatorOnMeanZero_isSymmetric
#print axioms DGRHS.Kernel.integralOperatorOnMeanZero_isCompact
#print axioms DGRHS.Kernel.exists_integralOperatorOnMeanZero_eigenbasis
#print axioms DGRHS.Kernel.exists_full_meanZero_nonzero_label_equiv
#print axioms DGRHS.Kernel.regularizedDet_full_eq_meanZero
#check @DGRHS.Kernel.regularizedDet_full_eq_meanZero
