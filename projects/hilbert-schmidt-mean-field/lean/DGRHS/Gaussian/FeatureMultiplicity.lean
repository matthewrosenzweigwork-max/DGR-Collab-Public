/- UNCHECKED draft outside frozen proof. Actual nonzero algebraic
multiplicity equality, using generalized=ordinary for symmetric maps.
No finite-dimensional hypothesis is imposed on the ambient L2 or H. -/
import DGRHS.Gaussian.FeatureEigenspaces
import DGRHS.Gaussian.FeatureCovarianceCompact
import DGRHS.Kernel.SymmetricMultiplicity
import DGRHS.Kernel.RegularizedDeterminantNonzero
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
noncomputable section
open MeasureTheory
namespace DGRHS.Gaussian
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

theorem finiteDimensional_featureCovariance_eigenspace (k : X → H)
    (hk : StronglyMeasurable k) (hk2 : MemLp k 2 μ) (r : ℝ) (hr : r ≠ 0) :
    FiniteDimensional ℝ (Module.End.eigenspace (featureCovariance k hk2).toLinearMap r) := by
  exact (featureCovariance k hk2).finite_dimensional_eigenspace
    (featureCovariance_isCompactOperator k hk2) r hr

theorem finrank_feature_nonzero_eigenspaces (k : X → H)
    (hk : StronglyMeasurable k) (hk2 : MemLp k 2 μ) (r : ℝ) (hr : r ≠ 0) :
    Module.finrank ℝ (Module.End.eigenspace
      (DGRHS.Kernel.integralOperator (featureKernel k) (memLp_featureKernel k hk hk2)).toLinearMap r) =
    Module.finrank ℝ (Module.End.eigenspace (featureCovariance k hk2).toLinearMap r) :=
  (featureNonzeroEigenspaceEquiv k hk hk2 r hr).finrank_eq

/-- Algebraic multiplicity here is the dimension of the actual maximal
generalized eigenspace. Symmetry identifies it with the ordinary eigenspace;
nonzero compact eigenspaces are finite by the preceding actual construction. -/
theorem finrank_feature_nonzero_maxGenEigenspaces (k : X → H)
    (hk : StronglyMeasurable k) (hk2 : MemLp k 2 μ) (r : ℝ) (hr : r ≠ 0) :
    Module.finrank ℝ (Module.End.maxGenEigenspace
      (DGRHS.Kernel.integralOperator (featureKernel k) (memLp_featureKernel k hk hk2)).toLinearMap r) =
    Module.finrank ℝ (Module.End.maxGenEigenspace (featureCovariance k hk2).toLinearMap r) := by
  have hT := DGRHS.Kernel.integralOperator_isSymmetric (featureKernel k)
    (memLp_featureKernel k hk hk2) (Filter.Eventually.of_forall (featureKernel_symmetric k))
  rw [DGRHS.Kernel.symmetric_maxGenEigenspace_eq _ hT,
    DGRHS.Kernel.symmetric_maxGenEigenspace_eq _ (featureCovariance_isSymmetric k hk2)]
  exact finrank_feature_nonzero_eigenspaces k hk hk2 r hr

end DGRHS.Gaussian
namespace DGRHS.Kernel
variable {ι κ : Type*}

/-- Genuine product convergence transports through the nonzero label
equivalence. Zero eigenvalues contribute unit factors even when β=0. -/
theorem hasProd_regularizedFactors_iff_nonzero_equiv
    (a : ι → ℝ) (b : κ → ℝ) (β d : ℝ)
    (e : {i // a i ≠ 0} ≃ {j // b j ≠ 0}) (he : ∀ i : {i // a i ≠ 0}, a i = b (e i)) :
    HasProd (fun i => (1 + β * a i) * Real.exp (-(β * a i))) d ↔
      HasProd (fun j => (1 + β * b j) * Real.exp (-(β * b j))) d := by
  have hsa : Function.mulSupport (fun i => (1 + β * a i) * Real.exp (-(β * a i))) ⊆
      {i | a i ≠ 0} := by
    intro i hi hz
    exact hi (by simp [hz])
  have hsb : Function.mulSupport (fun j => (1 + β * b j) * Real.exp (-(β * b j))) ⊆
      {j | b j ≠ 0} := by
    intro j hj hz
    exact hj (by simp [hz])
  rw [← hasProd_subtype_iff_of_mulSupport_subset hsa,
    ← hasProd_subtype_iff_of_mulSupport_subset hsb]
  have hh : (fun i : {i // a i ≠ 0} => (1 + β * a i) * Real.exp (-(β * a i))) =
      (fun j : {j // b j ≠ 0} => (1 + β * b j) * Real.exp (-(β * b j))) ∘ e := by
    funext i
    simp only [Function.comp_apply, he]
  change HasProd (fun i : {i // a i ≠ 0} => (1 + β * a i) * Real.exp (-(β * a i))) d ↔
    HasProd (fun j : {j // b j ≠ 0} => (1 + β * b j) * Real.exp (-(β * b j))) d
  rw [hh, e.hasProd_iff]

/-- An existing genuine determinant limit for one enumeration supplies the
same limit for the other; totalized tprod equality alone is not the premise. -/
theorem regularizedDet_eq_of_hasProd_nonzero_equiv
    (a : ι → ℝ) (b : κ → ℝ) (β d : ℝ)
    (e : {i // a i ≠ 0} ≃ {j // b j ≠ 0}) (he : ∀ i : {i // a i ≠ 0}, a i = b (e i))
    (ha : HasProd (fun i => (1 + β * a i) * Real.exp (-(β * a i))) d) :
    regularizedDet (fun i => β * a i) = d ∧ regularizedDet (fun j => β * b j) = d := by
  exact ⟨ha.tprod_eq,
    ((hasProd_regularizedFactors_iff_nonzero_equiv a b β d e he).mp ha).tprod_eq⟩

/-- Exact reindexing preserves the genuine regularized product. The
nonzero-index equivalence must be constructed from actual multiplicities. -/
theorem regularizedDet_congr_nonzero_equiv (a : ι → ℝ) (b : κ → ℝ) (β : ℝ)
    (e : {i // a i ≠ 0} ≃ {j // b j ≠ 0}) (he : ∀ i : {i // a i ≠ 0}, a i = b (e i)) :
    regularizedDet (fun i => β * a i) = regularizedDet (fun j => β * b j) := by
  rw [regularizedDet_restrict_nonzero a β, regularizedDet_restrict_nonzero b β]
  unfold regularizedDet
  simpa only [he] using e.tprod_eq
    (fun j : {i // b i ≠ 0} => (1 + β * b j) * Real.exp (-(β * b j)))
end DGRHS.Kernel
#print axioms DGRHS.Gaussian.finiteDimensional_featureCovariance_eigenspace
#print axioms DGRHS.Gaussian.finrank_feature_nonzero_eigenspaces
#print axioms DGRHS.Gaussian.finrank_feature_nonzero_maxGenEigenspaces
#print axioms DGRHS.Kernel.hasProd_regularizedFactors_iff_nonzero_equiv
#print axioms DGRHS.Kernel.regularizedDet_eq_of_hasProd_nonzero_equiv
#print axioms DGRHS.Kernel.regularizedDet_congr_nonzero_equiv
