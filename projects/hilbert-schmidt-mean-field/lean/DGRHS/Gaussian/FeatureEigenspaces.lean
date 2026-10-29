/- Nonzero eigenspace correspondence for the actual feature covariance and
Gram integral operator. This is constructed from the actual adjoint factors. -/
import DGRHS.Gaussian.FeatureSpectral
import Mathlib.LinearAlgebra.Eigenspace.Basic
open MeasureTheory
namespace DGRHS.Gaussian

/-- The AB/BA eigenspaces at a nonzero eigenvalue are linearly equivalent. -/
noncomputable def nonzero_comp_eigenspace_equiv {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (A : E →ₗ[ℝ] F) (B : F →ₗ[ℝ] E) (r : ℝ) (hr : r ≠ 0) :
    Module.End.eigenspace (B.comp A) r ≃ₗ[ℝ] Module.End.eigenspace (A.comp B) r where
  toFun x := ⟨A x, by
    rw [Module.End.mem_eigenspace_iff]
    have h := congrArg A (Module.End.mem_eigenspace_iff.mp x.property)
    simpa only [LinearMap.comp_apply, map_smul] using h⟩
  invFun y := ⟨r⁻¹ • B y, by
    rw [Module.End.mem_eigenspace_iff]
    have h := congrArg B (Module.End.mem_eigenspace_iff.mp y.property)
    have hB : (B.comp A) (B y) = r • B y := by
      simpa only [LinearMap.comp_apply, map_smul] using h
    rw [map_smul, hB]
    simp only [smul_smul, mul_comm r⁻¹ r]⟩
  left_inv x := by
    apply Subtype.ext
    change r⁻¹ • B (A x) = x
    rw [← LinearMap.comp_apply, Module.End.mem_eigenspace_iff.mp x.property,
      smul_smul, inv_mul_cancel₀ hr, one_smul]
  right_inv y := by
    apply Subtype.ext
    change A (r⁻¹ • B y) = y
    rw [map_smul, ← LinearMap.comp_apply, Module.End.mem_eigenspace_iff.mp y.property,
      smul_smul, inv_mul_cancel₀ hr, one_smul]
  map_add' x y := by
    apply Subtype.ext
    exact A.map_add x y
  map_smul' c x := by
    apply Subtype.ext
    exact A.map_smul c x

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- Actual nonzero eigenspaces of T and Σ correspond via synthesis and scaled readout. -/
noncomputable def featureNonzeroEigenspaceEquiv (k : X → H)
    (hk : StronglyMeasurable k) (hk2 : MemLp k 2 μ) (r : ℝ) (hr : r ≠ 0) :
    Module.End.eigenspace (DGRHS.Kernel.integralOperator (featureKernel k)
      (memLp_featureKernel k hk hk2)).toLinearMap r ≃ₗ[ℝ]
      Module.End.eigenspace (featureCovariance k hk2).toLinearMap r := by
  rw [integralOperator_featureKernel_eq k hk hk2]
  exact nonzero_comp_eigenspace_equiv (featureSynthesis k hk2).toLinearMap
    (featureReadout k hk2).toLinearMap r hr

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.nonzero_comp_eigenspace_equiv
#print axioms DGRHS.Gaussian.featureNonzeroEigenspaceEquiv
#check DGRHS.Gaussian.featureNonzeroEigenspaceEquiv
