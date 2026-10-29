/- UNCHECKED outside the frozen proof tree. Nonzero spectral labels are
constructed from full Hilbert bases and actual finite eigenspace dimensions.
Zero eigenspaces need not have matching dimensions. -/
import DGRHS.Kernel.SymmetricMultiplicity
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic
noncomputable section
open scoped InnerProductSpace
namespace DGRHS.Kernel
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

def spectralFiberVector (T : H →ₗ[ℝ] H) (a : ι → ℝ) (b : HilbertBasis ι ℝ H)
    (hb : ∀ i, T (b i) = a i • b i) (r : ℝ) (i : {i // a i = r}) :
    Module.End.eigenspace T r :=
  ⟨b i.val, Module.End.mem_eigenspace_iff.mpr (by rw [hb, i.property])⟩

lemma spectralFiberVector_orthonormal (T : H →ₗ[ℝ] H) (a : ι → ℝ)
    (b : HilbertBasis ι ℝ H) (hb : ∀ i, T (b i) = a i • b i) (r : ℝ) :
    Orthonormal ℝ (spectralFiberVector T a b hb r) := by
  classical
  have h := b.orthonormal.comp (Subtype.val : {i // a i = r} → ι) Subtype.val_injective
  rw [orthonormal_iff_ite] at h ⊢
  intro i j
  change inner ℝ (b i.val) (b j.val) = if i = j then 1 else 0
  exact h i j

lemma finite_spectralFiber (T : H →ₗ[ℝ] H) (a : ι → ℝ)
    (b : HilbertBasis ι ℝ H) (hb : ∀ i, T (b i) = a i • b i) (r : ℝ)
    [FiniteDimensional ℝ (Module.End.eigenspace T r)] : Finite {i // a i = r} :=
  (spectralFiberVector_orthonormal T a b hb r).linearIndependent.finite

lemma spectralFiber_span_orthogonal_eq_bot (T : H →ₗ[ℝ] H) (hT : T.IsSymmetric)
    (a : ι → ℝ) (b : HilbertBasis ι ℝ H) (hb : ∀ i, T (b i) = a i • b i)
    (r : ℝ) :
    (Submodule.span ℝ (Set.range (spectralFiberVector T a b hb r)))ᗮ = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hzero : (x : H) = 0 := by
      apply b.repr.injective
      ext j
      rw [map_zero, b.repr_apply_apply]
      change inner ℝ (b j) (x : H) = 0
      by_cases hj : a j = r
      · exact (Submodule.mem_orthogonal _ _).mp hx
          (spectralFiberVector T a b hb r ⟨j, hj⟩)
          (Submodule.subset_span (Set.mem_range_self _))
      · have he := hT (b j) (x : H)
        rw [hb, Module.End.mem_eigenspace_iff.mp x.property,
          inner_smul_left, inner_smul_right] at he
        have he' : a j * inner ℝ (b j) (x : H) = r * inner ℝ (b j) (x : H) := by
          simpa only [conj_trivial] using he
        have hd : (a j - r) * inner ℝ (b j) (x : H) = 0 := by
          rw [sub_mul, he', sub_self]
        exact (mul_eq_zero.mp hd).resolve_left (sub_ne_zero.mpr hj)
    exact show x = 0 from Subtype.ext hzero
  · exact bot_le

lemma finrank_eq_card_spectralFiber (T : H →ₗ[ℝ] H) (hT : T.IsSymmetric)
    (a : ι → ℝ) (b : HilbertBasis ι ℝ H) (hb : ∀ i, T (b i) = a i • b i)
    (r : ℝ) [FiniteDimensional ℝ (Module.End.eigenspace T r)]
    [Fintype {i // a i = r}] :
    Module.finrank ℝ (Module.End.eigenspace T r) = Fintype.card {i // a i = r} := by
  let c := HilbertBasis.mkOfOrthogonalEqBot
    (spectralFiberVector_orthonormal T a b hb r)
    (spectralFiber_span_orthogonal_eq_bot T hT a b hb r)
  exact Module.finrank_eq_card_basis c.toOrthonormalBasis.toBasis

/-- Restricting to nonzero labels leaves every nonzero eigenvalue fiber intact. -/
def nonzeroFiberEquiv (a : ι → ℝ) (r : {r : ℝ // r ≠ 0}) :
    {i : {i // a i ≠ 0} // a i = r.val} ≃ {i // a i = r.val} where
  toFun i := ⟨i.val.val, i.property⟩
  invFun i := ⟨⟨i.val, by rw [i.property]; exact r.property⟩, i.property⟩
  left_inv i := by cases i; rfl
  right_inv i := by cases i; rfl

variable {F κ : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F]

/-- Construct the value-preserving bijection from actual finite nonzero
multiplicities. The ambient spaces may be infinite dimensional. -/
theorem exists_nonzeroSpectralLabelEquiv
    (T : H →ₗ[ℝ] H) (hT : T.IsSymmetric)
    (S : F →ₗ[ℝ] F) (hS : S.IsSymmetric)
    (a : ι → ℝ) (b : HilbertBasis ι ℝ H) (hb : ∀ i, T (b i) = a i • b i)
    (c : κ → ℝ) (d : HilbertBasis κ ℝ F) (hd : ∀ j, S (d j) = c j • d j)
    (hTf : ∀ r, r ≠ 0 → FiniteDimensional ℝ (Module.End.eigenspace T r))
    (hSf : ∀ r, r ≠ 0 → FiniteDimensional ℝ (Module.End.eigenspace S r))
    (hm : ∀ r, r ≠ 0 → Module.finrank ℝ (Module.End.eigenspace T r) =
      Module.finrank ℝ (Module.End.eigenspace S r)) :
    ∃ e : {i // a i ≠ 0} ≃ {j // c j ≠ 0}, ∀ i : {i // a i ≠ 0}, a i.val = c (e i).val := by
  classical
  let av : {i // a i ≠ 0} → {r : ℝ // r ≠ 0} := fun i => ⟨a i, i.property⟩
  let cv : {j // c j ≠ 0} → {r : ℝ // r ≠ 0} := fun j => ⟨c j, j.property⟩
  have ef : ∀ r, {i // av i = r} ≃ {j // cv j = r} := by
    intro r
    letI := hTf r.val r.property
    letI := hSf r.val r.property
    letI := finite_spectralFiber T a b hb r.val
    letI := finite_spectralFiber S c d hd r.val
    letI := Fintype.ofFinite {i // a i = r.val}
    letI := Fintype.ofFinite {j // c j = r.val}
    let ea : {i // av i = r} ≃ {i // a i = r.val} :=
      (Equiv.subtypeEquivRight (fun i => Subtype.ext_iff)).trans (nonzeroFiberEquiv a r)
    let ec : {j // cv j = r} ≃ {j // c j = r.val} :=
      (Equiv.subtypeEquivRight (fun j => Subtype.ext_iff)).trans (nonzeroFiberEquiv c r)
    have hcard : Fintype.card {i // a i = r.val} = Fintype.card {j // c j = r.val} := by
      rw [← finrank_eq_card_spectralFiber T hT a b hb r.val,
        ← finrank_eq_card_spectralFiber S hS c d hd r.val]
      exact hm r.val r.property
    exact ea.trans ((Fintype.equivOfCardEq hcard).trans ec.symm)
  refine ⟨Equiv.ofFiberEquiv ef, ?_⟩
  intro i
  exact (congrArg Subtype.val (Equiv.ofFiberEquiv_map ef i)).symm


end DGRHS.Kernel
#print axioms DGRHS.Kernel.finite_spectralFiber
#print axioms DGRHS.Kernel.finrank_eq_card_spectralFiber
#print axioms DGRHS.Kernel.exists_nonzeroSpectralLabelEquiv
