import DGRHS.Commutator.SourceRieszForceSymmetry
import DGRHS.Commutator.SourceRieszLocalEmpirical
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! Actual physical force sum and its literal empirical offcollision drift.
Collision force is zero even repeated spatial coordinates; finite atomic
integrability does not require a bounded force or favorable pair hypothesis. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal RealInnerProductSpace
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma measurable_sourceRieszForce (s : ℝ) : Measurable (sourceRieszForce s : E→E) := by
  exact ((continuous_norm.measurable.pow_const (-s-2)).neg).smul measurable_id

lemma sourceRieszForce_eq_gradient (s : ℝ) (hs : 0<s) {z : E} (hz : z≠0) :
    sourceRieszForce s z=gradient (sourceRieszPotential s) z := by
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [gradient,(InnerProductSpace.toDual ℝ E).apply_symm_apply]
  ext w
  exact sourceRieszForce_fderiv s hs hz w

lemma sourceRiesz_force_offDiagonalSum (s : ℝ) (N : ℕ) (x : Fin N→E) (v : E→E) :
    DGRHS.CanonicalVariance.offDiagonalSum
      (fun p : E×E=>⟪sourceRieszForce s (p.1-p.2),v p.1⟫) x=
      ∑ i : Fin N,∑ j : Fin N,⟪sourceRieszForce s (x i-x j),v (x i)⟫ := by
  classical
  let h := fun p : E×E=>⟪sourceRieszForce s (p.1-p.2),v p.1⟫
  unfold DGRHS.CanonicalVariance.offDiagonalSum
  have hp := Finset.sum_union (f:=fun p : Fin N×Fin N=>h (x p.1,x p.2))
    (Finset.disjoint_diag_offDiag (Finset.univ : Finset (Fin N)))
  rw [Finset.diag_union_offDiag,Finset.sum_product] at hp
  have hz : (∑ p ∈ (Finset.univ : Finset (Fin N)).diag,h (x p.1,x p.2))=0 := by
    simp [Finset.diag,h,sourceRieszForce_zero]
  rw [hz,zero_add] at hp
  exact hp.symm

theorem sourceRiesz_dynamic_drift_empirical (s : ℝ) (hs : 0<s)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (N : ℕ) (x : Fin N→E) :
    Integrable (sourceRieszTransportKernel 1 s v)
      ((sourceRieszLocalEmpiricalLaw N x).prod (sourceRieszLocalEmpiricalLaw N x)) ∧
    ((N:ℝ)^2)⁻¹*DGRHS.CanonicalVariance.offDiagonalSum
      (fun p : E×E=>⟪sourceRieszForce s (p.1-p.2),v p.1⟫) x=
      (1/2:ℝ)*(∫ p in {p : E×E|p.1≠p.2},sourceRieszTransportKernel 1 s v p
        ∂(sourceRieszLocalEmpiricalLaw N x).prod (sourceRieszLocalEmpiricalLaw N x)) := by
  obtain ⟨hi,he⟩ := sourceRieszLocalEmpirical_square (sourceRieszTransportKernel 1 s v)
    (measurable_sourceRieszTransportKernel s 1 hv) N x
  refine ⟨hi,?_⟩
  rw [sourceRieszLocalTransport_restrict_offCollision,he,
    sourceRiesz_dynamic_force_symmetrization s hs,sourceRiesz_force_offDiagonalSum]
  ring

end DGRHS.Commutator
#check @DGRHS.Commutator.measurable_sourceRieszForce
#print axioms DGRHS.Commutator.measurable_sourceRieszForce
#check @DGRHS.Commutator.sourceRieszForce_eq_gradient
#print axioms DGRHS.Commutator.sourceRieszForce_eq_gradient
#check @DGRHS.Commutator.sourceRiesz_force_offDiagonalSum
#print axioms DGRHS.Commutator.sourceRiesz_force_offDiagonalSum
#check @DGRHS.Commutator.sourceRiesz_dynamic_drift_empirical
#print axioms DGRHS.Commutator.sourceRiesz_dynamic_drift_empirical
