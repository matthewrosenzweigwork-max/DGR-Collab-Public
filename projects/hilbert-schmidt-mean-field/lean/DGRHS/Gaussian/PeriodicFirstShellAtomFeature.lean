import DGRHS.Gaussian.PeriodicFirstShellResidual
import DGRHS.Gaussian.SharpnessFiniteGram

/-! Concrete actual first-shell atom averages and residual matrix-root vectors.
Their Gram sum is exactly the full original logarithmic compression. No
favorable covariance decomposition or projected feature is supplied. -/
noncomputable section
open MeasureTheory Set Matrix
open scoped Classical BigOperators InnerProductSpace
namespace DGRHS.Periodic
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicFirstShellMode_integrable (q : ι × Bool) :
    Integrable (periodicFirstShellMode q) (periodicHaar ι) :=
  (periodicFirstShellMode_continuous q).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

def periodicFirstShellAtomMode (A : Set (PeriodicTorus ι)) (q : ι × Bool) : ℝ :=
  (∫ x in A,periodicFirstShellMode q x ∂periodicHaar ι)/((periodicHaar ι) A).toReal

lemma periodicFirstShell_atom_integral (A B : Set (PeriodicTorus ι)) :
    sharpnessAtomIntegral (periodicHaar ι) (fun p => periodicFirstShellKernel p.1 p.2) A B =
      (2*(periodicStabilityThreshold ι)⁻¹)*∑ q : ι × Bool,
        (∫ x in A,periodicFirstShellMode q x ∂periodicHaar ι)*
        (∫ y in B,periodicFirstShellMode q y ∂periodicHaar ι) := by
  unfold sharpnessAtomIntegral periodicFirstShellKernel
  rw [integral_const_mul,integral_finsetSum _
    (fun q _ => (periodicFirstShellMode_integrable q).restrict.mul_prod
      (periodicFirstShellMode_integrable q).restrict)]
  simp_rw [integral_prod_mul]

lemma periodicFirstShell_atom_average (A B : Set (PeriodicTorus ι)) :
    sharpnessAtomAverage (periodicHaar ι) (fun p => periodicFirstShellKernel p.1 p.2) A B =
      (2*(periodicStabilityThreshold ι)⁻¹)*∑ q : ι × Bool,
        periodicFirstShellAtomMode A q*periodicFirstShellAtomMode B q := by
  unfold sharpnessAtomAverage
  rw [periodicFirstShell_atom_integral]
  unfold periodicFirstShellAtomMode
  simp only [div_eq_mul_inv,_root_.mul_inv_rev,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

lemma periodicFirstShell_residual_atom_average (A B : Set (PeriodicTorus ι)) :
    sharpnessAtomAverage (periodicHaar ι) periodicFirstShellResidualPair A B =
      sharpnessAtomAverage (periodicHaar ι) (fun p => periodicLogKernel (p.1-p.2)) A B-
      sharpnessAtomAverage (periodicHaar ι) (fun p => periodicFirstShellKernel p.1 p.2) A B := by
  have hiG : Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (p.1-p.2))
      (((periodicHaar ι).restrict A).prod ((periodicHaar ι).restrict B)) := by
    rw [Measure.prod_restrict]
    exact periodicLogPair_integrable.restrict
  have hiS : Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicFirstShellKernel p.1 p.2)
      (((periodicHaar ι).restrict A).prod ((periodicHaar ι).restrict B)) := by
    rw [Measure.prod_restrict]
    exact periodicFirstShellPair_integrable.restrict
  unfold sharpnessAtomAverage sharpnessAtomIntegral periodicFirstShellResidualPair
  rw [integral_sub hiG hiS]
  ring

def periodicFirstShellAtomFeature (A : Set (PeriodicTorus ι)) : EuclideanSpace ℝ (ι × Bool) :=
  WithLp.toLp 2 (fun q => Real.sqrt (2*(periodicStabilityThreshold ι)⁻¹)*periodicFirstShellAtomMode A q)

lemma inner_periodicFirstShellAtomFeature (A B : Set (PeriodicTorus ι)) :
    inner ℝ (periodicFirstShellAtomFeature A) (periodicFirstShellAtomFeature B) =
      sharpnessAtomAverage (periodicHaar ι) (fun p => periodicFirstShellKernel p.1 p.2) A B := by
  unfold periodicFirstShellAtomFeature
  rw [EuclideanSpace.inner_toLp_toLp,periodicFirstShell_atom_average]
  simp only [star_trivial,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  have hc : 0 ≤ 2*(periodicStabilityThreshold ι)⁻¹ := by
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr periodicStabilityThreshold_pos.le)
  calc
    _ = Real.sqrt (2*(periodicStabilityThreshold ι)⁻¹)^2*
        (periodicFirstShellAtomMode A q*periodicFirstShellAtomMode B q) := by ring
    _ = _ := by rw [Real.sq_sqrt hc]

def periodicFirstShellResidualAtomFeature {α : Type*} [Fintype α] [DecidableEq α]
    (A : α → Set (PeriodicTorus ι)) (i : α) : EuclideanSpace ℝ α :=
  sharpnessMatrixFeature (fun a b => sharpnessAtomAverage (periodicHaar ι)
    periodicFirstShellResidualPair (A a) (A b)) i

lemma inner_periodicFirstShellResidualAtomFeature {α : Type*} [Fintype α] [DecidableEq α]
    (A : α → Set (PeriodicTorus ι)) (hA : ∀ i,MeasurableSet (A i)) (i j : α) :
    inner ℝ (periodicFirstShellResidualAtomFeature A i) (periodicFirstShellResidualAtomFeature A j) =
      sharpnessAtomAverage (periodicHaar ι) periodicFirstShellResidualPair (A i) (A j) :=
  inner_sharpnessMatrixFeature _ (periodicFirstShellResidual_average_matrix_posSemidef A hA) i j

/-- Exact source compressed covariance decomposition, constructed for every
actual measurable finite atom family, including all null atoms. -/
theorem periodicLog_atom_average_firstShell_residual_gram {α : Type*} [Fintype α] [DecidableEq α]
    (A : α → Set (PeriodicTorus ι)) (hA : ∀ i,MeasurableSet (A i)) (i j : α) :
    sharpnessAtomAverage (periodicHaar ι) (fun p => periodicLogKernel (p.1-p.2)) (A i) (A j) =
      inner ℝ (periodicFirstShellAtomFeature (A i)) (periodicFirstShellAtomFeature (A j))+
      inner ℝ (periodicFirstShellResidualAtomFeature A i) (periodicFirstShellResidualAtomFeature A j) := by
  rw [inner_periodicFirstShellAtomFeature,inner_periodicFirstShellResidualAtomFeature A hA,
    periodicFirstShell_residual_atom_average]
  ring

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicFirstShellMode_integrable
#print axioms DGRHS.Periodic.periodicFirstShell_atom_integral
#print axioms DGRHS.Periodic.periodicFirstShell_atom_average
#print axioms DGRHS.Periodic.periodicFirstShell_residual_atom_average
#print axioms DGRHS.Periodic.inner_periodicFirstShellAtomFeature
#print axioms DGRHS.Periodic.inner_periodicFirstShellResidualAtomFeature
#print axioms DGRHS.Periodic.periodicLog_atom_average_firstShell_residual_gram
#check @DGRHS.Periodic.periodicLog_atom_average_firstShell_residual_gram
