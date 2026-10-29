import DGRHS.Commutator.SourceBoundedC2Fourier
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-! UNCOMPILED spatial regularity adapters. The native derivative-norm Cb2
class is equivalent to the literal value/gradient/Hessian bounds of the
source. The native Laplacian is a finite trace, hence inherits both its
uniform bound and joint continuity from the actual Hessian. -/
noncomputable section
open MeasureTheory Laplacian
open scoped BigOperators
namespace DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sourceBoundedC2Test_iff_classical_bounds (φ : E→ℝ) :
    SourceBoundedC2Test φ ↔ ContDiff ℝ 2 φ ∧ ∃ C:ℝ, 0≤C ∧ ∀ x,
      |φ x|≤C ∧ ‖gradient φ x‖≤C ∧ ‖iteratedFDeriv ℝ 2 φ x‖≤C := by
  have hG (x : E) : ‖gradient φ x‖=‖iteratedFDeriv ℝ 1 φ x‖ := by
    simpa only [gradient, norm_iteratedFDeriv_one] using
      (InnerProductSpace.toDual ℝ E).symm.norm_map (fderiv ℝ φ x)
  constructor
  · rintro ⟨hc,C,hC,hb⟩
    refine ⟨hc,C,hC,fun x => ⟨?_,?_,hb 2 le_rfl x⟩⟩
    · simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hb 0 (by omega) x
    · rw [hG]
      exact hb 1 (by omega) x
  · rintro ⟨hc,C,hC,hb⟩
    refine ⟨hc,C,hC,?_⟩
    intro n hn x
    interval_cases n
    · simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using (hb x).1
    · rw [← hG]
      exact (hb x).2.1
    · exact (hb x).2.2

lemma source_laplacian_bound_of_hessian
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (φ : E→ℝ) (C : ℝ) (hC : ∀ x, ‖iteratedFDeriv ℝ 2 φ x‖≤C) (x : E) :
    |laplacian φ x|≤(Fintype.card ι:ℝ)*C := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ b]
  change |∑ i, iteratedFDeriv ℝ 2 φ x ![b i,b i]|≤_
  calc
    _ ≤ ∑ i, |iteratedFDeriv ℝ 2 φ x ![b i,b i]| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i:ι, C := Finset.sum_le_sum (fun i _ => by
      have hi := (iteratedFDeriv ℝ 2 φ x).le_opNorm ![b i,b i]
      have hi' : |iteratedFDeriv ℝ 2 φ x ![b i,b i]|≤‖iteratedFDeriv ℝ 2 φ x‖ := by
        simpa [Real.norm_eq_abs, Fin.prod_univ_two, b.norm_eq_one] using hi
      exact hi'.trans (hC x))
    _ = _ := by simp

lemma continuous_laplacian_of_joint_hessian
    {P ι : Type*} [TopologicalSpace P] [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (q : P→E→ℝ)
    (hH : Continuous (fun p:P×E => iteratedFDeriv ℝ 2 (q p.1) p.2)) :
    Continuous (fun p:P×E => laplacian (q p.1) p.2) := by
  have he (p : P×E) : laplacian (q p.1) p.2 =
      ∑ i, iteratedFDeriv ℝ 2 (q p.1) p.2 ![b i,b i] :=
    congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (q p.1) b) p.2
  simp_rw [he]
  apply continuous_finset_sum
  intro i hi
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ ![b i,b i]).continuous.comp hH

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.sourceBoundedC2Test_iff_classical_bounds
#print axioms DGRHS.Commutator.sourceBoundedC2Test_iff_classical_bounds
#check @DGRHS.Commutator.source_laplacian_bound_of_hessian
#print axioms DGRHS.Commutator.source_laplacian_bound_of_hessian
#check @DGRHS.Commutator.continuous_laplacian_of_joint_hessian
#print axioms DGRHS.Commutator.continuous_laplacian_of_joint_hessian
