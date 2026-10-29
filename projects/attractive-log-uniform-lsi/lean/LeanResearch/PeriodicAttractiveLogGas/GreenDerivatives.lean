import LeanResearch.PeriodicAttractiveLogGas.GreenRepresentative
import LeanResearch.PeriodicAttractiveLogGas.TorusDistance
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! Ordinary differential, Euclidean gradient and Hessian of the regular Green
representative on the square torus.

The fields are defined using the centered Euclidean lift. Exact translation
identities for ordinary Fréchet derivatives prove independence of the lift.
Continuity is asserted off the torus origin, where the actual regular lift is
smooth. Values at the origin use Mathlib's totalized derivative conventions;
no differentiability at the pole is asserted. The real Riesz isometry introduces
no scaling factor in either the gradient or the Hessian operator norm.
-/

noncomputable section

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff RealInnerProductSpace

namespace PeriodicAttractiveLogGas

theorem contDiffOn_fderiv_regularGreenLift :
    ContDiffOn ℝ ∞ (fderiv ℝ regularGreenLift) offIntegerLattice :=
  contDiffOn_regularGreenLift.fderiv_of_isOpen isOpen_offIntegerLattice (by simp)

theorem contDiffOn_hessian_regularGreenLift :
    ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ regularGreenLift)) offIntegerLattice :=
  contDiffOn_fderiv_regularGreenLift.fderiv_of_isOpen isOpen_offIntegerLattice (by simp)

theorem regularGreenLift_eventuallyEq_smoothGreenLift {x : PlanarSpace}
    (hx : x ∈ offIntegerLattice) : regularGreenLift =ᶠ[𝓝 x] smoothGreenLift := by
  filter_upwards [isOpen_offIntegerLattice.mem_nhds hx] with y hy
  exact regularGreenLift_of_mem hy

theorem fderiv_regularGreenLift_eq_smoothGreenLift {x : PlanarSpace}
    (hx : x ∈ offIntegerLattice) :
    fderiv ℝ regularGreenLift x = fderiv ℝ smoothGreenLift x :=
  (regularGreenLift_eventuallyEq_smoothGreenLift hx).fderiv_eq

theorem hessian_regularGreenLift_eq_smoothGreenLift {x : PlanarSpace}
    (hx : x ∈ offIntegerLattice) :
    fderiv ℝ (fderiv ℝ regularGreenLift) x = fderiv ℝ (fderiv ℝ smoothGreenLift) x :=
  (regularGreenLift_eventuallyEq_smoothGreenLift hx).fderiv.fderiv_eq

/-- Translation differentiates with factor one, including the totalized values
of the derivative at lattice points. -/
@[simp] theorem fderiv_regularGreenLift_add_frequencyVector (x : PlanarSpace) (k : Frequency) :
    fderiv ℝ regularGreenLift (x + frequencyVector k) = fderiv ℝ regularGreenLift x := by
  simpa only [regularGreenLift_add_frequencyVector] using
    (fderiv_comp_add_right (𝕜 := ℝ) (f := regularGreenLift) (x := x)
      (frequencyVector k)).symm

@[simp] theorem hessian_regularGreenLift_add_frequencyVector (x : PlanarSpace) (k : Frequency) :
    fderiv ℝ (fderiv ℝ regularGreenLift) (x + frequencyVector k) =
      fderiv ℝ (fderiv ℝ regularGreenLift) x := by
  simpa only [fderiv_regularGreenLift_add_frequencyVector] using
    (fderiv_comp_add_right (𝕜 := ℝ) (f := fderiv ℝ regularGreenLift) (x := x)
      (frequencyVector k)).symm

theorem fderiv_regularGreenLift_eq_of_torusQuotient_eq {x y : PlanarSpace}
    (hxy : torusQuotient x = torusQuotient y) :
    fderiv ℝ regularGreenLift x = fderiv ℝ regularGreenLift y := by
  obtain ⟨k, rfl⟩ := exists_frequencyVector_of_torusQuotient_eq hxy
  exact (fderiv_regularGreenLift_add_frequencyVector x k).symm

theorem hessian_regularGreenLift_eq_of_torusQuotient_eq {x y : PlanarSpace}
    (hxy : torusQuotient x = torusQuotient y) :
    fderiv ℝ (fderiv ℝ regularGreenLift) x = fderiv ℝ (fderiv ℝ regularGreenLift) y := by
  obtain ⟨k, rfl⟩ := exists_frequencyVector_of_torusQuotient_eq hxy
  exact (hessian_regularGreenLift_add_frequencyVector x k).symm

/-- The descended ordinary differential, as a real continuous linear functional. -/
def greenDifferential (z : Torus) : PlanarSpace →L[ℝ] ℝ :=
  fderiv ℝ regularGreenLift (centeredLift z)

/-- The descended ordinary Hessian, in curried bilinear form. -/
def greenHessian (z : Torus) : PlanarSpace →L[ℝ] PlanarSpace →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ regularGreenLift) (centeredLift z)

@[simp] theorem greenDifferential_lift (x : PlanarSpace) :
    greenDifferential (torusQuotient x) = fderiv ℝ regularGreenLift x :=
  fderiv_regularGreenLift_eq_of_torusQuotient_eq (torusQuotient_centeredLift _)

@[simp] theorem greenHessian_lift (x : PlanarSpace) :
    greenHessian (torusQuotient x) = fderiv ℝ (fderiv ℝ regularGreenLift) x :=
  hessian_regularGreenLift_eq_of_torusQuotient_eq (torusQuotient_centeredLift _)

theorem greenDifferential_of_lift {z : Torus} {x : PlanarSpace}
    (hx : torusQuotient x = z) : greenDifferential z = fderiv ℝ regularGreenLift x := by
  rw [← hx, greenDifferential_lift]

theorem greenHessian_of_lift {z : Torus} {x : PlanarSpace}
    (hx : torusQuotient x = z) :
    greenHessian z = fderiv ℝ (fderiv ℝ regularGreenLift) x := by
  rw [← hx, greenHessian_lift]

theorem greenDifferential_lift_of_mem {x : PlanarSpace} (hx : x ∈ offIntegerLattice) :
    greenDifferential (torusQuotient x) = fderiv ℝ smoothGreenLift x :=
  (greenDifferential_lift x).trans (fderiv_regularGreenLift_eq_smoothGreenLift hx)

theorem greenHessian_lift_of_mem {x : PlanarSpace} (hx : x ∈ offIntegerLattice) :
    greenHessian (torusQuotient x) = fderiv ℝ (fderiv ℝ smoothGreenLift) x :=
  (greenHessian_lift x).trans (hessian_regularGreenLift_eq_smoothGreenLift hx)

/-- Compatibility with the ordinary derivative of the actual torus representative's lift. -/
theorem greenDifferential_eq_fderiv_representative_lift (x : PlanarSpace) :
    greenDifferential (torusQuotient x) =
      fderiv ℝ (fun y : PlanarSpace ↦ regularGreenRepresentative (torusQuotient y)) x := by
  simp only [regularGreenRepresentative_lift, greenDifferential_lift]

theorem greenHessian_eq_hessian_representative_lift (x : PlanarSpace) :
    greenHessian (torusQuotient x) =
      fderiv ℝ (fderiv ℝ (fun y : PlanarSpace ↦
        regularGreenRepresentative (torusQuotient y))) x := by
  simp only [regularGreenRepresentative_lift, greenHessian_lift]

theorem continuousAt_greenDifferential {z : Torus} (hz : z ≠ 0) :
    ContinuousAt greenDifferential z := by
  obtain ⟨x, rfl⟩ := torusQuotient_surjective z
  apply isOpenQuotientMap_torusQuotient.continuousAt_comp_iff.mp
  have hx : x ∈ offIntegerLattice := hz
  have hc := contDiffOn_fderiv_regularGreenLift.continuousOn.continuousAt
    (isOpen_offIntegerLattice.mem_nhds hx)
  simpa only [Function.comp_def, greenDifferential_lift] using hc

theorem continuousAt_greenHessian {z : Torus} (hz : z ≠ 0) :
    ContinuousAt greenHessian z := by
  obtain ⟨x, rfl⟩ := torusQuotient_surjective z
  apply isOpenQuotientMap_torusQuotient.continuousAt_comp_iff.mp
  have hx : x ∈ offIntegerLattice := hz
  have hc := contDiffOn_hessian_regularGreenLift.continuousOn.continuousAt
    (isOpen_offIntegerLattice.mem_nhds hx)
  simpa only [Function.comp_def, greenHessian_lift] using hc

theorem continuousOn_greenDifferential : ContinuousOn greenDifferential ({0}ᶜ : Set Torus) := by
  intro z hz
  exact (continuousAt_greenDifferential (by simpa using hz)).continuousWithinAt

theorem continuousOn_greenHessian : ContinuousOn greenHessian ({0}ᶜ : Set Torus) := by
  intro z hz
  exact (continuousAt_greenHessian (by simpa using hz)).continuousWithinAt

theorem measurable_greenDifferential : Measurable greenDifferential :=
  measurable_of_continuousOn_compl_singleton 0 continuousOn_greenDifferential

theorem measurable_greenHessian : Measurable greenHessian :=
  measurable_of_continuousOn_compl_singleton 0 continuousOn_greenHessian

/-- The Euclidean gradient, using the real Riesz isometry with normalization one. -/
def greenGradient (z : Torus) : PlanarSpace :=
  (InnerProductSpace.toDual ℝ PlanarSpace).symm (greenDifferential z)

theorem greenGradient_inner (z : Torus) (v : PlanarSpace) :
    inner ℝ (greenGradient z) v = greenDifferential z v :=
  InnerProductSpace.toDual_symm_apply

theorem norm_greenGradient (z : Torus) : ‖greenGradient z‖ = ‖greenDifferential z‖ :=
  (InnerProductSpace.toDual ℝ PlanarSpace).symm.norm_map _

theorem greenGradient_inner_of_lift {z : Torus} {x : PlanarSpace}
    (hx : torusQuotient x = z) (v : PlanarSpace) :
    inner ℝ (greenGradient z) v = fderiv ℝ regularGreenLift x v := by
  rw [greenGradient_inner, greenDifferential_of_lift hx]

theorem continuousAt_greenGradient {z : Torus} (hz : z ≠ 0) :
    ContinuousAt greenGradient z :=
  (InnerProductSpace.toDual ℝ PlanarSpace).symm.continuous.continuousAt.comp
    (continuousAt_greenDifferential hz)

theorem continuousOn_greenGradient : ContinuousOn greenGradient ({0}ᶜ : Set Torus) := by
  intro z hz
  exact (continuousAt_greenGradient (by simpa using hz)).continuousWithinAt

theorem measurable_greenGradient : Measurable greenGradient :=
  measurable_of_continuousOn_compl_singleton 0 continuousOn_greenGradient

/-- The same Hessian as a Euclidean linear endomorphism, through the real Riesz map. -/
def greenHessianOperator (z : Torus) : PlanarSpace →L[ℝ] PlanarSpace :=
  InnerProductSpace.continuousLinearMapOfBilin (greenHessian z)

theorem greenHessianOperator_inner (z : Torus) (u v : PlanarSpace) :
    inner ℝ (greenHessianOperator z u) v = greenHessian z u v :=
  InnerProductSpace.continuousLinearMapOfBilin_apply (greenHessian z) u v

theorem norm_greenHessianOperator_apply (z : Torus) (u : PlanarSpace) :
    ‖greenHessianOperator z u‖ = ‖greenHessian z u‖ := by
  change ‖(InnerProductSpace.toDual ℝ PlanarSpace).symm (greenHessian z u)‖ = _
  exact (InnerProductSpace.toDual ℝ PlanarSpace).symm.norm_map _

/-- Riesz conversion preserves the operator norm of the full Hessian exactly. -/
theorem norm_greenHessianOperator (z : Torus) : ‖greenHessianOperator z‖ = ‖greenHessian z‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound (greenHessianOperator z) (norm_nonneg (greenHessian z))
    intro u
    rw [norm_greenHessianOperator_apply]
    exact (greenHessian z).le_opNorm u
  · apply ContinuousLinearMap.opNorm_le_bound (greenHessian z) (norm_nonneg (greenHessianOperator z))
    intro u
    rw [← norm_greenHessianOperator_apply]
    exact (greenHessianOperator z).le_opNorm u

/-- The Euclidean Hessian operator is the ordinary derivative of the lifted
gradient at every nonlattice point. -/
theorem fderiv_greenGradient_lift {x : PlanarSpace} (hx : x ∈ offIntegerLattice) :
    fderiv ℝ (fun y : PlanarSpace ↦ greenGradient (torusQuotient y)) x =
      greenHessianOperator (torusQuotient x) := by
  let R : (PlanarSpace →L[ℝ] ℝ) →L[ℝ] PlanarSpace :=
    (InnerProductSpace.toDual ℝ PlanarSpace).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfun : (fun y : PlanarSpace ↦ greenGradient (torusQuotient y)) =
      R ∘ (fderiv ℝ regularGreenLift) := by
    funext y
    exact congrArg (fun L : PlanarSpace →L[ℝ] ℝ ↦ R L) (greenDifferential_lift y)
  have hd : DifferentiableAt ℝ (fderiv ℝ regularGreenLift) x :=
    (contDiffOn_fderiv_regularGreenLift.contDiffAt
      (isOpen_offIntegerLattice.mem_nhds hx)).differentiableAt (by simp)
  rw [hfun]
  change fderiv ℝ (R ∘ fderiv ℝ regularGreenLift) x = R.comp (greenHessian (torusQuotient x))
  rw [greenHessian_lift]
  exact (R.hasFDerivAt.comp x hd.hasFDerivAt).fderiv

end PeriodicAttractiveLogGas
