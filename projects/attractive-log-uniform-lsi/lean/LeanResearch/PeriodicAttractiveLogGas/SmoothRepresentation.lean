import LeanResearch.PeriodicAttractiveLogGas.PeriodicCalculus
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Constructions

/-! Exact representation of smooth periodic scalar functions by SmoothPair.
Source: the ambient smooth core in prop:ambient. The gradient is obtained from
the actual derivative on the Euclidean cover by the Riesz equivalence. Its
fiber invariance and continuity on the quotient are proved, not assumed. -/

noncomputable section

open scoped Topology ContDiff

namespace PeriodicAttractiveLogGas

@[simp]
theorem configurationQuotient_sub (N : ℕ) (y z : Gradient N) :
    configurationQuotient N (y - z) =
      configurationQuotient N y - configurationQuotient N z := by
  ext i k
  simp [configurationQuotient]

/-- The actual Euclidean covering map is an open quotient map. -/
theorem isOpenQuotientMap_configurationQuotient (N : ℕ) :
    IsOpenQuotientMap (configurationQuotient N) := by
  let e : Gradient N ≃ₜ ((Fin N × Fin 2) → ℝ) :=
    (EuclideanSpace.equiv (Fin N × Fin 2) ℝ).toHomeomorph
  let c : ((Fin N × Fin 2) → UnitAddCircle) ≃ₜ Configuration N :=
    Homeomorph.piCurry
  have hcircle : IsOpenQuotientMap (fun t : ℝ ↦ (t : UnitAddCircle)) :=
    QuotientAddGroup.isOpenQuotientMap_mk
  have hflat : IsOpenQuotientMap
      (fun y : (Fin N × Fin 2) → ℝ ↦ fun j ↦ (y j : UnitAddCircle)) :=
    IsOpenQuotientMap.piMap (fun _ : Fin N × Fin 2 ↦ hcircle)
  have h := c.isOpenQuotientMap.comp (hflat.comp e.isOpenQuotientMap)
  change IsOpenQuotientMap (configurationQuotient N) at h
  exact h

/-- Translation by a difference of lifts leaves the scalar lift unchanged,
so its Fréchet derivatives agree at points of the same quotient fiber. -/
theorem fderiv_lift_eq_of_configurationQuotient_eq {N : ℕ}
    (f : C(Configuration N, ℝ)) {y z : Gradient N}
    (hyz : configurationQuotient N y = configurationQuotient N z) :
    fderiv ℝ (fun w ↦ f (configurationQuotient N w)) y =
      fderiv ℝ (fun w ↦ f (configurationQuotient N w)) z := by
  let F : Gradient N → ℝ := fun w ↦ f (configurationQuotient N w)
  change fderiv ℝ F y = fderiv ℝ F z
  have hperiod : (fun w ↦ F (w + (z - y))) = F := by
    funext w
    dsimp [F]
    rw [configurationQuotient_add, configurationQuotient_sub, ← hyz]
    simp
  have hshift : y + (z - y) = z := by
    rw [add_comm, sub_add_cancel]
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := F) (x := y) (z - y)
  rw [hperiod] at h
  simpa only [hshift] using h

/-- Riesz vector of the derivative of the scalar lift to the Euclidean cover. -/
def euclideanLiftGradient {N : ℕ} (f : C(Configuration N, ℝ)) (y : Gradient N) :
    Gradient N :=
  (InnerProductSpace.toDual ℝ (Gradient N)).symm
    (fderiv ℝ (fun w ↦ f (configurationQuotient N w)) y)

theorem euclideanLiftGradient_eq_of_configurationQuotient_eq {N : ℕ}
    (f : C(Configuration N, ℝ)) {y z : Gradient N}
    (hyz : configurationQuotient N y = configurationQuotient N z) :
    euclideanLiftGradient f y = euclideanLiftGradient f z :=
  congrArg (InnerProductSpace.toDual ℝ (Gradient N)).symm
    (fderiv_lift_eq_of_configurationQuotient_eq f hyz)

theorem continuous_euclideanLiftGradient {N : ℕ} (f : C(Configuration N, ℝ))
    (hf : ContDiff ℝ ∞ (fun y ↦ f (configurationQuotient N y))) :
    Continuous (euclideanLiftGradient f) := by
  exact (InnerProductSpace.toDual ℝ (Gradient N)).symm.continuous.comp
    (hf.continuous_fderiv (by simp))

/-- Choose a lift only to define the descended function. Fiber invariance below
shows that its value is independent of that choice. -/
def descendedLiftGradient {N : ℕ} (f : C(Configuration N, ℝ))
    (x : Configuration N) : Gradient N :=
  euclideanLiftGradient f (Classical.choose (configurationQuotient_surjective N x))

@[simp]
theorem descendedLiftGradient_configurationQuotient {N : ℕ}
    (f : C(Configuration N, ℝ)) (y : Gradient N) :
    descendedLiftGradient f (configurationQuotient N y) = euclideanLiftGradient f y := by
  unfold descendedLiftGradient
  apply euclideanLiftGradient_eq_of_configurationQuotient_eq f
  exact Classical.choose_spec
    (configurationQuotient_surjective N (configurationQuotient N y))

theorem continuous_descendedLiftGradient {N : ℕ} (f : C(Configuration N, ℝ))
    (hf : ContDiff ℝ ∞ (fun y ↦ f (configurationQuotient N y))) :
    Continuous (descendedLiftGradient f) := by
  apply (isOpenQuotientMap_configurationQuotient N).isQuotientMap.continuous_iff.mpr
  simpa only [Function.comp_def, descendedLiftGradient_configurationQuotient] using
    continuous_euclideanLiftGradient f hf

theorem hasFDerivAt_lift_descendedGradient {N : ℕ} (f : C(Configuration N, ℝ))
    (hf : ContDiff ℝ ∞ (fun y ↦ f (configurationQuotient N y))) (y : Gradient N) :
    HasFDerivAt (fun w ↦ f (configurationQuotient N w))
      (innerSL ℝ (descendedLiftGradient f (configurationQuotient N y))) y := by
  have hderiv : innerSL ℝ (descendedLiftGradient f (configurationQuotient N y)) =
      fderiv ℝ (fun w ↦ f (configurationQuotient N w)) y := by
    ext v
    simp only [innerSL_apply_apply, descendedLiftGradient_configurationQuotient,
      euclideanLiftGradient, InnerProductSpace.toDual_symm_apply]
  rw [hderiv]
  exact (hf.differentiable (by simp) y).hasFDerivAt

/-- The directional derivative of any actual SmoothPair agrees on the cover
with evaluation of the lift's genuine Fréchet derivative. -/
theorem SmoothPair.inner_gradient_configurationQuotient {N : ℕ} (f : SmoothPair N)
    (y v : Gradient N) :
    inner ℝ (f.gradient (configurationQuotient N y)) v =
      fderiv ℝ (fun w ↦ f.value (configurationQuotient N w)) y v := by
  have h := congrArg (fun L : Gradient N →L[ℝ] ℝ ↦ L v) (f.differential y).fderiv
  simpa only [innerSL_apply_apply] using h.symm

/-- Formula for the gradient of any actual SmoothPair on the Euclidean cover. -/
theorem SmoothPair.gradient_configurationQuotient_eq_riesz {N : ℕ} (f : SmoothPair N)
    (y : Gradient N) :
    f.gradient (configurationQuotient N y) =
      (InnerProductSpace.toDual ℝ (Gradient N)).symm
        (fderiv ℝ (fun w ↦ f.value (configurationQuotient N w)) y) := by
  apply ext_inner_right ℝ
  intro v
  rw [InnerProductSpace.toDual_symm_apply]
  exact f.inner_gradient_configurationQuotient y v

/-- Every continuous scalar function with a smooth Euclidean lift has a genuine
continuous gradient on the quotient and therefore defines an actual SmoothPair. -/
def SmoothPair.ofContDiffLift {N : ℕ} (f : C(Configuration N, ℝ))
    (hf : ContDiff ℝ ∞ (fun y ↦ f (configurationQuotient N y))) : SmoothPair N where
  value := f
  gradient := ⟨descendedLiftGradient f, continuous_descendedLiftGradient f hf⟩
  smooth := hf
  differential := hasFDerivAt_lift_descendedGradient f hf

@[simp]
theorem SmoothPair.ofContDiffLift_value {N : ℕ} (f : C(Configuration N, ℝ))
    (hf : ContDiff ℝ ∞ (fun y ↦ f (configurationQuotient N y))) :
    (SmoothPair.ofContDiffLift f hf).value = f := rfl

theorem exists_smoothPair_of_contDiff_lift {N : ℕ} (f : C(Configuration N, ℝ))
    (hf : ContDiff ℝ ∞ (fun y ↦ f (configurationQuotient N y))) :
    ∃ g : SmoothPair N, g.value = f :=
  ⟨SmoothPair.ofContDiffLift f hf, rfl⟩

/-- Exact scalar-class correspondence for the implemented ambient smooth core. -/
theorem exists_smoothPair_iff_contDiff_lift {N : ℕ} (f : C(Configuration N, ℝ)) :
    (∃ g : SmoothPair N, g.value = f) ↔
      ContDiff ℝ ∞ (fun y ↦ f (configurationQuotient N y)) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact g.smooth
  · exact exists_smoothPair_of_contDiff_lift f

end PeriodicAttractiveLogGas
