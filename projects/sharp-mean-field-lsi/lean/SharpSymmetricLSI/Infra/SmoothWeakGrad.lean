import SharpSymmetricLSI.Infra.WeakGrad

/-!
# Smooth functions on a torus have their classical gradient as weak gradient (Phase 1)

For `f : 𝕋^ι → ℝ` whose periodic lift `F = f ∘ liftT` is `C¹`, the classical gradient
`y ↦ ∇F(secT y)` is a weak gradient of `f` (`isWeakGrad_of_contDiff`), hence agrees a.e. with
`weakGrad f` (`weakGrad_ae_eq_of_contDiff`).
-/

open MeasureTheory
open scoped ContDiff

namespace SharpLSI

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem liftT_add (x y : ι → ℝ) : liftT (x + y) = liftT x + liftT y := by
  funext i; simp [liftT]

omit [Fintype ι] [DecidableEq ι] in
theorem liftT_sub (x y : ι → ℝ) : liftT (x - y) = liftT x - liftT y := by
  funext i; simp [liftT]

omit [DecidableEq ι] in
/-- The derivative of a lifted function is periodic. -/
theorem fderiv_lift_secT (f : UnitAddTorus ι → ℝ) (x : ι → ℝ) :
    fderiv ℝ (f ∘ liftT) (secT (liftT x)) = fderiv ℝ (f ∘ liftT) x := by
  set m := x - secT (liftT x) with hm
  have hm0 : liftT m = 0 := by rw [hm, liftT_sub, liftT_secT, sub_self]
  have hper : (fun z => (f ∘ liftT) (z + m)) = f ∘ liftT := by
    funext z; simp [liftT_add, hm0]
  have := fderiv_comp_add_right (𝕜 := ℝ) (f := f ∘ liftT) (x := secT (liftT x)) m
  rw [hper] at this
  rw [this, hm, add_sub_cancel]

theorem isWeakGrad_of_contDiff {f : UnitAddTorus ι → ℝ} (hf : ContDiff ℝ 1 (f ∘ liftT)) :
    IsWeakGrad f (fun y k => fderiv ℝ (f ∘ liftT) (secT y) (Pi.single k 1)) := by
  have hg : ∀ k, (fun x => fderiv ℝ (f ∘ liftT) (secT (liftT x)) (Pi.single k 1)) =
      fun x => fderiv ℝ (f ∘ liftT) x (Pi.single k 1) := by
    intro k; funext x; rw [fderiv_lift_secT]
  have hcont : ∀ k, Continuous fun x => fderiv ℝ (f ∘ liftT) x (Pi.single k 1) := fun k =>
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine ⟨hf.continuous.locallyIntegrable, fun k => ?_, fun φ hφ hφc k => ?_⟩
  · rw [hg k]; exact (hcont k).locallyIntegrable
  · simp_rw [fderiv_lift_secT]
    have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
    have hFd : Differentiable ℝ (f ∘ liftT) := hf.differentiable one_ne_zero
    have hφ' : Continuous fun x => fderiv ℝ φ x (Pi.single k 1) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hφ'c : HasCompactSupport fun x => fderiv ℝ φ x (Pi.single k 1) :=
      hφc.fderiv_apply (𝕜 := ℝ) _
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (((hcont k).mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left)
      ((hf.continuous.mul hφ').integrable_of_hasCompactSupport hφ'c.mul_left)
      ((hf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left)
      (fun x _ => hFd x) (fun x _ => hφd x)

theorem weakGrad_ae_eq_of_contDiff {f : UnitAddTorus ι → ℝ} (hf : ContDiff ℝ 1 (f ∘ liftT)) :
    weakGrad f =ᵐ[volume] fun y k => fderiv ℝ (f ∘ liftT) (secT y) (Pi.single k 1) := by
  have hw : HasWeakGrad f := ⟨_, isWeakGrad_of_contDiff hf⟩
  have : weakGrad f = hw.choose := by simp [weakGrad, hw]
  rw [this]
  exact weakGrad_ae_unique hw.choose_spec (isWeakGrad_of_contDiff hf)

end SharpLSI
