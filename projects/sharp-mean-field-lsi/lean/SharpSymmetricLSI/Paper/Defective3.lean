import SharpSymmetricLSI.Paper.Defective2

/-!
# R03 (Proposition 2.2), part 3: weak gradients under reindexing

For an equivalence of index types `σ : ι' ≃ ι`, `reidx σ y = y ∘ σ.symm` is a measure preserving
isomorphism `𝕋^{ι'} ≃ 𝕋^ι`, and weak gradients transfer: if `∇f = g` then
`∇(f ∘ reidx σ)_k = g(reidx σ ·)_{σ k}` (`isWeakGrad_reidx`).
-/

open MeasureTheory Filter
open scoped ENNReal ContDiff

namespace SharpLSI

section reindex
variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

/-- Reindexing of points: `(reidx σ y) i = y (σ.symm i)`. -/
def reidx {X : Type*} (σ : ι' ≃ ι) (y : ι' → X) : ι → X := fun i => y (σ.symm i)

theorem reidx_apply {X : Type*} (σ : ι' ≃ ι) (y : ι' → X) (a : ι') : reidx σ y (σ a) = y a := by
  simp [reidx]

theorem reidx_eq_piCongrLeft {X : Type*} [MeasurableSpace X] (σ : ι' ≃ ι) :
    (reidx σ : (ι' → X) → (ι → X)) = MeasurableEquiv.piCongrLeft (fun _ : ι => X) σ := by
  funext y i
  obtain ⟨a, rfl⟩ := σ.surjective i
  rw [MeasurableEquiv.piCongrLeft_apply_apply, reidx_apply]

theorem measurePreserving_reidx_torus (σ : ι' ≃ ι) :
    MeasurePreserving (reidx σ : UnitAddTorus ι' → UnitAddTorus ι) volume volume := by
  rw [reidx_eq_piCongrLeft]
  exact volume_measurePreserving_piCongrLeft (fun _ : ι => UnitAddCircle) σ

theorem measurePreserving_reidx_real (σ : ι' ≃ ι) :
    MeasurePreserving (reidx σ : (ι' → ℝ) → (ι → ℝ)) volume volume := by
  rw [reidx_eq_piCongrLeft]
  exact volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) σ

theorem liftT_reidx (σ : ι' ≃ ι) (x : ι' → ℝ) : liftT (reidx σ x) = reidx σ (liftT x) := rfl

/-- The linear map `w ↦ w ∘ σ`. -/
noncomputable def reidxCLM (σ : ι' ≃ ι) : (ι → ℝ) →L[ℝ] (ι' → ℝ) :=
  ContinuousLinearMap.pi fun a => ContinuousLinearMap.proj (σ a)

theorem reidxCLM_apply (σ : ι' ≃ ι) (w : ι → ℝ) : reidxCLM σ w = fun a => w (σ a) := rfl

theorem reidxCLM_reidx (σ : ι' ≃ ι) (x : ι' → ℝ) : reidxCLM σ (reidx σ x) = x := by
  funext a; simp [reidxCLM_apply, reidx]

theorem reidxCLM_single (σ : ι' ≃ ι) (k : ι') :
    reidxCLM σ (Pi.single (σ k) 1) = Pi.single k 1 := by
  funext a
  simp only [reidxCLM_apply]
  by_cases h : a = k
  · subst h; simp
  · rw [Pi.single_eq_of_ne (fun h' => h (σ.injective h')), Pi.single_eq_of_ne h]

theorem integrable_comp_reidx (σ : ι' ≃ ι) {u : UnitAddTorus ι → ℝ} (hu : Integrable u volume) :
    Integrable (fun y => u (reidx σ y)) volume :=
  (measurePreserving_reidx_torus σ).integrable_comp_of_integrable hu

/-- **Weak gradients under reindexing.** -/
theorem isWeakGrad_reidx (σ : ι' ≃ ι) {f : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad f g) (hf : Integrable f volume) (hg : ∀ k, Integrable (fun y => g y k) volume) :
    IsWeakGrad (fun y => f (reidx σ y)) (fun y k => g (reidx σ y) (σ k)) := by
  refine ⟨locallyIntegrable_comp_liftT (integrable_comp_reidx σ hf),
    fun k => locallyIntegrable_comp_liftT (integrable_comp_reidx σ (hg (σ k))),
    fun φ hφ hφc k => ?_⟩
  set ψ : (ι → ℝ) → ℝ := fun w => φ (reidxCLM σ w) with hψ
  have hψs : ContDiff ℝ ∞ ψ := hφ.comp (reidxCLM σ).contDiff
  have hψc : HasCompactSupport ψ := by
    have := hφc.comp_homeomorph (Homeomorph.piCongrLeft (Y := fun _ : ι => ℝ) σ).symm
    convert this using 1
    funext w
    simp only [Function.comp_apply, hψ]
    congr 1
  have hderiv : ∀ x : ι' → ℝ, fderiv ℝ φ x (Pi.single k 1) =
      fderiv ℝ ψ (reidx σ x) (Pi.single (σ k) 1) := by
    intro x
    have hd : HasFDerivAt ψ ((fderiv ℝ φ (reidxCLM σ (reidx σ x))).comp (reidxCLM σ)) (reidx σ x) :=
      (hφ.differentiable (by simp) _).hasFDerivAt.comp _ (reidxCLM σ).hasFDerivAt
    rw [hd.fderiv, ContinuousLinearMap.comp_apply, reidxCLM_single, reidxCLM_reidx]
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) σ
  have key := h.ibp ψ hψs hψc (σ k)
  have e1 : ∫ x : ι' → ℝ, f (reidx σ (liftT x)) * fderiv ℝ φ x (Pi.single k 1) =
      ∫ w : ι → ℝ, f (liftT w) * fderiv ℝ ψ w (Pi.single (σ k) 1) := by
    rw [← (hmp.integral_comp' (f := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) σ)
      (g := fun w => f (liftT w) * fderiv ℝ ψ w (Pi.single (σ k) 1)))]
    · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [← reidx_eq_piCongrLeft, hderiv, liftT_reidx]
  have e2 : ∫ x : ι' → ℝ, g (reidx σ (liftT x)) (σ k) * φ x =
      ∫ w : ι → ℝ, g (liftT w) (σ k) * ψ w := by
    rw [← (hmp.integral_comp' (f := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) σ)
      (g := fun w => g (liftT w) (σ k) * ψ w))]
    · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [← reidx_eq_piCongrLeft, liftT_reidx]
      simp only [hψ, reidxCLM_reidx]
  show ∫ x, f (reidx σ (liftT x)) * fderiv ℝ φ x (Pi.single k 1) =
    -∫ x, g (reidx σ (liftT x)) (σ k) * φ x
  rw [e1, e2, key]

end reindex

end SharpLSI
