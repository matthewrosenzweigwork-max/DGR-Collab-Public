import SharpSymmetricLSI.Paper.RefSpec1

/-!
# Smooth one-particle slices of functions on `𝕋^{N×d}` (Phase 3, lane D; R29 groundwork)

For `F` with `F ∘ liftT ∈ C¹`, the slice `y ↦ F(flat (X[i := y]))` is `C¹` on `𝕋^d` and its
gradient is the `i`-th block of the gradient of `F`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {N d : ℕ}

/-- The classical gradient of `F` on `𝕋^ι` (in the section coordinates). -/
def cgrad {ι : Type*} [DecidableEq ι] (F : UnitAddTorus ι → ℝ) (Y : UnitAddTorus ι) (p : ι) : ℝ :=
  fderiv ℝ (F ∘ liftT) (secT Y) (Pi.single p 1)

/-- The affine embedding of block `i`. -/
def embI (X : Config N d) (i : Fin N) (z : Fin d → ℝ) : Fin N × Fin d → ℝ :=
  fun p => if p.1 = i then z p.2 else secT (X p.1) p.2

theorem liftT_embI (X : Config N d) (i : Fin N) (z : Fin d → ℝ) :
    liftT (embI X i z) = flat (Function.update X i (liftT z)) := by
  funext p
  obtain ⟨j, k⟩ := p
  by_cases hj : j = i
  · subst hj; simp [liftT, flat, embI]
  · simp only [liftT, flat, embI, hj, ↓reduceIte, Function.update_of_ne hj]
    exact congrFun (liftT_secT (X j)) k

theorem embI_secT (X : Config N d) (i : Fin N) (y : Torus d) :
    embI X i (secT y) = secT (flat (Function.update X i y)) := by
  funext p
  obtain ⟨j, k⟩ := p
  by_cases hj : j = i
  · subst hj; simp [embI, secT, flat]
  · simp [embI, hj, secT, flat, Function.update_of_ne hj]

theorem hasFDerivAt_embI (X : Config N d) (i : Fin N) (z : Fin d → ℝ) :
    HasFDerivAt (embI X i) (ContinuousLinearMap.pi fun p : Fin N × Fin d =>
      if p.1 = i then ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) p.2 else 0) z := by
  refine hasFDerivAt_pi.mpr fun p => ?_
  simp only [embI]
  split_ifs
  · exact hasFDerivAt_apply p.2 z
  · exact hasFDerivAt_const _ _

theorem contDiff_embI (X : Config N d) (i : Fin N) : ContDiff ℝ ⊤ (embI X i) := by
  refine contDiff_pi.mpr fun p => ?_
  simp only [embI]
  split_ifs
  · exact contDiff_apply ℝ ℝ p.2
  · exact contDiff_const

/-- The slice. -/
def sliceF (F : UnitAddTorus (Fin N × Fin d) → ℝ) (X : Config N d) (i : Fin N) (y : Torus d) : ℝ :=
  F (flat (Function.update X i y))

theorem sliceF_comp_liftT (F : UnitAddTorus (Fin N × Fin d) → ℝ) (X : Config N d) (i : Fin N) :
    sliceF F X i ∘ liftT = (F ∘ liftT) ∘ embI X i := by
  funext z
  simp only [Function.comp, sliceF, liftT_embI]

theorem contDiff_sliceF {F : UnitAddTorus (Fin N × Fin d) → ℝ} (hF : ContDiff ℝ 1 (F ∘ liftT))
    (X : Config N d) (i : Fin N) : ContDiff ℝ 1 (sliceF F X i ∘ liftT) := by
  rw [sliceF_comp_liftT]
  exact hF.comp ((contDiff_embI X i).of_le le_top)

theorem cgrad_sliceF {F : UnitAddTorus (Fin N × Fin d) → ℝ} (hF : ContDiff ℝ 1 (F ∘ liftT))
    (X : Config N d) (i : Fin N) (y : Torus d) (k : Fin d) :
    cgrad (sliceF F X i) y k = cgrad F (flat (Function.update X i y)) (i, k) := by
  unfold cgrad
  rw [sliceF_comp_liftT]
  have hd : DifferentiableAt ℝ (F ∘ liftT) (embI X i (secT y)) :=
    (hF.differentiable one_ne_zero) _
  rw [fderiv_comp _ hd (hasFDerivAt_embI X i _).differentiableAt, (hasFDerivAt_embI X i _).fderiv,
    embI_secT, ContinuousLinearMap.comp_apply]
  congr 1
  funext p
  obtain ⟨j, l⟩ := p
  simp only [ContinuousLinearMap.pi_apply]
  by_cases hj : j = i
  · subst hj
    simp [Pi.single_apply, Prod.ext_iff]
  · simp [hj, Pi.single_apply, Prod.ext_iff]

end SharpLSI
