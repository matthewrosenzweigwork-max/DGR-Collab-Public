import LeanResearch.PeriodicAttractiveLogGas.DeletedPairConditionals

/-! Actual one-site inequalities for every optional deleted-pair law.
The coefficient and density bounds are proved upstream; this unit applies
the local physical-gradient inequalities with the unchanged source constants.
It covers functions Lipschitz only on the relevant closed patch. -/

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal

namespace PeriodicAttractiveLogGas.DeletedPointEstimates

open MeshCells MeshAdjacentCells GreenPointWeights LabelOccupations
  LocalPointEstimates OneCoordinateConditionals CoordinateConditionalKernels
  ConditionalLawEstimates

/-- General coefficient version of the one-site function package. Every
integrability statement is a conclusion, including the ordinary gradient. -/
theorem pointLaw_functionEstimates {ι : Type*} [Fintype ι] {J : ℕ}
    (hJ : 0 < J) (β₀ : ℝ) (Y : ι → Torus) (v : ι → ℝ)
    (a : MeshIndex J) (b : Patch)
    (hprob : IsProbabilityMeasure (pointLaw (patchMeasure J hJ a b) Y v))
    (hlower : ∀ᵐ z ∂patchMeasure J hJ a b,
      lowerBound β₀ ≤ pointDensity (patchMeasure J hJ a b) Y v z)
    (hmem : MemLp (pointDensity (patchMeasure J hJ a b) Y v) 4 (patchMeasure J hJ a b))
    (hnorm : lpNorm (pointDensity (patchMeasure J hJ a b) Y v) 4
      (patchMeasure J hJ a b) ≤ densityNormBound β₀)
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (patchDomain J hJ a b))) :
    FunctionEstimates β₀ J b (pointLaw (patchMeasure J hJ a b) Y v) f := by
  let p := pointDensity (patchMeasure J hJ a b) Y v
  have he : TorusPatchDensity.law (shape b) J hJ a p =
      pointLaw (patchMeasure J hJ a b) Y v := by
    rw [TorusPatchDensity.law, baseMeasure_shape]
    rfl
  let hprob' : IsProbabilityMeasure (TorusPatchDensity.law (shape b) J hJ a p) := by
    rw [he]
    exact hprob
  have hfinite := TorusPatchDensity.density_finite (shape b) J hJ a p hf
  rw [he] at hfinite
  have hlocal := pointLaw_estimates hJ a b Y v (lowerBound_pos β₀) hprob hlower hmem hnorm hf
  have hu := OneSiteConstants.uniform_estimates hJ b
    (lowerBound_pos β₀).le (densityNormBound_pos β₀).le hlocal
  exact ⟨hfinite.1, hfinite.2.1, hfinite.2.2.1, hfinite.2.2.2.1,
    hfinite.2.2.2.2.1, hfinite.2.2.2.2.2, hlocal, hu.1, hu.2.1, hu.2.2.1, hu.2.2.2⟩

/-- All actual deleted source coefficients satisfy the same estimates,
for every fixed closed placement, even if poles coincide. -/
theorem capped_source_functionEstimates {n J : ℕ}
    (d : Option (DeletedPairEnsemble.Pair (n + 1)))
    {β β₀ δ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PrescribedOutside (mesh_pos hmesh) η i Y)
    (a : MeshIndex J) (b : Patch) {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (patchDomain J (mesh_pos hmesh) a b))) :
    FunctionEstimates β₀ J b
      (pointLaw (patchMeasure J (mesh_pos hmesh) a b) Y
        (DeletedPairEnsemble.sourceCoefficient d β i)) f := by
  have hb := DeletedPairEnsemble.capped_source_bounds d hβ hβ₀ hδ hmesh η hη i Y hY a b
  exact pointLaw_functionEstimates (mesh_pos hmesh) β₀ Y _ a b
    hb.2.2.1 hb.2.2.2.2.1 hb.2.2.2.1 hb.2.2.2.2.2 hf

theorem ambientKernel_functionEstimates {n J : ℕ}
    (d : Option (DeletedPairEnsemble.Pair (n + 1)))
    {β β₀ δ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (i : Fin (n + 1)) (X : Configuration (n + 1))
    (hX : PrescribedOutside (mesh_pos hmesh) η i (removeSite i X))
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (patchDomain J (mesh_pos hmesh) (A i) (B i)))) :
    FunctionEstimates β₀ J (B i)
      (DeletedPairConditionals.ambientKernels (mesh_pos hmesh) A B d β i X) f := by
  have hb := DeletedPairEnsemble.capped_source_bounds d hβ hβ₀ hδ hmesh η hη i _ hX (A i) (B i)
  rw [DeletedPairConditionals.ambientKernel_eq_pointLaw _ A B d β i X hb.1 hb.2.1]
  exact capped_source_functionEstimates d hβ hβ₀ hδ hmesh η hη i _ hX (A i) (B i) hf

/-- The measure is the pushforward of the actual subtype resampling
kernel, not an independently chosen probability with a similar density. -/
theorem labelKernel_functionEstimates {n J : ℕ}
    (d : Option (DeletedPairEnsemble.Pair (n + 1)))
    {β β₀ δ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η) (i : Fin (n + 1))
    (X : PatchCoordinates (mesh_pos hmesh) η (fun _ ↦ .cell))
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (meshCell J (mesh_pos hmesh) (η i)))) :
    FunctionEstimates β₀ J .cell
      (Measure.map (Subtype.val : patchDomain J (mesh_pos hmesh) (η i) .cell → Torus)
        (DeletedPairConditionals.patchKernels (mesh_pos hmesh) (mesh_two_le hmesh)
          η (fun _ ↦ .cell) d β i X)) f := by
  rw [DeletedPairConditionals.map_val_labelKernel d hβ hβ₀ hδ hmesh η hη i X]
  exact capped_source_functionEstimates d hβ hβ₀ hδ hmesh η hη i _
    (patchOutside_inclusion _ η (fun _ ↦ .cell) i X) (η i) .cell hf

/-- Every conditioned coordinate of the actual adjacent product is
included. Both capped completions discharge the fixed-source cap. -/
theorem adjacentKernel_functionEstimates {n J : ℕ}
    (d : Option (DeletedPairEnsemble.Pair (n + 1)))
    {β β₀ δ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (t i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η t a r)
    (X : PatchCoordinates (mesh_pos hmesh) (Function.update η t a) (adjacentShapes t r))
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (patchDomain J (mesh_pos hmesh)
      (Function.update η t a i) (adjacentShapes t r i)))) :
    FunctionEstimates β₀ J (adjacentShapes t r i)
      (Measure.map (Subtype.val : patchDomain J (mesh_pos hmesh)
        (Function.update η t a i) (adjacentShapes t r i) → Torus)
        (DeletedPairConditionals.patchKernels (mesh_pos hmesh) (mesh_two_le hmesh)
          (Function.update η t a) (adjacentShapes t r) d β i X)) f := by
  rw [DeletedPairConditionals.map_val_adjacentKernel d hβ hβ₀ hδ hmesh η t i a r hadm X]
  obtain ⟨ζ, hζ, hY⟩ := exists_capped_adjacent_outside (mesh_pos hmesh) η t i a r hadm _
    (patchOutside_inclusion _ _ _ i X)
  exact capped_source_functionEstimates d hβ hβ₀ hδ hmesh ζ hζ i _ hY _ _ hf

end PeriodicAttractiveLogGas.DeletedPointEstimates
