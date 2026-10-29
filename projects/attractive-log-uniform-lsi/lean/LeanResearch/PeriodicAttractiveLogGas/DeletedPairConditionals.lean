import LeanResearch.PeriodicAttractiveLogGas.DeletedPairEnsemble
import LeanResearch.PeriodicAttractiveLogGas.PositiveProductConditionals

/-! Actual conditional versions and coordinate kernels for the optional
deleted-pair law in source Proposition 3.8. All-placement identities use
the actual finite positive point weights. The outer marginal remains the
pushforward of the true joint law. No influence estimate is assumed here. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace PeriodicAttractiveLogGas.DeletedPairConditionals

open MeshCells MeshAdjacentCells GreenPointWeights LabelOccupations
open OneCoordinateConditionals ConditionalLawEstimates CoordinateConditionalKernels

variable {n J : ℕ}

def jointLaw (hJ : 0 < J) (a : Fin (n + 1) → MeshIndex J)
    (b : Fin (n + 1) → Patch) (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) :
    Measure (Configuration (n + 1)) :=
  PositiveProductConditionals.productLaw (fun k ↦ patchMeasure J hJ (a k) (b k))
    (DeletedPairEnsemble.weight regularGreenRepresentative d β)

theorem jointLaw_eq_deleted (hJ : 0 < J) (a : Fin (n + 1) → MeshIndex J)
    (b : Fin (n + 1) → Patch) (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) :
    jointLaw hJ a b d β = DeletedPairEnsemble.law (DeletedPairEnsemble.domainReference hJ a b)
      regularGreenRepresentative d β := rfl

theorem jointLaw_none (hJ : 0 < J) (a : Fin (n + 1) → MeshIndex J)
    (b : Fin (n + 1) → Patch) (β : ℝ) :
    jointLaw hJ a b none β = productGibbs (fun k ↦ patchMeasure J hJ (a k) (b k)) β := by
  unfold jointLaw
  rw [DeletedPairEnsemble.weight_none]
  rfl

theorem jointLaw_probability (hJ : 0 < J) (hJ2 : 2 ≤ J) (hn : 2 ≤ n + 1)
    (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    IsProbabilityMeasure (jointLaw hJ a b d β) :=
  (DeletedPairEnsemble.regular_domain_normalization hJ hJ2 hn a b d hβ hsub).2.2.2

def ambientKernels (hJ : 0 < J) (a : Fin (n + 1) → MeshIndex J)
    (b : Fin (n + 1) → Patch) (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) :
    Fin (n + 1) → Kernel (Configuration (n + 1)) Torus :=
  PositiveProductConditionals.coordinateKernels (fun k ↦ patchMeasure J hJ (a k) (b k))
    (DeletedPairEnsemble.weight regularGreenRepresentative d β)
    (DeletedPairEnsemble.measurable_weight regularGreenRepresentative_measurable d β)
    (DeletedPairEnsemble.weight_pos regularGreenRepresentative d β)

instance isMarkovKernel_ambientKernels (hJ : 0 < J) (a : Fin (n + 1) → MeshIndex J)
    (b : Fin (n + 1) → Patch) (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ)
    (i : Fin (n + 1)) : IsMarkovKernel (ambientKernels hJ a b d β i) := by
  unfold ambientKernels
  infer_instance

theorem independentSite_ambientKernels (hJ : 0 < J) (a : Fin (n + 1) → MeshIndex J)
    (b : Fin (n + 1) → Patch) (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) :
    CoordinateOscillation.IndependentSite (ambientKernels hJ a b d β) :=
  PositiveProductConditionals.independentSite_coordinateKernels _ _ _ _

theorem preservesLaw_ambientKernels (hJ : 0 < J) (hJ2 : 2 ≤ J) (hn : 2 ≤ n + 1)
    (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    ConditionalKernelL2.PreservesLaw (ambientKernels hJ a b d β) (jointLaw hJ a b d β) :=
  PositiveProductConditionals.preservesLaw_coordinateKernels _ _ _ _
    (DeletedPairEnsemble.regular_domain_normalization hJ hJ2 hn a b d hβ hsub).2.2.1

theorem jointLaw_ae_mem_patches (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) :
    ∀ᵐ X ∂jointLaw hJ a b d β, ∀ i, X i ∈ patchDomain J hJ (a i) (b i) := by
  apply (PositiveProductConditionals.productLaw_absolutelyContinuous _ _).ae_le
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval (fun k ↦ patchMeasure J hJ (a k) (b k)) i).quasiMeasurePreserving.ae
    (ae_mem_patchDomain J hJ hJ2 (a i) (b i))

def patchLaw (hJ : 0 < J) (hJ2 : 2 ≤ J) (a : Fin (n + 1) → MeshIndex J)
    (b : Fin (n + 1) → Patch) (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) :
    Measure (PatchCoordinates hJ a b) :=
  domainMeasure (fun k ↦ patchDomain J hJ (a k) (b k))
    (fun k ↦ patchPoint hJ hJ2 (a k) (b k)) (jointLaw hJ a b d β)

def patchKernels (hJ : 0 < J) (hJ2 : 2 ≤ J) (a : Fin (n + 1) → MeshIndex J)
    (b : Fin (n + 1) → Patch) (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ)
    (i : Fin (n + 1)) : Kernel (PatchCoordinates hJ a b) (patchDomain J hJ (a i) (b i)) :=
  domainKernel (fun k ↦ patchDomain J hJ (a k) (b k))
    (fun k ↦ measurableSet_patchDomain J hJ (a k) (b k))
    (fun k ↦ patchPoint hJ hJ2 (a k) (b k)) (ambientKernels hJ a b d β) i

instance isMarkovKernel_patchKernels (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) (i : Fin (n + 1)) :
    IsMarkovKernel (patchKernels hJ hJ2 a b d β i) := by
  unfold patchKernels
  infer_instance

theorem patchLaw_probability (hJ : 0 < J) (hJ2 : 2 ≤ J) (hn : 2 ≤ n + 1)
    (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    IsProbabilityMeasure (patchLaw hJ hJ2 a b d β) := by
  let hp := jointLaw_probability hJ hJ2 hn a b d hβ hsub
  unfold patchLaw
  infer_instance

theorem independentSite_patchKernels (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) :
    CoordinateOscillation.IndependentSite (patchKernels hJ hJ2 a b d β) :=
  independentSite_domainKernel _ (fun k ↦ measurableSet_patchDomain J hJ (a k) (b k)) _ _
    (independentSite_ambientKernels hJ a b d β)

theorem preservesLaw_patchKernels (hJ : 0 < J) (hJ2 : 2 ≤ J) (hn : 2 ≤ n + 1)
    (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    ConditionalKernelL2.PreservesLaw (patchKernels hJ hJ2 a b d β) (patchLaw hJ hJ2 a b d β) := by
  let hp := jointLaw_probability hJ hJ2 hn a b d hβ hsub
  exact preservesLaw_domainKernel _ (fun k ↦ measurableSet_patchDomain J hJ (a k) (b k)) _ _ _
    (preservesLaw_ambientKernels hJ hJ2 hn a b d hβ hsub) (jointLaw_ae_mem_patches hJ hJ2 a b d β)

/-- Exact source measure, with the raw manuscript kernel, after forgetting
the subtype. The statement includes both an actual deletion and none. -/
theorem map_patchLaw_raw (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) :
    Measure.map (patchInclusion hJ a b) (patchLaw hJ hJ2 a b d β) =
      DeletedPairEnsemble.law (DeletedPairEnsemble.domainReference hJ a b)
        greenRealRepresentative d β := by
  calc
    _ = jointLaw hJ a b d β := map_domainInclusion_domainMeasure _
      (fun k ↦ measurableSet_patchDomain J hJ (a k) (b k)) _ _
      (jointLaw_ae_mem_patches hJ hJ2 a b d β)
    _ = _ := DeletedPairEnsemble.regular_domain_law_eq hJ hJ2 a b d β

theorem ambientKernel_eq_pointLaw (hJ : 0 < J)
    (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) (i : Fin (n + 1))
    (X : Configuration (n + 1))
    (hi : Integrable (torusWeight (removeSite i X) (DeletedPairEnsemble.sourceCoefficient d β i))
      (patchMeasure J hJ (a i) (b i)))
    (hz : 0 < ∫ z, torusWeight (removeSite i X) (DeletedPairEnsemble.sourceCoefficient d β i) z
      ∂patchMeasure J hJ (a i) (b i)) :
    ambientKernels hJ a b d β i X =
      pointLaw (patchMeasure J hJ (a i) (b i)) (removeSite i X)
        (DeletedPairEnsemble.sourceCoefficient d β i) := by
  exact PositiveProductConditionals.conditionalKernel_factor_eq_pointLaw _ _
    (DeletedPairEnsemble.measurable_weight regularGreenRepresentative_measurable d β)
    (DeletedPairEnsemble.weight_pos regularGreenRepresentative d β) i _
    (Real.exp_pos _) _ _ (fun z ↦ DeletedPairEnsemble.weight_insertSite d β i z _) hi hz

theorem map_val_patchKernel (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) (i : Fin (n + 1))
    (X : PatchCoordinates hJ a b)
    (hi : Integrable (torusWeight (removeSite i (patchInclusion hJ a b X))
      (DeletedPairEnsemble.sourceCoefficient d β i)) (patchMeasure J hJ (a i) (b i)))
    (hz : 0 < ∫ z, torusWeight (removeSite i (patchInclusion hJ a b X))
      (DeletedPairEnsemble.sourceCoefficient d β i) z ∂patchMeasure J hJ (a i) (b i)) :
    Measure.map (Subtype.val : patchDomain J hJ (a i) (b i) → Torus)
      (patchKernels hJ hJ2 a b d β i X) =
        pointLaw (patchMeasure J hJ (a i) (b i)) (removeSite i (patchInclusion hJ a b X))
          (DeletedPairEnsemble.sourceCoefficient d β i) := by
  have hs : ∀ᵐ z ∂ambientKernels hJ a b d β i (patchInclusion hJ a b X),
      z ∈ patchDomain J hJ (a i) (b i) := by
    rw [ambientKernel_eq_pointLaw hJ a b d β i _ hi hz, pointLaw]
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_mem_patchDomain J hJ hJ2 (a i) (b i))
  exact (map_val_domainKernel _ (fun k ↦ measurableSet_patchDomain J hJ (a k) (b k))
    _ _ i X hs).trans (ambientKernel_eq_pointLaw hJ a b d β i _ hi hz)

theorem map_val_labelKernel {β β₀ δ : ℝ}
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η) (i : Fin (n + 1))
    (X : PatchCoordinates (mesh_pos hmesh) η (fun _ ↦ .cell)) :
    let hJ := mesh_pos hmesh
    Measure.map (Subtype.val : patchDomain J hJ (η i) .cell → Torus)
      (patchKernels hJ (mesh_two_le hmesh) η (fun _ ↦ .cell) d β i X) =
        pointLaw (meshCellMeasure J hJ (η i))
          (removeSite i (patchInclusion hJ η (fun _ ↦ .cell) X))
          (DeletedPairEnsemble.sourceCoefficient d β i) := by
  have hb := DeletedPairEnsemble.capped_source_bounds d hβ hβ₀ hδ hmesh η hη i _
    (patchOutside_inclusion _ η (fun _ ↦ .cell) i X) (η i) .cell
  exact map_val_patchKernel _ (mesh_two_le hmesh) η (fun _ ↦ .cell) d β i X hb.1 hb.2.1

theorem map_val_adjacentKernel {β β₀ δ : ℝ}
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (t i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η t a r)
    (X : PatchCoordinates (mesh_pos hmesh) (Function.update η t a) (adjacentShapes t r)) :
    let hJ := mesh_pos hmesh
    let A := Function.update η t a
    let B := adjacentShapes t r
    Measure.map (Subtype.val : patchDomain J hJ (A i) (B i) → Torus)
      (patchKernels hJ (mesh_two_le hmesh) A B d β i X) =
        pointLaw (patchMeasure J hJ (A i) (B i)) (removeSite i (patchInclusion hJ A B X))
          (DeletedPairEnsemble.sourceCoefficient d β i) := by
  obtain ⟨ζ, hζ, hY⟩ := exists_capped_adjacent_outside (mesh_pos hmesh) η t i a r hadm _
    (patchOutside_inclusion _ _ _ i X)
  have hb := DeletedPairEnsemble.capped_source_bounds d hβ hβ₀ hδ hmesh ζ hζ i _ hY
    (Function.update η t a i) (adjacentShapes t r i)
  exact map_val_patchKernel _ (mesh_two_le hmesh) _ _ d β i X hb.1 hb.2.1

theorem patchLaw_none (hJ : 0 < J) (hJ2 : 2 ≤ J) (a : Fin (n + 1) → MeshIndex J)
    (b : Fin (n + 1) → Patch) (β : ℝ) :
    patchLaw hJ hJ2 a b none β = CoordinateConditionalKernels.patchLaw hJ hJ2 a b β := by
  rw [patchLaw, jointLaw_none]
  rfl

theorem map_patchLaw_none_cells (hJ : 0 < J) (hJ2 : 2 ≤ J) (hn : 2 ≤ n + 1)
    (η : LabelVector J (n + 1)) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    Measure.map (patchInclusion hJ η (fun _ ↦ .cell))
      (patchLaw hJ hJ2 η (fun _ ↦ .cell) none β) = CellRestrictions.labelGibbsMeasure hJ η β := by
  rw [patchLaw_none]
  exact CoordinateConditionalKernels.map_patchLaw_cells hJ hJ2 hn η hβ hsub

theorem map_patchLaw_none_adjacent (hJ : 0 < J) (hJ2 : 2 ≤ J) (hn : 2 ≤ n + 1)
    (η : LabelVector J (n + 1)) (t : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    Measure.map (patchInclusion hJ (Function.update η t a) (adjacentShapes t r))
      (patchLaw hJ hJ2 (Function.update η t a) (adjacentShapes t r) none β) =
        CellRestrictions.twoCellGibbsMeasure hJ η t a (nextCell J hJ a r) β := by
  rw [patchLaw_none]
  exact CoordinateConditionalKernels.map_patchLaw_adjacent hJ hJ2 hn η t a r hβ hsub

end PeriodicAttractiveLogGas.DeletedPairConditionals
