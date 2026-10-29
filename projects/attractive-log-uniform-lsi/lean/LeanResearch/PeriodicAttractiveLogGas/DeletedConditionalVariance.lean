import LeanResearch.PeriodicAttractiveLogGas.GreenConditionalInfluence
import LeanResearch.PeriodicAttractiveLogGas.InfluenceColumnCount
import LeanResearch.PeriodicAttractiveLogGas.ConditionalVarianceIntegral

/-! Source-only assembly of the variance part of source Proposition 3.8.
The kernels, their invariant probability, all Green influence bounds, and the
occupation count are the actual previously constructed objects. No influence,
column, stationarity, or variance conclusion is assumed. The physical-gradient
Poincare inequality is outside this module. Central checking is pending.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace PeriodicAttractiveLogGas.DeletedConditionalVariance

open MeshCells GreenPointWeights LabelOccupations ConditionalLawEstimates
open OneCoordinateConditionals (adjacentShapes)
open CoordinateConditionalKernels (PatchCoordinates)
open CoordinateOscillation (influence columnSum maxColumnSum)

theorem patchCells_eq {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (b : Patch) :
    InfluenceColumnCount.patchCells hJ a b =
      GreenConditionalInfluence.patchCells J hJ a b := by
  cases b <;> rfl

/-- Both constructions use the literal prescribed-cell distance R+1. -/
theorem near_iff {J N R : ℕ} (hJ : 0 < J) (A : Fin N → MeshIndex J)
    (B : Fin N → Patch) (i j : Fin N) :
    InfluenceColumnCount.Near R hJ A B i j ↔
      GreenConditionalInfluence.NearPair J hJ R (A i) (A j) (B i) (B j) := by
  simpa only [patchCells_eq, GreenConditionalInfluence.NearPair] using
    (InfluenceColumnCount.near_iff (R := R) hJ A B i j)

theorem nearInfluenceBound_eq (β₀ : ℝ) (N : ℕ) :
    InfluenceColumnCount.nearInfluenceBound β₀ N =
      GreenConditionalInfluence.nearInfluenceConstant β₀ N := rfl

theorem farInfluenceBound_eq (β₀ : ℝ) (N : ℕ) :
    InfluenceColumnCount.farInfluenceBound β₀ N =
      GreenConditionalInfluence.farInfluenceConstant β₀ N := rfl

theorem pairInfluenceBound_of_near {J N : ℕ} (hJ : 0 < J) (β₀ : ℝ)
    (A : Fin N → MeshIndex J) (B : Fin N → Patch) (i j : Fin N)
    (h : InfluenceColumnCount.Near (radius β₀) hJ A B i j) :
    GreenConditionalInfluence.pairInfluenceBound J hJ β₀ N (A i) (A j) (B i) (B j) =
      InfluenceColumnCount.nearInfluenceBound β₀ N := by
  classical
  have hn := (near_iff hJ A B i j).mp h
  simp only [GreenConditionalInfluence.pairInfluenceBound, ite_eq_left hn, ← nearInfluenceBound_eq]

theorem pairInfluenceBound_of_far {J N : ℕ} (hJ : 0 < J) (β₀ : ℝ)
    (A : Fin N → MeshIndex J) (B : Fin N → Patch) (i j : Fin N)
    (h : ¬InfluenceColumnCount.Near (radius β₀) hJ A B i j) :
    GreenConditionalInfluence.pairInfluenceBound J hJ β₀ N (A i) (A j) (B i) (B j) =
      InfluenceColumnCount.farInfluenceBound β₀ N := by
  classical
  have hn : ¬GreenConditionalInfluence.NearPair J hJ (radius β₀)
      (A i) (A j) (B i) (B j) := fun hh ↦ h ((near_iff hJ A B i j).mpr hh)
  simp only [GreenConditionalInfluence.pairInfluenceBound, ite_eq_right hn, ← farInfluenceBound_eq]

/-- The actual influence matrix, including an optional deleted interaction.
Its diagonal is excluded by the genuine columnSum definition. -/
theorem column_cells_le_half {n J : ℕ} {β β₀ δ : ℝ}
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η) (j : Fin (n + 1)) :
    columnSum (DeletedPairConditionals.patchKernels (mesh_pos hmesh)
      (mesh_two_le hmesh) η (fun _ ↦ .cell) d β) j ≤ 1 / 2 := by
  let κ := DeletedPairConditionals.patchKernels (mesh_pos hmesh)
    (mesh_two_le hmesh) η (fun _ ↦ .cell) d β
  have he (i : Fin (n + 1)) : influence κ i j ≤
      GreenConditionalInfluence.pairInfluenceBound J (mesh_pos hmesh) β₀ (n + 1)
        (η i) (η j) .cell .cell :=
    (GreenConditionalInfluence.deleted_cell_kernel_influence d hβ hβ₀ hδ hmesh η hη i j).1
  change (∑ i ∈ Finset.univ.erase j, influence κ i j) ≤ 1 / 2
  apply InfluenceColumnCount.column_cells_le_half (mesh_pos hmesh) (Nat.zero_lt_succ n)
    (hβ.trans hβ₀) hδ₀ hδ η hη (fun i j ↦ influence κ i j) j
  · intro i _hij hnear
    have hi := he i
    rw [pairInfluenceBound_of_near (mesh_pos hmesh) β₀ η (fun _ ↦ .cell) i j hnear] at hi
    exact hi
  · intro i _hij hfar
    have hi := he i
    rw [pairInfluenceBound_of_far (mesh_pos hmesh) β₀ η (fun _ ↦ .cell) i j hfar] at hi
    exact hi

/-- The count uses whichever genuinely capped endpoint makes the exceptional
target near; all roles of that coordinate are covered by the imported count. -/
theorem column_adjacent_le_half {n J : ℕ} {β β₀ δ : ℝ}
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (t : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η t a r) (j : Fin (n + 1)) :
    columnSum (DeletedPairConditionals.patchKernels (mesh_pos hmesh) (mesh_two_le hmesh)
      (Function.update η t a) (adjacentShapes t r) d β) j ≤ 1 / 2 := by
  let A := Function.update η t a
  let B := adjacentShapes t r
  let κ := DeletedPairConditionals.patchKernels (mesh_pos hmesh) (mesh_two_le hmesh) A B d β
  have he (i : Fin (n + 1)) : influence κ i j ≤
      GreenConditionalInfluence.pairInfluenceBound J (mesh_pos hmesh) β₀ (n + 1)
        (A i) (A j) (B i) (B j) :=
    (GreenConditionalInfluence.deleted_adjacent_kernel_influence
      d hβ hβ₀ hδ hmesh η t i j a r hadm).1
  change (∑ i ∈ Finset.univ.erase j, influence κ i j) ≤ 1 / 2
  apply InfluenceColumnCount.column_adjacent_le_half (mesh_pos hmesh) (Nat.zero_lt_succ n)
    (hβ.trans hβ₀) hδ₀ hδ η t a r hadm (fun i j ↦ influence κ i j) j
  · intro i _hij hnear
    have hi := he i
    rw [pairInfluenceBound_of_near (mesh_pos hmesh) β₀ A B i j hnear] at hi
    exact hi
  · intro i _hij hfar
    have hi := he i
    rw [pairInfluenceBound_of_far (mesh_pos hmesh) β₀ A B i j hfar] at hi
    exact hi

theorem maxColumnSum_cells_le_half {n J : ℕ} {β β₀ δ : ℝ}
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η) :
    maxColumnSum (DeletedPairConditionals.patchKernels (mesh_pos hmesh)
      (mesh_two_le hmesh) η (fun _ ↦ .cell) d β) ≤ 1 / 2 := by
  unfold maxColumnSum
  apply csSup_le (range_nonempty _)
  rintro _ ⟨j, rfl⟩
  exact column_cells_le_half d hβ hβ₀ hδ₀ hδ hmesh η hη j

theorem maxColumnSum_adjacent_le_half {n J : ℕ} {β β₀ δ : ℝ}
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (t : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η t a r) :
    maxColumnSum (DeletedPairConditionals.patchKernels (mesh_pos hmesh) (mesh_two_le hmesh)
      (Function.update η t a) (adjacentShapes t r) d β) ≤ 1 / 2 := by
  unfold maxColumnSum
  apply csSup_le (range_nonempty _)
  rintro _ ⟨j, rfl⟩
  exact column_adjacent_le_half d hβ hβ₀ hδ₀ hδ hmesh η t a r hadm j

/-- Actual section variances are integrable under the actual patch law.
No global measurability representative is added as a hypothesis to MemLp. -/
theorem integrable_patch_kernelVariance {n J : ℕ} (hn : 2 ≤ n + 1)
    (hJ : 0 < J) (hJ2 : 2 ≤ J) (A : Fin (n + 1) → MeshIndex J)
    (B : Fin (n + 1) → Patch) (d : Option (DeletedPairEnsemble.Pair (n + 1)))
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (f : PatchCoordinates hJ A B → ℝ)
    (hf : MemLp f 2 (DeletedPairConditionals.patchLaw hJ hJ2 A B d β))
    (i : Fin (n + 1)) :
    Integrable (fun X ↦ ProbabilityTheory.variance (fun z ↦ f (Function.update X i z))
      (DeletedPairConditionals.patchKernels hJ hJ2 A B d β i X))
      (DeletedPairConditionals.patchLaw hJ hJ2 A B d β) := by
  let hp : IsProbabilityMeasure (DeletedPairConditionals.patchLaw hJ hJ2 A B d β) :=
    DeletedPairConditionals.patchLaw_probability hJ hJ2 hn A B d hβ hsub
  have h := ConditionalVarianceIntegral.integrable_kernelVariance
    (DeletedPairConditionals.patchKernels hJ hJ2 A B d β)
    (DeletedPairConditionals.patchLaw hJ hJ2 A B d β)
    (DeletedPairConditionals.independentSite_patchKernels hJ hJ2 A B d β)
    (DeletedPairConditionals.preservesLaw_patchKernels hJ hJ2 hn A B d hβ hsub) hf i
  exact h

/-- The literal variance statement for every L2 function on the prescribed
cell product, for the original law or one specified deleted pair. -/
theorem cells_variance {n J : ℕ} (hn : 2 ≤ n + 1) {β β₀ δ : ℝ}
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hsub : β₀ < 4) (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (f : PatchCoordinates (mesh_pos hmesh) η (fun _ ↦ .cell) → ℝ)
    (hf : MemLp f 2 (DeletedPairConditionals.patchLaw (mesh_pos hmesh)
      (mesh_two_le hmesh) η (fun _ ↦ .cell) d β)) :
    let μ := DeletedPairConditionals.patchLaw (mesh_pos hmesh)
      (mesh_two_le hmesh) η (fun _ ↦ .cell) d β
    let κ := DeletedPairConditionals.patchKernels (mesh_pos hmesh)
      (mesh_two_le hmesh) η (fun _ ↦ .cell) d β
    ProbabilityTheory.variance f μ ≤
      2 * ∑ i, ∫ X, ProbabilityTheory.variance (fun z ↦ f (Function.update X i z)) (κ i X) ∂μ := by
  let μ := DeletedPairConditionals.patchLaw (mesh_pos hmesh)
    (mesh_two_le hmesh) η (fun _ ↦ .cell) d β
  let κ := DeletedPairConditionals.patchKernels (mesh_pos hmesh)
    (mesh_two_le hmesh) η (fun _ ↦ .cell) d β
  let hp : IsProbabilityMeasure μ := DeletedPairConditionals.patchLaw_probability
    (mesh_pos hmesh) (mesh_two_le hmesh) hn η (fun _ ↦ .cell) d hβ (hβ₀.trans_lt hsub)
  have h := ConditionalVarianceIntegral.variance_le_twice_kernel_variances κ μ
    (DeletedPairConditionals.independentSite_patchKernels
      (mesh_pos hmesh) (mesh_two_le hmesh) η (fun _ ↦ .cell) d β)
    (DeletedPairConditionals.preservesLaw_patchKernels (mesh_pos hmesh)
      (mesh_two_le hmesh) hn η (fun _ ↦ .cell) d hβ (hβ₀.trans_lt hsub))
    (maxColumnSum_cells_le_half d hβ hβ₀ hδ₀.le hδ hmesh η hη) hf
  change ProbabilityTheory.variance f μ ≤
    2 * ∑ i, ∫ X, ProbabilityTheory.variance (fun z ↦ f (Function.update X i z)) (κ i X) ∂μ
  simpa only [ConditionalVarianceIntegral.kernelVariance] using h

/-- The same literal inequality on the actual single-adjacent product.
Both endpoint completions are required before choosing any outside point. -/
theorem adjacent_variance {n J : ℕ} (hn : 2 ≤ n + 1) {β β₀ δ : ℝ}
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hsub : β₀ < 4) (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (t : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η t a r)
    (f : PatchCoordinates (mesh_pos hmesh) (Function.update η t a) (adjacentShapes t r) → ℝ)
    (hf : MemLp f 2 (DeletedPairConditionals.patchLaw (mesh_pos hmesh) (mesh_two_le hmesh)
      (Function.update η t a) (adjacentShapes t r) d β)) :
    let A := Function.update η t a
    let B := adjacentShapes t r
    let μ := DeletedPairConditionals.patchLaw (mesh_pos hmesh) (mesh_two_le hmesh) A B d β
    let κ := DeletedPairConditionals.patchKernels (mesh_pos hmesh) (mesh_two_le hmesh) A B d β
    ProbabilityTheory.variance f μ ≤
      2 * ∑ i, ∫ X, ProbabilityTheory.variance (fun z ↦ f (Function.update X i z)) (κ i X) ∂μ := by
  let A := Function.update η t a
  let B := adjacentShapes t r
  let μ := DeletedPairConditionals.patchLaw (mesh_pos hmesh) (mesh_two_le hmesh) A B d β
  let κ := DeletedPairConditionals.patchKernels (mesh_pos hmesh) (mesh_two_le hmesh) A B d β
  let hp : IsProbabilityMeasure μ := DeletedPairConditionals.patchLaw_probability
    (mesh_pos hmesh) (mesh_two_le hmesh) hn A B d hβ (hβ₀.trans_lt hsub)
  have h := ConditionalVarianceIntegral.variance_le_twice_kernel_variances κ μ
    (DeletedPairConditionals.independentSite_patchKernels (mesh_pos hmesh) (mesh_two_le hmesh) A B d β)
    (DeletedPairConditionals.preservesLaw_patchKernels (mesh_pos hmesh)
      (mesh_two_le hmesh) hn A B d hβ (hβ₀.trans_lt hsub))
    (maxColumnSum_adjacent_le_half d hβ hβ₀ hδ₀.le hδ hmesh η t a r hadm) hf
  change ProbabilityTheory.variance f μ ≤
    2 * ∑ i, ∫ X, ProbabilityTheory.variance (fun z ↦ f (Function.update X i z)) (κ i X) ∂μ
  simpa only [ConditionalVarianceIntegral.kernelVariance] using h

end PeriodicAttractiveLogGas.DeletedConditionalVariance
