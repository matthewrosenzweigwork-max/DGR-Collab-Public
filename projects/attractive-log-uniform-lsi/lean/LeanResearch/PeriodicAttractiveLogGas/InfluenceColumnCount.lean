import LeanResearch.PeriodicAttractiveLogGas.ConditionalLawEstimates
import LeanResearch.PeriodicAttractiveLogGas.CoordinateOscillation

/-! Actual occupation counting in the column estimate of Proposition 3.8.
The exceptional adjacent coordinate is assigned to a genuinely capped
endpoint completion. No near-coordinate count is assumed. -/

noncomputable section
open Set
open scoped BigOperators

namespace PeriodicAttractiveLogGas.InfluenceColumnCount

open MeshCells MeshAdjacentCells MeshNearbyGeometry GreenPointWeights
  LabelOccupations OneCoordinateConditionals ConditionalParameters ConditionalLawEstimates

def patchCells {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) : Patch → Finset (MeshIndex J)
  | .cell => {a}
  | .edge r => {a, nextCell J hJ a r}

def nearCells {J : ℕ} (R : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    Patch → Finset (MeshIndex J)
  | .cell => nearbyCells (R + 1) a
  | .edge r => nearbyEdgeCells J hJ (R + 1) a r

theorem mem_nearCells {J R : ℕ} (hJ : 0 < J) (a c : MeshIndex J) (b : Patch) :
    c ∈ nearCells R hJ a b ↔
      ∃ v ∈ patchCells hJ a b, periodicIndexDistance c v ≤ R + 1 := by
  cases b with
  | cell => simp [nearCells, patchCells, periodicIndexDistance_comm c a]
  | edge r =>
    simp [nearCells, patchCells, periodicIndexDistance_comm c a,
      periodicIndexDistance_comm c (nextCell J hJ a r)]

def Near {J N : ℕ} (R : ℕ) (hJ : 0 < J) (a : Fin N → MeshIndex J)
    (b : Fin N → Patch) (i j : Fin N) : Prop :=
  ∃ u ∈ patchCells hJ (a i) (b i), u ∈ nearCells R hJ (a j) (b j)

theorem near_iff {J N R : ℕ} (hJ : 0 < J) (a : Fin N → MeshIndex J)
    (b : Fin N → Patch) (i j : Fin N) :
    Near R hJ a b i j ↔ ∃ u ∈ patchCells hJ (a i) (b i),
      ∃ v ∈ patchCells hJ (a j) (b j), periodicIndexDistance u v ≤ R + 1 := by
  simp only [Near, mem_nearCells]

def nearTargets {J N : ℕ} (R : ℕ) (hJ : 0 < J) (a : Fin N → MeshIndex J)
    (b : Fin N → Patch) (j : Fin N) : Finset (Fin N) := by
  classical
  exact (Finset.univ.erase j).filter fun i ↦ Near R hJ a b i j

theorem mem_nearTargets {J N R : ℕ} (hJ : 0 < J) (a : Fin N → MeshIndex J)
    (b : Fin N → Patch) (i j : Fin N) :
    i ∈ nearTargets R hJ a b j ↔ i ≠ j ∧ Near R hJ a b i j := by
  classical
  simp [nearTargets]

theorem card_nearCells_le {J R : ℕ} (hJ : 0 < J) (a : MeshIndex J) (b : Patch) :
    (nearCells R hJ a b).card ≤ (2 * R + 4) ^ 2 := by
  have he : 2 * (R + 1) + 2 = 2 * R + 4 := by omega
  cases b with
  | cell => simpa only [nearCells, he] using card_nearbyCells_le J hJ (R + 1) a
  | edge r => simpa only [nearCells, he] using card_nearbyEdgeCells_le J hJ (R + 1) a r

theorem nearTargets_cells_subset {J N R : ℕ} (hJ : 0 < J) (η : LabelVector J N)
    (j : Fin N) : nearTargets R hJ η (fun _ ↦ .cell) j ⊆
      sourceIndices η Finset.univ (nearCells R hJ (η j) .cell) := by
  classical
  intro i hi
  have hn := ((mem_nearTargets hJ η (fun _ ↦ .cell) i j).mp hi).2
  apply (mem_sourceIndices _ _ _ _).mpr
  exact ⟨Finset.mem_univ _, by simpa [Near, patchCells] using hn⟩

/-- Choose the exceptional target's endpoint that witnesses nearness. If it
is the source, its excluded diagonal creates no extra target. -/
theorem exists_capped_near_completion {J N R : ℕ} (hJ : 0 < J) {δ : ℝ}
    (η : LabelVector J N) (t : Fin N) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible hJ δ η t a r) (j : Fin N) :
    ∃ ζ : LabelVector J N, OccupationCap δ ζ ∧
      nearTargets R hJ (Function.update η t a) (adjacentShapes t r) j ⊆
        sourceIndices ζ Finset.univ
          (nearCells R hJ (Function.update η t a j) (adjacentShapes t r j)) := by
  classical
  let A := Function.update η t a
  let B := adjacentShapes t r
  let S := nearCells R hJ (A j) (B j)
  have ho (i : Fin N) (hi : i ≠ t) (hn : Near R hJ A B i j) : η i ∈ S := by
    simpa [Near, A, B, adjacentShapes, patchCells, hi, S] using hn
  have hc (u : MeshIndex J) (hu : u ∈ patchCells hJ (A t) (B t)) :
      OccupationCap δ (Function.update η t u) := by
    have hu' : u = a ∨ u = nextCell J hJ a r := by
      simpa [patchCells, A, B, adjacentShapes] using hu
    rcases hu' with rfl | rfl
    · exact hadm.1
    · exact hadm.2
  by_cases ht : Near R hJ A B t j
  · obtain ⟨u, hu, huS⟩ := ht
    refine ⟨Function.update η t u, hc u hu, ?_⟩
    intro i hi
    have hn := ((mem_nearTargets hJ A B i j).mp hi).2
    apply (mem_sourceIndices _ _ _ _).mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_cases hit : i = t
    · subst i
      simpa only [Function.update_self] using huS
    · simpa [hit] using ho i hit hn
  · refine ⟨Function.update η t a, hadm.1, ?_⟩
    intro i hi
    have hn := ((mem_nearTargets hJ A B i j).mp hi).2
    have hit : i ≠ t := by rintro rfl; exact ht hn
    apply (mem_sourceIndices _ _ _ _).mpr
    exact ⟨Finset.mem_univ _, by simpa [hit] using ho i hit hn⟩

theorem count_le_of_capped_selection {J N R : ℕ} (hJ : 0 < J) {δ : ℝ}
    (hδ : 0 ≤ δ) {ζ : LabelVector J N} (hζ : OccupationCap δ ζ)
    (I : Finset (Fin N)) (a : MeshIndex J) (b : Patch)
    (hI : I ⊆ sourceIndices ζ Finset.univ (nearCells R hJ a b)) :
    (I.card : ℝ) ≤ 2 * (2 * (R : ℝ) + 5) ^ 2 * δ * N := by
  have hc : (I.card : ℝ) ≤ ((sourceIndices ζ Finset.univ (nearCells R hJ a b)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hI
  have hn : ((nearCells R hJ a b).card : ℝ) ≤ (2 * (R : ℝ) + 4) ^ 2 := by
    exact_mod_cast card_nearCells_le hJ a b
  have hb : (2 * (R : ℝ) + 4) ^ 2 ≤ 2 * (2 * (R : ℝ) + 5) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ R from Nat.cast_nonneg R]
  calc
    (I.card : ℝ) ≤ ((nearCells R hJ a b).card : ℝ) * (δ * N) :=
      hc.trans (source_count_le hζ Finset.univ _)
    _ ≤ (2 * (R : ℝ) + 4) ^ 2 * (δ * N) :=
      mul_le_mul_of_nonneg_right hn (mul_nonneg hδ (Nat.cast_nonneg N))
    _ ≤ (2 * (2 * (R : ℝ) + 5) ^ 2) * (δ * N) :=
      mul_le_mul_of_nonneg_right hb (mul_nonneg hδ (Nat.cast_nonneg N))
    _ = _ := by ring

theorem nearTargets_cells_count {J N R : ℕ} (hJ : 0 < J) {δ : ℝ} (hδ : 0 ≤ δ)
    (η : LabelVector J N) (hη : OccupationCap δ η) (j : Fin N) :
    ((nearTargets R hJ η (fun _ ↦ .cell) j).card : ℝ) ≤
      2 * (2 * (R : ℝ) + 5) ^ 2 * δ * N :=
  count_le_of_capped_selection hJ hδ hη _ _ _ (nearTargets_cells_subset hJ η j)

theorem nearTargets_adjacent_count {J N R : ℕ} (hJ : 0 < J) {δ : ℝ} (hδ : 0 ≤ δ)
    (η : LabelVector J N) (t : Fin N) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible hJ δ η t a r) (j : Fin N) :
    ((nearTargets R hJ (Function.update η t a) (adjacentShapes t r) j).card : ℝ) ≤
      2 * (2 * (R : ℝ) + 5) ^ 2 * δ * N := by
  obtain ⟨ζ, hζ, hsub⟩ := exists_capped_near_completion hJ η t a r hadm j
  exact count_le_of_capped_selection hJ hδ hζ _ _ _ hsub

/-- The far allowance is paid at most N times. Near targets are counted
exactly and retain their own bound; no ordering of the two bounds is needed. -/
theorem column_le_near_count {J N R : ℕ} (hJ : 0 < J)
    (a : Fin N → MeshIndex J) (b : Fin N → Patch) (c : Fin N → Fin N → ℝ)
    (j : Fin N) {A B : ℝ} (hB : 0 ≤ B)
    (hnear : ∀ i, i ≠ j → Near R hJ a b i j → c i j ≤ A)
    (hfar : ∀ i, i ≠ j → ¬Near R hJ a b i j → c i j ≤ B) :
    (∑ i ∈ Finset.univ.erase j, c i j) ≤
      ((nearTargets R hJ a b j).card : ℝ) * A + N * B := by
  classical
  have hp (i : Fin N) (hi : i ∈ Finset.univ.erase j) :
      c i j ≤ (if Near R hJ a b i j then A else 0) + B := by
    have hij := (Finset.mem_erase.mp hi).1
    split_ifs with hn
    ·
      exact (hnear i hij hn).trans (le_add_of_nonneg_right hB)
    · simpa only [zero_add] using hfar i hij hn
  have hs : (∑ i ∈ Finset.univ.erase j, if Near R hJ a b i j then A else 0) =
      ((nearTargets R hJ a b j).card : ℝ) * A := by
    rw [← Finset.sum_filter]
    simp [nearTargets]
  have hc : ((Finset.univ.erase j).card : ℝ) ≤ N := by
    have hc' : (Finset.univ.erase j).card ≤ N := by
      simp
    exact_mod_cast hc'
  calc
    _ ≤ ∑ i ∈ Finset.univ.erase j, ((if Near R hJ a b i j then A else 0) + B) :=
      Finset.sum_le_sum hp
    _ = ((nearTargets R hJ a b j).card : ℝ) * A + ((Finset.univ.erase j).card : ℝ) * B := by
      rw [Finset.sum_add_distrib, hs]
      simp
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hc hB)

def nearInfluenceBound (β₀ : ℝ) (N : ℕ) : ℝ :=
  (2 * β₀ / N) * densityNormBound β₀ *
    (PoleLogMoments.lambdaStar (radius β₀) + kernelConstant)

def farInfluenceBound (β₀ : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt 5 * β₀ * kernelConstant / ((N : ℝ) * radius β₀)

theorem nearInfluenceBound_nonneg {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (N : ℕ) :
    0 ≤ nearInfluenceBound β₀ N := by
  have hK := (densityNormBound_pos β₀).le
  have hL := PoleLogMoments.lambdaStar_nonneg
    (show (1 : ℝ) ≤ radius β₀ by exact_mod_cast radius_one_le β₀)
  have hC := kernelConstant_pos.le
  unfold nearInfluenceBound
  positivity

theorem farInfluenceBound_nonneg {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (N : ℕ) :
    0 ≤ farInfluenceBound β₀ N := by
  have hC := kernelConstant_pos.le
  unfold farInfluenceBound
  positivity

theorem column_le_half_of_count {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β₀ δ : ℝ} (hβ₀ : 0 ≤ β₀) (hδ : δ ≤ occupationBound β₀)
    (a : Fin N → MeshIndex J) (b : Fin N → Patch) (c : Fin N → Fin N → ℝ)
    (j : Fin N)
    (hcount : ((nearTargets (radius β₀) hJ a b j).card : ℝ) ≤
      2 * (2 * (radius β₀ : ℝ) + 5) ^ 2 * δ * N)
    (hnear : ∀ i, i ≠ j → Near (radius β₀) hJ a b i j → c i j ≤ nearInfluenceBound β₀ N)
    (hfar : ∀ i, i ≠ j → ¬Near (radius β₀) hJ a b i j → c i j ≤ farInfluenceBound β₀ N) :
    (∑ i ∈ Finset.univ.erase j, c i j) ≤ 1 / 2 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hK := (densityNormBound_pos β₀).le
  have hL := PoleLogMoments.lambdaStar_nonneg
    (show (1 : ℝ) ≤ radius β₀ by exact_mod_cast radius_one_le β₀)
  have hC := kernelConstant_pos.le
  have hn : ((nearTargets (radius β₀) hJ a b j).card : ℝ) * nearInfluenceBound β₀ N ≤
      1 / 4 := by
    calc
      _ ≤ (2 * (2 * (radius β₀ : ℝ) + 5) ^ 2 * δ * N) * nearInfluenceBound β₀ N :=
        mul_le_mul_of_nonneg_right hcount (nearInfluenceBound_nonneg hβ₀ N)
      _ = 4 * β₀ * (2 * (radius β₀ : ℝ) + 5) ^ 2 * δ * densityNormBound β₀ *
          (PoleLogMoments.lambdaStar (radius β₀) + kernelConstant) := by
        unfold nearInfluenceBound
        field_simp
        ring
      _ ≤ 4 * β₀ * (2 * (radius β₀ : ℝ) + 5) ^ 2 * occupationBound β₀ * densityNormBound β₀ *
          (PoleLogMoments.lambdaStar (radius β₀) + kernelConstant) := by
        gcongr
      _ ≤ 1 / 4 := (chosen_parameters β₀ hβ₀).2.2.2
  have hf : (N : ℝ) * farInfluenceBound β₀ N ≤ 1 / 4 := by
    calc
      _ = oscillationBound β₀ kernelConstant (radius β₀) := by
        unfold farInfluenceBound oscillationBound
        field_simp
      _ ≤ _ := chosen_far_oscillation β₀
  exact (column_le_near_count hJ a b c j (farInfluenceBound_nonneg hβ₀ N) hnear hfar).trans
    (by linarith)

theorem column_cells_le_half {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β₀ δ : ℝ} (hβ₀ : 0 ≤ β₀) (hδ₀ : 0 ≤ δ) (hδ : δ ≤ occupationBound β₀)
    (η : LabelVector J N) (hη : OccupationCap δ η) (c : Fin N → Fin N → ℝ) (j : Fin N)
    (hnear : ∀ i, i ≠ j → Near (radius β₀) hJ η (fun _ ↦ .cell) i j →
      c i j ≤ nearInfluenceBound β₀ N)
    (hfar : ∀ i, i ≠ j → ¬Near (radius β₀) hJ η (fun _ ↦ .cell) i j →
      c i j ≤ farInfluenceBound β₀ N) :
    (∑ i ∈ Finset.univ.erase j, c i j) ≤ 1 / 2 :=
  column_le_half_of_count hJ hN hβ₀ hδ η (fun _ ↦ .cell) c j
    (nearTargets_cells_count hJ hδ₀ η hη j) hnear hfar

theorem column_adjacent_le_half {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β₀ δ : ℝ} (hβ₀ : 0 ≤ β₀) (hδ₀ : 0 ≤ δ) (hδ : δ ≤ occupationBound β₀)
    (η : LabelVector J N) (t : Fin N) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible hJ δ η t a r) (c : Fin N → Fin N → ℝ) (j : Fin N)
    (hnear : ∀ i, i ≠ j → Near (radius β₀) hJ (Function.update η t a)
      (adjacentShapes t r) i j → c i j ≤ nearInfluenceBound β₀ N)
    (hfar : ∀ i, i ≠ j → ¬Near (radius β₀) hJ (Function.update η t a)
      (adjacentShapes t r) i j → c i j ≤ farInfluenceBound β₀ N) :
    (∑ i ∈ Finset.univ.erase j, c i j) ≤ 1 / 2 :=
  column_le_half_of_count hJ hN hβ₀ hδ _ _ c j
    (nearTargets_adjacent_count hJ hδ₀ η t a r hadm j) hnear hfar

end PeriodicAttractiveLogGas.InfluenceColumnCount
