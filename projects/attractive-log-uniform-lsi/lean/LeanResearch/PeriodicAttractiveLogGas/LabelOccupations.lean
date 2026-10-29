import LeanResearch.PeriodicAttractiveLogGas.MeshNearbyGeometry
import LeanResearch.PeriodicAttractiveLogGas.ConditionalParameters
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! SOURCE_ONLY candidate for the prescribed-label occupation counts in source
lines 344–355 and the finite weight calculation in `prop:one-particle`, lines
543–568. Every source family is an actual finite subset of `Fin N`. Completion
is `Function.update`; two-endpoint admissibility requires both completions.
No conditional-law, marginal-law, disintegration, or positional-separation
assertion is made here. This source has not been elaborated by its author.
-/

noncomputable section
open Set
open scoped BigOperators ENNReal NNReal

namespace PeriodicAttractiveLogGas.LabelOccupations

open MeshCells MeshAdjacentCells MeshNearbyGeometry ConditionalParameters

abbrev LabelVector (J N : ℕ) := Fin N → MeshIndex J

/-- The number of particles with the prescribed label `a`. -/
def occupation {J N : ℕ} (η : LabelVector J N) (a : MeshIndex J) : ℕ :=
  (Finset.univ.filter fun i ↦ η i = a).card

/-- The maximum-occupation condition, written without a choice of maximum. -/
def OccupationCap {J N : ℕ} (δ : ℝ) (η : LabelVector J N) : Prop :=
  ∀ a : MeshIndex J, (occupation η a : ℝ) ≤ δ * N

def goodLabels (J N : ℕ) (δ : ℝ) : Set (LabelVector J N) :=
  {η | OccupationCap δ η}

/-- The source's occupation-vector cap, including its exact total mass. -/
def cappedOccupations (J N : ℕ) (δ : ℝ) : Set (MeshIndex J → ℕ) :=
  {n | (∑ a, n a) = N ∧ ∀ a, (n a : ℝ) ≤ δ * N}

theorem sum_occupation {J N : ℕ} (η : LabelVector J N) :
    ∑ a, occupation η a = N := by
  simpa only [occupation, Finset.mem_univ, Finset.filter_true, Finset.card_univ,
    Fintype.card_fin] using
    (Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin N))
      (Finset.univ : Finset (MeshIndex J)) η)

theorem occupation_mem_cappedOccupations_iff {J N : ℕ} {δ : ℝ}
    (η : LabelVector J N) :
    occupation η ∈ cappedOccupations J N δ ↔ OccupationCap δ η := by
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨sum_occupation η, h⟩⟩

theorem occupation_at_label_pos {J N : ℕ} (η : LabelVector J N) (i : Fin N) :
    1 ≤ occupation η (η i) := by
  apply Finset.one_le_card.mpr
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

theorem one_le_cap_mass {J N : ℕ} {δ : ℝ} (hN : 0 < N)
    {η : LabelVector J N} (hη : OccupationCap δ η) : 1 ≤ δ * N := by
  let i : Fin N := ⟨0, hN⟩
  have hi : (1 : ℝ) ≤ (occupation η (η i) : ℝ) := by
    exact_mod_cast occupation_at_label_pos η i
  exact hi.trans (hη (η i))

theorem nonempty_goodLabels_one_le {J N : ℕ} {δ : ℝ} (hN : 0 < N)
    (h : (goodLabels J N δ).Nonempty) : 1 ≤ δ * N := by
  obtain ⟨η, hη⟩ := h
  exact one_le_cap_mass hN hη

theorem OccupationCap.mono {J N : ℕ} {δ t : ℝ} {η : LabelVector J N}
    (hη : OccupationCap δ η) (hδt : δ ≤ t) : OccupationCap t η := by
  intro a
  exact (hη a).trans (mul_le_mul_of_nonneg_right hδt (Nat.cast_nonneg N))

/-- A prescribed subfamily, selected by a finite set of prescribed cell labels. -/
def sourceIndices {J N : ℕ} (η : LabelVector J N) (I : Finset (Fin N))
    (S : Finset (MeshIndex J)) : Finset (Fin N) := I.filter fun i ↦ η i ∈ S

@[simp] theorem mem_sourceIndices {J N : ℕ} (η : LabelVector J N)
    (I : Finset (Fin N)) (S : Finset (MeshIndex J)) (i : Fin N) :
    i ∈ sourceIndices η I S ↔ i ∈ I ∧ η i ∈ S := Finset.mem_filter

theorem sourceIndices_card_eq_sum_fibers {J N : ℕ} (η : LabelVector J N)
    (I : Finset (Fin N)) (S : Finset (MeshIndex J)) :
    (sourceIndices η I S).card = ∑ a ∈ S, (I.filter fun i ↦ η i = a).card :=
  (Finset.sum_card_fiberwise_eq_card_filter I S η).symm

theorem sourceIndices_card_le_sum_occupation {J N : ℕ} (η : LabelVector J N)
    (I : Finset (Fin N)) (S : Finset (MeshIndex J)) :
    (sourceIndices η I S).card ≤ ∑ a ∈ S, occupation η a := by
  rw [sourceIndices_card_eq_sum_fibers]
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩

theorem source_count_le {J N : ℕ} {δ : ℝ} {η : LabelVector J N}
    (hη : OccupationCap δ η) (I : Finset (Fin N)) (S : Finset (MeshIndex J)) :
    ((sourceIndices η I S).card : ℝ) ≤ (S.card : ℝ) * (δ * N) := by
  calc
    _ ≤ ((∑ a ∈ S, occupation η a : ℕ) : ℝ) := by
      exact_mod_cast sourceIndices_card_le_sum_occupation η I S
    _ = ∑ a ∈ S, (occupation η a : ℝ) := by rw [Nat.cast_sum]
    _ ≤ ∑ _a ∈ S, δ * N := Finset.sum_le_sum fun a _ ↦ hη a
    _ = _ := by simp

theorem source_count_le_mesh_bound {J N R : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    {η : LabelVector J N} (hη : OccupationCap δ η) (I : Finset (Fin N))
    (S : Finset (MeshIndex J)) (hS : S.card ≤ (2 * R + 2) ^ 2) :
    ((sourceIndices η I S).card : ℝ) ≤ (2 * (R : ℝ) + 2) ^ 2 * (δ * N) := by
  have hSr : (S.card : ℝ) ≤ (2 * (R : ℝ) + 2) ^ 2 := by exact_mod_cast hS
  exact (source_count_le hη I S).trans
    (mul_le_mul_of_nonneg_right hSr (mul_nonneg hδ (Nat.cast_nonneg N)))

theorem nearby_cell_source_count_le {J N R : ℕ} (hJ : 0 < J) {δ : ℝ} (hδ : 0 ≤ δ)
    {η : LabelVector J N} (hη : OccupationCap δ η) (I : Finset (Fin N)) (a : MeshIndex J) :
    ((sourceIndices η I (nearbyCells R a)).card : ℝ) ≤
      (2 * (R : ℝ) + 2) ^ 2 * (δ * N) :=
  source_count_le_mesh_bound hδ hη I _ (card_nearbyCells_le J hJ R a)

theorem nearby_edge_source_count_le {J N R : ℕ} (hJ : 0 < J) {δ : ℝ} (hδ : 0 ≤ δ)
    {η : LabelVector J N} (hη : OccupationCap δ η) (I : Finset (Fin N))
    (a : MeshIndex J) (j : Fin 2) :
    ((sourceIndices η I (nearbyEdgeCells J hJ R a j)).card : ℝ) ≤
      (2 * (R : ℝ) + 2) ^ 2 * (δ * N) :=
  source_count_le_mesh_bound hδ hη I _ (card_nearbyEdgeCells_le J hJ R a j)

def sourceWeight {J N : ℕ} (η : LabelVector J N) (I : Finset (Fin N))
    (S : Finset (MeshIndex J)) (w : Fin N → ℝ) : ℝ :=
  ∑ i ∈ sourceIndices η I S, w i

theorem sourceWeight_eq_sum_ite {J N : ℕ} (η : LabelVector J N)
    (I : Finset (Fin N)) (S : Finset (MeshIndex J)) (w : Fin N → ℝ) :
    sourceWeight η I S w = ∑ i ∈ I, if η i ∈ S then w i else 0 := by
  rw [sourceWeight, sourceIndices, Finset.sum_filter]

@[simp] theorem sourceWeight_univ {J N : ℕ} (η : LabelVector J N)
    (I : Finset (Fin N)) (w : Fin N → ℝ) :
    sourceWeight η I Finset.univ w = ∑ i ∈ I, w i := by
  simp [sourceWeight, sourceIndices]

theorem sourceWeight_nonneg {J N : ℕ} (η : LabelVector J N)
    (I : Finset (Fin N)) (S : Finset (MeshIndex J)) {w : Fin N → ℝ}
    (hw : ∀ i ∈ I, 0 ≤ w i) : 0 ≤ sourceWeight η I S w := by
  exact Finset.sum_nonneg fun i hi ↦ hw i ((mem_sourceIndices η I S i).mp hi).1

theorem zero_coupling_sourceWeight {J N : ℕ} (η : LabelVector J N)
    (I : Finset (Fin N)) (S : Finset (MeshIndex J)) {w : Fin N → ℝ}
    (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ (0 : ℝ) / N) :
    sourceWeight η I S w = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hiI := ((mem_sourceIndices η I S i).mp hi).1
  exact le_antisymm (by simpa only [zero_div] using hw i hiI) (hw₀ i hiI)

theorem sum_weights_le_card_mul {N : ℕ} (I : Finset (Fin N)) {w : Fin N → ℝ} {c : ℝ}
    (hw : ∀ i ∈ I, w i ≤ c) : ∑ i ∈ I, w i ≤ (I.card : ℝ) * c := by
  calc
    _ ≤ ∑ _i ∈ I, c := Finset.sum_le_sum hw
    _ = _ := by simp

/-- No positivity of `β` is needed: only its nonnegativity is used. -/
theorem total_source_weight_le {N : ℕ} (hN : 0 < N) {β β₀ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (I : Finset (Fin N)) {w : Fin N → ℝ}
    (hw : ∀ i ∈ I, w i ≤ β / N) : ∑ i ∈ I, w i ≤ β₀ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcardNat : I.card ≤ N := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_le_card (Finset.subset_univ I))
  have hcard : (I.card : ℝ) ≤ N := by
    exact_mod_cast hcardNat
  calc
    _ ≤ (I.card : ℝ) * (β / N) := sum_weights_le_card_mul I hw
    _ ≤ (N : ℝ) * (β / N) := mul_le_mul_of_nonneg_right hcard (div_nonneg hβ hNr.le)
    _ = β := by field_simp [hNr.ne']
    _ ≤ β₀ := hβ₀

/-- The finite source count gives the exact capped total for any label set. -/
theorem sourceWeight_le {J N : ℕ} (hN : 0 < N) {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : 0 ≤ δ) {η : LabelVector J N}
    (hη : OccupationCap δ η) (I : Finset (Fin N)) (S : Finset (MeshIndex J))
    {w : Fin N → ℝ} (hw : ∀ i ∈ I, w i ≤ β / N) :
    sourceWeight η I S w ≤ β₀ * (S.card : ℝ) * δ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ ((sourceIndices η I S).card : ℝ) * (β / N) :=
      sum_weights_le_card_mul _ fun i hi ↦ hw i ((mem_sourceIndices η I S i).mp hi).1
    _ ≤ ((S.card : ℝ) * (δ * N)) * (β / N) :=
      mul_le_mul_of_nonneg_right (source_count_le hη I S) (div_nonneg hβ hNr.le)
    _ = β * (S.card : ℝ) * δ := by field_simp [hNr.ne']
    _ ≤ β₀ * (S.card : ℝ) * δ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hβ₀ (Nat.cast_nonneg _)) hδ

theorem sourceWeight_le_mesh_bound {J N R : ℕ} (hN : 0 < N) {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : 0 ≤ δ) {η : LabelVector J N}
    (hη : OccupationCap δ η) (I : Finset (Fin N)) (S : Finset (MeshIndex J))
    (hS : S.card ≤ (2 * R + 2) ^ 2) {w : Fin N → ℝ}
    (hw : ∀ i ∈ I, w i ≤ β / N) :
    sourceWeight η I S w ≤ β₀ * (2 * (R : ℝ) + 2) ^ 2 * δ := by
  have hSr : (S.card : ℝ) ≤ (2 * (R : ℝ) + 2) ^ 2 := by exact_mod_cast hS
  exact (sourceWeight_le hN hβ hβ₀ hδ hη I S hw).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSr (hβ.trans hβ₀)) hδ)

theorem nearby_cell_weight_le {J N R : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β β₀ δ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : 0 ≤ δ)
    {η : LabelVector J N} (hη : OccupationCap δ η) (I : Finset (Fin N))
    (a : MeshIndex J) {w : Fin N → ℝ} (hw : ∀ i ∈ I, w i ≤ β / N) :
    sourceWeight η I (nearbyCells R a) w ≤ β₀ * (2 * (R : ℝ) + 2) ^ 2 * δ :=
  sourceWeight_le_mesh_bound hN hβ hβ₀ hδ hη I _ (card_nearbyCells_le J hJ R a) hw

theorem nearby_edge_weight_le {J N R : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β β₀ δ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : 0 ≤ δ)
    {η : LabelVector J N} (hη : OccupationCap δ η) (I : Finset (Fin N))
    (a : MeshIndex J) (j : Fin 2) {w : Fin N → ℝ} (hw : ∀ i ∈ I, w i ≤ β / N) :
    sourceWeight η I (nearbyEdgeCells J hJ R a j) w ≤
      β₀ * (2 * (R : ℝ) + 2) ^ 2 * δ :=
  sourceWeight_le_mesh_bound hN hβ hβ₀ hδ hη I _ (card_nearbyEdgeCells_le J hJ R a j) hw

/-- The first actual conditional-parameter restriction closes the smallness estimate. -/
theorem sourceWeight_le_one_sixteenth {J N R : ℕ} (hN : 0 < N) {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : 0 ≤ δ) {η : LabelVector J N}
    (hη : OccupationCap δ η) (I : Finset (Fin N)) (S : Finset (MeshIndex J))
    (hS : S.card ≤ (2 * R + 2) ^ 2) {w : Fin N → ℝ}
    (hw : ∀ i ∈ I, w i ≤ β / N)
    (hsmall : β₀ * (2 * (R : ℝ) + 2) ^ 2 * δ ≤ 1 / 16) :
    sourceWeight η I S w ≤ 1 / 16 :=
  (sourceWeight_le_mesh_bound hN hβ hβ₀ hδ hη I S hS hw).trans hsmall

/-- The concrete positive choice from `ConditionalParameters`, with no division by β. -/
theorem sourceWeight_occupationDelta_le {J N R : ℕ} (hN : 0 < N)
    {β β₀ K Λ C₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hK : 0 ≤ K) (hΛ : 0 ≤ Λ) (hC₀ : 0 ≤ C₀) {η : LabelVector J N}
    (hη : OccupationCap (occupationDelta β₀ R K Λ C₀) η)
    (I : Finset (Fin N)) (S : Finset (MeshIndex J))
    (hS : S.card ≤ (2 * R + 2) ^ 2) {w : Fin N → ℝ}
    (hw : ∀ i ∈ I, w i ≤ β / N) : sourceWeight η I S w ≤ 1 / 16 := by
  have hpar := occupationDelta_bounds (hβ.trans hβ₀) hK hΛ hC₀ R
  exact sourceWeight_le_one_sixteenth hN hβ hβ₀ hpar.1.le hη I S hS hw hpar.2.2.1

theorem sourceWeight_fixedDelta_le {J N : ℕ} (hN : 0 < N)
    {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    {η : LabelVector J N} (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (I : Finset (Fin N)) (S : Finset (MeshIndex J))
    (hS : S.card ≤ (2 * nearRadius β₀ C₁ + 2) ^ 2) {w : Fin N → ℝ}
    (hw : ∀ i ∈ I, w i ≤ β / N) : sourceWeight η I S w ≤ 1 / 16 := by
  have hpar := fixedDelta_bounds (hβ.trans hβ₀) hC₀ (C₁ := C₁)
  exact sourceWeight_le_one_sixteenth hN hβ hβ₀ hpar.1.le hη I S hS hw hpar.2.2.1

/-- All finite weight hypotheses needed before the geometric point-weight step. -/
theorem source_weight_bounds {J N R : ℕ} (hN : 0 < N) {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : 0 ≤ δ) {η : LabelVector J N}
    (hη : OccupationCap δ η) (I : Finset (Fin N)) (S : Finset (MeshIndex J))
    (hS : S.card ≤ (2 * R + 2) ^ 2) {w : Fin N → ℝ}
    (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (hsmall : β₀ * (2 * (R : ℝ) + 2) ^ 2 * δ ≤ 1 / 16) :
    0 ≤ (∑ i ∈ I, w i) ∧ (∑ i ∈ I, w i) ≤ β₀ ∧
      0 ≤ sourceWeight η I S w ∧ sourceWeight η I S w ≤ 1 / 16 :=
  ⟨Finset.sum_nonneg hw₀, total_source_weight_le hN hβ hβ₀ I hw,
    sourceWeight_nonneg η I S hw₀,
    sourceWeight_le_one_sixteenth hN hβ hβ₀ hδ hη I S hS hw hsmall⟩

theorem nearby_cell_fixed_weight_bounds {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    {η : LabelVector J N} (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (I : Finset (Fin N)) (a : MeshIndex J) {w : Fin N → ℝ}
    (hw₀ : ∀ k ∈ I, 0 ≤ w k) (hw : ∀ k ∈ I, w k ≤ β / N) :
    0 ≤ (∑ k ∈ I, w k) ∧ (∑ k ∈ I, w k) ≤ β₀ ∧
      0 ≤ sourceWeight η I (nearbyCells (nearRadius β₀ C₁) a) w ∧
      sourceWeight η I (nearbyCells (nearRadius β₀ C₁) a) w ≤ 1 / 16 := by
  have hpar := fixedDelta_bounds (hβ.trans hβ₀) hC₀ (C₁ := C₁)
  exact source_weight_bounds hN hβ hβ₀ hpar.1.le hη I _
    (card_nearbyCells_le J hJ (nearRadius β₀ C₁) a) hw₀ hw hpar.2.2.1

theorem nearby_edge_fixed_weight_bounds {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    {η : LabelVector J N} (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (I : Finset (Fin N)) (a : MeshIndex J) (j : Fin 2) {w : Fin N → ℝ}
    (hw₀ : ∀ k ∈ I, 0 ≤ w k) (hw : ∀ k ∈ I, w k ≤ β / N) :
    0 ≤ (∑ k ∈ I, w k) ∧ (∑ k ∈ I, w k) ≤ β₀ ∧
      0 ≤ sourceWeight η I (nearbyEdgeCells J hJ (nearRadius β₀ C₁) a j) w ∧
      sourceWeight η I (nearbyEdgeCells J hJ (nearRadius β₀ C₁) a j) w ≤ 1 / 16 := by
  have hpar := fixedDelta_bounds (hβ.trans hβ₀) hC₀ (C₁ := C₁)
  exact source_weight_bounds hN hβ hβ₀ hpar.1.le hη I _
    (card_nearbyEdgeCells_le J hJ (nearRadius β₀ C₁) a j) hw₀ hw hpar.2.2.1

/-- Replacing any one coefficient by zero preserves the actual coefficient bounds. -/
theorem coefficientBounds_update_zero {N : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (I : Finset (Fin N)) {w : Fin N → ℝ}
    (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N) (d : Fin N) :
    (∀ i ∈ I, 0 ≤ Function.update w d 0 i) ∧
      (∀ i ∈ I, Function.update w d 0 i ≤ β / N) := by
  constructor
  · intro i hi
    by_cases hid : i = d
    · subst i
      simp only [Function.update_self, le_refl]
    · simpa only [Function.update_of_ne hid] using hw₀ i hi
  · intro i hi
    by_cases hid : i = d
    · subst i
      simpa only [Function.update_self] using div_nonneg hβ (Nat.cast_nonneg N)
    · simpa only [Function.update_of_ne hid] using hw i hi

/-- The actual one-particle source family, omitting the variable particle. -/
def otherParticles {N : ℕ} (i : Fin N) : Finset (Fin N) := Finset.univ.erase i

@[simp] theorem mem_otherParticles {N : ℕ} (i j : Fin N) :
    j ∈ otherParticles i ↔ j ≠ i := by simp [otherParticles]

@[simp] theorem not_mem_otherParticles {N : ℕ} (i : Fin N) :
    i ∉ otherParticles i := by simp

theorem one_particle_weight_bounds {J N R : ℕ} (hN : 0 < N) {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : 0 ≤ δ) {η : LabelVector J N}
    (hη : OccupationCap δ η) (i : Fin N) (S : Finset (MeshIndex J))
    (hS : S.card ≤ (2 * R + 2) ^ 2)
    (hsmall : β₀ * (2 * (R : ℝ) + 2) ^ 2 * δ ≤ 1 / 16) :
    0 ≤ (∑ _j ∈ otherParticles i, β / N) ∧
      (∑ _j ∈ otherParticles i, β / N) ≤ β₀ ∧
      0 ≤ sourceWeight η (otherParticles i) S (fun _ ↦ β / N) ∧
      sourceWeight η (otherParticles i) S (fun _ ↦ β / N) ≤ 1 / 16 :=
  source_weight_bounds hN hβ hβ₀ hδ hη _ S hS
    (fun _ _ ↦ div_nonneg hβ (Nat.cast_nonneg N)) (fun _ _ ↦ le_rfl) hsmall

theorem one_particle_deleted_weight_bounds {J N R : ℕ} (hN : 0 < N) {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : 0 ≤ δ) {η : LabelVector J N}
    (hη : OccupationCap δ η) (i d : Fin N) (S : Finset (MeshIndex J))
    (hS : S.card ≤ (2 * R + 2) ^ 2)
    (hsmall : β₀ * (2 * (R : ℝ) + 2) ^ 2 * δ ≤ 1 / 16) :
    0 ≤ (∑ j ∈ otherParticles i, Function.update (fun _ : Fin N ↦ β / N) d 0 j) ∧
      (∑ j ∈ otherParticles i, Function.update (fun _ : Fin N ↦ β / N) d 0 j) ≤ β₀ ∧
      0 ≤ sourceWeight η (otherParticles i) S (Function.update (fun _ ↦ β / N) d 0) ∧
      sourceWeight η (otherParticles i) S (Function.update (fun _ ↦ β / N) d 0) ≤ 1 / 16 := by
  have hw := coefficientBounds_update_zero hβ (otherParticles i)
    (w := fun _ : Fin N ↦ β / N)
    (fun _ _ ↦ div_nonneg hβ (Nat.cast_nonneg N)) (fun _ _ ↦ le_rfl) d
  exact source_weight_bounds hN hβ hβ₀ hδ hη _ S hS hw.1 hw.2 hsmall

/-- Filling the distinguished coordinate does not alter the other labels. -/
def complete {J N : ℕ} (η : LabelVector J N) (i : Fin N) (a : MeshIndex J) :
    LabelVector J N := Function.update η i a

@[simp] theorem complete_self {J N : ℕ} (η : LabelVector J N)
    (i : Fin N) (a : MeshIndex J) : complete η i a i = a := Function.update_self _ _ _

theorem complete_of_ne {J N : ℕ} (η : LabelVector J N) (i k : Fin N)
    (a : MeshIndex J) (hk : k ≠ i) : complete η i a k = η k := Function.update_of_ne hk _ _

theorem sourceIndices_complete {J N : ℕ} (η : LabelVector J N) (i : Fin N)
    (a : MeshIndex J) (I : Finset (Fin N)) (S : Finset (MeshIndex J)) (hi : i ∉ I) :
    sourceIndices (complete η i a) I S = sourceIndices η I S := by
  unfold sourceIndices
  apply Finset.filter_congr
  intro k hk
  have hki : k ≠ i := by intro h; subst k; exact hi hk
  rw [complete_of_ne η i k a hki]

theorem sourceWeight_complete {J N : ℕ} (η : LabelVector J N) (i : Fin N)
    (a : MeshIndex J) (I : Finset (Fin N)) (S : Finset (MeshIndex J))
    (w : Fin N → ℝ) (hi : i ∉ I) :
    sourceWeight (complete η i a) I S w = sourceWeight η I S w := by
  unfold sourceWeight
  rw [sourceIndices_complete η i a I S hi]

/-- Any valid completion bounds the fixed, prescribed other-source count. -/
theorem source_count_le_of_completion {J N : ℕ} {δ : ℝ}
    (η : LabelVector J N) (i : Fin N) (a : MeshIndex J)
    (ha : OccupationCap δ (complete η i a)) (I : Finset (Fin N))
    (S : Finset (MeshIndex J)) (hi : i ∉ I) :
    ((sourceIndices η I S).card : ℝ) ≤ (S.card : ℝ) * (δ * N) := by
  rw [← sourceIndices_complete η i a I S hi]
  exact source_count_le ha I S

theorem sourceWeight_le_of_completion {J N : ℕ} (hN : 0 < N) {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : 0 ≤ δ) (η : LabelVector J N)
    (i : Fin N) (a : MeshIndex J) (ha : OccupationCap δ (complete η i a))
    (I : Finset (Fin N)) (S : Finset (MeshIndex J)) (hi : i ∉ I)
    {w : Fin N → ℝ} (hw : ∀ k ∈ I, w k ≤ β / N) :
    sourceWeight η I S w ≤ β₀ * (S.card : ℝ) * δ := by
  rw [← sourceWeight_complete η i a I S w hi]
  exact sourceWeight_le hN hβ hβ₀ hδ ha I S hw

/-- Both endpoints are required. One valid endpoint alone is not this predicate. -/
def TwoEndpointAdmissible {J N : ℕ} (δ : ℝ) (η : LabelVector J N) (i : Fin N)
    (a b : MeshIndex J) : Prop :=
  OccupationCap δ (complete η i a) ∧ OccupationCap δ (complete η i b)

def AdjacentAdmissible {J N : ℕ} (hJ : 0 < J) (δ : ℝ)
    (η : LabelVector J N) (i : Fin N) (a : MeshIndex J) (j : Fin 2) : Prop :=
  TwoEndpointAdmissible δ η i a (nextCell J hJ a j)

/-- Every label allowed for the probe must give a valid completed vector. -/
def ProbeAdmissible {J N : ℕ} (δ : ℝ) (η : LabelVector J N) (i : Fin N)
    (A : Finset (MeshIndex J)) : Prop :=
  ∀ a ∈ A, OccupationCap δ (complete η i a)

theorem twoEndpointAdmissible_iff_probe {J N : ℕ} (δ : ℝ) (η : LabelVector J N)
    (i : Fin N) (a b : MeshIndex J) :
    TwoEndpointAdmissible δ η i a b ↔ ProbeAdmissible δ η i {a, b} := by
  simp [TwoEndpointAdmissible, ProbeAdmissible]

theorem probe_source_weight_bounds {J N R : ℕ} (hN : 0 < N) {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : 0 ≤ δ) (η : LabelVector J N)
    (i : Fin N) (A : Finset (MeshIndex J)) (hA : ProbeAdmissible δ η i A)
    (a : MeshIndex J) (ha : a ∈ A) (I : Finset (Fin N)) (S : Finset (MeshIndex J))
    (hS : S.card ≤ (2 * R + 2) ^ 2) {w : Fin N → ℝ}
    (hw₀ : ∀ k ∈ I, 0 ≤ w k) (hw : ∀ k ∈ I, w k ≤ β / N)
    (hsmall : β₀ * (2 * (R : ℝ) + 2) ^ 2 * δ ≤ 1 / 16) :
    0 ≤ (∑ k ∈ I, w k) ∧ (∑ k ∈ I, w k) ≤ β₀ ∧
      0 ≤ sourceWeight (complete η i a) I S w ∧
      sourceWeight (complete η i a) I S w ≤ 1 / 16 :=
  source_weight_bounds hN hβ hβ₀ hδ (hA a ha) I S hS hw₀ hw hsmall

/-- The fixed source labels are independent of the selected probe completion. -/
theorem probe_fixed_source_weight_bounds {J N R : ℕ} (hN : 0 < N) {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : 0 ≤ δ) (η : LabelVector J N)
    (i : Fin N) (A : Finset (MeshIndex J)) (hA : ProbeAdmissible δ η i A)
    (hne : A.Nonempty) (I : Finset (Fin N)) (hi : i ∉ I) (S : Finset (MeshIndex J))
    (hS : S.card ≤ (2 * R + 2) ^ 2) {w : Fin N → ℝ}
    (hw₀ : ∀ k ∈ I, 0 ≤ w k) (hw : ∀ k ∈ I, w k ≤ β / N)
    (hsmall : β₀ * (2 * (R : ℝ) + 2) ^ 2 * δ ≤ 1 / 16) :
    0 ≤ (∑ k ∈ I, w k) ∧ (∑ k ∈ I, w k) ≤ β₀ ∧
      0 ≤ sourceWeight η I S w ∧ sourceWeight η I S w ≤ 1 / 16 := by
  obtain ⟨a, ha⟩ := hne
  have h := probe_source_weight_bounds hN hβ hβ₀ hδ η i A hA a ha I S hS hw₀ hw hsmall
  rw [sourceWeight_complete η i a I S w hi] at h
  exact h

/-- A different conditional coordinate may retain the moving source. Both
allowed endpoint labelings are controlled; no source deletion is needed here. -/
theorem twoEndpoint_sourceWeight_le {J N : ℕ} (hN : 0 < N) {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : 0 ≤ δ) (η : LabelVector J N)
    (i : Fin N) (a b : MeshIndex J) (hη : TwoEndpointAdmissible δ η i a b)
    (I : Finset (Fin N)) (S : Finset (MeshIndex J)) {w : Fin N → ℝ}
    (hw : ∀ k ∈ I, w k ≤ β / N) :
    sourceWeight (complete η i a) I S w ≤ β₀ * (S.card : ℝ) * δ ∧
      sourceWeight (complete η i b) I S w ≤ β₀ * (S.card : ℝ) * δ :=
  ⟨sourceWeight_le hN hβ hβ₀ hδ hη.1 I S hw,
    sourceWeight_le hN hβ hβ₀ hδ hη.2 I S hw⟩

/-- An actual fractional splitting of the distinguished source. Every other
source keeps its original prescribed label and its original coefficient. -/
def splitSourceWeight {J N : ℕ} (θ : ℝ) (η : LabelVector J N) (i : Fin N)
    (a b : MeshIndex J) (I : Finset (Fin N)) (S : Finset (MeshIndex J))
    (w : Fin N → ℝ) : ℝ :=
  ∑ k ∈ I, if k = i then
    θ * (if a ∈ S then w k else 0) + (1 - θ) * (if b ∈ S then w k else 0)
  else if η k ∈ S then w k else 0

theorem splitSourceWeight_eq {J N : ℕ} (θ : ℝ) (η : LabelVector J N) (i : Fin N)
    (a b : MeshIndex J) (I : Finset (Fin N)) (S : Finset (MeshIndex J))
    (w : Fin N → ℝ) :
    splitSourceWeight θ η i a b I S w =
      θ * sourceWeight (complete η i a) I S w +
      (1 - θ) * sourceWeight (complete η i b) I S w := by
  rw [splitSourceWeight, sourceWeight_eq_sum_ite, sourceWeight_eq_sum_ite,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hki : k = i
  · subst k
    simp only [ite_true, complete_self]
  · simp only [hki, ite_false, complete_of_ne η i k a hki, complete_of_ne η i k b hki]
    ring

@[simp] theorem splitSourceWeight_univ {J N : ℕ} (θ : ℝ) (η : LabelVector J N)
    (i : Fin N) (a b : MeshIndex J) (I : Finset (Fin N)) (w : Fin N → ℝ) :
    splitSourceWeight θ η i a b I Finset.univ w = ∑ k ∈ I, w k := by
  rw [splitSourceWeight_eq, sourceWeight_univ, sourceWeight_univ]
  ring

theorem splitSourceWeight_nonneg {J N : ℕ} {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (η : LabelVector J N) (i : Fin N) (a b : MeshIndex J)
    (I : Finset (Fin N)) (S : Finset (MeshIndex J)) {w : Fin N → ℝ}
    (hw : ∀ k ∈ I, 0 ≤ w k) : 0 ≤ splitSourceWeight θ η i a b I S w := by
  rw [splitSourceWeight_eq]
  exact add_nonneg (mul_nonneg hθ₀ (sourceWeight_nonneg _ I S hw))
    (mul_nonneg (sub_nonneg.mpr hθ₁) (sourceWeight_nonneg _ I S hw))

theorem split_coefficient_bounds {θ w c : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hw₀ : 0 ≤ w) (hw : w ≤ c) :
    (0 ≤ θ * w ∧ θ * w ≤ c) ∧ (0 ≤ (1 - θ) * w ∧ (1 - θ) * w ≤ c) := by
  refine ⟨⟨mul_nonneg hθ₀ hw₀, ?_⟩, ⟨mul_nonneg (sub_nonneg.mpr hθ₁) hw₀, ?_⟩⟩
  · calc
      θ * w ≤ 1 * w := mul_le_mul_of_nonneg_right hθ₁ hw₀
      _ = w := one_mul _
      _ ≤ c := hw
  · have hθ : 1 - θ ≤ 1 := by linarith
    calc
      (1 - θ) * w ≤ 1 * w := mul_le_mul_of_nonneg_right hθ hw₀
      _ = w := one_mul _
      _ ≤ c := hw

theorem split_total_source_weight_le {J N : ℕ} (hN : 0 < N) {β β₀ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (θ : ℝ) (η : LabelVector J N)
    (i : Fin N) (a b : MeshIndex J) (I : Finset (Fin N)) {w : Fin N → ℝ}
    (hw : ∀ k ∈ I, w k ≤ β / N) :
    splitSourceWeight θ η i a b I Finset.univ w ≤ β₀ := by
  rw [splitSourceWeight_univ]
  exact total_source_weight_le hN hβ hβ₀ I hw

theorem splitSourceWeight_le {J N : ℕ} (hN : 0 < N) {β β₀ δ θ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : 0 ≤ δ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (η : LabelVector J N) (i : Fin N) (a b : MeshIndex J)
    (hη : TwoEndpointAdmissible δ η i a b) (I : Finset (Fin N))
    (S : Finset (MeshIndex J)) {w : Fin N → ℝ} (hw : ∀ k ∈ I, w k ≤ β / N) :
    splitSourceWeight θ η i a b I S w ≤ β₀ * (S.card : ℝ) * δ := by
  obtain ⟨ha, hb⟩ := twoEndpoint_sourceWeight_le hN hβ hβ₀ hδ η i a b hη I S hw
  rw [splitSourceWeight_eq]
  calc
    _ ≤ θ * (β₀ * (S.card : ℝ) * δ) + (1 - θ) * (β₀ * (S.card : ℝ) * δ) :=
      add_le_add (mul_le_mul_of_nonneg_left ha hθ₀)
        (mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hθ₁))
    _ = _ := by ring

theorem splitSourceWeight_le_one_sixteenth {J N R : ℕ} (hN : 0 < N) {β β₀ δ θ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : 0 ≤ δ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (η : LabelVector J N) (i : Fin N) (a b : MeshIndex J)
    (hη : TwoEndpointAdmissible δ η i a b) (I : Finset (Fin N))
    (S : Finset (MeshIndex J)) (hS : S.card ≤ (2 * R + 2) ^ 2) {w : Fin N → ℝ}
    (hw : ∀ k ∈ I, w k ≤ β / N)
    (hsmall : β₀ * (2 * (R : ℝ) + 2) ^ 2 * δ ≤ 1 / 16) :
    splitSourceWeight θ η i a b I S w ≤ 1 / 16 := by
  have ha := sourceWeight_le_one_sixteenth hN hβ hβ₀ hδ hη.1 I S hS hw hsmall
  have hb := sourceWeight_le_one_sixteenth hN hβ hβ₀ hδ hη.2 I S hS hw hsmall
  rw [splitSourceWeight_eq]
  calc
    _ ≤ θ * (1 / 16) + (1 - θ) * (1 / 16) :=
      add_le_add (mul_le_mul_of_nonneg_left ha hθ₀)
        (mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hθ₁))
    _ = _ := by ring

/-- The same actual fixed parameter controls fractional endpoint sources. -/
theorem splitSourceWeight_fixedDelta_le {J N : ℕ} (hN : 0 < N)
    {β β₀ C₀ C₁ θ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (η : LabelVector J N) (i : Fin N)
    (a b : MeshIndex J) (hη : TwoEndpointAdmissible (fixedDelta β₀ C₀ C₁) η i a b)
    (I : Finset (Fin N)) (S : Finset (MeshIndex J))
    (hS : S.card ≤ (2 * nearRadius β₀ C₁ + 2) ^ 2) {w : Fin N → ℝ}
    (hw : ∀ k ∈ I, w k ≤ β / N) : splitSourceWeight θ η i a b I S w ≤ 1 / 16 := by
  have hpar := fixedDelta_bounds (hβ.trans hβ₀) hC₀ (C₁ := C₁)
  exact splitSourceWeight_le_one_sixteenth hN hβ hβ₀ hpar.1.le hθ₀ hθ₁ η i a b hη
    I S hS hw hpar.2.2.1

end PeriodicAttractiveLogGas.LabelOccupations
