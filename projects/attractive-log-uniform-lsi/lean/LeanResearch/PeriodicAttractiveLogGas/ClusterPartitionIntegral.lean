import LeanResearch.PeriodicAttractiveLogGas.ClusterAnchor
import Mathlib.Order.Fin.Tuple

/-! Integration of the two complete subclusters in a proper partition.

Source: `lem:collision-integral`, lines 209–213 of the immutable corrected
manuscript. The free coordinates in the group containing index zero and
their complement are separated by an actual volume-preserving measurable
equivalence. Increasing enumerations identify the complete pair products;
the zero anchor is proved to be the first index of its group. Tonelli then
gives an exact product of extended integrals, before invoking the checked
free-anchor bound for the second group. No integrability or independence
identity is assumed.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace PeriodicAttractiveLogGas

/-- The free coordinates belonging to a group of anchored indices. -/
def clusterFreeGroup {n : ℕ} (S : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter (fun i ↦ i.succ ∈ S)

@[simp] theorem mem_clusterFreeGroup {n : ℕ} (S : Finset (Fin (n + 1))) (i : Fin n) :
    i ∈ clusterFreeGroup S ↔ i.succ ∈ S := by simp [clusterFreeGroup]

theorem clusterGroup_eq_insert_map {n : ℕ} (S : Finset (Fin (n + 1))) (h0 : 0 ∈ S) :
    S = insert 0 ((clusterFreeGroup S).map (Fin.succEmb n)) := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [Finset.mem_map, h0]
  · simp [Finset.mem_map, Fin.coe_succEmb]

theorem clusterGroup_compl_eq_map {n : ℕ} (S : Finset (Fin (n + 1))) (h0 : 0 ∈ S) :
    Sᶜ = (clusterFreeGroup S)ᶜ.map (Fin.succEmb n) := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [Finset.mem_map, h0]
  · simp [Finset.mem_map, Fin.coe_succEmb]

theorem card_clusterGroup {n : ℕ} (S : Finset (Fin (n + 1))) (h0 : 0 ∈ S) :
    S.card = (clusterFreeGroup S).card + 1 := by
  have hn : (0 : Fin (n + 1)) ∉ (clusterFreeGroup S).map (Fin.succEmb n) := by
    simp [Finset.mem_map]
  simpa only [Finset.card_insert_of_notMem hn, Finset.card_map] using
    congrArg Finset.card (clusterGroup_eq_insert_map S h0)

theorem card_clusterGroup_compl {n : ℕ} (S : Finset (Fin (n + 1))) (h0 : 0 ∈ S) :
    Sᶜ.card = (clusterFreeGroup S)ᶜ.card := by
  simpa only [Finset.card_map] using congrArg Finset.card (clusterGroup_compl_eq_map S h0)

/-- The increasing enumeration of the anchored group begins with zero and
then enumerates precisely its free indices in increasing order. -/
theorem clusterGroup_orderEmbOfFin {n : ℕ} (S : Finset (Fin (n + 1))) (h0 : 0 ∈ S) :
    (S.orderEmbOfFin (card_clusterGroup S h0) :
        Fin ((clusterFreeGroup S).card + 1) → Fin (n + 1)) =
      Fin.cons (α := fun _ : Fin ((clusterFreeGroup S).card + 1) ↦ Fin (n + 1)) 0
        (fun i ↦ ((clusterFreeGroup S).orderEmbOfFin rfl i).succ) := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa only [Fin.cons_zero] using h0
    · simpa only [Fin.cons_succ, ← mem_clusterFreeGroup] using
        (clusterFreeGroup S).orderEmbOfFin_mem rfl j
  · exact Fin.strictMono_cons.mpr ⟨fun _ ↦ Fin.succ_pos _,
      Fin.strictMono_succ.comp ((clusterFreeGroup S).orderEmbOfFin rfl).strictMono⟩

theorem clusterGroup_orderEmbOfFin_zero {n : ℕ} (S : Finset (Fin (n + 1))) (h0 : 0 ∈ S) :
    S.orderEmbOfFin (card_clusterGroup S h0) 0 = 0 := by
  rw [clusterGroup_orderEmbOfFin S h0, Fin.cons_zero]

theorem clusterGroup_compl_orderEmbOfFin {n : ℕ} (S : Finset (Fin (n + 1))) (h0 : 0 ∈ S) :
    (Sᶜ.orderEmbOfFin (card_clusterGroup_compl S h0) :
        Fin (clusterFreeGroup S)ᶜ.card → Fin (n + 1)) =
      fun i ↦ ((clusterFreeGroup S)ᶜ.orderEmbOfFin rfl i).succ := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro i
    have hi := (clusterFreeGroup S)ᶜ.orderEmbOfFin_mem rfl i
    simpa only [Finset.mem_compl, mem_clusterFreeGroup] using hi
  · exact Fin.strictMono_succ.comp ((clusterFreeGroup S)ᶜ.orderEmbOfFin rfl).strictMono

theorem planarRestrictedPairWeight_anchored_group {n : ℕ} (a : ℝ)
    (S : Finset (Fin (n + 1))) (h0 : 0 ∈ S) (w : Fin n → PlanarSpace) :
    planarRestrictedPairWeight (n + 1) a S (anchoredCluster n w) =
      clusterWeight (clusterFreeGroup S).card a
        (fun i ↦ w ((clusterFreeGroup S).orderEmbOfFin rfl i)) := by
  rw [planarRestrictedPairWeight_reindex a S (card_clusterGroup S h0)]
  apply congrArg (planarPairWeight ((clusterFreeGroup S).card + 1) a)
  funext i
  rw [clusterGroup_orderEmbOfFin S h0]
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp only [Fin.cons_zero, anchoredCluster_zero]
  · simp only [Fin.cons_succ, anchoredCluster_succ]

theorem planarRestrictedPairWeight_unanchored_group {n : ℕ} (a : ℝ)
    (S : Finset (Fin (n + 1))) (h0 : 0 ∈ S) (w : Fin n → PlanarSpace) :
    planarRestrictedPairWeight (n + 1) a Sᶜ (anchoredCluster n w) =
      planarPairWeight (clusterFreeGroup S)ᶜ.card a
        (fun i ↦ w ((clusterFreeGroup S)ᶜ.orderEmbOfFin rfl i)) := by
  rw [planarRestrictedPairWeight_reindex a Sᶜ (card_clusterGroup_compl S h0)]
  apply congrArg (planarPairWeight (clusterFreeGroup S)ᶜ.card a)
  funext i
  rw [clusterGroup_compl_orderEmbOfFin S h0]
  exact anchoredCluster_succ n w _

/-- The complement enumeration with the subtype expected by the library's
coordinate-partition equivalence. Its underlying coordinates are unchanged. -/
def clusterComplementEnum {n : ℕ} (A : Finset (Fin n)) :
    Fin Aᶜ.card ≃ {i : Fin n // i ∉ A} :=
  (Aᶜ.orderIsoOfFin rfl).toEquiv.trans
    (Equiv.subtypeEquivRight (fun i : Fin n ↦
      (show i ∈ Aᶜ ↔ i ∉ A from Finset.mem_compl)))

@[simp] theorem clusterComplementEnum_val {n : ℕ} (A : Finset (Fin n)) (i : Fin Aᶜ.card) :
    (clusterComplementEnum A i).val = Aᶜ.orderEmbOfFin rfl i := rfl

/-- An actual measurable equivalence that splits and enumerates all free
coordinates. No coordinate occurs on both sides or is omitted. -/
def clusterCoordinateSplit {n : ℕ} (A : Finset (Fin n)) :
    (Fin n → PlanarSpace) ≃ᵐ
      ((Fin A.card → PlanarSpace) × (Fin Aᶜ.card → PlanarSpace)) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n ↦ PlanarSpace) (fun i ↦ i ∈ A)).trans
    ((MeasurableEquiv.piCongrLeft (fun _ : A ↦ PlanarSpace)
      (A.orderIsoOfFin rfl).toEquiv).symm.prodCongr
      (MeasurableEquiv.piCongrLeft (fun _ : {i : Fin n // i ∉ A} ↦ PlanarSpace)
        (clusterComplementEnum A)).symm)

theorem clusterCoordinateSplit_apply {n : ℕ} (A : Finset (Fin n)) (w : Fin n → PlanarSpace) :
    clusterCoordinateSplit A w =
      (fun i ↦ w (A.orderEmbOfFin rfl i), fun i ↦ w (Aᶜ.orderEmbOfFin rfl i)) := rfl

theorem measurePreserving_clusterCoordinateSplit {n : ℕ} (A : Finset (Fin n)) :
    MeasurePreserving (clusterCoordinateSplit A) volume volume := by
  have hA := (volume_measurePreserving_piCongrLeft (fun _ : A ↦ PlanarSpace)
    (A.orderIsoOfFin rfl).toEquiv).symm _
  have hB := (volume_measurePreserving_piCongrLeft
    (fun _ : {i : Fin n // i ∉ A} ↦ PlanarSpace) (clusterComplementEnum A)).symm _
  have hsplit := volume_preserving_piEquivPiSubtypeProd
    (fun _ : Fin n ↦ PlanarSpace) (fun i ↦ i ∈ A)
  rw [Measure.volume_eq_prod] at hsplit
  have hsplit' : MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n ↦ PlanarSpace) (fun i ↦ i ∈ A))
      volume (volume.prod volume) := by
    convert hsplit using 1
    congr 3
    exact Subsingleton.elim _ _
  simpa only [Measure.volume_eq_prod] using! (hA.prod hB).comp hsplit'

theorem clusterCoordinateSplit_preimage_box {n : ℕ} (A : Finset (Fin n)) (ρ : ℝ) :
    clusterCoordinateSplit A ⁻¹' (clusterBox A.card ρ ×ˢ clusterBox Aᶜ.card ρ) =
      clusterBox n ρ := by
  ext w
  change clusterCoordinateSplit A w ∈ (clusterBox A.card ρ ×ˢ clusterBox Aᶜ.card ρ) ↔ _
  rw [clusterCoordinateSplit_apply]
  constructor
  · rintro ⟨hA, hB⟩ i _
    by_cases hi : i ∈ A
    · obtain ⟨j, hj⟩ := (A.orderIsoOfFin rfl).surjective ⟨i, hi⟩
      have he : A.orderEmbOfFin rfl j = i := congrArg Subtype.val hj
      simpa only [he] using hA j (mem_univ j)
    · obtain ⟨j, hj⟩ := (Aᶜ.orderIsoOfFin rfl).surjective ⟨i, Finset.mem_compl.mpr hi⟩
      have he : Aᶜ.orderEmbOfFin rfl j = i := congrArg Subtype.val hj
      simpa only [he] using hB j (mem_univ j)
  · intro hw
    exact ⟨fun i _ ↦ hw (A.orderEmbOfFin rfl i) (mem_univ _),
      fun i _ ↦ hw (Aᶜ.orderEmbOfFin rfl i) (mem_univ _)⟩

/-- The actual integral of the two within-group products. -/
def clusterPartitionIntegral (n : ℕ) (ρ a : ℝ) (S : Finset (Fin (n + 1))) : ℝ≥0∞ :=
  ∫⁻ w in clusterBox n ρ,
    ENNReal.ofReal (planarRestrictedPairWeight (n + 1) a S (anchoredCluster n w) *
      planarRestrictedPairWeight (n + 1) a Sᶜ (anchoredCluster n w))

/-- Exact product integration after the measure-preserving coordinate split.
Both factors are extended integrals, and the identity permits infinite values. -/
theorem clusterPartitionIntegral_eq (n : ℕ) (ρ a : ℝ) (S : Finset (Fin (n + 1)))
    (h0 : 0 ∈ S) :
    clusterPartitionIntegral n ρ a S =
      clusterIntegral (clusterFreeGroup S).card ρ a *
        unanchoredClusterIntegral (clusterFreeGroup S)ᶜ.card ρ a := by
  let A := clusterFreeGroup S
  let F : ((Fin A.card → PlanarSpace) × (Fin Aᶜ.card → PlanarSpace)) → ℝ≥0∞ :=
    fun p ↦ ENNReal.ofReal (clusterWeight A.card a p.1) *
      ENNReal.ofReal (planarPairWeight Aᶜ.card a p.2)
  have hf : Measurable F :=
    (((measurable_clusterWeight A.card a).ennreal_ofReal).comp measurable_fst).mul
      (((measurable_planarPairWeight Aᶜ.card a).ennreal_ofReal).comp measurable_snd)
  have hpoint (w : Fin n → PlanarSpace) :
      ENNReal.ofReal (planarRestrictedPairWeight (n + 1) a S (anchoredCluster n w) *
        planarRestrictedPairWeight (n + 1) a Sᶜ (anchoredCluster n w)) =
      F (clusterCoordinateSplit A w) := by
    rw [ENNReal.ofReal_mul
      (planarRestrictedPairWeight_nonneg (n + 1) a S (anchoredCluster n w))]
    simp only [F, A, clusterCoordinateSplit_apply,
      planarRestrictedPairWeight_anchored_group a S h0,
      planarRestrictedPairWeight_unanchored_group a S h0]
  calc
    clusterPartitionIntegral n ρ a S = ∫⁻ w in clusterBox n ρ, F (clusterCoordinateSplit A w) :=
      lintegral_congr hpoint
    _ = ∫⁻ p in clusterBox A.card ρ ×ˢ clusterBox Aᶜ.card ρ, F p := by
      simpa only [clusterCoordinateSplit_preimage_box] using
        (measurePreserving_clusterCoordinateSplit A).setLIntegral_comp_preimage
          ((measurableSet_clusterBox A.card ρ).prod (measurableSet_clusterBox Aᶜ.card ρ)) hf
    _ = clusterIntegral A.card ρ a * unanchoredClusterIntegral Aᶜ.card ρ a := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      exact lintegral_prod_mul (measurable_clusterWeight A.card a).ennreal_ofReal.aemeasurable
        (measurable_planarPairWeight Aᶜ.card a).ennreal_ofReal.aemeasurable

theorem clusterPartition_compl_nonempty {n : ℕ} (S : Finset (Fin (n + 1)))
    (hproper : S ⊂ Finset.univ) : Sᶜ.Nonempty := by
  obtain ⟨i, _, hi⟩ := (Finset.ssubset_iff_of_subset (Finset.subset_univ S)).mp hproper
  exact ⟨i, Finset.mem_compl.mpr hi⟩

/-- The source subcluster integral bound, including the actual planar `pi`
coefficient for the freely moving second anchor. -/
theorem clusterPartitionIntegral_le (n : ℕ) (a : ℝ) (S : Finset (Fin (n + 1)))
    (h0 : 0 ∈ S) (hproper : S ⊂ Finset.univ) :
    clusterPartitionIntegral n 1 a S ≤
      clusterIntegral (S.card - 1) 1 a *
        (ENNReal.ofReal Real.pi * clusterIntegral (Sᶜ.card - 1) 2 a) := by
  have hA : (clusterFreeGroup S).card = S.card - 1 := by
    have h := card_clusterGroup S h0
    omega
  have hBpos : 0 < Sᶜ.card := (clusterPartition_compl_nonempty S hproper).card_pos
  have hB : (clusterFreeGroup S)ᶜ.card = (Sᶜ.card - 1) + 1 := by
    have h := card_clusterGroup_compl S h0
    omega
  have hu : unanchoredClusterIntegral (clusterFreeGroup S)ᶜ.card 1 a ≤
      ENNReal.ofReal Real.pi * clusterIntegral (Sᶜ.card - 1) 2 a := by
    rw [hB]
    exact unanchoredClusterIntegral_unit_le (Sᶜ.card - 1) a
  rw [clusterPartitionIntegral_eq n 1 a S h0, hA]
  exact mul_le_mul le_rfl hu zero_le zero_le

/-- Both indices in the resulting anchored integrals are strictly smaller
than the original number of free coordinates. -/
theorem clusterPartition_smaller_indices {n : ℕ} (S : Finset (Fin (n + 1)))
    (h0 : 0 ∈ S) (hproper : S ⊂ Finset.univ) :
    S.card - 1 < n ∧ Sᶜ.card - 1 < n := by
  have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨0, h0⟩
  have hBpos : 0 < Sᶜ.card := (clusterPartition_compl_nonempty S hproper).card_pos
  have htotal : S.card + Sᶜ.card = n + 1 := by
    simpa only [Fintype.card_fin] using Finset.card_add_card_compl S
  omega

/-- Finiteness is deduced only from the two actual smaller anchored integrals. -/
theorem clusterPartitionIntegral_lt_top (n : ℕ) (a : ℝ) (S : Finset (Fin (n + 1)))
    (h0 : 0 ∈ S) (hproper : S ⊂ Finset.univ)
    (hS : clusterIntegral (S.card - 1) 1 a < ∞)
    (hB : clusterIntegral (Sᶜ.card - 1) 2 a < ∞) :
    clusterPartitionIntegral n 1 a S < ∞ :=
  (clusterPartitionIntegral_le n a S h0 hproper).trans_lt
    (ENNReal.mul_lt_top hS (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB))

theorem clusterPartitionIntegral_lt_top_of_smaller (n : ℕ) (a : ℝ)
    (S : Finset (Fin (n + 1))) (h0 : 0 ∈ S) (hproper : S ⊂ Finset.univ)
    (hsmaller : ∀ m < n, ∀ ρ : ℝ, 0 < ρ → clusterIntegral m ρ a < ∞) :
    clusterPartitionIntegral n 1 a S < ∞ := by
  have hlt := clusterPartition_smaller_indices S h0 hproper
  exact clusterPartitionIntegral_lt_top n a S h0 hproper
    (hsmaller _ hlt.1 1 zero_lt_one) (hsmaller _ hlt.2 2 (by norm_num))

end PeriodicAttractiveLogGas
