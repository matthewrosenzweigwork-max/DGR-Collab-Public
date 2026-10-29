import LeanResearch.PeriodicAttractiveLogGas.CollisionWeights
import LeanResearch.PeriodicAttractiveLogGas.ClusterSeparation
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto

/-! Finite-product factorization for the collision-integral induction.

Source: `lem:collision-integral`, "Separation into smaller groups", lines
201–218 of the immutable corrected manuscript. All pair sets retain the
original `i < j` convention. The cross-pair count is proved by an explicit
bijection with `S × Sᶜ`, so neither orientation doubles a factor. The final
reindexing uses the increasing enumeration of the entire finite subset and
then subtracts its first coordinate. These are algebraic identities and a
pointwise bound, not an integral change of variables or a finiteness result.
-/

noncomputable section

open Set
open scoped BigOperators

namespace PeriodicAttractiveLogGas

def planarRestrictedPairs (k : ℕ) (S : Finset (Fin k)) : Finset (Fin k × Fin k) :=
  (planarOrderedPairs k).filter (fun ij ↦ ij.1 ∈ S ∧ ij.2 ∈ S)

def planarCrossPairs (k : ℕ) (S : Finset (Fin k)) : Finset (Fin k × Fin k) :=
  (planarOrderedPairs k).filter (fun ij ↦
    (ij.1 ∈ S ∧ ij.2 ∉ S) ∨ (ij.1 ∉ S ∧ ij.2 ∈ S))

@[simp] theorem mem_planarRestrictedPairs {k : ℕ} (S : Finset (Fin k)) (ij : Fin k × Fin k) :
    ij ∈ planarRestrictedPairs k S ↔ ij.1 < ij.2 ∧ ij.1 ∈ S ∧ ij.2 ∈ S := by
  simp only [planarRestrictedPairs, Finset.mem_filter, mem_planarOrderedPairs]

@[simp] theorem mem_planarCrossPairs {k : ℕ} (S : Finset (Fin k)) (ij : Fin k × Fin k) :
    ij ∈ planarCrossPairs k S ↔ ij.1 < ij.2 ∧
      ((ij.1 ∈ S ∧ ij.2 ∉ S) ∨ (ij.1 ∉ S ∧ ij.2 ∈ S)) := by
  simp only [planarCrossPairs, Finset.mem_filter, mem_planarOrderedPairs]

def planarRestrictedPairWeight (k : ℕ) (a : ℝ) (S : Finset (Fin k))
    (w : Fin k → PlanarSpace) : ℝ :=
  ∏ ij ∈ planarRestrictedPairs k S, ‖w ij.1 - w ij.2‖ ^ (-a)

def planarCrossPairWeight (k : ℕ) (a : ℝ) (S : Finset (Fin k))
    (w : Fin k → PlanarSpace) : ℝ :=
  ∏ ij ∈ planarCrossPairs k S, ‖w ij.1 - w ij.2‖ ^ (-a)

theorem planarRestrictedPairWeight_nonneg (k : ℕ) (a : ℝ) (S : Finset (Fin k))
    (w : Fin k → PlanarSpace) : 0 ≤ planarRestrictedPairWeight k a S w :=
  Finset.prod_nonneg (fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _)

theorem measurable_planarRestrictedPairWeight (k : ℕ) (a : ℝ) (S : Finset (Fin k)) :
    Measurable (planarRestrictedPairWeight k a S) := by
  unfold planarRestrictedPairWeight
  fun_prop

/-- Each cross pair is oriented once by `i < j`, and once by membership in `S`.
Sorting and orienting by membership give mutually inverse maps. -/
theorem card_planarCrossPairs (k : ℕ) (S : Finset (Fin k)) :
    (planarCrossPairs k S).card = S.card * Sᶜ.card := by
  rw [← Finset.card_product]
  apply Finset.card_bij'
    (fun ij _ ↦ if ij.1 ∈ S then ij else ij.swap)
    (fun ij _ ↦ if ij.1 < ij.2 then ij else ij.swap)
  · intro ij hij
    have hlt := ((mem_planarCrossPairs S ij).mp hij).1
    by_cases hi : ij.1 ∈ S
    · simp only [ite_eq_left hi, ite_eq_left hlt]
    · simp only [ite_eq_right hi, Prod.fst_swap, Prod.snd_swap,
        ite_eq_right (not_lt_of_ge hlt.le), Prod.swap_swap]
  · intro ij hij
    rcases Finset.mem_product.mp hij with ⟨hi, hj⟩
    have hjnot : ij.2 ∉ S := Finset.mem_compl.mp hj
    by_cases hlt : ij.1 < ij.2
    · simp only [ite_eq_left hlt, ite_eq_left hi]
    · simp only [ite_eq_right hlt, Prod.fst_swap, ite_eq_right hjnot, Prod.swap_swap]
  · intro ij hij
    rcases (mem_planarCrossPairs S ij).mp hij with ⟨_, ⟨hi, hj⟩ | ⟨hi, hj⟩⟩
    · simpa only [ite_eq_left hi, Finset.mem_product, Finset.mem_compl] using And.intro hi hj
    · simpa only [ite_eq_right hi, Finset.mem_product, Finset.mem_compl, Prod.fst_swap,
        Prod.snd_swap] using And.intro hj hi
  · intro ij hij
    rcases Finset.mem_product.mp hij with ⟨hi, hj⟩
    have hjnot : ij.2 ∉ S := Finset.mem_compl.mp hj
    by_cases hlt : ij.1 < ij.2
    · simp only [ite_eq_left hlt, mem_planarCrossPairs]
      exact ⟨hlt, Or.inl ⟨hi, hjnot⟩⟩
    · have hne : ij.1 ≠ ij.2 := by
        intro heq
        exact hjnot (heq ▸ hi)
      have hrev : ij.2 < ij.1 := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
      simp only [ite_eq_right hlt, mem_planarCrossPairs, Prod.fst_swap, Prod.snd_swap]
      exact ⟨hrev, Or.inr ⟨hjnot, hi⟩⟩

/-- The three disjoint kinds of pairs exhaust the complete graph. -/
theorem planarPairWeight_partition (k : ℕ) (a : ℝ) (S : Finset (Fin k))
    (w : Fin k → PlanarSpace) :
    planarPairWeight k a w =
      planarRestrictedPairWeight k a S w * planarRestrictedPairWeight k a Sᶜ w *
        planarCrossPairWeight k a S w := by
  have hcover : planarOrderedPairs k =
      (planarRestrictedPairs k S ∪ planarRestrictedPairs k Sᶜ) ∪ planarCrossPairs k S := by
    ext ij
    simp only [Finset.mem_union, mem_planarOrderedPairs, mem_planarRestrictedPairs,
      mem_planarCrossPairs, Finset.mem_compl]
    tauto
  have hwithin : Disjoint (planarRestrictedPairs k S) (planarRestrictedPairs k Sᶜ) := by
    apply Finset.disjoint_left.mpr
    intro ij hi hj
    have h₁ := ((mem_planarRestrictedPairs S ij).mp hi).2.1
    have h₂ := ((mem_planarRestrictedPairs Sᶜ ij).mp hj).2.1
    exact (Finset.mem_compl.mp h₂) h₁
  have hcross : Disjoint (planarRestrictedPairs k S ∪ planarRestrictedPairs k Sᶜ)
      (planarCrossPairs k S) := by
    apply Finset.disjoint_left.mpr
    intro ij hi hj
    simp only [Finset.mem_union, mem_planarRestrictedPairs, mem_planarCrossPairs,
      Finset.mem_compl] at hi hj
    tauto
  unfold planarPairWeight planarRestrictedPairWeight planarCrossPairWeight
  rw [hcover, Finset.prod_union hcross, Finset.prod_union hwithin]

/-- The actual cross product is bounded by one factor for every cross pair. -/
theorem planarCrossPairWeight_le {k : ℕ} {a τ : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ)
    (S : Finset (Fin k)) (w : Fin k → PlanarSpace)
    (hsep : ∀ i ∈ S, ∀ j ∈ Sᶜ, τ ≤ dist (w i) (w j)) :
    planarCrossPairWeight k a S w ≤ τ ^ (-a * (S.card : ℝ) * (Sᶜ.card : ℝ)) := by
  have hpair : ∀ ij ∈ planarCrossPairs k S, ‖w ij.1 - w ij.2‖ ^ (-a) ≤ τ ^ (-a) := by
    intro ij hij
    have hdist : τ ≤ dist (w ij.1) (w ij.2) := by
      rcases ((mem_planarCrossPairs S ij).mp hij).2 with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · exact hsep _ hi _ (Finset.mem_compl.mpr hj)
      · simpa only [dist_comm] using hsep _ hj _ (Finset.mem_compl.mpr hi)
    exact Real.rpow_le_rpow_of_nonpos hτ
      (by simpa only [dist_eq_norm] using hdist) (neg_nonpos.mpr ha)
  calc
    planarCrossPairWeight k a S w ≤ ∏ _ij ∈ planarCrossPairs k S, τ ^ (-a) :=
      Finset.prod_le_prod₀ (fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) hpair
    _ = τ ^ (-a * (S.card : ℝ) * (Sᶜ.card : ℝ)) := by
      rw [Finset.prod_const, card_planarCrossPairs, ← Real.rpow_mul_natCast hτ.le,
        Nat.cast_mul, mul_assoc]

/-- The source's pointwise partition estimate. It is valid for every finite
partition with positive cross separation; neither group is assumed regular. -/
theorem planarPairWeight_le_cluster_partition {k : ℕ} {a τ : ℝ}
    (ha : 0 ≤ a) (hτ : 0 < τ) (S : Finset (Fin k)) (w : Fin k → PlanarSpace)
    (hsep : ∀ i ∈ S, ∀ j ∈ Sᶜ, τ ≤ dist (w i) (w j)) :
    planarPairWeight k a w ≤ τ ^ (-a * (S.card : ℝ) * (Sᶜ.card : ℝ)) *
      planarRestrictedPairWeight k a S w * planarRestrictedPairWeight k a Sᶜ w := by
  rw [planarPairWeight_partition k a S w]
  calc
    planarRestrictedPairWeight k a S w * planarRestrictedPairWeight k a Sᶜ w *
        planarCrossPairWeight k a S w ≤
      planarRestrictedPairWeight k a S w * planarRestrictedPairWeight k a Sᶜ w *
        τ ^ (-a * (S.card : ℝ) * (Sᶜ.card : ℝ)) :=
      mul_le_mul_of_nonneg_left (planarCrossPairWeight_le ha hτ S w hsep)
        (mul_nonneg (planarRestrictedPairWeight_nonneg k a S w)
          (planarRestrictedPairWeight_nonneg k a Sᶜ w))
    _ = τ ^ (-a * (S.card : ℝ) * (Sᶜ.card : ℝ)) *
        planarRestrictedPairWeight k a S w * planarRestrictedPairWeight k a Sᶜ w := by ring

/-- Reindexing enumerates every internal pair and preserves `i < j`. -/
theorem planarRestrictedPairWeight_reindex {k m : ℕ} (a : ℝ) (S : Finset (Fin k))
    (hS : S.card = m) (w : Fin k → PlanarSpace) :
    planarRestrictedPairWeight k a S w =
      planarPairWeight m a (fun i ↦ w (S.orderEmbOfFin hS i)) := by
  let e := S.orderEmbOfFin hS
  symm
  unfold planarPairWeight planarRestrictedPairWeight
  apply Finset.prod_bij (fun ij _ ↦ (e ij.1, e ij.2))
  · intro ij hij
    exact (mem_planarRestrictedPairs S _).mpr
      ⟨e.strictMono ((mem_planarOrderedPairs ij).mp hij),
        S.orderEmbOfFin_mem hS ij.1, S.orderEmbOfFin_mem hS ij.2⟩
  · intro ij hij pq hpq heq
    apply Prod.ext
    · exact e.injective (congrArg Prod.fst heq)
    · exact e.injective (congrArg Prod.snd heq)
  · intro ij hij
    rcases (mem_planarRestrictedPairs S ij).mp hij with ⟨hlt, hi, hj⟩
    obtain ⟨i, hi'⟩ := (S.orderIsoOfFin hS).surjective ⟨ij.1, hi⟩
    obtain ⟨j, hj'⟩ := (S.orderIsoOfFin hS).surjective ⟨ij.2, hj⟩
    have hei : e i = ij.1 := congrArg Subtype.val hi'
    have hej : e j = ij.2 := congrArg Subtype.val hj'
    refine ⟨(i, j), (mem_planarOrderedPairs _).mpr ?_, ?_⟩
    · exact e.lt_iff_lt.mp (by simpa only [hei, hej] using hlt)
    · exact Prod.ext hei hej
  · intro ij hij
    rfl

/-- Subtracting one common vector leaves every pair difference unchanged. -/
theorem planarPairWeight_sub_const (k : ℕ) (a : ℝ) (w : Fin k → PlanarSpace)
    (z : PlanarSpace) :
    planarPairWeight k a (fun i ↦ w i - z) = planarPairWeight k a w := by
  unfold planarPairWeight
  apply Finset.prod_congr rfl
  intro ij hij
  have hdiff : (w ij.1 - z) - (w ij.2 - z) = w ij.1 - w ij.2 := by abel
  rw [hdiff]

/-- The first coordinate becomes the zero anchor; all remaining coordinates
are the actual differences from it. -/
theorem planarPairWeight_reanchor (n : ℕ) (a : ℝ) (w : Fin (n + 1) → PlanarSpace) :
    planarPairWeight (n + 1) a w =
      clusterWeight n a (fun i ↦ w i.succ - w 0) := by
  have hanchor : anchoredCluster n (fun i ↦ w i.succ - w 0) = fun i ↦ w i - w 0 := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [anchoredCluster_zero, sub_self]
    · rfl
  rw [clusterWeight, hanchor, planarPairWeight_sub_const]

/-- A nonempty restricted complete graph is exactly the anchored cluster
product on its increasing enumeration, after a common translation. -/
theorem planarRestrictedPairWeight_eq_clusterWeight {k n : ℕ} (a : ℝ)
    (S : Finset (Fin k)) (hS : S.card = n + 1) (w : Fin k → PlanarSpace) :
    planarRestrictedPairWeight k a S w = clusterWeight n a
      (fun i ↦ w (S.orderEmbOfFin hS i.succ) - w (S.orderEmbOfFin hS 0)) := by
  rw [planarRestrictedPairWeight_reindex a S hS w, planarPairWeight_reanchor]

/-- The geometric unit-shell separation supplies a proper anchored partition
and its actual finite-product estimate with the manuscript's exact threshold. -/
theorem exists_unitShell_clusterFactorization {k : ℕ} (hk : 2 ≤ k) {a : ℝ}
    (ha : 0 ≤ a) (w : Fin k → PlanarSpace) (hw0 : w ⟨0, by omega⟩ = 0)
    (hfar : ∃ j : Fin k, (1 / 2 : ℝ) ≤ ‖w j‖) :
    ∃ S : Finset (Fin k), (⟨0, by omega⟩ : Fin k) ∈ S ∧ S.Nonempty ∧
      S ⊂ Finset.univ ∧ Sᶜ.Nonempty ∧
      (∀ i ∈ S, ∀ j ∈ Sᶜ, (1 : ℝ) / (2 * ((k : ℝ) - 1)) ≤ dist (w i) (w j)) ∧
      planarPairWeight k a w ≤
        ((1 : ℝ) / (2 * ((k : ℝ) - 1))) ^ (-a * (S.card : ℝ) * (Sᶜ.card : ℝ)) *
          planarRestrictedPairWeight k a S w * planarRestrictedPairWeight k a Sᶜ w := by
  classical
  obtain ⟨U, hzero, _, _, hcomp, hsep⟩ :=
    exists_unitShell_separated_cluster hk w hw0 hfar
  let S := Finset.univ.filter (fun i : Fin k ↦ i ∈ U)
  have hmem (i : Fin k) : i ∈ S ↔ i ∈ U := by simp [S]
  have hmemc (i : Fin k) : i ∈ Sᶜ ↔ i ∈ Uᶜ := by
    simp only [Finset.mem_compl, hmem, Set.mem_compl_iff]
  have hSzero : (⟨0, by omega⟩ : Fin k) ∈ S := (hmem _).mpr hzero
  have hSc : Sᶜ.Nonempty := by
    obtain ⟨i, hi⟩ := hcomp
    exact ⟨i, (hmemc i).mpr hi⟩
  have hSne : S ≠ Finset.univ := by
    intro heq
    obtain ⟨i, hi⟩ := hSc
    simp only [heq, Finset.compl_univ, Finset.notMem_empty] at hi
  have hSsep : ∀ i ∈ S, ∀ j ∈ Sᶜ,
      (1 : ℝ) / (2 * ((k : ℝ) - 1)) ≤ dist (w i) (w j) := by
    intro i hi j hj
    exact hsep i ((hmem i).mp hi) j ((hmemc j).mp hj)
  have hkR : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hτ : (0 : ℝ) < 1 / (2 * ((k : ℝ) - 1)) :=
    div_pos zero_lt_one (mul_pos (by norm_num) (sub_pos.mpr hkR))
  exact ⟨S, hSzero, ⟨_, hSzero⟩, Finset.ssubset_univ_iff.mpr hSne, hSc,
    hSsep, planarPairWeight_le_cluster_partition ha hτ S w hSsep⟩

end PeriodicAttractiveLogGas
