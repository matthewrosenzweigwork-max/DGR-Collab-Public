import LeanResearch.PeriodicAttractiveLogGas.WeightedCubeMeasure
import Mathlib.Data.Finset.Max

/-! Open axis-parallel cubes for the source's uncentered maximal function.
Their averages use the actual Euclidean volume. The finite selection
argument keeps the source's exact factor three. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology BigOperators
namespace PeriodicAttractiveLogGas.PhysicalCubes
variable {ι : Type*} [Fintype ι]

def openCube (c : EuclideanSpace ℝ ι) (ℓ : ℝ) : Set (EuclideanSpace ℝ ι) :=
  WithLp.ofLp ⁻¹' Set.pi Set.univ (fun j => Ioo (c j - ℓ / 2) (c j + ℓ / 2))

lemma mem_openCube (c x : EuclideanSpace ℝ ι) (ℓ : ℝ) :
    x ∈ openCube c ℓ ↔ ∀ j, |x j - c j| < ℓ / 2 := by
  constructor
  · intro hx j
    have hj := hx j (mem_univ j)
    exact abs_lt.mpr ⟨by linarith only [hj.1], by linarith only [hj.2]⟩
  · intro hx j _
    obtain ⟨hl, hu⟩ := abs_lt.mp (hx j)
    exact ⟨by linarith only [hl], by linarith only [hu]⟩

lemma isOpen_openCube (c : EuclideanSpace ℝ ι) (ℓ : ℝ) : IsOpen (openCube c ℓ) :=
  (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)).preimage
    (PiLp.homeomorph 2 (fun _ : ι => ℝ)).continuous

lemma openCube_subset_cube (c : EuclideanSpace ℝ ι) (ℓ : ℝ) : openCube c ℓ ⊆ cube c ℓ := by
  intro x hx j hj
  exact ⟨(hx j hj).1.le, (hx j hj).2.le⟩

lemma mem_openCube_self (c : EuclideanSpace ℝ ι) {ℓ : ℝ} (hℓ : 0 < ℓ) : c ∈ openCube c ℓ := by
  apply (mem_openCube c c ℓ).mpr
  intro j
  simpa only [sub_self, abs_zero] using half_pos hℓ

lemma openCube_ae_eq_cube (c : EuclideanSpace ℝ ι) (ℓ : ℝ) : openCube c ℓ =ᵐ[volume] cube c ℓ := by
  have hp : (Set.pi Set.univ (fun j => Ioo (c j - ℓ / 2) (c j + ℓ / 2))) =ᵐ[volume]
      Set.pi Set.univ (fun j => Icc (c j - ℓ / 2) (c j + ℓ / 2)) := Measure.pi_Ioo_ae_eq_pi_Icc
  exact (PiLp.volume_preserving_ofLp ι).quasiMeasurePreserving.preimage_ae_eq hp

lemma openCube_volume (c : EuclideanSpace ℝ ι) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    volume (openCube c ℓ) = ENNReal.ofReal (ℓ ^ Fintype.card ι) := by
  rw [measure_congr (openCube_ae_eq_cube c ℓ), cube_volume c hℓ]

lemma openCube_volume_pos (c : EuclideanSpace ℝ ι) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    0 < volume (openCube c ℓ) := by
  rw [openCube_volume c hℓ.le]
  exact ENNReal.ofReal_pos.mpr (pow_pos hℓ _)

lemma openCube_volume_ne_top (c : EuclideanSpace ℝ ι) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    volume (openCube c ℓ) ≠ ∞ := by rw [openCube_volume c hℓ]; exact ENNReal.ofReal_ne_top

lemma openCube_mono (c : EuclideanSpace ℝ ι) {ℓ r : ℝ} (h : ℓ ≤ r) : openCube c ℓ ⊆ openCube c r := by
  intro x hx
  apply (mem_openCube c x r).mpr
  intro j
  exact ((mem_openCube c x ℓ).mp hx j).trans_le (by linarith only [h])

lemma openCube_subset_triple_of_inter {c b : EuclideanSpace ℝ ι} {ℓ r : ℝ}
    (hℓr : ℓ ≤ r) (hi : (openCube c ℓ ∩ openCube b r).Nonempty) :
    openCube c ℓ ⊆ openCube b (3 * r) := by
  obtain ⟨y, hyc, hyb⟩ := hi
  intro x hx
  apply (mem_openCube b x (3 * r)).mpr
  intro j
  have hxc := (mem_openCube c x ℓ).mp hx j
  have hyc := (mem_openCube c y ℓ).mp hyc j
  have hyb := (mem_openCube b y r).mp hyb j
  have h1 := abs_sub_le (x j) (c j) (b j)
  have h2 := abs_sub_le (c j) (y j) (b j)
  rw [abs_sub_comm (c j) (y j)] at h2
  linarith only [hxc, hyc, hyb, h1, h2, hℓr]

/-- Greedy selection of largest cubes, with exact triple coverage. -/
theorem finite_disjoint_triple_cover {α : Type*} (s : Finset α)
    (c : α → EuclideanSpace ℝ ι) (ℓ : α → ℝ) (hpos : ∀ i ∈ s, 0 < ℓ i) :
    ∃ t : Finset α, t ⊆ s ∧ (t : Set α).PairwiseDisjoint (fun i => openCube (c i) (ℓ i)) ∧
      ∀ i ∈ s, ∃ j ∈ t, openCube (c i) (ℓ i) ⊆ openCube (c j) (3 * ℓ j) := by
  classical
  revert hpos
  refine Finset.strongInductionOn s ?_
  intro s ih hpos
  by_cases hs : s = ∅
  · subst s
    exact ⟨∅, by simp⟩
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image ℓ (Finset.nonempty_iff_ne_empty.mpr hs)
  let u := s.filter (fun j => Disjoint (openCube (c j) (ℓ j)) (openCube (c i) (ℓ i)))
  have hus : u ⊆ s := Finset.filter_subset _ _
  have hiu : i ∉ u := by
    intro hh
    have hd := (Finset.mem_filter.mp hh).2
    exact Set.disjoint_left.mp hd (mem_openCube_self (c i) (hpos i hi))
      (mem_openCube_self (c i) (hpos i hi))
  have hstrict : u ⊂ s := ⟨hus, fun hh => hiu (hh hi)⟩
  obtain ⟨t, ht, hdis, hcov⟩ := ih u hstrict (fun j hj => hpos j (hus hj))
  refine ⟨insert i t, Finset.insert_subset_iff.mpr ⟨hi, ht.trans hus⟩, ?_, ?_⟩
  · intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with rfl | hat
    · rcases Finset.mem_insert.mp hb with rfl | hbt
      · exact (hab rfl).elim
      · exact ((Finset.mem_filter.mp (ht hbt)).2).symm
    · rcases Finset.mem_insert.mp hb with rfl | hbt
      · exact (Finset.mem_filter.mp (ht hat)).2
      · exact hdis hat hbt hab
  · intro j hj
    by_cases hd : Disjoint (openCube (c j) (ℓ j)) (openCube (c i) (ℓ i))
    · obtain ⟨k, hk, hsub⟩ := hcov j (Finset.mem_filter.mpr ⟨hj, hd⟩)
      exact ⟨k, Finset.mem_insert_of_mem hk, hsub⟩
    · exact ⟨i, Finset.mem_insert_self _ _,
        openCube_subset_triple_of_inter (hmax j hj) (Set.not_disjoint_iff_nonempty_inter.mp hd)⟩
end PeriodicAttractiveLogGas.PhysicalCubes
