import DGRHS.Gaussian.SharpnessAtoms

noncomputable section
open MeasureTheory Set BoxIntegral
open scoped ENNReal Classical
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma sharpness_good_cell_real_iff (ρ : EuclideanSpace ℝ ι → ℝ) (a : ℝ) (J : Box ι) :
    sharpnessGoodCell ρ a J ↔
      (volume (J : Set (ι → ℝ))).toReal/2 ≤
        (volume ({z : ι → ℝ | a ≤ ρ (WithLp.toLp 2 z)} ∩ (J : Set (ι → ℝ)))).toReal := by
  have hv := sharpness_volume_box_ne_top J
  have hi : volume ({z : ι → ℝ | a ≤ ρ (WithLp.toLp 2 z)} ∩ (J : Set (ι → ℝ))) ≠ ∞ :=
    ne_top_of_le_ne_top hv (measure_mono inter_subset_right)
  have hl : (1/2 : ℝ≥0∞)*volume (J : Set (ι → ℝ)) ≠ ∞ := by finiteness
  have hh : (1/2 : ℝ≥0∞).toReal = (1/2 : ℝ) := by norm_num
  rw [sharpnessGoodCell, ← ENNReal.toReal_le_toReal hl hi, ENNReal.toReal_mul, hh]
  have he : (1/2 : ℝ)*(volume (J : Set (ι → ℝ))).toReal =
      (volume (J : Set (ι → ℝ))).toReal/2 := by ring
  rw [he]

lemma sharpness_bad_cells_eq_not_good (ρ : EuclideanSpace ℝ ι → ℝ) (a : ℝ)
    {I : Box ι} (P : Prepartition I) :
    sharpnessBadCells P {z : ι → ℝ | a ≤ ρ (WithLp.toLp 2 z)} =
      P.boxes.filter (fun J => ¬sharpnessGoodCell ρ a J) := by
  ext J
  simp only [sharpnessBadCells, Finset.mem_filter, sharpness_good_cell_real_iff, not_le]
  rw [inter_comm]

/-- The actual good-atom union misses at most the density-level complement
plus the actual bad-cell volume inside the original box. -/
theorem sharpness_good_union_complement_volume (ρ : EuclideanSpace ℝ ι → ℝ)
    (hρm : Measurable ρ) (a : ℝ) (I : Box ι) (m : ℕ) :
    (volume ((I : Set (ι → ℝ)) \
      (WithLp.toLp 2 ⁻¹' sharpnessGoodUnion ρ a (sharpnessDyadicPartition I m)))).toReal ≤
      3 * (volume ((I : Set (ι → ℝ)) \ {z : ι → ℝ | a ≤ ρ (WithLp.toLp 2 z)})).toReal := by
  let P := sharpnessDyadicPartition I m
  let E := {z : ι → ℝ | a ≤ ρ (WithLp.toLp 2 z)}
  let G := WithLp.toLp 2 ⁻¹' sharpnessGoodUnion ρ a P
  let b := sharpnessBadCells P E
  have hE : MeasurableSet E := measurableSet_le measurable_const
    (hρm.comp (PiLp.volume_preserving_toLp ι).measurable)
  have hbmeas : MeasurableSet (⋃ J ∈ b, (J : Set (ι → ℝ))) := by
    have he : (⋃ J ∈ b, (J : Set (ι → ℝ))) =
        ⋃ J : {J // J ∈ b}, (J.1 : Set (ι → ℝ)) := by ext x; simp
    rw [he]
    exact MeasurableSet.iUnion (fun J => measurableSet_sharpnessBox J.1)
  have hsub : (I : Set (ι → ℝ)) \ G ⊆ ((I : Set (ι → ℝ)) \ E) ∪ (⋃ J ∈ b, (J : Set (ι → ℝ))) := by
    intro x hx
    by_cases hxE : x ∈ E
    · right
      have hc : x ∈ P.iUnion := by rw [sharpnessDyadicPartition_covers]; exact hx.1
      rw [P.iUnion_def'] at hc
      obtain ⟨J, hc⟩ := mem_iUnion.mp hc
      obtain ⟨hJ, hxJ⟩ := mem_iUnion.mp hc
      have hbad : J ∈ b := by
        rw [show b = P.boxes.filter (fun J => ¬sharpnessGoodCell ρ a J) from
          sharpness_bad_cells_eq_not_good ρ a P]
        refine Finset.mem_filter.mpr ⟨hJ, ?_⟩
        intro hg
        apply hx.2
        change WithLp.toLp 2 x ∈ sharpnessGoodUnion ρ a P
        apply mem_iUnion.mpr ⟨J, ?_⟩
        apply mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hJ, hg⟩, ?_⟩
        exact ⟨hxE, by simpa using hxJ⟩
      exact mem_iUnion.mpr ⟨J, mem_iUnion.mpr ⟨hbad, hxJ⟩⟩
    · exact Or.inl ⟨hx.1, hxE⟩
  have hd : PairwiseDisjoint (↑b : Set (Box ι)) (fun J => (J : Set (ι → ℝ))) := by
    intro J hJ K hK hne
    exact P.disjoint_coe_of_mem (Finset.mem_filter.mp hJ).1 (Finset.mem_filter.mp hK).1 hne
  have hu := measure_biUnion_finset (μ := volume) hd (fun J _ => measurableSet_sharpnessBox J)
  have hfD : volume ((I : Set (ι → ℝ)) \ E) ≠ ∞ :=
    ne_top_of_le_ne_top (sharpness_volume_box_ne_top I) (measure_mono sdiff_subset)
  have hfB : volume (⋃ J ∈ b, (J : Set (ι → ℝ))) ≠ ∞ := by
    rw [hu]
    exact ENNReal.sum_ne_top.mpr (fun J _ => sharpness_volume_box_ne_top J)
  have hvol : volume ((I : Set (ι → ℝ)) \ G) ≤
      volume ((I : Set (ι → ℝ)) \ E) + volume (⋃ J ∈ b, (J : Set (ι → ℝ))) :=
    (measure_mono hsub).trans (measure_union_le _ _)
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfD, hfB⟩) hvol
  rw [ENNReal.toReal_add hfD hfB, hu,
    ENNReal.toReal_sum (fun J _ => sharpness_volume_box_ne_top J)] at hr
  have hbad := sharpness_bad_cell_volume_sum P E hE
  linarith

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_good_cell_real_iff
#print axioms DGRHS.Gaussian.sharpness_good_union_complement_volume
#check @DGRHS.Gaussian.sharpness_good_union_complement_volume
