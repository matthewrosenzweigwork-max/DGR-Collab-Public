import DGRHS.Gaussian.SharpnessSpatialData

noncomputable section
open MeasureTheory Set BoxIntegral
open scoped ENNReal Classical
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def sharpnessGoodCells (ρ : EuclideanSpace ℝ ι → ℝ) (a : ℝ) {I : Box ι}
    (P : Prepartition I) : Finset (Box ι) := P.boxes.filter (sharpnessGoodCell ρ a)

def sharpnessGoodUnion (ρ : EuclideanSpace ℝ ι → ℝ) (a : ℝ) {I : Box ι}
    (P : Prepartition I) : Set (EuclideanSpace ℝ ι) :=
  ⋃ J ∈ sharpnessGoodCells ρ a P, sharpnessGoodAtom ρ a J

def sharpnessRemainder (ρ : EuclideanSpace ℝ ι → ℝ) (a : ℝ) {I : Box ι}
    (P : Prepartition I) : Set (EuclideanSpace ℝ ι) := (sharpnessGoodUnion ρ a P)ᶜ

lemma measurableSet_sharpnessGoodUnion (ρ : EuclideanSpace ℝ ι → ℝ)
    (hρm : Measurable ρ) (a : ℝ) {I : Box ι} (P : Prepartition I) :
    MeasurableSet (sharpnessGoodUnion ρ a P) :=
by
  have he : sharpnessGoodUnion ρ a P =
      ⋃ J : {J // J ∈ sharpnessGoodCells ρ a P}, sharpnessGoodAtom ρ a J.1 := by
    ext x
    simp [sharpnessGoodUnion]
  rw [he]
  exact MeasurableSet.iUnion (fun J => measurableSet_sharpnessGoodAtom ρ hρm a J.1)

lemma sharpness_good_atoms_disjoint (ρ : EuclideanSpace ℝ ι → ℝ) (a : ℝ)
    {I : Box ι} (P : Prepartition I) :
    PairwiseDisjoint (↑(sharpnessGoodCells ρ a P) : Set (Box ι))
      (sharpnessGoodAtom ρ a) := by
  intro J hJ K hK hne
  change Disjoint (sharpnessGoodAtom ρ a J) (sharpnessGoodAtom ρ a K)
  rw [Set.disjoint_left]
  intro x hx hy
  exact (Set.disjoint_left.mp (P.disjoint_coe_of_mem (Finset.mem_filter.mp hJ).1
    (Finset.mem_filter.mp hK).1 hne)) hx.2 hy.2

lemma sharpness_good_union_subset (ρ : EuclideanSpace ℝ ι → ℝ) (a : ℝ)
    {I : Box ι} (P : Prepartition I) :
    sharpnessGoodUnion ρ a P ⊆ WithLp.ofLp ⁻¹' (I : Set (ι → ℝ)) := by
  intro x hx
  obtain ⟨J, hx⟩ := mem_iUnion.mp hx
  obtain ⟨hJ, hx⟩ := mem_iUnion.mp hx
  exact P.le_of_mem (Finset.mem_filter.mp hJ).1 hx.2

/-- The actual remainder atom has at least half the probability mass.
It is constructed as the complement of the genuine finite good-cell union. -/
theorem sharpness_remainder_mass_lower (ρ : EuclideanSpace ℝ ι → ℝ)
    (hρm : Measurable ρ) (a : ℝ) {I : Box ι} (P : Prepartition I)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hI : gaussianRieszDensityMeasure ρ (WithLp.ofLp ⁻¹' (I : Set (ι → ℝ))) ≤
      ENNReal.ofReal (1/2 : ℝ)) :
    ENNReal.ofReal (1/2 : ℝ) ≤ gaussianRieszDensityMeasure ρ (sharpnessRemainder ρ a P) := by
  let μ := gaussianRieszDensityMeasure ρ
  have hu : μ (sharpnessGoodUnion ρ a P) ≤ ENNReal.ofReal (1/2 : ℝ) :=
    (measure_mono (sharpness_good_union_subset ρ a P)).trans hI
  change _ ≤ μ (sharpnessGoodUnion ρ a P)ᶜ
  rw [measure_compl (measurableSet_sharpnessGoodUnion ρ hρm a P) (measure_ne_top _ _), measure_univ]
  have h := tsub_le_tsub_left hu (1 : ℝ≥0∞)
  have hhalf : (1 : ℝ≥0∞)-ENNReal.ofReal (1/2 : ℝ) = ENNReal.ofReal (1/2 : ℝ) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num : 0 ≤ (1/2 : ℝ))]
    norm_num
  rw [hhalf] at h
  exact h

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_good_atoms_disjoint
#print axioms DGRHS.Gaussian.sharpness_remainder_mass_lower
#check @DGRHS.Gaussian.sharpness_remainder_mass_lower
