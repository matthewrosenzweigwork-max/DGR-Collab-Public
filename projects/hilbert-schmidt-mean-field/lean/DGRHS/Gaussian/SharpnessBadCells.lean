import DGRHS.Gaussian.SharpnessDyadic
import Mathlib.MeasureTheory.Measure.Basic

noncomputable section
open MeasureTheory Set BoxIntegral
open scoped ENNReal Classical
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma sharpness_volume_box_ne_top (I : Box ι) : volume (I : Set (ι → ℝ)) ≠ ∞ := by
  rw [volume_sharpnessBox]
  exact ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)

def sharpnessBadCells {I : Box ι} (P : Prepartition I) (E : Set (ι → ℝ)) : Finset (Box ι) :=
  P.boxes.filter fun J => (volume ((J : Set (ι → ℝ)) ∩ E)).toReal <
    (volume (J : Set (ι → ℝ))).toReal / 2

/-- Bad cells are counted from actual disjoint complementary volume. -/
theorem sharpness_bad_cell_volume_sum {I : Box ι} (P : Prepartition I)
    (E : Set (ι → ℝ)) (hE : MeasurableSet E) :
    (∑ J ∈ sharpnessBadCells P E, (volume (J : Set (ι → ℝ))).toReal) ≤
      2 * (volume ((I : Set (ι → ℝ)) \ E)).toReal := by
  let b := sharpnessBadCells P E
  have hdiffFin (J : Box ι) : volume ((J : Set (ι → ℝ)) \ E) ≠ ∞ :=
    ne_top_of_le_ne_top (sharpness_volume_box_ne_top J) (measure_mono sdiff_subset)
  have hcell (J : Box ι) (hJ : J ∈ b) :
      (volume (J : Set (ι → ℝ))).toReal ≤
        2 * (volume ((J : Set (ι → ℝ)) \ E)).toReal := by
    have hb := (Finset.mem_filter.mp hJ).2
    have hinterFin : volume ((J : Set (ι → ℝ)) ∩ E) ≠ ∞ :=
      ne_top_of_le_ne_top (sharpness_volume_box_ne_top J) (measure_mono inter_subset_left)
    have hadd := congrArg ENNReal.toReal (measure_inter_add_sdiff (μ := volume)
      (J : Set (ι → ℝ)) hE)
    rw [ENNReal.toReal_add hinterFin (hdiffFin J)] at hadd
    linarith
  have hd : PairwiseDisjoint (↑b : Set (Box ι)) (fun J => (J : Set (ι → ℝ)) \ E) := by
    intro J hJ K hK hne
    exact (P.disjoint_coe_of_mem (Finset.mem_filter.mp hJ).1
      (Finset.mem_filter.mp hK).1 hne).mono sdiff_subset sdiff_subset
  have hm : ∀ J ∈ b, MeasurableSet ((J : Set (ι → ℝ)) \ E) :=
    fun J _ => (measurableSet_sharpnessBox J).diff hE
  have hu := measure_biUnion_finset (μ := volume) hd hm
  have hs : (∑ J ∈ b, volume ((J : Set (ι → ℝ)) \ E)) ≤
      volume ((I : Set (ι → ℝ)) \ E) := by
    rw [← hu]
    apply measure_mono
    rintro x hx
    obtain ⟨J, hx⟩ := mem_iUnion.mp hx
    obtain ⟨hJ, hx⟩ := mem_iUnion.mp hx
    exact ⟨P.le_of_mem (Finset.mem_filter.mp hJ).1 hx.1, hx.2⟩
  have hsReal := ENNReal.toReal_mono (hdiffFin I) hs
  rw [ENNReal.toReal_sum (fun J _ => hdiffFin J)] at hsReal
  calc
    _ ≤ ∑ J ∈ b, 2 * (volume ((J : Set (ι → ℝ)) \ E)).toReal :=
      Finset.sum_le_sum hcell
    _ = 2 * (∑ J ∈ b, (volume ((J : Set (ι → ℝ)) \ E)).toReal) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsReal (by norm_num)

/-- The actual dyadic count times common physical cell volume is controlled
by the missing density volume, with the exact factor two. -/
theorem sharpness_dyadic_bad_count (I : Box ι) (L : ℝ) (hL : 0 < L)
    (hwidth : ∀ i, I.upper i-I.lower i = L) (m : ℕ)
    (E : Set (ι → ℝ)) (hE : MeasurableSet E) :
    ((sharpnessBadCells (sharpnessDyadicPartition I m) E).card : ℝ) *
        (L/(2 : ℝ)^m) ^ Fintype.card ι ≤
      2 * (volume ((I : Set (ι → ℝ)) \ E)).toReal := by
  have hδ : 0 ≤ L/(2 : ℝ)^m := by positivity
  have hvol (J : Box ι) (hJ : J ∈ sharpnessBadCells (sharpnessDyadicPartition I m) E) :
      (volume (J : Set (ι → ℝ))).toReal = (L/(2 : ℝ)^m)^Fintype.card ι := by
    rw [sharpnessDyadicPartition_cell_volume I L hwidth m (Finset.mem_filter.mp hJ).1]
    simp only [ENNReal.toReal_pow, ENNReal.toReal_ofReal hδ]
  have he : (∑ J ∈ sharpnessBadCells (sharpnessDyadicPartition I m) E,
      (volume (J : Set (ι → ℝ))).toReal) =
      ((sharpnessBadCells (sharpnessDyadicPartition I m) E).card : ℝ) *
        (L/(2 : ℝ)^m)^Fintype.card ι := by
    calc
      _ = ∑ _J ∈ sharpnessBadCells (sharpnessDyadicPartition I m) E,
          (L/(2 : ℝ)^m)^Fintype.card ι := Finset.sum_congr rfl hvol
      _ = _ := by simp
  rw [← he]
  exact sharpness_bad_cell_volume_sum _ E hE

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_bad_cell_volume_sum
#print axioms DGRHS.Gaussian.sharpness_dyadic_bad_count
#check @DGRHS.Gaussian.sharpness_dyadic_bad_count
