import Mathlib.Analysis.BoxIntegral.Partition.SubboxInduction
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Genuine finite dyadic subdivisions, built from pinned native splitCenter
and biUnion. No favorable partition or mass conclusion is assumed. -/
noncomputable section
open BoxIntegral MeasureTheory Set
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def sharpnessDyadicPartition (I : Box ι) : ℕ → Prepartition I
  | 0 => ⊤
  | m+1 => (sharpnessDyadicPartition I m).biUnion Prepartition.splitCenter

lemma sharpnessDyadicPartition_isPartition (I : Box ι) (m : ℕ) :
    (sharpnessDyadicPartition I m).IsPartition := by
  induction m with
  | zero => exact Prepartition.isPartitionTop I
  | succ m ih => exact ih.biUnion (fun J _ => Prepartition.isPartition_splitCenter J)

lemma sharpnessDyadicPartition_width (I : Box ι) (m : ℕ) {J : Box ι}
    (hJ : J ∈ sharpnessDyadicPartition I m) (i : ι) :
    J.upper i-J.lower i = (I.upper i-I.lower i)/(2 : ℝ)^m := by
  induction m generalizing J with
  | zero =>
      have he : J = I := Prepartition.mem_top.mp hJ
      subst J
      simp
  | succ m ih =>
      obtain ⟨J', hJ', hsplit⟩ := ((sharpnessDyadicPartition I m).mem_biUnion (πi := Prepartition.splitCenter)).mp hJ
      rw [Prepartition.upper_sub_lower_of_mem_splitCenter hsplit, ih hJ', pow_succ]
      ring

lemma sharpnessDyadicPartition_covers (I : Box ι) (m : ℕ) :
    (sharpnessDyadicPartition I m).iUnion = (I : Set (ι → ℝ)) :=
  (sharpnessDyadicPartition_isPartition I m).iUnion_eq

lemma volume_sharpnessBox (I : Box ι) :
    volume (I : Set (ι → ℝ)) = ∏ i, ENNReal.ofReal (I.upper i-I.lower i) := by
  rw [Box.coe_eq_pi, Real.volume_pi_Ioc]

lemma measurableSet_sharpnessBox (I : Box ι) : MeasurableSet (I : Set (ι → ℝ)) := by
  rw [Box.coe_eq_pi]
  exact MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Ioc)

/-- Every actual dyadic cell has the prescribed common volume when the
initial physical box is a cube. -/
theorem sharpnessDyadicPartition_cell_volume (I : Box ι) (L : ℝ)
    (hL : ∀ i, I.upper i-I.lower i = L) (m : ℕ) {J : Box ι}
    (hJ : J ∈ sharpnessDyadicPartition I m) :
    volume (J : Set (ι → ℝ)) = ENNReal.ofReal (L/(2 : ℝ)^m) ^ Fintype.card ι := by
  rw [volume_sharpnessBox]
  have hw (i : ι) : J.upper i-J.lower i = L/(2 : ℝ)^m := by
    rw [sharpnessDyadicPartition_width I m hJ, hL]
  simp_rw [hw]
  simp

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpnessDyadicPartition_isPartition
#print axioms DGRHS.Gaussian.sharpnessDyadicPartition_width
#print axioms DGRHS.Gaussian.sharpnessDyadicPartition_cell_volume
#check @DGRHS.Gaussian.sharpnessDyadicPartition_cell_volume
