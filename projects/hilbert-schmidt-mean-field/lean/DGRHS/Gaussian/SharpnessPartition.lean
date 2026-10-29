import DGRHS.Gaussian.SharpnessAtoms
import DGRHS.Gaussian.SharpnessCellMass

noncomputable section
open MeasureTheory Set BoxIntegral
open scoped ENNReal Classical
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

abbrev sharpnessAtomIndex (ρ : EuclideanSpace ℝ ι → ℝ) (a : ℝ) {I : Box ι}
    (P : Prepartition I) := Option ↥(sharpnessGoodCells ρ a P)

def sharpnessPartitionAtom (ρ : EuclideanSpace ℝ ι → ℝ) (a : ℝ) {I : Box ι}
    (P : Prepartition I) : sharpnessAtomIndex ρ a P → Set (EuclideanSpace ℝ ι)
  | none => sharpnessRemainder ρ a P
  | some J => sharpnessGoodAtom ρ a J.1

lemma sharpness_good_atom_subset_union (ρ : EuclideanSpace ℝ ι → ℝ) (a : ℝ)
    {I : Box ι} (P : Prepartition I) (J : ↥(sharpnessGoodCells ρ a P)) :
    sharpnessGoodAtom ρ a J.1 ⊆ sharpnessGoodUnion ρ a P := by
  intro x hx
  exact mem_iUnion.mpr ⟨J.1, mem_iUnion.mpr ⟨J.2, hx⟩⟩

lemma measurableSet_sharpnessPartitionAtom (ρ : EuclideanSpace ℝ ι → ℝ)
    (hρm : Measurable ρ) (a : ℝ) {I : Box ι} (P : Prepartition I)
    (i : sharpnessAtomIndex ρ a P) : MeasurableSet (sharpnessPartitionAtom ρ a P i) := by
  cases i with
  | none => exact (measurableSet_sharpnessGoodUnion ρ hρm a P).compl
  | some J => exact measurableSet_sharpnessGoodAtom ρ hρm a J.1

lemma sharpnessPartitionAtom_pairwise_disjoint (ρ : EuclideanSpace ℝ ι → ℝ)
    (a : ℝ) {I : Box ι} (P : Prepartition I) :
    Pairwise (fun i j => Disjoint (sharpnessPartitionAtom ρ a P i)
      (sharpnessPartitionAtom ρ a P j)) := by
  intro i j hne
  cases i with
  | none =>
    cases j with
    | none => exact (hne rfl).elim
    | some J =>
      rw [Set.disjoint_left]
      intro x hx hy
      exact hx (sharpness_good_atom_subset_union ρ a P J hy)
  | some J =>
    cases j with
    | none =>
      rw [Set.disjoint_left]
      intro x hx hy
      exact hy (sharpness_good_atom_subset_union ρ a P J hx)
    | some K =>
      have hjk : J.1 ≠ K.1 := by
        intro he
        exact hne (congrArg Option.some (Subtype.ext he))
      exact sharpness_good_atoms_disjoint ρ a P J.2 K.2 hjk

lemma sharpnessPartitionAtom_covers (ρ : EuclideanSpace ℝ ι → ℝ)
    (a : ℝ) {I : Box ι} (P : Prepartition I) (x : EuclideanSpace ℝ ι) :
    ∃ i : sharpnessAtomIndex ρ a P, x ∈ sharpnessPartitionAtom ρ a P i := by
  by_cases hx : x ∈ sharpnessGoodUnion ρ a P
  · obtain ⟨J, hx⟩ := mem_iUnion.mp hx
    obtain ⟨hJ, hx⟩ := mem_iUnion.mp hx
    exact ⟨some ⟨J,hJ⟩, hx⟩
  · exact ⟨none, hx⟩

/-- Every actual atom in the dyadic compression has positive probability
mass, including the genuine remainder; no favorable atom mass is assumed. -/
theorem sharpnessPartitionAtom_mass_pos (ρ : EuclideanSpace ℝ ι → ℝ)
    (hρm : Measurable ρ) (a : ℝ) (ha : 0 < a) (I : Box ι) (L : ℝ) (hL : 0 < L)
    (hw : ∀ i, I.upper i-I.lower i = L) (m : ℕ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hI : gaussianRieszDensityMeasure ρ (WithLp.ofLp ⁻¹' (I : Set (ι → ℝ))) ≤
      ENNReal.ofReal (1/2 : ℝ))
    (i : sharpnessAtomIndex ρ a (sharpnessDyadicPartition I m)) :
    0 < (gaussianRieszDensityMeasure ρ (sharpnessPartitionAtom ρ a (sharpnessDyadicPartition I m) i)).toReal := by
  let μ := gaussianRieszDensityMeasure ρ
  let P := sharpnessDyadicPartition I m
  cases i with
  | none =>
    have hb := sharpness_remainder_mass_lower ρ hρm a P hI
    have hr := ENNReal.toReal_mono (measure_ne_top μ _) hb
    rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1/2 : ℝ))] at hr
    change 0 < (μ (sharpnessRemainder ρ a P)).toReal
    linarith
  | some J =>
    let A := sharpnessGoodAtom ρ a J.1
    have hJ := Finset.mem_filter.mp J.2
    have hδ : 0 < L/(2 : ℝ)^m := by positivity
    have hlow := sharpness_density_level_mass_lower ρ a A
      (measurableSet_sharpnessGoodAtom ρ hρm a J.1) (fun _ hx => hx.1)
    have hlevel : ENNReal.ofReal a * ((1/2 : ℝ≥0∞)*volume (J.1 : Set (ι → ℝ))) ≤ μ A := by
      have hgood := hJ.2
      calc
        _ ≤ ENNReal.ofReal a * volume A := by
          rw [volume_sharpnessGoodAtom ρ hρm a J.1]
          gcongr
          exact hgood
        _ ≤ _ := hlow
    rw [sharpnessDyadicPartition_cell_volume I L hw m hJ.1] at hlevel
    have hr := ENNReal.toReal_mono (measure_ne_top μ A) hlevel
    have hh : (1/2 : ℝ≥0∞).toReal = (1/2 : ℝ) := by norm_num
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha.le,
      ENNReal.toReal_mul, hh, ENNReal.toReal_pow, ENNReal.toReal_ofReal hδ.le] at hr
    exact lt_of_lt_of_le (by positivity : 0 < a*((1/2)*(L/(2 : ℝ)^m)^Fintype.card ι)) hr

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpnessPartitionAtom_pairwise_disjoint
#print axioms DGRHS.Gaussian.sharpnessPartitionAtom_mass_pos
#check @DGRHS.Gaussian.sharpnessPartitionAtom_mass_pos
