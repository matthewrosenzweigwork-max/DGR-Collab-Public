import DGRHS.Gaussian.SharpnessAtomLower
import DGRHS.Gaussian.SharpnessAnnulusQuantitative
import DGRHS.Gaussian.SharpnessPartition

noncomputable section
open MeasureTheory Set Filter BoxIntegral
open scoped ENNReal Classical
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

/-- The genuine compression coefficient on each good-good shell pair inherits
the source physical singularity. Atom masses, integrability and collision
exclusion are derived from the actual bounded density. -/
theorem sharpness_compression_good_annulus_lower (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρm : Measurable ρ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (a : ℝ) (ha0 : 0 < a)
    (z : ι → ℝ) (q : ℝ) (hq : 0 < q)
    (hmass : gaussianRieszDensityMeasure ρ (sharpnessCenteredCube z q) ≤ ENNReal.ofReal (1/2 : ℝ))
    (hlocal : ∀ u v : EuclideanSpace ℝ ι, u ∈ sharpnessCenteredCube z q →
      v ∈ sharpnessCenteredCube z q → u ≠ v → gaussianRieszPhysicalPair s (u,v)/2 ≤
        hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s) (u,v))
    (m : ℕ) (R : ℝ) (hR : 0 < R) (hδR : (2*q)/(2:ℝ)^m ≤ R/4)
    {x y : ι → ℝ}
    (hp : (x,y) ∈ sharpnessAnnularPairs z q R ∩
      ((WithLp.toLp 2 ⁻¹' sharpnessGoodUnion ρ a (sharpnessDyadicPartition (sharpnessInitialBox z q hq) m)) ×ˢ
       (WithLp.toLp 2 ⁻¹' sharpnessGoodUnion ρ a (sharpnessDyadicPartition (sharpnessInitialBox z q hq) m)))) :
    (((3/2:ℝ)*(Fintype.card ι : ℝ)*R)^(-s))/(2*s) ≤
      sharpnessCompression (gaussianRieszDensityMeasure ρ)
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
        (sharpnessPartitionAtom ρ a (sharpnessDyadicPartition (sharpnessInitialBox z q hq) m))
        (WithLp.toLp 2 x,WithLp.toLp 2 y) := by
  let I := sharpnessInitialBox z q hq
  let P := sharpnessDyadicPartition I m
  let A := sharpnessPartitionAtom ρ a P
  let μ := gaussianRieszDensityMeasure ρ
  let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  have hc : 0 < Fintype.card ι := by exact_mod_cast (show (0:ℝ) < Fintype.card ι by linarith)
  have : Nonempty ι := Fintype.card_pos_iff.mp hc
  have hd : (0:ℝ) < Fintype.card ι := by exact_mod_cast hc
  have hwI (i : ι) : I.upper i-I.lower i = 2*q := by dsimp [I,sharpnessInitialBox]; ring
  have hsub : WithLp.ofLp ⁻¹' (I : Set (ι → ℝ)) ⊆ sharpnessCenteredCube z q := by
    intro u hu
    change ∀ i, u i ∈ Ioc (z i-q) (z i+q) at hu
    change (∀ i, z i-q ≤ u i) ∧ (∀ i, u i ≤ z i+q)
    exact ⟨fun i => (hu i).1.le,fun i => (hu i).2⟩
  have hI : μ (WithLp.ofLp ⁻¹' (I : Set (ι → ℝ))) ≤ ENNReal.ofReal (1/2 : ℝ) :=
    (measure_mono hsub).trans hmass
  have hpos := sharpnessPartitionAtom_mass_pos ρ hρm a ha0 I (2*q) (by positivity) hwI m hI
  have hx : WithLp.toLp 2 x ∈ sharpnessGoodUnion ρ a P := hp.2.1
  have hy : WithLp.toLp 2 y ∈ sharpnessGoodUnion ρ a P := hp.2.2
  obtain ⟨J,hJx⟩ := mem_iUnion.mp hx
  obtain ⟨hJ,hxJ⟩ := mem_iUnion.mp hJx
  obtain ⟨K,hKy⟩ := mem_iUnion.mp hy
  obtain ⟨hK,hyK⟩ := mem_iUnion.mp hKy
  let j : ↥(sharpnessGoodCells ρ a P) := ⟨J,hJ⟩
  let k : ↥(sharpnessGoodCells ρ a P) := ⟨K,hK⟩
  have hxA : WithLp.toLp 2 x ∈ A (some j) := hxJ
  have hyA : WithLp.toLp 2 y ∈ A (some k) := hyK
  have hJmem : J ∈ P := (Finset.mem_filter.mp hJ).1
  have hKmem : K ∈ P := (Finset.mem_filter.mp hK).1
  have hwidthJ (i : ι) : J.upper i-J.lower i = (2*q)/(2:ℝ)^m := by
    rw [sharpnessDyadicPartition_width I m hJmem,hwI]
  have hwidthK (i : ι) : K.upper i-K.lower i = (2*q)/(2:ℝ)^m := by
    rw [sharpnessDyadicPartition_width I m hKmem,hwI]
  have hxy : dist x y ≤ R := by
    have hh := hp.1.2.1
    simpa only [Metric.mem_closedBall,dist_eq_norm,sub_zero,norm_sub_rev] using hh
  have hdist : ∀ u ∈ A (some j), ∀ v ∈ A (some k),
      ‖u-v‖ ≤ (3/2:ℝ)*(Fintype.card ι : ℝ)*R := by
    intro u hu v hv
    exact sharpness_two_cell_distance_shell J K (by positivity) hR.le hδR
      hwidthJ hwidthK (by simpa using hxJ.2) (by simpa using hyK.2) hxy hu.2 hv.2
  have hloc : ∀ u ∈ A (some j), ∀ v ∈ A (some k), u ≠ v →
      gaussianRieszPhysicalPair s (u,v)/2 ≤ H (u,v) := by
    intro u hu v hv hne
    exact hlocal u v (hsub (P.le_of_mem hJmem hu.2)) (hsub (P.le_of_mem hKmem hv.2)) hne
  have hb := sharpness_centered_atom_average_lower s ((3/2:ℝ)*(Fintype.card ι : ℝ)*R)
    hs (by positivity) ha ρ M hM hρ (A (some j)) (A (some k))
    (measurableSet_sharpnessPartitionAtom ρ hρm a P _) (measurableSet_sharpnessPartitionAtom ρ hρm a P _)
    (hpos _) (hpos _) hdist hloc
  change _ ≤ sharpnessCompression μ H A (WithLp.toLp 2 x,WithLp.toLp 2 y)
  rw [sharpnessCompression_on_atom μ H A (sharpnessPartitionAtom_pairwise_disjoint ρ a P) hxA hyA]
  exact hb

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_compression_good_annulus_lower
#check @DGRHS.Gaussian.sharpness_compression_good_annulus_lower
