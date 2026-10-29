import DGRHS.Gaussian.SharpnessCompressionLower
import DGRHS.Gaussian.SharpnessPairMass

noncomputable section
open MeasureTheory Set Filter BoxIntegral
open scoped ENNReal Classical
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

/-- One genuine annular contribution to the actual compression square
integral. All properness and the density-square factor are proved here. -/
theorem sharpness_compression_annular_square_lower (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρm : Measurable ρ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (a : ℝ) (ha0 : 0 < a)
    (z : ι → ℝ) (q : ℝ) (hq : 0 < q)
    (hmass : gaussianRieszDensityMeasure ρ (sharpnessCenteredCube z q) ≤ ENNReal.ofReal (1/2 : ℝ))
    (hlocal : ∀ u v : EuclideanSpace ℝ ι, u ∈ sharpnessCenteredCube z q →
      v ∈ sharpnessCenteredCube z q → u ≠ v → gaussianRieszPhysicalPair s (u,v)/2 ≤
        hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s) (u,v))
    (m : ℕ) (R : ℝ) (hR : 0 < R) (hδR : (2*q)/(2:ℝ)^m ≤ R/4) :
    let I := sharpnessInitialBox z q hq
    let P := sharpnessDyadicPartition I m
    let G := WithLp.toLp 2 ⁻¹' sharpnessGoodUnion ρ a P
    let S := sharpnessAnnularPairs z q R ∩ (G ×ˢ G)
    let f := fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => (WithLp.ofLp p.1,WithLp.ofLp p.2)
    let κ := sharpnessCompression (gaussianRieszDensityMeasure ρ)
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
      (sharpnessPartitionAtom ρ a P)
    ((((3/2:ℝ)*(Fintype.card ι : ℝ)*R)^(-s))/(2*s))^2*a^2*(volume.prod volume S).toReal ≤
      ∫ p in f ⁻¹' S, κ p^2 ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ) := by
  dsimp only
  let I := sharpnessInitialBox z q hq
  let P := sharpnessDyadicPartition I m
  let G := WithLp.toLp 2 ⁻¹' sharpnessGoodUnion ρ a P
  let S := sharpnessAnnularPairs z q R ∩ (G ×ˢ G)
  let f := fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => (WithLp.ofLp p.1,WithLp.ofLp p.2)
  let μ := gaussianRieszDensityMeasure ρ
  let κ := sharpnessCompression μ (hoeffdingCentered μ (gaussianRieszPhysicalPair s)) (sharpnessPartitionAtom ρ a P)
  let b := (((3/2:ℝ)*(Fintype.card ι : ℝ)*R)^(-s))/(2*s)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hG : MeasurableSet G := (measurableSet_sharpnessGoodUnion ρ hρm a P).preimage
    (PiLp.volume_preserving_toLp ι).measurable
  have hS : MeasurableSet S := (measurableSet_sharpnessAnnularPairs z q R).inter (hG.prod hG)
  have hf : Measurable f := ((PiLp.volume_preserving_ofLp ι).measurable.comp measurable_fst).prodMk
    ((PiLp.volume_preserving_ofLp ι).measurable.comp measurable_snd)
  have hiκ : Integrable (fun p => κ p^2) (μ.prod μ) :=
    (sharpnessCompression_memLp μ _ _ (measurableSet_sharpnessPartitionAtom ρ hρm a P)).integrable_sq
  have hpoint : ∀ p ∈ f ⁻¹' S, b^2 ≤ κ p^2 := by
    intro p hp
    have hp' := sharpness_compression_good_annulus_lower s hs ha ρ hρm M hM hρ a ha0 z q hq
      hmass hlocal m R hR hδR hp
    have hc : b ≤ κ p := by simpa only [WithLp.toLp_ofLp] using hp'
    nlinarith [sq_nonneg (κ p-b)]
  have hi := integral_mono_ae (integrable_const (b^2)) hiκ.restrict
    (by filter_upwards [ae_restrict_mem (hS.preimage hf)] with p hp; exact hpoint p hp)
  rw [MeasureTheory.integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ] at hi
  have hd := sharpness_physical_good_annular_mass_lower ρ hρm a ha0.le z hq m R
  have hdReal := ENNReal.toReal_mono (measure_ne_top (μ.prod μ) (f ⁻¹' S)) hd
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg a)] at hdReal
  have hm := mul_le_mul_of_nonneg_left hdReal (sq_nonneg b)
  change b^2*a^2*(volume.prod volume S).toReal ≤ _
  nlinarith [hi]

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_compression_annular_square_lower
#check @DGRHS.Gaussian.sharpness_compression_annular_square_lower
