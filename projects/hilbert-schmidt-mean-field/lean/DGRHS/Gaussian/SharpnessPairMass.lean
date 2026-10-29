import DGRHS.Gaussian.SharpnessAnnulusQuantitative
import Mathlib.MeasureTheory.Measure.WithDensity

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

/-- Actual product density dominates a squared density level on genuine
measurable pair sets.  This transfers the annular volume bound to the physical
probability law without assuming pair independence conclusions separately. -/
lemma sharpness_density_pair_mass_lower (ρ : EuclideanSpace ℝ ι → ℝ)
    (hρm : Measurable ρ) (a : ℝ) (ha : 0 ≤ a)
    (S : Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) (hS : MeasurableSet S)
    (hlevel : ∀ p ∈ S, a ≤ ρ p.1 ∧ a ≤ ρ p.2) :
    ENNReal.ofReal (a^2)*(volume.prod volume) S ≤
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) S := by
  have hm : Measurable (fun x => ENNReal.ofReal (ρ x)) := hρm.ennreal_ofReal
  rw [gaussianRieszDensityMeasure, prod_withDensity hm hm, withDensity_apply _ hS]
  rw [ENNReal.ofReal_pow ha]
  calc
    _ = ∫⁻ _ in S, (ENNReal.ofReal a)^2 ∂volume.prod volume := (setLIntegral_const S _).symm
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hS] with p hp
      rw [pow_two]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hlevel p hp).1)
        (ENNReal.ofReal_le_ofReal (hlevel p hp).2)

/-- Exact native product-volume transport between Euclidean PiLp coordinates
and coordinate sup-norm space. -/
lemma sharpness_pair_coordinate_volume (S : Set ((ι → ℝ) × (ι → ℝ)))
    (hS : MeasurableSet S) :
    (volume.prod volume) ((fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      (WithLp.ofLp p.1,WithLp.ofLp p.2)) ⁻¹' S) = (volume.prod volume) S := by
  exact ((PiLp.volume_preserving_ofLp ι).prod (PiLp.volume_preserving_ofLp ι)).measure_preimage
    hS.nullMeasurableSet

/-- Genuine physical annular pair mass, using the actual good density atoms. -/
theorem sharpness_physical_good_annular_mass_lower
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρm : Measurable ρ) (a : ℝ) (ha : 0 ≤ a)
    (z : ι → ℝ) {q : ℝ} (hq : 0 < q) (m : ℕ) (R : ℝ) :
    let I := sharpnessInitialBox z q hq
    let G := WithLp.toLp 2 ⁻¹' sharpnessGoodUnion ρ a (sharpnessDyadicPartition I m)
    let S := sharpnessAnnularPairs z q R ∩ (G ×ˢ G)
    ENNReal.ofReal (a^2)*(volume.prod volume) S ≤
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))
        ((fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
          (WithLp.ofLp p.1,WithLp.ofLp p.2)) ⁻¹' S) := by
  dsimp only
  let P := sharpnessDyadicPartition (sharpnessInitialBox z q hq) m
  let G := WithLp.toLp 2 ⁻¹' sharpnessGoodUnion ρ a P
  let S := sharpnessAnnularPairs z q R ∩ (G ×ˢ G)
  let f := fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
    (WithLp.ofLp p.1,WithLp.ofLp p.2)
  have hG : MeasurableSet G := (measurableSet_sharpnessGoodUnion ρ hρm a P).preimage
    (PiLp.volume_preserving_toLp ι).measurable
  have hS : MeasurableSet S := (measurableSet_sharpnessAnnularPairs z q R).inter (hG.prod hG)
  have hf : Measurable f := ((PiLp.volume_preserving_ofLp ι).measurable.comp measurable_fst).prodMk
    ((PiLp.volume_preserving_ofLp ι).measurable.comp measurable_snd)
  have hlevel (x : EuclideanSpace ℝ ι) (hx : WithLp.ofLp x ∈ G) : a ≤ ρ x := by
    have hx' : x ∈ sharpnessGoodUnion ρ a P := by simpa [G] using hx
    obtain ⟨J,hxJ⟩ := mem_iUnion.mp hx'
    obtain ⟨hJ,hxA⟩ := mem_iUnion.mp hxJ
    exact hxA.1
  have hb := sharpness_density_pair_mass_lower ρ hρm a ha (f ⁻¹' S) (hS.preimage hf)
    (fun p hp => ⟨hlevel p.1 hp.2.1,hlevel p.2 hp.2.2⟩)
  rw [sharpness_pair_coordinate_volume S hS] at hb
  exact hb

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_density_pair_mass_lower
#print axioms DGRHS.Gaussian.sharpness_pair_coordinate_volume
#print axioms DGRHS.Gaussian.sharpness_physical_good_annular_mass_lower
#check @DGRHS.Gaussian.sharpness_physical_good_annular_mass_lower
