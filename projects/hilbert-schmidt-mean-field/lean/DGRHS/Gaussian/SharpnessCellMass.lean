import DGRHS.Gaussian.SharpnessCubes
import DGRHS.Gaussian.SharpnessDyadic

/-! Actual lower and upper probability masses of good density cells.
The good-cell predicate is geometric; no favorable probability mass is an input. -/
noncomputable section
open MeasureTheory Set BoxIntegral
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma sharpness_density_level_mass_lower (ρ : EuclideanSpace ℝ ι → ℝ)
    (a : ℝ) (A : Set (EuclideanSpace ℝ ι)) (hA : MeasurableSet A)
    (hlevel : ∀ x ∈ A, a ≤ ρ x) :
    ENNReal.ofReal a * volume A ≤ gaussianRieszDensityMeasure ρ A := by
  calc
    _ = ∫⁻ _ in A, ENNReal.ofReal a := (setLIntegral_const A _).symm
    _ ≤ ∫⁻ x in A, ENNReal.ofReal (ρ x) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with x hx
      exact ENNReal.ofReal_le_ofReal (hlevel x hx)
    _ = _ := by rw [gaussianRieszDensityMeasure, withDensity_apply _ hA]

def sharpnessGoodAtom (ρ : EuclideanSpace ℝ ι → ℝ) (a : ℝ) (I : Box ι) :
    Set (EuclideanSpace ℝ ι) := {x | a ≤ ρ x} ∩ (WithLp.ofLp ⁻¹' (I : Set (ι → ℝ)))

def sharpnessGoodCell (ρ : EuclideanSpace ℝ ι → ℝ) (a : ℝ) (I : Box ι) : Prop :=
  (1/2 : ℝ≥0∞) * volume (I : Set (ι → ℝ)) ≤
    volume ({z : ι → ℝ | a ≤ ρ (WithLp.toLp 2 z)} ∩ (I : Set (ι → ℝ)))

lemma measurableSet_sharpnessGoodAtom (ρ : EuclideanSpace ℝ ι → ℝ)
    (hρ : Measurable ρ) (a : ℝ) (I : Box ι) : MeasurableSet (sharpnessGoodAtom ρ a I) :=
  (measurableSet_le measurable_const hρ).inter
    ((measurableSet_sharpnessBox I).preimage (PiLp.volume_preserving_ofLp ι).measurable)

lemma volume_sharpnessGoodAtom (ρ : EuclideanSpace ℝ ι → ℝ) (hρ : Measurable ρ)
    (a : ℝ) (I : Box ι) : volume (sharpnessGoodAtom ρ a I) =
    volume ({z : ι → ℝ | a ≤ ρ (WithLp.toLp 2 z)} ∩ (I : Set (ι → ℝ))) := by
  have he : WithLp.toLp 2 ⁻¹' sharpnessGoodAtom ρ a I =
      {z : ι → ℝ | a ≤ ρ (WithLp.toLp 2 z)} ∩ (I : Set (ι → ℝ)) := by
    ext z
    simp [sharpnessGoodAtom]
  rw [← he]
  exact ((PiLp.volume_preserving_toLp ι).measure_preimage
    (measurableSet_sharpnessGoodAtom ρ hρ a I).nullMeasurableSet).symm

/-- Actual good-cell masses, with all constants and physical measure explicit. -/
theorem sharpness_good_atom_mass_bounds (ρ : EuclideanSpace ℝ ι → ℝ)
    (hρm : Measurable ρ) (a M : ℝ) (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (I : Box ι) (hgood : sharpnessGoodCell ρ a I) :
    ENNReal.ofReal a * ((1/2 : ℝ≥0∞) * volume (I : Set (ι → ℝ))) ≤
      gaussianRieszDensityMeasure ρ (sharpnessGoodAtom ρ a I) ∧
    gaussianRieszDensityMeasure ρ (sharpnessGoodAtom ρ a I) ≤
      ENNReal.ofReal M * volume (I : Set (ι → ℝ)) := by
  have hA := measurableSet_sharpnessGoodAtom ρ hρm a I
  have hv := volume_sharpnessGoodAtom ρ hρm a I
  constructor
  · calc
      _ ≤ ENNReal.ofReal a * volume (sharpnessGoodAtom ρ a I) := by
        rw [hv]
        gcongr
        exact hgood
      _ ≤ _ := sharpness_density_level_mass_lower ρ a _ hA (fun _ hx => hx.1)
  · calc
      _ ≤ ENNReal.ofReal M * volume (sharpnessGoodAtom ρ a I) :=
        gaussianRieszDensityMeasure_le ρ M hρ _
      _ ≤ _ := by
        rw [hv]
        gcongr
        exact inter_subset_right

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_density_level_mass_lower
#print axioms DGRHS.Gaussian.sharpness_good_atom_mass_bounds
#check @DGRHS.Gaussian.sharpness_good_atom_mass_bounds
