/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.PeriodizationIntegral

/-! Complex-valued integral unfolding on the same fundamental cube. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace DGRHS.Gaussian.D11Imported.PeriodizationCube
open HighDim

attribute [local instance] integerAction
local instance (d : ℕ) : MeasurableConstVAdd (Frequency d) (Fin d → ℝ) where
  measurable_const_vadd n := by
    change Measurable (fun x : Fin d → ℝ => (fun i => (n i : ℝ)) + x)
    fun_prop
local instance (d : ℕ) : VAddInvariantMeasure (Frequency d) (Fin d → ℝ) volume where
  measure_preimage_vadd n s hs := by
    exact (measurePreserving_add_left volume (fun i => (n i : ℝ))).measure_preimage hs.nullMeasurableSet

lemma unfold_integral_complex (d : ℕ) (f : (Fin d → ℝ) → ℂ)
    (hm : Measurable f) (hf : Integrable f) :
    (∫ x in cube d, ∑' n : Frequency d, f (fun i => x i+(n i:ℝ))) = ∫ x, f x := by
  rw [integral_tsum (μ := volume.restrict (cube d))
    (f := fun (n : Frequency d) (x : Fin d → ℝ) => f (fun i => x i+(n i:ℝ))) (fun n : Frequency d =>
    (hm.comp (show Measurable (fun x : Fin d → ℝ => fun i => x i+(n i:ℝ)) by
      fun_prop)).aestronglyMeasurable)]
  · have h := (cube_fundamental d).integral_eq_tsum'' f hf
    rw [h]
    apply tsum_congr
    intro n
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by
      dsimp only
      congr 1
      funext i
      change x i+(n i:ℝ) = (n i:ℝ)+x i
      ring)
  · rw [← lintegral_tsum (μ := volume.restrict (cube d))
      (f := fun (n : Frequency d) (x : Fin d → ℝ) => ‖f (fun i => x i+(n i:ℝ))‖ₑ) (fun n : Frequency d =>
      (hm.enorm.comp (show Measurable (fun x : Fin d → ℝ => fun i => x i+(n i:ℝ)) by
        fun_prop)).aemeasurable)]
    rw [unfold_lintegral d _ hm.enorm]
    exact hf.2.ne

#print axioms unfold_integral_complex
end DGRHS.Gaussian.D11Imported.PeriodizationCube
