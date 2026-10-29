/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.PeriodizationCube
import Mathlib.MeasureTheory.Integral.Prod

/-! Splitting a coordinate of the half-open fundamental cube, with its
restricted Lebesgue measure, for the label-law marginal calculation. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DGRHS.Gaussian.D11Imported.PeriodizationCube

lemma cube_split_measure (d : ℕ) (i : Fin (d+1)) :
    MeasurePreserving (fun z : ℝ × (Fin d → ℝ) => i.insertNth z.1 z.2)
      ((volume.restrict (Ico (-(1/2:ℝ)) (1/2))).prod (volume.restrict (cube d)))
      (volume.restrict (cube (d+1))) := by
  have h := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (d+1) => volume.restrict (Ico (-(1/2:ℝ)) (1/2))) i).symm
  simp only [← Measure.restrict_pi_pi, ← volume_pi] at h
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk] at h
  convert h using 1 <;> rfl

lemma lintegral_cube_split (d : ℕ) (i : Fin (d+1)) (f : (Fin (d+1) → ℝ) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ x in cube (d+1), f x) =
      ∫⁻ t in Ico (-(1/2:ℝ)) (1/2), ∫⁻ y in cube d, f (i.insertNth t y) := by
  rw [← (cube_split_measure d i).lintegral_comp hf]
  exact lintegral_prod _ (hf.comp (cube_split_measure d i).measurable).aemeasurable

#print axioms lintegral_cube_split
end DGRHS.Gaussian.D11Imported.PeriodizationCube
