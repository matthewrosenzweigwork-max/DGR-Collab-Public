/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.PeriodizationCube
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Absolute integrability and signed integral unfolding for the lattice sum. -/
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

lemma translated_norm_sum_integral (d : ℕ) (f : (Fin d → ℝ) → ℝ) (hm : Measurable f) :
    (∑' n : Frequency d, ∫⁻ x in cube d, ‖f (fun i => x i+(n i:ℝ))‖ₑ) =
      ∫⁻ x, ‖f x‖ₑ := by
  rw [← lintegral_tsum (μ := volume.restrict (cube d))
    (f := fun (n : Frequency d) (x : Fin d → ℝ) => ‖f (fun i => x i+(n i:ℝ))‖ₑ) (fun n : Frequency d =>
    (hm.enorm.comp (show Measurable (fun x : Fin d → ℝ => fun i => x i+(n i:ℝ)) by
      fun_prop)).aemeasurable)]
  exact unfold_lintegral d _ hm.enorm

lemma translated_summable_ae (d : ℕ) (f : (Fin d → ℝ) → ℝ)
    (hm : Measurable f) (hf : Integrable f) :
    ∀ᵐ x ∂volume.restrict (cube d), Summable (fun n : Frequency d => f (fun i => x i+(n i:ℝ))) := by
  have hn : (∫⁻ x in cube d, ∑' n : Frequency d, ‖f (fun i => x i+(n i:ℝ))‖ₑ) ≠ ⊤ := by
    rw [unfold_lintegral d _ hm.enorm]
    exact hf.2.ne
  have ha := ae_lt_top' (Measurable.aemeasurable (Measurable.tsum (fun n : Frequency d =>
    hm.enorm.comp (show Measurable (fun x : Fin d → ℝ => fun i => x i+(n i:ℝ)) by fun_prop)))) hn
  filter_upwards [ha] with x hx
  exact (tsum_enorm_ne_top_iff_summable_norm.mp hx.ne).of_norm

lemma periodization_integrable (d : ℕ) (f : (Fin d → ℝ) → ℝ)
    (hm : Measurable f) (hf : Integrable f) :
    IntegrableOn (fun x => ∑' n : Frequency d, f (fun i => x i+(n i:ℝ))) (cube d) := by
  refine ⟨(Measurable.tsum (fun n : Frequency d =>
    hm.comp (show Measurable (fun x : Fin d → ℝ => fun i => x i+(n i:ℝ)) by fun_prop))).aestronglyMeasurable, ?_⟩
  apply lt_of_le_of_lt (lintegral_mono (fun x => enorm_tsum_le_tsum_enorm))
  rw [unfold_lintegral d _ hm.enorm]
  exact hf.2

lemma unfold_integral (d : ℕ) (f : (Fin d → ℝ) → ℝ)
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
    filter_upwards [] with x
    congr 1
    funext i
    change x i+(n i:ℝ) = (n i:ℝ)+x i
    ring
  · rw [translated_norm_sum_integral d f hm]
    exact hf.2.ne

#print axioms unfold_integral
end DGRHS.Gaussian.D11Imported.PeriodizationCube
