/- UNCHECKED outside the frozen coordinator snapshot. Actual finite-coordinate
product laws. These bridge a fixed infinite iid sample to each particle product
and match every retained finite Gaussian vector to the SAME countable product. -/
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import DGRHS.Gaussian.FiniteLaplace
import DGRHS.Gaussian.Imported.IsonormalProcess
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.CLT
variable {S j : Type*} [MeasurableSpace S] [Fintype j]

lemma finiteCoordinateSample_measurePreserving
    (μ : Measure S) [IsProbabilityMeasure μ]
    (f : j → ℕ) (hf : Function.Injective f) :
    MeasurePreserving (fun ω : ℕ → S => fun i : j => ω (f i))
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.pi (fun _ : j => μ)) := by
  let P := Measure.infinitePi (fun _ : ℕ => μ)
  have hi : iIndepFun (fun n (ω : ℕ → S) => ω n) P :=
    iIndepFun_infinitePi (X := fun _ : ℕ => id) (fun _ => measurable_id)
  have hif : iIndepFun (fun i (ω : ℕ → S) => ω (f i)) P := hi.precomp (g := f) hf
  refine ⟨measurable_pi_iff.mpr (fun i => measurable_pi_apply (f i)), ?_⟩
  rw [iIndepFun.map_fun_eq_pi_map (fun i => (measurable_pi_apply (f i)).aemeasurable) hif]
  congr 1
  funext i
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => μ) (f i)).map_eq

lemma prefixSample_measurePreserving (μ : Measure S) [IsProbabilityMeasure μ] (N : ℕ) :
    MeasurePreserving (fun ω : ℕ → S => fun i : Fin N => ω i)
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.pi (fun _ : Fin N => μ)) :=
  finiteCoordinateSample_measurePreserving μ (fun i : Fin N => (i : ℕ)) Fin.val_injective

lemma selectedGaussian_measurePreserving (f : j → ℕ) (hf : Function.Injective f) :
    MeasurePreserving (fun ω : ℕ → ℝ => fun i : j => ω (f i))
      IsonormalProcess.iidStdGaussian (DGRHS.Gaussian.finiteStandardGaussian j) := by
  exact finiteCoordinateSample_measurePreserving (gaussianReal 0 1) f hf

lemma identDistrib_selectedGaussian_polynomial
    (f : j → ℕ) (hf : Function.Injective f) (G : (j → ℝ) → ℝ) (hG : Measurable G) :
    IdentDistrib (fun ω : ℕ → ℝ => G (fun i => ω (f i))) G
      IsonormalProcess.iidStdGaussian (DGRHS.Gaussian.finiteStandardGaussian j) := by
  let m := selectedGaussian_measurePreserving f hf
  refine ⟨hG.aemeasurable.comp_aemeasurable m.aemeasurable,hG.aemeasurable,?_⟩
  rw [← Function.comp_def,← Measure.map_map hG m.measurable,m.map_eq]

end DGRHS.CLT
#print axioms DGRHS.CLT.finiteCoordinateSample_measurePreserving
#print axioms DGRHS.CLT.prefixSample_measurePreserving
#print axioms DGRHS.CLT.selectedGaussian_measurePreserving
#print axioms DGRHS.CLT.identDistrib_selectedGaussian_polynomial
