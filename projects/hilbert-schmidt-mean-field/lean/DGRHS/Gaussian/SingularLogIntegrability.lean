import DGRHS.Gaussian.LogPhysicalPotential
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/- The singular absolute logarithm is infinite at spatial collisions.
This is a faithful L1 representation for the original attractive theorem;
properness of the totalized real logarithm alone is insufficient for it. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Gaussian
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

def singularAbsLog (p : E × E) : ℝ≥0∞ :=
  if ‖p.1-p.2‖ = 0 then ∞ else ENNReal.ofReal |Real.log ‖p.1-p.2‖|

lemma measurable_singularAbsLog : Measurable (singularAbsLog (E := E)) := by
  have hm : Measurable (fun p : E × E => ‖p.1-p.2‖) :=
    (measurable_fst.sub measurable_snd).norm
  exact measurable_const.ite (measurableSet_eq_fun hm measurable_const)
    (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
      (Real.measurable_log.comp hm)))

lemma measurable_logPhysicalPair : Measurable (logPhysicalPair (E := E)) := by
  exact (Real.measurable_log.comp ((measurable_fst.sub measurable_snd).norm)).neg

theorem singularAbsLog_finite_iff (μ : Measure E) :
    (∫⁻ p,singularAbsLog p ∂μ.prod μ) < ∞ ↔
      Integrable logPhysicalPair (μ.prod μ) ∧
        (∀ᵐ p : E × E ∂μ.prod μ,p.1 ≠ p.2) := by
  constructor
  · intro hf
    have hn : ∀ᵐ p : E × E ∂μ.prod μ,p.1 ≠ p.2 := by
      filter_upwards [ae_lt_top measurable_singularAbsLog hf.ne] with p hp
      intro he
      have hz : ‖p.1-p.2‖ = 0 := by simp [he]
      simpa [singularAbsLog,hz] using hp
    have hbound : ∀ p : E × E,
        ENNReal.ofReal ‖logPhysicalPair p‖ ≤ singularAbsLog p := by
      intro p
      by_cases hz : ‖p.1-p.2‖ = 0
      · simp [singularAbsLog,hz]
      · simp [singularAbsLog,hz,logPhysicalPair,Real.norm_eq_abs]
    refine ⟨⟨measurable_logPhysicalPair.aestronglyMeasurable,?_⟩,hn⟩
    apply (hasFiniteIntegral_iff_norm _).mpr
    exact (lintegral_mono hbound).trans_lt hf
  · rintro ⟨hi,hn⟩
    have he : singularAbsLog =ᵐ[μ.prod μ]
        (fun p : E × E => ENNReal.ofReal ‖logPhysicalPair p‖) := by
      filter_upwards [hn] with p hp
      have hz : ‖p.1-p.2‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp)
      simp [singularAbsLog,hz,logPhysicalPair,Real.norm_eq_abs]
    rw [lintegral_congr_ae he]
    exact (hasFiniteIntegral_iff_norm _).mp hi.hasFiniteIntegral

end DGRHS.Gaussian
#check @DGRHS.Gaussian.singularAbsLog_finite_iff
#print axioms DGRHS.Gaussian.singularAbsLog_finite_iff
