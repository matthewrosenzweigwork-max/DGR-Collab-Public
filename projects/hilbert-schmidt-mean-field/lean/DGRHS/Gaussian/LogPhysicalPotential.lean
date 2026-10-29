import DGRHS.Gaussian.GaussianRieszPhysicalPotential

/-! Actual logarithmic physical kernel, source eq:gDef (s=0).
Source SHA256 6f52778d92aa534e2b5851ca0f6b0712dc56470259cb3efcb7146ac2384dac0c.
The diagonal is totalized by Real.log 0 = 0. Density null-singletons are
required before using the singular off-origin estimates. Tail integrability
is derived from the source pair-log assumption, not supplied independently. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

def logPhysicalPair (p : E × E) : ℝ := -Real.log ‖p.1-p.2‖

lemma log_one_add_le_abs_log (r : ℝ) (hr : 0 ≤ r) :
    Real.log (1+r) ≤ Real.log 2 + |Real.log r| := by
  by_cases h : r ≤ 1
  · have hlog := Real.log_le_log (by positivity : 0 < 1+r) (show 1+r ≤ 2 by linarith)
    exact hlog.trans (le_add_of_nonneg_right (abs_nonneg _))
  · have hp : 0 < r := by linarith
    have hlog := Real.log_le_log (by positivity : 0 < 1+r) (show 1+r ≤ 2*r by linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hp.ne'] at hlog
    exact hlog.trans (by linarith [le_abs_self (Real.log r)])

lemma log_one_add_norm_sub_le (x y : E) :
    Real.log (1+‖x-y‖) ≤ Real.log (1+‖x‖) + Real.log (1+‖y‖) := by
  have hn := norm_sub_le x y
  have hp := mul_nonneg (norm_nonneg x) (norm_nonneg y)
  have hlog := Real.log_le_log (by positivity : 0 < 1+‖x-y‖)
    (show 1+‖x-y‖ ≤ (1+‖x‖)*(1+‖y‖) by nlinarith)
  rwa [Real.log_mul (by positivity : (1+‖x‖) ≠ 0) (by positivity : (1+‖y‖) ≠ 0)] at hlog

lemma integrable_log_one_add_norm_of_pair_log
    (μ : Measure E) [IsProbabilityMeasure μ]
    (hpair : Integrable logPhysicalPair (μ.prod μ)) :
    Integrable (fun y : E => Real.log (1+‖y‖)) μ := by
  obtain ⟨x,hx⟩ := hpair.prod_right_ae.exists
  have hsection : Integrable (fun y : E => |Real.log ‖x-y‖|) μ := by
    simpa [logPhysicalPair, Real.norm_eq_abs] using hx.norm
  refine ((integrable_const (Real.log (1+‖x‖)+Real.log 2)).add hsection).mono'
    (Real.measurable_log.comp (measurable_const.add measurable_id.norm)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith [norm_nonneg y]))]
  have hn := log_one_add_norm_sub_le x (x-y)
  simp only [sub_sub_cancel] at hn
  change Real.log (1+‖y‖) ≤ (Real.log (1+‖x‖)+Real.log 2)+|Real.log ‖x-y‖|
  linarith [log_one_add_le_abs_log ‖x-y‖ (norm_nonneg _)]

end DGRHS.Gaussian
#check @DGRHS.Gaussian.logPhysicalPair
#print axioms DGRHS.Gaussian.logPhysicalPair
#check @DGRHS.Gaussian.log_one_add_le_abs_log
#print axioms DGRHS.Gaussian.log_one_add_le_abs_log
#check @DGRHS.Gaussian.log_one_add_norm_sub_le
#print axioms DGRHS.Gaussian.log_one_add_norm_sub_le
#check @DGRHS.Gaussian.integrable_log_one_add_norm_of_pair_log
#print axioms DGRHS.Gaussian.integrable_log_one_add_norm_of_pair_log
