import DGRHS.Gaussian.PeriodicTrialParticleMean
import DGRHS.Concentration.EntropyVariational

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Periodic

/-- The normalized density variational estimate needs only genuine proper
weighted energy; the exponent itself need not be bounded. The infinite
partition case is retained in ENNReal rather than passed through toReal. -/
theorem positive_density_partition_lower {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f U : X → ℝ} {c C : ℝ}
    (hf : DGRHS.Concentration.PositiveBounded μ f c C) (hn : (∫ x,f x ∂μ)=1)
    (hU : AEStronglyMeasurable U μ) (hfu : Integrable (fun x => f x*U x) μ) :
    ENNReal.ofReal (Real.exp ((∫ x,f x*U x ∂μ)-(∫ x,f x*Real.log (f x) ∂μ))) ≤
      ∫⁻ x,ENNReal.ofReal (Real.exp (U x)) ∂μ := by
  by_cases ht : (∫⁻ x,ENNReal.ofReal (Real.exp (U x)) ∂μ)=⊤
  · rw [ht]; exact le_top
  have he : Integrable (fun x => Real.exp (U x)) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (Real.continuous_exp.comp_aestronglyMeasurable hU)
      (Filter.Eventually.of_forall fun x => (Real.exp_pos (U x)).le)).mp ht
  let A := ∫ x,Real.exp (U x) ∂μ
  have hA : 0 < A := integral_exp_pos he
  have hfc := hf.integrable.mul_const (Real.log A-1)
  have hec := he.mul_const (1/A)
  have hr := (hf.mul_log_integrable.add hfc).add hec
  have hv := integral_mono_ae hfu hr (hf.bounds.mono fun x hx => by
    simpa only [Real.log_one,sub_zero,Pi.add_apply] using
      DGRHS.Concentration.logarithmic_variational_pointwise (u := U x)
        (hf.lower_pos.trans_le hx.1) (by norm_num : (0:ℝ)<1) hA)
  simp only [Pi.add_apply] at hv
  have hs : Integrable (fun x => f x*Real.log (f x)+f x*(Real.log A-1)) μ :=
    hf.mul_log_integrable.add hfc
  rw [integral_add hs hec,
    integral_add hf.mul_log_integrable hfc,integral_mul_const,integral_mul_const,hn] at hv
  have ha : A*(1/A)=1 := by field_simp
  change _ ≤ _+1*(Real.log A-1)+A*(1/A) at hv
  rw [ha] at hv
  have hx : (∫ x,f x*U x ∂μ)-(∫ x,f x*Real.log (f x) ∂μ) ≤ Real.log A := by linarith
  have hb : Real.exp ((∫ x,f x*U x ∂μ)-(∫ x,f x*Real.log (f x) ∂μ)) ≤ A := by
    simpa only [Real.exp_log hA] using Real.exp_le_exp.mpr hx
  rw [← ofReal_integral_eq_lintegral_ofReal he (Filter.Eventually.of_forall fun x => (Real.exp_pos (U x)).le)]
  exact ENNReal.ofReal_le_ofReal hb

end DGRHS.Periodic
#print axioms DGRHS.Periodic.positive_density_partition_lower
#check @DGRHS.Periodic.positive_density_partition_lower
