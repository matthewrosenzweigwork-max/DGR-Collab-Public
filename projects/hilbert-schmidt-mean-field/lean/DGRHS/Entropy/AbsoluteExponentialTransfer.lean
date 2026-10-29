/- Source dynamicEntropyTransfers: absolute EXPECTATION, not absolute mean.
Actual two-sign proper exponential moments imply a proper absolute competitor
expectation using the existing exact DV/Fatou theorem, with the source log2. -/
import DGRHS.Entropy.ExponentialTransfer
noncomputable section
open MeasureTheory InformationTheory
namespace DGRHS.Entropy

theorem entropy_absolute_expectation_scaled_of_two_exponential_bounds
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (u : Ω→ℝ) (hu : StronglyMeasurable u) (ε : ℝ) (hε : 0<ε)
    (hp : Integrable (fun x=>Real.exp (ε*u x)) μ)
    (hm : Integrable (fun x=>Real.exp (-(ε*u x))) μ)
    (hKL : klDiv ν μ≠⊤) (C : ℝ)
    (hCp : (∫ x,Real.exp (ε*u x) ∂μ)≤C)
    (hCm : (∫ x,Real.exp (-(ε*u x)) ∂μ)≤C) :
    Integrable u ν ∧ (∫ x,|u x| ∂ν)≤ε⁻¹*((klDiv ν μ).toReal+Real.log (2*C)) := by
  have he := integrable_exp_abs_of_two_signs μ (fun x=>ε*u x) (hu.const_mul ε) hp hm
  have hpoint (x : Ω) : Real.exp |ε*u x|≤Real.exp (ε*u x)+Real.exp (-(ε*u x)) := by
    by_cases hh : 0≤ε*u x
    · rw [abs_of_nonneg hh]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_neg (lt_of_not_ge hh)]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  have hexp : (∫ x,Real.exp |ε*u x| ∂μ)≤2*C := by
    have hi := integral_mono he (hp.add hm) hpoint
    simp only [Pi.add_apply] at hi
    rw [integral_add hp hm] at hi
    linarith
  obtain ⟨hi,hb⟩ := entropy_integrable_abs_of_exponential μ ν (fun x=>ε*u x) (hu.const_mul ε) he hKL
  have hiu : Integrable u ν := by
    have h := hi.const_mul ε⁻¹
    simpa only [←mul_assoc,inv_mul_cancel₀ hε.ne',one_mul] using h
  have hlog := Real.log_le_log (integral_exp_pos he) hexp
  have habs : (fun x=>|ε*u x|)=(fun x=>ε*|u x|) := by
    funext x
    rw [abs_mul,abs_of_pos hε]
  rw [habs,integral_const_mul] at hb
  refine ⟨hiu,?_⟩
  have hh := hb.trans (add_le_add le_rfl hlog)
  have hd : (∫ x,|u x| ∂ν)≤((klDiv ν μ).toReal+Real.log (2*C))/ε :=
    (le_div_iff₀ hε).mpr (by simpa only [mul_comm] using hh)
  simpa only [div_eq_mul_inv,mul_comm] using hd
end DGRHS.Entropy
#check @DGRHS.Entropy.entropy_absolute_expectation_scaled_of_two_exponential_bounds
#print axioms DGRHS.Entropy.entropy_absolute_expectation_scaled_of_two_exponential_bounds
