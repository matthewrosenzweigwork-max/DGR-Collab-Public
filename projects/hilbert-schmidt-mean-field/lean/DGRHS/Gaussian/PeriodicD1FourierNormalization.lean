import DGRHS.Gaussian.PeriodicDimensionThreshold

/-! UNCOMPILED CANDIDATE (Claude D1 operator review, 2026-10-03). Not elaborated.
Dimension-one integer frequency identification for the actual source Green
kernel. It does not identify the singular circle logarithm or assume its
Fourier coefficients. All six declaration names and statements are unchanged
from the supplied draft, because Codex drafts (CircleKernel, AbelPreparation)
already use them. Only proof scripts gained `first` fallbacks. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.Periodic

def periodicD1Frequency (k : ℤ) : PeriodicFrequency (Fin 1) := fun _ => k

lemma periodicD1Frequency_ne_zero {k : ℤ} (hk : k≠0) : periodicD1Frequency k≠0 := by
  intro h
  exact hk (congrFun h 0)

lemma norm_periodicD1Frequency (k : ℤ) :
    ‖periodicFrequencyVector (periodicD1Frequency k)‖=|(k:ℝ)| := by
  have hs : ‖periodicFrequencyVector (periodicD1Frequency k)‖^2=(k:ℝ)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    first
    | (simp [periodicFrequencyVector,periodicD1Frequency]; done)
    | simp [periodicD1Frequency]
  have hn := norm_nonneg (periodicFrequencyVector (periodicD1Frequency k))
  first
  | nlinarith [abs_nonneg (k:ℝ),sq_abs (k:ℝ)]
  | rw [← Real.sqrt_sq hn,hs,Real.sqrt_sq_eq_abs]

lemma periodicD1_green_multiplier_constant :
    periodicLogConstant (Fin 1)/(2*Real.pi)=(1:ℝ)/2 := by
  first
  | (have h := congrArg (fun x : ℝ => x⁻¹) periodicStabilityThreshold_one
     simpa [periodicStabilityThreshold,inv_div] using h)
  | (have hc : periodicLogConstant (Fin 1)≠0 := periodicLogConstant_pos.ne'
     have hπ : (2*Real.pi)≠0 := by positivity
     have h := periodicStabilityThreshold_one
     simp only [periodicStabilityThreshold,Fintype.card_fin,pow_one] at h
     field_simp at h ⊢
     linarith)

lemma periodicD1_log_fourierCoeff {k : ℤ} (hk : k≠0) :
    periodicLogFourierCoeff (periodicD1Frequency k)=((1/(2*|(k:ℝ)|):ℝ):ℂ) := by
  have hk' : |(k:ℝ)|≠0 := abs_ne_zero.mpr (Int.cast_ne_zero.mpr hk)
  first
  | (simp only [periodicLogFourierCoeff,if_neg (periodicD1Frequency_ne_zero hk),
      Fintype.card_fin,pow_one,norm_periodicD1Frequency,periodicD1_green_multiplier_constant]
     congr 1
     simp only [div_eq_mul_inv,mul_inv_rev]
     ring1)
  | (rw [periodicLogFourierCoeff,if_neg (periodicD1Frequency_ne_zero hk)]
     congr 1
     simp only [Fintype.card_fin,pow_one,norm_periodicD1Frequency]
     rw [periodicD1_green_multiplier_constant]
     field_simp)

/-- Nonzero Fourier coefficients of the existing actual Green representative.
The circle-logarithm coefficient computation is a separate (Codex) step. -/
theorem periodicD1_green_fourierCoeff {k : ℤ} (hk : k≠0) :
    UnitAddTorus.mFourierCoeff (fun x : PeriodicTorus (Fin 1) =>
      (periodicLogKernel x:ℂ)) (periodicD1Frequency k)=((1/(2*|(k:ℝ)|):ℝ):ℂ) := by
  rw [periodicLogKernel_fourierCoeff,periodicD1_log_fourierCoeff hk]

end DGRHS.Periodic
