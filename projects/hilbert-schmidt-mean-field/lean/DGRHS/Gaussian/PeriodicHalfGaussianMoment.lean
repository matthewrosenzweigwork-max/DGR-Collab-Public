import DGRHS.Gaussian.PeriodicHalfGaussianRadial

/-! Properness and the actual critical Gaussian expectation are derived
from the native radial identity and the proved radial domination.
No Gaussian moment/properness or desired critical lower bound is an input. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DGRHS.Periodic

lemma periodicCriticalRadialIntegral_lt_top (N : ℕ) (hN : 1 ≤ N) :
    periodicCriticalRadialIntegral N < ∞ := by
  have hnng : ∀ᵐ r ∂volume.restrict (Ioi (0:ℝ)),
      0 ≤ 2*r*Real.exp (-r^2)*(periodicBesselI0 (2*r/Real.sqrt (N:ℝ)))^N := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr' : 0 < r := hr
    exact mul_nonneg (by positivity) (pow_nonneg (periodicBesselI0_pos _).le N)
  have he := ofReal_integral_eq_lintegral_ofReal (periodic_critical_radial_integrable N hN) hnng
  change _ = periodicCriticalRadialIntegral N at he
  rw [←he]
  exact ENNReal.ofReal_lt_top

/-- Genuine critical Gaussian Bessel factor, proper for every positive particle number. -/
theorem periodic_halfGaussian_Bessel_integrable (N : ℕ) (hN : 1 ≤ N) :
    Integrable (fun p : ℝ × ℝ => (periodicBesselI0
      (2*Real.sqrt (p.1^2+p.2^2)/Real.sqrt (N:ℝ)))^N)
      ((gaussianReal 0 (1/2)).prod (gaussianReal 0 (1/2))) := by
  have hs : StronglyMeasurable (fun p : ℝ × ℝ => (periodicBesselI0
      (2*Real.sqrt (p.1^2+p.2^2)/Real.sqrt (N:ℝ)))^N) :=
    (stronglyMeasurable_periodicBesselI0.comp_measurable (by fun_prop)).pow N
  refine ⟨hs.aestronglyMeasurable, (hasFiniteIntegral_iff_norm _).mpr ?_⟩
  have he : (fun p : ℝ × ℝ => ENNReal.ofReal ‖(periodicBesselI0
      (2*Real.sqrt (p.1^2+p.2^2)/Real.sqrt (N:ℝ)))^N‖) =
    (fun p => ENNReal.ofReal ((periodicBesselI0
      (2*Real.sqrt (p.1^2+p.2^2)/Real.sqrt (N:ℝ)))^N)) := by
    funext p
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (periodicBesselI0_pos _).le N)]
  rw [he,periodic_halfGaussian_Bessel_identity]
  exact periodicCriticalRadialIntegral_lt_top N hN

/-- Exact original critical radial lower bound for the actual Gaussian law. -/
theorem periodic_halfGaussian_Bessel_sqrt_lower (N : ℕ) (hN : 1 ≤ N) :
    Real.sqrt Real.pi*Real.sqrt (N:ℝ) ≤
      ∫ p : ℝ × ℝ,(periodicBesselI0
        (2*Real.sqrt (p.1^2+p.2^2)/Real.sqrt (N:ℝ)))^N
        ∂(gaussianReal 0 (1/2)).prod (gaussianReal 0 (1/2)) := by
  have hi := periodic_halfGaussian_Bessel_integrable N hN
  have hnng : ∀ᵐ p ∂(gaussianReal 0 (1/2)).prod (gaussianReal 0 (1/2)),
      0 ≤ (periodicBesselI0 (2*Real.sqrt (p.1^2+p.2^2)/Real.sqrt (N:ℝ)))^N :=
    Filter.Eventually.of_forall (fun p => pow_nonneg (periodicBesselI0_pos _).le N)
  have he := ofReal_integral_eq_lintegral_ofReal hi hnng
  rw [periodic_halfGaussian_Bessel_identity] at he
  have hl := ENNReal.toReal_mono (periodicCriticalRadialIntegral_lt_top N hN).ne
    (periodicCriticalRadialIntegral_sqrt_lower N hN)
  rw [←he,ENNReal.toReal_ofReal (integral_nonneg_of_ae hnng),
    ENNReal.toReal_ofReal (by positivity)] at hl
  exact hl

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicCriticalRadialIntegral_lt_top
#print axioms DGRHS.Periodic.periodic_halfGaussian_Bessel_integrable
#print axioms DGRHS.Periodic.periodic_halfGaussian_Bessel_sqrt_lower
#check @DGRHS.Periodic.periodic_halfGaussian_Bessel_integrable
#check @DGRHS.Periodic.periodic_halfGaussian_Bessel_sqrt_lower
