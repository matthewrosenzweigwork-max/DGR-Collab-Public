import DGRHS.Gaussian.PeriodicBesselCritical
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DGRHS.Periodic

lemma periodic_quartic_radial_integral (N : ℕ) (hN : 1 ≤ N) :
    (∫ r in Ioi (0:ℝ),2*r*Real.exp (-(r^4/(4*(N:ℝ))))) =
      Real.sqrt Real.pi*Real.sqrt (N:ℝ) := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have h := integral_comp_rpow_Ioi (fun u : ℝ => Real.exp (-(1/(4*(N:ℝ)))*u^2))
    (p := 2) (by norm_num)
  have he : (∫ r in Ioi (0:ℝ),2*r*Real.exp (-(r^4/(4*(N:ℝ))))) =
      ∫ u in Ioi (0:ℝ),Real.exp (-(1/(4*(N:ℝ)))*u^2) := by
    rw [←h]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    norm_num only [show (2:ℝ)-1=1 by norm_num,abs_of_pos (by norm_num : (0:ℝ)<2),
      Real.rpow_one,Real.rpow_two,smul_eq_mul]
    congr 1
    congr 1
    ring
  rw [he,integral_gaussian_Ioi]
  rw [one_div,div_inv_eq_mul,Real.sqrt_mul Real.pi_pos.le,
    Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
  rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.sqrt_sq (by norm_num : (0:ℝ)≤2)]
  ring

/-- Properness is derived from the exact nonzero integral formula; no
quartic-tail integrability is added as a premise. -/
lemma periodic_quartic_radial_integrable (N : ℕ) (hN : 1 ≤ N) :
    IntegrableOn (fun r : ℝ => 2*r*Real.exp (-(r^4/(4*(N:ℝ))))) (Ioi 0) := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  by_contra h
  have he := periodic_quartic_radial_integral N hN
  rw [integral_undef h] at he
  have hp : 0 < Real.sqrt Real.pi*Real.sqrt (N:ℝ) :=
    mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (Real.sqrt_pos.mpr hn)
  linarith

/-- The exact source radial factor has at least sqrt(pi)*sqrt(N), for
EVERY N>=1, from a genuine global circle inequality and native power
substitution. No Bessel expansion, asymptotic or radial bound is a premise. -/
theorem periodicCriticalRadialIntegral_sqrt_lower (N : ℕ) (hN : 1 ≤ N) :
    ENNReal.ofReal (Real.sqrt Real.pi*Real.sqrt (N:ℝ)) ≤ periodicCriticalRadialIntegral N := by
  have hnng : ∀ᵐ r ∂volume.restrict (Ioi (0:ℝ)),0 ≤ 2*r*Real.exp (-(r^4/(4*(N:ℝ)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    change 0 < r at hr
    positivity
  have he := ofReal_integral_eq_lintegral_ofReal (periodic_quartic_radial_integrable N hN) hnng
  rw [periodic_quartic_radial_integral N hN] at he
  rw [he]
  exact periodicCriticalRadialIntegral_lower N hN

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_quartic_radial_integral
#print axioms DGRHS.Periodic.periodic_quartic_radial_integrable
#print axioms DGRHS.Periodic.periodicCriticalRadialIntegral_sqrt_lower
#check @DGRHS.Periodic.periodicCriticalRadialIntegral_sqrt_lower
