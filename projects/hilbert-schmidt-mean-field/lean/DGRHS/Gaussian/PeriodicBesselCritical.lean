import DGRHS.Gaussian.PeriodicBesselCircle

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DGRHS.Periodic

lemma periodic_critical_radial_exponent_lower (N : ℕ) (hN : 1 ≤ N) (r : ℝ) :
    -(r^4/(4*(N:ℝ))) ≤ -(r^2)+(N:ℝ)*Real.log (periodicBesselI0 (2*r/Real.sqrt (N:ℝ))) := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hs : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hn
  have h2 : (2*r/Real.sqrt (N:ℝ))^2=4*r^2/(N:ℝ) := by
    rw [div_pow,mul_pow,Real.sq_sqrt hn.le];ring
  have h4 : (2*r/Real.sqrt (N:ℝ))^4=16*r^4/(N:ℝ)^2 := by
    rw [show (2*r/Real.sqrt (N:ℝ))^4=((2*r/Real.sqrt (N:ℝ))^2)^2 by ring,h2]
    ring
  have h := mul_le_mul_of_nonneg_left (periodicBesselI0_log_quartic_lower (2*r/Real.sqrt (N:ℝ))) hn.le
  rw [h2,h4] at h
  have he : (N:ℝ)*((4*r^2/(N:ℝ))/4-(16*r^4/(N:ℝ)^2)/64)=r^2-r^4/(4*(N:ℝ)) := by
    field_simp
    <;> ring
  rw [he] at h
  linarith

lemma periodic_critical_radial_integrand_lower (N : ℕ) (hN : 1 ≤ N) (r : ℝ) (hr : 0 ≤ r) :
    2*r*Real.exp (-(r^4/(4*(N:ℝ)))) ≤
      2*r*Real.exp (-r^2)*(periodicBesselI0 (2*r/Real.sqrt (N:ℝ)))^N := by
  have h := Real.exp_le_exp.mpr (periodic_critical_radial_exponent_lower N hN r)
  rw [Real.exp_add,Real.exp_nat_mul,Real.exp_log (periodicBesselI0_pos _)] at h
  have hh := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2*r)
  convert hh using 1 <;> ring

/-- The actual source radial integral, retaining infinite values honestly. -/
def periodicCriticalRadialIntegral (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ r in Set.Ioi (0:ℝ),ENNReal.ofReal
    (2*r*Real.exp (-r^2)*(periodicBesselI0 (2*r/Real.sqrt (N:ℝ)))^N)

lemma periodicCriticalRadialIntegral_lower (N : ℕ) (hN : 1 ≤ N) :
    (∫⁻ r in Set.Ioi (0:ℝ),ENNReal.ofReal (2*r*Real.exp (-(r^4/(4*(N:ℝ)))))) ≤
      periodicCriticalRadialIntegral N := by
  unfold periodicCriticalRadialIntegral
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact ENNReal.ofReal_le_ofReal (periodic_critical_radial_integrand_lower N hN r hr.le)

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_critical_radial_exponent_lower
#print axioms DGRHS.Periodic.periodicCriticalRadialIntegral_lower
#check @DGRHS.Periodic.periodicCriticalRadialIntegral_lower
