import DGRHS.Gaussian.PeriodicBesselCritical
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Genuine properness of the actual source
radial factor, independent of the still-open full-to-first-shell comparison. -/
noncomputable section
open MeasureTheory Set Filter
namespace DGRHS.Periodic

lemma periodicBesselI0_le_exp_abs (z : ℝ) : periodicBesselI0 z ≤ Real.exp |z| := by
  unfold periodicBesselI0
  have hh (x : UnitAddCircle) : z*(fourier 1 x).re ≤ |z| := by
    have hc : |(fourier 1 x).re| ≤ 1 :=
      (Complex.abs_re_le_norm _).trans_eq (by simp [fourier_apply])
    exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hc)
  exact (integral_mono (periodicBessel_exp_integrable z) (integrable_const _)
    (fun x => Real.exp_le_exp.mpr (hh x))).trans_eq (by simp)

lemma stronglyMeasurable_periodicBesselI0 : StronglyMeasurable periodicBesselI0 := by
  have h : Continuous (fun p : ℝ × UnitAddCircle => Real.exp (p.1*(fourier 1 p.2).re)) := by fun_prop
  exact h.stronglyMeasurable.integral_prod_right' (ν := AddCircle.haarAddCircle)

lemma periodic_critical_radial_integrable (N : ℕ) (hN : 1 ≤ N) :
    IntegrableOn (fun r : ℝ => 2*r*Real.exp (-r^2)*(periodicBesselI0 (2*r/Real.sqrt (N:ℝ)))^N) (Ioi 0) := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hs : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hn
  have hg : IntegrableOn (fun r : ℝ => r*Real.exp (-(1/2:ℝ)*r^2)) (Ioi 0) :=
    (integrable_mul_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/2)).integrableOn
  have hdom := hg.const_mul (2*Real.exp (2*(N:ℝ)))
  apply hdom.mono'
  · have hI : StronglyMeasurable (fun r : ℝ => periodicBesselI0 (2*r/Real.sqrt (N:ℝ))) :=
      stronglyMeasurable_periodicBesselI0.comp_measurable (by fun_prop)
    exact ((by fun_prop : Continuous (fun r : ℝ => 2*r*Real.exp (-r^2))).stronglyMeasurable.mul
      (hI.pow N)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    change 0 < r at hr
    have hBpos := periodicBesselI0_pos (2*r/Real.sqrt (N:ℝ))
    rw [Real.norm_eq_abs,abs_of_pos (by positivity)]
    have hI := pow_le_pow_left₀ (periodicBesselI0_pos _).le (periodicBesselI0_le_exp_abs (2*r/Real.sqrt (N:ℝ))) N
    rw [abs_of_pos (by positivity : 0 < 2*r/Real.sqrt (N:ℝ)),←Real.exp_nat_mul] at hI
    have he : (N:ℝ)*(2*r/Real.sqrt (N:ℝ))=2*Real.sqrt (N:ℝ)*r := by
      have hh := Real.sq_sqrt hn.le
      field_simp
      nlinarith [hh]
    rw [he] at hI
    have hy : -(r^2)+2*Real.sqrt (N:ℝ)*r ≤ -(1/2:ℝ)*r^2+2*(N:ℝ) := by
      have hh := sq_nonneg (r-2*Real.sqrt (N:ℝ))
      nlinarith [Real.sq_sqrt hn.le]
    calc
      _ ≤ 2*r*Real.exp (-r^2)*Real.exp (2*Real.sqrt (N:ℝ)*r) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
      _ = 2*r*Real.exp (-(r^2)+2*Real.sqrt (N:ℝ)*r) := by rw [Real.exp_add];ring
      _ ≤ 2*r*Real.exp (-(1/2:ℝ)*r^2+2*(N:ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hy) (by positivity)
      _ = _ := by rw [Real.exp_add];ring

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_critical_radial_integrable

#print axioms DGRHS.Periodic.stronglyMeasurable_periodicBesselI0
#check @DGRHS.Periodic.periodic_critical_radial_integrable
