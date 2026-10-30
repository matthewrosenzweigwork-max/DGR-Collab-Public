import DGPS.Examples.PolynomialSpeciesReflectionOptimizers
import DGPS.Structural.SmallRateCircle

/-! Literal x↦−x pushforward for the actual polynomial chart laws. -/
noncomputable section
open MeasureTheory Filter Topology
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization
open DGPS.Examples.PolynomialEquilibrium
namespace DGPS.Examples.PolynomialSpecies

/-- Angular reflection of the retained chart induces the literal physical
reflection of its actual absolute density. -/
theorem polynomial_reflected_chart_density (h : ℝ) (u v : PeriodicC2_STR02969)
    (huv : ∀ t : ℝ, v.val (-t) = u.val t) (x : Torus 1) :
    (polynomialChartAbsolute h v).density (-x) = (polynomialChartAbsolute h u).density x := by
  let du := eulerDensity (polynomialLogReference h) u
  let dv := eulerDensity (polynomialLogReference h) v
  have hd (t : ℝ) : dv.val (-t) = du.val t := by
    have he := polynomialRangeDensity_reflection h (root_EX054 h) u v huv t
    rw [polynomialRangeDensity_actual, polynomialRangeDensity_actual] at he
    exact he
  have hang : angEquiv (-x) = -angEquiv x := by
    change angRescale (-x 0) = -angRescale (x 0)
    exact map_neg angRescale (x 0)
  have hcoe : ((angSec (angEquiv (-x)) : ℝ) : AngCircle) =
      ((-angSec (angEquiv x) : ℝ) : AngCircle) := by
    rw [coe_angSec_STR02962, hang]
    change -angEquiv x = -((angSec (angEquiv x) : ℝ) : AngCircle)
    rw [coe_angSec_STR02962]
  have heval : dv.val (angSec (angEquiv (-x))) = dv.val (-angSec (angEquiv x)) := by
    calc
      _ = dv.isPerHolder.1.lift ((angSec (angEquiv (-x)) : ℝ) : AngCircle) :=
        (dv.isPerHolder.1.lift_coe _).symm
      _ = dv.isPerHolder.1.lift ((-angSec (angEquiv x) : ℝ) : AngCircle) := congrArg _ hcoe
      _ = _ := dv.isPerHolder.1.lift_coe _
  rw [polynomialChartAbsolute_density, polynomialChartAbsolute_density]
  exact heval.trans (hd _)

/-- Probability-law pushforward by the physical reflection. This fixes the
orientation and does not identify merely formal chart parameters. -/
theorem polynomial_reflected_chart_pushforward (h : ℝ) (u v : PeriodicC2_STR02969)
    (huv : ∀ t : ℝ, v.val (-t) = u.val t) :
    (densityMeasure (polynomialChartAbsolute h v) : Measure (Torus 1)) =
      Measure.map (fun x : Torus 1 => -x) (densityMeasure (polynomialChartAbsolute h u) : Measure (Torus 1)) := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map continuous_neg.measurable.aemeasurable f.continuous.aestronglyMeasurable,
    Structural.budget_integral_densityMeasure, Structural.budget_integral_densityMeasure]
  have hd (x : Torus 1) : (polynomialChartAbsolute h v).density x =
      (polynomialChartAbsolute h u).density (-x) := by
    simpa only [neg_neg] using polynomial_reflected_chart_density h u v huv (-x)
  simp_rw [hd]
  have he := integral_neg_eq_self
    (fun x : Torus 1 => (polynomialChartAbsolute h u).density x * f (-x)) (haar 1)
  simpa only [neg_neg] using he

end DGPS.Examples.PolynomialSpecies
