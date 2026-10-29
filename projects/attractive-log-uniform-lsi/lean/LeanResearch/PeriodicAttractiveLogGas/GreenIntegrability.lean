import LeanResearch.PeriodicAttractiveLogGas.GreenBounds
import LeanResearch.PeriodicAttractiveLogGas.GreenDerivatives
import LeanResearch.PeriodicAttractiveLogGas.TorusIntegrability
import LeanResearch.PeriodicAttractiveLogGas.Collisions
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! Bounds and finite real-exponent moments for the actual regular Green
representative and its Euclidean torus gradient. The gradient and both Hessian
norms inherit exactly the same constant as the centered ordinary derivatives.
All `MemLp` statements use the specified probability Haar measure. The sole
exceptional point in the domination arguments is handled by the proved
singleton nullity; no value or differentiability of a derivative at the pole
is assumed.
-/

noncomputable section
open MeasureTheory Set Filter

namespace PeriodicAttractiveLogGas

/-- Norm-preserving descent transfers the existing centered Euclidean bounds
to the actual torus gradient and Hessian, without enlarging the constant. -/
theorem exists_regularGreenRepresentative_torus_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C ∧
      ‖greenGradient z‖ ≤ C / torusEuclideanNorm z ∧
      ‖greenHessian z‖ ≤ C / (torusEuclideanNorm z ^ 2) ∧
      ‖greenHessianOperator z‖ ≤ C / (torusEuclideanNorm z ^ 2) := by
  obtain ⟨C, hC, hb⟩ := exists_regularGreenRepresentative_bounds
  refine ⟨C, hC, ?_⟩
  intro z hz
  obtain ⟨h0, h1, h2⟩ := hb z hz
  have hx : centeredLift z ∈ offIntegerLattice := by
    simpa only [offIntegerLattice, mem_ofPred_eq, torusQuotient_centeredLift] using hz
  have hd := greenDifferential_lift_of_mem hx
  have hh := greenHessian_lift_of_mem hx
  simp only [torusQuotient_centeredLift] at hd hh
  refine ⟨h0, ?_, ?_, ?_⟩
  · simpa only [norm_greenGradient, hd] using h1
  · simpa only [hh] using h2
  · simpa only [norm_greenHessianOperator, hh] using h2

/-- Conversion of the proved real logarithmic moments to the library's
`ENNReal.ofReal` exponent, with its nonzero and finite-exponent conditions. -/
theorem memLp_log_torusEuclideanNorm (p : ℝ) (hp : 0 < p) :
    MemLp (fun z : Torus ↦ Real.log (torusEuclideanNorm z))
      (ENNReal.ofReal p) torusMeasure := by
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  apply (integrable_norm_rpow_iff
    measurable_torusEuclideanNorm.log.aestronglyMeasurable hpne ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs] using
    integrable_abs_log_torusEuclideanNorm_rpow p hp

/-- The inverse quotient radius belongs to every positive real `Lp` below
dimension two, including its totalized value at the origin. -/
theorem memLp_torusEuclideanNorm_inv (p : ℝ) (hp : 0 < p) (hp2 : p < 2) :
    MemLp (fun z : Torus ↦ (torusEuclideanNorm z)⁻¹)
      (ENNReal.ofReal p) torusMeasure := by
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  apply (integrable_norm_rpow_iff
    measurable_torusEuclideanNorm.inv.aestronglyMeasurable hpne ENNReal.ofReal_ne_top).mp
  have heq : (fun z : Torus ↦ ‖(torusEuclideanNorm z)⁻¹‖ ^ (ENNReal.ofReal p).toReal) =
      (fun z : Torus ↦ torusEuclideanNorm z ^ (-p)) := by
    funext z
    rw [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (torusEuclideanNorm_nonneg z)),
      Real.inv_rpow (torusEuclideanNorm_nonneg z), Real.rpow_neg (torusEuclideanNorm_nonneg z)]
  change Integrable (fun z : Torus ↦ ‖(torusEuclideanNorm z)⁻¹‖ ^
    (ENNReal.ofReal p).toReal) torusMeasure
  rw [heq]
  exact integrable_torusEuclideanNorm_rpow_neg p hp2

/-- The actual regular Green representative has every finite real moment in
the source range, with no assumed finite-moment or Green bound premise. -/
theorem memLp_regularGreenRepresentative (p : ℝ) (hp : 1 ≤ p) :
    MemLp regularGreenRepresentative (ENNReal.ofReal p) torusMeasure := by
  obtain ⟨C, _hC, hb⟩ := exists_regularGreenRepresentative_torus_bounds
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hlog := memLp_log_torusEuclideanNorm p hp0
  have hdom : MemLp (fun z : Torus ↦ C + ‖Real.log (torusEuclideanNorm z)‖)
      (ENNReal.ofReal p) torusMeasure := (memLp_const C).add hlog.norm
  refine hdom.mono' regularGreenRepresentative_measurable.aestronglyMeasurable ?_
  filter_upwards [torusMeasure.ae_ne (0 : Torus)] with z hz
  simp only [Real.norm_eq_abs]
  have htriangle := abs_add_le
    (regularGreenRepresentative z + Real.log (torusEuclideanNorm z))
    (-Real.log (torusEuclideanNorm z))
  have heq : (regularGreenRepresentative z + Real.log (torusEuclideanNorm z)) +
      (-Real.log (torusEuclideanNorm z)) = regularGreenRepresentative z := by ring
  rw [heq, abs_neg] at htriangle
  exact htriangle.trans (add_le_add (hb z hz).1 le_rfl)

/-- The actual Euclidean torus gradient has the requested subcritical
real-exponent `Lp` integrability. Its totalized origin value is immaterial. -/
theorem memLp_greenGradient (p : ℝ) (hp : 1 ≤ p) (hp2 : p < 2) :
    MemLp greenGradient (ENNReal.ofReal p) torusMeasure := by
  obtain ⟨C, _hC, hb⟩ := exists_regularGreenRepresentative_torus_bounds
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hdom := (memLp_torusEuclideanNorm_inv p hp0 hp2).const_mul C
  refine hdom.mono' measurable_greenGradient.aestronglyMeasurable ?_
  filter_upwards [torusMeasure.ae_ne (0 : Torus)] with z hz
  simpa only [div_eq_mul_inv] using (hb z hz).2.1

theorem integrable_greenGradient : Integrable greenGradient torusMeasure :=
  MemLp.integrable (by norm_num) (memLp_greenGradient 1 le_rfl (by norm_num))

end PeriodicAttractiveLogGas
