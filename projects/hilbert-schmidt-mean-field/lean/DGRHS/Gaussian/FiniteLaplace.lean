import DGRHS.Gaussian.Imported.GaussianSquareMGF
import Mathlib.MeasureTheory.Integral.Pi

/-!
Finite Gaussian quadratic integrals used in the finite truncations of manuscript
lines 1932–1936 and 3673–3695. These statements neither identify a kernel operator
nor assert an infinite determinant identity. The analytic scalar brick is imported
from Apache-2.0 StatLean (see Imported/LICENSE and source provenance).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace DGRHS.Gaussian

/-- The repulsive one-coordinate factor, including the zero-parameter cases. -/
theorem integral_exp_neg_square {β a : ℝ} (hβ : 0 ≤ β) (ha : 0 ≤ a) :
    (∫ x : ℝ, Real.exp (-(β * a / 2) * x ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 + β * a))⁻¹ := by
  have hm : 0 ≤ β * a := mul_nonneg hβ ha
  have hlt : -(β * a / 2) < 1 / 2 := by linarith
  have h := StatLean.MultipleTesting.mgf_exp_sq_stdGaussian hlt
  have heq : 1 - 2 * (-(β * a / 2)) = 1 + β * a := by ring
  simpa only [heq] using h

theorem integrable_exp_neg_square {β a : ℝ} (hβ : 0 ≤ β) (ha : 0 ≤ a) :
    Integrable (fun x : ℝ => Real.exp (-(β * a / 2) * x ^ 2)) (gaussianReal 0 1) := by
  apply StatLean.MultipleTesting.integrable_exp_sq_stdGaussian
  have hm : 0 ≤ β * a := mul_nonneg hβ ha
  linarith

/-- The attractive factor requires the strict Gaussian convergence margin. -/
theorem integral_exp_pos_square {β a : ℝ} (hmargin : β * a < 1) :
    (∫ x : ℝ, Real.exp ((β * a / 2) * x ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 - β * a))⁻¹ := by
  have hlt : β * a / 2 < 1 / 2 := by linarith
  have h := StatLean.MultipleTesting.mgf_exp_sq_stdGaussian hlt
  have heq : 1 - 2 * (β * a / 2) = 1 - β * a := by ring
  simpa only [heq] using h

theorem integrable_exp_pos_square {β a : ℝ} (hmargin : β * a < 1) :
    Integrable (fun x : ℝ => Real.exp ((β * a / 2) * x ^ 2)) (gaussianReal 0 1) := by
  apply StatLean.MultipleTesting.integrable_exp_sq_stdGaussian
  linarith

noncomputable def finiteStandardGaussian (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => gaussianReal 0 1)

instance {ι : Type*} [Fintype ι] : IsProbabilityMeasure (finiteStandardGaussian ι) := by
  unfold finiteStandardGaussian
  infer_instance

/-- Genuine finite independent standard-normal product law, with integrability
proved separately below to exclude totalized-integral interpretations. -/
theorem integral_exp_neg_quadratic {ι : Type*} [Fintype ι]
    (β : ℝ) (a : ι → ℝ) (hβ : 0 ≤ β) (ha : ∀ i, 0 ≤ a i) :
    (∫ z : ι → ℝ, Real.exp (∑ i, -(β * a i / 2) * (z i) ^ 2)
      ∂finiteStandardGaussian ι) = ∏ i, (Real.sqrt (1 + β * a i))⁻¹ := by
  classical
  simp_rw [Real.exp_sum]
  rw [finiteStandardGaussian, integral_fintype_prod_eq_prod
    (fun i (x : ℝ) => Real.exp (-(β * a i / 2) * x ^ 2))]
  exact Finset.prod_congr rfl (fun i _ => integral_exp_neg_square hβ (ha i))

theorem integrable_exp_neg_quadratic {ι : Type*} [Fintype ι]
    (β : ℝ) (a : ι → ℝ) (hβ : 0 ≤ β) (ha : ∀ i, 0 ≤ a i) :
    Integrable (fun z : ι → ℝ => Real.exp (∑ i, -(β * a i / 2) * (z i) ^ 2))
      (finiteStandardGaussian ι) := by
  classical
  simp_rw [Real.exp_sum]
  exact Integrable.fintype_prod (fun i => integrable_exp_neg_square hβ (ha i))

theorem integral_exp_pos_quadratic {ι : Type*} [Fintype ι]
    (β : ℝ) (a : ι → ℝ) (hmargin : ∀ i, β * a i < 1) :
    (∫ z : ι → ℝ, Real.exp (∑ i, (β * a i / 2) * (z i) ^ 2)
      ∂finiteStandardGaussian ι) = ∏ i, (Real.sqrt (1 - β * a i))⁻¹ := by
  classical
  simp_rw [Real.exp_sum]
  rw [finiteStandardGaussian, integral_fintype_prod_eq_prod
    (fun i (x : ℝ) => Real.exp ((β * a i / 2) * x ^ 2))]
  exact Finset.prod_congr rfl (fun i _ => integral_exp_pos_square (hmargin i))

theorem integrable_exp_pos_quadratic {ι : Type*} [Fintype ι]
    (β : ℝ) (a : ι → ℝ) (hmargin : ∀ i, β * a i < 1) :
    Integrable (fun z : ι → ℝ => Real.exp (∑ i, (β * a i / 2) * (z i) ^ 2))
      (finiteStandardGaussian ι) := by
  classical
  simp_rw [Real.exp_sum]
  exact Integrable.fintype_prod (fun i => integrable_exp_pos_square (hmargin i))

/-- The finite regularized-determinant factor: centering adds exactly
`exp(β aᵢ/2)`, with the repulsive square-root denominator. -/
theorem integral_exp_centered_neg_quadratic {ι : Type*} [Fintype ι]
    (β : ℝ) (a : ι → ℝ) (hβ : 0 ≤ β) (ha : ∀ i, 0 ≤ a i) :
    (∫ z : ι → ℝ, Real.exp (∑ i, (β * a i / 2) * (1 - (z i) ^ 2))
      ∂finiteStandardGaussian ι) =
      ∏ i, Real.exp (β * a i / 2) * (Real.sqrt (1 + β * a i))⁻¹ := by
  classical
  have hpoint : ∀ z : ι → ℝ,
      Real.exp (∑ i, (β * a i / 2) * (1 - (z i) ^ 2)) =
      Real.exp (∑ i, β * a i / 2) *
        Real.exp (∑ i, -(β * a i / 2) * (z i) ^ 2) := by
    intro z
    rw [← Real.exp_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)
  simp_rw [hpoint]
  rw [integral_const_mul, integral_exp_neg_quadratic β a hβ ha,
    Finset.prod_mul_distrib, ← Real.exp_sum]

theorem integrable_exp_centered_neg_quadratic {ι : Type*} [Fintype ι]
    (β : ℝ) (a : ι → ℝ) (hβ : 0 ≤ β) (ha : ∀ i, 0 ≤ a i) :
    Integrable (fun z : ι → ℝ => Real.exp (∑ i, (β * a i / 2) * (1 - (z i) ^ 2)))
      (finiteStandardGaussian ι) := by
  classical
  have hpoint : (fun z : ι → ℝ => Real.exp (∑ i, (β * a i / 2) * (1 - (z i) ^ 2))) =
      fun z => Real.exp (∑ i, β * a i / 2) *
        Real.exp (∑ i, -(β * a i / 2) * (z i) ^ 2) := by
    funext z
    rw [← Real.exp_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hpoint]
  exact (integrable_exp_neg_quadratic β a hβ ha).const_mul _

end DGRHS.Gaussian

#print axioms DGRHS.Gaussian.integral_exp_neg_square
#print axioms DGRHS.Gaussian.integrable_exp_neg_square
#print axioms DGRHS.Gaussian.integral_exp_pos_square
#print axioms DGRHS.Gaussian.integrable_exp_pos_square
#print axioms DGRHS.Gaussian.integral_exp_neg_quadratic
#print axioms DGRHS.Gaussian.integrable_exp_neg_quadratic
#print axioms DGRHS.Gaussian.integral_exp_pos_quadratic
#print axioms DGRHS.Gaussian.integrable_exp_pos_quadratic

#print axioms DGRHS.Gaussian.integral_exp_centered_neg_quadratic
#print axioms DGRHS.Gaussian.integrable_exp_centered_neg_quadratic

#check DGRHS.Gaussian.integral_exp_neg_square
#check DGRHS.Gaussian.integrable_exp_neg_square
#check DGRHS.Gaussian.integral_exp_pos_square
#check DGRHS.Gaussian.integrable_exp_pos_square
#check DGRHS.Gaussian.finiteStandardGaussian
#check DGRHS.Gaussian.integral_exp_neg_quadratic
#check DGRHS.Gaussian.integrable_exp_neg_quadratic
#check DGRHS.Gaussian.integral_exp_pos_quadratic
#check DGRHS.Gaussian.integrable_exp_pos_quadratic
#check DGRHS.Gaussian.integral_exp_centered_neg_quadratic
#check DGRHS.Gaussian.integrable_exp_centered_neg_quadratic
