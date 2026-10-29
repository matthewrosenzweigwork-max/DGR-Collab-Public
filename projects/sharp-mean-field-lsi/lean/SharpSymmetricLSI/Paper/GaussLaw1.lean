import SharpSymmetricLSI.Paper.ULimit6
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# R27 groundwork: Gaussian integrals of exponentials of quadratic forms

`∫ exp(a x - b x²/2) dN(0,1) = (1+b)^{-1/2} exp(a²/(2(1+b)))` for `1 + b > 0`, and its
multivariate version under the standard Gaussian of `ℝⁿ`, obtained by diagonalizing the symmetric
matrix in an orthonormal eigenbasis (the standard Gaussian does not depend on the basis).
-/

open MeasureTheory ProbabilityTheory Real
open scoped InnerProductSpace NNReal

namespace SharpLSI

/-- The Gaussian density identity behind the tilted variance `(1+b)⁻¹`. -/
theorem gaussianPDFReal_mul_exp {b : ℝ} (hb : 0 < 1 + b) (x : ℝ) :
    gaussianPDFReal 0 1 x * rexp (-(b * x ^ 2 / 2)) =
      (√(1 + b))⁻¹ * gaussianPDFReal 0 ((1 + b)⁻¹).toNNReal x := by
  have hv : (((1 + b)⁻¹).toNNReal : ℝ) = (1 + b)⁻¹ := Real.coe_toNNReal _ (inv_nonneg.2 hb.le)
  simp only [gaussianPDFReal, hv, NNReal.coe_one, sub_zero, mul_one]
  have hs : √(2 * π * (1 + b)⁻¹) = √(2 * π) * (√(1 + b))⁻¹ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_inv]
  have h1 : 0 < √(1 + b) := Real.sqrt_pos.2 hb
  have h2 : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  have he : rexp (-x ^ 2 / 2) * rexp (-(b * x ^ 2 / 2)) = rexp (-x ^ 2 / (2 * (1 + b)⁻¹)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [hs, mul_inv, inv_inv, mul_assoc, he]
  field_simp

/-- **The one-dimensional Gaussian integral.** -/
theorem integral_exp_quad_gaussian {a b : ℝ} (hb : 0 < 1 + b) :
    ∫ x, rexp (a * x - b * x ^ 2 / 2) ∂(gaussianReal 0 1) =
      (√(1 + b))⁻¹ * rexp ((1 + b)⁻¹ * a ^ 2 / 2) := by
  have hv : ((1 + b)⁻¹).toNNReal ≠ 0 := by
    simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; exact inv_pos.2 hb
  have hv' : (((1 + b)⁻¹).toNNReal : ℝ) = (1 + b)⁻¹ := Real.coe_toNNReal _ (inv_nonneg.2 hb.le)
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have h : ∀ x, gaussianPDFReal 0 1 x • rexp (a * x - b * x ^ 2 / 2) =
      (√(1 + b))⁻¹ * (gaussianPDFReal 0 ((1 + b)⁻¹).toNNReal x • rexp (a * x)) := by
    intro x
    rw [smul_eq_mul, smul_eq_mul, sub_eq_add_neg, Real.exp_add, ← mul_assoc,
      mul_comm (gaussianPDFReal 0 1 x), mul_assoc, gaussianPDFReal_mul_exp hb]
    ring
  simp_rw [h]
  rw [integral_const_mul, ← integral_gaussianReal_eq_integral_smul hv]
  have hm := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := ((1 + b)⁻¹).toNNReal)) a
  simp only [mgf, zero_mul, zero_add, hv'] at hm
  rw [hm]

theorem integrable_exp_quad_gaussian {a b : ℝ} (hb : 0 < 1 + b) :
    Integrable (fun x => rexp (a * x - b * x ^ 2 / 2)) (gaussianReal 0 1) := by
  by_contra h
  have := integral_exp_quad_gaussian (a := a) hb
  rw [integral_undef h] at this
  have : 0 < (√(1 + b))⁻¹ * rexp ((1 + b)⁻¹ * a ^ 2 / 2) :=
    mul_pos (inv_pos.2 (Real.sqrt_pos.2 hb)) (Real.exp_pos _)
  linarith

/-! ### The symmetric operator of a finite section -/

variable {n : ℕ}

/-- `y ↦ (∑_j A_{ij} y_j)_{i<n}` on `ℝⁿ`. -/
def secOp (A : ℕ → ℕ → ℝ) (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun y := WithLp.toLp 2 fun i : Fin n => ∑ j : Fin n, A i j * y j
  map_add' x y := by
    ext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    ext i; simp [Finset.mul_sum, mul_left_comm]

theorem secOp_apply (A : ℕ → ℕ → ℝ) (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    secOp A n y i = ∑ j : Fin n, A i j * y j := rfl

theorem inner_euclid (x y : EuclideanSpace ℝ (Fin n)) : ⟪x, y⟫_ℝ = ∑ i, x i * y i := by
  simp [PiLp.inner_apply, mul_comm]

theorem secOp_isSymmetric {A : ℕ → ℕ → ℝ} (hA : ∀ i j, A i j = A j i) :
    (secOp A n).IsSymmetric := by
  intro x y
  simp only [inner_euclid, secOp_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hA]; ring

theorem inner_secOp_self (A : ℕ → ℕ → ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    ⟪y, secOp A n y⟫_ℝ = ∑ i : Fin n, ∑ j : Fin n, A i j * (y i * y j) := by
  simp only [inner_euclid, secOp_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem trace_secOp (A : ℕ → ℕ → ℝ) :
    LinearMap.trace ℝ _ (secOp A n) = ∑ i : Fin n, A i i := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin n) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [inner_euclid, secOp_apply, EuclideanSpace.basisFun_apply]

end SharpLSI
