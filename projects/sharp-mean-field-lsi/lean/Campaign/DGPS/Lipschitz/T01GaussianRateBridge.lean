import DGPS.Lipschitz.T01CovarianceMatrix
import SharpSymmetricLSI.Paper.LamSym3

/-!
# Physical covariance forms in the positive spectral coordinates

These identities identify the actual operator covariance with the matrix used in the
legacy Gaussian quotient. They do not assume a scalar-rate upper bound.
-/

noncomputable section
open MeasureTheory Filter
open scoped RealInnerProductSpace

namespace DGPS.Lipschitz

open KernelApproximation

variable {d : ℕ}

/-- The bounded operator's quadratic form equals its nested spectral coefficient sum.
This identity does not commute the covariance and generator. -/
theorem t01_covariance_quadratic_coordinates (S : Spec d) (A : InteractionData d)
    (u : Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d))) :
    inner ℝ u (Ring.inverse (1 + DGPS.kernelOp A (specProbability_LIP016 S)) u) =
      ∑' i, inner ℝ ((spectralBasis_LIP016 S) i) u * ∑' j,
        inner ℝ ((spectralBasis_LIP016 S) i)
          (Ring.inverse (1 + DGPS.kernelOp A (specProbability_LIP016 S)) ((spectralBasis_LIP016 S) j)) *
            inner ℝ ((spectralBasis_LIP016 S) j) u := by
  let B := Ring.inverse (1 + DGPS.kernelOp A (specProbability_LIP016 S))
  have hrow : ∀ i, HasSum (fun j => inner ℝ ((spectralBasis_LIP016 S) i) (B ((spectralBasis_LIP016 S) j)) * inner ℝ ((spectralBasis_LIP016 S) j) u)
      (inner ℝ ((spectralBasis_LIP016 S) i) (B u)) := by
    intro i
    convert ((((spectralBasis_LIP016 S).hasSum_repr u).mapL B).mapL (innerSL ℝ ((spectralBasis_LIP016 S) i))) using 1
    · funext j
      simp only [map_smul, innerSL_apply_apply,
        HilbertBasis.repr_apply_apply, smul_eq_mul]
      ring
    · simp only [innerSL_apply_apply]
  calc inner ℝ u (B u) = ∑' i, inner ℝ u ((spectralBasis_LIP016 S) i) * inner ℝ ((spectralBasis_LIP016 S) i) (B u) :=
      ((spectralBasis_LIP016 S).tsum_inner_mul_inner u (B u)).symm
    _ = _ := by
      apply tsum_congr
      intro i
      rw [real_inner_comm u ((spectralBasis_LIP016 S) i), ← (hrow i).tsum_eq]

/-- Finite positive-coordinate covariance forms are the finite matrix forms exactly. -/
theorem t01_finite_covariance_quadratic (S : Spec d) (A : InteractionData d)
    (n : ℕ) (v : ℕ → ℝ) :
    inner ℝ (∑ i ∈ Finset.range n, v i • (spectralBasis_LIP016 S) (i + 1))
      (Ring.inverse (1 + DGPS.kernelOp A (specProbability_LIP016 S))
        (∑ j ∈ Finset.range n, v j • (spectralBasis_LIP016 S) (j + 1))) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        v i * t01CovarianceMatrix S A i j * v j := by
  rw [map_sum]
  simp only [map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    conj_trivial]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  unfold t01CovarianceMatrix
  ring

/-- Dropping the constant mode gives an actually centered L² vector. -/
theorem t01_finite_positive_modes_centered (S : Spec d) (aux : Aux S)
    (n : ℕ) (v : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, v i • (spectralBasis_LIP016 S) (i + 1)) ∈ centeredL2 (specProbability_LIP016 S) := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  have he0 : (spectralBasis_LIP016 S) 0 = oneL (specProbability_LIP016 S : Measure (Torus d)) := by
    apply Lp.ext
    filter_upwards [S.ae_mu (S.ve 0), oneL_ae (specProbability_LIP016 S : Measure (Torus d))] with x hx hy
    change S.v 0 x = (spectralBasis_LIP016 S) 0 x at hx
    rw [← hx, aux.v0, hy]
  rw [mem_centeredL2, ← inner_oneL, ← he0, inner_sum]
  simp only [inner_smul_right, (orthonormal_iff_ite.mp (spectralBasis_LIP016 S).orthonormal),
    Nat.zero_ne_add_one, ite_false, mul_zero, Finset.sum_const_zero]

/-- The finite positive-mode matrix form is the actual centered density covariance form. -/
theorem t01_finite_densityCovariance_quadratic (S : Spec d) (aux : Aux S)
    (A : InteractionData d) (hH : IsCoerciveDensityHessian A (specProbability_LIP016 S))
    (n : ℕ) (v : ℕ → ℝ) :
    ∃ f : centeredL2 (specProbability_LIP016 S),
      (f : Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d))) = ∑ i ∈ Finset.range n, v i • (spectralBasis_LIP016 S) (i + 1) ∧
      inner ℝ f (densityCovariance A (specProbability_LIP016 S) hH f) =
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          v i * t01CovarianceMatrix S A i j * v j := by
  let f : centeredL2 (specProbability_LIP016 S) :=
    ⟨∑ i ∈ Finset.range n, v i • (spectralBasis_LIP016 S) (i + 1), t01_finite_positive_modes_centered S aux n v⟩
  obtain ⟨σ, hσ, hbound⟩ := hH
  have hcov := kernelCovariance_centered_LIP016 A (specProbability_LIP016 S) hσ hbound f
  refine ⟨f, rfl, ?_⟩
  change inner ℝ (f : Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d)))
    (densityCovariance A (specProbability_LIP016 S) ⟨σ, hσ, hbound⟩ f : Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d))) = _
  rw [← hcov]
  exact t01_finite_covariance_quadratic S A n v

end DGPS.Lipschitz
