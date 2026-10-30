import DGPS.Lipschitz.T01FiniteRankBridge
import DGPS.Lipschitz.GaussianKernelTilt
import FullLabeledLSI.Paper.Hybrid63Defs

/-!
# Finite-rank positivity from the actual direct-Lipschitz Hessian

The positive-mode coefficients inherit coercivity from the genuine density Hessian. The
constant coordinate is set to zero before passing to the shifted legacy matrix convention.
-/

open MeasureTheory

namespace DGPS.Lipschitz

open KernelApproximation

variable {d : ℕ}

theorem positiveKernelCoefficient_coercive (J : InteractionData d) (S : Spec d) (D : KData d)
    (hD : D.K = centeredKernel J S.mu) {σ t : ℝ}
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ inner ℝ g (DGPS.densityHessian J (specProbability_LIP016 S) g))
    (ht : 0 ≤ t) (m : ℕ) (v : ℕ → ℝ) :
    min 1 σ * (∑ i ∈ Finset.range m, v i ^ 2) ≤
      (∑ i ∈ Finset.range m, v i ^ 2) +
        ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
          positiveKernelCoefficient S D t m i j * v i * v j := by
  have hD' : ∀ x y, D.K x y = centeredKernel J (specProbability_LIP016 S) x y :=
    fun x y => congrFun (congrFun hD x) y
  have hK := original_kernel_symmetric_LIP016 S D J hD'
  have hc := original_kernel_centered_LIP016 S D J hD'
  have hH' := original_hessian_transport_LIP016 S D hK hc J hD' hH
  let z : ℕ → ℝ := fun n => match n with
    | 0 => 0
    | n + 1 => v n
  have hnorm : (∑ i ∈ Finset.range (m + 1), z i ^ 2) =
      ∑ i ∈ Finset.range m, v i ^ 2 := by
    rw [Finset.sum_range_succ']
    simp only [z, zero_pow (by norm_num : 2 ≠ 0), zero_add, add_zero]
  have hquad : (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
      kernelCoefficient_LIP016 S D t m i j * z i * z j) =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
        positiveKernelCoefficient S D t m i j * v i * v j := by
    rw [Finset.sum_range_succ']
    simp only [z, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_range_succ']
    simp only [z, mul_zero, zero_add, add_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    rw [kernelCoefficient_LIP016, if_pos ⟨by omega, by omega⟩,
      positiveKernelCoefficient, if_pos ⟨hi', hj'⟩]
  have h := kernelCoefficient_coercive_from_hessian_LIP016 S D hK hc hH' ht m z
  rwa [hnorm, hquad] at h

theorem finiteRank_posIPlus_of_hessian (J : InteractionData d) (S : Spec d) (D : KData d)
    (hD : D.K = centeredKernel J S.mu)
    (F : SharpLSI.FL.FiniteRankApprox J.W S.mu S.v) (R : ℕ) {σ t : ℝ} (m : ℕ)
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ inner ℝ g (DGPS.densityHessian J (specProbability_LIP016 S) g))
    (ht : 0 ≤ t) (hs : F.s R = Finset.range m)
    (ha : ∀ i j, F.a R i j = positiveKernelCoefficient S D t m i j) :
    SharpLSI.FL.PosIPlus F R (2 * min 1 σ) := by
  intro v _
  rw [hs]
  simp only [ha]
  have hdiag : ∀ i ∈ Finset.range m,
      (∑ j ∈ Finset.range m, v i * (if i = j then 1 else 0) * v j) = v i ^ 2 := by
    intro i hi
    rw [Finset.sum_eq_single_of_mem i hi]
    · simp
      ring
    · intro j _ hji
      rw [if_neg (Ne.symm hji)]
      ring
  have hrow : ∀ i ∈ Finset.range m,
      (∑ j ∈ Finset.range m, v i *
        ((if i = j then 1 else 0) + positiveKernelCoefficient S D t m i j) * v j) =
        v i ^ 2 + ∑ j ∈ Finset.range m,
          positiveKernelCoefficient S D t m i j * v i * v j := by
    intro i hi
    calc
      _ = ∑ j ∈ Finset.range m, (v i * (if i = j then 1 else 0) * v j +
          positiveKernelCoefficient S D t m i j * v i * v j) :=
        Finset.sum_congr rfl fun j _ => by ring
      _ = _ := by rw [Finset.sum_add_distrib, hdiag i hi]
  rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib]
  convert positiveKernelCoefficient_coercive J S D hD hH ht m v using 1 <;> ring

end DGPS.Lipschitz
