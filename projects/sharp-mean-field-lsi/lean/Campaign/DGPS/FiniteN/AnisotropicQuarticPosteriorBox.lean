import DGPS.FiniteN.AnisotropicQuarticHubbard

/-! A true uniformly positive posterior noise event. The estimate is conditioned
on the particle configuration and therefore never subtracts an unconditional
Gaussian tail from an exponentially small rare mass. -/

open MeasureTheory ProbabilityTheory Matrix
open DGPS.Models DGPS.FiniteN.Tools.GaussianCoupling
open scoped ENNReal NNReal

namespace DGPS.FiniteN

/-- One fixed standard-Gaussian cube has positive probability. Its image lies in
every posterior box wider than a fixed multiple of `N^(-1/2)`, uniformly in the
posterior center. No posterior probability bound is assumed. -/
theorem quartic_posterior_box_probability :
    ∃ L : ℝ, 0 < L ∧ ∃ p : ℝ≥0∞, 0 < p ∧ p ≤ 1 ∧
      ∀ N : ℕ+, ∀ z : Fin 2 → ℝ, ∀ rx ry : ℝ,
        (Real.sqrt (N : ℝ))⁻¹ * L ≤ rx →
        (Real.sqrt (N : ℝ))⁻¹ * L ≤ ry →
        p ≤ gaussLaw quarticHubbardD N z
          {w | |w 0 - z 0| ≤ rx ∧ |w 1 - z 1| ≤ ry} := by
  classical
  let R := sqrtD quarticHubbardD
  let L := (∑ i : Fin 2, ∑ j : Fin 2, |R i j|) + 1
  let Q : Set (Fin 2 → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1)
  let p := (stdGaussianPi 2) Q
  have hL : 0 < L := by
    dsimp only [L]
    positivity
  have hg : 0 < gaussianReal 0 1 (Set.Icc (-1 : ℝ) 1) := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have hv := (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : ℝ≥0) ≠ 0)) hz
    norm_num [Real.volume_Icc] at hv
  have hp : 0 < p := by
    dsimp only [p, Q, stdGaussianPi]
    rw [Measure.pi_pi, Fin.prod_univ_two]
    exact ENNReal.mul_pos hg.ne' hg.ne'
  have hp1 : p ≤ 1 := prob_le_one (μ := stdGaussianPi 2) (s := Q)
  refine ⟨L, hL, p, hp, hp1, fun N z rx ry hx hy => ?_⟩
  let E : Set (Fin 2 → ℝ) := {w | |w 0 - z 0| ≤ rx ∧ |w 1 - z 1| ≤ ry}
  have hEm : MeasurableSet E := by
    exact (isClosed_le (show Continuous (fun w : Fin 2 → ℝ => |w 0 - z 0|) by fun_prop)
      (continuous_const (y := rx))).measurableSet.inter
      (isClosed_le (show Continuous (fun w : Fin 2 → ℝ => |w 1 - z 1|) by fun_prop)
        (continuous_const (y := ry))).measurableSet
  have hrow : ∀ i : Fin 2, ∑ j : Fin 2, |R i j| ≤ L := by
    intro i
    have h : (∑ j : Fin 2, |R i j|) ≤ ∑ k : Fin 2, ∑ j : Fin 2, |R k j| :=
      Finset.single_le_sum (s := Finset.univ) (f := fun k : Fin 2 => ∑ j : Fin 2, |R k j|)
        (fun k _ => Finset.sum_nonneg fun j _ => abs_nonneg (R k j)) (Finset.mem_univ i)
    dsimp only [L]
    linarith only [h]
  have hnoise : ∀ ξ ∈ Q, ∀ i : Fin 2,
      |affineMap quarticHubbardD N z ξ i - z i| ≤ (Real.sqrt (N : ℝ))⁻¹ * L := by
    intro ξ hξ i
    have hξb : ∀ j : Fin 2, |ξ j| ≤ 1 := fun j =>
      abs_le.mpr (hξ j (Set.mem_univ j))
    have hsum : |∑ j : Fin 2, R i j * ξ j| ≤ L := by
      calc
        _ ≤ ∑ j : Fin 2, |R i j * ξ j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin 2, |R i j| := Finset.sum_le_sum fun j _ => by
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hξb j)
        _ ≤ L := hrow i
    change |(z i + (Real.sqrt (N : ℝ))⁻¹ * (∑ j, R i j * ξ j)) - z i| ≤ _
    rw [add_sub_cancel_left, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt (N : ℝ))⁻¹)]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have hsub : Q ⊆ affineMap quarticHubbardD N z ⁻¹' E := by
    intro ξ hξ
    exact ⟨(hnoise ξ hξ 0).trans hx, (hnoise ξ hξ 1).trans hy⟩
  rw [← map_stdGaussian_affine quartic_hubbard_D_posDef N z,
    Measure.map_apply (measurable_affineMap quarticHubbardD N z) hEm]
  exact measure_mono hsub

end DGPS.FiniteN
