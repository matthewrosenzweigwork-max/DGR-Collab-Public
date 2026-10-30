import DGPS.Frontier.FIN068.Close

/-! Actual Gaussian control in the stable direction on the rare transverse strip.
The negative quartic transverse term is retained; no positive Hessian is inferred
at the degenerate remote saddle. -/

open DGPS.Models DGPS.Frontier.FIN068 DGPS.FiniteN.QuarticSaddleGlobalFIN066

namespace DGPS.FiniteN

/-- After shrinking a fixed neighborhood, the actual potential has a positive
longitudinal quadratic lower bound minus a transverse quartic error. This is the
Gaussian strip and longitudinal-shell input for FIN071 and FIN074. -/
theorem quartic_stable_direction_lower :
    ∃ δ c K : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < c ∧ 0 < K ∧ ∀ u y : ℝ,
      |u| ≤ δ → y ^ 2 ≤ δ →
      c * u ^ 2 - K * y ^ 4 ≤
        quarticPsi_FIN066 !₂[-4 + u, y] - quarticPsi_FIN066 !₂[-4, 0] := by
  obtain ⟨d, M, hd, hd1, hM, hTaylor⟩ := weighted_expansion_FIN068CLOSE
  have hA := exact_negative_reduced_quartic_coefficient.1.2.1
  have hD := exact_negative_reduced_quartic_coefficient.1.2.2.1
  let A := quarticA_FIN06803
  let D := quarticD_FIN06803
  let δ := min d (A / (64 * (M + 1)))
  let L := D ^ 2 / (512 * A)
  have hδ : 0 < δ := lt_min hd (div_pos hA (by positivity))
  have hδd : δ ≤ d := min_le_left _ _
  have hδA : δ ≤ A / (64 * (M + 1)) := min_le_right _ _
  have hL : 0 ≤ L := by dsimp [L, A]; positivity
  have hLA : (512 * A) * L = D ^ 2 := by
    dsimp only [L]
    field_simp [show A ≠ 0 from hA.ne']
  refine ⟨δ, A / 4, L + A / 8 + 1, hδ, hδd.trans hd1.le,
    div_pos hA (by norm_num), by positivity, fun u y hu hy => ?_⟩
  have hcubic : (|u| + y ^ 2) ^ 3 ≤ 4 * δ * (u ^ 2 + y ^ 4) := by
    have hm := mul_nonneg (show 0 ≤ |u| + y ^ 2 by positivity) (sq_nonneg (|u| - y ^ 2))
    have hu3 := mul_le_mul_of_nonneg_right hu (sq_nonneg |u|)
    have hy3 := mul_le_mul_of_nonneg_right hy (by positivity : 0 ≤ (y ^ 2) ^ 2)
    rw [sq_abs] at hu3
    have hfirst : (|u| + y ^ 2) ^ 3 ≤ 4 * (|u| ^ 3 + (y ^ 2) ^ 3) := by
      nlinarith only [hm]
    have huabs : |u| ^ 3 = |u| * u ^ 2 := by
      rw [pow_succ, sq_abs]
      ring
    rw [huabs] at hfirst
    nlinarith only [hfirst, hu3, hy3]
  have hcoef : 4 * M * δ ≤ A / 8 := by
    have hm := (le_div_iff₀ (by positivity : 0 < 64 * (M + 1))).mp hδA
    nlinarith only [hm, hδ.le, mul_nonneg hM hδ.le]
  have hrem := (hTaylor u y (hu.trans hδd) (hy.trans hδd)).trans
    (mul_le_mul_of_nonneg_left hcubic hM)
  have hrem' :
      |quarticPsi_FIN066 !₂[-4 + u, y] - quarticPsi_FIN066 !₂[-4, 0] -
        (A * u ^ 2 / 2 - D * u * y ^ 2 / 32 + D * y ^ 4 / 512)| ≤
        A / 8 * (u ^ 2 + y ^ 4) := by
    have hc := mul_le_mul_of_nonneg_right hcoef
      (by positivity : 0 ≤ u ^ 2 + y ^ 4)
    dsimp only [A, D] at *
    nlinarith only [hrem, hc]
  have hcross : -(A / 8 * u ^ 2 + L * y ^ 4) ≤ -(D * u * y ^ 2 / 32) := by
    apply le_of_mul_le_mul_left (a := 512 * A) _ (by positivity)
    have he := congrArg (fun z : ℝ => z * y ^ 4) hLA
    nlinarith only [sq_nonneg (8 * A * u - D * y ^ 2), he]
  have hpos : 0 ≤ D * y ^ 4 / 512 := by dsimp [D]; positivity
  have hlo := (abs_le.mp hrem').1
  nlinarith only [hlo, hcross, hpos, show 0 ≤ y ^ 4 by positivity]

end DGPS.FiniteN
