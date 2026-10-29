import DGPS.Examples.AttractiveXYFoldEX027
import DGPS.Examples.AttractiveXYFoldUpperEX028
import DGPS.Structural.SmallRateCircleEquality

/-!
# EX029: small-rate equality along the positive fold side

For the attractive XY model at `κ = 4`, `h = h_c + ε` with `0 < ε ≤ 1` (the fold parameter `h_c`
of EX027/EX028), this file proves that there is `ε₀ ∈ (0,1]` such that the multi-species rate equals
the scalar rate, `r_ms = r_*`, for all `0 < ε < ε₀` (the small-rate circle equality STR021 applied
with the explicit total oscillation `M = osc V + osc W = 2h + 8`).  Uniformly on `(0,1]` both the
nonlinear rates and their ratios to the equilibrium Gaussian rate are `Θ(ε²)`
(`DGPS.Examples.small_rate_equality_along_the_positive_fold_side`).

Routes: the lower bound comes from EX027, the upper bound and Gaussian comparability from EX028,
and the equality from STR021.  The only new analytic input is that `M` is positive and at most
`2 (h_c + 1) + 8` along the parameter interval, which makes the STR021 threshold bounded below.
-/

open MeasureTheory
open DGPS DGPS.Examples.AttractiveXY DGPS.Examples.AttractiveXYCritical
open DGPS.Circle.BesselMoments DGPS.Circle.BesselMonotonicity DGPS.Circle.BesselConcavity
open DGPS.Examples.AttractiveXYTilt DGPS.Examples.AttractiveXYCollapseEX026
open DGPS.Models
open scoped ENNReal NNReal

namespace DGPS.Examples.SmallRateEX029

/-- The point `x = 1/2` of the circle, at which `cos 2πx = -1`. -/
noncomputable def halfPt_EX029 : DGPS.Torus 1 := DGPS.torusLift (fun _ : Fin 1 => (1 / 2 : ℝ))

theorem xyMode_halfPt_EX029 : (xyMode halfPt_EX029).re = -1 := by
  unfold halfPt_EX029
  rw [xyMode_re_lift]
  show Real.cos (2 * Real.pi * (1 / 2 : ℝ)) = -1
  rw [show 2 * Real.pi * (1 / 2 : ℝ) = Real.pi by ring, Real.cos_pi]

/-- The total oscillation of the attractive XY interaction is strictly positive when `h > 0`. -/
theorem totalOscillation_pos_EX029 {κ h : ℝ} (hκ : 0 < κ) (hh : 0 < h) :
    0 < totalOscillation (attractiveXY κ h) := by
  have hV1 : (attractiveXY κ h).V halfPt_EX029 = h := by
    rw [attractiveXY_V, xyMode_halfPt_EX029]; ring
  have hV0 : (attractiveXY κ h).V 0 = -h := by
    rw [attractiveXY_V, xyMode_zero, Complex.one_re]; ring
  have hW1 : (attractiveXY κ h).W halfPt_EX029 0 = 2 * κ := by
    rw [attractiveXY_W, sub_zero, xyMode_halfPt_EX029]; ring
  have hW0 : (attractiveXY κ h).W 0 0 = 0 := (attractiveXY κ h).W_diag 0
  have hP : 2 * h ≤ potentialOscillation (attractiveXY κ h) := by
    have h1 := def025_V_le (attractiveXY κ h) halfPt_EX029
    have h2 := def025_le_V (attractiveXY κ h) 0
    rw [hV1] at h1
    rw [hV0] at h2
    unfold potentialOscillation
    linarith
  have hI : 2 * κ ≤ interactionOscillation (attractiveXY κ h) := by
    have h1 := def025_W_le (attractiveXY κ h) halfPt_EX029 0
    have h2 := def025_le_W (attractiveXY κ h) 0 0
    rw [hW1] at h1
    rw [hW0] at h2
    unfold interactionOscillation
    linarith
  unfold totalOscillation
  linarith

/-- On the fold parameter interval `0 < ε ≤ 1`, `0 < M ≤ 2 (h_c + 1) + 8` where
`M = totalOscillation (attractiveXY 4 (h_c + ε))`. -/
theorem totalOscillation_bounds_EX029 {hc ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hc0 : 0 < hc) :
    0 < totalOscillation (attractiveXY 4 (hc + ε)) ∧
      totalOscillation (attractiveXY 4 (hc + ε)) ≤ 2 * (hc + 1) + 8 := by
  refine ⟨totalOscillation_pos_EX029 (by norm_num) (by linarith), ?_⟩
  have h := attractiveXY_oscillation_EX026 (κ := 4) (h := hc + ε) (by norm_num) (by linarith)
  linarith

end DGPS.Examples.SmallRateEX029

namespace DGPS.Examples

open DGPS.Examples.SmallRateEX029

/-- **EX029 (small-rate equality along the positive fold side).** Let `s > 0` with `g'(s) = 1/4`
and `h_c = 4 g(s) - s`.  There are `ε₀ ∈ (0,1]` and constants `c, C, c', C' > 0`, independent of
`ε`, such that for every `0 < ε ≤ 1` at `κ = 4`, `h = h_c + ε`:
the positive root `t = 4 g(t) + h` exists; for every Lipschitz presentation of the attractive XY
data, `c a₀ ε² ≤ r_ms ≤ r_* ≤ C a₀ ε²` (with `r_ms ≤ r_*` in general); for `0 < ε < ε₀`,
`r_ms = r_*`; and at every positive root, the nonlinear rates satisfy
`c' ε² λ_G ≤ r_ms` and `r_* ≤ C' ε² λ_G`, where `λ_G` is the equilibrium Gaussian rate. -/
theorem small_rate_equality_along_the_positive_fold_side {s hc : ℝ} (hs : 0 < s)
    (hd : deriv besselRatio s = 1 / 4) (hhc : hc = 4 * besselRatio s - s) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ 1 ∧
    ∃ c C c' C' : ℝ, 0 < c ∧ 0 < C ∧ 0 < c' ∧ 0 < C' ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∃ t : ℝ, 0 < t ∧ t = 4 * besselRatio t + (hc + ε)) ∧
      (∀ hLip : LipschitzData (attractiveXY 4 (hc + ε)),
        ENNReal.ofReal (c * a0 * ε ^ 2) ≤
            speciesRate (attractiveXY 4 (hc + ε)) (lipschitz_absoluteDrift _ hLip) ∧
          scalarRate (attractiveXY 4 (hc + ε)) (lipschitz_absoluteDrift _ hLip) ≤
            ENNReal.ofReal (C * a0 * ε ^ 2) ∧
          (ε < ε0 → speciesRate (attractiveXY 4 (hc + ε)) (lipschitz_absoluteDrift _ hLip) =
            scalarRate (attractiveXY 4 (hc + ε)) (lipschitz_absoluteDrift _ hLip))) ∧
      (∀ t : ℝ, 0 < t → t = 4 * besselRatio t + (hc + ε) →
        ∀ hH : IsCoerciveDensityHessian (attractiveXY 4 (hc + ε)) (xyLaw_EX023 t),
          (∀ hLip : LipschitzData (attractiveXY 4 (hc + ε)),
            ENNReal.ofReal (c' * ε ^ 2) * gaussianRate (attractiveXY 4 (hc + ε)) (xyLaw_EX023 t) hH ≤
                speciesRate (attractiveXY 4 (hc + ε)) (lipschitz_absoluteDrift _ hLip) ∧
              scalarRate (attractiveXY 4 (hc + ε)) (lipschitz_absoluteDrift _ hLip) ≤
                ENNReal.ofReal (C' * ε ^ 2) * gaussianRate (attractiveXY 4 (hc + ε)) (xyLaw_EX023 t) hH)) := by
  obtain ⟨hc0, cG, CG, -, hcG, hCG, hall⟩ := fold_upper_bound_and_gaussian_comparability hs hd hhc
  obtain ⟨-, hEX⟩ := all_species_fold_lower_bound hs hd hhc
  -- the threshold `T` bounding `exp(-M) min(a0/9, 1/(4M))` from below, uniformly in `ε`
  have hT : 0 < Real.exp (-(2 * (hc + 1) + 8)) * min (a0 / 9) (1 / (4 * (2 * (hc + 1) + 8))) :=
    mul_pos (Real.exp_pos _) (lt_min (div_pos a0_pos (by norm_num))
      (one_div_pos.2 (by linarith)))
  set T := Real.exp (-(2 * (hc + 1) + 8)) * min (a0 / 9) (1 / (4 * (2 * (hc + 1) + 8))) with hTdef
  have hX : 0 < 4 * hc * s * T / a0 :=
    div_pos (mul_pos (mul_pos (mul_pos (by norm_num) hc0) hs) hT) a0_pos
  have hs4 : 0 < 4 * hc * s := mul_pos (mul_pos (by norm_num) hc0) hs
  -- explicit constants (names kept opaque, defining equations recorded)
  obtain ⟨cc, hcc⟩ : ∃ x : ℝ, x = Real.exp (-(2 * (hc + 5))) /
      (1 + 20 * (max 8 (max (16 / hc) ((2 + Real.sqrt 2) * (hc + 5) / hc))) ^ 2) := ⟨_, rfl⟩
  obtain ⟨CC, hCC⟩ : ∃ x : ℝ, x = 1 / (4 * hc * s) := ⟨_, rfl⟩
  have hccpos : 0 < cc := by
    rw [hcc]
    exact div_pos (Real.exp_pos _) (by positivity)
  have hCCpos : 0 < CC := by
    rw [hCC]
    exact one_div_pos.2 hs4
  have hc'pos : 0 < cc / CG := div_pos hccpos hCG
  have hC'pos : 0 < CC / cG := div_pos hCCpos hcG
  refine ⟨min 1 (Real.sqrt (4 * hc * s * T / a0)), lt_min one_pos (Real.sqrt_pos.2 hX),
    min_le_left _ _, cc, CC, cc / CG, CC / cG, hccpos, hCCpos, hc'pos, hC'pos, ?_⟩
  intro ε hε0 hε1
  obtain ⟨hex, -, -, -, hrate, hgaussAll⟩ := hall ε hε0 hε1
  obtain ⟨-, -, -, hlow⟩ := hEX ε hε0 hε1
  obtain ⟨hMpos, hMle⟩ := totalOscillation_bounds_EX029 hε0 hε1 hc0
  set M := totalOscillation (attractiveXY 4 (hc + ε)) with hMdef
  -- two-sided nonlinear bounds, uniform in the drift
  have hLowAll : ∀ b : AbsoluteDrift (attractiveXY 4 (hc + ε)),
      ENNReal.ofReal (cc * a0 * ε ^ 2) ≤ speciesRate (attractiveXY 4 (hc + ε)) b := by
    intro b
    have e : cc * a0 * ε ^ 2 = a0 * Real.exp (-(2 * (hc + 5))) * ε ^ 2 /
        (1 + 20 * (max 8 (max (16 / hc) ((2 + Real.sqrt 2) * (hc + 5) / hc))) ^ 2) := by
      rw [hcc]; ring
    rw [e]
    exact hlow b
  have hUpAll : ∀ b : AbsoluteDrift (attractiveXY 4 (hc + ε)),
      scalarRate (attractiveXY 4 (hc + ε)) b ≤ ENNReal.ofReal (CC * a0 * ε ^ 2) := by
    intro b
    have e : CC * a0 * ε ^ 2 = a0 * ε ^ 2 / (4 * hc * s) := by
      rw [hCC]; ring
    rw [e]
    exact hrate b
  -- the equality threshold
  have key : ∀ x y : ℝ, y ≠ 0 → x / y * ε ^ 2 * (y * a0) = x * a0 * ε ^ 2 := by
    intro x y hy
    have hxy : x / y * y = x := div_mul_cancel₀ x hy
    calc x / y * ε ^ 2 * (y * a0) = (x / y * y) * a0 * ε ^ 2 := by ring
      _ = x * a0 * ε ^ 2 := by rw [hxy]
  refine ⟨hex, fun hLip => ⟨hLowAll _, hUpAll _, fun hlt => ?_⟩, fun t ht heq hH => ?_⟩
  · -- equality for `ε < ε₀`
    have hεs : ε ≤ Real.sqrt (4 * hc * s * T / a0) :=
      (lt_of_lt_of_le hlt (min_le_right _ _)).le
    have hsq : ε ^ 2 ≤ 4 * hc * s * T / a0 := by
      have h1 : ε * ε ≤ Real.sqrt (4 * hc * s * T / a0) * Real.sqrt (4 * hc * s * T / a0) :=
        mul_le_mul hεs hεs hε0.le (Real.sqrt_nonneg _)
      rw [Real.mul_self_sqrt hX.le] at h1
      rw [sq]
      exact h1
    have hbound : a0 * ε ^ 2 / (4 * hc * s) ≤ T := by
      rw [div_le_iff₀ hs4]
      have h2 := (le_div_iff₀ a0_pos).1 hsq
      have h3 : a0 * ε ^ 2 = ε ^ 2 * a0 := mul_comm _ _
      have h4 : T * (4 * hc * s) = 4 * hc * s * T := mul_comm _ _
      linarith
    have hTle : T ≤ Real.exp (-M) * min (a0 / 9) (1 / (4 * M)) := by
      rw [hTdef]
      apply mul_le_mul
      · exact Real.exp_le_exp.2 (by linarith)
      · exact le_min (min_le_left _ _)
          ((min_le_right _ _).trans (one_div_le_one_div_of_le (by linarith) (by linarith)))
      · exact le_of_lt (lt_min (div_pos a0_pos (by norm_num)) (one_div_pos.2 (by linarith)))
      · exact (Real.exp_pos _).le
    have hsmall : scalarRate (attractiveXY 4 (hc + ε)) (lipschitz_absoluteDrift _ hLip) ≤
        ENNReal.ofReal (Real.exp (-M) * min (a0 / 9) (1 / (4 * M))) :=
      (hrate (lipschitz_absoluteDrift _ hLip)).trans (ENNReal.ofReal_le_ofReal (hbound.trans hTle))
    have hpos0 : 0 < a0 * Real.exp (-(2 * (hc + 5))) * ε ^ 2 /
        (1 + 20 * (max 8 (max (16 / hc) ((2 + Real.sqrt 2) * (hc + 5) / hc))) ^ 2) :=
      div_pos (mul_pos (mul_pos a0_pos (Real.exp_pos _)) (pow_pos hε0 2)) (by positivity)
    have hpos : 0 < scalarRate (attractiveXY 4 (hc + ε)) (lipschitz_absoluteDrift _ hLip) :=
      lt_of_lt_of_le (ENNReal.ofReal_pos.2 hpos0)
        (le_trans (hlow (lipschitz_absoluteDrift _ hLip))
          (speciesRate_le_scalarRate _ (lipschitz_absoluteDrift _ hLip)))
    exact DGPS.Structural.speciesRate_eq_scalarRate_of_small_circle_rate
      (attractiveXY 4 (hc + ε)) hLip hMpos hpos hsmall
  · -- Gaussian ratios, at every positive root and coercive Hessian witness
    have hG := (hgaussAll t ht heq).2 hH
    intro hLip
    have hcnn : 0 ≤ cc / CG * ε ^ 2 := mul_nonneg hc'pos.le (sq_nonneg ε)
    have hCnn : 0 ≤ CC / cG * ε ^ 2 := mul_nonneg hC'pos.le (sq_nonneg ε)
    constructor
    · calc ENNReal.ofReal (cc / CG * ε ^ 2) * gaussianRate (attractiveXY 4 (hc + ε)) (xyLaw_EX023 t) hH
          ≤ ENNReal.ofReal (cc / CG * ε ^ 2) * ENNReal.ofReal (CG * a0) :=
            mul_le_mul_of_nonneg_left hG.2 zero_le
        _ = ENNReal.ofReal (cc / CG * ε ^ 2 * (CG * a0)) := (ENNReal.ofReal_mul hcnn).symm
        _ = ENNReal.ofReal (cc * a0 * ε ^ 2) := by rw [key cc CG hCG.ne']
        _ ≤ speciesRate (attractiveXY 4 (hc + ε)) (lipschitz_absoluteDrift _ hLip) :=
            hLowAll _
    · calc scalarRate (attractiveXY 4 (hc + ε)) (lipschitz_absoluteDrift _ hLip)
          ≤ ENNReal.ofReal (CC * a0 * ε ^ 2) := hUpAll _
        _ = ENNReal.ofReal (CC / cG * ε ^ 2 * (cG * a0)) := by rw [key CC cG hcG.ne']
        _ = ENNReal.ofReal (CC / cG * ε ^ 2) * ENNReal.ofReal (cG * a0) :=
            ENNReal.ofReal_mul hCnn
        _ ≤ ENNReal.ofReal (CC / cG * ε ^ 2) * gaussianRate (attractiveXY 4 (hc + ε)) (xyLaw_EX023 t) hH :=
            mul_le_mul_of_nonneg_left hG.1 zero_le

end DGPS.Examples
