import DGPS.Examples.PolynomialSpeciesResidualBound
import DGPS.Examples.PolynomialResidualNormalization
import DGPS.Analysis.BoundedPerturbation

/-! Actual one-body and interacting lower bounds on the polynomial moving reference.
The one-body comparison here is the genuine bounded-potential comparison; it is
not the sharper small-field sixth-order comparison needed later in the optimizer proof. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
open DGPS.Circle.AngularNormalization

namespace DGPS.Examples.PolynomialSpecies
open DGPS.Examples.PolynomialEquilibrium DGPS.Examples.PolynomialExactGap

/-- An explicit upper bound for the oscillation of the actual moving-reference potential. -/
noncomputable def polynomialReferenceOscillation (h : ℝ) : ℝ :=
  2 * |h| + 2 * |root_EX054 h| * (1 + |h| / 3)

/-- A proved actual ordinary-reference lower rate, in physical units. -/
noncomputable def polynomialReferenceLowerRate (h : ℝ) : ℝ :=
  a0 * Real.exp (-polynomialReferenceOscillation h)

private theorem potential_abs_bound (h : ℝ) (x : Torus 1) :
    |polyPot_EX055 h (root_EX054 h) x| ≤ |h| + |root_EX054 h| * (1 + |h| / 3) := by
  unfold polyPot_EX055
  calc |-h * cosT 1 x + root_EX054 h * polyFeature h x| ≤
      |-h * cosT 1 x| + |root_EX054 h * polyFeature h x| := abs_add_le _ _
    _ ≤ |h| + |root_EX054 h| * (1 + |h| / 3) := by
      rw [abs_mul, abs_neg, abs_mul]
      have hc := mul_le_mul_of_nonneg_left (abs_cosT_le 1 x) (abs_nonneg h)
      have hp := mul_le_mul_of_nonneg_left (abs_polyFeature_le h x) (abs_nonneg (root_EX054 h))
      nlinarith

/-- The displayed lower rate is supplied by the exact moving Gibbs density. -/
theorem polynomial_reference_lsi_lower (h : ℝ) :
    ENNReal.ofReal (polynomialReferenceLowerRate h) ≤ ordinaryLSRate (polynomialRankOne h).ref := by
  apply boundedPerturbation_lsi (polynomialRankOne h).ref
    (polyPot_EX055 h (root_EX054 h))
    (ThreeSpeciesCircle.gibbsZ (polyPot_EX055 h (root_EX054 h)))
    (polynomialReferenceOscillation h)
  · exact Eventually.of_forall fun _ => rfl
  · intro x y
    have hx := potential_abs_bound h x
    have hy := potential_abs_bound h y
    have hxy := (le_abs_self (polyPot_EX055 h (root_EX054 h) x -
      polyPot_EX055 h (root_EX054 h) y)).trans (abs_sub _ _)
    dsimp only [polynomialReferenceOscillation]
    linarith

/-- The one-body input is positive and bounded above by the unperturbed physical rate. -/
theorem polynomial_reference_lower_rate_bounds (h : ℝ) :
    0 < polynomialReferenceLowerRate h ∧ polynomialReferenceLowerRate h ≤ a0 := by
  have hO : 0 ≤ polynomialReferenceOscillation h := by
    unfold polynomialReferenceOscillation
    positivity
  have he : Real.exp (-polynomialReferenceOscillation h) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  exact ⟨mul_pos a0_pos (Real.exp_pos _), by
    dsimp only [polynomialReferenceLowerRate]
    nlinarith [mul_le_mul_of_nonneg_left he a0_pos.le]⟩

/-- The actual residual and actual reference LSI give an all-family lower estimate.
The constants precede h, every absolute drift and every finite species family. -/
theorem polynomial_actual_residual_rate_bound :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h : ℝ, |h| ≤ δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h),
        ENNReal.ofReal (polynomialReferenceLowerRate h - eta * C ^ 2 * h ^ 2 / (4 * a0)) ≤
          speciesRate (canonical_elementary_polynomial_model h) b := by
  obtain ⟨C, δ, hC, hδ, hR⟩ := polynomial_physical_residual_bound
  refine ⟨C, δ, hC, hδ, fun h hh b => ?_⟩
  have hrate := polynomial_reference_lower_rate_bounds h
  by_cases hr : 0 ≤ polynomialReferenceLowerRate h - eta * (C * |h|) ^ 2 / (4 * a0)
  · have ht := polynomial_speciesRate_ge_of_residual_bound h b hrate.1.le
      (mul_pos (by norm_num : (0 : ℝ) < 4) a0_pos)
      (hrate.2.trans (by nlinarith [a0_pos]))
      (mul_nonneg hC.le (abs_nonneg h)) (polynomial_reference_lsi_lower h) (hR h hh) hr
    have he : eta * (C * |h|) ^ 2 / (4 * a0) = eta * C ^ 2 * h ^ 2 / (4 * a0) := by
      rw [mul_pow, sq_abs]
      ring
    simpa only [he] using ht
  · have he : eta * (C * |h|) ^ 2 / (4 * a0) = eta * C ^ 2 * h ^ 2 / (4 * a0) := by
      rw [mul_pow, sq_abs]
      ring
    rw [he] at hr
    rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hr)]
    exact bot_le

/-- A uniform positive lower rate for the actual polynomial model on a small field interval.
This coarse positivity statement does not claim the sharper second-order source asymptotic. -/
theorem polynomial_actual_speciesRate_positive :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| ≤ δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h),
        ENNReal.ofReal (a0 / 2) ≤ speciesRate (canonical_elementary_polynomial_model h) b := by
  obtain ⟨C, δR, hC, hδR, hrate⟩ := polynomial_actual_residual_rate_bound
  obtain ⟨C0, δ0, hC0, hδ0, hroot⟩ := abs_root_le_sixth_EX054
  let L := 2 + 3 * C0
  let κ := eta * C ^ 2 / (4 * a0)
  have hL : 0 < L := by dsimp [L]; positivity
  have hκ : 0 ≤ κ := by
    dsimp only [κ]
    exact div_nonneg (mul_nonneg eta_pos.le (sq_nonneg C))
      (mul_nonneg (by norm_num) a0_pos.le)
  have hden : 0 < 2 * (a0 * L + κ + 1) :=
    mul_pos (by norm_num) (add_pos_of_nonneg_of_pos
      (add_nonneg (mul_nonneg a0_pos.le hL.le) hκ) zero_lt_one)
  let δ := min δR (min δ0 (min 1 (a0 / (2 * (a0 * L + κ + 1)))))
  refine ⟨δ, lt_min hδR (lt_min hδ0 (lt_min one_pos (div_pos a0_pos hden))),
    fun h hh b => ?_⟩
  have hhR : |h| ≤ δR := hh.trans (min_le_left _ _)
  have hh0 : |h| ≤ δ0 := hh.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hh1 : |h| ≤ 1 := hh.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hsmall : |h| ≤ a0 / (2 * (a0 * L + κ + 1)) := hh.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have h6 : h ^ 6 ≤ |h| := by
    rw [← Even.pow_abs (by decide : Even (6 : ℕ)) h]
    exact pow_le_of_le_one (abs_nonneg h) hh1 (by norm_num)
  have hs : |root_EX054 h| ≤ C0 * |h| :=
    (hroot h hh0).trans (mul_le_mul_of_nonneg_left h6 hC0.le)
  have hprod : |root_EX054 h| * (1 + |h| / 3) ≤ C0 * |h| * (4 / 3) :=
    mul_le_mul hs (by linarith) (by positivity) (by positivity)
  have hO : polynomialReferenceOscillation h ≤ L * |h| := by
    dsimp only [polynomialReferenceOscillation, L]
    nlinarith [mul_nonneg hC0.le (abs_nonneg h)]
  have he : 1 - L * |h| ≤ Real.exp (-polynomialReferenceOscillation h) := by
    linarith [Real.add_one_le_exp (-polynomialReferenceOscillation h)]
  have ha : a0 * (1 - L * |h|) ≤ polynomialReferenceLowerRate h :=
    mul_le_mul_of_nonneg_left he a0_pos.le
  have hsq : h ^ 2 ≤ |h| := by
    rw [← sq_abs]
    nlinarith [mul_nonneg (abs_nonneg h) (sub_nonneg.mpr hh1)]
  have hloss : eta * C ^ 2 * h ^ 2 / (4 * a0) ≤ κ * |h| := by
    have heq : eta * C ^ 2 * h ^ 2 / (4 * a0) = κ * h ^ 2 := by dsimp only [κ]; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hsq hκ
  have hlin := (le_div_iff₀ hden).mp hsmall
  have hlow : a0 / 2 ≤ polynomialReferenceLowerRate h - eta * C ^ 2 * h ^ 2 / (4 * a0) := by
    nlinarith [abs_nonneg h]
  exact (ENNReal.ofReal_le_ofReal hlow).trans (hrate h hhR b)

end DGPS.Examples.PolynomialSpecies
