import DGPS.Examples.PolynomialSpeciesOriginData

/-! The explicit solution of the actual origin quadratic forcing. Its amplitude
is a SECOND derivative, rather than the coefficient of the squared path parameter. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

def polynomialOriginSineSecond : PeriodicC2_STR02969 :=
  PeriodicC2_STR02969.mk (fun t => Real.sin (2 * t)) (sinFreq_isC2_STR02962 2)

private theorem sine_val (t : ℝ) : polynomialOriginSineSecond.val t = Real.sin (2 * t) := rfl

private theorem sine_second (t : ℝ) :
    deriv (deriv polynomialOriginSineSecond.val) t = -4 * polynomialOriginSineSecond.val t := by
  have h1 : deriv polynomialOriginSineSecond.val = fun y => 2 * Real.cos (2 * y) := by
    funext y
    change deriv (fun x : ℝ => Real.sin (2 * x)) y = _
    convert (((hasDerivAt_id y).const_mul 2).sin).deriv using 1 <;> dsimp only [id_eq] <;> ring
  rw [h1, sine_val]
  have h2 := (((hasDerivAt_id t).const_mul 2).cos).const_mul 2
  convert h2.deriv using 1 <;> dsimp only [id_eq] <;> ring

private theorem sine_mean : meanT_STR02901 polynomialOriginSineSecond.val = 0 := by
  simpa only [show polynomialOriginSineSecond.val = (fun t => Real.sin ((2 : ℝ) * t)) from rfl,
    Nat.cast_ofNat] using meanT_sin_STR02962 (by decide : (2 : ℕ) ≠ 0)

private theorem sine_inE : InE_STR02901 polynomialOriginSineSecond.val := by
  have h := c2_inE_STR02955 polynomialOriginSineSecond.isC2 sine_mean
  have he : (fun t => deriv (deriv polynomialOriginSineSecond.val) t + polynomialOriginSineSecond.val t) =
      fun t => (-3 : ℝ) * polynomialOriginSineSecond.val t := by
    funext t
    rw [sine_second]
    ring
  rw [he] at h
  have hs := inE_smul_STR02955 (-1 / 3) h
  have he' : (fun t => (-1 / 3 : ℝ) * ((-3 : ℝ) * polynomialOriginSineSecond.val t)) =
      polynomialOriginSineSecond.val := by funext t; ring
  rw [he'] at hs
  exact hs

def polynomialOriginSineSecondE : E_STR02969 :=
  ⟨polynomialOriginSineSecond,
    (str029_69_completeness_closed_complements_range_spaces_E.1 _).2 sine_inE⟩

private theorem coefficient_sine : polynomialOriginCoefficient polynomialOriginSineSecondE = 0 := by
  have h : meanCLM_STR02954 (e0_STR02955 polynomialOriginMode *
      (Real.sqrt 2 • e0_STR02955 polynomialOriginSineSecond)) = 0 := by
    rw [meanCLM_apply_STR02954]
    change meanT_STR02901 (fun t => (Real.sqrt 2 * Real.cos (2 * t)) *
      (Real.sqrt 2 * Real.sin (2 * t))) = 0
    rw [meanT_eq_normInt_STR02909]
    simpa [trigBasisFun_STR02934] using
      normInt_trigBasis_mul_STR02934 (some (false, 1)) (some (true, 1))
  rw [mul_smul_comm, map_smul, smul_eq_mul] at h
  change meanCLM_STR02954
    (e0_STR02955 polynomialOriginMode * e0_STR02955 polynomialOriginSineSecond) = 0
  exact (mul_eq_zero.mp h).resolve_left (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'

/-- The explicit actual second-amplitude correction in the genuine closed
complement. The quadratic Taylor coefficient is half this element. -/
def polynomialOriginSecondCorrection (a b : ℝ) : E_STR02969 :=
  (-(a ^ 2 - b ^ 2) / (3 * Real.sqrt 2)) • polynomialOriginModeE +
    (-(a * b) / 3) • polynomialOriginSineSecondE

theorem polynomialOriginSecondCorrection_val (a b t : ℝ) :
    (polynomialOriginSecondCorrection a b : PeriodicC2_STR02969).val t =
      -(a ^ 2 - b ^ 2) / 3 * Real.cos (2 * t) - a * b / 3 * Real.sin (2 * t) := by
  change (-(a ^ 2 - b ^ 2) / (3 * Real.sqrt 2)) * (Real.sqrt 2 * Real.cos (2 * t)) +
    (-(a * b) / 3) * Real.sin (2 * t) = _
  field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
  ring

/-- The corrected origin inverse sends this SECOND derivative to minus the
true second-amplitude forcing, with coefficients12a0 and6a0 on the two modes. -/
theorem polynomialOriginSecondCorrection_inverse (a b t : ℝ) :
    ((polynomialOriginRangeEquiv (polynomialOriginSecondCorrection a b) : Y_STR02969) :
      PeriodicHolder_STR02968).val t =
      -DGPS.Circle.AngularNormalization.a0 *
        (4 * (a ^ 2 - b ^ 2) * Real.cos (2 * t) + 2 * a * b * Real.sin (2 * t)) := by
  have hcos : polynomialOriginCoefficient polynomialOriginModeE = 1 := polynomialOriginMode_unit
  have hc : polynomialOriginCoefficient (polynomialOriginSecondCorrection a b) =
      -(a ^ 2 - b ^ 2) / (3 * Real.sqrt 2) := by
    rw [polynomialOriginSecondCorrection, map_add, map_smul, map_smul, hcos, coefficient_sine]
    simp only [smul_eq_mul, mul_one, mul_zero, add_zero]
  have hc2 : e2_STR02955 polynomialOriginMode = (-4 : ℝ) • e0_STR02955 polynomialOriginMode := by
    apply ext_STR02954
    funext y
    exact polynomialOriginMode_second y
  have hs2 : e2_STR02955 polynomialOriginSineSecond = (-4 : ℝ) • e0_STR02955 polynomialOriginSineSecond := by
    apply ext_STR02954
    funext y
    exact sine_second y
  have hw2 : e2_STR02955 (polynomialOriginSecondCorrection a b : PeriodicC2_STR02969) =
      (-4 : ℝ) • e0_STR02955 (polynomialOriginSecondCorrection a b : PeriodicC2_STR02969) := by
    change e2_STR02955 ((-(a ^ 2 - b ^ 2) / (3 * Real.sqrt 2)) • polynomialOriginMode +
      (-(a * b) / 3) • polynomialOriginSineSecond) = (-4 : ℝ) • e0_STR02955 ((-(a ^ 2 - b ^ 2) / (3 * Real.sqrt 2)) • polynomialOriginMode + (-(a * b) / 3) • polynomialOriginSineSecond)
    rw [map_add, map_smul, map_smul, hc2, hs2]
    apply ext_STR02954
    funext y
    simp only [map_add, map_smul, PeriodicHolder_STR02968.val_add,
      PeriodicHolder_STR02968.val_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hw2t := congrFun (congrArg PeriodicHolder_STR02968.val hw2) t
  change deriv (deriv (polynomialOriginSecondCorrection a b : PeriodicC2_STR02969).val) t =
    -4 * (polynomialOriginSecondCorrection a b : PeriodicC2_STR02969).val t at hw2t
  rw [polynomialOriginRangeEquiv_apply, hw2t, hc, polynomialOriginSecondCorrection_val]
  change (-2 * DGPS.Circle.AngularNormalization.a0) *
      (-4 * (-(a ^ 2 - b ^ 2) / 3 * Real.cos (2 * t) - a * b / 3 * Real.sin (2 * t)) +
        (-(a ^ 2 - b ^ 2) / 3 * Real.cos (2 * t) - a * b / 3 * Real.sin (2 * t))) +
      6 * DGPS.Circle.AngularNormalization.a0 * (-(a ^ 2 - b ^ 2) / (3 * Real.sqrt 2)) *
        (Real.sqrt 2 * Real.cos (2 * t)) = _
  field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
  ring

end DGPS.Examples.PolynomialSpecies
