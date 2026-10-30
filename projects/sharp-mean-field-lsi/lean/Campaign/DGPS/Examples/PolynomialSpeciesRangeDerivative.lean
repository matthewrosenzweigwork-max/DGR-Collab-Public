import DGPS.Examples.PolynomialSpeciesRangeMap
import DGPS.Examples.PolynomialSpeciesRangeInverse

/-! Identification of the actual interacting range derivative at the origin.
Every coefficient is computed from the same independent-parameter normalized chart. -/

noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization
open DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

private theorem logWeight_origin : polynomialRangeLogWeight (0, 0) = 0 := by
  simp [polynomialRangeLogWeight]

private theorem feature_origin : polynomialRangeFeature (0, 0) = polynomialOriginMode := by
  have h := polynomialRangeFeature_actual 0
  rw [polynomial_root_origin, ← polynomialOriginMode_actual] at h
  apply Subtype.ext
  have he := congrArg PeriodicHolder_STR02968.val h
  simp only [e0_val_STR02955] at he
  unfold PeriodicC2_STR02969.val at he
  exact he

private theorem reference_origin : polynomialRangeReference (0, 0) = 1 := by
  rw [polynomialRangeReference, logWeight_origin, map_zero, rho_zero_STR02955]

private theorem second_origin : e2_STR02955 polynomialOriginMode = (-4 : ℝ) • e0_STR02955 polynomialOriginMode := by
  apply ext_STR02954
  funext t
  exact polynomialOriginMode_second t

private theorem generator_origin : polynomialRangeGenerator (0, 0) =
    (4 * DGPS.Circle.AngularNormalization.a0) • e0_STR02955 polynomialOriginMode := by
  unfold polynomialRangeGenerator
  rw [logWeight_origin, feature_origin, map_zero, zero_mul, sub_zero, second_origin]
  apply ext_STR02954
  funext t
  simp only [PeriodicHolder_STR02968.val_smul, Pi.smul_apply, smul_eq_mul,
    show (-((-4 : ℝ) • e0_STR02955 polynomialOriginMode)).val t =
      -((-4 : ℝ) * polynomialOriginMode.val t) from rfl]
  simp only [e0_val_STR02955]
  ring

private theorem feature_mean_origin : meanCLM_STR02954 (e0_STR02955 polynomialOriginMode) = 0 := by
  have h := polynomialRangeFeature_centered (0, 0)
  rw [feature_origin, reference_origin, mul_one] at h
  exact h

private theorem gradient_mean_origin : meanCLM_STR02954 (polynomialRangeGradientSq (0, 0)) =
    4 * DGPS.Circle.AngularNormalization.a0 := by
  let H := e1_STR02955 polynomialOriginMode * e1_STR02955 polynomialOriginMode +
    e0_STR02955 polynomialOriginMode * e2_STR02955 polynomialOriginMode
  have hd : ∀ t, HasDerivAt (fun s => polynomialOriginMode.val s * deriv polynomialOriginMode.val s)
      (H.val t) t := by
    intro t
    convert ((polynomialOriginMode.isC2.2.1 t).hasDerivAt.mul
      (polynomialOriginMode.isC2.2.2.1 t).hasDerivAt) using 1
    rfl
  have hp : polynomialOriginMode.val (2 * Real.pi) * deriv polynomialOriginMode.val (2 * Real.pi) =
      polynomialOriginMode.val 0 * deriv polynomialOriginMode.val 0 := by
    rw [show polynomialOriginMode.val (2 * Real.pi) = polynomialOriginMode.val 0 by
      simpa using polynomialOriginMode.isC2.1 0,
      show deriv polynomialOriginMode.val (2 * Real.pi) = deriv polynomialOriginMode.val 0 by
        simpa using (periodic_deriv_STR02901 polynomialOriginMode.isC2.1) 0]
  have hm : meanCLM_STR02954 H = 0 := ftc_mean_STR02955 hd H.isPerHolder.2.1 hp
  dsimp only [H] at hm
  rw [map_add, second_origin, mul_smul_comm, map_smul, polynomialOriginMode_unit] at hm
  have hnorm : meanCLM_STR02954 (e1_STR02955 polynomialOriginMode * e1_STR02955 polynomialOriginMode) = 4 := by
    change meanCLM_STR02954 (e1_STR02955 polynomialOriginMode * e1_STR02955 polynomialOriginMode) +
      (-4 : ℝ) * 1 = 0 at hm
    linarith
  unfold polynomialRangeGradientSq
  rw [feature_origin, map_smul, hnorm]
  change DGPS.Circle.AngularNormalization.a0 * 4 = 4 * DGPS.Circle.AngularNormalization.a0
  ring

private theorem mean_of_memY (y : Y_STR02969) : meanCLM_STR02954 (y : PeriodicHolder_STR02968) = 0 :=
  ((str029_69_completeness_closed_complements_range_spaces_Y.1 _).1 y.2).1

private theorem PY_of_memY (y : Y_STR02969) : PY_STR02955 (y : PeriodicHolder_STR02968) = y := by
  apply Subtype.ext
  apply ext_STR02954
  rw [PY_val_STR02955]
  exact projP_of_inE_STR02955 ((str029_69_completeness_closed_complements_range_spaces_Y.1 _).1 y.2)

/-- The actual Euler map has the corrected physical linearization along every complement direction. -/
theorem polynomialRangeEuler_origin_line (w : E_STR02969) :
    HasDerivAt (fun z : ℝ => polynomialRangeEuler (0, 0) DGPS.Circle.AngularNormalization.a0
      (z • (w : PeriodicC2_STR02969)))
      ((polynomialOriginRangeEquiv w : Y_STR02969) : PeriodicHolder_STR02968) 0 := by
  let a := DGPS.Circle.AngularNormalization.a0
  let V := e0_STR02955 (w : PeriodicC2_STR02969)
  let D := e1_STR02955 (w : PeriodicC2_STR02969)
  let D2 := e2_STR02955 (w : PeriodicC2_STR02969)
  let φ := e0_STR02955 polynomialOriginMode
  let B := polynomialRangeGenerator (0, 0)
  let j := polynomialRangeGradientSq (0, 0)
  let R := fun z : ℝ => rho_STR02954 (0, z • V)
  let m := fun z : ℝ => meanCLM_STR02954 (φ * R z)
  let A := fun z : ℝ => meanCLM_STR02954 (B * R z)
  let J := fun z : ℝ => meanCLM_STR02954 (j * R z)
  let c := polynomialOriginCoefficient w
  let Lw : PeriodicHolder_STR02968 := (polynomialOriginRangeEquiv w : Y_STR02969)
  have hV : meanCLM_STR02954 V = 0 :=
    ((str029_69_completeness_closed_complements_range_spaces_E.1 _).1 w.2).1
  have hR : HasDerivAt R V 0 := by
    simpa only [zero_add, rho_zero_STR02955, mul_one, one_mul, hV, zero_smul, sub_zero] using
      hasDerivAt_rho_path_STR02949 0 (0 : PeriodicHolder_STR02968) V
  have hR0 : R 0 = 1 := by simp only [R, zero_smul, rho_zero_STR02955]
  have hm0 : m 0 = 0 := by rw [show m 0 = meanCLM_STR02954 (φ * R 0) from rfl, hR0, mul_one]; exact feature_mean_origin
  have hA0 : A 0 = 0 := by
    rw [show A 0 = meanCLM_STR02954 (B * R 0) from rfl, hR0, mul_one]
    dsimp only [B]
    rw [generator_origin, map_smul, feature_mean_origin, smul_zero]
  have hJ0 : J 0 = 4 * a := by
    rw [show J 0 = meanCLM_STR02954 (j * R 0) from rfl, hR0, mul_one]
    exact gradient_mean_origin
  have hm : HasDerivAt m c 0 := by
    have hd := meanCLM_STR02954.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_const (0 : ℝ) φ).mul hR)
    simp only [Function.comp_def, Pi.mul_apply, zero_mul, zero_add] at hd
    convert hd using 1
    change c = meanCLM_STR02954 (φ * V)
    rfl
  have hA : HasDerivAt A (4 * a * c) 0 := by
    have hd := meanCLM_STR02954.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_const (0 : ℝ) B).mul hR)
    simp only [Function.comp_def, Pi.mul_apply, zero_mul, zero_add] at hd
    convert hd using 1
    change 4 * a * c = meanCLM_STR02954 (B * V)
    rw [show B = (4 * a) • φ from generator_origin, smul_mul_assoc, map_smul]
    rfl
  have hJ : HasDerivAt J (meanCLM_STR02954 (j * V)) 0 := by
    simpa only [Function.comp_def, Pi.mul_apply, zero_mul, zero_add] using
      meanCLM_STR02954.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        ((hasDerivAt_const (0 : ℝ) j).mul hR)
  have hs0 : HasDerivAt (fun z : ℝ => z • V) V 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const V
  have hs1 : HasDerivAt (fun z : ℝ => z • D) D 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const D
  have hs2 : HasDerivAt (fun z : ℝ => z • D2) D2 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const D2
  let K := fun z : ℝ =>
    a • ((-2 : ℝ) • (z • D2) - (z • D) * (z • D)) - (2 * a) • (z • V) +
      (2 * eta * (A z + eta * m z * J z - a * m z)) • φ +
      (2 * eta * m z) • B + (eta ^ 2 * m z ^ 2) • j
  have hKraw := ((((((hs2.const_smul (-2 : ℝ)).sub (hs1.mul hs1)).const_smul a).sub
    (hs0.const_smul (2 * a))).add
      (((hA.add ((hm.const_mul eta).mul hJ)).sub (hm.const_mul a)).const_mul (2 * eta) |>.smul_const φ)).add
        ((hm.const_mul (2 * eta)).smul_const B)).add
          (((hm.pow 2).const_mul (eta ^ 2)).smul_const j)
  have hK : HasDerivAt K Lw 0 := by
    change HasDerivAt K _ 0 at hKraw
    apply hKraw.congr_deriv
    apply ext_STR02954
    funext t
    simp only [hm0, hA0, hJ0, zero_smul, zero_mul, mul_zero, add_zero, zero_add, sub_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), PeriodicHolder_STR02968.val_add,
      PeriodicHolder_STR02968.val_sub, PeriodicHolder_STR02968.val_smul, val_mul_STR02954,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
      show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    have hval := polynomialOriginRangeEquiv_apply w t
    change _ = ((polynomialOriginRangeEquiv w : Y_STR02969) : PeriodicHolder_STR02968).val t
    rw [hval]
    have hb : B.val t = 4 * a * polynomialOriginMode.val t := by
      rw [show B = (4 * a) • φ from generator_origin]
      rfl
    rw [hb]
    dsimp only [D2, V, φ, c, a]
    simp only [e0_val_STR02955, e2_val_STR02955]
    have hc := congrArg (fun z : ℝ => z * polynomialOriginCoefficient w * polynomialOriginMode.val t)
      polynomial_origin_coupling_coefficient
    nlinarith [hc]
  have hK0 : K 0 = 0 := by simp only [K, hm0, hA0, zero_smul, smul_zero, zero_mul, mul_zero, add_zero, zero_add,
    sub_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have hN := meanCLM_STR02954.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hK.mul hR)
  simp only [Function.comp_def, Pi.mul_apply, hK0, hR0, zero_mul, zero_add, add_zero, mul_one] at hN
  have hLw : meanCLM_STR02954 Lw = 0 := mean_of_memY _
  rw [hLw] at hN
  have hEuler := hR.mul (hK.sub (hN.smul_const (1 : PeriodicHolder_STR02968)))
  change HasDerivAt (fun z : ℝ => R z * (K z - meanCLM_STR02954 (K z * R z) • (1 : PeriodicHolder_STR02968)))
    (V * (K 0 - meanCLM_STR02954 (K 0 * R 0) • (1 : PeriodicHolder_STR02968)) +
      R 0 * (Lw - (0 : ℝ) • (1 : PeriodicHolder_STR02968))) 0 at hEuler
  simp only [hK0, hR0, zero_mul, map_zero, zero_smul, sub_zero, mul_zero, zero_add, one_mul] at hEuler
  have hDensity (z : ℝ) : eulerDensity (e0_STR02955 (polynomialRangeLogWeight (0, 0)))
      (z • (w : PeriodicC2_STR02969)) = R z := by
    simp only [eulerDensity, logWeight_origin, map_zero, map_smul, zero_add, R, V]
  have hPotential (z : ℝ) : polynomialRangeEulerPotential (0, 0)
      DGPS.Circle.AngularNormalization.a0 (z • (w : PeriodicC2_STR02969)) = K z := by
    simp only [polynomialRangeEulerPotential, logWeight_origin, feature_origin,
      map_zero, map_smul, zero_mul, smul_zero, sub_zero, zero_add, eulerMean, eulerDensity,
      K, R, m, A, J, a, V, D, D2, φ, B, j]
    <;> rfl
  have hfun : (fun z : ℝ => polynomialRangeEuler (0, 0) DGPS.Circle.AngularNormalization.a0
      (z • (w : PeriodicC2_STR02969))) =
      fun z : ℝ => R z * (K z - meanCLM_STR02954 (K z * R z) • (1 : PeriodicHolder_STR02968)) := by
    funext z
    simp only [polynomialRangeEuler, eulerMean, hPotential, hDensity]
  rw [hfun]
  exact hEuler

/-- The actual partial derivative is the explicit corrected isomorphism, with no inverse premise. -/
theorem polynomialRangeMap_partial_origin :
    fderiv ℝ polynomialRangeMap ((0 : PolynomialRangeParameters), (0 : E_STR02969)) ∘L
      ContinuousLinearMap.inr ℝ PolynomialRangeParameters E_STR02969 =
        (polynomialOriginRangeEquiv : E_STR02969 →L[ℝ] Y_STR02969) := by
  apply ContinuousLinearMap.ext
  intro w
  have hp := PY_STR02955.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (polynomialRangeEuler_origin_line w)
  rw [PY_of_memY] at hp
  have hfun : (fun z : ℝ => PY_STR02955 (polynomialRangeEuler (0, 0)
      DGPS.Circle.AngularNormalization.a0 (z • (w : PeriodicC2_STR02969)))) =
      fun z : ℝ => polynomialRangeMap ((0 : PolynomialRangeParameters), z • w) := by
    funext z
    simp [polynomialRangeMap]
    rw [show (0 : ℝ × ℝ) = (0, 0) by ext <;> rfl]
  change HasDerivAt (fun z : ℝ => PY_STR02955 (polynomialRangeEuler (0, 0)
    DGPS.Circle.AngularNormalization.a0 (z • (w : PeriodicC2_STR02969)))) _ 0 at hp
  rw [hfun] at hp
  have hline : HasDerivAt (fun z : ℝ => ((0 : PolynomialRangeParameters), z • w))
      ((0 : PolynomialRangeParameters), w) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (0 : PolynomialRangeParameters)).prodMk
      ((hasDerivAt_id (0 : ℝ)).smul_const w)
  have hd := ((polynomialRangeMap_smooth.differentiable (by simp)
    ((0 : PolynomialRangeParameters), (0 : E_STR02969))).hasFDerivAt).comp_hasDerivAt_of_eq
      (0 : ℝ) hline (by simp)
  change fderiv ℝ polynomialRangeMap ((0 : PolynomialRangeParameters), (0 : E_STR02969))
    ((0 : PolynomialRangeParameters), w) = polynomialOriginRangeEquiv w
  exact hd.unique hp

/-- Actual invertibility, obtained from the constructed complement isomorphism. -/
theorem polynomialRangeMap_partial_invertible :
    (fderiv ℝ polynomialRangeMap ((0 : PolynomialRangeParameters), (0 : E_STR02969)) ∘L
      ContinuousLinearMap.inr ℝ PolynomialRangeParameters E_STR02969).IsInvertible := by
  rw [polynomialRangeMap_partial_origin]
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (polynomialOriginRangeEquiv.symm : Y_STR02969 →L[ℝ] E_STR02969))
  · apply ContinuousLinearMap.ext
    intro y
    exact polynomialOriginRangeEquiv.apply_symm_apply y
  · apply ContinuousLinearMap.ext
    intro w
    exact polynomialOriginRangeEquiv.symm_apply_apply w

/-- The genuine interacting range graph; its zero-amplitude correction vanishes for every
independent (h,s,gamma) in the same open parameter neighborhood. -/
theorem exists_polynomial_range_graph :
    ∃ (U : Set PolynomialRangeParameters) (N : Set E_STR02969) (ψ : PolynomialRangeParameters → E_STR02969),
      IsOpen U ∧ (0 : PolynomialRangeParameters) ∈ U ∧ IsOpen N ∧ (0 : E_STR02969) ∈ N ∧
      ContDiffOn ℝ ∞ ψ U ∧ (∀ p ∈ U, ψ p ∈ N) ∧
      (∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w) ∧
      ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
        ψ (0, 0, (h, s), γ) = 0 := by
  haveI : CompleteSpace E_STR02969 := str029_69_completeness_closed_complements_range_spaces_E.2.2
  haveI : CompleteSpace Y_STR02969 := str029_69_completeness_closed_complements_range_spaces_Y.2.2
  have h0 : polynomialRangeMap ((0 : PolynomialRangeParameters), (0 : E_STR02969)) = 0 := by
    rw [show (0 : PolynomialRangeParameters) = (0, 0, (0, 0), 0) by ext <;> rfl]
    exact polynomialRangeMap_equilibrium 0 0 0
  obtain ⟨U, N, ψ, hU, h0U, hN, h0N, hsmooth, hψ0, hψN, hgraph⟩ :=
    implicit_graph_STR02916 polynomialRangeMap_smooth h0 polynomialRangeMap_partial_invertible
  refine ⟨U, N, ψ, hU, h0U, hN, h0N, hsmooth, hψN, hgraph, ?_⟩
  intro h s γ hp
  exact (hgraph _ hp 0 h0N).1 (polynomialRangeMap_equilibrium h s γ)

end DGPS.Examples.PolynomialSpecies
