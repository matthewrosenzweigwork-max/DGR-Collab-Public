import DGPS.Examples.PolynomialSpeciesHalfTurnValue
import DGPS.Frontier.STR029.T21

/-! The ACTUAL interacting range equation is natural under the polynomial
half-turn. Only the generic projection/pullback algebra is imported from T21. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem derivative_shift (f g : ℝ → ℝ) (he : ∀ t, f (t + Real.pi) = g t) (t : ℝ) :
    deriv f (t + Real.pi) = deriv g t := by
  have hfun : (fun y : ℝ => f (y + Real.pi)) = g := funext he
  have hd := deriv_comp_add_const (f := f) Real.pi t
  rw [hfun] at hd
  exact hd.symm

private theorem potential_half_turn (h s r : ℝ) (u v : PeriodicC2_STR02969)
    (hu : ∀ t, v.val (t + Real.pi) = u.val t) (t : ℝ) :
    (polynomialRangeEulerPotential (-h, s) r v).val (t + Real.pi) =
      (polynomialRangeEulerPotential (h, s) r u).val t := by
  obtain ⟨_, _, hm, hA, hJ⟩ := polynomialRange_moments_half_turn h s u v hu
  have hv1 := derivative_shift _ _ hu
  have hv2 := derivative_shift _ _ hv1
  simp only [polynomialRangeEulerPotential, PeriodicHolder_STR02968.val_add,
    PeriodicHolder_STR02968.val_sub, PeriodicHolder_STR02968.val_smul, val_mul_STR02954,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
    e0_val_STR02955, e1_val_STR02955, e2_val_STR02955]
  rw [hm, hA, hJ, hv1, hv2, hu, polynomialRangeLogWeight_derivative_half_turn,
    polynomialRangeFeature_half_turn, polynomialRangeGenerator_half_turn, polynomialRangeGradientSq_half_turn]

private theorem potential_mean_half_turn (h s r : ℝ) (u v : PeriodicC2_STR02969)
    (hu : ∀ t, v.val (t + Real.pi) = u.val t) :
    eulerMean (e0_STR02955 (polynomialRangeLogWeight (-h, s))) v
      (polynomialRangeEulerPotential (-h, s) r v) =
    eulerMean (e0_STR02955 (polynomialRangeLogWeight (h, s))) u
      (polynomialRangeEulerPotential (h, s) r u) := by
  let K := polynomialRangeEulerPotential (-h, s) r v
  let R := eulerDensity (e0_STR02955 (polynomialRangeLogWeight (-h, s))) v
  let F := fun t : ℝ => K.val t * R.val t
  have hp : Function.Periodic F (2 * Real.pi) := by
    intro t
    dsimp only [F]
    rw [K.isPerHolder.1 t, R.isPerHolder.1 t]
  unfold eulerMean
  rw [meanCLM_apply_STR02954, meanCLM_apply_STR02954]
  change meanT_STR02901 F = meanT_STR02901 (fun t : ℝ =>
    (polynomialRangeEulerPotential (h, s) r u).val t *
      (eulerDensity (e0_STR02955 (polynomialRangeLogWeight (h, s))) u).val t)
  calc
    meanT_STR02901 F = meanT_STR02901 (pb_STR02916 1 Real.pi F) :=
      (meanT_pb_STR02916 (Or.inl rfl) Real.pi hp).symm
    _ = _ := by
      congr 1
      funext t
      simp only [pb_STR02916, one_mul, F, K, R, potential_half_turn h s r u v hu,
        polynomialRangeDensity_half_turn h s u v hu]

/-- The normalized full interacting Euler map transforms, including its actual
mean subtraction. No Euler equation is assumed in this identity. -/
theorem polynomialRangeEuler_half_turn (h s r : ℝ) (u v : PeriodicC2_STR02969)
    (hu : ∀ t, v.val (t + Real.pi) = u.val t) (t : ℝ) :
    (polynomialRangeEuler (-h, s) r v).val (t + Real.pi) =
      (polynomialRangeEuler (h, s) r u).val t := by
  simp only [polynomialRangeEuler, val_mul_STR02954, PeriodicHolder_STR02968.val_sub,
    PeriodicHolder_STR02968.val_smul, val_one_STR02954,
    Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  rw [polynomialRangeDensity_half_turn h s u v hu, potential_half_turn h s r u v hu,
    potential_mean_half_turn h s r u v hu]

/-- A genuine interacting range zero is transported to the reflected field and
amplitudes. The correction remains in the actual first-harmonic complement. -/
theorem polynomialRangeMap_half_turn_zero (a b h s γ : ℝ) (w : E_STR02969)
    (hw : polynomialRangeMap (((a, b, (h, s), γ) : PolynomialRangeParameters), w) = 0) :
    polynomialRangeMap (((-a, -b, (-h, s), γ) : PolynomialRangeParameters),
      pullE_STR02916 1 (Or.inl rfl) (-Real.pi) w) = 0 := by
  let u := a • cosC2_STR02915 + b • sinC2_STR02915 + (w : PeriodicC2_STR02969)
  let v := (-a) • cosC2_STR02915 + (-b) • sinC2_STR02915 +
    (pullE_STR02916 1 (Or.inl rfl) (-Real.pi) w : PeriodicC2_STR02969)
  let r := DGPS.Circle.AngularNormalization.a0 * (1 + γ)
  let Eplus := polynomialRangeEuler (h, s) r u
  let Eminus := polynomialRangeEuler (-h, s) r v
  have hu (t : ℝ) : v.val (t + Real.pi) = u.val t := by
    change (-a) * Real.cos (t + Real.pi) + (-b) * Real.sin (t + Real.pi) +
      (pullE_STR02916 1 (Or.inl rfl) (-Real.pi) w : PeriodicC2_STR02969).val (t + Real.pi) =
        a * Real.cos t + b * Real.sin t + (w : PeriodicC2_STR02969).val t
    rw [pullE_val_STR02916, Real.cos_add_pi, Real.sin_add_pi]
    simp only [one_mul, add_neg_cancel_right]
    ring
  have hE : Eminus.val = pb_STR02916 1 (-Real.pi) Eplus.val := by
    funext t
    have he := polynomialRangeEuler_half_turn h s r u v hu (t - Real.pi)
    rw [sub_add_cancel] at he
    simpa only [pb_STR02916, one_mul, sub_eq_add_neg, Eminus, Eplus] using he
  have hp : projP_STR02953 Eplus.val = 0 := by
    have hh := congrArg Subtype.val hw
    have ht := congrArg PeriodicHolder_STR02968.val hh
    change (PY_STR02955 Eplus : PeriodicHolder_STR02968).val = 0 at ht
    rw [PY_val_STR02955] at ht
    exact ht
  have hm : projP_STR02953 Eminus.val = 0 := by
    rw [hE, projP_pb_STR02921 (Or.inl rfl) Eplus.isPerHolder.2.1 Eplus.isPerHolder.1, hp]
    rfl
  apply Subtype.ext
  apply ext_STR02954
  change (PY_STR02955 Eminus : PeriodicHolder_STR02968).val = 0
  rw [PY_val_STR02955]
  exact hm

end DGPS.Examples.PolynomialSpecies
