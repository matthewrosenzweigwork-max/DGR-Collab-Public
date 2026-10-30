import DGPS.Examples.PolynomialSpeciesReflectionValue
import DGPS.Frontier.STR029.T21

/-! The ACTUAL interacting range equation is natural under SAME-field spatial
reflection. Only generic projection/pullback algebra is reused from T21. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem derivative_reflection (f g : ℝ → ℝ) (he : ∀ t, f (-t) = g t) (t : ℝ) :
    deriv f (-t) = -deriv g t := by
  have hfun : (fun y : ℝ => f (-y)) = g := funext he
  have hd := deriv_comp_neg (f := f) (x := t)
  rw [hfun] at hd
  linarith only [hd]

private theorem second_reflection (f g : PeriodicC2_STR02969)
    (he : ∀ t, f.val (-t) = g.val t) (t : ℝ) :
    deriv (deriv f.val) (-t) = deriv (deriv g.val) t := by
  have hf : pb_STR02916 (-1) 0 f.val = g.val := by
    funext x
    simpa only [pb_STR02916, neg_one_mul, add_zero] using he x
  have hd := deriv2_pb_STR02916 (σ := -1) (c := 0) (Or.inr rfl)
    f.isC2.2.1 f.isC2.2.2.1
  rw [hf] at hd
  simpa only [pb_STR02916, neg_one_mul, add_zero] using (congrFun hd t).symm

private theorem potential_reflection (h s r : ℝ) (u v : PeriodicC2_STR02969)
    (hu : ∀ t, v.val (-t) = u.val t) (t : ℝ) :
    (polynomialRangeEulerPotential (h, s) r v).val (-t) =
      (polynomialRangeEulerPotential (h, s) r u).val t := by
  obtain ⟨_, _, hm, hA, hJ⟩ := polynomialRange_moments_reflection h s u v hu
  have hv1 := derivative_reflection _ _ hu
  have hv2 := second_reflection v u hu
  simp only [polynomialRangeEulerPotential, PeriodicHolder_STR02968.val_add,
    PeriodicHolder_STR02968.val_sub, PeriodicHolder_STR02968.val_smul, val_mul_STR02954,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
    e0_val_STR02955, e1_val_STR02955, e2_val_STR02955]
  rw [hm, hA, hJ, hv1, hv2, hu, polynomialRangeLogWeight_derivative_reflection,
    polynomialRangeFeature_reflection, polynomialRangeGenerator_reflection, polynomialRangeGradientSq_reflection]
  ring

private theorem potential_mean_reflection (h s r : ℝ) (u v : PeriodicC2_STR02969)
    (hu : ∀ t, v.val (-t) = u.val t) :
    eulerMean (e0_STR02955 (polynomialRangeLogWeight (h, s))) v
      (polynomialRangeEulerPotential (h, s) r v) =
    eulerMean (e0_STR02955 (polynomialRangeLogWeight (h, s))) u
      (polynomialRangeEulerPotential (h, s) r u) := by
  let K := polynomialRangeEulerPotential (h, s) r v
  let R := eulerDensity (e0_STR02955 (polynomialRangeLogWeight (h, s))) v
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
    meanT_STR02901 F = meanT_STR02901 (pb_STR02916 (-1) 0 F) :=
      (meanT_pb_STR02916 (Or.inr rfl) 0 hp).symm
    _ = _ := by
      congr 1
      funext t
      simp only [pb_STR02916, neg_one_mul, add_zero, F, K, R, potential_reflection h s r u v hu,
        polynomialRangeDensity_reflection h s u v hu]

/-- The normalized full interacting Euler map transforms, including its actual
mean subtraction. No Euler equation is assumed in this identity. -/
theorem polynomialRangeEuler_reflection (h s r : ℝ) (u v : PeriodicC2_STR02969)
    (hu : ∀ t, v.val (-t) = u.val t) (t : ℝ) :
    (polynomialRangeEuler (h, s) r v).val (-t) =
      (polynomialRangeEuler (h, s) r u).val t := by
  simp only [polynomialRangeEuler, val_mul_STR02954, PeriodicHolder_STR02968.val_sub,
    PeriodicHolder_STR02968.val_smul, val_one_STR02954,
    Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  rw [polynomialRangeDensity_reflection h s u v hu, potential_reflection h s r u v hu,
    potential_mean_reflection h s r u v hu]

/-- A genuine interacting range zero is transported at the SAME field and
tilt. The original first-harmonic complement is retained exactly. -/
theorem polynomialRangeMap_reflection_zero (a b h s γ : ℝ) (w : E_STR02969)
    (hw : polynomialRangeMap (((a, b, (h, s), γ) : PolynomialRangeParameters), w) = 0) :
    polynomialRangeMap (((a, -b, (h, s), γ) : PolynomialRangeParameters),
      pullE_STR02916 (-1) (Or.inr rfl) 0 w) = 0 := by
  let u := a • cosC2_STR02915 + b • sinC2_STR02915 + (w : PeriodicC2_STR02969)
  let v := a • cosC2_STR02915 + (-b) • sinC2_STR02915 +
    (pullE_STR02916 (-1) (Or.inr rfl) 0 w : PeriodicC2_STR02969)
  let r := DGPS.Circle.AngularNormalization.a0 * (1 + γ)
  let Eplus := polynomialRangeEuler (h, s) r u
  let Eminus := polynomialRangeEuler (h, s) r v
  have hu (t : ℝ) : v.val (-t) = u.val t := by
    change a * Real.cos (-t) + (-b) * Real.sin (-t) +
      (pullE_STR02916 (-1) (Or.inr rfl) 0 w : PeriodicC2_STR02969).val (-t) =
        a * Real.cos t + b * Real.sin t + (w : PeriodicC2_STR02969).val t
    rw [pullE_val_STR02916, Real.cos_neg, Real.sin_neg]
    simp only [neg_one_mul, neg_neg, add_zero]
    ring
  have hE : Eminus.val = pb_STR02916 (-1) 0 Eplus.val := by
    funext t
    have he := polynomialRangeEuler_reflection h s r u v hu (-t)
    simpa only [neg_neg, pb_STR02916, neg_one_mul, add_zero, Eminus, Eplus] using he
  have hp : projP_STR02953 Eplus.val = 0 := by
    have hh := congrArg Subtype.val hw
    have ht := congrArg PeriodicHolder_STR02968.val hh
    change (PY_STR02955 Eplus : PeriodicHolder_STR02968).val = 0 at ht
    rw [PY_val_STR02955] at ht
    exact ht
  have hm : projP_STR02953 Eminus.val = 0 := by
    rw [hE, projP_pb_STR02921 (Or.inr rfl) Eplus.isPerHolder.2.1 Eplus.isPerHolder.1, hp]
    rfl
  apply Subtype.ext
  apply ext_STR02954
  change (PY_STR02955 Eminus : PeriodicHolder_STR02968).val = 0
  rw [PY_val_STR02955]
  exact hm

end DGPS.Examples.PolynomialSpecies
