import DGPS.Examples.PolynomialSpeciesRangeGraphMixedSecond
import DGPS.Examples.PolynomialSpeciesMixedEulerSecond
import DGPS.Examples.PolynomialSpeciesOriginMixedCorrection

/-! Exact mixed field/amplitude second derivative of the SAME genuine implicit
graph. Moving-reference normalization and the true generator are retained in
the forcing. The quadratic Taylor coefficient is half this second derivative. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem projection_of_memY (y : Y_STR02969) :
    PY_STR02955 (y : PeriodicHolder_STR02968) = y := by
  apply Subtype.ext
  apply ext_STR02954
  rw [PY_val_STR02955]
  exact projP_of_inE_STR02955 ((str029_69_completeness_closed_complements_range_spaces_Y.1 _).1 y.2)

private theorem projection_second (F : ℝ → PeriodicHolder_STR02968)
    (hF : ContDiff ℝ ∞ F) :
    iteratedDeriv 2 (PY_STR02955 ∘ F) 0 = PY_STR02955 (iteratedDeriv 2 F 0) := by
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    PY_STR02955.iteratedFDeriv_comp_left hF.contDiffAt (by simp)]
  rfl

/-- The actual graph's SECOND derivative is twice the quadratic Taylor
correction. All inputs are jointly produced same-graph properties, with no
prescribed second derivative or optimizer premise. -/
theorem polynomial_range_graph_mixed_second_coefficient
    {U : Set PolynomialRangeParameters} {ψ : PolynomialRangeParameters → E_STR02969}
    (hU : IsOpen U) (h0U : (0 : PolynomialRangeParameters) ∈ U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0)
    (hgraph : ∀ p ∈ U, polynomialRangeMap (p, ψ p) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (a b : ℝ) :
    iteratedDeriv 2 (fun z : ℝ => ψ (z • ((a, b, (1, 0), 0) : PolynomialRangeParameters))) 0 =
      polynomialOriginMixedSecondCorrection a b := by
  let v := a • cosC2_STR02915 + b • sinC2_STR02915
  let F := fun z : ℝ => polynomialRangeEuler (z, 0) DGPS.Circle.AngularNormalization.a0 (z • v)
  let Y := polynomialOriginRangeEquiv (polynomialOriginMixedSecondCorrection a b)
  have hF : ContDiff ℝ ∞ F := by
    let input := fun z : ℝ => (((z, 0), DGPS.Circle.AngularNormalization.a0, z • v) : PolynomialEulerInput)
    have hi : ContDiff ℝ ∞ input :=
      (contDiff_id.prodMk contDiff_const).prodMk
        (contDiff_const.prodMk (contDiff_id.smul contDiff_const))
    let E : PolynomialEulerInput → PeriodicHolder_STR02968 := fun q => polynomialRangeEuler q.1 q.2.1 q.2.2
    have hE : ContDiff ℝ ∞ E := polynomialRangeEuler_smooth
    change ContDiff ℝ ∞ (E ∘ input)
    exact hE.comp hi
  have hsecond : iteratedDeriv 2 F 0 = -(Y : PeriodicHolder_STR02968) := by
    apply ext_STR02954
    funext t
    have h1 := polynomialMixedEuler_second_pointwise a b t
    have h2 := polynomialOriginMixedSecondCorrection_inverse a b t
    change (iteratedDeriv 2 F 0).val t = -((Y : PeriodicHolder_STR02968).val t)
    rw [show (iteratedDeriv 2 F 0).val t = _ from h1,
      show (Y : PeriodicHolder_STR02968).val t = _ from h2]
    ring
  have hraw : (fun z : ℝ => polynomialRangeMap
      (z • ((a, b, (1, 0), 0) : PolynomialRangeParameters), (0 : E_STR02969))) =
      PY_STR02955 ∘ F := by
    funext z
    simp only [polynomialRangeMap, F, v, Function.comp_def, Prod.smul_mk,
      smul_zero, Submodule.coe_zero, zero_mul, mul_zero, zero_add, add_zero, mul_one,
      smul_add, smul_smul, smul_eq_mul]
  have hraw2 : iteratedDeriv 2 (fun z : ℝ => polynomialRangeMap
      (z • ((a, b, (1, 0), 0) : PolynomialRangeParameters), (0 : E_STR02969))) 0 = -Y := by
    rw [hraw, projection_second F hF, hsecond, map_neg, projection_of_memY]
  apply polynomialOriginRangeEquiv.injective
  rw [polynomial_range_graph_mixed_second hU h0U hψ hψ0 hgraph hzero hfirst, hraw2, neg_neg]

end DGPS.Examples.PolynomialSpecies
