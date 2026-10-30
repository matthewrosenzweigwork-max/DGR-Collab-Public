import DGPS.Examples.PolynomialSpeciesRangeDeficit
import DGPS.Examples.PolynomialSpeciesReflectionData

/-! Exact SAME-field reflection covariance of the actual normalized moments
and nonlocal deficit. The reference and all normalizing constants are retained. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem partition_reflection (f g : PeriodicC2_STR02969)
    (he : ∀ t, f.val (-t) = g.val t) :
    Z_STR02954 (0, e0_STR02955 f) = Z_STR02954 (0, e0_STR02955 g) := by
  let F := fun t : ℝ => Real.exp (f.val t)
  have hp : Function.Periodic F (2 * Real.pi) := by
    intro t
    dsimp only [F]
    rw [f.isC2.1 t]
  rw [Z_eq_meanT_STR02954, Z_eq_meanT_STR02954]
  simp only [zero_mul, zero_add, e0_val_STR02955]
  calc
    meanT_STR02901 F = meanT_STR02901 (pb_STR02916 (-1) 0 F) :=
      (meanT_pb_STR02916 (Or.inr rfl) 0 hp).symm
    _ = _ := by congr 1; funext t; simp only [pb_STR02916, neg_one_mul, add_zero, F, he]

private theorem tilted_partition (h s : ℝ) (u v : PeriodicC2_STR02969)
    (hu : ∀ t, v.val (-t) = u.val t) :
    Z_STR02954 (0, e0_STR02955 (polynomialRangeLogWeight (h, s)) + e0_STR02955 v) =
      Z_STR02954 (0, e0_STR02955 (polynomialRangeLogWeight (h, s)) + e0_STR02955 u) := by
  rw [← map_add, ← map_add]
  apply partition_reflection
  intro t
  simp only [PeriodicC2_STR02969.val_add, Pi.add_apply, polynomialRangeLogWeight_reflection, hu]

private theorem density_value (L : PeriodicC2_STR02969) (u : PeriodicC2_STR02969) (t : ℝ) :
    (eulerDensity (e0_STR02955 L) u).val t = Real.exp (L.val t + u.val t) /
      Z_STR02954 (0, e0_STR02955 L + e0_STR02955 u) := by
  rw [eulerDensity, rho_val_STR02954]
  simp only [rhoT_STR02901, zero_mul, zero_add, PeriodicHolder_STR02968.val_add,
    Pi.add_apply, e0_val_STR02955, Z_eq_meanT_STR02954]

/-- The actual normalized chart densities transform with their references. -/
theorem polynomialRangeDensity_reflection (h s : ℝ) (u v : PeriodicC2_STR02969)
    (hu : ∀ t, v.val (-t) = u.val t) (t : ℝ) :
    (eulerDensity (e0_STR02955 (polynomialRangeLogWeight (h, s))) v).val (-t) =
      (eulerDensity (e0_STR02955 (polynomialRangeLogWeight (h, s))) u).val t := by
  rw [density_value, density_value, polynomialRangeLogWeight_reflection, hu, tilted_partition h s u v hu]

private theorem expectation_reflection (h s : ℝ) (u v : PeriodicC2_STR02969)
    (hu : ∀ t, v.val (-t) = u.val t) (f g : PeriodicHolder_STR02968)
    (hf : ∀ t, f.val (-t) = g.val t) :
    eulerMean (e0_STR02955 (polynomialRangeLogWeight (h, s))) v f =
      eulerMean (e0_STR02955 (polynomialRangeLogWeight (h, s))) u g := by
  let R := eulerDensity (e0_STR02955 (polynomialRangeLogWeight (h, s))) v
  let F := fun t : ℝ => f.val t * R.val t
  have hp : Function.Periodic F (2 * Real.pi) := by
    intro t
    dsimp only [F]
    rw [f.isPerHolder.1 t, R.isPerHolder.1 t]
  unfold eulerMean
  rw [meanCLM_apply_STR02954, meanCLM_apply_STR02954]
  change meanT_STR02901 F = meanT_STR02901 (fun t : ℝ => g.val t *
    (eulerDensity (e0_STR02955 (polynomialRangeLogWeight (h, s))) u).val t)
  calc
    meanT_STR02901 F = meanT_STR02901 (pb_STR02916 (-1) 0 F) :=
      (meanT_pb_STR02916 (Or.inr rfl) 0 hp).symm
    _ = _ := by
      congr 1
      funext t
      simp only [pb_STR02916, neg_one_mul, add_zero, F, R, hf, polynomialRangeDensity_reflection h s u v hu]

/-- Every changing scalar in the ACTUAL deficit transforms on the same chart pair.
The chart relation is only a concrete spatial pullback, not an Euler/optimizer premise. -/
theorem polynomialRange_moments_reflection (h s : ℝ) (u v : PeriodicC2_STR02969)
    (hu : ∀ t, v.val (-t) = u.val t) :
    let Lm := e0_STR02955 (polynomialRangeLogWeight (h, s))
    let Lp := e0_STR02955 (polynomialRangeLogWeight (h, s))
    eulerEntropy Lm v = eulerEntropy Lp u ∧ eulerFisher Lm v = eulerFisher Lp u ∧
      eulerMean Lm v (e0_STR02955 (polynomialRangeFeature (h, s))) =
        eulerMean Lp u (e0_STR02955 (polynomialRangeFeature (h, s))) ∧
      eulerMean Lm v (polynomialRangeGenerator (h, s)) =
        eulerMean Lp u (polynomialRangeGenerator (h, s)) ∧
      eulerMean Lm v (polynomialRangeGradientSq (h, s)) =
        eulerMean Lp u (polynomialRangeGradientSq (h, s)) := by
  have hfirst (t : ℝ) : deriv v.val (-t) = -deriv u.val t := by
    have he : (fun y : ℝ => v.val (-y)) = u.val := funext hu
    have hd := deriv_comp_neg (f := v.val) (x := t)
    rw [he] at hd
    linarith only [hd]
  have hEu := expectation_reflection h s u v hu (e0_STR02955 v) (e0_STR02955 u) hu
  have hZ := tilted_partition h s u v hu
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold eulerEntropy
    rw [hEu, hZ]
  · unfold eulerFisher
    congr 1
    apply expectation_reflection h s u v hu
    intro t
    change deriv v.val (-t) * deriv v.val (-t) = deriv u.val t * deriv u.val t
    rw [hfirst]
    ring
  · exact expectation_reflection h s u v hu _ _ (polynomialRangeFeature_reflection h s)
  · exact expectation_reflection h s u v hu _ _ (polynomialRangeGenerator_reflection h s)
  · exact expectation_reflection h s u v hu _ _ (polynomialRangeGradientSq_reflection h s)

/-- Exact value symmetry of the full nonlocal deficit; its true m*A and m²*J
terms are retained. No root parity, eigenfunction or desired quartic jet is assumed. -/
theorem polynomialRangeDeficit_reflection (h s r : ℝ) (u v : PeriodicC2_STR02969)
    (hu : ∀ t, v.val (-t) = u.val t) :
    polynomialRangeDeficit (h, s) r v = polynomialRangeDeficit (h, s) r u := by
  obtain ⟨hH, hI, hm, hA, hJ⟩ := polynomialRange_moments_reflection h s u v hu
  unfold polynomialRangeDeficit polynomialRangeGap
  dsimp only
  rw [hH, hI, hm, hA, hJ]

end DGPS.Examples.PolynomialSpecies
