import DGPS.Examples.PolynomialSpeciesRangeDeficit
import DGPS.Examples.PolynomialSpeciesHalfTurnGenerator

/-! Exact half-turn covariance of the independent-reference normalized moments
and ACTUAL nonlocal deficit. Normalizing constants are transported explicitly. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem partition_shift (f g : PeriodicC2_STR02969)
    (he : ∀ t, f.val (t + Real.pi) = g.val t) :
    Z_STR02954 (0, e0_STR02955 f) = Z_STR02954 (0, e0_STR02955 g) := by
  let F := fun t : ℝ => Real.exp (f.val t)
  have hp : Function.Periodic F (2 * Real.pi) := by
    intro t
    dsimp only [F]
    rw [f.isC2.1 t]
  rw [Z_eq_meanT_STR02954, Z_eq_meanT_STR02954]
  simp only [zero_mul, zero_add, e0_val_STR02955]
  calc
    meanT_STR02901 F = meanT_STR02901 (pb_STR02916 1 Real.pi F) :=
      (meanT_pb_STR02916 (Or.inl rfl) Real.pi hp).symm
    _ = _ := by congr 1; funext t; simp only [pb_STR02916, one_mul, F, he]

private theorem tilted_partition (h s : ℝ) (u v : PeriodicC2_STR02969)
    (hu : ∀ t, v.val (t + Real.pi) = u.val t) :
    Z_STR02954 (0, e0_STR02955 (polynomialRangeLogWeight (-h, s)) + e0_STR02955 v) =
      Z_STR02954 (0, e0_STR02955 (polynomialRangeLogWeight (h, s)) + e0_STR02955 u) := by
  rw [← map_add, ← map_add]
  apply partition_shift
  intro t
  simp only [PeriodicC2_STR02969.val_add, Pi.add_apply, polynomialRangeLogWeight_half_turn, hu]

private theorem density_value (L : PeriodicC2_STR02969) (u : PeriodicC2_STR02969) (t : ℝ) :
    (eulerDensity (e0_STR02955 L) u).val t = Real.exp (L.val t + u.val t) /
      Z_STR02954 (0, e0_STR02955 L + e0_STR02955 u) := by
  rw [eulerDensity, rho_val_STR02954]
  simp only [rhoT_STR02901, zero_mul, zero_add, PeriodicHolder_STR02968.val_add,
    Pi.add_apply, e0_val_STR02955, Z_eq_meanT_STR02954]

/-- The actual normalized chart densities transform with their references. -/
theorem polynomialRangeDensity_half_turn (h s : ℝ) (u v : PeriodicC2_STR02969)
    (hu : ∀ t, v.val (t + Real.pi) = u.val t) (t : ℝ) :
    (eulerDensity (e0_STR02955 (polynomialRangeLogWeight (-h, s))) v).val (t + Real.pi) =
      (eulerDensity (e0_STR02955 (polynomialRangeLogWeight (h, s))) u).val t := by
  rw [density_value, density_value, polynomialRangeLogWeight_half_turn, hu, tilted_partition h s u v hu]

private theorem expectation_shift (h s : ℝ) (u v : PeriodicC2_STR02969)
    (hu : ∀ t, v.val (t + Real.pi) = u.val t) (f g : PeriodicHolder_STR02968)
    (hf : ∀ t, f.val (t + Real.pi) = g.val t) :
    eulerMean (e0_STR02955 (polynomialRangeLogWeight (-h, s))) v f =
      eulerMean (e0_STR02955 (polynomialRangeLogWeight (h, s))) u g := by
  let R := eulerDensity (e0_STR02955 (polynomialRangeLogWeight (-h, s))) v
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
    meanT_STR02901 F = meanT_STR02901 (pb_STR02916 1 Real.pi F) :=
      (meanT_pb_STR02916 (Or.inl rfl) Real.pi hp).symm
    _ = _ := by
      congr 1
      funext t
      simp only [pb_STR02916, one_mul, F, R, hf, polynomialRangeDensity_half_turn h s u v hu]

/-- Every changing scalar in the ACTUAL deficit transforms on the same chart pair.
The chart relation is only a concrete spatial pullback, not an Euler/optimizer premise. -/
theorem polynomialRange_moments_half_turn (h s : ℝ) (u v : PeriodicC2_STR02969)
    (hu : ∀ t, v.val (t + Real.pi) = u.val t) :
    let Lm := e0_STR02955 (polynomialRangeLogWeight (-h, s))
    let Lp := e0_STR02955 (polynomialRangeLogWeight (h, s))
    eulerEntropy Lm v = eulerEntropy Lp u ∧ eulerFisher Lm v = eulerFisher Lp u ∧
      eulerMean Lm v (e0_STR02955 (polynomialRangeFeature (-h, s))) =
        eulerMean Lp u (e0_STR02955 (polynomialRangeFeature (h, s))) ∧
      eulerMean Lm v (polynomialRangeGenerator (-h, s)) =
        eulerMean Lp u (polynomialRangeGenerator (h, s)) ∧
      eulerMean Lm v (polynomialRangeGradientSq (-h, s)) =
        eulerMean Lp u (polynomialRangeGradientSq (h, s)) := by
  have hfirst (t : ℝ) : deriv v.val (t + Real.pi) = deriv u.val t := by
    have he : (fun y : ℝ => v.val (y + Real.pi)) = u.val := funext hu
    have hd := deriv_comp_add_const (f := v.val) Real.pi t
    rw [he] at hd
    exact hd.symm
  have hEu := expectation_shift h s u v hu (e0_STR02955 v) (e0_STR02955 u) hu
  have hZ := tilted_partition h s u v hu
  have hZ0 := partition_shift (polynomialRangeLogWeight (-h, s)) (polynomialRangeLogWeight (h, s))
    (polynomialRangeLogWeight_half_turn h s)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold eulerEntropy
    rw [hEu, hZ, hZ0]
  · unfold eulerFisher
    congr 1
    apply expectation_shift h s u v hu
    intro t
    change deriv v.val (t + Real.pi) * deriv v.val (t + Real.pi) = deriv u.val t * deriv u.val t
    rw [hfirst]
  · exact expectation_shift h s u v hu _ _ (polynomialRangeFeature_half_turn h s)
  · exact expectation_shift h s u v hu _ _ (polynomialRangeGenerator_half_turn h s)
  · exact expectation_shift h s u v hu _ _ (polynomialRangeGradientSq_half_turn h s)

/-- Exact value symmetry of the full nonlocal deficit; its true m*A and m²*J
terms are retained. No root parity, eigenfunction or desired quartic jet is assumed. -/
theorem polynomialRangeDeficit_half_turn (h s r : ℝ) (u v : PeriodicC2_STR02969)
    (hu : ∀ t, v.val (t + Real.pi) = u.val t) :
    polynomialRangeDeficit (-h, s) r v = polynomialRangeDeficit (h, s) r u := by
  obtain ⟨hH, hI, hm, hA, hJ⟩ := polynomialRange_moments_half_turn h s u v hu
  unfold polynomialRangeDeficit polynomialRangeGap
  dsimp only
  rw [hH, hI, hm, hA, hJ]

end DGPS.Examples.PolynomialSpecies
