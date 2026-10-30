import DGPS.Examples.PolynomialRootVariations
import DGPS.Examples.PolynomialMinimizerDeficit
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Genuine original-H1 stationarity for the actual polynomial model. The
reference and all three feature moments are retained at the same physical
field. No Euler equation, regularity, or positive entropy is an input. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.PositiveRankOne DGPS.Examples.ThreeSpeciesCircle

namespace DGPS.Examples.PolynomialSpecies

/-- The actual scalar deficit expanded in the true relative Fisher, entropy,
and three moving-reference feature moments. -/
def polynomialVariationalDeficit (h r : ℝ) (ρ : AbsoluteDensity 1) : ℝ :=
  let M := polynomialRankOne h
  let m := ∫ x, M.φ x ∂(densityMeasure ρ : Measure (Torus 1))
  let a := ∫ x, M.Aq x ∂(densityMeasure ρ : Measure (Torus 1))
  let j := ∫ x, M.dφ x ^ 2 ∂(densityMeasure ρ : Measure (Torus 1))
  (ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) M.ref).toReal -
    2 * r * (relativeEntropy (densityMeasure ρ : Measure (Torus 1)) M.ref.measure).toReal +
    2 * eta * m * a - r * eta * m ^ 2 + eta ^ 2 * m ^ 2 * j

theorem polynomialVariationalDeficit_eq (h r : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (ρ : AbsoluteDensity 1) :
    polynomialVariationalDeficit h r ρ =
      (scalarDissipation (canonical_elementary_polynomial_model h) b ρ).toReal -
        2 * r * (scalarGap (canonical_elementary_polynomial_model h) ρ : ℝ) := by
  obtain ⟨hg, _, _, hd⟩ := polynomial_family_gap_and_dissipation h b (SpeciesFamily.single ρ)
  have hg' : (scalarGap (canonical_elementary_polynomial_model h) ρ : ℝ) =
      (relativeEntropy (densityMeasure ρ : Measure (Torus 1)) (polynomialRankOne h).ref.measure).toReal +
        eta / 2 * (∫ x, (polynomialRankOne h).φ x ∂(densityMeasure ρ : Measure (Torus 1))) ^ 2 := by
    simpa only [speciesGap_single, densityMeasure_barycenter_single, sum_single_count,
      SpeciesFamily.single_weight, SpeciesFamily.single_density, one_mul,
      polynomialRankOne_reference] using hg
  have hd' : (scalarDissipation (canonical_elementary_polynomial_model h) b ρ).toReal =
      (ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) (polynomialRankOne h).ref).toReal +
        2 * eta * (∫ x, (polynomialRankOne h).φ x ∂(densityMeasure ρ : Measure (Torus 1))) *
          (∫ x, (polynomialRankOne h).Aq x ∂(densityMeasure ρ : Measure (Torus 1))) +
        eta ^ 2 * (∫ x, (polynomialRankOne h).φ x ∂(densityMeasure ρ : Measure (Torus 1))) ^ 2 *
          (∫ x, (polynomialRankOne h).dφ x ^ 2 ∂(densityMeasure ρ : Measure (Torus 1))) := by
    simpa only [speciesDissipation_single, densityMeasure_barycenter_single, sum_single_count,
      SpeciesFamily.single_weight, SpeciesFamily.single_density, one_mul] using hd
  rw [hg', hd']
  unfold polynomialVariationalDeficit
  ring

private theorem variation_measure_zero (ρ : AbsoluteDensity 1) {φ : Torus 1 → ℝ}
    {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    densityMeasure (absoluteRootVariation ρ hφ 0) = densityMeasure ρ := by
  have hn : 0 < ∫ x, (ρ.sqrt x + (0 : ℝ) * φ x) ^ 2 ∂haar 1 := by
    simpa only [zero_mul, add_zero, ρ.mass_one] using (one_pos : (0 : ℝ) < 1)
  apply Subtype.ext
  change (haar 1).withDensity (fun x => ENNReal.ofReal ((absoluteRootVariation ρ hφ 0).density x)) =
    (haar 1).withDensity (fun x => ENNReal.ofReal (ρ.density x))
  apply congrArg ((haar 1).withDensity)
  funext x
  unfold absoluteRootVariation
  rw [dif_pos hn]
  dsimp only [normAbs, AbsoluteDensity.density]
  rw [div_pow, sq_abs, Real.sq_sqrt hn.le]
  simp only [zero_mul, add_zero, ρ.mass_one, div_one]

/-- Every actual positive-gap minimizer is stationary along EVERY normalized
original-H1 root variation. The absolute value in the path is retained, so the
competitors and the minimizer may have zeros. -/
theorem polynomial_minimizer_deficit_hasDerivAt_zero (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (ρ : AbsoluteDensity 1)
    (hG : 0 < scalarGap (canonical_elementary_polynomial_model h) ρ)
    (hmin : scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
      scalarRate (canonical_elementary_polynomial_model h) b)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    HasDerivAt (fun t : ℝ => polynomialVariationalDeficit h
      (scalarRate (canonical_elementary_polynomial_model h) b).toReal (absoluteRootVariation ρ hφ t)) 0 0 := by
  let M := polynomialRankOne h
  let r := (scalarRate (canonical_elementary_polynomial_model h) b).toReal
  let f := fun t : ℝ => polynomialVariationalDeficit h r (absoluteRootVariation ρ hφ t)
  have hi := polynomial_rootVariation_fisher_hasDerivAt h ρ hφ
  have hh := polynomial_rootVariation_entropy_hasDerivAt h ρ hφ
  have hm := absoluteRootVariation_moment_hasDerivAt ρ hφ M.φ M.φ_cont
  have ha := absoluteRootVariation_moment_hasDerivAt ρ hφ M.Aq M.Aq_cont
  have hj := absoluteRootVariation_moment_hasDerivAt ρ hφ (fun x => M.dφ x ^ 2) (M.dφ_cont.pow 2)
  have hd : DifferentiableAt ℝ f 0 := by
    exact (((hi.differentiableAt.sub (hh.differentiableAt.const_mul (2 * r))).add
      ((hm.differentiableAt.const_mul (2 * eta)).mul ha.differentiableAt)).sub
        ((hm.differentiableAt.pow 2).const_mul (r * eta))).add
          (((hm.differentiableAt.pow 2).const_mul (eta ^ 2)).mul hj.differentiableAt)
  obtain ⟨hz, hnon⟩ := polynomial_minimizer_deficit_zero_and_nonnegative h b ρ hG hmin
  have hz' : polynomialVariationalDeficit h r ρ = 0 := by
    rw [polynomialVariationalDeficit_eq h r b ρ]
    exact hz
  have hf0 : f 0 = 0 := by
    simpa only [f, polynomialVariationalDeficit, variation_measure_zero] using hz'
  have hloc : IsLocalMin f 0 := by
    apply Eventually.of_forall
    intro t
    rw [hf0]
    rw [show f t = polynomialVariationalDeficit h r (absoluteRootVariation ρ hφ t) from rfl,
      polynomialVariationalDeficit_eq h r b]
    exact hnon _
  have he := hloc.deriv_eq_zero
  simpa only [he] using hd.hasDerivAt

end DGPS.Examples.PolynomialSpecies
