import DGPS.Examples.PolynomialSpeciesProfilePoincare

/-! The strict one-sided cosine margin near the TWO actual limiting
coefficient points. This support theorem retains the supplied graph and the
true normalized profile. Actual every-minimizer capture is discharged by its
separate producer before the final original-domain factory is assembled. -/

noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ContDiff ENNReal
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization
open DGPS.Circle.FirstClusterPerturbation

namespace DGPS.Examples.PolynomialSpecies

private def cosineCoefficient (A : ℝ) : ℝ := (1 + 3 * A + 2 * A ^ 2) / 6
private def amplitudeCenter : ℝ := -(1 + Real.sqrt 2) / 2
private def rateCenter : ℝ := (3 - Real.sqrt 2) / 24
private def coefficientMargin : ℝ := (Real.sqrt 2 - 1) / 24

private theorem coefficientMargin_pos : 0 < coefficientMargin := by
  have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  dsimp only [coefficientMargin]
  nlinarith

private theorem center_margin :
    rateCenter - cosineCoefficient amplitudeCenter = coefficientMargin := by
  have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  dsimp only [rateCenter, cosineCoefficient, amplitudeCenter, coefficientMargin]
  nlinarith only [hs]

/-- A true open coefficient neighborhood suffices for the strict cosine
margin. B may lie near either sign: the one-sided coefficient is independent
of B. No spectral or actual-optimizer assertion is a premise. -/
theorem polynomial_cosine_coefficient_margin :
    ∃ η : ℝ, 0 < η ∧ ∀ A α : ℝ,
      |A - (-(1 + Real.sqrt 2) / 2)| < η →
      |α - (3 - Real.sqrt 2) / 24| < η →
      (Real.sqrt 2 - 1) / 48 ≤ α - (1 + 3 * A + 2 * A ^ 2) / 6 := by
  let F : (ℝ × ℝ) → ℝ := fun p => p.2 - cosineCoefficient p.1
  have hc : Continuous F := by dsimp only [F, cosineCoefficient]; fun_prop
  have hval : F (amplitudeCenter, rateCenter) = coefficientMargin := center_margin
  have hev : ∀ᶠ p in 𝓝 (amplitudeCenter, rateCenter), coefficientMargin / 2 < F p :=
    hc.continuousAt.eventually (lt_mem_nhds (show coefficientMargin / 2 < F (amplitudeCenter, rateCenter) by rw [hval]; linarith [coefficientMargin_pos]))
  obtain ⟨η, hη, hb⟩ := Metric.mem_nhds_iff.1 hev
  refine ⟨η, hη, fun A α hA hα => ?_⟩
  have hp : (A, α) ∈ Metric.ball (amplitudeCenter, rateCenter) η := by
    change dist (A, α) (amplitudeCenter, rateCenter) < η
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_lt hA hα
  have hlt : coefficientMargin / 2 < F (A, α) := hb hp
  have hh := hlt.le
  change coefficientMargin / 2 ≤ α - cosineCoefficient A at hh
  convert hh using 1 <;> dsimp only [coefficientMargin, cosineCoefficient] <;> ring

/-- The actual SAME-graph C2 profile supplies a quantitative native Poincare
margin below its scaled rate, uniformly in a bounded box. Only the explicit
coefficient neighborhood and the factual smooth normalized profile enter this
support interface. They are not hypotheses of the eventual every-minimizer
factory, which uses actual capture and native regularity. -/
theorem polynomial_same_graph_profile_poincare_margin
    {U : Set PolynomialRangeParameters} {ψ : PolynomialRangeParameters → E_STR02969}
    (hU : IsOpen U) (h0U : (0 : PolynomialRangeParameters) ∈ U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0)
    (hgraph : ∀ p ∈ U, polynomialRangeMap (p, ψ p) = 0)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (M : ℝ) (hM : 1 ≤ M) :
    ∃ η δ c : ℝ, 0 < η ∧ 0 < δ ∧ 0 < c ∧ ∀ A B σ α h : ℝ,
      |A| ≤ M → |B| ≤ M → |σ| ≤ M → |α| ≤ M → 0 ≤ h → h ≤ δ →
      |A - (-(1 + Real.sqrt 2) / 2)| < η →
      |α - (3 - Real.sqrt 2) / 24| < η →
      ∀ (P : BoundedPositiveReference 1) (ell : AngCircle → ℝ), IsSmoothAngular ell →
      (∀ t : ℝ, ell (t : AngCircle) =
        (polynomialRangeLogWeight (h, h ^ 4 * σ) +
          polynomialGapLift ψ ((h, h ^ 4 * σ), h ^ 2 * α) (h * A, h * B)).val t) →
      P.density = angularGibbs_EX009 ell →
      poincareRate ⟨P.measure, P.isProbabilityMeasure⟩ ≤
        ENNReal.ofReal (a0 * (1 + h ^ 2 * α) - c * h ^ 2) := by
  obtain ⟨η, hη, hgap⟩ := polynomial_cosine_coefficient_margin
  obtain ⟨δP, C, hδP, hC, hPC⟩ := polynomial_same_graph_profile_poincare_upper
    hU h0U hψ hψ0 hgraph hzero hfirst M hM
  let δ := min δP (coefficientMargin / (4 * C))
  let c := a0 * coefficientMargin / 4
  have hδ : 0 < δ := lt_min hδP (div_pos coefficientMargin_pos (by positivity))
  have hc : 0 < c := by dsimp only [c]; positivity [a0_pos, coefficientMargin_pos]
  refine ⟨η, δ, c, hη, hδ, hc,
    fun A B σ α h hA hB hσ hα hh hsmall hnearA hnearα P ell hell hlift hP => ?_⟩
  have hupper := hPC A B σ α h hA hB hσ hα hh
    (hsmall.trans (min_le_left _ _)) P ell hell hlift hP
  have hcoeff : coefficientMargin / 2 ≤ α - cosineCoefficient A := by
    convert hgap A α hnearA hnearα using 1 <;>
      dsimp only [coefficientMargin, cosineCoefficient] <;> ring
  have hCh : C * h ≤ coefficientMargin / 4 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp
      (hsmall.trans (min_le_right _ _))
    nlinarith only [ht]
  apply hupper.trans
  apply ENNReal.ofReal_le_ofReal
  have hcoeff2 := mul_le_mul_of_nonneg_left hcoeff (sq_nonneg h)
  have hCh2 := mul_le_mul_of_nonneg_right hCh (sq_nonneg h)
  have hscaledCoeff := mul_le_mul_of_nonneg_left hcoeff2 a0_pos.le
  have hscaledError := mul_le_mul_of_nonneg_left hCh2 a0_pos.le
  dsimp only [c, cosineCoefficient] at *
  nlinarith only [hscaledCoeff, hscaledError]

end DGPS.Examples.PolynomialSpecies
