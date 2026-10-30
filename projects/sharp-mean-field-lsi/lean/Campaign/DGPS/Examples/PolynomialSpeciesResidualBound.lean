import DGPS.Examples.PolynomialSpeciesDescentBridge
import DGPS.Variational.LocalGaussianEndpoint
import DGPS.Structural.PositivityFromResidual

/-! Centered residual control for the genuine all-family polynomial dissipation.
The analytic input is a pointwise bound on the actual generator residual, not an
exact eigenfunction equation or a species-rate inequality. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BoundedContinuousFunction

namespace DGPS.Examples.PolynomialSpecies
open DGPS.PositiveRankOne DGPS.Structural

private theorem generator_mean_zero (M : RankOneModel) :
    ∫ x, M.Aq x ∂M.ref.measure = 0 := by
  have hi : Integrable (fun x => M.q x * coordPartial 0 M.dφ x) (haar 1) :=
    (M.q_cont.mul M.ddφ_cont).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (fun x => coordPartial 0 M.q x * M.dφ x) (haar 1) :=
    ((M.q_smooth.continuous_coordPartial 0).mul M.dφ_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb := integral_mul_coordPartial_of_smooth M.q_smooth M.dφ_smooth (0 : Fin 1)
  have he : ∀ x, M.q x * M.Aq x =
      -(M.q x * coordPartial 0 M.dφ x) - coordPartial 0 M.q x * M.dφ x := by
    intro x
    rw [RankOneModel.Aq, LocalGaussianEndpoint.dlogq_eq]
    change M.q x * (-coordPartial 0 M.dφ x -
      (M.q x)⁻¹ * coordPartial 0 M.q x * M.dφ x) = _
    field_simp [(M.q_pos x).ne']
  rw [LocalGaussianEndpoint.integral_ref_eq]
  simp_rw [he]
  calc (∫ x, -(M.q x * coordPartial 0 M.dφ x) - coordPartial 0 M.q x * M.dφ x ∂haar 1)
      = (∫ x, -(M.q x * coordPartial 0 M.dφ x) ∂haar 1) -
        ∫ x, coordPartial 0 M.q x * M.dφ x ∂haar 1 :=
      integral_sub (f := fun x => -(M.q x * coordPartial 0 M.dφ x))
        (g := fun x => coordPartial 0 M.q x * M.dφ x) hi.neg hj
    _ = -(∫ x, M.q x * coordPartial 0 M.dφ x ∂haar 1) -
        ∫ x, coordPartial 0 M.q x * M.dφ x ∂haar 1 := by
      congr 1
      exact integral_neg _
    _ = 0 := by rw [hb]; ring

/-- The actual generator residual is centered for every spectral comparison number. -/
theorem polynomial_residual_centered (h ell : ℝ) :
    ∫ x, ((polynomialRankOne h).Aq x - ell * (polynomialRankOne h).φ x)
      ∂(polynomialRankOne h).ref.measure = 0 := by
  let M := polynomialRankOne h
  have hφ : ∫ x, M.φ x ∂M.ref.measure = 0 := by
    rw [LocalGaussianEndpoint.integral_ref_eq]
    exact (integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)).trans M.φ_centered
  rw [integral_sub (M.Aq_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((M.φ_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul ell),
    integral_const_mul, generator_mean_zero, hφ]
  ring

/-- Centered Pinsker controls the residual uniformly over every finite weighted family. -/
theorem polynomial_residual_family_pinsker (h ell ε : ℝ) (hε : 0 ≤ ε)
    (hR : ∀ x, |(polynomialRankOne h).Aq x - ell * (polynomialRankOne h).φ x| ≤ ε)
    (F : SpeciesFamily 1) :
    (∫ x, ((polynomialRankOne h).Aq x - ell * (polynomialRankOne h).φ x)
      ∂(densityMeasure (barycenter F) : Measure (Torus 1))) ^ 2 ≤
      2 * ε ^ 2 * ∑ s, F.weight s *
        (relativeEntropy (densityMeasure (F.density s) : Measure (Torus 1))
          (polynomialRankOne h).ref.measure).toReal := by
  let M := polynomialRankOne h
  let ν := densityMeasure (barycenter F)
  let R : Torus 1 →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => M.Aq x - ell * M.φ x) (M.Aq_cont.sub (continuous_const.mul M.φ_cont)) ε
      (fun x => by simpa only [Real.norm_eq_abs] using hR x)
  have hnorm : ‖R‖ ≤ ε := (BoundedContinuousFunction.norm_le hε).2 fun x => by
    change |M.Aq x - ell * M.φ x| ≤ ε
    exact hR x
  have hTV := abs_integral_sub_le_fullVariation (ν : Measure (Torus 1)) M.ref.measure R
  have hT0 := fullVariation_nonneg (ν : Measure (Torus 1)) M.ref.measure
  have hz : ∫ x, R x ∂M.ref.measure = 0 := polynomial_residual_centered h ell
  rw [hz, sub_zero] at hTV
  have hbound : |∫ x, R x ∂(ν : Measure (Torus 1))| ≤
      ε * fullVariation (ν : Measure (Torus 1)) M.ref.measure :=
    hTV.trans (mul_le_mul_of_nonneg_right hnorm hT0)
  have hs := pow_le_pow_left₀ (abs_nonneg _) hbound 2
  rw [sq_abs, mul_pow] at hs
  have hp := pinsker_fullVariation_real (ν : Measure (Torus 1)) M.ref.measure
    (relativeEntropy_reference M.ref (barycenter F)).1
  have hH := relativeEntropy_barycenter_le_sum F M.ref
  have hh : fullVariation (ν : Measure (Torus 1)) M.ref.measure ^ 2 ≤
      2 * ∑ s, F.weight s * (relativeEntropy
        (densityMeasure (F.density s) : Measure (Torus 1)) M.ref.measure).toReal := by linarith
  exact hs.trans (by nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg ε)])

private theorem residual_square_completion {H I m E S D G η a ell r ε : ℝ}
    (hη : 0 ≤ η) (hS : 0 ≤ S) (hell : 0 < ell) (hrell : r ≤ ell)
    (hε : E ^ 2 ≤ 2 * ε ^ 2 * H) (hI : 2 * a * H ≤ I)
    (hD : D = I + 2 * η * m * (ell * m + E) + η ^ 2 * m ^ 2 * S)
    (hG : G = H + η / 2 * m ^ 2) (hr : a - r = η * ε ^ 2 / ell) :
    2 * r * G ≤ D := by
  have hε' := mul_le_mul_of_nonneg_left hε hη
  have hq := mul_nonneg hη (sq_nonneg (ell * m + E))
  have hrem := mul_nonneg hη (mul_nonneg (sub_nonneg.mpr hrell) (sq_nonneg m))
  have hs := mul_nonneg (mul_nonneg (sq_nonneg η) (sq_nonneg m)) hS
  have hI' := mul_le_mul_of_nonneg_left hI hell.le
  have hrem' := mul_nonneg hell.le hrem
  have hs' := mul_nonneg hell.le hs
  have hr' : ell * (a - r) = η * ε ^ 2 := by
    rw [hr]
    field_simp
  have hrH : ell * (a - r) * H = η * ε ^ 2 * H := by rw [hr']
  have hh : 0 ≤ ell * (D - 2 * r * G) := by
    rw [hD, hG]
    nlinarith [hrH]
  have := nonneg_of_mul_nonneg_right hh hell
  linarith

/-- A genuine pointwise generator-residual bound gives an actual all-species lower rate.
No exact eigenfunction relation is required. All family counts and positive weights are allowed. -/
theorem polynomial_speciesRate_ge_of_residual_bound (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) {a ell ε : ℝ}
    (ha : 0 ≤ a) (hell : 0 < ell) (haell : a ≤ ell) (hε : 0 ≤ ε)
    (haLS : ENNReal.ofReal a ≤ ordinaryLSRate (polynomialRankOne h).ref)
    (hR : ∀ x, |(polynomialRankOne h).Aq x - ell * (polynomialRankOne h).φ x| ≤ ε)
    (hr : 0 ≤ a - eta * ε ^ 2 / ell) :
    ENNReal.ofReal (a - eta * ε ^ 2 / ell) ≤
      speciesRate (canonical_elementary_polynomial_model h) b := by
  let M := polynomialRankOne h
  let r := a - eta * ε ^ 2 / ell
  unfold speciesRate
  refine le_iInf fun F => ?_
  obtain ⟨hG, hIne, hDne, hD⟩ := polynomial_family_gap_and_dissipation h b F.1
  let H := ∑ s, F.1.weight s * (relativeEntropy
    (densityMeasure (F.1.density s) : Measure (Torus 1)) M.ref.measure).toReal
  let I := ∑ s, F.1.weight s * (ordinaryRelativeFisher
    (densityMeasure (F.1.density s) : Measure (Torus 1)) M.ref).toReal
  let m := ∫ x, M.φ x ∂(densityMeasure (barycenter F.1) : Measure (Torus 1))
  let E := ∫ x, (M.Aq x - ell * M.φ x) ∂(densityMeasure (barycenter F.1) : Measure (Torus 1))
  have hI : 2 * a * H ≤ I := by
    dsimp only [H, I]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hne := (relativeEntropy_reference M.ref (F.1.density s)).1
    have hac : (densityMeasure (F.1.density s) : Measure (Torus 1)) ≪ M.ref.measure := by
      by_contra hn
      exact hne (relativeEntropy_of_not_absolutelyContinuous hn)
    have hLS := two_mul_lsRate_mul_relativeEntropy_le M.ref _ hac
    have hlow : 2 * ENNReal.ofReal a * (relativeEntropy
        (densityMeasure (F.1.density s) : Measure (Torus 1)) M.ref.measure) ≤
        ordinaryRelativeFisher (densityMeasure (F.1.density s) : Measure (Torus 1)) M.ref :=
      (mul_le_mul' (mul_le_mul' le_rfl haLS) le_rfl).trans hLS
    have ht := ENNReal.toReal_mono (hIne s) hlow
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha] at ht
    norm_num only [ENNReal.toReal_ofNat] at ht
    have hh := mul_le_mul_of_nonneg_left ht (F.1.weight_nonneg s)
    nlinarith
  have hB : (∫ x, M.Aq x ∂(densityMeasure (barycenter F.1) : Measure (Torus 1))) = ell * m + E := by
    dsimp only [m, E]
    rw [integral_sub (M.Aq_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((M.φ_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul ell),
      integral_const_mul]
    ring
  rw [hB] at hD
  have hG' : (speciesGap (canonical_elementary_polynomial_model h) F.1 : ℝ) = H + eta / 2 * m ^ 2 := by
    simpa only [M, H, m, polynomialRankOne_reference] using hG
  have hD' : (speciesDissipation (canonical_elementary_polynomial_model h) b F.1).toReal =
      I + 2 * eta * m * (ell * m + E) + eta ^ 2 * m ^ 2 *
        (∫ x, M.dφ x ^ 2 ∂(densityMeasure (barycenter F.1) : Measure (Torus 1))) := hD
  have hE := polynomial_residual_family_pinsker h ell ε hε hR F.1
  have hrell : r ≤ ell := (sub_le_self _
    (div_nonneg (mul_nonneg eta_pos.le (sq_nonneg ε)) hell.le)).trans haell
  have hreal := residual_square_completion eta_pos.le (integral_nonneg fun _ => sq_nonneg _)
    hell hrell hE hI hD' hG' (show a - r = eta * ε ^ 2 / ell by dsimp only [r]; ring)
  have h2G0 : (2 * (speciesGap (canonical_elementary_polynomial_model h) F.1 : ℝ≥0∞)) ≠ 0 := by
    have hpos : (0 : ℝ≥0∞) < speciesGap (canonical_elementary_polynomial_model h) F.1 := by exact_mod_cast F.2
    simp [hpos.ne']
  unfold speciesQuotient
  rw [ENNReal.le_div_iff_mul_le (Or.inl h2G0)
    (Or.inl (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top))]
  rw [← ENNReal.ofReal_toReal hDne]
  have hGco : 2 * (speciesGap (canonical_elementary_polynomial_model h) F.1 : ℝ≥0∞) =
      ENNReal.ofReal (2 * (speciesGap (canonical_elementary_polynomial_model h) F.1 : ℝ)) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_coe_nnreal]
    simp
  rw [hGco, ← ENNReal.ofReal_mul hr]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [hreal]

end DGPS.Examples.PolynomialSpecies
