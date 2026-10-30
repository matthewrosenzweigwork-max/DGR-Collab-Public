import DGPS.Examples.PolynomialDeficitVariation

/-! Actual physical weak Euler equation for every full-original-domain scalar
minimizer of the polynomial model. The generator moment is retained as its
actual expectation; no eigenfunction relation is used away from the origin. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.PositiveRankOne DGPS.Examples.ThreeSpeciesCircle

namespace DGPS.Examples.PolynomialSpecies

def polynomialEulerCorrection (h r : ℝ) (ρ : AbsoluteDensity 1) (x : Torus 1) : ℝ :=
  let M := polynomialRankOne h
  let m := ∫ y, M.φ y ∂(densityMeasure ρ : Measure (Torus 1))
  let a := ∫ y, M.Aq y ∂(densityMeasure ρ : Measure (Torus 1))
  let j := ∫ y, M.dφ y ^ 2 ∂(densityMeasure ρ : Measure (Torus 1))
  2 * eta * (a + eta * m * j - r * m) * M.φ x +
    2 * eta * m * M.Aq x + eta ^ 2 * m ^ 2 * M.dφ x ^ 2

def polynomialEulerMultiplier (h r : ℝ) (ρ : AbsoluteDensity 1) : ℝ :=
  let M := polynomialRankOne h
  let m := ∫ y, M.φ y ∂(densityMeasure ρ : Measure (Torus 1))
  let a := ∫ y, M.Aq y ∂(densityMeasure ρ : Measure (Torus 1))
  let j := ∫ y, M.dφ y ^ 2 ∂(densityMeasure ρ : Measure (Torus 1))
  2 * eta * m * a - r * eta * m ^ 2 + 2 * eta ^ 2 * m ^ 2 * j

private theorem mixed_integrable (ρ : AbsoluteDensity 1) {φ : Torus 1 → ℝ}
    {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G)
    {g : Torus 1 → ℝ} (hg : Continuous g) :
    Integrable (fun x => ρ.sqrt x * φ x * g x) (haar 1) := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  exact integrable_mul_bdd_two hg.aestronglyMeasurable
    (fun x => by simpa only [Real.norm_eq_abs] using hB x (Set.mem_univ x))
    ρ.memLp_sqrt hφ.memLp

/-- The genuine weak equation holds for every original H1 test and every
actual positive-gap minimizer. Neither positivity of a stored root nor any
smoothness, Euler, or regularity conclusion is a premise. -/
theorem polynomial_scalarMinimizer_weakEuler (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (ρ : AbsoluteDensity 1)
    (hG : 0 < scalarGap (canonical_elementary_polynomial_model h) ρ)
    (hmin : scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
      scalarRate (canonical_elementary_polynomial_model h) b)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    let M := polynomialRankOne h
    let r := (scalarRate (canonical_elementary_polynomial_model h) b).toReal
    (∫ x, (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * M.dlogq x) *
        (2 * G x 0 - φ x * M.dlogq x) ∂haar 1) +
      (∫ x, ρ.sqrt x * φ x * polynomialEulerCorrection h r ρ x ∂haar 1) =
      2 * r * (∫ x, ρ.sqrt x * φ x * (Real.log (ρ.sqrt x ^ 2) - Real.log (M.q x)) ∂haar 1) +
        polynomialEulerMultiplier h r ρ * (∫ x, ρ.sqrt x * φ x ∂haar 1) := by
  let M := polynomialRankOne h
  let r := (scalarRate (canonical_elementary_polynomial_model h) b).toReal
  let z := ∫ x, ρ.sqrt x * φ x ∂haar 1
  let m := ∫ x, M.φ x ∂(densityMeasure ρ : Measure (Torus 1))
  let a := ∫ x, M.Aq x ∂(densityMeasure ρ : Measure (Torus 1))
  let j := ∫ x, M.dφ x ^ 2 ∂(densityMeasure ρ : Measure (Torus 1))
  let pm := ∫ x, ρ.sqrt x * φ x * M.φ x ∂haar 1
  let pa := ∫ x, ρ.sqrt x * φ x * M.Aq x ∂haar 1
  let pj := ∫ x, ρ.sqrt x * φ x * M.dφ x ^ 2 ∂haar 1
  let I := (ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) M.ref).toReal
  let H := (relativeEntropy (densityMeasure ρ : Measure (Torus 1)) M.ref.measure).toReal
  let A := ∫ x, (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * M.dlogq x) *
    (2 * G x 0 - φ x * M.dlogq x) ∂haar 1
  let R := ∫ x, ρ.sqrt x * φ x * (Real.log (ρ.sqrt x ^ 2) - Real.log (M.q x)) ∂haar 1
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  have hiLog := integrable_mul_mul_log hw hφ
  obtain ⟨B, hB⟩ := M.log_bound
  have hiQ := integrable_mul_bdd_two M.log_smooth.continuous_torus.aestronglyMeasurable
    hB ρ.memLp_sqrt hφ.memLp
  have hiZ : Integrable (fun x => ρ.sqrt x * φ x) (haar 1) :=
    ρ.memLp_sqrt.integrable_mul hφ.memLp
  have hEF : (∫ x, eulF' (ρ.sqrt x) * φ x ∂haar 1) =
      2 * (∫ x, ρ.sqrt x * φ x * Real.log (ρ.sqrt x ^ 2) ∂haar 1) + 2 * z := by
    have he : (fun x => eulF' (ρ.sqrt x) * φ x) = fun x =>
        2 * (ρ.sqrt x * φ x * Real.log (ρ.sqrt x ^ 2)) + 2 * (ρ.sqrt x * φ x) := by
      funext x
      unfold eulF'
      ring
    rw [he, integral_add (hiLog.const_mul 2) (hiZ.const_mul 2), integral_const_mul, integral_const_mul]
  have hR : R = (∫ x, ρ.sqrt x * φ x * Real.log (ρ.sqrt x ^ 2) ∂haar 1) -
      ∫ x, ρ.sqrt x * φ x * Real.log (M.q x) ∂haar 1 := by
    dsimp only [R]
    rw [← integral_sub hiLog hiQ]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have hI := polynomial_rootVariation_fisher_hasDerivAt h ρ hφ
  change HasDerivAt (fun t : ℝ => (ordinaryRelativeFisher
    (densityMeasure (absoluteRootVariation ρ hφ t) : Measure (Torus 1)) M.ref).toReal)
    (2 * A - 2 * z * I) 0 at hI
  have hHraw := polynomial_rootVariation_entropy_hasDerivAt h ρ hφ
  have hH : HasDerivAt (fun t : ℝ => (relativeEntropy
      (densityMeasure (absoluteRootVariation ρ hφ t) : Measure (Torus 1)) M.ref.measure).toReal)
      (2 * R - 2 * z * H) 0 := by
    convert hHraw using 1
    rw [hEF, hR]
    dsimp only [z, H]
    ring
  have hm := absoluteRootVariation_moment_hasDerivAt ρ hφ M.φ M.φ_cont
  have ha := absoluteRootVariation_moment_hasDerivAt ρ hφ M.Aq M.Aq_cont
  have hj := absoluteRootVariation_moment_hasDerivAt ρ hφ (fun x => M.dφ x ^ 2) (M.dφ_cont.pow 2)
  change HasDerivAt _ (2 * pm - 2 * z * m) 0 at hm
  change HasDerivAt _ (2 * pa - 2 * z * a) 0 at ha
  change HasDerivAt _ (2 * pj - 2 * z * j) 0 at hj
  have hF := (((hI.sub (hH.const_mul (2 * r))).add
    ((hm.const_mul (2 * eta)).mul ha)).sub ((hm.pow 2).const_mul (r * eta))).add
      (((hm.pow 2).const_mul (eta ^ 2)).mul hj)
  have hstation := polynomial_minimizer_deficit_hasDerivAt_zero h b ρ hG hmin hφ
  have hmeasure : densityMeasure (absoluteRootVariation ρ hφ 0) = densityMeasure ρ := by
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
  have hδ := hF.unique hstation
  simp only [Pi.pow_apply, hmeasure, Nat.cast_ofNat, Nat.reduceSub, pow_one] at hδ
  obtain ⟨hz, _⟩ := polynomial_minimizer_deficit_zero_and_nonnegative h b ρ hG hmin
  have hbase : I - 2 * r * H + 2 * eta * m * a - r * eta * m ^ 2 + eta ^ 2 * m ^ 2 * j = 0 := by
    change polynomialVariationalDeficit h r ρ = 0
    rw [polynomialVariationalDeficit_eq h r b]
    exact hz
  have hXi : (∫ x, ρ.sqrt x * φ x * polynomialEulerCorrection h r ρ x ∂haar 1) =
      2 * eta * (a + eta * m * j - r * m) * pm + 2 * eta * m * pa + eta ^ 2 * m ^ 2 * pj := by
    have hi1 := mixed_integrable ρ hφ M.φ_cont
    have hi2 := mixed_integrable ρ hφ M.Aq_cont
    have hi3 : Integrable (fun x => ρ.sqrt x * φ x * M.dφ x ^ 2) (haar 1) :=
      mixed_integrable ρ hφ (M.dφ_cont.pow 2)
    have he : (fun x => ρ.sqrt x * φ x * polynomialEulerCorrection h r ρ x) = fun x =>
        (2 * eta * (a + eta * m * j - r * m)) * (ρ.sqrt x * φ x * M.φ x) +
          (2 * eta * m) * (ρ.sqrt x * φ x * M.Aq x) +
            (eta ^ 2 * m ^ 2) * (ρ.sqrt x * φ x * M.dφ x ^ 2) := by
      funext x
      dsimp only [polynomialEulerCorrection, M, m, a, j]
      ring
    rw [he]
    have hi12 : Integrable (fun x =>
        (2 * eta * (a + eta * m * j - r * m)) * (ρ.sqrt x * φ x * M.φ x) +
        (2 * eta * m) * (ρ.sqrt x * φ x * M.Aq x)) (haar 1) :=
      (hi1.const_mul _).add (hi2.const_mul _)
    rw [integral_add hi12 (hi3.const_mul (eta ^ 2 * m ^ 2))]
    rw [integral_add (hi1.const_mul (2 * eta * (a + eta * m * j - r * m)))
      (hi2.const_mul (2 * eta * m))]
    simp only [integral_const_mul]
    rfl
  change A + (∫ x, ρ.sqrt x * φ x * polynomialEulerCorrection h r ρ x ∂haar 1) =
    2 * r * R + (2 * eta * m * a - r * eta * m ^ 2 + 2 * eta ^ 2 * m ^ 2 * j) * z
  rw [hXi]
  have halg : 2 * (A + 2 * eta * (a + eta * m * j - r * m) * pm + 2 * eta * m * pa +
        eta ^ 2 * m ^ 2 * pj - 2 * r * R -
        (2 * eta * m * a - r * eta * m ^ 2 + 2 * eta ^ 2 * m ^ 2 * j) * z) =
      ((2 * A - 2 * z * I) - 2 * r * (2 * R - 2 * z * H) +
        ((2 * eta) * (2 * pm - 2 * z * m) * a + (2 * eta) * m * (2 * pa - 2 * z * a)) -
        (r * eta) * (2 * m * (2 * pm - 2 * z * m)) +
        (eta ^ 2 * (2 * m * (2 * pm - 2 * z * m)) * j + eta ^ 2 * m ^ 2 * (2 * pj - 2 * z * j))) +
      2 * z * (I - 2 * r * H + 2 * eta * m * a - r * eta * m ^ 2 + eta ^ 2 * m ^ 2 * j) := by ring
  have hδ' : (2 * A - 2 * z * I) - 2 * r * (2 * R - 2 * z * H) +
      ((2 * eta) * (2 * pm - 2 * z * m) * a + (2 * eta) * m * (2 * pa - 2 * z * a)) -
      (r * eta) * (2 * m * (2 * pm - 2 * z * m)) +
      (eta ^ 2 * (2 * m * (2 * pm - 2 * z * m)) * j + eta ^ 2 * m ^ 2 * (2 * pj - 2 * z * j)) = 0 := by
    convert hδ using 1 <;> ring
  rw [hδ', hbase, mul_zero, add_zero] at halg
  linarith

end DGPS.Examples.PolynomialSpecies
