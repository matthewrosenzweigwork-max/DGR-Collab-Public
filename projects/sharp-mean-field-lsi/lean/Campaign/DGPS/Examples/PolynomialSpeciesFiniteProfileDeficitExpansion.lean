import DGPS.Examples.PolynomialSpeciesFiniteProfileNonlocalBounds
import DGPS.Examples.PolynomialSpeciesMixedFiniteProfile

/-! Uniform actual fourth-order value on the concrete mixed finite profile.
Ordinary information, physical scaling and true nonlocal moments are combined
before any comparison with the implicit graph or selected reference root. -/

noncomputable section
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

/-- The actual independent-zero-tilt physical deficit on the concrete mixed
finite profile. One interval and error constant precede every bounded pair.
No graph/value expansion or nonlocal moment estimate is a premise. -/
theorem polynomialMixedFiniteProfile_deficit_expansion (M : ℝ) (hM : 1 ≤ M) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ a b h : ℝ,
      |a| ≤ M → |b| ≤ M → 0 ≤ h → h ≤ δ →
      |polynomialRangeDeficit (h, 0) DGPS.Circle.AngularNormalization.a0
          (polynomialMixedFiniteProfile a b h) -
        DGPS.Circle.AngularNormalization.a0 *
          ((a ^ 2 + b ^ 2) / 12 + a * (a ^ 2 + b ^ 2) / 12 +
            (a ^ 4 + b ^ 4) / 24) * h ^ 4| ≤ K * h ^ 5 := by
  let R := 4 * (M + 1) ^ 2
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hR : M ≤ R := by dsimp only [R]; nlinarith [sq_nonneg M]
  obtain ⟨δ, hδ, C, hC, hinfo⟩ := polynomialFiniteProfile_information_expansion_raw R
  obtain ⟨N, hN, hnloc⟩ := polynomialFiniteProfile_nonlocal_expansion M hM
  have ha0 := DGPS.Circle.AngularNormalization.a0_pos
  let K := 3 * DGPS.Circle.AngularNormalization.a0 * C + N
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨min δ 1, K, lt_min hδ zero_lt_one, hK, fun a b h ha hb hh hhδ => ?_⟩
  let c := -(a + a ^ 2 - b ^ 2) / 6
  let d := -(b * (1 + a)) / 6
  let q := Real.sqrt 2 * (a ^ 2 - b ^ 2) / 24
  let S := (a ^ 2 + b ^ 2) / 12 + a * (a ^ 2 + b ^ 2) / 12 + (a ^ 4 + b ^ 4) / 24
  let m := polynomialFiniteMoment a b h
  let A := polynomialFiniteGeneratorMoment a b h
  let J := polynomialFiniteGradientMoment a b h
  let T := 2 * eta * m * A + eta ^ 2 * m ^ 2 * J - DGPS.Circle.AngularNormalization.a0 * eta * m ^ 2
  have ha2 : a ^ 2 ≤ M ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg a) ha 2
  have hb2 : b ^ 2 ≤ M ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg b) hb 2
  have hc : |c| ≤ R := by
    dsimp only [c]
    rw [abs_div, abs_neg]
    have hs : |a + a ^ 2 - b ^ 2| ≤ M + M ^ 2 + M ^ 2 := by
      exact (abs_sub _ _).trans (add_le_add
        ((abs_add_le _ _).trans (by simpa only [abs_of_nonneg (sq_nonneg a)] using add_le_add ha ha2))
        (by simpa only [abs_of_nonneg (sq_nonneg b)] using hb2))
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    dsimp only [R]
    nlinarith
  have hd : |d| ≤ R := by
    dsimp only [d]
    rw [abs_div, abs_neg, abs_mul]
    have hs : |1 + a| ≤ 1 + M := (abs_add_le _ _).trans (by simpa only [abs_one] using add_le_add le_rfl ha)
    have hp := mul_le_mul hb hs (abs_nonneg _) hMp.le
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    dsimp only [R]
    nlinarith
  have hh1 : h ≤ 1 := hhδ.trans (min_le_right _ _)
  have hhδ' : |h| ≤ δ := by rw [abs_of_nonneg hh]; exact hhδ.trans (min_le_left _ _)
  obtain ⟨_, _, _, _, eI, eH⟩ := hinfo a b c d (ha.trans hR) (hb.trans hR) hc hd h hhδ'
  rw [polynomialFiniteI2_eq, polynomialFiniteI3_eq_zero, zero_mul, add_zero] at eI
  rw [polynomialFiniteH2_eq, polynomialFiniteH3_eq_zero, zero_mul, add_zero] at eH
  rw [abs_of_nonneg hh] at eI eH
  have eT := hnloc a b h ha hb hh hh1
  change |T - 3 * DGPS.Circle.AngularNormalization.a0 * q ^ 2 * h ^ 4| ≤ N * h ^ 5 at eT
  have hq : q = Real.sqrt 2 * (c / 2 + a / 12 + (a ^ 2 - b ^ 2) / 8) := by dsimp only [q, c]; ring
  have hq2 : 3 * q ^ 2 = 6 * (c / 2 + a / 12 + (a ^ 2 - b ^ 2) / 8) ^ 2 := by
    rw [hq, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hcoef : polynomialFiniteI4 a b c d - 2 * polynomialFiniteH4 a b c d + 3 * q ^ 2 = S := by
    have he := polynomialFiniteNonlocalFourth_mixed a b
    change polynomialFiniteI4 a b c d - 2 * polynomialFiniteH4 a b c d +
      6 * (c / 2 + a / 12 + (a ^ 2 - b ^ 2) / 8) ^ 2 = S at he
    rw [← hq2] at he
    exact he
  obtain ⟨hFI, hFH⟩ := polynomialMixedFiniteProfile_information a b h
  have hactual : polynomialRangeDeficit (h, 0) DGPS.Circle.AngularNormalization.a0
      (polynomialMixedFiniteProfile a b h) =
    DGPS.Circle.AngularNormalization.a0 * polynomialFiniteProfileFisher a b c d h -
      2 * DGPS.Circle.AngularNormalization.a0 * polynomialFiniteProfileEntropy a b c d h + T := by
    unfold polynomialRangeDeficit polynomialRangeGap
    dsimp only
    rw [hFI, hFH]
    dsimp only [T, m, A, J, polynomialFiniteMoment, polynomialFiniteGeneratorMoment, polynomialFiniteGradientMoment]
    ring
  have hid : polynomialRangeDeficit (h, 0) DGPS.Circle.AngularNormalization.a0
      (polynomialMixedFiniteProfile a b h) - DGPS.Circle.AngularNormalization.a0 * S * h ^ 4 =
    DGPS.Circle.AngularNormalization.a0 *
        (polynomialFiniteProfileFisher a b c d h - ((a ^ 2 + b ^ 2) / 2 * h ^ 2 + polynomialFiniteI4 a b c d * h ^ 4)) -
      2 * DGPS.Circle.AngularNormalization.a0 *
        (polynomialFiniteProfileEntropy a b c d h - ((a ^ 2 + b ^ 2) / 4 * h ^ 2 + polynomialFiniteH4 a b c d * h ^ 4)) +
      (T - 3 * DGPS.Circle.AngularNormalization.a0 * q ^ 2 * h ^ 4) := by
    rw [hactual]
    linear_combination (DGPS.Circle.AngularNormalization.a0 * h ^ 4) * hcoef
  change |polynomialRangeDeficit (h, 0) DGPS.Circle.AngularNormalization.a0
    (polynomialMixedFiniteProfile a b h) - DGPS.Circle.AngularNormalization.a0 * S * h ^ 4| ≤ _
  rw [hid]
  calc
    _ ≤ (DGPS.Circle.AngularNormalization.a0 *
        |polynomialFiniteProfileFisher a b c d h - ((a ^ 2 + b ^ 2) / 2 * h ^ 2 + polynomialFiniteI4 a b c d * h ^ 4)| +
      2 * DGPS.Circle.AngularNormalization.a0 *
        |polynomialFiniteProfileEntropy a b c d h - ((a ^ 2 + b ^ 2) / 4 * h ^ 2 + polynomialFiniteH4 a b c d * h ^ 4)|) +
      |T - 3 * DGPS.Circle.AngularNormalization.a0 * q ^ 2 * h ^ 4| := by
        apply (abs_add_le _ _).trans
        apply add_le_add ?_ le_rfl
        have he := abs_sub
          (DGPS.Circle.AngularNormalization.a0 * (polynomialFiniteProfileFisher a b c d h - ((a ^ 2 + b ^ 2) / 2 * h ^ 2 + polynomialFiniteI4 a b c d * h ^ 4)))
          (2 * DGPS.Circle.AngularNormalization.a0 * (polynomialFiniteProfileEntropy a b c d h - ((a ^ 2 + b ^ 2) / 4 * h ^ 2 + polynomialFiniteH4 a b c d * h ^ 4)))
        simpa only [abs_mul, abs_of_pos ha0, abs_of_pos (by positivity : 0 < 2 * DGPS.Circle.AngularNormalization.a0)] using he
    _ ≤ K * h ^ 5 := by
      have hi := mul_le_mul_of_nonneg_left eI ha0.le
      have he := mul_le_mul_of_nonneg_left eH (show 0 ≤ 2 * DGPS.Circle.AngularNormalization.a0 by positivity)
      dsimp only [K]
      nlinarith only [hi, he, eT]

end DGPS.Examples.PolynomialSpecies
