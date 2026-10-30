import DGPS.Examples.PolynomialSpeciesFiniteProfileMomentBounds
import DGPS.Examples.PolynomialSpeciesNonlocalFourth

/-! Genuine uniform fourth-order nonlocal value on the actual finite mixed
profile. The true generator residual remains an error expectation; no
pointwise nonzero-field eigenfunction relation is used. -/

noncomputable section
open DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

/-- Actual interaction contribution to D-2*a0*G, excluding the ordinary
Fisher/entropy terms. Constants precede all coefficients in the box. -/
theorem polynomialFiniteProfile_nonlocal_expansion (M : ℝ) (hM : 1 ≤ M) :
    ∃ K : ℝ, 0 < K ∧ ∀ a b h : ℝ, |a| ≤ M → |b| ≤ M → 0 ≤ h → h ≤ 1 →
      let m := polynomialFiniteMoment a b h
      let A := polynomialFiniteGeneratorMoment a b h
      let J := polynomialFiniteGradientMoment a b h
      |(2 * eta * m * A + eta ^ 2 * m ^ 2 * J -
          DGPS.Circle.AngularNormalization.a0 * eta * m ^ 2) -
        3 * DGPS.Circle.AngularNormalization.a0 *
          (Real.sqrt 2 * (a ^ 2 - b ^ 2) / 24) ^ 2 * h ^ 4| ≤ K * h ^ 5 := by
  obtain ⟨C, hC, hbound⟩ := polynomialFiniteProfile_moment_bounds M hM
  let P := |Real.sqrt 2| * (M ^ 2 + M ^ 2) / 24 + 1
  let B := P + C
  have hP : 0 < P := by dsimp only [P]; positivity
  have hB : 0 < B := add_pos hP hC
  have ha0 := DGPS.Circle.AngularNormalization.a0_pos
  have hη := eta_pos
  let K := 3 * DGPS.Circle.AngularNormalization.a0 * C * (B + P) +
    2 * eta * B * C + eta ^ 2 * B ^ 2 * C + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, fun a b h ha hb hh hh1 => ?_⟩
  dsimp only
  let m := polynomialFiniteMoment a b h
  let A := polynomialFiniteGeneratorMoment a b h
  let J := polynomialFiniteGradientMoment a b h
  let q := Real.sqrt 2 * (a ^ 2 - b ^ 2) / 24
  obtain ⟨em, eA, eJ⟩ := hbound a b h ha hb hh hh1
  have hq : |q| ≤ P := by
    have ha2 : a ^ 2 ≤ M ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg a) ha 2
    have hb2 : b ^ 2 ≤ M ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg b) hb 2
    have hd : |a ^ 2 - b ^ 2| ≤ M ^ 2 + M ^ 2 :=
      (abs_sub _ _).trans (by simpa only [abs_of_nonneg (sq_nonneg a), abs_of_nonneg (sq_nonneg b)] using add_le_add ha2 hb2)
    dsimp only [q, P]
    rw [abs_div, abs_mul]
    have hm := mul_le_mul_of_nonneg_left hd (abs_nonneg (Real.sqrt 2))
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 24)]
    linarith
  have h3 : h ^ 3 ≤ h ^ 2 := pow_le_pow_of_le_one hh hh1 (by norm_num)
  have hqh : |q * h ^ 2| ≤ P * h ^ 2 := by
    rw [abs_mul, abs_pow, abs_of_nonneg hh]
    exact mul_le_mul_of_nonneg_right hq (sq_nonneg h)
  have hm : |m| ≤ B * h ^ 2 := by
    calc
      _ = |(m - q * h ^ 2) + q * h ^ 2| := by ring_nf
      _ ≤ |m - q * h ^ 2| + |q * h ^ 2| := abs_add_le _ _
      _ ≤ C * h ^ 3 + P * h ^ 2 := add_le_add em hqh
      _ ≤ B * h ^ 2 := by
        have hs := mul_le_mul_of_nonneg_left h3 hC.le
        dsimp only [B]
        nlinarith only [hs]
  have em2 : |m ^ 2 - q ^ 2 * h ^ 4| ≤ C * (B + P) * h ^ 5 := by
    have hid : m ^ 2 - q ^ 2 * h ^ 4 = (m - q * h ^ 2) * (m + q * h ^ 2) := by ring
    rw [hid, abs_mul]
    have hs : |m + q * h ^ 2| ≤ (B + P) * h ^ 2 := by
      calc _ ≤ |m| + |q * h ^ 2| := abs_add_le _ _
        _ ≤ B * h ^ 2 + P * h ^ 2 := add_le_add hm hqh
        _ = _ := by ring
    calc
      _ ≤ (C * h ^ 3) * ((B + P) * h ^ 2) := mul_le_mul em hs (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hm2 : m ^ 2 ≤ B ^ 2 * h ^ 4 := by
    have hs := pow_le_pow_left₀ (abs_nonneg m) hm 2
    simpa only [sq_abs, mul_pow, ← pow_mul, show 2 * 2 = (4 : ℕ) from rfl] using hs
  have hid : 2 * eta * m * A + eta ^ 2 * m ^ 2 * J -
      DGPS.Circle.AngularNormalization.a0 * eta * m ^ 2 -
      3 * DGPS.Circle.AngularNormalization.a0 * q ^ 2 * h ^ 4 =
    3 * DGPS.Circle.AngularNormalization.a0 * (m ^ 2 - q ^ 2 * h ^ 4) +
      2 * eta * m * (A - 4 * DGPS.Circle.AngularNormalization.a0 * m) +
      eta ^ 2 * m ^ 2 * (J - 4 * DGPS.Circle.AngularNormalization.a0) := by
    linear_combination (DGPS.Circle.AngularNormalization.a0 * m ^ 2) * eta_relation
  change |2 * eta * m * A + eta ^ 2 * m ^ 2 * J -
    DGPS.Circle.AngularNormalization.a0 * eta * m ^ 2 -
    3 * DGPS.Circle.AngularNormalization.a0 * q ^ 2 * h ^ 4| ≤ _
  rw [hid]
  have e1 : |3 * DGPS.Circle.AngularNormalization.a0 * (m ^ 2 - q ^ 2 * h ^ 4)| ≤
      3 * DGPS.Circle.AngularNormalization.a0 * C * (B + P) * h ^ 5 := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 3 * DGPS.Circle.AngularNormalization.a0)]
    calc _ ≤ 3 * DGPS.Circle.AngularNormalization.a0 * (C * (B + P) * h ^ 5) :=
      mul_le_mul_of_nonneg_left em2 (by positivity)
      _ = _ := by ring
  have e2 : |2 * eta * m * (A - 4 * DGPS.Circle.AngularNormalization.a0 * m)| ≤
      2 * eta * B * C * h ^ 5 := by
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 * eta)]
    calc _ ≤ (2 * eta * (B * h ^ 2)) * (C * h ^ 3) := by gcongr
      _ = _ := by ring
  have e3 : |eta ^ 2 * m ^ 2 * (J - 4 * DGPS.Circle.AngularNormalization.a0)| ≤
      eta ^ 2 * B ^ 2 * C * h ^ 5 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ eta ^ 2 * m ^ 2)]
    calc _ ≤ (eta ^ 2 * (B ^ 2 * h ^ 4)) * (C * h) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ (|3 * DGPS.Circle.AngularNormalization.a0 * (m ^ 2 - q ^ 2 * h ^ 4)| +
        |2 * eta * m * (A - 4 * DGPS.Circle.AngularNormalization.a0 * m)|) +
        |eta ^ 2 * m ^ 2 * (J - 4 * DGPS.Circle.AngularNormalization.a0)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (3 * DGPS.Circle.AngularNormalization.a0 * C * (B + P) +
        2 * eta * B * C + eta ^ 2 * B ^ 2 * C) * h ^ 5 := by nlinarith only [e1, e2, e3]
    _ ≤ K * h ^ 5 := by dsimp only [K]; nlinarith [pow_nonneg hh 5]

end DGPS.Examples.PolynomialSpecies
