import DGPS.Examples.PolynomialSpeciesFiniteProfileDeficitExpansion

/-! Actual quadratic gap on the concrete finite profile, with uniform cubic
error. This supplies the fixed-profile normalized-rate term before same-graph
and selected-reference transport. -/

noncomputable section
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

theorem polynomialMixedFiniteProfile_gap_expansion (M : ℝ) (hM : 1 ≤ M) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ a b h : ℝ,
      |a| ≤ M → |b| ≤ M → 0 ≤ h → h ≤ δ →
      |polynomialRangeGap (h, 0) (polynomialMixedFiniteProfile a b h) -
        (a ^ 2 + b ^ 2) / 4 * h ^ 2| ≤ K * h ^ 3 := by
  let c := fun x : ℝ × ℝ => -(x.1 + x.1 ^ 2 - x.2 ^ 2) / 6
  let d := fun x : ℝ × ℝ => -(x.2 * (1 + x.1)) / 6
  have hcoef : Continuous (fun x : ℝ × ℝ => polynomialFiniteH4 x.1 x.2 (c x) (d x)) := by
    simp_rw [polynomialFiniteH4_eq]
    dsimp only [c, d]
    fun_prop
  obtain ⟨B0, hB0⟩ := (isCompact_closedBall (0 : ℝ × ℝ) M).exists_bound_of_continuousOn hcoef.continuousOn
  let B := max B0 0 + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  let R := 4 * (M + 1) ^ 2
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hR : M ≤ R := by dsimp only [R]; nlinarith [sq_nonneg M]
  obtain ⟨δ, hδ, C, hC, hinfo⟩ := polynomialFiniteProfile_information_expansion_raw R
  obtain ⟨Cm, hCm, hmom⟩ := polynomialFiniteProfile_moment_bounds M hM
  let P := |Real.sqrt 2| * (M ^ 2 + M ^ 2) / 24 + 1
  have hP : 0 < P := by dsimp only [P]; positivity
  have hη := eta_pos
  let K := C + B + eta / 2 * (P + Cm) ^ 2
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨min δ 1, K, lt_min hδ zero_lt_one, hK, fun a b h ha hb hh hhδ => ?_⟩
  have ha2 : a ^ 2 ≤ M ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg a) ha 2
  have hb2 : b ^ 2 ≤ M ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg b) hb 2
  have hc : |c (a, b)| ≤ R := by
    dsimp only [c]
    rw [abs_div, abs_neg]
    have hs : |a + a ^ 2 - b ^ 2| ≤ M + M ^ 2 + M ^ 2 := (abs_sub _ _).trans
      (add_le_add ((abs_add_le _ _).trans (by simpa only [abs_of_nonneg (sq_nonneg a)] using add_le_add ha ha2))
        (by simpa only [abs_of_nonneg (sq_nonneg b)] using hb2))
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 6), abs_of_pos (by norm_num : (0 : ℝ) < 24)]
    dsimp only [R]
    nlinarith
  have hd : |d (a, b)| ≤ R := by
    dsimp only [d]
    rw [abs_div, abs_neg, abs_mul]
    have hs : |1 + a| ≤ 1 + M := (abs_add_le _ _).trans (by simpa only [abs_one] using add_le_add le_rfl ha)
    have hp := mul_le_mul hb hs (abs_nonneg _) hMp.le
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 6), abs_of_pos (by norm_num : (0 : ℝ) < 24)]
    dsimp only [R]
    nlinarith
  have hh1 : h ≤ 1 := hhδ.trans (min_le_right _ _)
  have hhδ' : |h| ≤ δ := by rw [abs_of_nonneg hh]; exact hhδ.trans (min_le_left _ _)
  obtain ⟨_, _, _, _, _, eH⟩ := hinfo a b (c (a, b)) (d (a, b)) (ha.trans hR) (hb.trans hR) hc hd h hhδ'
  rw [polynomialFiniteH2_eq, polynomialFiniteH3_eq_zero, zero_mul, add_zero, abs_of_nonneg hh] at eH
  have hBH : |polynomialFiniteH4 a b (c (a, b)) (d (a, b))| ≤ B := by
    have hp : (a, b) ∈ Metric.closedBall (0 : ℝ × ℝ) M := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using max_le ha hb
    exact (hB0 _ hp).trans (by dsimp only [B]; linarith [le_max_left B0 0])
  have hp3 : h ^ 3 ≤ h ^ 2 := pow_le_pow_of_le_one hh hh1 (by norm_num)
  have hp4 : h ^ 4 ≤ h ^ 3 := pow_le_pow_of_le_one hh hh1 (by norm_num)
  have hp5 : h ^ 5 ≤ h ^ 3 := pow_le_pow_of_le_one hh hh1 (by norm_num)
  let m := polynomialFiniteMoment a b h
  let q := Real.sqrt 2 * (a ^ 2 - b ^ 2) / 24
  have hq : |q| ≤ P := by
    have hs : |a ^ 2 - b ^ 2| ≤ M ^ 2 + M ^ 2 := (abs_sub _ _).trans
      (by simpa only [abs_of_nonneg (sq_nonneg a), abs_of_nonneg (sq_nonneg b)] using add_le_add ha2 hb2)
    have hm := mul_le_mul_of_nonneg_left hs (abs_nonneg (Real.sqrt 2))
    dsimp only [q, P]
    rw [abs_div, abs_mul]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 6), abs_of_pos (by norm_num : (0 : ℝ) < 24)]
    linarith
  have em := (hmom a b h ha hb hh hh1).1
  have hm : |m| ≤ (P + Cm) * h ^ 2 := by
    have hqh : |q * h ^ 2| ≤ P * h ^ 2 := by
      rw [abs_mul, abs_pow, abs_of_nonneg hh]
      exact mul_le_mul_of_nonneg_right hq (sq_nonneg h)
    calc _ = |(m - q * h ^ 2) + q * h ^ 2| := by ring_nf
      _ ≤ |m - q * h ^ 2| + |q * h ^ 2| := abs_add_le _ _
      _ ≤ Cm * h ^ 3 + P * h ^ 2 := add_le_add em hqh
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hp3 hCm.le]
  have hm2 : m ^ 2 ≤ (P + Cm) ^ 2 * h ^ 4 := by
    simpa only [sq_abs, mul_pow, ← pow_mul, show 2 * 2 = (4 : ℕ) from rfl] using pow_le_pow_left₀ (abs_nonneg m) hm 2
  have eH' : |polynomialFiniteProfileEntropy a b (c (a, b)) (d (a, b)) h -
      (a ^ 2 + b ^ 2) / 4 * h ^ 2| ≤ (C + B) * h ^ 3 := by
    have he : polynomialFiniteProfileEntropy a b (c (a, b)) (d (a, b)) h - (a ^ 2 + b ^ 2) / 4 * h ^ 2 =
        (polynomialFiniteProfileEntropy a b (c (a, b)) (d (a, b)) h -
          ((a ^ 2 + b ^ 2) / 4 * h ^ 2 + polynomialFiniteH4 a b (c (a, b)) (d (a, b)) * h ^ 4)) +
        polynomialFiniteH4 a b (c (a, b)) (d (a, b)) * h ^ 4 := by ring
    rw [he]
    have hbnd : |polynomialFiniteH4 a b (c (a, b)) (d (a, b)) * h ^ 4| ≤ B * h ^ 4 := by
      rw [abs_mul, abs_pow, abs_of_nonneg hh]
      exact mul_le_mul_of_nonneg_right hBH (pow_nonneg hh 4)
    exact (abs_add_le _ _).trans ((add_le_add eH hbnd).trans (by
      nlinarith [mul_le_mul_of_nonneg_left hp5 hC, mul_le_mul_of_nonneg_left hp4 hB.le]))
  have hgap : polynomialRangeGap (h, 0) (polynomialMixedFiniteProfile a b h) =
      polynomialFiniteProfileEntropy a b (c (a, b)) (d (a, b)) h + eta / 2 * m ^ 2 := by
    unfold polynomialRangeGap
    dsimp only
    rw [(polynomialMixedFiniteProfile_information a b h).2]
    dsimp only [m, polynomialFiniteMoment, c, d]
    ring
  rw [hgap]
  have he : polynomialFiniteProfileEntropy a b (c (a, b)) (d (a, b)) h + eta / 2 * m ^ 2 -
      (a ^ 2 + b ^ 2) / 4 * h ^ 2 =
    (polynomialFiniteProfileEntropy a b (c (a, b)) (d (a, b)) h -
      (a ^ 2 + b ^ 2) / 4 * h ^ 2) + eta / 2 * m ^ 2 := by ring
  rw [he]
  have hem : |eta / 2 * m ^ 2| ≤ eta / 2 * (P + Cm) ^ 2 * h ^ 3 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ eta / 2 * m ^ 2)]
    exact (mul_le_mul_of_nonneg_left hm2 (by positivity)).trans
      (by
        calc
          _ = (eta / 2 * (P + Cm) ^ 2) * h ^ 4 := by ring
          _ ≤ (eta / 2 * (P + Cm) ^ 2) * h ^ 3 := mul_le_mul_of_nonneg_left hp4 (by positivity))
  exact (abs_add_le _ _).trans ((add_le_add eH' hem).trans (by dsimp only [K]; ring_nf; exact le_rfl))

end DGPS.Examples.PolynomialSpecies
