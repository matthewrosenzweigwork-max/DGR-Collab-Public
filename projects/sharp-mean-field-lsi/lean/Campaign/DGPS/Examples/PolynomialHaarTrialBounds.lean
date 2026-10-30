import DGPS.Examples.PolynomialHaarTrial

/-! A genuine strict Haar trial upper bound below the reference spectral
barrier. Only one-sided elementary Bessel/log bounds are needed; no optional
full asymptotic, optimizer, graph, or desired rate conclusion is assumed. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments
open DGPS.Examples.PolynomialEquilibrium DGPS.Examples.SixthOrderCentering

namespace DGPS.Examples.PolynomialSpecies

private theorem log_bessel_lower (h : ℝ) (hh : |h| ≤ 1) :
    h ^ 2 / 4 - h ^ 4 / 64 - h ^ 6 ≤ Real.log (besselI 0 h) := by
  let a := h ^ 2 / 4
  let x := a + a ^ 2 / 4
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hI : 1 + x ≤ besselI 0 h := by
    have he := (besselI_zero_expand h hh).1
    change 0 ≤ besselI 0 h - (1 + a + a ^ 2 / 4 + a ^ 3 / 36) at he
    dsimp only [x]
    nlinarith [pow_nonneg ha 3]
  have hp : x - x ^ 2 / 2 ≤ 2 * x / (x + 2) := by
    apply (le_div_iff₀ (by positivity : 0 < x + 2)).2
    nlinarith [mul_nonneg (sq_nonneg x) hx]
  have hsq : h ^ 2 ≤ 1 := by nlinarith [sq_abs h, abs_nonneg h]
  have h86 : h ^ 8 ≤ h ^ 6 := by
    have he := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ h ^ 6)
    nlinarith
  have he : x - x ^ 2 / 2 = h ^ 2 / 4 - h ^ 4 / 64 - h ^ 6 / 256 - h ^ 8 / 8192 := by
    dsimp only [a, x]
    ring
  have hlo : h ^ 2 / 4 - h ^ 4 / 64 - h ^ 6 ≤ x - x ^ 2 / 2 := by
    rw [he]
    nlinarith [show 0 ≤ h ^ 6 by positivity]
  exact ((hlo.trans hp).trans (Real.le_log_one_add_of_nonneg hx)).trans
    (Real.log_le_log (by positivity : 0 < 1 + x) hI)

/-- A common polynomial lower bound for the actual Haar trial gap, with its
true fourth coefficient retained and its moving-reference remainder derived. -/
theorem polynomial_haar_trial_gap_lower :
    ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧ δ ≤ 1 ∧ ∀ h : ℝ, |h| ≤ δ →
      h ^ 2 / 4 + ((eta - 9) / 576) * h ^ 4 - K * h ^ 6 ≤
        (scalarGap (canonical_elementary_polynomial_model h) polynomialHaarTrial : ℝ) := by
  obtain ⟨C, δ0, hC, hδ0, hroot⟩ := abs_root_le_sixth_EX054
  let K := 1 + 11 * C / 8
  refine ⟨K, min δ0 1, by dsimp only [K]; positivity, lt_min hδ0 one_pos,
    min_le_right _ _, fun h hh => ?_⟩
  let s := root_EX054 h
  have hh1 : |h| ≤ 1 := hh.trans (min_le_right _ _)
  have hs : |s| ≤ C * h ^ 6 := hroot h (hh.trans (min_le_left _ _))
  have hsq : h ^ 2 ≤ 1 := by nlinarith [sq_abs h, abs_nonneg h]
  have h86 : h ^ 8 ≤ h ^ 6 := by
    have he := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ h ^ 6)
    nlinarith
  have hlog : h ^ 2 / 4 - h ^ 4 / 64 - (1 + 4 * C / 3) * h ^ 6 ≤
      Real.log (partition_EX054 h s) := by
    have he := abs_log_partition_sub_EX054 h s
    rw [partition_zero_EX054] at he
    have hp := mul_le_mul (show 1 + |h| / 3 ≤ 4 / 3 by linarith) hs
      (abs_nonneg s) (by norm_num : (0 : ℝ) ≤ 4 / 3)
    have hl := log_bessel_lower h hh1
    have hn := (abs_le.mp he).1
    nlinarith
  have hm : moment_EX054 h s = s / (2 * eta) - h ^ 2 / 24 := by
    have he := root_equation_EX054 h
    change s = 2 * eta * (moment_EX054 h s - polyCentering h) at he
    unfold polyCentering at he
    apply eq_sub_iff_add_eq.mpr
    apply (eq_div_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) eta_pos.ne')).mpr
    nlinarith
  have hmquad : eta * moment_EX054 h s ^ 2 = eta * h ^ 4 / 576 - s * h ^ 2 / 24 + s ^ 2 / (4 * eta) := by
    rw [hm]
    field_simp [eta_pos.ne']
    ring
  have hcross : s * h ^ 2 / 24 ≤ C * h ^ 6 / 24 := by
    have he := mul_le_mul_of_nonneg_right ((le_abs_self s).trans hs) (by positivity : 0 ≤ h ^ 2)
    have ht := mul_le_mul_of_nonneg_left h86 hC.le
    nlinarith
  let b := lipschitz_absoluteDrift (canonical_elementary_polynomial_model h) (lipschitzData_canonical_model h)
  rw [(polynomial_haar_trial_gap_dissipation h b).1]
  change h ^ 2 / 4 + ((eta - 9) / 576) * h ^ 4 - K * h ^ 6 ≤
    Real.log (partition_EX054 h s) + eta * moment_EX054 h s ^ 2
  rw [hmquad]
  dsimp only [K]
  nlinarith [div_nonneg (sq_nonneg s) (mul_pos (by norm_num : (0 : ℝ) < 4) eta_pos).le]

/-- One fixed actual original-domain Haar competitor lies strictly below a
native rate barrier with coefficient 5/48. The threshold precedes every field
and genuine drift; positive gap and finite dissipation are derived internally. -/
theorem polynomial_haar_trial_strict_upper :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h ≤ δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h),
        0 < scalarGap (canonical_elementary_polynomial_model h) polynomialHaarTrial ∧
        scalarQuotient (canonical_elementary_polynomial_model h) b polynomialHaarTrial <
          ENNReal.ofReal (a0 * (1 + 5 * h ^ 2 / 48)) := by
  obtain ⟨K, δ0, hK, hδ0, hδ01, hgap⟩ := polynomial_haar_trial_gap_lower
  let q := (eta - 9) / 576
  let L := 1 + eta ^ 2 + |q| + 3 * K
  have hL : 0 < L := by dsimp only [L]; positivity
  refine ⟨min δ0 (1 / (192 * (L + 1))), lt_min hδ0 (by positivity), fun h hh hsmall b => ?_⟩
  let t := h ^ 2
  let R := a0 / 2 * (h ^ 2 * (1 + eta * h ^ 2 / 36) ^ 2 + eta ^ 2 * h ^ 4 / 36)
  let r := a0 * (1 + 5 * h ^ 2 / 48)
  let G : ℝ := scalarGap (canonical_elementary_polynomial_model h) polynomialHaarTrial
  have ha0 : 0 < a0 := a0_pos
  have hrpos : 0 < r := by
    change 0 < a0 * (1 + 5 * h ^ 2 / 48)
    exact mul_pos ha0 (by positivity)
  have ht : 0 < t := sq_pos_of_pos hh
  have hhδ : |h| ≤ δ0 := by rw [abs_of_pos hh]; exact hsmall.trans (min_le_left _ _)
  have hh1 : h ≤ 1 := (hsmall.trans (min_le_left _ _)).trans hδ01
  have hth : t ≤ h := by
    have he := mul_le_mul_of_nonneg_left hh1 hh.le
    change h ^ 2 ≤ h
    nlinarith
  have ht1 : t ≤ 1 := hth.trans hh1
  have hLt : L * t ≤ 1 / 192 := by
    have he := (le_div_iff₀ (by positivity : 0 < 192 * (L + 1))).1 (hsmall.trans (min_le_right _ _))
    have hp := mul_le_mul_of_nonneg_left hth hL.le
    nlinarith
  have hG : t / 4 + q * t ^ 2 - K * t ^ 3 ≤ G := by
    simpa only [G, q, t, ← pow_mul] using hgap h hhδ
  have hR : R = a0 * (t / 2 + (eta / 36 + eta ^ 2 / 72) * t ^ 2 + eta ^ 2 / 2592 * t ^ 3) := by
    dsimp only [R, t]
    ring
  have hfour : eta / 36 + eta ^ 2 / 72 - 2 * q - 5 / 96 = -1 / 96 := by
    dsimp only [q]
    nlinarith [eta_relation]
  have hpoly : R - 2 * r * (t / 4 + q * t ^ 2 - K * t ^ 3) =
      a0 * t ^ 2 * (-1 / 96 + (eta ^ 2 / 2592 - 5 * q / 24 + 2 * K) * t + 5 * K / 24 * t ^ 2) := by
    rw [hR]
    change a0 * (t / 2 + (eta / 36 + eta ^ 2 / 72) * t ^ 2 + eta ^ 2 / 2592 * t ^ 3) -
      2 * (a0 * (1 + 5 * t / 48)) * (t / 4 + q * t ^ 2 - K * t ^ 3) = _
    calc
      _ = a0 * t ^ 2 * ((eta / 36 + eta ^ 2 / 72 - 2 * q - 5 / 96) +
        (eta ^ 2 / 2592 - 5 * q / 24 + 2 * K) * t + 5 * K / 24 * t ^ 2) := by ring
      _ = _ := by rw [hfour]
  have hcoef : eta ^ 2 / 2592 - 5 * q / 24 + 2 * K + 5 * K / 24 ≤ L := by
    dsimp only [L]
    nlinarith [sq_nonneg eta, neg_le_abs q, abs_nonneg q]
  have htail : (eta ^ 2 / 2592 - 5 * q / 24 + 2 * K) * t + 5 * K / 24 * t ^ 2 ≤ L * t := by
    have ht2 : t ^ 2 ≤ t := by
      simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left ht1 ht.le
    have he := mul_le_mul_of_nonneg_left ht2 (by positivity : 0 ≤ 5 * K / 24)
    have hp := mul_le_mul_of_nonneg_right hcoef ht.le
    nlinarith
  have hnegative : R - 2 * r * G < 0 := by
    have he := mul_le_mul_of_nonneg_left hG (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hrpos.le)
    have hp : a0 * t ^ 2 * (-1 / 96 + (eta ^ 2 / 2592 - 5 * q / 24 + 2 * K) * t +
        5 * K / 24 * t ^ 2) < 0 := by
      apply mul_neg_of_pos_of_neg (mul_pos ha0 (sq_pos_of_pos ht))
      linarith
    rw [← hpoly] at hp
    linarith
  have hR0 : 0 ≤ R := by
    dsimp only [R]
    exact mul_nonneg (div_nonneg ha0.le (by norm_num)) (by positivity)
  have hGpos : 0 < scalarGap (canonical_elementary_polynomial_model h) polynomialHaarTrial := by
    have hg : 0 < G := by
      have hp : 0 < 2 * r * G := by linarith
      exact pos_of_mul_pos_right hp (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hrpos.le)
    exact_mod_cast hg
  have hD := (polynomial_haar_trial_gap_dissipation h b).2
  have hGr : 0 < G := by exact_mod_cast hGpos
  have hDfin : scalarDissipation (canonical_elementary_polynomial_model h) b polynomialHaarTrial ≠ ⊤ := by rw [hD]; exact ENNReal.ofReal_ne_top
  have hQfin := ((scalarQuotient_lt_top_iff (canonical_elementary_polynomial_model h) b polynomialHaarTrial hGpos).2
    (lt_top_iff_ne_top.mpr hDfin)).ne
  refine ⟨hGpos, (ENNReal.toReal_lt_toReal hQfin ENNReal.ofReal_ne_top).1 ?_⟩
  rw [scalarQuotient, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.coe_toReal, hD, ENNReal.toReal_ofReal hR0, ENNReal.toReal_ofReal hrpos.le]
  change R / (2 * G) < r
  apply (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hGr)).2
  nlinarith

end DGPS.Examples.PolynomialSpecies
