import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootNormalizedMoments
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootCubicMoment
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryReferenceMoments

/-! The actual centered third root moment. The numerator, normalizer and reference
errors are all proved integral estimates; no formal coefficient or symmetry is assumed. -/

noncomputable section
open MeasureTheory Filter Set Real
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem cos3_quotient_error (h Z N K L : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hZ : (1 / 2 : ℝ) ≤ Z) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hz : |Z - (1 + (5 / 4 : ℝ) * h ^ 2)| ≤ K * h ^ 4)
    (hn : |N - (h / 2 + (199 / 240 : ℝ) * h ^ 3)| ≤ L * h ^ 4) :
    |N / Z - (h / 2 + (49 / 240 : ℝ) * h ^ 3)| ≤ 2 * (L + K + 1) * h ^ 4 := by
  let T := h / 2 + (49 / 240 : ℝ) * h ^ 3
  have hp3 : h ^ 3 ≤ h := by
    simpa only [pow_one] using (pow_le_pow_of_le_one hh.le hh1 (by norm_num : (1 : ℕ) ≤ 3))
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hT1 : T ≤ 1 := by dsimp [T]; nlinarith
  have he : N - Z * T = (N - (h / 2 + (199 / 240 : ℝ) * h ^ 3)) -
      (Z - (1 + (5 / 4 : ℝ) * h ^ 2)) * T - (49 / 192 : ℝ) * h ^ 5 := by
    dsimp [T]
    ring
  have hprod : |(Z - (1 + (5 / 4 : ℝ) * h ^ 2)) * T| ≤ K * h ^ 4 := by
    rw [abs_mul, abs_of_nonneg hT0]
    calc
      _ ≤ (K * h ^ 4) * 1 := mul_le_mul hz hT1 hT0 (by positivity)
      _ = _ := by ring
  have hp5 : h ^ 5 ≤ h ^ 4 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
  have hnum : |N - Z * T| ≤ (L + K + 1) * h ^ 4 := by
    rw [he]
    have ht1 := abs_sub (N - (h / 2 + (199 / 240 : ℝ) * h ^ 3))
      ((Z - (1 + (5 / 4 : ℝ) * h ^ 2)) * T)
    have ht2 := abs_sub ((N - (h / 2 + (199 / 240 : ℝ) * h ^ 3)) -
      (Z - (1 + (5 / 4 : ℝ) * h ^ 2)) * T) ((49 / 192 : ℝ) * h ^ 5)
    rw [abs_of_nonneg (by positivity : 0 ≤ (49 / 192 : ℝ) * h ^ 5)] at ht2
    nlinarith
  have hZpos : 0 < Z := by linarith
  have hdiv : |N - Z * T| / Z ≤ 2 * ((L + K + 1) * h ^ 4) := by
    apply (div_le_iff₀ hZpos).2
    nlinarith [mul_le_mul_of_nonneg_left hZ (by positivity : 0 ≤ 2 * ((L + K + 1) * h ^ 4))]
  have hid : N / Z - T = (N - Z * T) / Z := by field_simp [hZpos.ne']
  change |N / Z - T| ≤ _
  rw [hid, abs_div, abs_of_pos hZpos]
  nlinarith

/-- The true root third-harmonic density moment, including the normalizer correction. -/
theorem ordinaryRoot_thirdMoment_estimate (D : OrdinaryRootGraphData) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ δ ≤ D.radius ∧ δ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < δ →
        |normInt_STR02933 (fun t => rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z 0 h)) t *
          Real.cos (3 * t)) - (h / 2 + (49 / 240 : ℝ) * h ^ 3)| ≤ C * h ^ 4 := by
  obtain ⟨K, δN, hK, hδN, hδNr, hNb⟩ := ordinaryRoot_normalizer_cos3_estimates D
  obtain ⟨M, δM, hM, hδM, _, hMb⟩ := ordinaryRoot_cubic_logMoment_estimate D
  let δ := min δN (min δM (min 1 (4 * (K + 1))⁻¹))
  let C := 2 * ((K + M) + K + 1)
  have hδ : 0 < δ := lt_min hδN (lt_min hδM (lt_min (by norm_num) (by positivity)))
  have hδr : δ ≤ D.radius := (min_le_left _ _).trans hδNr
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  refine ⟨C, δ, by dsimp [C]; positivity, hδ, hδr, hδ1, fun h hh hhd => ?_⟩
  have hhN : h < δN := hhd.trans_le (min_le_left _ _)
  have hhM : h < δM := hhd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hh1 : h ≤ 1 := (hhd.trans_le hδ1).le
  have hhK : h ≤ (4 * (K + 1))⁻¹ := (hhd.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))).le
  let u := chartU_STR02924 D.ψ h (D.Z 0 h)
  let Z := normInt_STR02933 (fun t => Real.exp (h * Real.cos (3 * t) + u t))
  let N := normInt_STR02933 (fun t => Real.cos (3 * t) * Real.exp (h * Real.cos (3 * t) + u t))
  let m := normInt_STR02933 (fun t => u t * Real.cos (3 * t))
  obtain ⟨hZ, hN⟩ := hNb h hh hhN
  have hcomm : normInt_STR02933 (fun t => Real.cos (3 * t) * u t) = m := by
    congr 1; funext t; ring
  change |Z - (1 + (5 / 4 : ℝ) * h ^ 2)| ≤ K * h ^ 4 at hZ
  change |N - (h / 2 + (77 / 80 : ℝ) * h ^ 3 +
    normInt_STR02933 (fun t => Real.cos (3 * t) * u t))| ≤ K * h ^ 4 at hN
  rw [hcomm] at hN
  have hm0 : |m / h ^ 3 + (2 / 15 : ℝ)| ≤ M * h := hMb h hh hhM
  have hm : |m + (2 / 15 : ℝ) * h ^ 3| ≤ M * h ^ 4 := by
    have he : (m / h ^ 3 + (2 / 15 : ℝ)) * h ^ 3 = m + (2 / 15 : ℝ) * h ^ 3 := by
      field_simp [hh.ne']
    rw [← he, abs_mul, abs_of_pos (pow_pos hh 3)]
    nlinarith [mul_le_mul_of_nonneg_right hm0 (pow_nonneg hh.le 3)]
  have hN' : |N - (h / 2 + (199 / 240 : ℝ) * h ^ 3)| ≤ (K + M) * h ^ 4 := by
    have he : N - (h / 2 + (199 / 240 : ℝ) * h ^ 3) =
        (N - (h / 2 + (77 / 80 : ℝ) * h ^ 3 + m)) + (m + (2 / 15 : ℝ) * h ^ 3) := by ring
    rw [he]
    have ht := abs_add_le (N - (h / 2 + (77 / 80 : ℝ) * h ^ 3 + m)) (m + (2 / 15 : ℝ) * h ^ 3)
    nlinarith
  have hKh : K * h ≤ 1 / 4 := by
    have ht := mul_le_mul_of_nonneg_left hhK (by positivity : 0 ≤ 4 * (K + 1))
    rw [mul_inv_cancel₀ (by positivity : 4 * (K + 1) ≠ 0)] at ht
    nlinarith
  have hp4 : h ^ 4 ≤ h := by
    simpa only [pow_one] using (pow_le_pow_of_le_one hh.le hh1 (by norm_num : (1 : ℕ) ≤ 4))
  have hZhalf : (1 / 2 : ℝ) ≤ Z := by
    have hl := (abs_le.mp hZ).1
    nlinarith [mul_le_mul_of_nonneg_left hp4 hK, sq_nonneg h]
  have hquot := cos3_quotient_error h Z N K (K + M) hh hh1 hZhalf hK (by positivity) hZ hN'
  have hratio : normInt_STR02933 (fun t => rhoT_STR02901 h u t * Real.cos (3 * t)) = N / Z := by
    have he : (fun t => rhoT_STR02901 h u t * Real.cos (3 * t)) =
        fun t => Z⁻¹ * (Real.cos (3 * t) * Real.exp (h * Real.cos (3 * t) + u t)) := by
      funext t
      unfold rhoT_STR02901
      rw [← normInt_eq_meanT_STR02962]
      dsimp only [Z]
      ring
    rw [he, normInt_mul_const_STR02933]
    dsimp only [N]
    rw [div_eq_mul_inv]
    ring
  rw [hratio]
  exact hquot

/-- The actual bare third-moment difference has coefficient4/15, with a proved
uniform fourth-order error. This is a leading coefficient result, not STR031's
stronger second-order error for the rescaled feature. -/
theorem ordinaryRoot_centeredThirdMoment_estimate (D : OrdinaryRootGraphData) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ δ ≤ D.radius ∧
      ∀ h : ℝ, 0 < h → h < δ →
        |normInt_STR02933 (fun t => rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z 0 h)) t *
          Real.cos (3 * t)) - referenceMean h - (4 / 15 : ℝ) * h ^ 3| ≤ C * h ^ 4 := by
  obtain ⟨C, δ, hC, hδ, hδr, hδ1, hb⟩ := ordinaryRoot_thirdMoment_estimate D
  refine ⟨C + 1, δ, by positivity, hδ, hδr, fun h hh hhd => ?_⟩
  have hh1 : h ≤ 1 := (hhd.trans_le hδ1).le
  have hr := (ordinaryReference_moment_estimates h hh hh1).1
  have ht := hb h hh hhd
  let R := normInt_STR02933 (fun t => rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z 0 h)) t * Real.cos (3 * t))
  have he : R - referenceMean h - (4 / 15 : ℝ) * h ^ 3 =
      (R - (h / 2 + (49 / 240 : ℝ) * h ^ 3)) - (referenceMean h - (h / 2 - h ^ 3 / 16)) := by ring
  change |R - referenceMean h - (4 / 15 : ℝ) * h ^ 3| ≤ _
  rw [he]
  have htriangle := abs_sub (R - (h / 2 + (49 / 240 : ℝ) * h ^ 3))
    (referenceMean h - (h / 2 - h ^ 3 / 16))
  have hp : h ^ 5 ≤ h ^ 4 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
  nlinarith

end DGPS.Examples.ThreeSpeciesCircle
