import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootNormalizedMoments

/-! A uniform quadratic expansion of the actual normalized ordinary-root density.
This pointwise statement is obtained from genuine exponential and normalizer
remainder estimates, with one radius and constant before h and the spatial point. -/

noncomputable section
open MeasureTheory Filter Set Real
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem scalar_density_quotient_error (h a b r E Z K J R : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hK : 0 ≤ K) (hJ : 0 ≤ J) (hR : 0 ≤ R)
    (ha : |a| ≤ 3) (hb : |b| ≤ 3) (hr : |r| ≤ R * h ^ 3)
    (hTaylor : |E - (1 + h * a + h ^ 2 * (b + a ^ 2 / 2) +
      h ^ 3 * (a * b + a ^ 3 / 6) + r)| ≤ J * h ^ 4)
    (hZ : |Z - (1 + (5 / 4 : ℝ) * h ^ 2)| ≤ K * h ^ 4)
    (hKh : K * h ≤ 1 / 4) :
    |E / Z - (1 + h * a + h ^ 2 * (b + a ^ 2 / 2 - (5 / 4 : ℝ)))| ≤
      2 * (J + R + 14 + 14 * K + 17) * h ^ 3 := by
  let B := J + R + 14
  let C := 2 * (B + 14 * K + 17)
  let Q := b + a ^ 2 / 2
  let P := a * b + a ^ 3 / 6
  let T := 1 + h * a + h ^ 2 * (Q - (5 / 4 : ℝ))
  change |E - (1 + h * a + h ^ 2 * Q + h ^ 3 * P + r)| ≤ J * h ^ 4 at hTaylor
  have ha2 : a ^ 2 ≤ 9 := by
    have hs := pow_le_pow_left₀ (abs_nonneg a) ha 2
    norm_num at hs
    exact hs
  have ha3 : |a| ^ 3 ≤ 27 := by
    have hs := pow_le_pow_left₀ (abs_nonneg a) ha 3
    norm_num at hs
    exact hs
  have hQ : |Q| ≤ 8 := by
    have ht := abs_add_le b (a ^ 2 / 2)
    rw [abs_of_nonneg (by positivity : 0 ≤ a ^ 2 / 2)] at ht
    dsimp [Q]
    nlinarith only [ht, hb, ha2]
  have hP : |P| ≤ 14 := by
    have ht := abs_add_le (a * b) (a ^ 3 / 6)
    rw [abs_mul, abs_div, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 6)] at ht
    have hab := mul_le_mul ha hb (abs_nonneg b) (by norm_num : (0 : ℝ) ≤ 3)
    dsimp [P]
    nlinarith only [ht, hab, ha3]
  have hQ' : |Q - (5 / 4 : ℝ)| ≤ 10 := by
    have ht := abs_sub Q (5 / 4 : ℝ)
    norm_num at ht
    linarith only [ht, hQ]
  have hp43 : h ^ 4 ≤ h ^ 3 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
  have hp41 : h ^ 4 ≤ h := by
    simpa only [pow_one] using (pow_le_pow_of_le_one hh.le hh1 (by norm_num : (1 : ℕ) ≤ 4))
  have hE : |E - (1 + h * a + h ^ 2 * Q)| ≤ B * h ^ 3 := by
    have he : E - (1 + h * a + h ^ 2 * Q) =
        (E - (1 + h * a + h ^ 2 * Q + h ^ 3 * P + r)) + h ^ 3 * P + r := by ring
    rw [he]
    have ht1 := abs_add_le (E - (1 + h * a + h ^ 2 * Q + h ^ 3 * P + r)) (h ^ 3 * P)
    have ht2 := abs_add_le ((E - (1 + h * a + h ^ 2 * Q + h ^ 3 * P + r)) + h ^ 3 * P) r
    have hp : |h ^ 3 * P| ≤ 14 * h ^ 3 := by
      rw [abs_mul, abs_of_pos (pow_pos hh 3)]
      calc
        _ ≤ h ^ 3 * 14 := mul_le_mul_of_nonneg_left hP (pow_nonneg hh.le 3)
        _ = _ := by ring
    dsimp [B]
    nlinarith only [hTaylor, hp, hr, ht1, ht2, mul_le_mul_of_nonneg_left hp43 hJ]
  have hZhalf : (1 / 2 : ℝ) ≤ Z := by
    have hl := (abs_le.mp hZ).1
    nlinarith only [hl, hKh, mul_le_mul_of_nonneg_left hp41 hK, sq_nonneg h]
  have hZpos : 0 < Z := by linarith
  have hhsq : h ^ 2 ≤ 1 := pow_le_one₀ hh.le hh1
  have hT : |T| ≤ 14 := by
    have ht1 := abs_add_le (1 : ℝ) (h * a)
    have ht2 := abs_add_le (1 + h * a) (h ^ 2 * (Q - (5 / 4 : ℝ)))
    rw [abs_mul, abs_of_pos hh] at ht1
    rw [abs_mul, abs_of_nonneg (sq_nonneg h)] at ht2
    norm_num only [abs_one] at ht1
    dsimp [T]
    nlinarith only [ht1, ht2, hhsq, hh1, mul_le_mul_of_nonneg_left ha hh.le,
      mul_le_mul_of_nonneg_left hQ' (sq_nonneg h)]
  have hZT : |(Z - (1 + (5 / 4 : ℝ) * h ^ 2)) * T| ≤ 14 * K * h ^ 3 := by
    rw [abs_mul]
    calc
      _ ≤ (K * h ^ 4) * 14 := mul_le_mul hZ hT (abs_nonneg T) (by positivity)
      _ = (14 * K) * h ^ 4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp43 (by positivity)
  have hcross : |(5 / 4 : ℝ) * h ^ 3 * a + (5 / 4 : ℝ) * h ^ 4 * (Q - (5 / 4 : ℝ))| ≤ 17 * h ^ 3 := by
    have ht := abs_add_le ((5 / 4 : ℝ) * h ^ 3 * a) ((5 / 4 : ℝ) * h ^ 4 * (Q - (5 / 4 : ℝ)))
    simp only [abs_mul, abs_pow, abs_of_pos hh,
      abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4)] at ht
    nlinarith only [ht, hp43, pow_nonneg hh.le 3,
      mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ (5 / 4 : ℝ) * h ^ 3),
      mul_le_mul_of_nonneg_left hQ' (by positivity : 0 ≤ (5 / 4 : ℝ) * h ^ 4)]
  have hnum : |E - Z * T| ≤ (B + 14 * K + 17) * h ^ 3 := by
    have he : E - Z * T = (E - (1 + h * a + h ^ 2 * Q)) -
        (Z - (1 + (5 / 4 : ℝ) * h ^ 2)) * T -
        ((5 / 4 : ℝ) * h ^ 3 * a + (5 / 4 : ℝ) * h ^ 4 * (Q - (5 / 4 : ℝ))) := by
      dsimp [T]
      ring
    rw [he]
    have ht1 := abs_sub (E - (1 + h * a + h ^ 2 * Q)) ((Z - (1 + (5 / 4 : ℝ) * h ^ 2)) * T)
    have ht2 := abs_sub ((E - (1 + h * a + h ^ 2 * Q)) - (Z - (1 + (5 / 4 : ℝ) * h ^ 2)) * T)
      ((5 / 4 : ℝ) * h ^ 3 * a + (5 / 4 : ℝ) * h ^ 4 * (Q - (5 / 4 : ℝ)))
    nlinarith only [hE, hZT, hcross, ht1, ht2]
  have he : E / Z - T = (E - Z * T) / Z := by field_simp [hZpos.ne'] <;> ring
  change |E / Z - T| ≤ C * h ^ 3
  rw [he, abs_div, abs_of_pos hZpos]
  apply (div_le_iff₀ hZpos).2
  dsimp [C]
  nlinarith only [hnum, mul_le_mul_of_nonneg_left hZhalf
    (by positivity : 0 ≤ 2 * ((B + 14 * K + 17) * h ^ 3))]


/-- The actual normalized density has the two prescribed leading spatial profiles.
The unknown cubic chart remainder is controlled by its proved uniform bound. -/
theorem ordinaryRoot_evenBranch_density_expansion (D : OrdinaryRootGraphData) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ δ ≤ D.radius ∧ δ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < δ → ∀ t : ℝ,
        let a := Real.cos (3 * t) + 2 * Real.cos t
        let b := (2 / 3 : ℝ) * Real.cos (2 * t) - (1 / 5 : ℝ) * Real.cos (4 * t)
        |rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z 0 h)) t -
          (1 + h * a + h ^ 2 * (b + a ^ 2 / 2 - (5 / 4 : ℝ)))| ≤ C * h ^ 3 := by
  obtain ⟨K, δN, hK, hδN, hδNr, hNb⟩ := ordinaryRoot_normalizer_cos3_estimates D
  obtain ⟨J, δT, hJ, hδT, _, hTb⟩ := ordinaryRoot_evenBranch_exponential_expansion D
  obtain ⟨R, hR, hRb⟩ := ordinaryRoot_evenBranch_C1_expansion D
  let δ := min δN (min δT (min 1 (4 * (K + 1))⁻¹))
  let C := 2 * (J + R + 14 + 14 * K + 17)
  have hδ : 0 < δ := lt_min hδN (lt_min hδT (lt_min (by norm_num) (by positivity)))
  have hδr : δ ≤ D.radius := (min_le_left _ _).trans hδNr
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  refine ⟨C, δ, by dsimp [C]; positivity, hδ, hδr, hδ1, fun h hh hhd t => ?_⟩
  have hhN : h < δN := hhd.trans_le (min_le_left _ _)
  have hhT : h < δT := hhd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hh1 : h ≤ 1 := (hhd.trans_le hδ1).le
  have hhR : |h| ≤ D.radius := by rw [abs_of_pos hh]; exact (hhd.trans_le hδr).le
  have hhK : h ≤ (4 * (K + 1))⁻¹ := (hhd.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))).le
  let u := chartU_STR02924 D.ψ h (D.Z 0 h)
  let Z := normInt_STR02933 (fun s => Real.exp (h * Real.cos (3 * s) + u s))
  let E := Real.exp (h * Real.cos (3 * t) + u t)
  let a := Real.cos (3 * t) + 2 * Real.cos t
  let b := (2 / 3 : ℝ) * Real.cos (2 * t) - (1 / 5 : ℝ) * Real.cos (4 * t)
  let r := u t - 2 * h * Real.cos t - h ^ 2 * b
  have ha : |a| ≤ 3 := by
    have ht := abs_add_le (Real.cos (3 * t)) (2 * Real.cos t)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
    dsimp [a]
    nlinarith [Real.abs_cos_le_one (3 * t), Real.abs_cos_le_one t]
  have hb : |b| ≤ 3 := by
    have ht := abs_sub ((2 / 3 : ℝ) * Real.cos (2 * t)) ((1 / 5 : ℝ) * Real.cos (4 * t))
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3),
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 5)] at ht
    dsimp [b]
    nlinarith [Real.abs_cos_le_one (2 * t), Real.abs_cos_le_one (4 * t)]
  have hr : |r| ≤ R * h ^ 3 := by simpa only [abs_of_pos hh] using (hRb h hhR t).1
  have hTaylor : |E - (1 + h * a + h ^ 2 * (b + a ^ 2 / 2) +
      h ^ 3 * (a * b + a ^ 3 / 6) + r)| ≤ J * h ^ 4 := hTb h hh hhT t
  have hZ : |Z - (1 + (5 / 4 : ℝ) * h ^ 2)| ≤ K * h ^ 4 := (hNb h hh hhN).1
  have hKh : K * h ≤ 1 / 4 := by
    have ht := mul_le_mul_of_nonneg_left hhK (by positivity : 0 ≤ 4 * (K + 1))
    rw [mul_inv_cancel₀ (by positivity : 4 * (K + 1) ≠ 0)] at ht
    nlinarith only [ht, hh.le]
  have hρ : rhoT_STR02901 h u t = E / Z := by
    unfold rhoT_STR02901
    rw [← normInt_eq_meanT_STR02962]
  rw [hρ]
  exact scalar_density_quotient_error h a b r E Z K J R hh hh1 hK hJ hR ha hb hr hTaylor hZ hKh

end DGPS.Examples.ThreeSpeciesCircle
