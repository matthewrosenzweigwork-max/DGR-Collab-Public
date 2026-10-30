import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootAngularMoments
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootThirdMoment

/-! Quantitative leading estimates for the six actual angular moments. The
second/fourth/sixth generator corrections are retained. The input expansions
are genuine integral bounds at the SAME retained graph, not formal jets. -/

noncomputable section
open MeasureTheory Filter Set Real
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem scalar_generator_linear_error (κ h M f target R : ℝ)
    (hκ : 0 < κ) (hf : |f - target| ≤ M * h) (hR : |R| ≤ 2 * M * h) :
    |κ * f + 3 * κ / 2 * R - κ * target| ≤ (4 * κ * M) * h := by
  have he : κ * f + 3 * κ / 2 * R - κ * target =
      κ * (f - target) + 3 * κ / 2 * R := by ring
  rw [he]
  have ht := abs_add_le (κ * (f - target)) (3 * κ / 2 * R)
  rw [abs_mul, abs_of_pos hκ, abs_mul, abs_of_pos (by positivity : 0 < 3 * κ / 2)] at ht
  nlinarith only [ht, mul_le_mul_of_nonneg_left hf hκ.le,
    mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 3 * κ / 2)]

private theorem scalar_generator_invariant_error (κ h KB M b R : ℝ)
    (hκ : 0 < κ) (hb : |b - 1| ≤ KB * h) (hR : |R| ≤ (M + 1) * h) :
    |9 * κ * b + (135 / 8 : ℝ) * κ * R - 9 * κ| ≤
      (9 * κ * KB + (135 / 8 : ℝ) * κ * (M + 1)) * h := by
  have he : 9 * κ * b + (135 / 8 : ℝ) * κ * R - 9 * κ =
      9 * κ * (b - 1) + (135 / 8 : ℝ) * κ * R := by ring
  rw [he]
  have ht := abs_add_le (9 * κ * (b - 1)) ((135 / 8 : ℝ) * κ * R)
  rw [abs_mul, abs_of_pos (by positivity : 0 < 9 * κ),
    abs_mul, abs_of_pos (by positivity : 0 < (135 / 8 : ℝ) * κ)] at ht
  nlinarith only [ht, mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 9 * κ),
    mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ (135 / 8 : ℝ) * κ)]

/-- All six leading moments have an actual first-order error bound. This does
not assert the stronger second-order STR031 error for the invariant moment. -/
theorem ordinaryRoot_sixAngularMoment_estimates (D : OrdinaryRootGraphData) :
    ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧ δ ≤ D.radius ∧ δ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < δ →
        let ρ := rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z 0 h))
        let C := normInt_STR02933 (fun t => Real.cos t * ρ t) / h
        let S := normInt_STR02933 (fun t => Real.sin t * ρ t) / h
        let B := 15 / (4 * h ^ 3) *
          (normInt_STR02933 (fun t => ρ t * Real.cos (3 * t)) - referenceMean h)
        let AC := a0 * C + 3 * a0 / 2 *
          (normInt_STR02933 (fun t => Real.cos (4 * t) * ρ t) -
            normInt_STR02933 (fun t => Real.cos (2 * t) * ρ t))
        let AS := a0 * S + 3 * a0 / 2 *
          (normInt_STR02933 (fun t => Real.sin (4 * t) * ρ t) +
            normInt_STR02933 (fun t => Real.sin (2 * t) * ρ t))
        let AB := 9 * a0 * B + 135 * a0 / (8 * h ^ 2) *
          (normInt_STR02933 (fun t => Real.cos (6 * t) * ρ t) - besselI 2 h / besselI 0 h)
        |C - 1| ≤ K * h ∧ |S| ≤ K * h ∧ |B - 1| ≤ K * h ∧
          |AC - a0| ≤ K * h ∧ |AS| ≤ K * h ∧ |AB - 9 * a0| ≤ K * h := by
  obtain ⟨M, δM, hM, hδM, hδMr, hδM1, hMb⟩ := ordinaryRoot_angularMoment_estimates D
  obtain ⟨L, δL, hL, hδL, _, hLb⟩ := ordinaryRoot_centeredThirdMoment_estimate D
  let KB := (15 / 4 : ℝ) * L
  let KA := 4 * a0 * M
  let KE := 9 * a0 * KB + (135 / 8 : ℝ) * a0 * (M + 1)
  let K := 1 + M + KB + KA + KE
  have ha : 0 < a0 := a0_pos
  have hKB : 0 ≤ KB := by dsimp [KB]; positivity
  have hKA : 0 ≤ KA := by dsimp [KA]; positivity
  have hKE : 0 ≤ KE := by dsimp [KE]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hMK : M ≤ K := by dsimp [K]; linarith
  have hBK : KB ≤ K := by dsimp [K]; linarith
  have hAK : KA ≤ K := by dsimp [K]; linarith
  have hEK : KE ≤ K := by dsimp [K]; linarith
  refine ⟨K, min δM δL, hK, lt_min hδM hδL,
    (min_le_left _ _).trans hδMr, (min_le_left _ _).trans hδM1, fun h hh hhd => ?_⟩
  have hhM : h < δM := hhd.trans_le (min_le_left _ _)
  have hhL : h < δL := hhd.trans_le (min_le_right _ _)
  have hh1 : h ≤ 1 := (hhM.trans_le hδM1).le
  have hp : h ^ 2 ≤ h := by nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hh1)]
  let ρ := rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z 0 h))
  let c := normInt_STR02933 (fun t => Real.cos t * ρ t) / h
  let s := normInt_STR02933 (fun t => Real.sin t * ρ t) / h
  let b := 15 / (4 * h ^ 3) *
    (normInt_STR02933 (fun t => ρ t * Real.cos (3 * t)) - referenceMean h)
  obtain ⟨hc, hs, h6, h24⟩ := hMb h hh hhM
  change |c - 1| ≤ M * h at hc
  change |s| ≤ M * h at hs
  have hb : |b - 1| ≤ KB * h := by
    have ht := hLb h hh hhL
    have he : b - 1 = (15 / (4 * h ^ 3)) *
        (normInt_STR02933 (fun t => ρ t * Real.cos (3 * t)) - referenceMean h -
          (4 / 15 : ℝ) * h ^ 3) := by dsimp [b]; field_simp [hh.ne'] <;> ring
    rw [he, abs_mul, abs_of_pos (by positivity : 0 < 15 / (4 * h ^ 3))]
    calc
      _ ≤ (15 / (4 * h ^ 3)) * (L * h ^ 4) := mul_le_mul_of_nonneg_left ht (by positivity)
      _ = KB * h := by dsimp [KB]; field_simp [hh.ne'] <;> ring
  have h6ref : |(normInt_STR02933 (fun t => Real.cos (6 * t) * ρ t) -
      besselI 2 h / besselI 0 h) / h ^ 2| ≤ (M + 1) * h := by
    have hr := (ordinaryReference_moment_estimates h hh hh1).2
    have hr' : |(besselI 2 h / besselI 0 h) / h ^ 2 - (1 / 8 : ℝ)| ≤ h ^ 2 := by
      have he : (besselI 2 h / besselI 0 h) / h ^ 2 - (1 / 8 : ℝ) =
          (besselI 2 h / besselI 0 h - h ^ 2 / 8) / h ^ 2 := by
        field_simp [hh.ne'] <;> ring
      rw [he, abs_div, abs_of_pos (pow_pos hh 2)]
      apply (div_le_iff₀ (pow_pos hh 2)).2
      nlinarith only [hr]
    have he : (normInt_STR02933 (fun t => Real.cos (6 * t) * ρ t) -
        besselI 2 h / besselI 0 h) / h ^ 2 =
        (normInt_STR02933 (fun t => Real.cos (6 * t) * ρ t) / h ^ 2 - (1 / 8 : ℝ)) -
          ((besselI 2 h / besselI 0 h) / h ^ 2 - (1 / 8 : ℝ)) := by ring
    rw [he]
    have ht := abs_sub
      (normInt_STR02933 (fun t => Real.cos (6 * t) * ρ t) / h ^ 2 - (1 / 8 : ℝ))
      ((besselI 2 h / besselI 0 h) / h ^ 2 - (1 / 8 : ℝ))
    nlinarith only [ht, h6, hr', hp]
  obtain ⟨hc2, hs2⟩ := h24 2 (Or.inl rfl)
  obtain ⟨hc4, hs4⟩ := h24 4 (Or.inr rfl)
  have hcorrC : |normInt_STR02933 (fun t => Real.cos (4 * t) * ρ t) -
      normInt_STR02933 (fun t => Real.cos (2 * t) * ρ t)| ≤ 2 * M * h := by
    have ht := abs_sub (normInt_STR02933 (fun t => Real.cos (4 * t) * ρ t))
      (normInt_STR02933 (fun t => Real.cos (2 * t) * ρ t))
    norm_num at hc2 hc4
    nlinarith only [ht, hc2, hc4]
  have hcorrS : |normInt_STR02933 (fun t => Real.sin (4 * t) * ρ t) +
      normInt_STR02933 (fun t => Real.sin (2 * t) * ρ t)| ≤ 2 * M * h := by
    have ht := abs_add_le (normInt_STR02933 (fun t => Real.sin (4 * t) * ρ t))
      (normInt_STR02933 (fun t => Real.sin (2 * t) * ρ t))
    norm_num at hs2 hs4
    nlinarith only [ht, hs2, hs4]
  have hAC : |a0 * c + 3 * a0 / 2 *
      (normInt_STR02933 (fun t => Real.cos (4 * t) * ρ t) -
        normInt_STR02933 (fun t => Real.cos (2 * t) * ρ t)) - a0| ≤ KA * h := by
    simpa only [mul_one, KA] using scalar_generator_linear_error a0 h M c 1 _ ha hc hcorrC
  have hAS : |a0 * s + 3 * a0 / 2 *
      (normInt_STR02933 (fun t => Real.sin (4 * t) * ρ t) +
        normInt_STR02933 (fun t => Real.sin (2 * t) * ρ t))| ≤ KA * h := by
    simpa only [mul_zero, sub_zero, KA] using
      scalar_generator_linear_error a0 h M s 0 _ ha (by simpa only [sub_zero] using hs) hcorrS
  have hAB : |9 * a0 * b + 135 * a0 / (8 * h ^ 2) *
      (normInt_STR02933 (fun t => Real.cos (6 * t) * ρ t) - besselI 2 h / besselI 0 h) -
        9 * a0| ≤ KE * h := by
    change _ ≤ (9 * a0 * KB + (135 / 8 : ℝ) * a0 * (M + 1)) * h
    convert scalar_generator_invariant_error a0 h KB M b
      ((normInt_STR02933 (fun t => Real.cos (6 * t) * ρ t) - besselI 2 h / besselI 0 h) / h ^ 2)
      ha hb h6ref using 1 <;> ring
  exact ⟨hc.trans (mul_le_mul_of_nonneg_right hMK hh.le),
    hs.trans (mul_le_mul_of_nonneg_right hMK hh.le),
    hb.trans (mul_le_mul_of_nonneg_right hBK hh.le),
    hAC.trans (mul_le_mul_of_nonneg_right hAK hh.le),
    hAS.trans (mul_le_mul_of_nonneg_right hAK hh.le),
    hAB.trans (mul_le_mul_of_nonneg_right hEK hh.le)⟩

end DGPS.Examples.ThreeSpeciesCircle
