import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootDensityExpansion
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootMomentCoefficients

/-! Leading angular root moments from the actual uniform density expansion.
Only the leading limits needed for the triangle signs are claimed. The estimates
retain both rotating coordinates, with no reflection or exact-eigenfeature premise. -/

noncomputable section
open MeasureTheory Filter Set Real
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The actual first rotating vector and sixth-harmonic leading moments, together
with the raw generator-correction moments. Constants precede h and the mode. -/
theorem ordinaryRoot_angularMoment_estimates (D : OrdinaryRootGraphData) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ D.radius ∧ δ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < δ →
        let ρ := rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z 0 h))
        |normInt_STR02933 (fun t => Real.cos t * ρ t) / h - 1| ≤ C * h ∧
        |normInt_STR02933 (fun t => Real.sin t * ρ t) / h| ≤ C * h ∧
        |normInt_STR02933 (fun t => Real.cos (6 * t) * ρ t) / h ^ 2 - (1 / 8 : ℝ)| ≤ C * h ∧
        ∀ k : ℕ, (k = 2 ∨ k = 4) →
          |normInt_STR02933 (fun t => Real.cos ((k : ℝ) * t) * ρ t)| ≤ C * h ∧
          |normInt_STR02933 (fun t => Real.sin ((k : ℝ) * t) * ρ t)| ≤ C * h := by
  obtain ⟨M, δ, hM, hδ, hδr, hδ1, hDb⟩ := ordinaryRoot_evenBranch_density_expansion D
  refine ⟨M + 23, δ, by positivity, hδ, hδr, hδ1, fun h hh hhd => ?_⟩
  have hh1 : h ≤ 1 := (hhd.trans_le hδ1).le
  have hp21 : h ^ 2 ≤ h := by nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hh1)]
  have hp32 : h ^ 3 ≤ h ^ 2 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
  have hp31 : h ^ 3 ≤ h := hp32.trans hp21
  let u := chartU_STR02924 D.ψ h (D.Z 0 h)
  let ρ := rhoT_STR02901 h u
  let p := vFun_STR02945 2 0
  let q := qFun_STR02945 (2 / 3) 0 (-1 / 5) 0
  let b : ℝ → ℝ := fun t => q t + p t ^ 2 / 2 - (5 / 4 : ℝ)
  let P : ℝ → ℝ := fun t => 1 + h * p t + h ^ 2 * b t
  have hp : Continuous p := by
    change Continuous (vFun_STR02945 2 0)
    unfold vFun_STR02945 pFun_STR02945 bFun_STR02945
    fun_prop
  have hq : Continuous q := by
    change Continuous (qFun_STR02945 (2 / 3) 0 (-1 / 5) 0)
    unfold qFun_STR02945
    fun_prop
  have hb : Continuous b := by dsimp [b]; fun_prop
  have hP : Continuous P := by dsimp [P]; fun_prop
  have hρ : Continuous ρ := continuous_rho_STR02950 h (chartU_isC2_STR02924 D.ψ h (D.Z 0 h)).2.1.continuous
  have hpval (t : ℝ) : Real.cos (3 * t) + 2 * Real.cos t = p t := by
    simp [p, vFun_STR02945, pFun_STR02945, bFun_STR02945]
  have hqval (t : ℝ) : (2 / 3 : ℝ) * Real.cos (2 * t) - (1 / 5 : ℝ) * Real.cos (4 * t) = q t := by
    dsimp [q, qFun_STR02945]; ring
  have hD (t : ℝ) : |ρ t - P t| ≤ M * h ^ 3 := by
    have ht := hDb h hh hhd t
    dsimp only at ht
    rw [hpval t, hqval t] at ht
    exact ht
  have hpBound (t : ℝ) : |p t| ≤ 3 := by
    rw [← hpval t]
    have ht := abs_add_le (Real.cos (3 * t)) (2 * Real.cos t)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
    nlinarith [Real.abs_cos_le_one (3 * t), Real.abs_cos_le_one t]
  have hqBound (t : ℝ) : |q t| ≤ 3 := by
    rw [← hqval t]
    have ht := abs_sub ((2 / 3 : ℝ) * Real.cos (2 * t)) ((1 / 5 : ℝ) * Real.cos (4 * t))
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3),
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 5)] at ht
    nlinarith [Real.abs_cos_le_one (2 * t), Real.abs_cos_le_one (4 * t)]
  have hbBound (t : ℝ) : |b t| ≤ 20 := by
    have hp2 := pow_le_pow_left₀ (abs_nonneg (p t)) (hpBound t) 2
    norm_num at hp2
    have ht1 := abs_add_le (q t) (p t ^ 2 / 2)
    rw [abs_of_nonneg (by positivity : 0 ≤ p t ^ 2 / 2)] at ht1
    have ht2 := abs_sub (q t + p t ^ 2 / 2) (5 / 4 : ℝ)
    norm_num at ht2
    dsimp [b]
    nlinarith [hqBound t]
  have hInt (φ : ℝ → ℝ) (hφ : Continuous φ) (hφb : ∀ t, |φ t| ≤ 1) :
      |normInt_STR02933 (fun t => φ t * ρ t) -
        (normInt_STR02933 φ + h * normInt_STR02933 (fun t => φ t * p t) +
          h ^ 2 * normInt_STR02933 (fun t => φ t * b t))| ≤ M * h ^ 3 := by
    have ht : |normInt_STR02933 (fun t => φ t * (ρ t - P t))| ≤ M * h ^ 3 := by
      apply abs_normInt_le_STR02944
      intro t
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hφb t) (abs_nonneg _)).trans
        (by simpa only [one_mul] using hD t)
    have he : (fun t => φ t * (ρ t - P t)) =
        fun t => φ t * ρ t - φ t * P t := by funext t; ring
    rw [he, normInt_sub_STR02902
      (f := fun t => φ t * ρ t) (h := fun t => φ t * P t)
      (integrable_continuous_STR02934 (hφ.mul hρ))
      (integrable_continuous_STR02934 (hφ.mul hP))] at ht
    have hpoly : normInt_STR02933 (fun t => φ t * P t) =
        normInt_STR02933 φ + h * normInt_STR02933 (fun t => φ t * p t) +
          h ^ 2 * normInt_STR02933 (fun t => φ t * b t) := by
      have he : (fun t => φ t * P t) =
          fun t => 1 * φ t + h * (φ t * p t) + h ^ 2 * (φ t * b t) := by
        funext t; dsimp [P]; ring
      rw [he, normInt_lin3_STR02935 (u := φ) (v := fun t => φ t * p t)
        (z := fun t => φ t * b t)
        (integrable_continuous_STR02934 hφ)
        (integrable_continuous_STR02934 (hφ.mul hp))
        (integrable_continuous_STR02934 (hφ.mul hb))]
      ring
    rwa [hpoly] at ht
  have hBounds (φ : ℝ → ℝ) (hφb : ∀ t, |φ t| ≤ 1) :
      |normInt_STR02933 (fun t => φ t * p t)| ≤ 3 ∧
        |normInt_STR02933 (fun t => φ t * b t)| ≤ 20 := by
    constructor
    · apply abs_normInt_le_STR02944
      intro t
      rw [abs_mul]
      nlinarith [mul_le_mul (hφb t) (hpBound t) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
    · apply abs_normInt_le_STR02944
      intro t
      rw [abs_mul]
      nlinarith [mul_le_mul (hφb t) (hbBound t) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  have hZero (φ : ℝ → ℝ) (hφ : Continuous φ) (hφb : ∀ t, |φ t| ≤ 1)
      (hφ0 : normInt_STR02933 φ = 0) :
      |normInt_STR02933 (fun t => φ t * ρ t)| ≤ (M + 23) * h := by
    have hi := hInt φ hφ hφb
    rw [hφ0] at hi
    obtain ⟨ha, hc⟩ := hBounds φ hφb
    have ht1 := abs_add_le (h * normInt_STR02933 (fun t => φ t * p t))
      (h ^ 2 * normInt_STR02933 (fun t => φ t * b t))
    rw [abs_mul, abs_of_pos hh, abs_mul, abs_of_nonneg (sq_nonneg h)] at ht1
    have ht2 := abs_sub_le (normInt_STR02933 (fun t => φ t * ρ t))
      (h * normInt_STR02933 (fun t => φ t * p t) + h ^ 2 * normInt_STR02933 (fun t => φ t * b t)) 0
    simp only [sub_zero, zero_add] at hi ht2
    nlinarith [mul_le_mul_of_nonneg_left ha hh.le,
      mul_le_mul_of_nonneg_left hc (sq_nonneg h), mul_le_mul_of_nonneg_left hp31 hM]
  have hcos : normInt_STR02933 Real.cos = 0 := by simpa using normInt_cos_nat_STR02934 1
  have hsin : normInt_STR02933 Real.sin = 0 := by simpa using normInt_sin_nat_STR02934 1
  have hc6 : normInt_STR02933 (fun t => Real.cos (6 * t)) = 0 := by simpa using normInt_cos_nat_STR02934 6
  have hfirst := ordinaryRoot_exponentialJet_first
  have hsix := ordinaryRoot_exponentialJet_cos6
  have hc := hInt Real.cos Real.continuous_cos Real.abs_cos_le_one
  have hs := hInt Real.sin Real.continuous_sin Real.abs_sin_le_one
  rw [hcos, hfirst.1] at hc
  rw [hsin, hfirst.2] at hs
  obtain ⟨_, hcb⟩ := hBounds Real.cos Real.abs_cos_le_one
  obtain ⟨_, hsb⟩ := hBounds Real.sin Real.abs_sin_le_one
  have hcError : |normInt_STR02933 (fun t => Real.cos t * ρ t) - h| ≤ (M + 20) * h ^ 2 := by
    have ht := abs_sub_le (normInt_STR02933 (fun t => Real.cos t * ρ t))
      (h + h ^ 2 * normInt_STR02933 (fun t => Real.cos t * b t)) h
    have hlast : |(h + h ^ 2 * normInt_STR02933 (fun t => Real.cos t * b t)) - h| ≤ 20 * h ^ 2 := by
      have he : (h + h ^ 2 * normInt_STR02933 (fun t => Real.cos t * b t)) - h =
          h ^ 2 * normInt_STR02933 (fun t => Real.cos t * b t) := by ring
      rw [he, abs_mul, abs_of_nonneg (sq_nonneg h)]
      nlinarith [mul_le_mul_of_nonneg_left hcb (sq_nonneg h)]
    simp only [zero_add, mul_one] at hc
    nlinarith [mul_le_mul_of_nonneg_left hp32 hM]
  have hsError : |normInt_STR02933 (fun t => Real.sin t * ρ t)| ≤ (M + 20) * h ^ 2 := by
    have ht := abs_sub_le (normInt_STR02933 (fun t => Real.sin t * ρ t))
      (h ^ 2 * normInt_STR02933 (fun t => Real.sin t * b t)) 0
    have hlast : |h ^ 2 * normInt_STR02933 (fun t => Real.sin t * b t)| ≤ 20 * h ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg h)]
      nlinarith [mul_le_mul_of_nonneg_left hsb (sq_nonneg h)]
    simp only [zero_add, mul_zero, sub_zero] at hs ht
    nlinarith [mul_le_mul_of_nonneg_left hp32 hM]
  have h6b : normInt_STR02933 (fun t => Real.cos (6 * t) * b t) = (1 / 8 : ℝ) := by
    have he : (fun t => Real.cos (6 * t) * b t) = fun t =>
        Real.cos (6 * t) * (q t + p t ^ 2 / 2) - (5 / 4 : ℝ) * Real.cos (6 * t) := by
      funext t; dsimp [b]; ring
    rw [he, normInt_sub_STR02902
      (f := fun t => Real.cos (6 * t) * (q t + p t ^ 2 / 2))
      (h := fun t => (5 / 4 : ℝ) * Real.cos (6 * t))
      (integrable_continuous_STR02934 (by fun_prop))
      (integrable_continuous_STR02934 (by fun_prop)),
      hsix.2, normInt_mul_const_STR02933, hc6]
    ring
  have h6 := hInt (fun t => Real.cos (6 * t)) (by fun_prop) (fun t => Real.abs_cos_le_one _)
  rw [hc6, hsix.1, h6b] at h6
  simp only [zero_add, mul_zero] at h6
  have h6' : |normInt_STR02933 (fun t => Real.cos (6 * t) * ρ t) - h ^ 2 / 8| ≤ M * h ^ 3 := by
    convert h6 using 1 <;> ring
  refine ⟨?_, ?_, ?_, fun k hk => ?_⟩
  · have he : normInt_STR02933 (fun t => Real.cos t * ρ t) / h - 1 =
        (normInt_STR02933 (fun t => Real.cos t * ρ t) - h) / h := by field_simp [hh.ne'] <;> ring
    rw [he, abs_div, abs_of_pos hh]
    apply (div_le_iff₀ hh).2
    nlinarith
  · rw [abs_div, abs_of_pos hh]
    apply (div_le_iff₀ hh).2
    nlinarith
  · have he : normInt_STR02933 (fun t => Real.cos (6 * t) * ρ t) / h ^ 2 - (1 / 8 : ℝ) =
        (normInt_STR02933 (fun t => Real.cos (6 * t) * ρ t) - h ^ 2 / 8) / h ^ 2 := by field_simp [hh.ne'] <;> ring
    rw [he, abs_div, abs_of_pos (pow_pos hh 2)]
    apply (div_le_iff₀ (pow_pos hh 2)).2
    nlinarith
  · have hk0 : k ≠ 0 := by omega
    constructor
    · apply hZero (fun t => Real.cos ((k : ℝ) * t)) (by fun_prop) (fun t => Real.abs_cos_le_one _)
      simpa [hk0] using normInt_cos_nat_STR02934 k
    · apply hZero (fun t => Real.sin ((k : ℝ) * t)) (by fun_prop) (fun t => Real.abs_sin_le_one _)
      exact normInt_sin_nat_STR02934 k

end DGPS.Examples.ThreeSpeciesCircle
