import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootMomentTaylor
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootMomentCoefficients

/-! Genuine integrated exponential estimates at the same ordinary root. The
actual chart remainder is integrated explicitly; no formal jet is substituted. -/

noncomputable section
open MeasureTheory Filter Set Real
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem polynomial_integral (h : ℝ) (p q r φ : ℝ → ℝ)
    (hp : Continuous p) (hq : Continuous q) (hr : Continuous r) (hφ : Continuous φ) :
    normInt_STR02933 (fun t => φ t *
      (1 + h * p t + h ^ 2 * (q t + p t ^ 2 / 2) + h ^ 3 * (p t * q t + p t ^ 3 / 6) + r t)) =
      normInt_STR02933 φ + h * normInt_STR02933 (fun t => φ t * p t) +
      h ^ 2 * normInt_STR02933 (fun t => φ t * (q t + p t ^ 2 / 2)) +
      h ^ 3 * normInt_STR02933 (fun t => φ t * (p t * q t + p t ^ 3 / 6)) +
      normInt_STR02933 (fun t => φ t * r t) := by
  have he : (fun t => φ t *
      (1 + h * p t + h ^ 2 * (q t + p t ^ 2 / 2) + h ^ 3 * (p t * q t + p t ^ 3 / 6) + r t)) =
      fun t => 1 * φ t + h * (φ t * p t) + h ^ 2 * (φ t * (q t + p t ^ 2 / 2)) +
        h ^ 3 * (φ t * (p t * q t + p t ^ 3 / 6)) + 1 * (φ t * r t) := by
    funext t; ring
  rw [he, normInt_lin5_STR02945
    (f1 := φ) (f2 := fun t => φ t * p t)
    (f3 := fun t => φ t * (q t + p t ^ 2 / 2))
    (f4 := fun t => φ t * (p t * q t + p t ^ 3 / 6))
    (f5 := fun t => φ t * r t) 1 h (h ^ 2) (h ^ 3) 1 hφ
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)]
  ring

/-- Actual normalizer and third-harmonic numerator estimates, with a uniform
fourth-order remainder and the actual cubic log moment retained explicitly. -/
theorem ordinaryRoot_normalizer_cos3_estimates (D : OrdinaryRootGraphData) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧ δ ≤ D.radius ∧
      ∀ h : ℝ, 0 < h → h < δ →
        let u := chartU_STR02924 D.ψ h (D.Z 0 h)
        |normInt_STR02933 (fun t => Real.exp (h * Real.cos (3 * t) + u t)) -
          (1 + (5 / 4 : ℝ) * h ^ 2)| ≤ K * h ^ 4 ∧
        |normInt_STR02933 (fun t => Real.cos (3 * t) * Real.exp (h * Real.cos (3 * t) + u t)) -
          (h / 2 + (77 / 80 : ℝ) * h ^ 3 +
            normInt_STR02933 (fun t => Real.cos (3 * t) * u t))| ≤ K * h ^ 4 := by
  obtain ⟨K, δ, hK, hδ, hδr, hTb⟩ := ordinaryRoot_evenBranch_exponential_expansion D
  refine ⟨K, δ, hK, hδ, hδr, fun h hh hhd => ?_⟩
  let u := chartU_STR02924 D.ψ h (D.Z 0 h)
  let p := vFun_STR02945 2 0
  let q := qFun_STR02945 (2 / 3) 0 (-1 / 5) 0
  let r : ℝ → ℝ := fun t => u t - 2 * h * Real.cos t - h ^ 2 * q t
  let E : ℝ → ℝ := fun t => Real.exp (h * Real.cos (3 * t) + u t)
  let P : ℝ → ℝ := fun t =>
    1 + h * p t + h ^ 2 * (q t + p t ^ 2 / 2) + h ^ 3 * (p t * q t + p t ^ 3 / 6) + r t
  have hu : Continuous u := (chartU_isC2_STR02924 D.ψ h (D.Z 0 h)).2.1.continuous
  have hp : Continuous p := by
    change Continuous (vFun_STR02945 2 0)
    unfold vFun_STR02945 pFun_STR02945 bFun_STR02945
    fun_prop
  have hq : Continuous q := by
    change Continuous (qFun_STR02945 (2 / 3) 0 (-1 / 5) 0)
    unfold qFun_STR02945
    fun_prop
  have hr : Continuous r := by dsimp [r]; fun_prop
  have hE : Continuous E := by dsimp [E]; fun_prop
  have hP : Continuous P := by dsimp [P]; fun_prop
  have hpval (t : ℝ) : Real.cos (3 * t) + 2 * Real.cos t = p t := by
    simp [p, vFun_STR02945, pFun_STR02945, bFun_STR02945]
  have hqval (t : ℝ) : (2 / 3 : ℝ) * Real.cos (2 * t) - (1 / 5 : ℝ) * Real.cos (4 * t) = q t := by
    dsimp [q, qFun_STR02945]
    ring
  have hT (t : ℝ) : |E t - P t| ≤ K * h ^ 4 := by
    have hb := hTb h hh hhd t
    dsimp only at hb
    rw [hpval t, hqval t] at hb
    exact hb
  have hnormal := ordinaryRoot_exponentialJet_normalizer
  have hthird := ordinaryRoot_exponentialJet_cos3
  have hcos1 : normInt_STR02933 Real.cos = 0 := by
    simpa using normInt_cos_nat_STR02934 1
  have hcos3 : normInt_STR02933 (fun t => Real.cos (3 * t)) = 0 := by
    simpa using normInt_cos_nat_STR02934 3
  have hmean : normInt_STR02933 u = 0 := by
    rw [normInt_eq_meanT_STR02962]
    change meanT_STR02901 (uT_STR02901 (h * D.Z 0 h 0) (h * D.Z 0 h 1)
      ((D.ψ (h * D.Z 0 h 0, h * D.Z 0 h 1, h, h ^ 2 * D.Z 0 h 2) : E_STR02969) : PeriodicC2_STR02969).val) = 0
    exact (meanT_uT_STR02924 _ _ (continuous_val_STR02924 _)
      (inE_of_mem_STR02924 _)).1
  have hr0 : normInt_STR02933 r = 0 := by
    have he : r = fun t => 1 * u t + (-2 * h) * Real.cos t + (-h ^ 2) * q t := by
      funext t; dsimp [r]; ring
    rw [he, normInt_lin3_STR02935
      (u := u) (v := Real.cos) (z := q)
      (integrable_continuous_STR02934 hu) (integrable_continuous_STR02934 Real.continuous_cos)
      (integrable_continuous_STR02934 hq), hmean, hcos1, hnormal.2.1]
    ring
  have h3q : normInt_STR02933 (fun t => Real.cos (3 * t) * q t) = 0 := by
    apply normInt_antiperiodic_STR02945 (by fun_prop)
    intro t
    have hc : Real.cos (3 * (t + π)) = -Real.cos (3 * t) := bFun_shift_STR02945 t
    rw [hc]
    change -Real.cos (3 * t) * qFun_STR02945 (2 / 3) 0 (-1 / 5) 0 (t + π) = _
    rw [qFun_shift_STR02945]
    ring
  have h31 : normInt_STR02933 (fun t => Real.cos (3 * t) * Real.cos t) = 0 := by
    simpa using normInt_cos_mul_cos_STR02934 3 1 (by norm_num)
  have hr3 : normInt_STR02933 (fun t => Real.cos (3 * t) * r t) =
      normInt_STR02933 (fun t => Real.cos (3 * t) * u t) := by
    have he : (fun t => Real.cos (3 * t) * r t) = fun t =>
        1 * (Real.cos (3 * t) * u t) + (-2 * h) * (Real.cos (3 * t) * Real.cos t) +
          (-h ^ 2) * (Real.cos (3 * t) * q t) := by
      funext t; dsimp [r]; ring
    rw [he, normInt_lin3_STR02935
      (u := fun t => Real.cos (3 * t) * u t)
      (v := fun t => Real.cos (3 * t) * Real.cos t)
      (z := fun t => Real.cos (3 * t) * q t)
      (integrable_continuous_STR02934 (by fun_prop))
      (integrable_continuous_STR02934 (by fun_prop))
      (integrable_continuous_STR02934 (by fun_prop)), h31, h3q]
    ring
  have hP0 : normInt_STR02933 P = 1 + (5 / 4 : ℝ) * h ^ 2 := by
    have he := polynomial_integral h p q r (fun _ => 1) hp hq hr continuous_const
    have hp0 : normInt_STR02933 (fun t => p t) = 0 := hnormal.1
    have hp2 : normInt_STR02933 (fun t => q t + p t ^ 2 / 2) = (5 / 4 : ℝ) := hnormal.2.2.1
    have hp3 : normInt_STR02933 (fun t => p t * q t + p t ^ 3 / 6) = 0 := hnormal.2.2.2
    have hr00 : normInt_STR02933 (fun t => r t) = 0 := hr0
    simp only [one_mul, normInt_const_STR02944] at he
    rw [hp0, hp2, hp3, hr00] at he
    change normInt_STR02933 P = _ at he
    convert he using 1 <;> ring
  have hP3 : normInt_STR02933 (fun t => Real.cos (3 * t) * P t) =
      h / 2 + (77 / 80 : ℝ) * h ^ 3 + normInt_STR02933 (fun t => Real.cos (3 * t) * u t) := by
    have he := polynomial_integral h p q r (fun t => Real.cos (3 * t)) hp hq hr (by fun_prop)
    rw [hcos3, hthird.1, hthird.2.1, hthird.2.2, hr3] at he
    change normInt_STR02933 (fun t => Real.cos (3 * t) * P t) = _ at he
    convert he using 1 <;> ring
  constructor
  · have hb := abs_normInt_le_STR02944 hT
    rw [normInt_sub_STR02902 (integrable_continuous_STR02934 hE)
      (integrable_continuous_STR02934 hP), hP0] at hb
    exact hb
  · have hb : |normInt_STR02933 (fun t => Real.cos (3 * t) * (E t - P t))| ≤ K * h ^ 4 := by
      apply abs_normInt_le_STR02944
      intro t
      rw [abs_mul]
      calc
        _ ≤ 1 * |E t - P t| := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one (3 * t)) (abs_nonneg _)
        _ ≤ K * h ^ 4 := by simpa only [one_mul] using hT t
    have he : (fun t => Real.cos (3 * t) * (E t - P t)) =
        fun t => Real.cos (3 * t) * E t - Real.cos (3 * t) * P t := by funext t; ring
    rw [he, normInt_sub_STR02902
      (f := fun t => Real.cos (3 * t) * E t) (h := fun t => Real.cos (3 * t) * P t)
      (integrable_continuous_STR02934 (by fun_prop))
      (integrable_continuous_STR02934 (by fun_prop)), hP3] at hb
    exact hb

end DGPS.Examples.ThreeSpeciesCircle
