import DGPS.Examples.PolynomialFiniteProfileIH
import DGPS.Examples.PolynomialSpeciesScaledFourier

/-! Exact coefficients for the TRUE cos-one finite profile. The nonzero
correlation of the relative first mode with the reference is retained. -/

noncomputable section
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem profile_absolute_eq (A B : ℝ) :
    pFun_STR02945 (1 + A) B = fun t => Real.cos t + pFun_STR02945 A B t := by
  funext t
  unfold pFun_STR02945
  ring

private theorem profile_q_mean (C D : ℝ) : normInt_STR02933 (qFun_STR02945 C D 0 0) = 0 := by
  rw [qFun_eq_STR02945]
  exact normInt_mode2_STR02945 C D 0 0 (by norm_num) (by norm_num)

private theorem profile_pb (A B : ℝ) :
    normInt_STR02933 (fun t => pFun_STR02945 A B t * Real.cos t) = A / 2 := by
  have he (t : ℝ) : pFun_STR02945 A B t * Real.cos t =
      0 * Real.cos t ^ 0 + A * Real.cos t ^ 2 + 0 * Real.cos t ^ 4 +
      0 * Real.cos t ^ 6 + 0 * Real.cos t ^ 8 + B * (Real.cos t ^ 1 * Real.sin t) +
      0 * (Real.cos t ^ 3 * Real.sin t) + 0 * (Real.cos t ^ 5 * Real.sin t) +
      0 * (Real.cos t ^ 7 * Real.sin t) := by
    unfold pFun_STR02945
    ring
  rw [normInt_congr_STR02945 he, mean9_STR02946]
  ring

private theorem profile_entropy_a2 {b p q : ℝ → ℝ} (hb : Continuous b) (hp : Continuous p)
    (hq : Continuous q) (hq0 : normInt_STR02933 q = 0) :
    normInt_STR02933 (fun t => ek2_STR02945 (p t) (q t) (b t + p t)) =
      normInt_STR02933 (fun t => p t * b t) + normInt_STR02933 (fun t => p t ^ 2) := by
  rw [normInt_congr_STR02945 (g := fun t => 1 * (p t * b t) + 1 * p t ^ 2 + 1 * q t)
    (fun t => by unfold ek2_STR02945; ring),
    normInt_lin3_STR02945 (f1 := fun t => p t * b t) (f2 := fun t => p t ^ 2) (f3 := q) 1 1 1 (hp.mul hb) (hp.pow 2) hq, hq0]
  ring

private theorem profile_entropy_z2 {b p q : ℝ → ℝ} (hb : Continuous b) (hp : Continuous p)
    (hq : Continuous q) (hq0 : normInt_STR02933 q = 0) :
    z2_STR02944 (fun t => b t + p t) q =
      (1 / 2) * normInt_STR02933 (fun t => b t ^ 2) +
      normInt_STR02933 (fun t => p t * b t) + (1 / 2) * normInt_STR02933 (fun t => p t ^ 2) := by
  unfold z2_STR02944
  rw [normInt_congr_STR02945
      (g := fun t => 1 * q t + (1 / 2) * b t ^ 2 + 1 * (p t * b t) + (1 / 2) * p t ^ 2)
      (fun t => by ring),
    normInt_lin4_STR02945 (f1 := q) (f2 := fun t => b t ^ 2) (f3 := fun t => p t * b t) (f4 := fun t => p t ^ 2) 1 (1 / 2) 1 (1 / 2) hq (hb.pow 2) (hp.mul hb) (hp.pow 2), hq0]
  ring

/-- Generic fourth entropy normalization, without the FALSE cos-one PB=0
specialization. Only continuity and the genuine second-mode mean zero occur. -/
private theorem profile_entropy_fourth {b p q : ℝ → ℝ} (hb : Continuous b) (hp : Continuous p)
    (hq : Continuous q) (hq0 : normInt_STR02933 q = 0) :
    entC4_STR02945 b (fun t => b t + p t) p q =
      (1 / 2) * normInt_STR02933 (fun t => q t ^ 2) +
      normInt_STR02933 (fun t => p t * b t * q t) +
      normInt_STR02933 (fun t => p t ^ 2 * q t) +
      (1 / 4) * normInt_STR02933 (fun t => p t ^ 2 * b t ^ 2) +
      (1 / 3) * normInt_STR02933 (fun t => p t ^ 3 * b t) +
      (1 / 8) * normInt_STR02933 (fun t => p t ^ 4) -
      (1 / 4) * normInt_STR02933 (fun t => b t ^ 2) * normInt_STR02933 (fun t => p t ^ 2) -
      (1 / 2) * normInt_STR02933 (fun t => p t * b t) ^ 2 -
      normInt_STR02933 (fun t => p t * b t) * normInt_STR02933 (fun t => p t ^ 2) -
      (3 / 8) * normInt_STR02933 (fun t => p t ^ 2) ^ 2 := by
  have hF : normInt_STR02933 (fun t => ek4_STR02945 (p t) (q t) (b t + p t)) -
      normInt_STR02933 (fun t => q t ^ 2 / 2 + (b t + p t) ^ 2 * q t / 2 + (b t + p t) ^ 4 / 24) +
      normInt_STR02933 (fun t => (0 : ℝ) ^ 2 / 2 + b t ^ 2 * 0 / 2 + b t ^ 4 / 24) =
      (1 / 2) * normInt_STR02933 (fun t => q t ^ 2) +
      normInt_STR02933 (fun t => p t * b t * q t) +
      normInt_STR02933 (fun t => p t ^ 2 * q t) +
      (1 / 4) * normInt_STR02933 (fun t => p t ^ 2 * b t ^ 2) +
      (1 / 3) * normInt_STR02933 (fun t => p t ^ 3 * b t) +
      (1 / 8) * normInt_STR02933 (fun t => p t ^ 4) := by
    have h1 := normInt_lin3_STR02945
      (f1 := fun t => ek4_STR02945 (p t) (q t) (b t + p t))
      (f2 := fun t => q t ^ 2 / 2 + (b t + p t) ^ 2 * q t / 2 + (b t + p t) ^ 4 / 24)
      (f3 := fun t => (0 : ℝ) ^ 2 / 2 + b t ^ 2 * 0 / 2 + b t ^ 4 / 24) 1 (-1) 1
      (by unfold ek4_STR02945; fun_prop) (by fun_prop) (by fun_prop)
    have h2 := normInt_lin6_STR02945 (f1 := fun t => q t ^ 2) (f2 := fun t => p t * b t * q t)
      (f3 := fun t => p t ^ 2 * q t) (f4 := fun t => p t ^ 2 * b t ^ 2)
      (f5 := fun t => p t ^ 3 * b t) (f6 := fun t => p t ^ 4) (1 / 2) 1 1 (1 / 4) (1 / 3) (1 / 8)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    have h3 := normInt_congr_STR02945
      (f := fun t => 1 * ek4_STR02945 (p t) (q t) (b t + p t) +
        (-1) * (q t ^ 2 / 2 + (b t + p t) ^ 2 * q t / 2 + (b t + p t) ^ 4 / 24) +
        1 * ((0 : ℝ) ^ 2 / 2 + b t ^ 2 * 0 / 2 + b t ^ 4 / 24))
      (g := fun t => (1 / 2) * q t ^ 2 + p t * b t * q t + p t ^ 2 * q t +
        (1 / 4) * (p t ^ 2 * b t ^ 2) + (1 / 3) * (p t ^ 3 * b t) + (1 / 8) * p t ^ 4)
      (fun t => by unfold ek4_STR02945; ring)
    simp only [one_mul] at h1 h2 h3
    linarith only [h1, h2, h3]
  unfold entC4_STR02945
  rw [profile_entropy_a2 hb hp hq hq0, profile_entropy_z2 hb hp hq hq0, ent_zb2_STR02945]
  unfold z4_STR02944
  linear_combination hF

theorem polynomialFiniteI2_eq (A B : ℝ) : polynomialFiniteI2 A B = (A ^ 2 + B ^ 2) / 2 := by
  unfold polynomialFiniteI2
  rw [mom_pd2_STR02946]
  ring

theorem polynomialFiniteH2_eq (A B C D : ℝ) :
    polynomialFiniteH2 A B C D = (A ^ 2 + B ^ 2) / 4 := by
  unfold polynomialFiniteH2 entC2_STR02945
  rw [profile_absolute_eq, profile_entropy_a2 Real.continuous_cos
    (pFun_cont_STR02945 A B) (qFun_cont_STR02945 C D 0 0) (profile_q_mean C D),
    profile_entropy_z2 Real.continuous_cos (pFun_cont_STR02945 A B)
      (qFun_cont_STR02945 C D 0 0) (profile_q_mean C D), ent_zb2_STR02945,
    mom_p2_STR02946]
  ring

theorem polynomialFiniteI3_eq_zero (A B C D : ℝ) : polynomialFiniteI3 A B C D = 0 := by
  exact fisher_n1_STR02945 (deriv_pFun_cont_STR02945 A B)
    (deriv_qFun_cont_STR02945 C D 0 0) (pFun_cont_STR02945 (1 + A) B)
    (deriv_pFun_shift_STR02945 A B) (deriv_qFun_shift_STR02945 C D 0 0)
    (pFun_shift_STR02945 (1 + A) B)

theorem polynomialFiniteH3_eq_zero (A B C D : ℝ) : polynomialFiniteH3 A B C D = 0 := by
  unfold polynomialFiniteH3
  rw [profile_absolute_eq]
  exact ent_c3_STR02945 Real.continuous_cos (pFun_cont_STR02945 A B)
    (qFun_cont_STR02945 C D 0 0) (fun t => Real.cos_add_pi t)
    (pFun_shift_STR02945 A B) (qFun_shift_STR02945 C D 0 0)

private theorem profile_pdqdv (A B C D : ℝ) :
    normInt_STR02933 (fun t => deriv (pFun_STR02945 A B) t * deriv (qFun_STR02945 C D 0 0) t *
      pFun_STR02945 (1 + A) B t) =
      ((A * (1 + A) - B ^ 2) * C + B * (1 + 2 * A) * D) / 2 := by
  let X := 1 + A
  have he (t : ℝ) : deriv (pFun_STR02945 A B) t * deriv (qFun_STR02945 C D 0 0) t * pFun_STR02945 X B t =
      (2 * A * B * D) * Real.cos t ^ 0 +
      (4 * C * (A * X - B ^ 2) - 2 * B * D * (X + 3 * A)) * Real.cos t ^ 2 +
      (-4 * C * (A * X - B ^ 2) + 4 * B * D * (X + A)) * Real.cos t ^ 4 +
      0 * Real.cos t ^ 6 + 0 * Real.cos t ^ 8 +
      (4 * A * B * C - 2 * D * (B ^ 2 - A * X)) * (Real.cos t ^ 1 * Real.sin t) +
      (-4 * B * C * (A + X) + 4 * D * (B ^ 2 - A * X)) * (Real.cos t ^ 3 * Real.sin t) +
      0 * (Real.cos t ^ 5 * Real.sin t) + 0 * (Real.cos t ^ 7 * Real.sin t) := by
    rw [dp_cs_STR02946, dq_cs_STR02946, p_cs_STR02946]
    linear_combination (4 * C * (A * X - B ^ 2) * Real.cos t ^ 2 +
      4 * A * B * C * Real.cos t * Real.sin t - 2 * A * B * D * (2 * Real.cos t ^ 2 - 1)) *
      Real.sin_sq_add_cos_sq t
  rw [normInt_congr_STR02945 he, mean9_STR02946]
  dsimp only [X]
  ring

private theorem profile_pd2v2 (A B : ℝ) :
    normInt_STR02933 (fun t => deriv (pFun_STR02945 A B) t ^ 2 * pFun_STR02945 (1 + A) B t ^ 2) =
      ((A ^ 2 + B ^ 2) * ((1 + A) ^ 2 + B ^ 2) + 2 * B ^ 2) / 8 := by
  let X := 1 + A
  let E := B ^ 4 - 4 * A * B ^ 2 * X + A ^ 2 * X ^ 2
  have he (t : ℝ) : deriv (pFun_STR02945 A B) t ^ 2 * pFun_STR02945 X B t ^ 2 =
      (A ^ 2 * B ^ 2) * Real.cos t ^ 0 + (E - 2 * A ^ 2 * B ^ 2) * Real.cos t ^ 2 +
      (B ^ 2 * X ^ 2 - E + A ^ 2 * B ^ 2) * Real.cos t ^ 4 +
      0 * Real.cos t ^ 6 + 0 * Real.cos t ^ 8 +
      (2 * A * B * (A * X - B ^ 2)) * (Real.cos t ^ 1 * Real.sin t) +
      (2 * B * X * (B ^ 2 - A * X) - 2 * A * B * (A * X - B ^ 2)) * (Real.cos t ^ 3 * Real.sin t) +
      0 * (Real.cos t ^ 5 * Real.sin t) + 0 * (Real.cos t ^ 7 * Real.sin t) := by
    rw [dp_cs_STR02946, p_cs_STR02946]
    dsimp only [E]
    linear_combination ((B ^ 4 - 4 * A * B ^ 2 * X + A ^ 2 * X ^ 2) * Real.cos t ^ 2 +
      A ^ 2 * B ^ 2 * (Real.sin t ^ 2 + 1 - Real.cos t ^ 2) +
      2 * A * B * (A * X - B ^ 2) * Real.cos t * Real.sin t) * Real.sin_sq_add_cos_sq t
  rw [normInt_congr_STR02945 he, mean9_STR02946]
  dsimp only [E, X]
  ring

theorem polynomialFiniteH4_eq (A B C D : ℝ) :
    polynomialFiniteH4 A B C D =
      (C ^ 2 + D ^ 2 + (A + A ^ 2 - B ^ 2) * C + B * (1 + 2 * A) * D) / 4 -
        (3 * A ^ 2 + B ^ 2) / 32 - A * (A ^ 2 + B ^ 2) / 8 - 3 * (A ^ 2 + B ^ 2) ^ 2 / 64 := by
  unfold polynomialFiniteH4
  rw [profile_absolute_eq, profile_entropy_fourth Real.continuous_cos
    (pFun_cont_STR02945 A B) (qFun_cont_STR02945 C D 0 0) (profile_q_mean C D)]
  simp only [mom_q2_STR02946, polynomial_scaled_cos_pbq_moment, mom_p2q_STR02946,
    polynomial_scaled_cos_p2b2_moment, polynomial_scaled_cos_p3b_moment, mom_p4_STR02946,
    mom_p2_STR02946, w2_STR02946, profile_pb]
  ring

theorem polynomialFiniteI4_eq (A B C D : ℝ) :
    polynomialFiniteI4 A B C D =
      2 * (C ^ 2 + D ^ 2) + (A + 3 * (A ^ 2 - B ^ 2) / 4) * C +
        B * (1 + 3 * A / 2) * D - (A ^ 2 - B ^ 2) / 16 -
        A * (A ^ 2 + B ^ 2) / 8 - (A ^ 2 + B ^ 2) ^ 2 / 16 := by
  have he : polynomialFiniteI4 A B C D =
      normInt_STR02933 (fun t => deriv (qFun_STR02945 C D 0 0) t ^ 2) +
      2 * normInt_STR02933 (fun t => deriv (pFun_STR02945 A B) t * deriv (qFun_STR02945 C D 0 0) t *
        pFun_STR02945 (1 + A) B t) +
      normInt_STR02933 (fun t => deriv (pFun_STR02945 A B) t ^ 2 * qFun_STR02945 C D 0 0 t) +
      (1 / 2) * normInt_STR02933 (fun t => deriv (pFun_STR02945 A B) t ^ 2 * pFun_STR02945 (1 + A) B t ^ 2) -
      (1 / 2) * normInt_STR02933 (fun t => deriv (pFun_STR02945 A B) t ^ 2) *
        normInt_STR02933 (fun t => pFun_STR02945 (1 + A) B t ^ 2) := by
    exact fisher_n2_STR02945 (deriv_pFun_cont_STR02945 A B) (deriv_qFun_cont_STR02945 C D 0 0)
      (pFun_cont_STR02945 (1 + A) B) (qFun_cont_STR02945 C D 0 0) (profile_q_mean C D)
  rw [he]
  simp only [mom_qd2_STR02946, profile_pdqdv, mom_pd2q_STR02946, profile_pd2v2,
    mom_pd2_STR02946, mom_p2_STR02946]
  ring

/-- Exact evaluated coefficients and uniform error for both actual normalized
angular functionals. The independent reference parameter is zero throughout. -/
theorem polynomialFiniteProfile_information_expansion (R : ℝ) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ A B C D : ℝ, |A| ≤ R → |B| ≤ R → |C| ≤ R → |D| ≤ R → ∀ h : ℝ, |h| ≤ h0 →
        |polynomialFiniteProfileFisher A B C D h - ((A ^ 2 + B ^ 2) / 2 * h ^ 2 +
          (2 * (C ^ 2 + D ^ 2) + (A + 3 * (A ^ 2 - B ^ 2) / 4) * C +
            B * (1 + 3 * A / 2) * D - (A ^ 2 - B ^ 2) / 16 -
            A * (A ^ 2 + B ^ 2) / 8 - (A ^ 2 + B ^ 2) ^ 2 / 16) * h ^ 4)| ≤ K * |h| ^ 5 ∧
        |polynomialFiniteProfileEntropy A B C D h - ((A ^ 2 + B ^ 2) / 4 * h ^ 2 +
          ((C ^ 2 + D ^ 2 + (A + A ^ 2 - B ^ 2) * C + B * (1 + 2 * A) * D) / 4 -
            (3 * A ^ 2 + B ^ 2) / 32 - A * (A ^ 2 + B ^ 2) / 8 -
            3 * (A ^ 2 + B ^ 2) ^ 2 / 64) * h ^ 4)| ≤ K * |h| ^ 5 := by
  obtain ⟨h0, hh0, K, hK, hmain⟩ := polynomialFiniteProfile_information_expansion_raw R
  refine ⟨h0, hh0, K, hK, fun A B C D hA hB hC hD h hh => ?_⟩
  obtain ⟨_, _, _, _, hI, hH⟩ := hmain A B C D hA hB hC hD h hh
  rw [polynomialFiniteI2_eq, polynomialFiniteI3_eq_zero, polynomialFiniteI4_eq, zero_mul, add_zero] at hI
  rw [polynomialFiniteH2_eq, polynomialFiniteH3_eq_zero, polynomialFiniteH4_eq, zero_mul, add_zero] at hH
  exact ⟨hI, hH⟩

end DGPS.Examples.PolynomialSpecies
