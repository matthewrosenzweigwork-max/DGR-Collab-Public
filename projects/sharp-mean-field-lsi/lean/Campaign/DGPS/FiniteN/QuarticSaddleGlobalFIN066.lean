import DGPS.FiniteN.QuarticSaddle
import DGPS.FiniteN.AttractivePoincare
import DGPS.Examples.AttractiveXYTilt

/-!
# Quartic saddle: unique global minimum and remote state (FIN066)

For the anisotropic quartic saddle model (`κ = 5 / b`, `η = 4 / 5`): the Hamiltonian formula,
the unique nondegenerate global free-energy minimizer `q_{t₊}`, the stationary remote state
`q_{-4}` with free-energy gap at least `2b`, and the auxiliary function
`ψ(x,y) = (x-1)²/(2κ) + y²/(2κη) - log I₀(√(x²+y²))` with unique nondegenerate global minimum
`w₊ = (t₊, 0)` and critical point `w₋ = (-4, 0)`.
Main result: `DGPS.FiniteN.quartic_unique_global_minimum_and_remote_state`.
-/

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace DGPS.FiniteN.QuarticSaddleGlobalFIN066

open DGPS DGPS.Models DGPS.Examples.AttractiveXY DGPS.Examples.AttractiveXYTilt
open DGPS.Circle.BesselMoments DGPS.FiniteN.AttractiveLandscape
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselConcavity DGPS.Examples.AttractiveXYCritical

theorem scalarCos_eq_FIN066 : scalarCos = fun x => (xyMode x).re := by
  funext x; rw [xyMode_apply]; rfl

theorem scalarSin_eq_FIN066 : scalarSin = fun x => (xyMode x).im := by
  funext x; rw [xyMode_apply]; rfl

theorem hamiltonian_FIN066 (N : ℕ+) (x : DGPS.ParticleSpace 1 N) :
    DGPS.particleHamiltonian anisotropicQuarticSaddle N x =
      -(∑ i, scalarCos (x i)) - quarticKappa *
        ((∑ i, scalarCos (x i)) ^ 2 + quarticEta * (∑ i, scalarSin (x i)) ^ 2) / (2 * (N : ℝ)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have e1 : ∀ c : Fin N → ℝ, ∑ i, ∑ j, (c i - c j) ^ 2 =
      2 * (N : ℝ) * ∑ i, c i ^ 2 - 2 * (∑ i, c i) ^ 2 := by
    intro c
    have h1 : ∀ i, ∑ j, (c i - c j) ^ 2 =
        (N : ℝ) * c i ^ 2 - 2 * (∑ j, c j) * c i + ∑ j, c j ^ 2 := by
      intro i
      have : ∀ j, (c i - c j) ^ 2 = c i ^ 2 - 2 * c j * c i + c j ^ 2 := fun j => by ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      simp
    simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp
    ring
  unfold DGPS.particleHamiltonian anisotropicQuarticSaddle
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_neg_distrib, Finset.sum_add_distrib]
  rw [e1 (fun i => scalarCos (x i)), e1 (fun i => scalarSin (x i))]
  field_simp
  ring



theorem integrable_cont_FIN066 {f : Torus 1 → ℝ} (hf : Continuous f) (μ : Measure (Torus 1))
    [IsFiniteMeasure μ] : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem sqdiff_FIN066 {f : Torus 1 → ℝ} (hf : Continuous f) (μ : Measure (Torus 1))
    [IsProbabilityMeasure μ] :
    ∫ p : Torus 1 × Torus 1, (f p.1 - f p.2) ^ 2 ∂(μ.prod μ) =
      2 * (∫ x, f x ^ 2 ∂μ - (∫ x, f x ∂μ) ^ 2) := by
  have j1 : Integrable (fun p : Torus 1 × Torus 1 => f p.1 ^ 2) (μ.prod μ) :=
    (hf.comp continuous_fst |>.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have j2 : Integrable (fun p : Torus 1 × Torus 1 => f p.2 ^ 2) (μ.prod μ) :=
    (hf.comp continuous_snd |>.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have j3 : Integrable (fun p : Torus 1 × Torus 1 => f p.1 * f p.2) (μ.prod μ) :=
    ((hf.comp continuous_fst).mul (hf.comp continuous_snd)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have e : ∀ p : Torus 1 × Torus 1, (f p.1 - f p.2) ^ 2 =
      f p.1 ^ 2 + f p.2 ^ 2 - 2 * (f p.1 * f p.2) := fun p => by ring
  simp only [e]
  rw [integral_sub (f := fun p : Torus 1 × Torus 1 => f p.1 ^ 2 + f p.2 ^ 2)
    (g := fun p : Torus 1 × Torus 1 => 2 * (f p.1 * f p.2)) (j1.add j2) (j3.const_mul _),
    integral_add j1 j2, integral_const_mul, integral_prod_mul (fun x => f x) (fun x => f x)]
  have k1 : ∫ p : Torus 1 × Torus 1, f p.1 ^ 2 ∂(μ.prod μ) = ∫ x, f x ^ 2 ∂μ := by
    have := integral_prod_mul (μ := μ) (ν := μ) (fun x => f x ^ 2) (fun _ => (1 : ℝ))
    simpa using this
  have k2 : ∫ p : Torus 1 × Torus 1, f p.2 ^ 2 ∂(μ.prod μ) = ∫ x, f x ^ 2 ∂μ := by
    have := integral_prod_mul (μ := μ) (ν := μ) (fun _ => (1 : ℝ)) (fun x => f x ^ 2)
    simpa using this
  rw [k1, k2]
  ring

theorem continuous_cos_FIN066 : Continuous fun x : Torus 1 => (xyMode x).re :=
  Complex.continuous_re.comp continuous_xyMode

theorem continuous_sin_FIN066 : Continuous fun x : Torus 1 => (xyMode x).im :=
  Complex.continuous_im.comp continuous_xyMode

theorem potentialEnergy_FIN066 (μ : Measure (Torus 1)) [IsProbabilityMeasure μ] :
    DGPS.potentialEnergy anisotropicQuarticSaddle μ =
      -(∫ x, (xyMode x).re ∂μ) - quarticKappa / 2 * (∫ x, (xyMode x).re ^ 2 ∂μ +
        quarticEta * ∫ x, (xyMode x).im ^ 2 ∂μ) := by
  have i1 := integrable_cont_FIN066 continuous_cos_FIN066 μ
  have i2 : Integrable (fun x : Torus 1 => (xyMode x).re ^ 2) μ :=
    integrable_cont_FIN066 (continuous_cos_FIN066.pow 2) μ
  have i3 : Integrable (fun x : Torus 1 => (xyMode x).im ^ 2) μ :=
    integrable_cont_FIN066 (continuous_sin_FIN066.pow 2) μ
  unfold DGPS.potentialEnergy anisotropicQuarticSaddle
  simp only [scalarCos_eq_FIN066, scalarSin_eq_FIN066]
  rw [integral_sub (f := fun x : Torus 1 => -(xyMode x).re)
    (g := fun x : Torus 1 => quarticKappa / 2 * ((xyMode x).re ^ 2 + quarticEta * (xyMode x).im ^ 2))
    i1.neg ((i2.add (i3.const_mul _)).const_mul _), integral_neg,
    integral_const_mul, integral_add i2 (i3.const_mul _), integral_const_mul]

theorem interactionEnergy_FIN066 (μ : Measure (Torus 1)) [IsProbabilityMeasure μ] :
    DGPS.interactionEnergy anisotropicQuarticSaddle μ =
      quarticKappa * ((∫ x, (xyMode x).re ^ 2 ∂μ - (∫ x, (xyMode x).re ∂μ) ^ 2) +
        quarticEta * (∫ x, (xyMode x).im ^ 2 ∂μ - (∫ x, (xyMode x).im ∂μ) ^ 2)) := by
  have hc := continuous_cos_FIN066
  have hs := continuous_sin_FIN066
  have j1 : Integrable (fun p : Torus 1 × Torus 1 => ((xyMode p.1).re - (xyMode p.2).re) ^ 2)
      (μ.prod μ) :=
    (((hc.comp continuous_fst).sub (hc.comp continuous_snd)).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have j2 : Integrable (fun p : Torus 1 × Torus 1 => ((xyMode p.1).im - (xyMode p.2).im) ^ 2)
      (μ.prod μ) :=
    (((hs.comp continuous_fst).sub (hs.comp continuous_snd)).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold DGPS.interactionEnergy anisotropicQuarticSaddle
  simp only [scalarCos_eq_FIN066, scalarSin_eq_FIN066]
  rw [integral_const_mul, integral_add j1 (j2.const_mul _), integral_const_mul,
    sqdiff_FIN066 hc, sqdiff_FIN066 hs]
  ring

theorem freeEnergy_FIN066 (ν : ProbabilityMeasure (Torus 1)) :
    DGPS.freeEnergy anisotropicQuarticSaddle ν =
      ((DGPS.relativeEntropy (ν : Measure (Torus 1)) (DGPS.haar 1) : ℝ≥0∞) : EReal) +
        ((-xyZ1 (ν : Measure (Torus 1)) - quarticKappa / 2 *
          (xyZ1 (ν : Measure (Torus 1)) ^ 2 + quarticEta * xyZ2 (ν : Measure (Torus 1)) ^ 2) : ℝ) :
          EReal) := by
  unfold DGPS.freeEnergy
  rw [potentialEnergy_FIN066, interactionEnergy_FIN066, add_assoc, ← EReal.coe_add]
  congr 2
  simp only [xyZ1, xyZ2]
  ring



theorem quarticKappa_pos_FIN066 : 0 < quarticKappa := by
  have hb := DGPS.FiniteN.QuarticSaddle.quarticB_gt
  have hbpos : 0 < quarticB := lt_trans (by norm_num) hb
  unfold quarticKappa
  positivity

theorem quarticEta_FIN066 : quarticEta = 4 / 5 := rfl

/-- The offset between the quartic and the XY free energies. -/
noncomputable def offset_FIN066 (ν : ProbabilityMeasure (Torus 1)) : ℝ :=
  -quarticKappa / 2 + quarticKappa * (1 - quarticEta) / 2 * xyZ2 (ν : Measure (Torus 1)) ^ 2

theorem offset_ge_FIN066 (ν : ProbabilityMeasure (Torus 1)) :
    -quarticKappa / 2 ≤ offset_FIN066 ν := by
  have hk := quarticKappa_pos_FIN066
  have : 0 ≤ quarticKappa * (1 - quarticEta) / 2 * xyZ2 (ν : Measure (Torus 1)) ^ 2 := by
    rw [quarticEta_FIN066]; positivity
  unfold offset_FIN066; linarith

theorem freeEnergy_cmp_FIN066 (ν : ProbabilityMeasure (Torus 1)) :
    DGPS.freeEnergy anisotropicQuarticSaddle ν =
      DGPS.freeEnergy (attractiveXY quarticKappa 1) ν + ((offset_FIN066 ν : ℝ) : EReal) := by
  rw [freeEnergy_FIN066, freeEnergy_attractiveXY, add_assoc, ← EReal.coe_add]
  congr 2
  unfold offset_FIN066
  ring

theorem ereal_add_coe_FIN066 {x : EReal} {e r : ℝ} (h : x + (e : EReal) = (r : EReal)) :
    x = ((r - e : ℝ) : EReal) := by
  induction x using EReal.rec with
  | bot => simp at h
  | top => simp at h
  | coe a =>
    rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at h
    rw [EReal.coe_eq_coe_iff]; linarith

theorem offset_law_FIN066 (t : ℝ) : offset_FIN066 (xyLaw_EX023 t) = -quarticKappa / 2 := by
  unfold offset_FIN066
  rw [law_sin_EX023]; ring

/-- The free-energy minimum of the quartic model. -/
theorem minimum_FIN066 :
    DGPS.freeEnergyMinimum anisotropicQuarticSaddle =
      ((DGPS.freeEnergyMinimumReal (attractiveXY quarticKappa 1) - quarticKappa / 2 : ℝ) :
        EReal) := by
  have hk := quarticKappa_pos_FIN066
  have hco := DGPS.coe_freeEnergyMinimumReal (attractiveXY quarticKappa 1)
  obtain ⟨-, -, t, ht, he, hu, -, -, -, hiff, -⟩ :=
    DGPS.Examples.tilted_stationary_scalar_root_and_global_minimizer (κ := quarticKappa) (h := 1) hk.le one_pos
  apply le_antisymm
  · calc DGPS.freeEnergyMinimum anisotropicQuarticSaddle
        ≤ DGPS.freeEnergy anisotropicQuarticSaddle (xyLaw_EX023 t) := iInf_le _ _
      _ = _ := by
        rw [freeEnergy_cmp_FIN066, offset_law_FIN066, (hiff _).2 rfl, ← hco, ← EReal.coe_add]
        congr 1; ring
  · refine le_iInf fun ν => ?_
    rw [freeEnergy_cmp_FIN066]
    have h1 : ((DGPS.freeEnergyMinimumReal (attractiveXY quarticKappa 1) : ℝ) : EReal) ≤
        DGPS.freeEnergy (attractiveXY quarticKappa 1) ν := by
      rw [hco]; exact iInf_le _ _
    have h2 : ((-quarticKappa / 2 : ℝ) : EReal) ≤ ((offset_FIN066 ν : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.2 (offset_ge_FIN066 ν)
    have h3 := add_le_add h1 h2
    rw [← EReal.coe_add] at h3
    refine le_trans (le_of_eq ?_) h3
    congr 1; ring



theorem global_minimizer_FIN066 :
    ∃ t : ℝ, 1 < t ∧ t = 1 + quarticKappa * besselRatio t ∧
      (∀ u : ℝ, 0 < u → u = 1 + quarticKappa * besselRatio u → u = t) ∧
      ∀ ν : ProbabilityMeasure (Torus 1),
        DGPS.freeEnergy anisotropicQuarticSaddle ν = DGPS.freeEnergyMinimum anisotropicQuarticSaddle ↔
          ν = xyLaw_EX023 t := by
  have hk := quarticKappa_pos_FIN066
  have hco := DGPS.coe_freeEnergyMinimumReal (attractiveXY quarticKappa 1)
  obtain ⟨-, -, t, ht, he, hu, -, -, hbs, hiff, -⟩ :=
    DGPS.Examples.tilted_stationary_scalar_root_and_global_minimizer (κ := quarticKappa) (h := 1)
      hk.le one_pos
  refine ⟨t, (hbs hk).1, by linarith, fun u hu0 hue => hu u hu0 (by linarith), fun ν => ?_⟩
  rw [minimum_FIN066]
  constructor
  · intro h
    rw [freeEnergy_cmp_FIN066] at h
    have h1 := ereal_add_coe_FIN066 h
    have h2 : ((DGPS.freeEnergyMinimumReal (attractiveXY quarticKappa 1) : ℝ) : EReal) ≤
        DGPS.freeEnergy (attractiveXY quarticKappa 1) ν := by
      rw [hco]; exact iInf_le _ _
    have h3 := offset_ge_FIN066 ν
    rw [h1, EReal.coe_le_coe_iff] at h2
    have h4 : DGPS.freeEnergy (attractiveXY quarticKappa 1) ν =
        DGPS.freeEnergyMinimum (attractiveXY quarticKappa 1) := by
      rw [h1, ← hco, EReal.coe_eq_coe_iff]; linarith
    exact (hiff ν).1 h4
  · rintro rfl
    rw [freeEnergy_cmp_FIN066, offset_law_FIN066, (hiff _).2 rfl, ← hco, ← EReal.coe_add]
    congr 1; ring

theorem remote_neg_four_FIN066 : (-4 : ℝ) = 1 + quarticKappa * besselRatio (-4) := by
  have hb := DGPS.FiniteN.QuarticSaddle.quarticB_gt
  have hbpos : 0 < quarticB := lt_trans (by norm_num) hb
  rw [besselRatio_neg]
  have : quarticKappa * quarticB = 5 := by
    unfold quarticKappa; field_simp
  change (-4 : ℝ) = 1 + quarticKappa * (-quarticB)
  linarith

theorem remote_gap_FIN066 :
    ((2 * quarticB : ℝ) : EReal) ≤
      DGPS.freeEnergy anisotropicQuarticSaddle (xyLaw_EX023 (-4)) -
        DGPS.freeEnergyMinimum anisotropicQuarticSaddle := by
  have hk := quarticKappa_pos_FIN066
  have hco := DGPS.coe_freeEnergyMinimumReal (attractiveXY quarticKappa 1)
  have hg := (DGPS.Examples.AttractiveXYTilt.negative_gap_EX023 (κ := quarticKappa) (h := 1)
    one_pos (s := 4) (by norm_num)).1
  rw [opposite_energy_EX023, law_freeEnergy_EX023, ← hco] at hg
  rw [freeEnergy_cmp_FIN066, offset_law_FIN066, minimum_FIN066, opposite_energy_EX023,
    law_freeEnergy_EX023, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff]
  rw [← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hg
  have hb : quarticB = besselRatio 4 := rfl
  rw [hb]
  linarith



/-- the feature map -/
noncomputable def featU_FIN066 : Torus 1 → ℝ := fun x => -(xyMode x).re

noncomputable def featPhi_FIN066 : Torus 1 → Feature 2 := fun x =>
  !₂[Real.sqrt quarticKappa * (xyMode x).re, Real.sqrt (quarticKappa * quarticEta) * (xyMode x).im]

theorem continuous_U_FIN066 : Continuous featU_FIN066 :=
  continuous_cos_FIN066.neg

theorem continuous_Phi_FIN066 : Continuous featPhi_FIN066 := by
  have := continuous_cos_FIN066
  have := continuous_sin_FIN066
  unfold featPhi_FIN066
  fun_prop

theorem norm_sq_Phi_FIN066 (x : Torus 1) :
    ‖featPhi_FIN066 x‖ ^ 2 = quarticKappa * ((xyMode x).re ^ 2 + quarticEta * (xyMode x).im ^ 2) := by
  have hk := quarticKappa_pos_FIN066
  have hη : 0 ≤ quarticEta := by rw [quarticEta_FIN066]; norm_num
  rw [featPhi_FIN066, EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  simp
  rw [mul_pow, mul_pow, Real.sq_sqrt hk.le, Real.sq_sqrt (mul_nonneg hk.le hη)]
  ring

theorem norm_Phi_le_FIN066 (x : Torus 1) :
    ‖featPhi_FIN066 x‖ ≤ Real.sqrt (quarticKappa * (1 + quarticEta)) := by
  have hk := quarticKappa_pos_FIN066
  have hη : 0 ≤ quarticEta := by rw [quarticEta_FIN066]; norm_num
  have hn := xyMode_norm x
  have h1 := abs_xyMode_re_le x
  have h2 := abs_xyMode_im_le x
  refine (Real.le_sqrt (norm_nonneg _) (mul_nonneg hk.le (by linarith))).2 ?_
  rw [norm_sq_Phi_FIN066]
  have a1 : (xyMode x).re ^ 2 ≤ 1 := by nlinarith [abs_nonneg (xyMode x).re, sq_abs (xyMode x).re]
  have a2 : (xyMode x).im ^ 2 ≤ 1 := by nlinarith [abs_nonneg (xyMode x).im, sq_abs (xyMode x).im]
  apply mul_le_mul_of_nonneg_left _ hk.le
  nlinarith [mul_le_mul_of_nonneg_left a2 hη]

theorem norm_sq_Phi_sub_FIN066 (x y : Torus 1) :
    ‖featPhi_FIN066 x - featPhi_FIN066 y‖ ^ 2 = quarticKappa *
      (((xyMode x).re - (xyMode y).re) ^ 2 + quarticEta * ((xyMode x).im - (xyMode y).im) ^ 2) := by
  have hk := quarticKappa_pos_FIN066
  have hη : 0 ≤ quarticEta := by rw [quarticEta_FIN066]; norm_num
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  simp [featPhi_FIN066]
  rw [← mul_sub, ← mul_sub, mul_pow, mul_pow, Real.sq_sqrt hk.le, Real.sq_sqrt (mul_nonneg hk.le hη)]
  ring

theorem attractive_eq_FIN066 :
    attractiveData continuous_U_FIN066 continuous_Phi_FIN066 = anisotropicQuarticSaddle := by
  have hV : ∀ x, (attractiveData continuous_U_FIN066 continuous_Phi_FIN066).V x =
      anisotropicQuarticSaddle.V x := by
    intro x
    show featU_FIN066 x - ‖featPhi_FIN066 x‖ ^ 2 / 2 = _
    rw [norm_sq_Phi_FIN066]
    simp only [anisotropicQuarticSaddle, featU_FIN066, scalarCos_eq_FIN066, scalarSin_eq_FIN066]
    ring
  have hW : ∀ x y, (attractiveData continuous_U_FIN066 continuous_Phi_FIN066).W x y =
      anisotropicQuarticSaddle.W x y := by
    intro x y
    show ‖featPhi_FIN066 x - featPhi_FIN066 y‖ ^ 2 / 2 = _
    rw [norm_sq_Phi_sub_FIN066]
    simp only [anisotropicQuarticSaddle, scalarCos_eq_FIN066, scalarSin_eq_FIN066]
    ring
  cases h1 : attractiveData continuous_U_FIN066 continuous_Phi_FIN066 with
  | mk V W a b c d =>
    cases h2 : anisotropicQuarticSaddle with
    | mk V' W' a' b' c' d' =>
      rw [h1] at hV hW
      rw [h2] at hV hW
      have e1 : V = V' := funext hV
      have e2 : W = W' := funext fun x => funext (hW x)
      subst e1; subst e2; rfl

theorem inner_Phi_FIN066 (z : Feature 2) (x : Torus 1) :
    ⟪z, featPhi_FIN066 x⟫ - featU_FIN066 x =
      xyTrig (1 + Real.sqrt quarticKappa * z 0) (Real.sqrt (quarticKappa * quarticEta) * z 1) 0 x := by
  simp [featPhi_FIN066, featU_FIN066, xyTrig, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem gibbs_eq_FIN066 (z : Feature 2) :
    gibbs featU_FIN066 featPhi_FIN066 z =
      (xyBivariateLaw_EX023 (1 + Real.sqrt quarticKappa * z 0)
        (Real.sqrt (quarticKappa * quarticEta) * z 1) : Measure (Torus 1)) := by
  unfold gibbs xyBivariateLaw_EX023
  simp only [inner_Phi_FIN066]
  rfl

theorem zeta_eq_FIN066 (z : Feature 2) :
    zeta featU_FIN066 featPhi_FIN066 z =
      xyPartition (1 + Real.sqrt quarticKappa * z 0) (Real.sqrt (quarticKappa * quarticEta) * z 1) := by
  unfold zeta xyPartition
  simp only [inner_Phi_FIN066]

theorem partition_rot_FIN066 (a b : ℝ) :
    xyPartition a b = besselI 0 (Real.sqrt (a ^ 2 + b ^ 2)) := by
  rcases (add_nonneg (sq_nonneg a) (sq_nonneg b)).eq_or_lt with h | h
  · have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    subst ha; subst hb
    simpa using partition_EX023 0
  · have := DGPS.Examples.AttractiveXYCritical.integral_exp_rot_xyc (a / 2) (b / 2) (by nlinarith)
    have e1 : (2 : ℝ) * Real.sqrt ((a / 2) ^ 2 + (b / 2) ^ 2) = Real.sqrt (a ^ 2 + b ^ 2) := by
      have : (a / 2) ^ 2 + (b / 2) ^ 2 = (a ^ 2 + b ^ 2) / 4 := by ring
      rw [this, Real.sqrt_div (by positivity), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
      ring
    rw [e1] at this
    rw [← this]
    unfold xyPartition xyTrig
    congr 1
    funext x
    congr 1
    ring

/-- The auxiliary function `ψ(x,y) = (x-1)²/(2κ) + y²/(2κη) - log I₀(√(x²+y²))`. -/
noncomputable def quarticPsi_FIN066 (w : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (w 0 - 1) ^ 2 / (2 * quarticKappa) + (w 1) ^ 2 / (2 * (quarticKappa * quarticEta)) -
    Real.log (besselI 0 (Real.sqrt (w 0 ^ 2 + w 1 ^ 2)))

noncomputable def amap_FIN066 (w : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[(w 0 - 1) / Real.sqrt quarticKappa, w 1 / Real.sqrt (quarticKappa * quarticEta)]

theorem kappa_eta_pos_FIN066 : 0 < quarticKappa * quarticEta := by
  have := quarticKappa_pos_FIN066
  rw [quarticEta_FIN066]; positivity

theorem psi_amap_FIN066 (w : EuclideanSpace ℝ (Fin 2)) :
    psi featU_FIN066 featPhi_FIN066 (amap_FIN066 w) = quarticPsi_FIN066 w := by
  have hk := quarticKappa_pos_FIN066
  have hke := kappa_eta_pos_FIN066
  unfold psi quarticPsi_FIN066
  rw [zeta_eq_FIN066, partition_rot_FIN066, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  have e0 : 1 + Real.sqrt quarticKappa * (amap_FIN066 w) 0 = w 0 := by
    simp [amap_FIN066]; field_simp; ring
  have e1 : Real.sqrt (quarticKappa * quarticEta) * (amap_FIN066 w) 1 = w 1 := by
    simp [amap_FIN066]; field_simp
  rw [e0, e1]
  congr 1
  simp [amap_FIN066, Fin.sum_univ_two, div_pow, Real.sq_sqrt hk.le, Real.sq_sqrt hke.le]
  field_simp

theorem law_cos_sq_FIN066 {t : ℝ} (ht : t ≠ 0) :
    ∫ x, ((xyMode x).re) ^ 2 ∂(xyLaw_EX023 t : Measure (Torus 1)) =
      1 - besselRatio t / t := by
  rw [law_integral_EX023]
  simp_rw [xyMode_re_eq_angCos_xyc]
  rw [integral_comp_angEquiv (fun θ => Real.exp (t * angCos θ) / besselI 0 t * angCos θ ^ 2)]
  have e := besselI2Moment_eq t
  unfold besselI2Moment at e
  have hE := (besselI_zero_pos t).ne'
  have : ∀ θ : AngCircle, Real.exp (t * angCos θ) / besselI 0 t * angCos θ ^ 2 =
      (besselI 0 t)⁻¹ * (angCos θ * Real.exp (t * angCos θ) * angCos θ) := by
    intro θ; field_simp
  simp_rw [this]
  rw [integral_const_mul, e, ratio_div_eq t ht]
  field_simp

theorem law_odd_FIN066 (t : ℝ) (G : ℝ → ℝ) :
    ∫ x, G (xyMode x).re * (xyMode x).im ∂(xyLaw_EX023 t : Measure (Torus 1)) = 0 := by
  have : (haar 1).IsNegInvariant := Pi.isNegInvariant_volume
  rw [law_integral_EX023]
  have hi := integral_neg_eq_self (fun x : Torus 1 =>
    Real.exp (t * (xyMode x).re) / besselI 0 t * (G (xyMode x).re * (xyMode x).im)) (haar 1)
  simp only [mode_neg_EX023, Complex.conj_re, Complex.conj_im, mul_neg, integral_neg] at hi
  linarith

theorem im_sq_FIN066 (x : Torus 1) : (xyMode x).im ^ 2 = 1 - (xyMode x).re ^ 2 := by
  have h := xyMode_norm x
  have h2 : (xyMode x).re * (xyMode x).re + (xyMode x).im * (xyMode x).im = 1 := by
    have := Complex.sq_norm (xyMode x)
    rw [h, Complex.normSq_apply] at this
    linarith
  nlinarith

theorem m_ss_FIN066 {t : ℝ} (ht : t ≠ 0) :
    ∫ x, (xyMode x).im ^ 2 ∂(xyLaw_EX023 t : Measure (Torus 1)) = besselRatio t / t := by
  simp_rw [im_sq_FIN066]
  have hi : Integrable (fun x => (xyMode x).re ^ 2) (xyLaw_EX023 t : Measure (Torus 1)) :=
    integrable_cont_FIN066 ((Complex.continuous_re.comp continuous_xyMode).pow 2) _
  rw [integral_sub (integrable_const _) hi, law_cos_sq_FIN066 ht]
  simp

theorem measureMean_xyLaw_FIN066 (t : ℝ) :
    measureMean featPhi_FIN066 (xyLaw_EX023 t : Measure (Torus 1)) =
      !₂[Real.sqrt quarticKappa * besselRatio t, 0] := by
  have hint : Integrable featPhi_FIN066 (xyLaw_EX023 t : Measure (Torus 1)) :=
    integrable_feature _ continuous_Phi_FIN066
  have h0 := (EuclideanSpace.proj (0 : Fin 2)).integral_comp_comm hint
  have h1 := (EuclideanSpace.proj (1 : Fin 2)).integral_comp_comm hint
  unfold measureMean
  ext i
  fin_cases i
  · have : ∫ x, (featPhi_FIN066 x) 0 ∂(xyLaw_EX023 t : Measure (Torus 1)) = Real.sqrt quarticKappa * besselRatio t := by
      simp only [featPhi_FIN066]
      simp
      have hc := law_cos_EX023 t
      rw [xyZ1] at hc
      rw [integral_const_mul, hc]
    simpa [this] using h0.symm
  · have : ∫ x, (featPhi_FIN066 x) 1 ∂(xyLaw_EX023 t : Measure (Torus 1)) = 0 := by
      simp only [featPhi_FIN066]
      simp
      rw [integral_const_mul]
      have := law_sin_EX023 t
      rw [xyZ2] at this
      rw [this, mul_zero]
    simpa [this] using h1.symm

noncomputable def zOf_FIN066 (t : ℝ) : Feature 2 := !₂[(t - 1) / Real.sqrt quarticKappa, 0]

theorem gibbs_zOf_FIN066 (t : ℝ) :
    gibbs featU_FIN066 featPhi_FIN066 (zOf_FIN066 t) = (xyLaw_EX023 t : Measure (Torus 1)) := by
  have hk := quarticKappa_pos_FIN066
  rw [gibbs_eq_FIN066]
  have e0 : 1 + Real.sqrt quarticKappa * (zOf_FIN066 t) 0 = t := by
    simp [zOf_FIN066]; field_simp; ring
  have e1 : Real.sqrt (quarticKappa * quarticEta) * (zOf_FIN066 t) 1 = 0 := by
    simp [zOf_FIN066]
  rw [e0, e1]
  rfl

theorem featureMean_zOf_FIN066 (t : ℝ) :
    featureMean featU_FIN066 featPhi_FIN066 (zOf_FIN066 t) =
      !₂[Real.sqrt quarticKappa * besselRatio t, 0] := by
  rw [featureMean_eq_measureMean, gibbs_zOf_FIN066, measureMean_xyLaw_FIN066]

theorem featureCov_zOf_FIN066 {t : ℝ} (ht : t ≠ 0) (v : Feature 2) :
    featureCov featU_FIN066 featPhi_FIN066 (zOf_FIN066 t) v v =
      quarticKappa * (1 - besselRatio t / t - besselRatio t ^ 2) * (v 0) ^ 2 +
        quarticKappa * quarticEta * (besselRatio t / t) * (v 1) ^ 2 := by
  have hk := quarticKappa_pos_FIN066
  have hke := kappa_eta_pos_FIN066
  rw [featureCov_eq_gibbs continuous_U_FIN066 continuous_Phi_FIN066, featureMean_zOf_FIN066,
    gibbs_zOf_FIN066]
  have hin : ∀ x, ⟪v, featPhi_FIN066 x⟫ * ⟪v, featPhi_FIN066 x⟫ =
      (quarticKappa * (v 0) ^ 2) * (xyMode x).re ^ 2 +
      (2 * (v 0 * v 1 * Real.sqrt quarticKappa * Real.sqrt (quarticKappa * quarticEta))) *
        ((xyMode x).re * (xyMode x).im) +
      (quarticKappa * quarticEta * (v 1) ^ 2) * (xyMode x).im ^ 2 := by
    intro x
    have a := Real.mul_self_sqrt hk.le
    have b := Real.mul_self_sqrt hke.le
    simp only [featPhi_FIN066, PiLp.inner_apply, Fin.sum_univ_two]
    simp
    calc _ = (Real.sqrt quarticKappa * Real.sqrt quarticKappa) * (v 0) ^ 2 * (xyMode x).re ^ 2 +
        2 * (v 0 * v 1 * Real.sqrt quarticKappa * Real.sqrt (quarticKappa * quarticEta)) *
          ((xyMode x).re * (xyMode x).im) +
        (Real.sqrt (quarticKappa * quarticEta) * Real.sqrt (quarticKappa * quarticEta)) *
          (v 1) ^ 2 * (xyMode x).im ^ 2 := by ring
      _ = _ := by rw [a, b]
  simp_rw [hin]
  have i1 : Integrable (fun x : Torus 1 => (xyMode x).re ^ 2) (xyLaw_EX023 t : Measure (Torus 1)) :=
    integrable_cont_FIN066 (continuous_cos_FIN066.pow 2) _
  have i2 : Integrable (fun x : Torus 1 => (xyMode x).re * (xyMode x).im)
      (xyLaw_EX023 t : Measure (Torus 1)) :=
    integrable_cont_FIN066 (continuous_cos_FIN066.mul continuous_sin_FIN066) _
  have i3 : Integrable (fun x : Torus 1 => (xyMode x).im ^ 2) (xyLaw_EX023 t : Measure (Torus 1)) :=
    integrable_cont_FIN066 (continuous_sin_FIN066.pow 2) _
  set A := quarticKappa * (v 0) ^ 2
  set B := 2 * (v 0 * v 1 * Real.sqrt quarticKappa * Real.sqrt (quarticKappa * quarticEta))
  set C := quarticKappa * quarticEta * (v 1) ^ 2
  have i12 : Integrable (fun x : Torus 1 => A * (xyMode x).re ^ 2 + B * ((xyMode x).re * (xyMode x).im))
      (xyLaw_EX023 t : Measure (Torus 1)) := (i1.const_mul A).add (i2.const_mul B)
  have i3' : Integrable (fun x : Torus 1 => C * (xyMode x).im ^ 2)
      (xyLaw_EX023 t : Measure (Torus 1)) := i3.const_mul C
  rw [integral_add i12 i3', integral_add (i1.const_mul A) (i2.const_mul B), integral_const_mul,
    integral_const_mul, integral_const_mul, law_cos_sq_FIN066 ht, m_ss_FIN066 ht]
  have h0 : ∫ x, (xyMode x).re * (xyMode x).im ∂(xyLaw_EX023 t : Measure (Torus 1)) = 0 :=
    law_odd_FIN066 t (fun y => y)
  rw [h0]
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  have a := Real.mul_self_sqrt hk.le
  have e : Real.sqrt quarticKappa * besselRatio t * v 0 * (Real.sqrt quarticKappa * besselRatio t * v 0)
      = (Real.sqrt quarticKappa * Real.sqrt quarticKappa) * besselRatio t ^ 2 * (v 0) ^ 2 := by ring
  rw [e, a]
  simp only [A, C]
  ring

theorem hessian_coercive_FIN066 {t : ℝ} (ht1 : 1 < t)
    (hroot : t = 1 + quarticKappa * besselRatio t) (v : Feature 2) :
    (1 / t) * ‖v‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (psi featU_FIN066 featPhi_FIN066)) (zOf_FIN066 t) v v := by
  have hk := quarticKappa_pos_FIN066
  have ht0 : 0 < t := by linarith
  rw [hessian_psi continuous_U_FIN066 continuous_Phi_FIN066, featureCov_zOf_FIN066 ht0.ne',
    real_inner_self_eq_norm_sq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  have hg : 0 < besselRatio t := DGPS.Circle.BesselMonotonicity.besselRatio_pos t ht0
  have hd : ratioDeriv t = 1 - besselRatio t / t - besselRatio t ^ 2 := by
    unfold ratioDeriv; rw [ratio_div_eq t ht0.ne']
  have hlt := ratioDeriv_lt_div t ht0
  have hκg : quarticKappa * besselRatio t = t - 1 := by linarith
  have h1 : quarticKappa * (1 - besselRatio t / t - besselRatio t ^ 2) < (t - 1) / t := by
    rw [← hd]
    calc quarticKappa * ratioDeriv t < quarticKappa * (besselRatio t / t) :=
          mul_lt_mul_of_pos_left hlt hk
      _ = (t - 1) / t := by rw [← hκg]; ring
  have h2 : quarticKappa * quarticEta * (besselRatio t / t) ≤ (t - 1) / t := by
    have hη : quarticEta ≤ 1 := by rw [quarticEta_FIN066]; norm_num
    have : quarticKappa * quarticEta * (besselRatio t / t) = quarticEta * ((t - 1) / t) := by
      rw [← hκg]; ring
    rw [this]
    have : 0 ≤ (t - 1) / t := div_nonneg (by linarith) ht0.le
    nlinarith
  have e : 1 - (t - 1) / t = 1 / t := by field_simp; ring
  have s0 := sq_nonneg (v 0)
  have s1 := sq_nonneg (v 1)
  nlinarith [mul_le_mul_of_nonneg_right h1.le s0, mul_le_mul_of_nonneg_right h2 s1]

noncomputable def Alin_FIN066 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v =>
        !₂[v 0 / Real.sqrt quarticKappa, v 1 / Real.sqrt (quarticKappa * quarticEta)]
      map_add' := by
        intro x y; ext i; fin_cases i <;> simp [add_div]
      map_smul' := by
        intro c x; ext i; fin_cases i <;> simp [mul_div_assoc] }

theorem Alin_apply_FIN066 (v : EuclideanSpace ℝ (Fin 2)) :
    Alin_FIN066 v = !₂[v 0 / Real.sqrt quarticKappa, v 1 / Real.sqrt (quarticKappa * quarticEta)] :=
  rfl

theorem amap_eq_FIN066 (w : EuclideanSpace ℝ (Fin 2)) :
    amap_FIN066 w = Alin_FIN066 w + !₂[-1 / Real.sqrt quarticKappa, 0] := by
  ext i; fin_cases i <;> simp [amap_FIN066, Alin_apply_FIN066, sub_eq_add_neg, add_div]

theorem hasFDerivAt_amap_FIN066 (w : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt amap_FIN066 Alin_FIN066 w := by
  have : amap_FIN066 = fun w => Alin_FIN066 w + !₂[-1 / Real.sqrt quarticKappa, 0] :=
    funext amap_eq_FIN066
  rw [this]
  exact Alin_FIN066.hasFDerivAt.add_const _

theorem quarticPsi_eq_FIN066 :
    quarticPsi_FIN066 = psi featU_FIN066 featPhi_FIN066 ∘ amap_FIN066 :=
  funext fun w => (psi_amap_FIN066 w).symm

theorem fderiv_quarticPsi_FIN066 (w : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ quarticPsi_FIN066 w =
      (fderiv ℝ (psi featU_FIN066 featPhi_FIN066) (amap_FIN066 w)).comp Alin_FIN066 := by
  rw [quarticPsi_eq_FIN066]
  have hd : DifferentiableAt ℝ (psi featU_FIN066 featPhi_FIN066) (amap_FIN066 w) :=
    ((contDiff_psi_infty continuous_U_FIN066 continuous_Phi_FIN066).differentiable
      (by simp)).differentiableAt
  exact (hd.hasFDerivAt.comp w (hasFDerivAt_amap_FIN066 w)).fderiv

theorem hessian_quarticPsi_FIN066 (w v : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fderiv ℝ quarticPsi_FIN066) w v v =
      fderiv ℝ (fderiv ℝ (psi featU_FIN066 featPhi_FIN066)) (amap_FIN066 w)
        (Alin_FIN066 v) (Alin_FIN066 v) := by
  set R : (EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) ℝ).flip
      Alin_FIN066 with hR
  have e : fderiv ℝ quarticPsi_FIN066 =
      fun w => R (fderiv ℝ (psi featU_FIN066 featPhi_FIN066) (amap_FIN066 w)) := by
    funext w
    rw [fderiv_quarticPsi_FIN066]
    rfl
  have hdd : Differentiable ℝ (fderiv ℝ (psi featU_FIN066 featPhi_FIN066)) :=
    ((contDiff_psi_infty continuous_U_FIN066 continuous_Phi_FIN066).fderiv_right
      (m := 1) (by simp)).differentiable (by simp)
  have h1 := R.hasFDerivAt.comp w ((hdd (amap_FIN066 w)).hasFDerivAt.comp w
    (hasFDerivAt_amap_FIN066 w))
  rw [e]
  have h2 := h1.fderiv
  simp only [Function.comp_def] at h2
  rw [h2]
  rfl

theorem amapRoot_FIN066 (t : ℝ) : amap_FIN066 !₂[t, 0] = zOf_FIN066 t := by
  ext i; fin_cases i <;> simp [amap_FIN066, zOf_FIN066]

theorem featureMeanRoot_FIN066 {t : ℝ} (hroot : t = 1 + quarticKappa * besselRatio t) :
    featureMean featU_FIN066 featPhi_FIN066 (zOf_FIN066 t) = zOf_FIN066 t := by
  have hk := quarticKappa_pos_FIN066
  have hs : 0 < Real.sqrt quarticKappa := Real.sqrt_pos.2 hk
  have a := Real.mul_self_sqrt hk.le
  have h : Real.sqrt quarticKappa * besselRatio t = (t - 1) / Real.sqrt quarticKappa := by
    rw [eq_div_iff hs.ne']
    calc Real.sqrt quarticKappa * besselRatio t * Real.sqrt quarticKappa
        = (Real.sqrt quarticKappa * Real.sqrt quarticKappa) * besselRatio t := by ring
      _ = t - 1 := by rw [a]; linarith
  rw [featureMean_zOf_FIN066]
  ext i; fin_cases i <;> simp [zOf_FIN066, h]

theorem criticalRoot_FIN066 {t : ℝ} (hroot : t = 1 + quarticKappa * besselRatio t) :
    fderiv ℝ (psi featU_FIN066 featPhi_FIN066) (zOf_FIN066 t) = 0 :=
  (fderiv_psi_eq_zero_iff continuous_U_FIN066 continuous_Phi_FIN066 _).2
    (featureMeanRoot_FIN066 hroot)

theorem critical_quarticPsi_FIN066 {t : ℝ} (hroot : t = 1 + quarticKappa * besselRatio t) :
    fderiv ℝ quarticPsi_FIN066 !₂[t, 0] = 0 := by
  rw [fderiv_quarticPsi_FIN066, amapRoot_FIN066, criticalRoot_FIN066 hroot]
  exact ContinuousLinearMap.zero_comp _

theorem gibbsPM_zOf_FIN066 (t : ℝ) :
    gibbsPM continuous_U_FIN066 continuous_Phi_FIN066 (zOf_FIN066 t) = xyLaw_EX023 t :=
  Subtype.ext (gibbs_zOf_FIN066 t)

theorem fixedPointRoot_FIN066 {t : ℝ} (hroot : t = 1 + quarticKappa * besselRatio t) :
    (xyLaw_EX023 t : Measure (Torus 1)) =
      DGPS.Lipschitz.gibbsMeasure anisotropicQuarticSaddle (xyLaw_EX023 t : Measure (Torus 1)) := by
  have h := isStationaryFixedPoint_gibbs_of_critical continuous_U_FIN066 continuous_Phi_FIN066
    (criticalRoot_FIN066 hroot)
  rw [gibbsPM_zOf_FIN066] at h
  unfold IsStationaryFixedPoint at h
  rw [attractive_eq_FIN066] at h
  exact h

theorem isMinimizer_FIN066 {t : ℝ}
    (h : ∀ ν : ProbabilityMeasure (Torus 1),
      DGPS.freeEnergy anisotropicQuarticSaddle ν = DGPS.freeEnergyMinimum anisotropicQuarticSaddle ↔
        ν = xyLaw_EX023 t) :
    IsFreeEnergyMinimizer continuous_U_FIN066 continuous_Phi_FIN066 (xyLaw_EX023 t) := by
  intro ν
  rw [attractive_eq_FIN066, (h _).2 rfl]
  exact iInf_le _ ν

theorem minimizer_unique_FIN066 {t : ℝ}
    (h : ∀ ν : ProbabilityMeasure (Torus 1),
      DGPS.freeEnergy anisotropicQuarticSaddle ν = DGPS.freeEnergyMinimum anisotropicQuarticSaddle ↔
        ν = xyLaw_EX023 t)
    (ν : ProbabilityMeasure (Torus 1))
    (hν : IsFreeEnergyMinimizer continuous_U_FIN066 continuous_Phi_FIN066 ν) : ν = xyLaw_EX023 t := by
  apply (h ν).1
  apply le_antisymm
  · have := hν (xyLaw_EX023 t)
    rw [attractive_eq_FIN066, (h _).2 rfl] at this
    exact this
  · exact iInf_le _ ν

theorem coercive_FIN066 {t : ℝ} (ht1 : 1 < t) (hroot : t = 1 + quarticKappa * besselRatio t) :
    IsCoerciveDensityHessian anisotropicQuarticSaddle (xyLaw_EX023 t) := by
  have ht0 : 0 < t := by linarith
  have h := (coercive_hessian_iff continuous_U_FIN066 continuous_Phi_FIN066 (zOf_FIN066 t)).1
    ⟨1 / t, by positivity, hessian_coercive_FIN066 ht1 hroot⟩
  rw [gibbsPM_zOf_FIN066, attractive_eq_FIN066] at h
  exact h

theorem norm_Alin_FIN066 (v : EuclideanSpace ℝ (Fin 2)) :
    ‖v‖ ^ 2 / quarticKappa ≤ ‖Alin_FIN066 v‖ ^ 2 := by
  have hk := quarticKappa_pos_FIN066
  have hke := kappa_eta_pos_FIN066
  rw [Alin_apply_FIN066, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [div_pow, div_pow, Real.sq_sqrt hk.le, Real.sq_sqrt hke.le]
  have hη : quarticEta ≤ 1 := by rw [quarticEta_FIN066]; norm_num
  have h1 : (v 1) ^ 2 / quarticKappa ≤ (v 1) ^ 2 / (quarticKappa * quarticEta) := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) hke
    nlinarith
  have : ((v 0) ^ 2 + (v 1) ^ 2) / quarticKappa = (v 0) ^ 2 / quarticKappa + (v 1) ^ 2 / quarticKappa := by
    ring
  rw [this]
  linarith

theorem amap_injective_FIN066 {w w' : EuclideanSpace ℝ (Fin 2)}
    (h : amap_FIN066 w = amap_FIN066 w') : w = w' := by
  have hk := quarticKappa_pos_FIN066
  have hke := kappa_eta_pos_FIN066
  have hs : 0 < Real.sqrt quarticKappa := Real.sqrt_pos.2 hk
  have hs2 : 0 < Real.sqrt (quarticKappa * quarticEta) := Real.sqrt_pos.2 hke
  have h0 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) h
  have h1 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) h
  simp only [amap_FIN066] at h0 h1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  rw [div_left_inj' hs.ne'] at h0
  rw [div_left_inj' hs2.ne'] at h1
  ext i; fin_cases i
  · simpa using h0
  · simpa using h1

theorem psi_global_FIN066 {t : ℝ} (ht1 : 1 < t) (hroot : t = 1 + quarticKappa * besselRatio t)
    (h : ∀ ν : ProbabilityMeasure (Torus 1),
      DGPS.freeEnergy anisotropicQuarticSaddle ν = DGPS.freeEnergyMinimum anisotropicQuarticSaddle ↔
        ν = xyLaw_EX023 t) :
    (∀ w, quarticPsi_FIN066 !₂[t, 0] ≤ quarticPsi_FIN066 w) ∧
    (∀ w, quarticPsi_FIN066 w ≤ quarticPsi_FIN066 !₂[t, 0] → w = !₂[t, 0]) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ v : EuclideanSpace ℝ (Fin 2),
      c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ quarticPsi_FIN066) !₂[t, 0] v v) := by
  have hk := quarticKappa_pos_FIN066
  have ht0 : 0 < t := by linarith
  have hU := continuous_U_FIN066
  have hΦ := continuous_Phi_FIN066
  have hmin := isMinimizer_FIN066 h
  have hm := psi_min_of_minimizer hU hΦ (xyLaw_EX023 t) hmin
  have hmean : measureMean featPhi_FIN066 (xyLaw_EX023 t : Measure (Torus 1)) = zOf_FIN066 t := by
    rw [← featureMeanRoot_FIN066 hroot, featureMean_eq_measureMean, gibbs_zOf_FIN066]
  rw [hmean] at hm
  refine ⟨?_, ?_, ?_⟩
  · intro w
    rw [quarticPsi_eq_FIN066]
    simp only [Function.comp_apply]
    rw [amapRoot_FIN066]
    exact hm _
  · intro w hw
    rw [quarticPsi_eq_FIN066] at hw
    simp only [Function.comp_apply] at hw
    rw [amapRoot_FIN066] at hw
    have hy' : ∀ w', psi featU_FIN066 featPhi_FIN066 (amap_FIN066 w) ≤
        psi featU_FIN066 featPhi_FIN066 w' := fun w' => hw.trans (hm w')
    have h1 := minimizer_unique_FIN066 h _ (isFreeEnergyMinimizer_gibbs_of_psi_min hU hΦ hy')
    have h2 := featureMean_eq_of_psi_min hU hΦ hy'
    have h3 : amap_FIN066 w = zOf_FIN066 t := by
      rw [← hmean, ← h1]
      exact ((measureMean_gibbsPM hU hΦ _).trans h2).symm
    apply amap_injective_FIN066
    rw [h3, amapRoot_FIN066]
  · refine ⟨1 / (t * quarticKappa), by positivity, fun v => ?_⟩
    rw [hessian_quarticPsi_FIN066, amapRoot_FIN066]
    have h1 := hessian_coercive_FIN066 ht1 hroot (Alin_FIN066 v)
    have h2 := norm_Alin_FIN066 v
    have h3 : 1 / (t * quarticKappa) * ‖v‖ ^ 2 = (1 / t) * (‖v‖ ^ 2 / quarticKappa) := by
      field_simp
    rw [h3]
    refine le_trans ?_ h1
    exact mul_le_mul_of_nonneg_left h2 (by positivity)

end DGPS.FiniteN.QuarticSaddleGlobalFIN066

namespace DGPS.FiniteN

open DGPS DGPS.Models DGPS.Examples.AttractiveXYTilt DGPS.Circle.BesselMoments
open DGPS.FiniteN.QuarticSaddleGlobalFIN066

/-- **FIN066.**  For the anisotropic quartic saddle model `Q = anisotropicQuarticSaddle`
(`κ = 5 / b`, `η = 4 / 5`, `b = I₁(4)/I₀(4)`):
* the `N`-particle Hamiltonian is `H_N = -C - κ (C² + η S²) / (2N)`;
* there is a root `t₊ > 1` of `t = 1 + κ g(t)`, unique among positive roots, such that `q_{t₊}`
  (the von Mises law on the circle) is the unique global minimizer of the free energy, it has
  coercive density Hessian and it is a Gibbs fixed point;
* the auxiliary function `ψ(x,y) = (x-1)²/(2κ) + y²/(2κη) - log I₀(√(x²+y²))` on `ℝ²` has
  `w₊ = (t₊, 0)` as unique global minimum, with coercive Hessian (nondegenerate), `∇ψ(w₊) = 0`;
* the remote state `q_{-4}` is a Gibbs fixed point (`-4 = 1 + κ g(-4)`) whose free-energy gap
  above the minimum is at least `2b`, and `w₋ = (-4, 0)` is a critical point of `ψ`. -/
theorem quartic_unique_global_minimum_and_remote_state :
    (∀ (N : ℕ+) (x : DGPS.ParticleSpace 1 N),
      DGPS.particleHamiltonian anisotropicQuarticSaddle N x =
        -(∑ i, scalarCos (x i)) - quarticKappa *
          ((∑ i, scalarCos (x i)) ^ 2 + quarticEta * (∑ i, scalarSin (x i)) ^ 2) /
            (2 * (N : ℝ))) ∧
    (∃ t : ℝ, 0 < t ∧ 1 < t ∧ t = 1 + quarticKappa * besselRatio t ∧
      (∀ u : ℝ, 0 < u → u = 1 + quarticKappa * besselRatio u → u = t) ∧
      (∀ ν : ProbabilityMeasure (Torus 1),
        DGPS.freeEnergy anisotropicQuarticSaddle ν =
            DGPS.freeEnergyMinimum anisotropicQuarticSaddle ↔
          ν = xyLaw_EX023 t) ∧
      IsCoerciveDensityHessian anisotropicQuarticSaddle (xyLaw_EX023 t) ∧
      (xyLaw_EX023 t : MeasureTheory.Measure (Torus 1)) =
        DGPS.Lipschitz.gibbsMeasure anisotropicQuarticSaddle
          (xyLaw_EX023 t : MeasureTheory.Measure (Torus 1)) ∧
      fderiv ℝ quarticPsi_FIN066 !₂[t, 0] = 0 ∧
      (∀ w, quarticPsi_FIN066 !₂[t, 0] ≤ quarticPsi_FIN066 w) ∧
      (∀ w, quarticPsi_FIN066 w ≤ quarticPsi_FIN066 !₂[t, 0] → w = !₂[t, 0]) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ v : EuclideanSpace ℝ (Fin 2),
        c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ quarticPsi_FIN066) !₂[t, 0] v v)) ∧
    ((-4 : ℝ) = 1 + quarticKappa * besselRatio (-4) ∧
      (xyLaw_EX023 (-4) : MeasureTheory.Measure (Torus 1)) =
        DGPS.Lipschitz.gibbsMeasure anisotropicQuarticSaddle
          (xyLaw_EX023 (-4) : MeasureTheory.Measure (Torus 1)) ∧
      ((2 * quarticB : ℝ) : EReal) ≤
        DGPS.freeEnergy anisotropicQuarticSaddle (xyLaw_EX023 (-4)) -
          DGPS.freeEnergyMinimum anisotropicQuarticSaddle ∧
      fderiv ℝ quarticPsi_FIN066 !₂[-4, 0] = 0) := by
  refine ⟨hamiltonian_FIN066, ?_, ?_⟩
  · obtain ⟨t, ht1, hroot, huniq, hmin⟩ := global_minimizer_FIN066
    obtain ⟨hg, hu, hc⟩ := psi_global_FIN066 ht1 hroot hmin
    exact ⟨t, by linarith, ht1, hroot, huniq, hmin, coercive_FIN066 ht1 hroot,
      fixedPointRoot_FIN066 hroot, critical_quarticPsi_FIN066 hroot, hg, hu, hc⟩
  · exact ⟨remote_neg_four_FIN066, fixedPointRoot_FIN066 remote_neg_four_FIN066,
      remote_gap_FIN066, critical_quarticPsi_FIN066 remote_neg_four_FIN066⟩

end DGPS.FiniteN
