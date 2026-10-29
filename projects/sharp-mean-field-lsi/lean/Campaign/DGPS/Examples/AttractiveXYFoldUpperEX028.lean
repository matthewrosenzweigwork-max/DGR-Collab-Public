import DGPS.Examples.AttractiveXYFoldEX027
import DGPS.Examples.AttractiveXYTiltEX024
import DGPS.Examples.AttractiveXYTiltRemoteEX025
import DGPS.Examples.CriticalRecoveryBridgesEX021

/-!
# EX028: fold upper bound and Gaussian comparability

For the attractive XY model at `κ = 4`, `h = h_c + ε` with `0 < ε ≤ 1`, where `s > 0`,
`g'(s) = 1/4` and `h_c = 4 g(s) - s` (the fold parameter of EX027):

* the old fold density `q_{-s}` (the von Mises density with tilt `-s`) has scalar dissipation
  `D = a0 ε² g(s) / s` for every drift (`fold_dissipation_EX028`), proved by a general von Mises
  dissipation formula (`dissipation_EX028`) and the sine moment `∫ sin² dq_t = g(t)/t`;
* its gap satisfies `G ≥ 2 h g(s) > 0` (`gap_EX028`), hence `r_* ≤ a0 ε² / (4 h_c s)`
  (`fold_rate_upper_EX028`);
* at every positive root `t = 4 g(t) + h` the equilibrium Gaussian rate satisfies
  `c_G a0 ≤ λ_G ≤ C_G a0` with `c_G = (h_c / M0) exp(-2 M0)`, `M0 = h_c + 5`, and
  `C_G = (h_c + 1) / g(h_c)` (`fold_gaussian_EX028`); the upper bound is the Rayleigh quotient of
  the test function `sin 2πx` (`gaussian_upper_EX028`).
-/

open MeasureTheory
open DGPS DGPS.Examples.AttractiveXY DGPS.Examples.AttractiveXYTilt
open DGPS.Examples.AttractiveXYTiltEX024
open DGPS.Examples.CriticalRecoveryAsymptoticsEX021 DGPS.Examples.CriticalRecoveryBridgesEX021
open DGPS.Examples.AttractiveXYTiltRemoteEX025
open DGPS.Circle.BesselMoments DGPS.Circle.BesselMonotonicity DGPS.Circle.BesselConcavity
open DGPS.Models
open scoped ENNReal NNReal

namespace DGPS.Examples.AttractiveXYFoldUpperEX028

theorem im_weak_EX028 (μ : ProbabilityMeasure (Torus 1)) :
    IsMeasureWeakGradient μ (fun x => (xyMode x).im) (smoothGrad (fun x => (xyMode x).im)) := by
  have hs := isSmoothPeriodic_im_xyMode.isWeakGradient
  have hc : Continuous (fun x : Torus 1 => (xyMode x).im) :=
    Complex.continuous_im.comp continuous_xyMode
  have hg : Continuous (smoothGrad (fun x : Torus 1 => (xyMode x).im)) :=
    isSmoothPeriodic_im_xyMode.continuous_smoothGrad
  refine ⟨?_, ?_, ?_, ?_, hs.ibp⟩
  · exact hc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact hg.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)



theorem sinSq_moment_EX028 {t : ℝ} (ht : t ≠ 0) :
    ∫ x, vonMisesTorusDensityEX021 t x * (xyMode x).im ^ 2 ∂DGPS.haar 1 = besselRatio t / t := by
  have h1 := integral_vonMisesProbabilityEX021 t (f := fun x => (xyMode x).im ^ 2)
    ((Complex.continuous_im.comp continuous_xyMode).pow 2)
  have h2 : (vonMisesProbabilityEX021 t : Measure (DGPS.Torus 1)) =
      (xyLaw_EX023 t : Measure (DGPS.Torus 1)) := by
    rw [vonMisesProbability_eq_densityMeasureEX021, density_identity_EX025]
  rw [h2] at h1
  rw [← h1]
  exact m_ss_EX024 t ht

theorem dissipation_EX028 (κ h t : ℝ) (ht : t ≠ 0) (b : DGPS.AbsoluteDrift (attractiveXY κ h)) :
    DGPS.scalarDissipation (attractiveXY κ h) b (vonMisesAbsoluteDensityEX021 t) =
      ENNReal.ofReal (4 * Real.pi ^ 2 * (t - (h + κ * besselRatio t)) ^ 2 *
        (besselRatio t / t)) := by
  let ρ := vonMisesAbsoluteDensityEX021 t
  let a := h + κ * besselRatio t
  let P := xyFrozen a 0
  let c := -2 * Real.pi * (t - a)
  have hLaw := vonMisesProbability_eq_densityMeasureEX021 t
  have hMomP : xyZ1 (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) = besselRatio t ∧
      xyZ2 (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) = 0 := by
    have hm := vonMisesProbability_firstMomentsEX021 t
    rw [hLaw] at hm
    exact hm
  have hP : xyFrozenLaw κ h (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) = P := by
    unfold xyFrozenLaw P a
    rw [hMomP.1, hMomP.2]
    simp
  have hrootW := DGPS.isWeakGradient_weakGradient ρ.sqrt_mem
  have hrootGrad : DGPS.weakGradient ρ.sqrt ρ.sqrt_mem =ᵐ[DGPS.haar 1]
      DGPS.smoothGrad (vonMisesRootEX021 t) :=
    hrootW.ae_eq (vonMisesRoot_smoothEX021 t).isWeakGradient
  have hlog := DGPS.Examples.AttractiveXY.weakGradient_log_xyFrozen a 0
  have hscore :
      (fun x => (2 : ℝ) • DGPS.weakGradient ρ.sqrt ρ.sqrt_mem x -
        ρ.sqrt x • DGPS.weakGradient (fun x => Real.log (P.density x))
          (P.memH1_log (DGPS.Examples.AttractiveXY.xyFrozen_hasPositiveLipschitzDensity
            a 0)) x) =ᵐ[DGPS.haar 1]
      (fun x => (WithLp.toLp 2 (fun _ : Fin 1 => vonMisesRootEX021 t x *
        (c * (xyMode x).im)) : DGPS.Tangent 1)) := by
    filter_upwards [hrootGrad, hlog] with x hx hr
    ext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp only [PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply]
    rw [hx, hr, DGPS.smoothGrad_apply, DGPS.smoothGrad_apply,
      vonMisesRoot_coordPartialEX021,
      DGPS.Examples.AttractiveXY.coordPartial_re_xyMode,
      DGPS.Examples.AttractiveXY.coordPartial_xyTrig]
    have hρ : ρ.sqrt x = vonMisesRootEX021 t x := rfl
    rw [hρ]
    unfold xyTrig c
    simp
    ring
  have hcont : Continuous (fun x : DGPS.Torus 1 =>
      (c * (xyMode x).im) ^ 2 * vonMisesTorusDensityEX021 t x) :=
    ((continuous_const.mul (Complex.continuous_im.comp continuous_xyMode)).pow 2).mul
      (vonMisesTorusDensity_continuous_EX021 t)
  have hI : Integrable (fun x : DGPS.Torus 1 =>
      (c * (xyMode x).im) ^ 2 * vonMisesTorusDensityEX021 t x) (DGPS.haar 1) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnn : 0 ≤ᵐ[DGPS.haar 1]
      (fun x => (c * (xyMode x).im) ^ 2 * vonMisesTorusDensityEX021 t x) :=
    Filter.Eventually.of_forall fun x =>
      mul_nonneg (sq_nonneg _) (vonMisesTorusDensity_pos_EX021 t x).le
  rw [DGPS.Examples.AttractiveXY.scalarDissipation_attractiveXY κ h b ρ, hP]
  rw [DGPS.positiveReference_absolute_identity P
    (DGPS.Examples.AttractiveXY.xyFrozen_hasPositiveLipschitzDensity _ _) ρ]
  have hscoreENN :
      (fun x => ‖(2 : ℝ) • DGPS.weakGradient ρ.sqrt ρ.sqrt_mem x -
          ρ.sqrt x • DGPS.weakGradient (fun x => Real.log (P.density x))
            (P.memH1_log (DGPS.Examples.AttractiveXY.xyFrozen_hasPositiveLipschitzDensity
              a 0)) x‖ₑ ^ 2) =ᵐ[DGPS.haar 1]
        (fun x => ENNReal.ofReal
          ((c * (xyMode x).im) ^ 2 * vonMisesTorusDensityEX021 t x)) := by
    filter_upwards [hscore] with x hx
    rw [hx, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), tangent_norm_sq]
    simp only [Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton]
    congr 1
    rw [mul_pow, vonMisesRoot_sqEX021]
    ring
  rw [lintegral_congr_ae hscoreENN,
    ← ofReal_integral_eq_lintegral_ofReal hI hnn]
  congr 1
  have : ∀ x : DGPS.Torus 1, (c * (xyMode x).im) ^ 2 * vonMisesTorusDensityEX021 t x =
      c ^ 2 * (vonMisesTorusDensityEX021 t x * (xyMode x).im ^ 2) := fun x => by ring
  simp_rw [this]
  rw [integral_const_mul, sinSq_moment_EX028 ht]
  simp only [c]
  ring

theorem besselRatio_mono_EX028 {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    besselRatio a ≤ besselRatio b := by
  have hc : Continuous besselRatio := continuous_besselRatio
  have hmono : StrictMonoOn besselRatio (Set.Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) hc.continuousOn ?_
    intro x hx
    rw [interior_Ici] at hx
    rw [deriv_ratio]
    exact ratioDeriv_pos x hx
  exact hmono.monotoneOn (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr (ha.trans hab)) hab

theorem sin_dirichlet_EX028 (μ : ProbabilityMeasure (Torus 1)) :
    dirichletEnergy μ ⟨fun x => (xyMode x).im, smoothGrad (fun x => (xyMode x).im),
      im_weak_EX028 μ⟩ ≤ ENNReal.ofReal (4 * Real.pi ^ 2) := by
  unfold dirichletEnergy
  calc ∫⁻ x, ‖smoothGrad (fun x : Torus 1 => (xyMode x).im) x‖ₑ ^ 2 ∂(μ : Measure (Torus 1))
      ≤ ∫⁻ _x, ENNReal.ofReal (4 * Real.pi ^ 2) ∂(μ : Measure (Torus 1)) := by
        refine lintegral_mono fun x => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), tangent_norm_sq]
        refine ENNReal.ofReal_le_ofReal ?_
        simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
          smoothGrad_apply, coordPartial_im_xyMode]
        have h := xyMode_norm x
        have h2 := Complex.sq_norm (xyMode x)
        rw [h, Complex.normSq_apply] at h2
        nlinarith [sq_nonneg (xyMode x).im, Real.pi_pos, sq_nonneg Real.pi]
    _ = ENNReal.ofReal (4 * Real.pi ^ 2) := by simp

theorem gaussian_upper_EX028 {κ h t : ℝ} (hh : 0 < h) (ht : 0 < t)
    (heq : t = κ * besselRatio t + h)
    (hH : IsCoerciveDensityHessian (attractiveXY κ h) (xyLaw_EX023 t)) :
    gaussianRate (attractiveXY κ h) (xyLaw_EX023 t) hH ≤
      ENNReal.ofReal (4 * Real.pi ^ 2 * h / besselRatio t) := by
  have hg : 0 < besselRatio t := besselRatio_pos t ht
  let f : WeakH1Test (xyLaw_EX023 t) :=
    ⟨fun x => (xyMode x).im, smoothGrad (fun x => (xyMode x).im), im_weak_EX028 _⟩
  have hf0 : ∫ x, f.fn x ∂(xyLaw_EX023 t : Measure (Torus 1)) = 0 := m_s_EX024 t
  have hfne : ¬ f.fn =ᵐ[(xyLaw_EX023 t : Measure (Torus 1))] 0 := by
    intro hz
    have h1 := m_ss_EX024 t ht.ne'
    have h2 : ∫ x, (xyMode x).im ^ 2 ∂(xyLaw_EX023 t : Measure (Torus 1)) = 0 := by
      rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
      · simp
      · filter_upwards [hz] with x hx
        have : (xyMode x).im = 0 := hx
        rw [this]; norm_num
    rw [h2] at h1
    exact (div_pos hg ht).ne h1
  have hf : IsNonzeroCentered (xyLaw_EX023 t) f := ⟨hf0, hfne⟩
  have hcen : f.toCentered (xyLaw_EX023 t) hf0 = vC_EX024 t := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [f.isWeak.memLp.coeFn_toLp, vLp_ae_EX024 t] with x h1 h2
    exact h1.trans h2.symm
  have hHv := hessian_v_EX024 κ h t ht.ne'
  have hk : 1 - κ * (besselRatio t / t) = h / t := by field_simp; linarith
  rw [hk] at hHv
  have hC : densityCovariance (attractiveXY κ h) (xyLaw_EX023 t) hH (vC_EX024 t) =
      (t / h) • vC_EX024 t := by
    have h1 := densityCovariance_densityHessian (attractiveXY κ h) (xyLaw_EX023 t) hH (vC_EX024 t)
    rw [hHv, map_smul] at h1
    have h2 : (t / h) • ((h / t) • densityCovariance (attractiveXY κ h) (xyLaw_EX023 t) hH
        (vC_EX024 t)) = (t / h) • vC_EX024 t := by rw [h1]
    rw [smul_smul, show t / h * (h / t) = 1 by field_simp, one_smul] at h2
    exact h2
  have hden : gaussianDenominator (attractiveXY κ h) (xyLaw_EX023 t) hH f hf0 =
      besselRatio t / h := by
    unfold gaussianDenominator
    rw [hcen, hC]
    have e : inner ℝ (vC_EX024 t) ((t / h) • vC_EX024 t) =
        (t / h) * inner ℝ (vC_EX024 t) (vC_EX024 t) := by
      simp [inner_smul_right]
    have e2 : inner ℝ (vC_EX024 t) (vC_EX024 t) = besselRatio t / t := by
      have := inner_vv_EX024 (t := t) ht.ne'
      exact this
    rw [e, e2]
    field_simp
  calc gaussianRate (attractiveXY κ h) (xyLaw_EX023 t) hH
      ≤ gaussianQuotient (attractiveXY κ h) (xyLaw_EX023 t) hH f hf0 :=
        gaussianRate_le_quotient _ _ hH f hf
    _ = dirichletEnergy (xyLaw_EX023 t) f / ENNReal.ofReal (besselRatio t / h) := by
        unfold gaussianQuotient; rw [hden]
    _ ≤ ENNReal.ofReal (4 * Real.pi ^ 2) / ENNReal.ofReal (besselRatio t / h) :=
        ENNReal.div_le_div_right (sin_dirichlet_EX028 _) _
    _ = ENNReal.ofReal (4 * Real.pi ^ 2 * h / besselRatio t) := by
        rw [← ENNReal.ofReal_div_of_pos (div_pos hg hh)]
        congr 1
        field_simp

theorem gap_EX028 {κ h s : ℝ} (hh : 0 < h) (hs : 0 < s) :
    2 * h * besselRatio s ≤
        (scalarGap (attractiveXY κ h) (vonMisesAbsoluteDensityEX021 (-s)) : ℝ) ∧
      0 < scalarGap (attractiveXY κ h) (vonMisesAbsoluteDensityEX021 (-s)) := by
  obtain ⟨h1, h2⟩ := negative_gap_EX023 (κ := κ) hh hs
  have key : 2 * h * besselRatio s ≤
      (scalarGap (attractiveXY κ h) (vonMisesAbsoluteDensityEX021 (-s)) : ℝ) := by
    rw [← densityMeasure_eq_EX025 (-s), ← coe_densityFreeEnergy,
      ← coe_freeEnergyMinimumReal, ← EReal.coe_sub, EReal.coe_le_coe_iff] at h1
    rw [coe_scalarGap]
    exact h1
  exact ⟨key, NNReal.coe_pos.mp (lt_of_lt_of_le h2 key)⟩


theorem fold_dissipation_EX028 {s hc ε : ℝ} (hs : 0 < s) (hhc : hc = 4 * besselRatio s - s)
    (b : AbsoluteDrift (attractiveXY 4 (hc + ε))) :
    scalarDissipation (attractiveXY 4 (hc + ε)) b (vonMisesAbsoluteDensityEX021 (-s)) =
      ENNReal.ofReal (a0 * ε ^ 2 * besselRatio s / s) := by
  rw [dissipation_EX028 4 (hc + ε) (-s) (neg_ne_zero.2 hs.ne') b, besselRatio_neg]
  congr 1
  have h1 : -s - (hc + ε + 4 * -besselRatio s) = -ε := by rw [hhc]; ring
  rw [h1]
  unfold a0
  field_simp

theorem fold_rate_upper_EX028 {s hc ε : ℝ} (hs : 0 < s) (hhc : hc = 4 * besselRatio s - s)
    (hc0 : 0 < hc) (hε0 : 0 < ε) (b : AbsoluteDrift (attractiveXY 4 (hc + ε))) :
    scalarRate (attractiveXY 4 (hc + ε)) b ≤ ENNReal.ofReal (a0 * ε ^ 2 / (4 * hc * s)) := by
  have hg : 0 < besselRatio s := besselRatio_pos s hs
  have hh : 0 < hc + ε := by linarith
  obtain ⟨hG, hGpos⟩ := gap_EX028 (κ := 4) hh hs
  refine (scalarRate_le_quotient _ b _ hGpos).trans ?_
  unfold scalarQuotient
  rw [fold_dissipation_EX028 hs hhc b]
  have h2G : ENNReal.ofReal (4 * (hc + ε) * besselRatio s) ≤
      2 * ((scalarGap (attractiveXY 4 (hc + ε)) (vonMisesAbsoluteDensityEX021 (-s)) : ℝ≥0) :
        ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc ENNReal.ofReal (a0 * ε ^ 2 * besselRatio s / s) /
        (2 * ((scalarGap (attractiveXY 4 (hc + ε)) (vonMisesAbsoluteDensityEX021 (-s)) : ℝ≥0) :
          ℝ≥0∞))
      ≤ ENNReal.ofReal (a0 * ε ^ 2 * besselRatio s / s) /
          ENNReal.ofReal (4 * (hc + ε) * besselRatio s) :=
        ENNReal.div_le_div_left h2G _
    _ = ENNReal.ofReal (a0 * ε ^ 2 / (4 * (hc + ε) * s)) := by
        rw [← ENNReal.ofReal_div_of_pos (by positivity)]
        congr 1
        field_simp
    _ ≤ ENNReal.ofReal (a0 * ε ^ 2 / (4 * hc * s)) := by
        apply ENNReal.ofReal_le_ofReal
        have := a0_pos
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [mul_pos hc0 hs]


theorem fold_gaussian_EX028 {hc ε t : ℝ} (hc0 : 0 < hc) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (ht : 0 < t) (heq : t = 4 * besselRatio t + (hc + ε)) :
    IsCoerciveDensityHessian (attractiveXY 4 (hc + ε)) (xyLaw_EX023 t) ∧
      ∀ hH : IsCoerciveDensityHessian (attractiveXY 4 (hc + ε)) (xyLaw_EX023 t),
        ENNReal.ofReal (hc / (hc + 5) * Real.exp (-(2 * (hc + 5))) * a0) ≤
            gaussianRate (attractiveXY 4 (hc + ε)) (xyLaw_EX023 t) hH ∧
          gaussianRate (attractiveXY 4 (hc + ε)) (xyLaw_EX023 t) hH ≤
            ENNReal.ofReal ((hc + 1) / besselRatio hc * a0) := by
  have hh : 0 < hc + ε := by linarith
  obtain ⟨-, -, -, hcoer, -, hG, -⟩ :=
    tilted_centered_hessian_and_local_gaussian_bound (κ := 4) (h := hc + ε)
      (by norm_num) hh ht heq
  refine ⟨hcoer, fun hH => ⟨?_, ?_⟩⟩
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hG hH).2.2
    have ha := a0_pos
    have h1 : hc / (hc + 5) ≤ (hc + ε) / (hc + ε + 4) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have h2 : Real.exp (-(2 * (hc + 5))) ≤ Real.exp (-(2 * (hc + ε + 4))) :=
      Real.exp_le_exp.mpr (by linarith)
    have h3 : 4 * Real.pi ^ 2 = a0 := rfl
    rw [h3]
    have h4 : 0 ≤ hc / (hc + 5) := by positivity
    calc hc / (hc + 5) * Real.exp (-(2 * (hc + 5))) * a0
        ≤ (hc + ε) / (hc + ε + 4) * Real.exp (-(2 * (hc + ε + 4))) * a0 := by
          apply mul_le_mul_of_nonneg_right _ ha.le
          exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
      _ = a0 * ((hc + ε) / (hc + ε + 4)) * Real.exp (-(2 * (hc + ε + 4))) := by ring
  · refine (gaussian_upper_EX028 hh ht heq hH).trans (ENNReal.ofReal_le_ofReal ?_)
    have hg0 : 0 < besselRatio hc := besselRatio_pos hc hc0
    have hgt : 0 < besselRatio t := besselRatio_pos t ht
    have hth : hc + ε ≤ t := by linarith
    have hmono : besselRatio hc ≤ besselRatio t :=
      besselRatio_mono_EX028 hc0.le (by linarith)
    have h3 : 4 * Real.pi ^ 2 = a0 := rfl
    rw [h3, mul_comm ((hc + 1) / besselRatio hc) a0, mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ a0_pos.le
    exact div_le_div₀ (by linarith) (by linarith) hg0 hmono

end DGPS.Examples.AttractiveXYFoldUpperEX028

namespace DGPS.Examples

open DGPS.Examples.AttractiveXYFoldUpperEX028

/-- EX028. Fold upper bound and Gaussian comparability. Let `s > 0` with `g'(s) = 1/4` and
`h_c = 4 g(s) - s`. For every `0 < ε ≤ 1`, at `κ = 4`, `h = h_c + ε`, the old fold density
`q_{-s}` has dissipation `D = a0 ε² g(s) / s` (for every drift) and gap `G ≥ 2 h g(s) > 0`, so
`r_* ≤ a0 ε² / (4 h_c s)`; at any positive root `t = 4 g(t) + h` the density Hessian is coercive and
the Gaussian rate satisfies `c_G a0 ≤ λ_G ≤ C_G a0` with `c_G = (h_c/M0) exp(-2 M0)`
(`M0 = h_c + 5`) and `C_G = (h_c + 1)/g(h_c)`, both independent of `ε`. -/
theorem fold_upper_bound_and_gaussian_comparability {s hc : ℝ} (hs : 0 < s)
    (hd : deriv besselRatio s = 1 / 4) (hhc : hc = 4 * besselRatio s - s) :
    0 < hc ∧
    ∃ cG CG : ℝ, cG = hc / (hc + 5) * Real.exp (-(2 * (hc + 5))) ∧ 0 < cG ∧ 0 < CG ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∃ t : ℝ, 0 < t ∧ t = 4 * besselRatio t + (hc + ε)) ∧
      (∀ b : AbsoluteDrift (attractiveXY 4 (hc + ε)),
        scalarDissipation (attractiveXY 4 (hc + ε)) b (vonMisesAbsoluteDensityEX021 (-s)) =
          ENNReal.ofReal (a0 * ε ^ 2 * besselRatio s / s)) ∧
      2 * (hc + ε) * besselRatio s ≤
        (scalarGap (attractiveXY 4 (hc + ε)) (vonMisesAbsoluteDensityEX021 (-s)) : ℝ) ∧
      0 < scalarGap (attractiveXY 4 (hc + ε)) (vonMisesAbsoluteDensityEX021 (-s)) ∧
      (∀ b : AbsoluteDrift (attractiveXY 4 (hc + ε)),
        scalarRate (attractiveXY 4 (hc + ε)) b ≤ ENNReal.ofReal (a0 * ε ^ 2 / (4 * hc * s))) ∧
      ∀ t : ℝ, 0 < t → t = 4 * besselRatio t + (hc + ε) →
        IsCoerciveDensityHessian (attractiveXY 4 (hc + ε)) (xyLaw_EX023 t) ∧
        ∀ hH : IsCoerciveDensityHessian (attractiveXY 4 (hc + ε)) (xyLaw_EX023 t),
          ENNReal.ofReal (cG * a0) ≤
              gaussianRate (attractiveXY 4 (hc + ε)) (xyLaw_EX023 t) hH ∧
            gaussianRate (attractiveXY 4 (hc + ε)) (xyLaw_EX023 t) hH ≤
              ENNReal.ofReal (CG * a0) := by
  obtain ⟨hc0, hex, -, -, -⟩ := uniform_fold_residual_bound hs hd hhc
  refine ⟨hc0, hc / (hc + 5) * Real.exp (-(2 * (hc + 5))), (hc + 1) / besselRatio hc,
    rfl, by positivity, div_pos (by linarith) (besselRatio_pos hc hc0), ?_⟩
  intro ε hε0 hε1
  obtain ⟨t0, ht0, -⟩ := hex ε hε0 hε1
  have hh : 0 < hc + ε := by linarith
  obtain ⟨hG, hGpos⟩ := gap_EX028 (κ := 4) hh hs
  refine ⟨⟨t0, ht0⟩, fun b => fold_dissipation_EX028 hs hhc b, hG, hGpos,
    fun b => fold_rate_upper_EX028 hs hhc hc0 hε0 b, ?_⟩
  intro t ht heq
  obtain ⟨hcoer, hr⟩ := fold_gaussian_EX028 hc0 hε0 hε1 ht heq
  exact ⟨hcoer, hr⟩

end DGPS.Examples
