import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootGraphData
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootWeakPairing
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootDensityBounds

/-! Exact Euler moment identities at the same retained ordinary roots. This first
leaf supplies the genuine third-harmonic balance needed to determine the cubic bare
moment. It does not assert an asymptotic coefficient from a formal series. -/

noncomputable section
open MeasureTheory Filter Set Real
open scoped ContDiff Topology
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Pairing the actual critical equation with cos(3t) eliminates its constant
normalization term. Both integrations by parts are on genuine periodic C2 functions. -/
theorem ordinaryCritical_thirdHarmonic_balance (h γ : ℝ) (u : PeriodicC2_STR02969)
    (hcrit : ∀ t, gradG_STR02950 h γ u.val t = 0) :
    (18 - 2 * (1 + γ)) * normInt_STR02933 (fun t => u.val t * Real.cos (3 * t)) =
      normInt_STR02933 (fun t => deriv u.val t ^ 2 * Real.cos (3 * t)) -
        6 * h * normInt_STR02933
          (fun t => Real.sin (3 * t) * deriv u.val t * Real.cos (3 * t)) := by
  have hu : IsPeriodicWeakDerivative_STR02933 u.val (deriv u.val) :=
    ordinaryRoot_periodicWeak_of_c1 u.val u.isC2.1
      (contDiff_one_iff_deriv.mpr ⟨u.isC2.2.1, u.isC2.2.2.1.continuous⟩)
  have hdu : IsPeriodicWeakDerivative_STR02933 (deriv u.val) (deriv (deriv u.val)) :=
    ordinaryRoot_periodicWeak_of_c1 (deriv u.val) (periodic_deriv_STR02901 u.isC2.1)
      (contDiff_one_iff_deriv.mpr ⟨u.isC2.2.2.1, u.isC2.2.2.2.1⟩)
  have h1 := (str029_33_fourier_coefficients_weak_derivative u.val (deriv u.val) hu 3 (by norm_num)).2.1
  have h2 := (str029_33_fourier_coefficients_weak_derivative
    (deriv u.val) (deriv (deriv u.val)) hdu 3 (by norm_num)).1
  simp only [cosCoeff_STR02933, sinCoeff_STR02933, Nat.cast_ofNat] at h1 h2
  have hsecond : normInt_STR02933 (fun t => deriv (deriv u.val) t * Real.cos (3 * t)) =
      -9 * normInt_STR02933 (fun t => u.val t * Real.cos (3 * t)) := by linarith
  let C := -meanT_STR02901 (fun t => deriv u.val t ^ 2 * rhoT_STR02901 h u.val t) +
    2 * (1 + γ) * meanT_STR02901 (fun t => u.val t * rhoT_STR02901 h u.val t)
  have hbracket (t : ℝ) :
      -2 * deriv (deriv u.val) t + 6 * h * Real.sin (3 * t) * deriv u.val t -
        deriv u.val t ^ 2 - 2 * (1 + γ) * u.val t + C = 0 := by
    have ht := hcrit t
    unfold gradG_STR02950 at ht
    have he := (mul_eq_zero.mp ht).resolve_left
      (rhoT_pos_STR02901 h u.isC2.2.1.continuous t).ne'
    dsimp [C]
    linarith
  have he : (fun t => (-2 : ℝ) * (deriv (deriv u.val) t * Real.cos (3 * t)) +
      (6 * h) * (Real.sin (3 * t) * deriv u.val t * Real.cos (3 * t)) +
      (-1 : ℝ) * (deriv u.val t ^ 2 * Real.cos (3 * t)) +
      (-2 * (1 + γ)) * (u.val t * Real.cos (3 * t))) =
      fun t => -C * Real.cos (3 * t) := by
    funext t
    linear_combination Real.cos (3 * t) * hbracket t
  have hi1 : Integrable (fun t => deriv (deriv u.val) t * Real.cos (3 * t))
      (volume.restrict (Ioc 0 (2 * π))) := integrable_continuous_STR02934
    (u.isC2.2.2.2.1.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
  have hi2 : Integrable (fun t => Real.sin (3 * t) * deriv u.val t * Real.cos (3 * t))
      (volume.restrict (Ioc 0 (2 * π))) := integrable_continuous_STR02934
    (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
      u.isC2.2.2.1.continuous).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
  have hi3 : Integrable (fun t => deriv u.val t ^ 2 * Real.cos (3 * t))
      (volume.restrict (Ioc 0 (2 * π))) := integrable_continuous_STR02934
    ((u.isC2.2.2.1.continuous.pow 2).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
  have hi4 : Integrable (fun t => u.val t * Real.cos (3 * t))
      (volume.restrict (Ioc 0 (2 * π))) := integrable_continuous_STR02934
    (u.isC2.2.1.continuous.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
  have hm := congrArg normInt_STR02933 he
  rw [normInt_lin4_STR02935 hi1 hi2 hi3 hi4, normInt_mul_const_STR02933,
    show normInt_STR02933 (fun t => Real.cos (3 * t)) = 0 by
      simpa using normInt_cos_nat_STR02934 3, hsecond] at hm
  linarith

/-- The third-harmonic balance holds for every SAME retained branch on its original
common interval; criticality is supplied internally by the ordinary producer. -/
theorem ordinaryRoot_thirdHarmonic_balance (D : OrdinaryRootGraphData)
    (h : ℝ) (hh : h ∈ Ioo (-D.radius) D.radius) (j : Fin 3) :
    let u := Lamp_STR02956 D.ψ (h, h ^ 2 * D.Z j h 2)
      (h * D.Z j h 0, h * D.Z j h 1)
    (18 - 2 * (1 + h ^ 2 * D.Z j h 2)) *
        normInt_STR02933 (fun t => u.val t * Real.cos (3 * t)) =
      normInt_STR02933 (fun t => deriv u.val t ^ 2 * Real.cos (3 * t)) -
        6 * h * normInt_STR02933
          (fun t => Real.sin (3 * t) * deriv u.val t * Real.cos (3 * t)) := by
  exact ordinaryCritical_thirdHarmonic_balance h _ _ (D.chart_critical h hh j)


private theorem moment_logRemainder_formula (ψ : Par_STR02916 → E_STR02969)
    (Z : ℝ → Fin 3 → ℝ) (h : ℝ) :
    logRemainder_STR02931 ψ Z h = fun t => chartU_STR02924 ψ h (Z h) t -
      2 * h * Real.cos t - h ^ 2 * ((2 / 3 : ℝ) * Real.cos (2 * t) -
        (1 / 5 : ℝ) * Real.cos (4 * t)) := by
  funext t
  unfold logRemainder_STR02931
  linear_combination log_density_identity_STR02931 ψ Z h t

/-- A genuine C1 logarithmic remainder controls the actual spatial derivative,
with no differentiation of a C0 estimate. -/
theorem ordinaryRoot_derivative_remainder (ψ : Par_STR02916 → E_STR02969)
    (Z : ℝ → Fin 3 → ℝ) (h C : ℝ)
    (hrem : cmN_STR02966 1 (logRemainder_STR02931 ψ Z h) ≤ C * |h| ^ 3) :
    ∀ t, |deriv (chartU_STR02924 ψ h (Z h)) t -
      (-2 * h * Real.sin t + h ^ 2 *
        (-(4 / 3 : ℝ) * Real.sin (2 * t) + (4 / 5 : ℝ) * Real.sin (4 * t)))| ≤
      C * |h| ^ 3 := by
  let R := logRemainder_STR02931 ψ Z h
  have hu := chartU_isC2_STR02924 ψ h (Z h)
  have hU : ContDiff ℝ 1 (chartU_STR02924 ψ h (Z h)) :=
    contDiff_one_iff_deriv.mpr ⟨hu.2.1, hu.2.2.1.continuous⟩
  have hper : Function.Periodic R (2 * π) := by
    change Function.Periodic (logRemainder_STR02931 ψ Z h) (2 * π)
    rw [moment_logRemainder_formula]
    intro t
    dsimp only
    have hp2 : Real.cos (2 * (t + 2 * π)) = Real.cos (2 * t) := (cos_test_STR02933 2).2 t
    have hp4 : Real.cos (4 * (t + 2 * π)) = Real.cos (4 * t) := (cos_test_STR02933 4).2 t
    rw [hu.1 t, Real.cos_periodic t, hp2, hp4]
  have hRC : ContDiff ℝ 1 R := by
    dsimp only [R]
    rw [moment_logRemainder_formula]
    fun_prop
  have hR : IsPerCm_STR02966 1 R := ⟨hper, hRC⟩
  have hsup : DGPS.Analysis.PeriodicHolder.supNorm (deriv R) ≤ cmN_STR02966 1 R := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, cmN_succ_STR02966, cmN_zero_STR02966]
    linarith [DGPS.Analysis.PeriodicHolder.supNorm_nonneg R]
  intro t
  have hb := (abs_le_supNorm_STR02966 (isPerCm_deriv_STR02966 hR) t).trans (hsup.trans hrem)
  have hQ : HasDerivAt
      (fun s : ℝ => (2 / 3 : ℝ) * Real.cos (2 * s) - (1 / 5 : ℝ) * Real.cos (4 * s))
      (-(4 / 3 : ℝ) * Real.sin (2 * t) + (4 / 5 : ℝ) * Real.sin (4 * t)) t := by
    convert ((((hasDerivAt_id t).const_mul 2).cos).const_mul (2 / 3 : ℝ)).sub
      ((((hasDerivAt_id t).const_mul 4).cos).const_mul (1 / 5 : ℝ)) using 1
    · funext s; simp only [Pi.sub_apply, id_eq]
    · simp only [id_eq]; ring
  have hd : HasDerivAt
      (fun s : ℝ => chartU_STR02924 ψ h (Z h) s - 2 * h * Real.cos s -
        h ^ 2 * ((2 / 3 : ℝ) * Real.cos (2 * s) - (1 / 5 : ℝ) * Real.cos (4 * s)))
      (deriv (chartU_STR02924 ψ h (Z h)) t -
        (-2 * h * Real.sin t + h ^ 2 *
          (-(4 / 3 : ℝ) * Real.sin (2 * t) + (4 / 5 : ℝ) * Real.sin (4 * t)))) t := by
    convert (((hu.2.1 t).hasDerivAt.sub
      (((hasDerivAt_id t).cos).const_mul (2 * h))).sub (hQ.const_mul (h ^ 2))) using 1
    · funext s; simp only [Pi.sub_apply, id_eq]
    · simp only [id_eq]; ring
  have hder : deriv R t = deriv (chartU_STR02924 ψ h (Z h)) t -
      (-2 * h * Real.sin t + h ^ 2 *
        (-(4 / 3 : ℝ) * Real.sin (2 * t) + (4 / 5 : ℝ) * Real.sin (4 * t))) := by
    dsimp only [R]
    rw [moment_logRemainder_formula]
    exact hd.deriv
  rwa [hder] at hb

/-- The SAME actual even branch has a uniform spatial C1 expansion, with its
constant fixed before h and the angular point. The C1 bound comes from the actual
T31 producer retained by D, rather than from differentiating its C0 bound. -/
theorem ordinaryRoot_evenBranch_C1_expansion (D : OrdinaryRootGraphData) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, |h| ≤ D.radius → ∀ t : ℝ,
      |chartU_STR02924 D.ψ h (D.Z 0 h) t - 2 * h * Real.cos t -
        h ^ 2 * ((2 / 3 : ℝ) * Real.cos (2 * t) - (1 / 5 : ℝ) * Real.cos (4 * t))| ≤
          C * |h| ^ 3 ∧
      |deriv (chartU_STR02924 D.ψ h (D.Z 0 h)) t -
        (-2 * h * Real.sin t + h ^ 2 *
          (-(4 / 3 : ℝ) * Real.sin (2 * t) + (4 / 5 : ℝ) * Real.sin (4 * t)))| ≤
          C * |h| ^ 3 := by
  obtain ⟨C, hC, hrem⟩ := D.log_bound_one
  refine ⟨C, hC, fun h hh t => ⟨?_, ?_⟩⟩
  · have h0 : cmN_STR02966 0 (logRemainder_STR02931 D.ψ (D.Z 0) h) ≤ C * |h| ^ 3 := by
      rw [cmN_zero_STR02966]
      exact (supNorm_le_cmN_STR02966 1 _).trans (hrem h hh)
    have hb := ordinaryRoot_logRemainder_pointwise D.ψ (D.Z 0) h C h0 t
    rw [moment_logRemainder_formula] at hb
    exact hb
  · exact ordinaryRoot_derivative_remainder D.ψ (D.Z 0) h C (hrem h hh) t

end DGPS.Examples.ThreeSpeciesCircle
