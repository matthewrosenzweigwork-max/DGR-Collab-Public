import FullLabeledLSI.Nonvacuity.Prop82.Poincare
import FullLabeledLSI.Infra.FisherDensity
import FullLabeledLSI.Paper.Sec8Fourier1
import SharpSymmetricLSI.Paper.RefSpectrum16

/-!
# The logarithmic-score test

The score is the original smooth logarithmic gradient `gLog`, in physical
coordinates. Its smoothness, weighted mean zero, and weighted square norm
are justified here. Heat stationarity is a separate, unproved analytic step.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Prop82

noncomputable def scoreTest (rho : Torus 1 → Real) (x : Torus 1) : Real :=
  gLog rho x 0

noncomputable def scoreEnergy (rho : Torus 1 → Real) : Real :=
  ∫ x, rho x * Sec8.gradSq (scoreTest rho) x ∂haar 1

theorem scoreTest_smooth {rho : Torus 1 → Real} (hrho : SmoothProbability rho) :
    IsSmoothT (scoreTest rho) := by
  exact Sec8.isSmoothT_dpart (contDiff_logD hrho.smooth hrho.positive) 0

theorem rho_mul_scoreTest {rho : Torus 1 → Real} (hrho : SmoothProbability rho)
    (x : Torus 1) : rho x * scoreTest rho x = dpart rho 0 x := by
  have hd : HasFDerivAt (rho ∘ liftT)
      (fderiv Real (rho ∘ liftT) (secT x)) (secT x) :=
    (hrho.smooth.differentiable (by simp) _).hasFDerivAt
  have hl := hd.log (by
    simp only [Function.comp, liftT_secT]
    exact (hrho.positive x).ne')
  unfold scoreTest gLog logD dpart
  rw [show ((fun y => Real.log (rho y)) ∘ liftT) =
    (fun z => Real.log ((rho ∘ liftT) z)) from rfl, hl.fderiv]
  simp only [smul_apply, smul_eq_mul, Function.comp, liftT_secT]
  field_simp [(hrho.positive x).ne']

theorem scoreTest_mean_zero {rho : Torus 1 → Real} (hrho : SmoothProbability rho) :
    ∫ x, rho x * scoreTest rho x ∂haar 1 = 0 := by
  simp_rw [rho_mul_scoreTest hrho]
  exact integral_dpart_eq_zero (Sec8.c1T_of_smooth hrho.smooth) 0

/-- Applies the supplied, independently proved density/log-gradient Fisher
formula; it does not redefine Fisher information to make the identity true. -/
theorem fisher_eq_score_variance {rho : Torus 1 → Real}
    (hrho : SmoothProbability rho) :
    fisher rho = ∫ x, rho x * scoreTest rho x ^ 2 ∂haar 1 := by
  have hlog := contDiff_logD hrho.smooth hrho.positive
  have hg : IsWeakGrad (logD rho) (gLog rho) :=
    isWeakGrad_of_contDiff (hlog.of_le (by simp))
  obtain ⟨m, M, hm, hmrho, hrhoM⟩ :=
    Sec8.exists_pos_bounds (Sec8.continuous_of_smooth hrho.smooth) hrho.positive
  obtain ⟨B, hB⟩ := smoothGrad_bdd hlog (0 : Fin 1)
  have hgb : ∃ Cg : Real, ∀ y k, |gLog rho y k| ≤ Cg := by
    refine ⟨B, fun y k => ?_⟩
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    exact hB y
  have hF := fisherInfo_dens_torus
    (Sec8.continuous_of_smooth hrho.smooth).measurable
    (show Measurable (fun _ : Torus 1 => (1 : Real)) from measurable_const)
    (⟨m, M, hm, fun x => ⟨hmrho x, hrhoM x⟩⟩)
    (⟨1, 1, by norm_num, fun x => ⟨le_rfl, le_rfl⟩⟩)
    (by simp only [div_one]; exact hg) hgb
  have hF' : fisherInfo (densMeasure rho) (haar 1) =
      ∫⁻ x, ENNReal.ofReal (rho x * scoreTest rho x ^ 2) ∂haar 1 := by
    simp only [ENNReal.ofReal_one, withDensity_const, one_smul] at hF
    simp only [sqNorm, Fin.sum_univ_one, scoreTest] at hF
    exact hF
  have hi : Integrable (fun x => rho x * scoreTest rho x ^ 2) (haar 1) :=
    SharpLSI.integrable_of_continuous ((Sec8.continuous_of_smooth hrho.smooth).mul
      ((Sec8.continuous_of_smooth (scoreTest_smooth hrho)).pow 2))
  have h0 : ∀ x, 0 ≤ rho x * scoreTest rho x ^ 2 :=
    fun x => mul_nonneg (hrho.nonneg x) (sq_nonneg _)
  unfold fisher
  rw [hF', ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall h0),
    ENNReal.toReal_ofReal (integral_nonneg h0)]

theorem fisher_pos {rho : Torus 1 → Real}
    (h : Admissible cosV (cosW 1) rho) : 0 < fisher rho := by
  have hH := entropy_pos h
  have hprod := mul_pos a_pos hH
  have hdef := deficit_bound h
  have hn : 0 ≤ aCos / 6 * entropy rho ^ 2 := by
    have := a_pos.le
    positivity
  linarith

theorem scoreTest_variance_pos {rho : Torus 1 → Real}
    (h : SmoothOptimizer rho) :
    0 < ∫ x, rho x * scoreTest rho x ^ 2 ∂haar 1 := by
  rw [← fisher_eq_score_variance h.probability]
  exact fisher_pos h.admissible

end SharpLSI.FL.Prop82
