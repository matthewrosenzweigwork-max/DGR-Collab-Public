import DGPS.Examples.PolynomialLogProfileSmallness
import DGPS.Examples.PolynomialSpeciesEulerCanonical
import DGPS.Frontier.STR029.T65

/-! The actual original-density logarithmic profile is centered in the retained
angular C2,1/2 space. Its partition is computed from original mass one before
identifying the normalized chart with the same original density. -/

noncomputable section
open MeasureTheory Filter Topology Function
open DGPS.PositiveRankOne DGPS.Examples.ThreeSpeciesCircle
open DGPS.Circle.AngularNormalization DGPS.Circle.StationaryFlux
open DGPS.Frontier.STR029 DGPS.Analysis.PeriodicHolder

namespace DGPS.Examples.PolynomialSpecies

private theorem constant_c2 (c : ℝ) : IsC2Alpha_STR02901 (1 / 2) (fun _ : ℝ => c) := by
  have hd : deriv (fun _ : ℝ => c) = (0 : ℝ → ℝ) := funext fun t : ℝ => deriv_const t c
  have hz := IsPerHolder_STR02968.zero (1 / 2 : ℝ)
  refine ⟨fun _ => rfl, differentiable_const _, ?_, ?_, ?_⟩
  · rw [hd]
    exact differentiable_const _
  · rw [hd, deriv_zero_fun_STR02969]
    exact hz.2.1
  · rw [hd, deriv_zero_fun_STR02969]
    exact hz.2.2

private def constant_chart (c : ℝ) : PeriodicC2_STR02969 :=
  PeriodicC2_STR02969.mk (fun _ => c) (constant_c2 c)

private theorem constant_chart_norm (c : ℝ) : ‖constant_chart c‖ = |c| := by
  have hd : deriv (fun _ : ℝ => c) = (0 : ℝ → ℝ) := funext fun t : ℝ => deriv_const t c
  have hsup : supNorm (fun _ : ℝ => c) = |c| := by unfold supNorm; rw [ciSup_const]
  have hz : supNorm (0 : ℝ → ℝ) = 0 := by
    apply le_antisymm (supNorm_le fun t : ℝ => by simp)
    exact supNorm_nonneg _
  have hc : circHolder_STR02901 (1 / 2) (0 : ℝ → ℝ) = 0 := by
    apply le_antisymm
      (circHolder_le_STR02953 (by norm_num : (0 : ℝ) < 1 / 2) le_rfl fun s t => by simp)
    exact circHolder_nonneg_STR02953 _ _
  change c2Norm_STR02901 (1 / 2) (fun _ : ℝ => c) = |c|
  rw [c2Norm_parts_STR02969, hd, deriv_zero_fun_STR02969, hsup, hz, hc]
  ring

/-- Haar centering of a genuine retained logarithmic chart. -/
def polynomialCenteredLogChart (u : PeriodicC2_STR02969) : PeriodicC2_STR02969 :=
  u - constant_chart (meanT_STR02901 u.val)

theorem polynomialCenteredLogChart_mean (u : PeriodicC2_STR02969) :
    meanT_STR02901 (polynomialCenteredLogChart u).val = 0 := by
  change meanT_STR02965 (fun t : ℝ => u.val t - meanT_STR02965 u.val) = 0
  exact meanT_sub_self_STR02965 u.isC2.2.1.continuous

theorem polynomialCenteredLogChart_norm (u : PeriodicC2_STR02969) :
    ‖polynomialCenteredLogChart u‖ ≤ 2 * ‖u‖ := by
  have hb := (bdd_parts_STR02969 u.isC2).1
  have hm : |meanT_STR02901 u.val| ≤ ‖u‖ :=
    (abs_meanT_le_STR02953 fun t : ℝ => hb.abs_le_supNorm t).trans (le_c2Norm_STR02969 u.val).1
  exact (norm_sub_le u _).trans (by rw [constant_chart_norm]; linarith)

/-- The normalized centered chart recovers the exact uncentered density when
its original mass is one. The normalization constant is not suppressed. -/
theorem polynomialCenteredLogChart_density (h : ℝ) (u : PeriodicC2_STR02969)
    (hmass : meanT_STR02901 (fun t : ℝ => (polynomialRankOne h).q (angEquiv.symm (t : AngCircle)) *
      Real.exp (u.val t)) = 1) (x : Torus 1) :
    (polynomialChartAbsolute h (polynomialCenteredLogChart u)).density x =
      (polynomialRankOne h).q x * Real.exp (u.val (angSec (angEquiv x))) := by
  let c := meanT_STR02901 u.val
  have hv (t : ℝ) : (polynomialCenteredLogChart u).val t = u.val t - c := rfl
  have hZ : meanT_STR02901 (fun t : ℝ => (polynomialRankOne h).q (angEquiv.symm (t : AngCircle)) *
      Real.exp ((polynomialCenteredLogChart u).val t)) = Real.exp (-c) := by
    simp_rw [hv, show ∀ a : ℝ, Real.exp (a - c) = Real.exp (-c) * Real.exp a from
      fun a => by rw [sub_eq_add_neg, Real.exp_add]; ring]
    have he : (fun t : ℝ => (polynomialRankOne h).q (angEquiv.symm (t : AngCircle)) *
        (Real.exp (-c) * Real.exp (u.val t))) =
        fun t : ℝ => Real.exp (-c) * ((polynomialRankOne h).q (angEquiv.symm (t : AngCircle)) * Real.exp (u.val t)) := by
      funext t
      ring
    rw [he, meanT_const_mul_STR02962, hmass, mul_one]
  rw [polynomialChartAbsolute_density, polynomialEuler_density_val, hZ, hv,
    coe_angSec, MeasurableEquiv.symm_apply_apply]
  rw [show Real.exp (u.val (angSec (angEquiv x)) - c) =
    Real.exp (-c) * Real.exp (u.val (angSec (angEquiv x))) from by
      rw [sub_eq_add_neg, Real.exp_add]; ring]
  field_simp [(Real.exp_pos (-c)).ne']
  <;> ring

private theorem point_angular (t : ℝ) : pt (t / (2 * Real.pi)) = angEquiv.symm (t : AngCircle) := by
  apply angEquiv.injective
  rw [MeasurableEquiv.apply_symm_apply, angEquiv_apply]
  change angRescale ((t / (2 * Real.pi) : ℝ) : UnitAddCircle) = (t : AngCircle)
  rw [angRescale_mk]
  congr 1
  field_simp [Real.pi_ne_zero]

/-- Actual original-domain minimizers at vanishing fields have a subsequence
represented by the SAME normalized mean-zero C2,1/2 charts, whose full norms
vanish. The chart dictionary and mass normalization are proved internally. -/
theorem polynomial_scalarMinimizer_centered_chart_capture (h : ℕ → ℝ)
    (hh : Tendsto h atTop (𝓝 0))
    (b : ∀ n, AbsoluteDrift (canonical_elementary_polynomial_model (h n)))
    (ρ : ℕ → AbsoluteDensity 1)
    (hG : ∀ n, 0 < scalarGap (canonical_elementary_polynomial_model (h n)) (ρ n))
    (hmin : ∀ n, scalarQuotient (canonical_elementary_polynomial_model (h n)) (b n) (ρ n) =
      scalarRate (canonical_elementary_polynomial_model (h n)) (b n)) :
    ∃ φ : ℕ → ℕ, ∃ u : ℕ → PeriodicC2_STR02969, StrictMono φ ∧
      (∀ n, meanT_STR02901 (u n).val = 0) ∧
      (∀ n, (ρ (φ n)).density =ᵐ[haar 1] (polynomialChartAbsolute (h (φ n)) (u n)).density) ∧
      Tendsto (fun n => ‖u n‖) atTop (𝓝 0) := by
  obtain ⟨φ, f, hφ, hfs, hdensity, hC2, hnorm⟩ :=
    polynomial_scalarMinimizer_log_profile_C2_capture h hh b ρ hG hmin
  let w := fun n => PeriodicC2_STR02969.mk (fun t : ℝ => f n (pt (t / (2 * Real.pi)))) (hC2 n)
  let u := fun n => polynomialCenteredLogChart (w n)
  have hw (n : ℕ) (x : Torus 1) : (w n).val (angSec (angEquiv x)) = f n x := by
    change f n (pt (angSec (angEquiv x) / (2 * Real.pi))) = f n x
    rw [point_angular, coe_angSec, MeasurableEquiv.symm_apply_apply]
  have hmass (n : ℕ) : meanT_STR02901 (fun t : ℝ =>
      (polynomialRankOne (h (φ n))).q (angEquiv.symm (t : AngCircle)) * Real.exp ((w n).val t)) = 1 := by
    let F := fun t : ℝ => (polynomialRankOne (h (φ n))).q (angEquiv.symm (t : AngCircle)) * Real.exp ((w n).val t)
    have he : (fun x => F (angSec (angEquiv x))) =
        fun x => (polynomialRankOne (h (φ n))).q x * Real.exp (f n x) := by
      funext x
      dsimp only [F]
      rw [coe_angSec, MeasurableEquiv.symm_apply_apply, hw]
    calc
      _ = ∫ x, F (angSec (angEquiv x)) ∂haar 1 := by
        rw [integral_comp_angEquiv (fun θ => F (angSec θ)), integral_angSec_STR02962]
        rfl
      _ = ∫ x, (ρ (φ n)).density x ∂haar 1 := by
        rw [he]
        exact integral_congr_ae (hdensity n).symm
      _ = 1 := (ρ (φ n)).mass_one
  refine ⟨φ, u, hφ, fun n => polynomialCenteredLogChart_mean (w n), ?_, ?_⟩
  · intro n
    filter_upwards [hdensity n] with x hx
    rw [hx, polynomialCenteredLogChart_density _ _ (hmass n), hw]
  · have hwlim : Tendsto (fun n => ‖w n‖) atTop (𝓝 0) := hnorm
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => polynomialCenteredLogChart_norm (w n))
      (by simpa using hwlim.const_mul 2)

end DGPS.Examples.PolynomialSpecies
