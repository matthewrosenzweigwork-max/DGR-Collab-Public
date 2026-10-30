import DGPS.Examples.PolynomialSpeciesRangeRestriction
import DGPS.Examples.PolynomialSpeciesRangeDerivative
import DGPS.Frontier.STR029.T24

/-! The actual rate envelope along the interacting graph. The graph moves with the
rate; its contribution cancels by the genuine projected Euler equation. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029
open DGPS.Circle.AngularNormalization DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

/-- Actual gap in the normalized moving-reference logarithmic chart. -/
def polynomialChartGap (h : ℝ) (u : PeriodicC2_STR02969) : ℝ :=
  eulerEntropy (polynomialLogReference h) u + eta *
    (eulerMean (polynomialLogReference h) u (polynomialEulerFeature h)) ^ 2 / 2

private theorem chart_smooth (h r : ℝ) :
    ContDiff ℝ ∞ (polynomialChartGap h) ∧ ContDiff ℝ ∞ (polynomialChartDeficit h r) := by
  let L := polynomialLogReference h
  have hρ : ContDiff ℝ ∞ (eulerDensity L) :=
    rho_smooth_STR02954.comp (contDiff_const.prodMk (contDiff_const.add e0_STR02955.contDiff))
  have hmean (f : PeriodicHolder_STR02968) : ContDiff ℝ ∞ (fun u : PeriodicC2_STR02969 => eulerMean L u f) :=
    meanCLM_STR02954.contDiff.comp (contDiff_const.mul hρ)
  have hH : ContDiff ℝ ∞ (eulerEntropy L) :=
    ((meanCLM_STR02954.contDiff.comp (e0_STR02955.contDiff.mul hρ)).sub
      (logZ_smooth_STR02954.comp (contDiff_const.prodMk (contDiff_const.add e0_STR02955.contDiff)))).add contDiff_const
  have hI : ContDiff ℝ ∞ (eulerFisher L) :=
    contDiff_const.mul (meanCLM_STR02954.contDiff.comp
      ((e1_STR02955.contDiff.mul e1_STR02955.contDiff).mul hρ))
  have hm := hmean (polynomialEulerFeature h)
  have hA := hmean (polynomialEulerGenerator h)
  have hJ := hmean (polynomialEulerGradientSq h)
  constructor
  · exact hH.add ((contDiff_const.mul (hm.pow 2)).div_const 2)
  · exact ((hI.add ((contDiff_const.mul hm).mul hA)).add
      ((contDiff_const.mul (hm.pow 2)).mul hJ)).sub
      (contDiff_const.mul (hH.add ((contDiff_const.mul (hm.pow 2)).div_const 2)))

private theorem pair_zero_of_projection_zero (g : PeriodicHolder_STR02968)
    (hg : PY_STR02955 g = 0) (v : E_STR02969) :
    meanCLM_STR02954 (g * e0_STR02955 (v : PeriodicC2_STR02969)) = 0 := by
  have hv := (str029_69_completeness_closed_complements_range_spaces_E.1 _).1 v.2
  have hp : ∀ t, projP_STR02953 g.val t = 0 := by
    intro t
    have h := congrFun (congrArg PeriodicHolder_STR02968.val (congrArg Subtype.val hg)) t
    rw [PY_val_STR02955] at h
    exact h
  exact meanT_mul_inE_STR02924 (v : PeriodicC2_STR02969).isC2.2.1.continuous hv hp

/-- A genuine zero of the projected Euler map annihilates every complement direction. -/
theorem polynomialChartDeficit_complement_zero (h r : ℝ) (u : PeriodicC2_STR02969)
    (hu : PY_STR02955 (polynomialEulerGradient h r u) = 0) (v : E_STR02969) :
    fderiv ℝ (polynomialChartDeficit h r) u (v : PeriodicC2_STR02969) = 0 := by
  rw [polynomialChartDeficit_fderiv_strong]
  exact pair_zero_of_projection_zero _ hu v

/-- Along any differentiable actual complement solution curve, the total rate derivative
is the partial rate derivative. The complement motion is not silently held fixed. -/
theorem polynomialChartDeficit_rate_envelope (h a b γ : ℝ) (w : ℝ → E_STR02969)
    (v : E_STR02969) (hw : HasDerivAt w v γ)
    (hR : PY_STR02955 (polynomialEulerGradient h
      (DGPS.Circle.AngularNormalization.a0 * (1 + γ))
      (a • cosC2_STR02915 + b • sinC2_STR02915 + (w γ : PeriodicC2_STR02969))) = 0) :
    HasDerivAt (fun τ : ℝ => polynomialChartDeficit h
      (DGPS.Circle.AngularNormalization.a0 * (1 + τ))
      (a • cosC2_STR02915 + b • sinC2_STR02915 + (w τ : PeriodicC2_STR02969)))
      (-2 * DGPS.Circle.AngularNormalization.a0 * polynomialChartGap h
        (a • cosC2_STR02915 + b • sinC2_STR02915 + (w γ : PeriodicC2_STR02969))) γ := by
  let r := DGPS.Circle.AngularNormalization.a0 * (1 + γ)
  let u := fun τ : ℝ => a • cosC2_STR02915 + b • sinC2_STR02915 + (w τ : PeriodicC2_STR02969)
  have hu : HasDerivAt u (v : PeriodicC2_STR02969) γ :=
    (E_STR02969.subtypeL.hasFDerivAt.comp_hasDerivAt γ hw).const_add _
  have hd := ((chart_smooth h r).2.differentiable (by simp) (u γ)).hasFDerivAt.comp_hasDerivAt γ hu
  have hzero : fderiv ℝ (polynomialChartDeficit h r) (u γ) (v : PeriodicC2_STR02969) = 0 :=
    polynomialChartDeficit_complement_zero h r (u γ) hR v
  rw [hzero] at hd
  have hG := ((chart_smooth h r).1.differentiable (by simp) (u γ)).hasFDerivAt.comp_hasDerivAt γ hu
  have ht := (hasDerivAt_id γ).sub_const γ
  have hder := hd.sub (((ht.mul hG).const_mul (2 * DGPS.Circle.AngularNormalization.a0)))
  have he : (fun τ : ℝ => polynomialChartDeficit h
      (DGPS.Circle.AngularNormalization.a0 * (1 + τ)) (u τ)) =
      fun τ : ℝ => polynomialChartDeficit h r (u τ) -
        2 * DGPS.Circle.AngularNormalization.a0 * ((τ - γ) * polynomialChartGap h (u τ)) := by
    funext τ
    unfold polynomialChartDeficit polynomialChartGap
    dsimp only [r]
    ring
  simp only [Function.comp_apply, id_eq, sub_self, zero_mul, add_zero, one_mul, zero_sub] at hder
  rw [he]
  convert hder using 1
  · funext τ
    simp only [Function.comp_apply, Pi.sub_apply, Pi.mul_apply] <;> ring
  · ring

/-- The graph is produced by the actual interacting IFT; its selected-root rate curves
satisfy the actual envelope identity on the same open parameter neighborhood. -/
theorem exists_polynomial_range_graph_envelope :
    ∃ (U : Set PolynomialRangeParameters) (N : Set E_STR02969)
      (ψ : PolynomialRangeParameters → E_STR02969),
      IsOpen U ∧ (0 : PolynomialRangeParameters) ∈ U ∧ IsOpen N ∧ (0 : E_STR02969) ∈ N ∧
      ContDiffOn ℝ ∞ ψ U ∧ (∀ p ∈ U, ψ p ∈ N) ∧
      (∀ p ∈ U, ∀ z ∈ N, polynomialRangeMap (p, z) = 0 ↔ ψ p = z) ∧
      ∀ a b h γ : ℝ, ((a, b, (h, root_EX054 h), γ) : PolynomialRangeParameters) ∈ U →
        HasDerivAt (fun τ : ℝ => polynomialChartDeficit h
          (DGPS.Circle.AngularNormalization.a0 * (1 + τ))
          (a • cosC2_STR02915 + b • sinC2_STR02915 +
            (ψ (a, b, (h, root_EX054 h), τ) : PeriodicC2_STR02969)))
          (-2 * DGPS.Circle.AngularNormalization.a0 * polynomialChartGap h
            (a • cosC2_STR02915 + b • sinC2_STR02915 +
              (ψ (a, b, (h, root_EX054 h), γ) : PeriodicC2_STR02969))) γ := by
  obtain ⟨U, N, ψ, hU, h0U, hN, h0N, hψ, hψN, hgraph, hzero⟩ := exists_polynomial_range_graph
  refine ⟨U, N, ψ, hU, h0U, hN, h0N, hψ, hψN, hgraph, ?_⟩
  intro a b h γ hp
  let w := fun τ : ℝ => ψ (a, b, (h, root_EX054 h), τ)
  have hw : DifferentiableAt ℝ w γ :=
    ((hψ.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).comp γ (by fun_prop)
  apply polynomialChartDeficit_rate_envelope h a b γ w (deriv w γ) hw.hasDerivAt
  have hR := (hgraph _ hp _ (hψN _ hp)).2 rfl
  change PY_STR02955 (polynomialRangeEuler (h, root_EX054 h)
    (DGPS.Circle.AngularNormalization.a0 * (1 + γ))
    (a • cosC2_STR02915 + b • sinC2_STR02915 + (w γ : PeriodicC2_STR02969))) = 0 at hR
  rw [polynomialRangeEuler_actual] at hR
  exact hR

end DGPS.Examples.PolynomialSpecies
