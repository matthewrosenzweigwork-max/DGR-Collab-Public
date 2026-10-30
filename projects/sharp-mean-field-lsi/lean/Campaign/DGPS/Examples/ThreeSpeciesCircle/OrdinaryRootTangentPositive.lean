import DGPS.Examples.ThreeSpeciesCircle.OrdinaryReducedHessianPositive
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryReducedHessianScale
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryHessianSchur
import DGPS.Examples.ThreeSpeciesCircle.OrdinarySecondVariation

/-! Actual tangent positivity with the unscaled-amplitude normalization. The reduced
amplitude Hessian is multiplied by h²; the chart Hessian is twice the covariance form. -/

noncomputable section
open MeasureTheory Filter Set Real
open scoped ContDiff Topology
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- A common positive tangent bound for all three retained ordinary roots.
The graph, actual critical roots, and reduced amplitude positivity are constructed
upstream; no Hessian positivity premise is added here. -/
theorem ordinaryRoot_amplitude_tangent_positive (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧
      ∀ h : ℝ, 0 < h → h < δ → ∀ j : Fin 3, ∀ v : ℝ × ℝ,
        let u := Lamp_STR02956 D.ψ (h, h ^ 2 * D.Z j h 2)
          (h * D.Z j h 0, h * D.Z j h 1)
        let T := fderiv ℝ (Lamp_STR02956 D.ψ (h, h ^ 2 * D.Z j h 2))
          (h * D.Z j h 0, h * D.Z j h 1) v
        (h ^ 2 / 24) * (v.1 ^ 2 + v.2 ^ 2) ≤
          ordinaryRootHessianQuadratic (rhoT_STR02901 h u.val)
            (1 + h ^ 2 * D.Z j h 2) T.val (deriv T.val) := by
  obtain ⟨δ, hδ, hδr, hpos⟩ := ordinaryReduced_amplitude_hessian_positive D
  refine ⟨δ, hδ, hδr, fun h hh hhd j v => ?_⟩
  have hhr : h ∈ Ioo (-D.radius) D.radius := by
    constructor <;> linarith [D.radius_pos, hhd.trans_le hδr]
  let γ := h ^ 2 * D.Z j h 2
  let x : ℝ × ℝ := (h * D.Z j h 0, h * D.Z j h 1)
  let u := Lamp_STR02956 D.ψ (h, γ) x
  let T := fderiv ℝ (Lamp_STR02956 D.ψ (h, γ)) x v
  have hU : iota_STR02956 (h, γ) x ∈ D.U := D.branch_memU j h hhr
  have hc : ∀ t, gradG_STR02950 h γ u.val t = 0 := by
    intro t
    exact D.chart_critical h hhr j t
  have hvec : (![D.Z j h 0, D.Z j h 1, D.Z j h 2] : Fin 3 → ℝ) = D.Z j h := by
    ext i; fin_cases i <;> rfl
  have hO : (h, ![D.Z j h 0, D.Z j h 1, D.Z j h 2]) ∈ D.O := by
    rw [hvec]
    exact D.branch_memO j h hhr
  have hs := ordinaryReduced_hessian_scale D.ψ D.reduced D.openO D.reduced_value
    h (D.Z j h 2) hh.ne' (D.Z j h 0, D.Z j h 1) v v hO
  have hr := ordinaryRangeGraph_reduced_hessian_at_critical D.openU D.smoothψ
    h γ x v v hU hc
  have hH := OrdinarySecondVariation.hessian_JC2_eq_weighted_form h γ u T T hc
  have hk : meanT_STR02901 (fun t => deriv T.val t * deriv T.val t * rhoT_STR02901 h u.val t) =
      normInt_STR02933 (fun t => rhoT_STR02901 h u.val t * deriv T.val t ^ 2) := by
    rw [← normInt_eq_meanT_STR02962]
    congr 1; funext t; ring
  have hp : meanT_STR02901 (fun t => T.val t * T.val t * rhoT_STR02901 h u.val t) =
      normInt_STR02933 (fun t => rhoT_STR02901 h u.val t * T.val t ^ 2) := by
    rw [← normInt_eq_meanT_STR02962]
    congr 1; funext t; ring
  have hm : meanT_STR02901 (fun t => T.val t * rhoT_STR02901 h u.val t) =
      normInt_STR02933 (fun t => rhoT_STR02901 h u.val t * T.val t) := by
    rw [← normInt_eq_meanT_STR02962]
    congr 1; funext t; ring
  rw [hk, hp, hm] at hH
  have hhalf : fderiv ℝ (fderiv ℝ (JC2_STR02956 h γ)) u T T =
      2 * ordinaryRootHessianQuadratic (rhoT_STR02901 h u.val) (1 + γ) T.val (deriv T.val) := by
    rw [hH]
    unfold ordinaryRootHessianQuadratic
    ring
  have hp0 := hpos h (by rw [abs_of_pos hh]; exact hhd) j v
  have hp1 := mul_le_mul_of_nonneg_left hp0 (sq_nonneg h)
  have hscale : fderiv ℝ (fderiv ℝ (fun y => Fred_STR02956 D.ψ y (h, γ))) x v v =
      h ^ 2 * fderiv ℝ (fderiv ℝ (fun y : ℝ × ℝ =>
        D.reduced (h, ![y.1, y.2, D.Z j h 2]))) (D.Z j h 0, D.Z j h 1) v v := hs
  rw [hr, hhalf] at hscale
  change (h ^ 2 / 24) * (v.1 ^ 2 + v.2 ^ 2) ≤
    ordinaryRootHessianQuadratic (rhoT_STR02901 h u.val) (1 + γ) T.val (deriv T.val)
  nlinarith

end DGPS.Examples.ThreeSpeciesCircle
