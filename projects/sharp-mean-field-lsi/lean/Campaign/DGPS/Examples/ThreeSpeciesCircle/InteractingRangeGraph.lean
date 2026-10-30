import DGPS.Examples.ThreeSpeciesCircle.InteractingChartCalculus

/-! Local range graphs for the explicit fixed-h nonlinear feedback map. The
map is the one defined in InteractingChartCalculus; the native variational
identification and the augmented finite-dimensional deficit equation are separate. -/

noncomputable section
open Filter Topology Set
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem interacting_range_partial_zero (h a b γ : ℝ) (w : E_STR02969) :
    fderiv ℝ (interactingChartRange h) ((0, a, b, γ), w) ∘L
        ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ × ℝ) E_STR02969 =
      fderiv ℝ Fp_STR02916 ((a, b, h, γ), w) ∘L
        ContinuousLinearMap.inr ℝ Par_STR02916 E_STR02969 := by
  have heq : (fun z : E_STR02969 => interactingChartRange h ((0, a, b, γ), z)) =
      fun z => Fp_STR02916 ((a, b, h, γ), z) := by
    funext z
    exact interactingChartRange_zero h a b γ z
  have hleft := (((interactingChartRange_smooth h).differentiable (by simp))
    ((0, a, b, γ), w)).hasFDerivAt.comp w
      (hasFDerivAt_prodMk_right (0, a, b, γ) w)
  have hright := ((Fp_smooth_STR02916.differentiable (by simp))
    ((a, b, h, γ), w)).hasFDerivAt.comp w
      (hasFDerivAt_prodMk_right (a, b, h, γ) w)
  have hleftD : fderiv ℝ (fun z : E_STR02969 =>
      interactingChartRange h ((0, a, b, γ), z)) w =
      fderiv ℝ (interactingChartRange h) ((0, a, b, γ), w) ∘L
        ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ × ℝ) E_STR02969 := hleft.fderiv
  have hrightD : fderiv ℝ (fun z : E_STR02969 => Fp_STR02916 ((a, b, h, γ), z)) w =
      fderiv ℝ Fp_STR02916 ((a, b, h, γ), w) ∘L
        ContinuousLinearMap.inr ℝ Par_STR02916 E_STR02969 := hright.fderiv
  rw [← hleftD, ← hrightD]
  exact congrArg (fderiv ℝ · w) heq

/-- At each fixed small h, each SAME ordinary branch has a genuine smooth local
complement graph for every nearby real coupling, amplitude and rate parameter.
This statement asserts only the zero set of the explicit range map. -/
theorem interactingChartRange_local_graphs (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, |h| < δ → ∀ j : Fin 3,
      let p0 : ℝ × ℝ × ℝ × ℝ := (0, h * D.Z j h 0, h * D.Z j h 1, h ^ 2 * D.Z j h 2)
      let w0 := D.ψ (ptPar_STR02923 h (D.Z j h))
      ∃ (U : Set (ℝ × ℝ × ℝ × ℝ)) (V : Set E_STR02969)
          (ψ : (ℝ × ℝ × ℝ × ℝ) → E_STR02969),
        IsOpen U ∧ p0 ∈ U ∧ IsOpen V ∧ w0 ∈ V ∧ ContDiffOn ℝ ∞ ψ U ∧
          ψ p0 = w0 ∧ (∀ p ∈ U, ψ p ∈ V) ∧
            ∀ p ∈ U, ∀ w ∈ V, interactingChartRange h (p, w) = 0 ↔ ψ p = w := by
  letI : CompleteSpace E_STR02969 :=
    str029_69_completeness_closed_complements_range_spaces_E.2.2
  letI : CompleteSpace Y_STR02969 :=
    str029_69_completeness_closed_complements_range_spaces_Y.2.2
  obtain ⟨δ, hδ, hδr, hinv⟩ := ordinaryRoot_range_partial_invertible D
  refine ⟨δ, hδ, hδr, fun h hh j => ?_⟩
  let p0 : ℝ × ℝ × ℝ × ℝ :=
    (0, h * D.Z j h 0, h * D.Z j h 1, h ^ 2 * D.Z j h 2)
  let w0 := D.ψ (ptPar_STR02923 h (D.Z j h))
  have hhr : h ∈ Ioo (-D.radius) D.radius := abs_lt.mp (hh.trans_le hδr)
  have hU := D.branch_memU j h hhr
  have hV := D.memψ _ hU
  have hzero : interactingChartRange h (p0, w0) = 0 := by
    rw [show p0 = (0, h * D.Z j h 0, h * D.Z j h 1, h ^ 2 * D.Z j h 2) from rfl,
      interactingChartRange_zero]
    exact (D.range_eq _ hU _ hV).mpr rfl
  have hpartial : (fderiv ℝ (interactingChartRange h) (p0, w0) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ × ℝ) E_STR02969).IsInvertible := by
    dsimp only [p0]
    rw [interacting_range_partial_zero]
    exact hinv h hh j
  exact implicit_graph_STR02916 (interactingChartRange_smooth h) hzero hpartial

end DGPS.Examples.ThreeSpeciesCircle
