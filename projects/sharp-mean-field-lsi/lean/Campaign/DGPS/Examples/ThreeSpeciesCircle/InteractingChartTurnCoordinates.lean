import DGPS.Examples.ThreeSpeciesCircle.InteractingChartCoordinates
import DGPS.Examples.ThreeSpeciesCircle.InteractingSeedRotation

/-! Exact third-turn action on the retained amplitude/complement coordinates.
Seed identities follow from the SAME-D chart seed and bounded Fourier maps;
no implicit-function neighborhood invariance is asserted. -/

noncomputable section
open Filter Topology Set
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

def interactingThirdCoordinates (j : Fin 3) (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![z 0 * Real.cos (2 * Real.pi * ((j : ℕ) / 3)) - z 1 * Real.sin (2 * Real.pi * ((j : ℕ) / 3)),
    z 0 * Real.sin (2 * Real.pi * ((j : ℕ) / 3)) + z 1 * Real.cos (2 * Real.pi * ((j : ℕ) / 3)), z 2]

theorem interactingThirdCoordinates_continuous (j : Fin 3) :
    Continuous (interactingThirdCoordinates j) := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp only [interactingThirdCoordinates] <;> fun_prop

/-- Rotation of a full chart uses exactly the retained complement pullback. -/
theorem interactingChart_thirdTurn_decomposition (h : ℝ) (j : Fin 3)
    (z : Fin 3 → ℝ) (w : E_STR02969) :
    interactingC2Translate (2 * Real.pi * ((j : ℕ) / 3))
        ((h * z 0) • cosC2_STR02915 + (h * z 1) • sinC2_STR02915 + (w : PeriodicC2_STR02969)) =
      (h * interactingThirdCoordinates j z 0) • cosC2_STR02915 +
        (h * interactingThirdCoordinates j z 1) • sinC2_STR02915 +
          (pullE_STR02916 1 (Or.inl rfl) (-(2 * Real.pi * ((j : ℕ) / 3))) w : PeriodicC2_STR02969) := by
  apply Subtype.ext
  funext t
  change h * z 0 * Real.cos (1 * t + -(2 * Real.pi * ((j : ℕ) / 3))) +
      h * z 1 * Real.sin (1 * t + -(2 * Real.pi * ((j : ℕ) / 3))) +
      (w : PeriodicC2_STR02969).val (1 * t + -(2 * Real.pi * ((j : ℕ) / 3))) =
      h * interactingThirdCoordinates j z 0 * Real.cos t + h * interactingThirdCoordinates j z 1 * Real.sin t +
      (w : PeriodicC2_STR02969).val (1 * t + -(2 * Real.pi * ((j : ℕ) / 3)))
  simp only [PeriodicC2_STR02969.val_add, PeriodicC2_STR02969.val_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, cosC2_val_STR02915, sinC2_val_STR02915,
    pullE_val_STR02916, one_mul, sub_eq_add_neg, interactingThirdCoordinates,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rw [Real.cos_add, Real.sin_add, Real.cos_neg, Real.sin_neg]
  ring

/-- Full-chart equality determines the original amplitudes AND E complement. -/
theorem interactingChart_components_unique (a b a' b' : ℝ) (w w' : E_STR02969)
    (he : a • cosC2_STR02915 + b • sinC2_STR02915 + (w : PeriodicC2_STR02969) =
      a' • cosC2_STR02915 + b' • sinC2_STR02915 + (w' : PeriodicC2_STR02969)) :
    a = a' ∧ b = b' ∧ w = w' := by
  have h0 := interactingChart_seed_coordinates a b w
  have h1 := interactingChart_seed_coordinates a' b' w'
  have ha := congrArg interactingChartCos he
  have hb := congrArg interactingChartSin he
  rw [h0.1, h1.1] at ha
  rw [h0.2.1, h1.2.1] at hb
  refine ⟨ha, hb, ?_⟩
  rw [ha, hb] at he
  exact Subtype.ext (add_left_cancel he)

/-- The complement turn is continuous in its original full C2-Holder norm. -/
theorem interactingComplementTranslate_isometry (j : Fin 3) :
    Isometry (pullE_STR02916 1 (Or.inl rfl) (-(2 * Real.pi * ((j : ℕ) / 3)))) := by
  apply Isometry.of_dist_eq
  intro w v
  have he : pullE_STR02916 1 (Or.inl rfl) (-(2 * Real.pi * ((j : ℕ) / 3))) w -
      pullE_STR02916 1 (Or.inl rfl) (-(2 * Real.pi * ((j : ℕ) / 3))) v =
        pullE_STR02916 1 (Or.inl rfl) (-(2 * Real.pi * ((j : ℕ) / 3))) (w - v) := by
    apply Subtype.ext
    apply Subtype.ext
    funext t
    rfl
  rw [dist_eq_norm, dist_eq_norm, he, norm_pullE_STR02916]

/-- BOTH transported seed coordinates agree with the actual target graph seed;
the log-chart identity alone is not used to presume a graph domain invariant. -/
theorem ordinaryRoot_thirdTurn_components (D : OrdinaryRootGraphData) (h : ℝ) (hh : h ≠ 0)
    (hhr : h ∈ Ioo (-D.radius) D.radius) (j : Fin 3) :
    interactingThirdCoordinates j (D.Z 0 h) = D.Z j h ∧
      pullE_STR02916 1 (Or.inl rfl) (-(2 * Real.pi * ((j : ℕ) / 3)))
        (D.ψ (ptPar_STR02923 h (D.Z 0 h))) = D.ψ (ptPar_STR02923 h (D.Z j h)) := by
  have he := ordinaryRoot_chart_seed_thirdTurn D h hhr j
  change (h * D.Z j h 0) • cosC2_STR02915 + (h * D.Z j h 1) • sinC2_STR02915 +
    (D.ψ (ptPar_STR02923 h (D.Z j h)) : PeriodicC2_STR02969) =
    interactingC2Translate (2 * Real.pi * ((j : ℕ) / 3))
      ((h * D.Z 0 h 0) • cosC2_STR02915 + (h * D.Z 0 h 1) • sinC2_STR02915 +
        (D.ψ (ptPar_STR02923 h (D.Z 0 h)) : PeriodicC2_STR02969)) at he
  rw [interactingChart_thirdTurn_decomposition] at he
  have hc := interactingChart_components_unique
    (h * D.Z j h 0) (h * D.Z j h 1)
    (h * interactingThirdCoordinates j (D.Z 0 h) 0)
    (h * interactingThirdCoordinates j (D.Z 0 h) 1)
    (D.ψ (ptPar_STR02923 h (D.Z j h)))
    (pullE_STR02916 1 (Or.inl rfl) (-(2 * Real.pi * ((j : ℕ) / 3)))
      (D.ψ (ptPar_STR02923 h (D.Z 0 h)))) he
  refine ⟨?_, hc.2.2.symm⟩
  ext i
  fin_cases i
  · exact (mul_left_cancel₀ hh hc.1).symm
  · exact (mul_left_cancel₀ hh hc.2.1).symm
  · change D.Z 0 h 2 = D.Z j h 2
    exact (D.Z_rate_same h hhr j).symm

end DGPS.Examples.ThreeSpeciesCircle
