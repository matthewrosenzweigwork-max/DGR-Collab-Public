import DGPS.Lipschitz.MinimizerTopology
import DGPS.Particle.DiagonalForce

/-!
# Bounded mean-field data from direct Lipschitz potentials

The positive-rate contraction theorem takes everywhere bounded measurable drift
representatives. Clipping weak gradients on their null exceptional sets constructs those
inputs without imposing an additional hypothesis on the interaction data.
-/

open MeasureTheory Filter

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- Direct Lipschitz data supply all the drift inputs of the mean-field flow. -/
theorem exists_meanFieldData_of_lipschitz (A : InteractionData d)
    (hLip : LipschitzData A) :
    ∃ (G : Torus d → Tangent d) (B : Torus d → Torus d → Tangent d) (g β : ℝ),
      MeanFieldData G B g β ∧ IsWeakGradient A.V G ∧
        ∀ᵐ y ∂haar d, IsWeakGradientLp ⊤ (fun x => A.W x y) (fun x => B x y) := by
  classical
  obtain ⟨LV, hLV⟩ := hLip.V_lipschitz
  have hV : TorusLipschitzWith |LV| A.V := fun x y =>
    (hLV x y).trans (mul_le_mul_of_nonneg_right (le_abs_self LV) (Real.sqrt_nonneg _))
  obtain ⟨hVG, hVGbound⟩ := exists_weak_gradient (abs_nonneg LV) hV
  let G : Torus d → Tangent d := fun x =>
    if ‖smoothGrad A.V x‖ ≤ |LV| then smoothGrad A.V x else 0
  have hGm : Measurable G :=
    Measurable.ite (measurableSet_le measurable_smoothGrad.norm measurable_const)
      measurable_smoothGrad measurable_const
  have hGb : ∀ x, ‖G x‖ ≤ |LV| := by
    intro x
    dsimp only [G]
    split_ifs with hx
    · exact hx
    · simpa using abs_nonneg LV
  have hGae : smoothGrad A.V =ᵐ[haar d] G := by
    filter_upwards [hVGbound] with x hx
    simp [G, hx]
  have hGw : IsWeakGradient A.V G := by
    have hw : IsWeakGradient A.V (smoothGrad A.V) :=
      isWeakGradient_iff_isWeakGradientLp.mpr
        ⟨hVG.memLp.mono_exponent (by simp), hVG.memLp_grad.mono_exponent (by simp), hVG.ibp⟩
    exact hw.congr_ae (EventuallyEq.refl _ _) hGae
  obtain ⟨LW, hLW⟩ := hLip.W_lipschitz
  have hW : ∀ x y x' y', |A.W x y - A.W x' y'| ≤
      |LW| * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2) :=
    df_abs_bound hLW
  obtain ⟨B, hBm, hBb, hBw⟩ := df_exists_B (abs_nonneg LW) hW
  refine ⟨G, B, |LV|, |LW|,
    ⟨abs_nonneg LV, abs_nonneg LW, hGm, hBm, hGb, hBb⟩, hGw, ?_⟩
  refine Eventually.of_forall fun y => ?_
  have hsec : TorusLipschitzWith |LW| (fun x => A.W x y) := df_section_lipschitz hW y
  have hu := (exists_weak_gradient (abs_nonneg LW) hsec).1
  have hm : Measurable (fun x => B x y) :=
    hBm.comp (measurable_id.prodMk measurable_const)
  exact ⟨hu.memLp,
    memLp_top_of_bound hm.aestronglyMeasurable |LW| (Eventually.of_forall fun x => hBb x y),
    (hBw y).ibp⟩

/-- The full weak minimizer space is contractible under the direct Lipschitz hypotheses
and positive scalar rate; the bounded flow representatives are constructed internally. -/
theorem minimizer_set_contractible_of_lipschitz_positive_scalarRate
    (A : InteractionData d) (hLip : LipschitzData A) (b : AbsoluteDrift A)
    (hrate : 0 < scalarRate A b) :
    ContractibleSpace {ν : ProbabilityMeasure (Torus d) //
      DGPS.freeEnergy A ν = DGPS.freeEnergyMinimum A} := by
  obtain ⟨G, B, g, β, hMF, hV, hWB⟩ := exists_meanFieldData_of_lipschitz A hLip
  obtain ⟨μ, hμ⟩ := DGPS.freeEnergy_minimum_exists A
  exact minimizer_set_contractible_of_positive_scalarRate A b hMF hV hWB hrate μ hμ

end DGPS.Lipschitz
