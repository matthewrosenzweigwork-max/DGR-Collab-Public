import DGPS.Examples.ThreeSpeciesCircle.OrdinaryGroundStateRoots
import DGPS.Frontier.STR029.T26s2

/-!
# Native full weighted form domain at an ordinary root

Every native weighted weak-H1 test at the actual root is transported to the existing
real periodic weak-H1 domain. The angular derivative is the physical derivative divided
by `2*pi`. The bounded positive reference is constructed from the actual continuous
square-root representative and proved to have exactly the same probability measure.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The genuine Haar weak gradient of EVERY native weighted H1 test at an actual
positive continuous ordinary-root representative, with its SAME original gradient. -/
theorem ordinaryRoot_nativeTest_haarWeakGradient (σ : AbsoluteDensity 1)
    (u : Torus 1 → ℝ) (hu : Continuous u) (hupos : ∀ x, 0 < u x)
    (hurep : σ.sqrt =ᵐ[haar 1] u) (f : WeakH1Test (densityMeasure σ)) :
    IsWeakGradient f.fn f.grad := by
  have huc : Continuous (fun x => u x ^ 2) := hu.pow 2
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty huc.continuousOn
  obtain ⟨x1, -, hx1⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty huc.continuousOn
  have hmass : ∫ x, u x ^ 2 ∂haar 1 = 1 := by
    calc
      (∫ x, u x ^ 2 ∂haar 1) = ∫ x, σ.sqrt x ^ 2 ∂haar 1 := by
        apply integral_congr_ae
        filter_upwards [hurep] with x hx
        rw [hx]
      _ = 1 := σ.mass_one
  let P : BoundedPositiveReference 1 :=
    { density := fun x => u x ^ 2
      measurable_density := huc.measurable
      lower := u x0 ^ 2
      upper := u x1 ^ 2
      lower_pos := sq_pos_of_pos (hupos x0)
      lower_le := Eventually.of_forall fun x => hx0 (Set.mem_univ x)
      le_upper := Eventually.of_forall fun x => hx1 (Set.mem_univ x)
      mass_one := hmass }
  have hPmeasure : P.measure = (densityMeasure σ : Measure (Torus 1)) := by
    apply withDensity_congr_ae
    filter_upwards [hurep] with x hx
    change ENNReal.ofReal (u x ^ 2) = ENNReal.ofReal (σ.sqrt x ^ 2)
    rw [hx]
  have hPprob : (⟨P.measure, P.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus 1)) =
      densityMeasure σ := by
    exact ProbabilityMeasure.toMeasure_injective hPmeasure
  have hF : IsMeasureWeakGradient
      (⟨P.measure, P.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus 1)) f.fn f.grad :=
    (congrArg (fun ν : ProbabilityMeasure (Torus 1) =>
      IsMeasureWeakGradient ν f.fn f.grad) hPprob).mpr f.isWeak
  exact (isWeightedWeakGradient_iff P).mp ((isMeasureWeakGradient_iff P).mp hF)

/-- Full native weighted tests at the root have the exact real periodic H1 representation.
No Poincare, coercivity, smoothness of the test, or desired form inequality is assumed. -/
theorem ordinaryRoot_nativeTest_periodicH1 (σ : AbsoluteDensity 1)
    (u : Torus 1 → ℝ) (hu : Continuous u) (hupos : ∀ x, 0 < u x)
    (hurep : σ.sqrt =ᵐ[haar 1] u) (f : WeakH1Test (densityMeasure σ)) :
    IsPeriodicWeakDerivative_STR02933
      (fun t : ℝ => f.fn (angEquiv.symm (t : AngCircle)))
      (fun t : ℝ => (2 * Real.pi)⁻¹ * f.grad (angEquiv.symm (t : AngCircle)) 0) := by
  have hHaar := ordinaryRoot_nativeTest_haarWeakGradient σ u hu hupos hurep f
  let F : AngCircle → ℝ := fun θ => f.fn (angEquiv.symm θ)
  let G : AngCircle → ℝ := fun θ => (2 * Real.pi)⁻¹ * f.grad (angEquiv.symm θ) 0
  have hFG : IsWeakGradient (F ∘ angEquiv) (physGrad G) := by
    refine hHaar.congr_ae (Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · simp only [Function.comp_apply, F, angEquiv.symm_apply_apply]
    · ext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      rw [physGrad_apply]
      dsimp only [G]
      rw [angEquiv.symm_apply_apply]
      field_simp [Real.two_pi_pos.ne']
  have hAng : IsAngularWeakDeriv F G := (isWeakGradient_comp_iff F G).mpr hFG
  exact angularWD_to_periodicWD_STR02926 hAng

end DGPS.Examples.ThreeSpeciesCircle
