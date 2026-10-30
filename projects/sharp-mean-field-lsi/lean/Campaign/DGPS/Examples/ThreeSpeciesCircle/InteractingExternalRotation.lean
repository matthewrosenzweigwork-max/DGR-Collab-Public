import DGPS.Examples.ThreeSpeciesCircle.InteractingFeedbackRotation

/-! The actual common-field third-turn action on the retained Holder space.
The action is norm preserving and agrees with physical native pullback. No
invariance of any chosen IFT neighborhood or active-family classification occurs. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem circDist_sub (s t δ : ℝ) :
    circDist_STR02968 (s - δ) (t - δ) = circDist_STR02968 s t := by
  unfold circDist_STR02968
  rw [AddCircle.coe_sub, AddCircle.coe_sub, dist_sub_right]

/-- Translation in the existing angular Holder carrier, with the physical
pullback sign matching the positive probability-law turn. -/
def interactingHolderTranslate (δ : ℝ) (V : PeriodicHolder_STR02968) : PeriodicHolder_STR02968 :=
  PeriodicHolder_STR02968.mk (fun t => V.val (t - δ)) (by
    obtain ⟨C, hC, hVC⟩ := V.isPerHolder.2.2
    refine ⟨?_, V.isPerHolder.2.1.comp (continuous_id.sub continuous_const), C, hC, fun s t => ?_⟩
    · intro t
      dsimp only
      rw [show t + 2 * Real.pi - δ = (t - δ) + 2 * Real.pi by ring, V.isPerHolder.1]
    · simpa only [circDist_sub] using hVC (s - δ) (t - δ))

private theorem holderTranslate_norm_le (δ : ℝ) (V : PeriodicHolder_STR02968) :
    ‖interactingHolderTranslate δ V‖ ≤ ‖V‖ := by
  have hs : supNorm_STR02968 (interactingHolderTranslate δ V).val ≤ supNorm_STR02968 V.val :=
    supNorm_le_STR02968 fun t => V.isPerHolder.abs_le_supNorm (t - δ)
  have hh : holderSemi_STR02968 (1 / 2) (interactingHolderTranslate δ V).val ≤
      holderSemi_STR02968 (1 / 2) V.val := by
    apply holderSemi_le_STR02968 (by norm_num) (holderSemi_nonneg_STR02968 _ _)
    intro s t
    change |V.val (s - δ) - V.val (t - δ)| ≤ _
    simpa only [circDist_sub] using
      abs_sub_le_holderSemi_mul_STR02968 (by norm_num : (0 : ℝ) < 1 / 2)
        V.isPerHolder.1 V.isPerHolder.2.2 (s - δ) (t - δ)
  rw [PeriodicHolder_STR02968.norm_def, PeriodicHolder_STR02968.norm_def]
  exact add_le_add hs hh

/-- No Holder-norm loss under the genuine field transform. -/
theorem interactingHolderTranslate_norm (δ : ℝ) (V : PeriodicHolder_STR02968) :
    ‖interactingHolderTranslate δ V‖ = ‖V‖ := by
  apply le_antisymm (holderTranslate_norm_le δ V)
  have he : interactingHolderTranslate (-δ) (interactingHolderTranslate δ V) = V := by
    apply ext_STR02954
    funext t
    change V.val (t - -δ - δ) = V.val t
    congr 1
    ring
  have hi := holderTranslate_norm_le (-δ) (interactingHolderTranslate δ V)
  rw [he] at hi
  exact hi

private theorem angEquiv_sub_pt (x : Torus 1) (s : ℝ) :
    angEquiv (x - pt s) = angEquiv x - ((2 * Real.pi * s : ℝ) : AngCircle) := by
  change angRescale (x 0 - (pt s) 0) =
    angRescale (x 0) - ((2 * Real.pi * s : ℝ) : AngCircle)
  rw [map_sub]
  change angRescale (x 0) - angRescale ((s : ℝ) : UnitAddCircle) = _
  rw [angRescale_mk]

/-- Typed angular field translation is exactly physical native pullback. -/
theorem interactingHolderTranslate_native (s : ℝ) (V : PeriodicHolder_STR02968) (x : Torus 1) :
    (interactingHolderTranslate (2 * Real.pi * s) V).val (angSec (angEquiv x)) =
      V.val (angSec (angEquiv (x - pt s))) := by
  change V.val (angSec (angEquiv x) - 2 * Real.pi * s) = _
  apply eq_of_circDist_eq_zero_STR02968 V.isPerHolder.1
  unfold circDist_STR02968
  rw [AddCircle.coe_sub, coe_angSec_STR02962, coe_angSec_STR02962, angEquiv_sub_pt]
  exact dist_self _

/-- Actual external common-field/value covariance with the SAME real rate and
common scalar value, and with a norm-preserving transform in the true parameter
space. This precedes any common-feedback or stationarity identification. -/
theorem externalHolderNativeDeficit_interactingThirdTurn (h r c : ℝ) (j : Fin 3)
    (ρ : AbsoluteDensity 1) (V : PeriodicHolder_STR02968) :
    let a := pt ((j : ℕ) / 3)
    let τ := interactingDensityTranslate a ρ
    (ordinaryFisher h τ).toReal - 2 * r * (ordinaryEntropy h τ).toReal +
        (∫ x, (interactingHolderTranslate (2 * Real.pi * ((j : ℕ) / 3)) V).val
          (angSec (angEquiv x)) ∂(densityMeasure τ : Measure (Torus 1))) - c =
      (ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal +
        (∫ x, V.val (angSec (angEquiv x)) ∂(densityMeasure ρ : Measure (Torus 1))) - c := by
  dsimp only
  simp_rw [interactingHolderTranslate_native]
  exact externalNativeDeficit_interactingThirdTurn h r c j ρ (fun x => V.val (angSec (angEquiv x)))

end DGPS.Examples.ThreeSpeciesCircle
