import LeanResearch.PeriodicAttractiveLogGas.ConditionalSourceDerivatives

/-! Actual conditional variance and one-edge estimates of Propositions
3.11 and 3.12. The law throughout is the named two-cell Gibbs restriction;
conditional energies are integrated using its actual stationary kernel.

Only regularity of the original observable is an input: its global
physical Lipschitz bound and its local smooth factor on the edge chart.
Regularity, ordinary gradients, and integrability of the conditional mean
and crossing probability are conclusions of the preceding source calculus.

SOURCE_ONLY candidate. The author has not executed Lean or a checker.
Central elaboration, axiom inspection, review, and protected replay are
separate statuses. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace PeriodicAttractiveLogGas.ConditionalVarianceAssembly

open MovingPoleNumerators hiding patchDomain
open MovingPoleCharts MovingPoleCalculus GreenPointWeights
open MeshCells MeshAdjacentCells LabelOccupations OneCoordinateConditionals CellRestrictions
open ConditionalLawEstimates ConditionalSourceCharts ConditionalSourceLipschitz
open ConditionalSourceDerivatives CollectiveGradientBounds CollectiveCovarianceBounds
open BoundaryCovarianceSplitting DeletedConditionalPoincare
open CoordinateOscillation (siteAverage)

variable {n J : ℕ}

/-- The exact source constant C_A. -/
def finePoincareConstant (β₀ : ℝ) : ℝ := 2 * poincareBound β₀

theorem finePoincareConstant_nonneg (β₀ : ℝ) : 0 ≤ finePoincareConstant β₀ := by
  have hc := (lowerBound_pos β₀).le
  have hK := (densityNormBound_pos β₀).le
  unfold finePoincareConstant poincareBound OneSiteConstants.poincare DensityEntropy.poincareConstant
  positivity

theorem crossingConstantSquared_nonneg (β₀ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (C₂ : ℝ) :
    0 ≤ crossingConstantSquared β₀ δ C₂ := by
  unfold crossingConstantSquared
  positivity

/-- No integrated coordinate is included in the retained energy. -/
def retainedEnergy (f : Configuration (n + 1) → ℝ) (i : Fin (n + 1))
    (X : Configuration (n + 1)) : ℝ :=
  ∑ j : Fin n, ‖coordinateOrdinaryGradient f (i.succAbove j) X‖ ^ 2

def meanEnergy (β₀ δ : ℝ) (f : Configuration (n + 1) → ℝ) (i : Fin (n + 1))
    (X : Configuration (n + 1)) : ℝ :=
  retainedEnergy f i X + averageConstant β₀ δ / (n + 1 : ℕ) *
    ‖coordinateOrdinaryGradient f i X‖ ^ 2

theorem meanEnergy_nonneg (β₀ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (f : Configuration (n + 1) → ℝ) (i : Fin (n + 1)) (X : Configuration (n + 1)) :
    0 ≤ meanEnergy β₀ δ f i X := by
  have hc := averageConstant_nonneg β₀ hδ
  exact add_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    (mul_nonneg (div_nonneg hc (Nat.cast_nonneg _)) (sq_nonneg _))

theorem measurable_retainedEnergy {f : Configuration (n + 1) → ℝ} (hf : Continuous f)
    (i : Fin (n + 1)) : Measurable (retainedEnergy f i) :=
  Finset.measurable_fun_sum _ fun j _ ↦
    (measurable_coordinateOrdinaryGradient hf (i.succAbove j)).norm.pow_const 2

theorem integrable_retainedEnergy {f : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hf : ConfigurationEuclideanLipschitzWith L f)
    (μ : Measure (Configuration (n + 1))) [IsFiniteMeasure μ] (i : Fin (n + 1)) :
    Integrable (retainedEnergy f i) μ := by
  exact integrable_finsetSum Finset.univ fun j _ ↦
    integrable_coordinate_energy hf μ (i.succAbove j)

theorem integrable_meanEnergy {f : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hf : ConfigurationEuclideanLipschitzWith L f) (β₀ δ : ℝ)
    (μ : Measure (Configuration (n + 1))) [IsFiniteMeasure μ] (i : Fin (n + 1)) :
    Integrable (meanEnergy β₀ δ f i) μ :=
  (integrable_retainedEnergy hf μ i).add
    ((integrable_coordinate_energy hf μ i).const_mul _)

theorem closedProduct_prescribedOutside (hJ : 0 < J) (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    {X : Configuration (n + 1)}
    (hX : X ∈ closedPatchProduct hJ (Function.update η i a) (adjacentShapes i r)) :
    PrescribedOutside hJ η i (removeSite i X) := by
  intro j
  have hj := hX (i.succAbove j) (mem_univ _)
  simpa only [OneCoordinateConditionals.adjacentShapes, ite_eq_right (Fin.succAbove_ne i j),
    Function.update_of_ne (Fin.succAbove_ne i j), removeSite,
    patchDomain, LocalPointEstimates.shape, TorusPatchDensity.domain] using hj

theorem twoCell_ae_closedProduct (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ n + 1)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    ∀ᵐ X ∂twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β,
      X ∈ closedPatchProduct hJ (Function.update η i a) (adjacentShapes i r) := by
  have h := DeletedPairConditionals.jointLaw_ae_mem_patches hJ hJ2
    (Function.update η i a) (adjacentShapes i r) none β
  rw [jointLaw_adjacent_eq_twoCell hJ hJ2 hN η i a r hβ hsub] at h
  filter_upwards [h] with X hX
  exact fun k _ ↦ subset_closure (hX k)

/-- The actual event probability, rather than an independent chosen
version of the normalizer ratio, is physically Lipschitz on the closed
joint product. Endpoint caps construct the ratio and identify it there. -/
theorem twoCell_crossing_lipschitz {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r) :
    ∃ L : ℝ≥0, ConfigurationPhysicalLipschitzOn L
      (crossingProbability (mesh_pos hmesh) i a r β)
      (closedPatchProduct (mesh_pos hmesh) (Function.update η i a) (adjacentShapes i r)) := by
  let hJ := mesh_pos hmesh
  let ζ := Function.update η i a
  have hcap : OccupationCap (ConditionalParameters.fixedDelta β₀ kernelConstant kernelConstant) ζ :=
    hadm.1.mono hδ
  have hplace : ∀ X ∈ closedChart J (fun k : otherParticles i ↦ ζ k)
      (fun k ↦ adjacentShapes i r k), ∀ k ∈ otherParticles i,
      extendedSources (otherParticles i) X k ∈ closure (meshCell J hJ (ζ k)) := by
    intro X hX k hk
    have hX' : X ∈ cellChart (otherParticles i) η := by
      simpa only [ζ, twoCell_sourceChart] using hX
    have hki := (mem_otherParticles i k).mp hk
    simpa only [ζ, Function.update_of_ne hki] using cellChart_placement hJ (otherParticles i) η hX' k hk
  obtain ⟨L, _, hL⟩ := capped_normalizerRatio_lipschitz
    MovingPoleIntegrability.fixedKernelBounds hJ hβ hβ₀ kernelConstant_pos.le kernelConstant_pos.le
    kernel_log_bound kernel_gradient_bound hmesh i ζ (adjacentShapes i r)
    (fun _ ↦ ζ) (fun _ _ ↦ hcap) hplace a r
  refine ⟨L, ?_⟩
  intro X hX Y hY
  have hx := CrossingLogistic.adjacent_ratio_eq_probability hβ hβ₀ hδ hmesh η i a r hadm
    (removeSite i X) (closedProduct_prescribedOutside hJ η i a r hX)
  have hy := CrossingLogistic.adjacent_ratio_eq_probability hβ hβ₀ hδ hmesh η i a r hadm
    (removeSite i Y) (closedProduct_prescribedOutside hJ η i a r hY)
  change |((conditionalKernel _ i β (removeSite i X)) (meshCell J hJ a)).toReal -
    ((conditionalKernel _ i β (removeSite i Y)) (meshCell J hJ a)).toReal| ≤ _
  rw [← hx, ← hy]
  exact hL X hX Y hY

/-- The integrated patch is the actual two-cell union. Smoothness is
demanded only of the original observable's local factor. -/
theorem twoCell_average_lipschitz {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r)
    (f : Configuration (n + 1) → ℝ)
    (hf : SmoothOnChart (cellChart (otherParticles i) η) (patchClosed (.edge r))
      (torusFactor (configurationFactor i f) J a)) :
    ∃ L : ℝ≥0, ConfigurationPhysicalLipschitzOn L
      (conditionalAverage (mesh_pos hmesh) i a r β f)
      (closedPatchProduct (mesh_pos hmesh) (Function.update η i a) (adjacentShapes i r)) := by
  let hJ := mesh_pos hmesh
  let ζ := Function.update η i a
  have hcap : OccupationCap (ConditionalParameters.fixedDelta β₀ kernelConstant kernelConstant) ζ :=
    hadm.1.mono hδ
  have hplace : ∀ X ∈ closedChart J (fun k : otherParticles i ↦ ζ k)
      (fun k ↦ adjacentShapes i r k), ∀ k ∈ otherParticles i,
      extendedSources (otherParticles i) X k ∈ closure (meshCell J hJ (ζ k)) := by
    intro X hX k hk
    have hX' : X ∈ cellChart (otherParticles i) η := by
      simpa only [ζ, twoCell_sourceChart] using hX
    have hki := (mem_otherParticles i k).mp hk
    simpa only [ζ, Function.update_of_ne hki] using cellChart_placement hJ (otherParticles i) η hX' k hk
  have hf' : SmoothOnChart (closedChart J (fun k : otherParticles i ↦ ζ k)
      (fun k ↦ adjacentShapes i r k)) (patchClosed (.edge r))
      (torusFactor (configurationFactor i f) J a) := by
    simpa only [ζ, twoCell_sourceChart] using hf
  obtain ⟨_, L, _, hL⟩ := capped_actual_joint_lipschitz
    MovingPoleIntegrability.fixedKernelBounds hJ hβ hβ₀ kernelConstant_pos.le kernelConstant_pos.le
    kernel_log_bound kernel_gradient_bound hmesh i ζ (adjacentShapes i r)
    (fun _ ↦ ζ) (fun _ _ ↦ hcap) hplace a (.edge r) f hf'
  exact ⟨L, hL⟩

/-- All ordinary-gradient integrability is constructed from the physical
Lipschitz bound and the actual Gibbs density, without off-product gates. -/
theorem twoCell_local_finite (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ n + 1)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    {g : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hg : ConfigurationPhysicalLipschitzOn L g
      (closedPatchProduct hJ (Function.update η i a) (adjacentShapes i r))) :
    let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β
    IsProbabilityMeasure P ∧ (∀ p : ℝ≥0∞, MemLp g p P) ∧
      (∀ k : Fin (n + 1), ∀ p : ℝ≥0∞, MemLp (coordinateOrdinaryGradient g k) p P) ∧
      Integrable (fun X ↦ ∑ k, ‖coordinateOrdinaryGradient g k X‖ ^ 2) P := by
  simpa only [jointLaw_adjacent_eq_twoCell hJ hJ2 hN η i a r hβ hsub] using
    joint_local_finite hN hJ hJ2 (Function.update η i a) (adjacentShapes i r) none hβ hsub hg

/-- Source Proposition 3.11 for the actual crossing probability under the
named joint law. Its mean and Bernoulli moment come from stationarity. -/
theorem twoCell_crossing_variance {β β₀ δ : ℝ}
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r) :
    let hJ := mesh_pos hmesh
    let b := nextCell J hJ a r
    let P := twoCellGibbsMeasure hJ η i a b β
    let p := (twoCellMixingWeight hJ η i a b β).toReal
    variance (crossingProbability hJ i a r β) P ≤
      finePoincareConstant β₀ * crossingConstantSquared β₀ δ GreenCovarianceBounds.hessianConstant /
        (4 * (n + 1 : ℕ)) * (p * (1 - p)) := by
  let hJ := mesh_pos hmesh
  let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β
  let p := (twoCellMixingWeight hJ η i a (nextCell J hJ a r) β).toReal
  let q := crossingProbability hJ i a r β
  let C := crossingConstantSquared β₀ δ GreenCovarianceBounds.hessianConstant
  obtain ⟨L, hL⟩ := twoCell_crossing_lipschitz hβ hβ₀ hδ hmesh η i a r hadm
  have hfinite := twoCell_local_finite hJ (mesh_two_le hmesh) hN η i a r hβ (hβ₀.trans_lt hsub) hL
  let : IsProbabilityMeasure P := hfinite.1
  have hpi := twoCellGibbs_poincare hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm hL
  have hgrad := (twoCell_log_crossing_gradient_bounds hN hβ hβ₀ hsub hδ₀.le hδ hmesh η i a r hadm).mono
    (fun _ h ↦ h.2)
  have hbern := adjacent_integrability_and_crossing hJ (mesh_two_le hmesh) hN η i a r
    hβ (hβ₀.trans_lt hsub) (f := fun _ ↦ (0 : ℝ)) measurable_const (B := 0) (fun _ ↦ by simp)
  have hi := integral_mono_ae hfinite.2.2.2
    (hbern.2.2.2.2.1.const_mul (C * (J : ℝ) ^ 2 / (4 * (n + 1 : ℕ)))) hgrad
  rw [integral_const_mul] at hi
  have hCA := finePoincareConstant_nonneg β₀
  have hC := crossingConstantSquared_nonneg β₀ hδ₀.le GreenCovarianceBounds.hessianConstant
  have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hN0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  change variance q P ≤ finePoincareConstant β₀ * C / (4 * (n + 1 : ℕ)) * (p * (1 - p))
  calc
    variance q P ≤ (finePoincareConstant β₀ / (J : ℝ) ^ 2) *
        (∫ X, ∑ k, ‖coordinateOrdinaryGradient q k X‖ ^ 2 ∂P) := hpi
    _ ≤ (finePoincareConstant β₀ / (J : ℝ) ^ 2) *
        (C * (J : ℝ) ^ 2 / (4 * (n + 1 : ℕ)) * ∫ X, q X * (1 - q X) ∂P) :=
      mul_le_mul_of_nonneg_left hi (div_nonneg hCA (sq_nonneg _))
    _ = (finePoincareConstant β₀ * C / (4 * (n + 1 : ℕ))) *
        (∫ X, q X * (1 - q X) ∂P) := by field_simp [hJ0, hN0]
    _ ≤ _ := mul_le_mul_of_nonneg_left hbern.2.2.2.2.2
      (div_nonneg (mul_nonneg hCA hC) (by positivity))

/-- Source Proposition 3.11 for the actual union conditional average.
The literal derivative bound is integrated with the stationary edge
kernel; the outside marginal is never replaced by a smaller Gibbs law. -/
theorem twoCell_average_variance {β β₀ δ : ℝ}
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r)
    (f : Configuration (n + 1) → ℝ) {L : ℝ≥0}
    (hfLip : ConfigurationEuclideanLipschitzWith L f)
    (hf : SmoothOnChart (cellChart (otherParticles i) η) (patchClosed (.edge r))
      (torusFactor (configurationFactor i f) J a)) :
    let hJ := mesh_pos hmesh
    let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β
    variance (conditionalAverage hJ i a r β f) P ≤
      (2 * finePoincareConstant β₀ / (J : ℝ) ^ 2) * ∫ X, meanEnergy β₀ δ f i X ∂P := by
  let hJ := mesh_pos hmesh
  let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β
  let κ := adjacentKernels hJ η i a r β
  let A := conditionalAverage hJ i a r β f
  let eo := retainedEnergy f i
  let ei := fun X ↦ ‖coordinateOrdinaryGradient f i X‖ ^ 2
  let C := averageConstant β₀ δ
  obtain ⟨LA, hLA⟩ := twoCell_average_lipschitz hβ hβ₀ hδ hmesh η i a r hadm f hf
  have hfinite := twoCell_local_finite hJ (mesh_two_le hmesh) hN η i a r
    hβ (hβ₀.trans_lt hsub) hLA
  let : IsProbabilityMeasure P := hfinite.1
  have hstat := preservesLaw_adjacentKernels hJ (mesh_two_le hmesh) hN η i a r hβ (hβ₀.trans_lt hsub)
  have heom : Measurable eo := measurable_retainedEnergy hfLip.continuous i
  have heim : Measurable ei := (measurable_coordinateOrdinaryGradient hfLip.continuous i).norm.pow_const 2
  have heoi : Integrable eo P := integrable_retainedEnergy hfLip P i
  have heii : Integrable ei P := integrable_coordinate_energy hfLip P i
  have hso := ConditionalVarianceIntegral.integrable_siteAverage κ P hstat heom heoi i
  have hsi := ConditionalVarianceIntegral.integrable_siteAverage κ P hstat heim heii i
  have hd : ∀ᵐ X ∂P,
      (∑ k, ‖coordinateOrdinaryGradient A k X‖ ^ 2) ≤
        2 * siteAverage κ eo i X + 2 * C / (n + 1 : ℕ) * siteAverage κ ei i X := by
    simpa only [κ, eo, ei, A, C, siteAverage, adjacentKernels_self, retainedEnergy] using
      twoCell_average_gradient_bound hN hβ hβ₀ hsub hδ₀.le hδ hmesh η i a r hadm f hfLip hf
  have hi := integral_mono_ae hfinite.2.2.2
    ((hso.const_mul 2).add (hsi.const_mul (2 * C / (n + 1 : ℕ)))) hd
  change (∫ X, ∑ k, ‖coordinateOrdinaryGradient A k X‖ ^ 2 ∂P) ≤
    ∫ X, 2 * siteAverage κ eo i X + 2 * C / (n + 1 : ℕ) * siteAverage κ ei i X ∂P at hi
  rw [integral_add (hso.const_mul 2) (hsi.const_mul _), integral_const_mul, integral_const_mul,
    ConditionalVarianceIntegral.integral_siteAverage κ P hstat heom heoi i,
    ConditionalVarianceIntegral.integral_siteAverage κ P hstat heim heii i] at hi
  have he : (∫ X, ∑ k, ‖coordinateOrdinaryGradient A k X‖ ^ 2 ∂P) ≤
      2 * ∫ X, meanEnergy β₀ δ f i X ∂P := by
    calc
      _ ≤ 2 * (∫ X, eo X ∂P) + 2 * C / (n + 1 : ℕ) * (∫ X, ei X ∂P) := hi
      _ = _ := by
        change _ = 2 * ∫ X, eo X + (C / (n + 1 : ℕ)) * ei X ∂P
        rw [integral_add heoi (heii.const_mul _), integral_const_mul]
        ring
  have hpi := twoCellGibbs_poincare hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm hLA
  calc
    variance A P ≤ (finePoincareConstant β₀ / (J : ℝ) ^ 2) *
        (∫ X, ∑ k, ‖coordinateOrdinaryGradient A k X‖ ^ 2 ∂P) := hpi
    _ ≤ (finePoincareConstant β₀ / (J : ℝ) ^ 2) *
        (2 * ∫ X, meanEnergy β₀ δ f i X ∂P) :=
      mul_le_mul_of_nonneg_left he (div_nonneg (finePoincareConstant_nonneg β₀) (sq_nonneg _))
    _ = _ := by ring

/-- The actual conditional variance obeys the one-coordinate Poincare
bound and stationarity identifies its integrated energy exactly. -/
theorem twoCell_conditionalVariance_energy {β β₀ δ : ℝ}
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r)
    {f : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hfLip : ConfigurationEuclideanLipschitzWith L f) :
    let hJ := mesh_pos hmesh
    let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β
    (∫ X, conditionalVariance hJ i a r β f X ∂P) ≤
      (poincareBound β₀ / (J : ℝ) ^ 2) *
        ∫ X, ‖coordinateOrdinaryGradient f i X‖ ^ 2 ∂P := by
  let hJ := mesh_pos hmesh
  let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β
  let κ := adjacentKernels hJ η i a r β
  let ei := fun X ↦ ‖coordinateOrdinaryGradient f i X‖ ^ 2
  have hfLocal : ConfigurationPhysicalLipschitzOn L f
      (closedPatchProduct hJ (Function.update η i a) (adjacentShapes i r)) := by
    intro X _ Y _
    simpa only [Real.dist_eq] using hfLip X Y
  have hfinite := twoCell_local_finite hJ (mesh_two_le hmesh) hN η i a r
    hβ (hβ₀.trans_lt hsub) hfLocal
  let : IsProbabilityMeasure P := hfinite.1
  have hstat := preservesLaw_adjacentKernels hJ (mesh_two_le hmesh) hN η i a r hβ (hβ₀.trans_lt hsub)
  have hind := independentSite_adjacentKernels hJ η i a r β
  have hvi := ConditionalVarianceIntegral.integrable_kernelVariance κ P hind hstat (hfinite.2.1 2) i
  change Integrable (ConditionalVarianceIntegral.kernelVariance (adjacentKernels hJ η i a r β) f i) P at hvi
  rw [kernelVariance_eq_conditionalVariance] at hvi
  have heim : Measurable ei := (measurable_coordinateOrdinaryGradient hfLip.continuous i).norm.pow_const 2
  have heii : Integrable ei P := integrable_coordinate_energy hfLip P i
  have hsi := ConditionalVarianceIntegral.integrable_siteAverage κ P hstat heim heii i
  have hv : ∀ᵐ X ∂P, conditionalVariance hJ i a r β f X ≤
      (poincareBound β₀ / (J : ℝ) ^ 2) * siteAverage κ ei i X := by
    filter_upwards [twoCell_ae_closedProduct hJ (mesh_two_le hmesh) hN η i a r hβ (hβ₀.trans_lt hsub)] with X hX
    have hY := closedProduct_prescribedOutside hJ η i a r hX
    have hY' : PrescribedOutside hJ (Function.update η i a) i (removeSite i X) := by
      intro j
      simpa only [Function.update_of_ne (Fin.succAbove_ne i j)] using hY j
    have hb := capped_patch_law hJ hβ hβ₀ hδ hmesh (Function.update η i a) hadm.1
      i (removeSite i X) hY' a (.edge r)
    have hsec : PhysicalLipschitzOn L (fun z ↦ f (Function.update X i z))
        (closure (patchDomain J hJ a (.edge r))) := by
      intro z _ w _
      exact hfLip.section X i z (mem_univ _) w (mem_univ _)
    have hs := (hb.estimates hsec).uniform_variance
    simpa only [conditionalVariance, CoordinateConditionalKernels.insertSite_eq_update,
      κ, ei, siteAverage, adjacentKernels_self, coordinateOrdinaryGradient_update, patchMeasure] using hs
  calc
    (∫ X, conditionalVariance hJ i a r β f X ∂P) ≤
        ∫ X, (poincareBound β₀ / (J : ℝ) ^ 2) * siteAverage κ ei i X ∂P :=
      integral_mono_ae hvi (hsi.const_mul _) hv
    _ = _ := by
      rw [integral_const_mul, ConditionalVarianceIntegral.integral_siteAverage κ P hstat heim heii i]

/-- Quantitative single-edge estimate from the supplied proof of
Proposition 3.12. Both variance bounds and the one-site conditional bound
are established above; no desired variance or edge estimate is a premise.
The observable need not be symmetric, and no positive-coupling division
is used. Both caps and both periodic edge orientations are retained. -/
theorem twoCell_single_edge_estimate {β β₀ δ : ℝ}
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r)
    (f : Configuration (n + 1) → ℝ) {L : ℝ≥0}
    (hfLip : ConfigurationEuclideanLipschitzWith L f)
    (hf : SmoothOnChart (cellChart (otherParticles i) η) (patchClosed (.edge r))
      (torusFactor (configurationFactor i f) J a)) :
    let hJ := mesh_pos hmesh
    let b := nextCell J hJ a r
    let P := twoCellGibbsMeasure hJ η i a b β
    let p := (twoCellMixingWeight hJ η i a b β).toReal
    let Φa := ∫ X, f X ∂labelGibbsMeasure hJ (Function.update η i a) β
    let Φb := ∫ X, f X ∂labelGibbsMeasure hJ (Function.update η i b) β
    p * (1 - p) * (Φa - Φb) ^ 2 ≤
      (finePoincareConstant β₀ / (J : ℝ) ^ 2) *
        (∫ X, ‖coordinateOrdinaryGradient f i X‖ ^ 2 ∂P) +
      (finePoincareConstant β₀ ^ 2 *
        crossingConstantSquared β₀ δ GreenCovarianceBounds.hessianConstant /
          ((n + 1 : ℕ) * (J : ℝ) ^ 2)) * ∫ X, meanEnergy β₀ δ f i X ∂P := by
  let hJ := mesh_pos hmesh
  let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β
  let p := (twoCellMixingWeight hJ η i a (nextCell J hJ a r) β).toReal
  let A := conditionalAverage hJ i a r β f
  let q := crossingProbability hJ i a r β
  let CA := finePoincareConstant β₀
  let CΛ := crossingConstantSquared β₀ δ GreenCovarianceBounds.hessianConstant
  let E := ∫ X, meanEnergy β₀ δ f i X ∂P
  have hA : variance A P ≤ (2 * CA / (J : ℝ) ^ 2) * E :=
    twoCell_average_variance hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm f hfLip hf
  have hq : variance q P ≤ CA * CΛ / (4 * (n + 1 : ℕ)) * (p * (1 - p)) :=
    twoCell_crossing_variance hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm
  have hv := twoCell_conditionalVariance_energy hN hβ hβ₀ hsub hδ hmesh η i a r hadm hfLip
  obtain ⟨hp₀, hp₁, hsplit⟩ :=
    adjacent_boundary_splitting hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm hfLip.continuous
  have hp : 0 < p * (1 - p) := mul_pos hp₀ (sub_pos.mpr hp₁)
  have hCA : 0 ≤ CA := finePoincareConstant_nonneg β₀
  have hCΛ : 0 ≤ CΛ := crossingConstantSquared_nonneg β₀ hδ₀.le GreenCovarianceBounds.hessianConstant
  have hE : 0 ≤ E := integral_nonneg (meanEnergy_nonneg β₀ hδ₀.le f i)
  have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hN0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hprod : variance A P * variance q P ≤
      ((2 * CA / (J : ℝ) ^ 2) * E) * (CA * CΛ / (4 * (n + 1 : ℕ)) * (p * (1 - p))) :=
    mul_le_mul hA hq (variance_nonneg _ _)
      (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hCA) (sq_nonneg _)) hE)
  have hcov : 2 * variance A P * variance q P / (p * (1 - p)) ≤
      CA ^ 2 * CΛ / ((n + 1 : ℕ) * (J : ℝ) ^ 2) * E := by
    calc
      _ ≤ (2 * (((2 * CA / (J : ℝ) ^ 2) * E) *
          (CA * CΛ / (4 * (n + 1 : ℕ)) * (p * (1 - p))))) / (p * (1 - p)) := by
        rw [mul_assoc]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by norm_num)) hp.le
      _ = _ := by
        apply (div_eq_iff hp.ne').mpr
        field_simp [hJ0, hN0]; ring
  calc
    _ ≤ 2 * (∫ X, conditionalVariance hJ i a r β f X ∂P) +
        2 * variance A P * variance q P / (p * (1 - p)) := hsplit
    _ ≤ 2 * ((poincareBound β₀ / (J : ℝ) ^ 2) *
        ∫ X, ‖coordinateOrdinaryGradient f i X‖ ^ 2 ∂P) +
        CA ^ 2 * CΛ / ((n + 1 : ℕ) * (J : ℝ) ^ 2) * E :=
      add_le_add (mul_le_mul_of_nonneg_left hv (by norm_num)) hcov
    _ = _ := by dsimp only [CA, CΛ, E, finePoincareConstant]; ring

end PeriodicAttractiveLogGas.ConditionalVarianceAssembly
