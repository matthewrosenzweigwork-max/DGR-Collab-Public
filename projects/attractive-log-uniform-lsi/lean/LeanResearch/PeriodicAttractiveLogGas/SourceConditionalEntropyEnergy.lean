import LeanResearch.PeriodicAttractiveLogGas.SourceEntropyTests
import LeanResearch.PeriodicAttractiveLogGas.SmoothObservableInterfaces

/-! Source lines 2709–2717: the original one-site entropy sum and its
unscaled physical configuration energy. The zero entropy representative is
never differentiated. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

namespace PeriodicAttractiveLogGas.SourceConditionalEntropyEnergy

open MeshCells MeshAdjacentCells LabelOccupations GreenPointWeights
open MovingPoleNumerators MovingPoleCharts ConditionalSourceCharts
open OneCoordinateConditionals CellRestrictions ConditionalLawEstimates
open ReferenceSelfTerms ReferenceDensityChange ReferenceConditionalNormalization
open ConditionalEntropyDisintegration SourceEntropyTests

/-- The physical chart metric is exact on each prescribed cell rectangle;
no particle-dependent norm comparison enters the energy argument. -/
theorem closedChart_distance {J N : ℕ} (hJ3 : 3 ≤ J) (η : LabelVector J N)
    {Z W : SourceSpace (Fin N)}
    (hZ : Z ∈ closedChart J η (fun _ => Patch.cell))
    (hW : W ∈ closedChart J η (fun _ => Patch.cell)) :
    configurationEuclideanDist (sources Z) (sources W) = dist Z W := by
  have hj : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hj3 : (3 : ℝ) ≤ J := by exact_mod_cast hJ3
  rw [configurationEuclideanDist_eq_sqrt_sum_dist_sq, dist_eq_norm, EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro ik _
  have hz := (mem_closedChart_iff J η (fun _ => Patch.cell) Z).mp hZ ik
  have hw := (mem_closedChart_iff J η (fun _ => Patch.cell) W).mp hW ik
  have hwidth : upper J η (fun _ => Patch.cell) ik - lower J η ik ≤ (1 / 2 : ℝ) := by
    simp only [upper, lower, patchWidth, ← sub_div, add_sub_cancel_left]
    exact (div_le_iff₀ hj).mpr (by linarith)
  have hd : |Z ik - W ik| ≤ (1 / 2 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hn : ‖((Z ik - W ik : ℝ) : UnitAddCircle)‖ = |Z ik - W ik| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).mpr (by simpa using hd)
  rw [dist_eq_norm]
  change ‖((Z ik - W ik : ℝ) : UnitAddCircle)‖ ^ 2 = ‖Z ik - W ik‖ ^ 2
  rw [hn, Real.norm_eq_abs]

theorem physicalLipschitz_of_chart {J N : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (η : LabelVector J N) {f : Configuration N → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell))) :
    ConfigurationPhysicalLipschitzOn C f
      (Set.pi univ fun i => closure (meshCell J hJ (η i))) := by
  intro X hX Y hY
  obtain ⟨Z, hZ, rfl⟩ := (mem_closedRectangle hJ η X).mpr (fun i => hX i (mem_univ _))
  obtain ⟨W, hW, rfl⟩ := (mem_closedRectangle hJ η Y).mpr (fun i => hY i (mem_univ _))
  simpa only [Real.dist_eq, closedChart_distance hJ3 η hZ hW] using hf.dist_le_mul Z hZ W hW

theorem labelGibbs_cell_absolutelyContinuous {J N : ℕ} (hJ : 0 < J)
    (η : LabelVector J N) (β : ℝ) :
    labelGibbsMeasure hJ η β ≪ Measure.pi (fun i => meshCellMeasure J hJ (η i)) :=
  (withDensity_absolutelyContinuous _ _).smul_left _

theorem source_coordinate_energy_integrable {J N : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (hN : 2 ≤ N) (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    {f : Configuration N → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell)))
    (i : Fin N) :
    Integrable (fun X => ‖coordinateOrdinaryGradient f i X‖ ^ 2) (labelGibbsMeasure hJ η β) := by
  let : IsProbabilityMeasure (labelGibbsMeasure hJ η β) :=
    isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ hsub
  have hp := physicalLipschitz_of_chart hJ hJ3 η hf
  have hm := hp.patch_gradient_memLp hJ η (fun _ => TorusPatchDensity.Shape.cell)
    (labelGibbs_cell_absolutelyContinuous hJ η β) i 2
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm

theorem source_full_energy_integrable {J N : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (hN : 2 ≤ N) (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    {f : Configuration N → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell))) :
    Integrable (fun X => ∑ i, ‖coordinateOrdinaryGradient f i X‖ ^ 2)
      (labelGibbsMeasure hJ η β) :=
  integrable_finsetSum _ fun i _ => source_coordinate_energy_integrable hJ hJ3 hN η hβ hsub hf i

theorem section_ordinaryGradient {n : ℕ} (f : Configuration (n + 1) → ℝ)
    (i : Fin (n + 1)) (Y : Configuration n) (z : Torus) :
    torusOrdinaryGradient (fun w => f (insertSite i w Y)) z =
      coordinateOrdinaryGradient f i (insertSite i z Y) := by
  have he : (fun w => f (Function.update (insertSite i z Y) i w)) =
      fun w => f (insertSite i w Y) := by
    funext w
    rw [← CoordinateConditionalKernels.insertSite_eq_update, removeSite_insertSite]
  simp only [coordinateOrdinaryGradient, insertSite_self, he]

theorem section_physicalLipschitz {J n : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (η : LabelVector J (n + 1)) {f : Configuration (n + 1) → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell)))
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PrescribedOutside hJ η i Y) :
    PhysicalLipschitzOn C (fun z => f (insertSite i z Y)) (closure (meshCell J hJ (η i))) := by
  have hp := physicalLipschitz_of_chart hJ hJ3 η hf
  have hs := hp.section (insertSite i 0 Y) i (fun k hki => by
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hki
    simpa only [insertSite_succAbove] using hY j)
  have he : (fun z => f (Function.update (insertSite i 0 Y) i z)) =
      fun z => f (insertSite i z Y) := by
    funext z
    rw [← CoordinateConditionalKernels.insertSite_eq_update, removeSite_insertSite]
  rwa [he] at hs

/-- A genuine physical differential identifies every ordinary coordinate
block and its unscaled total energy, without a smoothness assumption. -/
theorem energy_eq_norm_of_hasFDerivAt {N : ℕ} {f : Configuration N → ℝ}
    {y G : Gradient N}
    (hd : HasFDerivAt (fun w => f (configurationQuotient N w)) (innerSL ℝ G) y) :
    BoundaryEdgeSummation.totalEnergyDensity f (configurationQuotient N y) = ‖G‖ ^ 2 := by
  have hc (i : Fin N) : coordinateOrdinaryGradient f i (configurationQuotient N y) =
      sourceProjection i G := by
    have hd' : HasFDerivAt (fun w => f (configurationQuotient N w))
        (InnerProductSpace.toDual ℝ (Gradient N) G) y := hd
    have hs := MovingPoleDerivativeIdentification.hasFDerivAt_sourceBlock hd' i
    simp only [configurationQuotient_sourceVariation] at hs
    change torusOrdinaryGradient
      (fun z => f (Function.update (configurationQuotient N y) i z))
      (torusQuotient (sourceProjection i y)) = _
    rw [torusOrdinaryGradient_lift, rectangleOrdinaryGradient, hs.fderiv]
    exact (InnerProductSpace.toDual ℝ PlanarSpace).symm_apply_apply _
  rw [gradient_norm_sq]
  apply Finset.sum_congr rfl
  intro i _
  change ‖coordinateOrdinaryGradient f i (configurationQuotient N y)‖ ^ 2 = _
  rw [hc, EuclideanSpace.real_norm_sq_eq]
  rfl

/-- A continuous Lipschitz extension supplies a measurable full Riesz field.
On the actual full-measure interior set it is the true derivative of the
original physical lift, at every representative, and its norm is exactly the
existing energy density. No derivative of the zero extension is used. -/
theorem source_full_gradient_identification {J N : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (η : LabelVector J N) (β : ℝ) {f : Configuration N → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell))) :
    ∃ g : C(Configuration N, ℝ), ConfigurationEuclideanLipschitzWith C g ∧
      EqOn f g (Set.pi univ fun i => closure (meshCell J hJ (η i))) ∧
      ∀ᵐ X ∂labelGibbsMeasure hJ η β,
        (∀ y : Gradient N, configurationQuotient N y = X →
          HasFDerivAt (fun w => f (configurationQuotient N w))
            (innerSL ℝ (descendedLiftGradient g X)) y) ∧
        BoundaryEdgeSummation.totalEnergyDensity f X = ‖descendedLiftGradient g X‖ ^ 2 := by
  have hp := physicalLipschitz_of_chart hJ hJ3 η hf
  obtain ⟨g, hg, hfg⟩ := hp.exists_extension
    (closed_product_patches_nonempty hJ η (fun _ => TorusPatchDensity.Shape.cell))
  have hac : labelGibbsMeasure hJ η β ≪ referenceMeasure N := by
    have hc : labelReference hJ η ≪ referenceMeasure N := by
      rw [labelReference_eq]
      exact Measure.absolutelyContinuous_restrict.smul_left _
    exact (labelGibbs_cell_absolutelyContinuous hJ η β).trans hc
  refine ⟨g, hg, hfg, ?_⟩
  filter_upwards [ae_hasFDerivAt_configurationLift_of_absolutelyContinuous g hg.lift hac,
    ae_closed_product_patch_nhds hJ η (fun _ => TorusPatchDensity.Shape.cell)
      (labelGibbs_cell_absolutelyContinuous hJ η β)] with X hd hX
  have hD : (Set.pi univ fun i => closure (meshCell J hJ (η i))) ∈ 𝓝 X :=
    set_pi_mem_nhds Set.finite_univ fun i _ => hX i
  have hactual (y : Gradient N) (hy : configurationQuotient N y = X) :
      HasFDerivAt (fun w => f (configurationQuotient N w))
        (innerSL ℝ (descendedLiftGradient g X)) y := by
    have ht : Tendsto (configurationQuotient N) (𝓝 y) (𝓝 X) := by
      rw [← hy]
      exact (isOpenQuotientMap_configurationQuotient N).continuous.continuousAt
    have hevent : ∀ᶠ w in 𝓝 y, configurationQuotient N w ∈
        (Set.pi univ fun i => closure (meshCell J hJ (η i))) := ht hD
    have he : (fun w => f (configurationQuotient N w)) =ᶠ[𝓝 y]
        fun w => g (configurationQuotient N w) :=
      hevent.mono fun w hw => hfg hw
    exact (hd y hy).congr_of_eventuallyEq he
  refine ⟨hactual, ?_⟩
  have hn := energy_eq_norm_of_hasFDerivAt
    (hactual (configurationCenteredLift X) (configurationQuotient_centeredLift X))
  simpa only [configurationQuotient_centeredLift] using hn

section ActualReference

variable {J n : ℕ} (hJ : 0 < J)
  (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
  (η : LabelVector J (n + 1)) {β β₀ t : ℝ}
  (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
  (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
    ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
  (hmesh : 8 * (radius β₀ + 4) ≤ J) (ht : t ≤ occupationBound β₀)
  (hη : OccupationCap t η)

include hβ hβ₀ hformula hmesh ht hη

/-- The reference conditional and the original prescribed-cell conditional
are the same probability law at every admissible fixed placement. -/
theorem reference_conditional_eq_cell (i : Fin (n + 1)) (Y : Configuration n)
    (hY : PrescribedOutside hJ η i Y) :
    PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i Y =
    OneCoordinateConditionals.conditionalKernel (meshCellMeasure J hJ (η i)) i β Y := by
  have hb := capped_patch_law hJ hβ hβ₀ ht hmesh η hη i Y hY (η i) Patch.cell
  have hcell : OneCoordinateConditionals.conditionalKernel (meshCellMeasure J hJ (η i)) i β Y =
      pointLaw (meshCellMeasure J hJ (η i)) Y (fun _ => β / (n + 1 : ℕ)) := hb.kernel_eq_pointLaw
  rw [conditionalKernel_eq_reference_density hJ μ η hβ hβ₀ hformula hmesh (hη.mono ht) i Y hY,
    hcell]
  let D := fun z => Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β (η i)
  let A := Real.exp ((β / (n + 1 : ℕ)) * ∑ j : Fin n,
    (ReferenceResidual.pairAverage (μ (η i)) (μ (η (i.succAbove j))) -
      ReferenceResidual.potential (μ (η i)) (Y j))) / cellNormalizer hJ μ η β (η i)
  have hz := cellNormalizer_pos_of_formula hJ μ η β (η i) (hformula (η i))
  have hA : 0 < A := div_pos (Real.exp_pos _) hz
  have hD0 : ∀ z, 0 ≤ D z := fun z => div_nonneg (Real.exp_pos _).le hz.le
  have hD : Measurable D := ((measurable_averagePotential μ η).const_mul β).exp.div_const _
  have he (z : Torus) : D z * sectionWeight μ η i β Y z =
      A * OneCoordinateConditionals.sourceWeight β Y z := density_mul_sectionWeight hJ μ η i β Y z
  have hZ : sectionNormalizer μ η i β Y =
      A * ∫ z, OneCoordinateConditionals.sourceWeight β Y z ∂meshCellMeasure J hJ (η i) := by
    unfold sectionNormalizer
    rw [DensityMoments.integral_density (hformula (η i)) hD (Eventually.of_forall hD0)]
    change (∫ z, D z * sectionWeight μ η i β Y z ∂meshCellMeasure J hJ (η i)) = _
    simp_rw [he]
    exact integral_const_mul _ _
  rw [hformula (η i), ← withDensity_mul _ hD.ennreal_ofReal
    ((measurable_sectionWeight μ η i β Y).div_const _).ennreal_ofReal]
  apply withDensity_congr_ae
  apply Eventually.of_forall
  intro z
  change ENNReal.ofReal (D z) * ENNReal.ofReal (sectionWeight μ η i β Y z /
    sectionNormalizer μ η i β Y) = ENNReal.ofReal
      (OneCoordinateConditionals.sourceWeight β Y z /
        ∫ u, OneCoordinateConditionals.sourceWeight β Y u ∂meshCellMeasure J hJ (η i))
  rw [← ENNReal.ofReal_mul (hD0 z), ← mul_div_assoc, he, hZ]
  congr 1
  exact mul_div_mul_left _ _ hA.ne'

theorem fixed_section_entropy_le (hJ3 : 3 ≤ J) {f : Configuration (n + 1) → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell)))
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PrescribedOutside hJ η i Y) :
    let κ := PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
    conditionalEntropyValue κ (fun p => f (insertSite i p.2 p.1) ^ 2) Y ≤
      (entropyBound β₀ / (J : ℝ) ^ 2) *
        ∫ z, ‖coordinateOrdinaryGradient f i (insertSite i z Y)‖ ^ 2 ∂κ Y := by
  let κ := PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
    (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
  have hb := capped_patch_law hJ hβ hβ₀ ht hmesh η hη i Y hY (η i) Patch.cell
  have he := hb.estimates (section_physicalLipschitz hJ hJ3 η hf i Y hY)
  have hk : κ Y = OneCoordinateConditionals.conditionalKernel (meshCellMeasure J hJ (η i)) i β Y :=
    reference_conditional_eq_cell hJ μ η hβ hβ₀ hformula hmesh ht hη i Y hY
  change FunctionEstimates β₀ J Patch.cell
    (OneCoordinateConditionals.conditionalKernel (meshCellMeasure J hJ (η i)) i β Y)
    (fun z => f (insertSite i z Y)) at he
  rw [← hk] at he
  let : IsProbabilityMeasure (κ Y) := by rw [hk]; exact hb.probability
  have heq : (conditionalEntropyValue κ (fun p => f (insertSite i p.2 p.1) ^ 2) Y : EReal) =
      entropy (κ Y) (fun z => f (insertSite i z Y) ^ 2) := by
    exact (entropy_eq_integral (Eventually.of_forall fun z => sq_nonneg (f (insertSite i z Y)))
      he.integrable_log_square).symm
  have hle := he.uniform_entropy
  rw [← heq] at hle
  simp_rw [section_ordinaryGradient] at hle
  exact_mod_cast hle

omit hβ₀ hmesh ht hη in
theorem source_coordinate_energy_disintegration (hN : 2 ≤ n + 1) (hsub : β < 4)
    (hJ3 : 3 ≤ J) {f : Configuration (n + 1) → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell)))
    (i : Fin (n + 1)) :
    let κ := PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
    Integrable (fun Y => ∫ z, ‖coordinateOrdinaryGradient f i (insertSite i z Y)‖ ^ 2 ∂κ Y)
      (Measure.map (removeSite i) (labelGibbsMeasure hJ η β)) ∧
    (∫ Y, ∫ z, ‖coordinateOrdinaryGradient f i (insertSite i z Y)‖ ^ 2 ∂κ Y
      ∂Measure.map (removeSite i) (labelGibbsMeasure hJ η β)) =
      ∫ X, ‖coordinateOrdinaryGradient f i X‖ ^ 2 ∂labelGibbsMeasure hJ η β := by
  let P := labelGibbsMeasure hJ η β
  let ρ := Measure.map (removeSite i) P
  let κ := PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
    (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
  let : IsProbabilityMeasure P := isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ hsub
  let : IsMarkovKernel κ := PositiveProductConditionals.isMarkovKernel_conditionalKernel
    (μ (η i)) (referenceTilt μ η β) (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
  let e := configurationSplit i
  let H := fun p => ‖coordinateOrdinaryGradient f i (e.symm p)‖ ^ 2
  have hsplit : Measure.map e P = ρ ⊗ₘ κ := by
    apply split_law_of_lintegral
    intro G hG
    exact reference_lintegral_disintegrate hJ hN μ η hβ hsub hformula i hG
  have hmp : MeasurePreserving e P (ρ ⊗ₘ κ) := ⟨e.measurable, hsplit⟩
  have hi : Integrable H (ρ ⊗ₘ κ) := (hmp.integrable_comp_emb e.measurableEmbedding).mp (by
    simpa only [H, Function.comp_def, MeasurableEquiv.symm_apply_apply] using
      source_coordinate_energy_integrable hJ hJ3 hN η hβ hsub hf i)
  have hn := (Measure.integrable_compProd_iff hi.aestronglyMeasurable).mp hi |>.2
  have hnorm (Y : Configuration n) (z : Torus) : ‖H (Y, z)‖ = H (Y, z) :=
    Real.norm_of_nonneg (sq_nonneg _)
  simp_rw [hnorm] at hn
  refine ⟨hn, ?_⟩
  calc
    _ = ∫ p, H p ∂ρ ⊗ₘ κ := (Measure.integral_compProd hi).symm
    _ = ∫ X, H (e X) ∂P := (hmp.integral_comp' H).symm
    _ = _ := by simp only [H, MeasurableEquiv.symm_apply_apply]; rfl

omit hβ₀ hmesh ht hη in
theorem source_conditional_entropy_integrable (hN : 2 ≤ n + 1) (hsub : β < 4)
    (hJ3 : 3 ≤ J) {f : Configuration (n + 1) → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell)))
    (i : Fin (n + 1)) :
    let κ := PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
    Integrable (conditionalEntropyValue κ (fun p => f (insertSite i p.2 p.1) ^ 2))
      (Measure.map (removeSite i) (labelGibbsMeasure hJ η β)) := by
  let P := labelGibbsMeasure hJ η β
  let ρ := Measure.map (removeSite i) P
  let κ := PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
    (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
  let F := squareExtension η (fun Z => f (sources Z))
  let F' := fun p : Configuration n × Torus => F (insertSite i p.2 p.1)
  let : IsProbabilityMeasure P := isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ hsub
  let : IsMarkovKernel κ := PositiveProductConditionals.isMarkovKernel_conditionalKernel
    (μ (η i)) (referenceTilt μ η β) (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
  have hm : Measurable F' := (measurable_squareExtension hJ3 η hf.continuousOn).comp
    ((measurable_insertSite i).comp measurable_swap)
  obtain ⟨K, hb⟩ := squareExtension_bounds η hf.continuousOn
  have hi := integrable_mass_mul_conditionalLogEntropy κ ρ hm (fun Y z => hb (insertSite i z Y))
  have he : (fun Y => ConditionalEntropyDisintegration.sectionMass κ F' Y * conditionalLogEntropy κ F' Y) =
      conditionalEntropyValue κ F' := funext fun Y =>
    sectionMass_mul_conditionalLogEntropy κ hm (fun Y z => hb (insertSite i z Y)) Y
  rw [he] at hi
  apply hi.congr
  exact (ae_squareExtension_conditional hJ hJ3 μ η hformula hN hβ hsub f i).mono fun Y hY =>
    conditionalEntropyValue_congr_ae κ Y hY

/-- The one-site source entropy estimate, integrated against the actual
outside marginal and pulled back to the original specified-label law. -/
theorem source_conditional_entropy_energy (hN : 2 ≤ n + 1) (hsub₀ : β₀ < 4)
    {f : Configuration (n + 1) → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell)))
    (i : Fin (n + 1)) :
    let κ := PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
    Integrable (fun X => conditionalEntropyValue κ
      (fun p => f (insertSite i p.2 p.1) ^ 2) (removeSite i X)) (labelGibbsMeasure hJ η β) ∧
    (∫ X, conditionalEntropyValue κ (fun p => f (insertSite i p.2 p.1) ^ 2) (removeSite i X)
      ∂labelGibbsMeasure hJ η β) ≤ (entropyBound β₀ / (J : ℝ) ^ 2) *
      ∫ X, ‖coordinateOrdinaryGradient f i X‖ ^ 2 ∂labelGibbsMeasure hJ η β := by
  have hJ3 : 3 ≤ J := by omega
  have hsub : β < 4 := hβ₀.trans_lt hsub₀
  let κ := PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
    (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
  let H := conditionalEntropyValue κ (fun p => f (insertSite i p.2 p.1) ^ 2)
  have hi : Integrable H (Measure.map (removeSite i) (labelGibbsMeasure hJ η β)) :=
    source_conditional_entropy_integrable hJ μ η hβ hformula hN hsub hJ3 hf i
  have hE := source_coordinate_energy_disintegration hJ μ η hβ hformula hN hsub hJ3 hf i
  refine ⟨(integrable_map_measure hi.aestronglyMeasurable (measurable_removeSite i).aemeasurable).mp hi, ?_⟩
  rw [← integral_map (measurable_removeSite i).aemeasurable hi.aestronglyMeasurable]
  calc
    ∫ Y, H Y ∂Measure.map (removeSite i) (labelGibbsMeasure hJ η β) ≤
        ∫ Y, (entropyBound β₀ / (J : ℝ) ^ 2) *
          (∫ z, ‖coordinateOrdinaryGradient f i (insertSite i z Y)‖ ^ 2 ∂κ Y)
          ∂Measure.map (removeSite i) (labelGibbsMeasure hJ η β) := by
      apply integral_mono_ae hi (hE.1.const_mul _)
      exact (ae_prescribedOutside_labelGibbs hJ η β i).mono fun Y hY =>
        fixed_section_entropy_le hJ μ η hβ hβ₀ hformula hmesh ht hη hJ3 hf i Y hY
    _ = _ := by rw [integral_const_mul, hE.2]

/-- Source lines 2709–2717, with the existing unscaled physical energy density.
Every real integral in the comparison is genuinely integrable. -/
theorem source_entropy_sum_energy (hN : 2 ≤ n + 1) (hsub₀ : β₀ < 4)
    {f : Configuration (n + 1) → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell))) :
    let κ := fun i => PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
    Integrable (BoundaryEdgeSummation.totalEnergyDensity f) (labelGibbsMeasure hJ η β) ∧
    (∀ i, Integrable (fun X => conditionalEntropyValue (κ i)
      (fun p => f (insertSite i p.2 p.1) ^ 2) (removeSite i X)) (labelGibbsMeasure hJ η β)) ∧
    (∑ i, ∫ X, conditionalEntropyValue (κ i) (fun p => f (insertSite i p.2 p.1) ^ 2)
      (removeSite i X) ∂labelGibbsMeasure hJ η β) ≤
      (entropyBound β₀ / (J : ℝ) ^ 2) *
        ∫ X, BoundaryEdgeSummation.totalEnergyDensity f X ∂labelGibbsMeasure hJ η β := by
  have hJ3 : 3 ≤ J := by omega
  have hsub : β < 4 := hβ₀.trans_lt hsub₀
  have he := source_full_energy_integrable hJ hJ3 hN η hβ hsub hf
  have hs := fun i => source_conditional_entropy_energy hJ μ η hβ hβ₀ hformula hmesh ht hη hN hsub₀ hf i
  refine ⟨he, fun i => (hs i).1, ?_⟩
  calc
    _ ≤ ∑ i, (entropyBound β₀ / (J : ℝ) ^ 2) *
        ∫ X, ‖coordinateOrdinaryGradient f i X‖ ^ 2 ∂labelGibbsMeasure hJ η β :=
      Finset.sum_le_sum fun i _ => (hs i).2
    _ = _ := by
      rw [← Finset.mul_sum, ← integral_finsetSum _
        (fun i _ => source_coordinate_energy_integrable hJ hJ3 hN η hβ hsub hf i)]
      rfl

/-- The same bound in the source's tilted conditional-log-entropy notation. -/
theorem source_tilted_entropy_sum_energy (hN : 2 ≤ n + 1) (hsub₀ : β₀ < 4)
    {f : Configuration (n + 1) → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell)))
    (hS : 0 < ∫ X, f X ^ 2 ∂labelGibbsMeasure hJ η β) :
    let κ := fun i => PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
    (∫ X, f X ^ 2 ∂labelGibbsMeasure hJ η β) *
      (∑ i, ∫ X, conditionalLogEntropy (κ i) (fun p => f (insertSite i p.2 p.1) ^ 2)
        (removeSite i X) ∂normalizedTilt (labelGibbsMeasure hJ η β) (fun X => f X ^ 2)) ≤
      (entropyBound β₀ / (J : ℝ) ^ 2) *
        ∫ X, BoundaryEdgeSummation.totalEnergyDensity f X ∂labelGibbsMeasure hJ η β := by
  have hJ3 : 3 ≤ J := by omega
  exact ((source_lipschitz_entropy_sum hJ hJ3 μ η hformula hN hβ
    (hβ₀.trans_lt hsub₀) hf hS).2).trans_le
      (source_entropy_sum_energy hJ μ η hβ hβ₀ hformula hmesh ht hη hN hsub₀ hf).2.2

end ActualReference

end PeriodicAttractiveLogGas.SourceConditionalEntropyEnergy
