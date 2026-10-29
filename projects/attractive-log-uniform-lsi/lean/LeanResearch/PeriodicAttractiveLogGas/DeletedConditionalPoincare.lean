import LeanResearch.PeriodicAttractiveLogGas.ConfigurationSections
import LeanResearch.PeriodicAttractiveLogGas.DeletedPointEstimates
import LeanResearch.PeriodicAttractiveLogGas.DeletedConditionalVariance

/-! The physical-gradient conclusion of source Proposition 3.8.

The law is the actual normalized Green law on the specified product, with
either no deleted interaction or one specified deleted pair. One-site
ordinary gradients are integrated using actual resampling stationarity.
For functions Lipschitz only on the closed product, a physical McShane
extension and the proved null-boundary locality recover the original
values and ordinary coordinate gradients. The energy is the unscaled sum
of squared Euclidean coordinate gradients.

SOURCE_ONLY candidate: no Lean execution, axiom inspection, independent
semantic review or protected acceptance is asserted by this file.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace PeriodicAttractiveLogGas.DeletedConditionalPoincare

open MeshCells GreenPointWeights LabelOccupations ConditionalLawEstimates
open OneCoordinateConditionals (adjacentShapes patchDomain measurableSet_patchDomain)
open CoordinateConditionalKernels
  (PatchCoordinates patchInclusion measurable_patchInclusion domainInclusion_update
    map_domainInclusion_domainMeasure patchPoint)
open CoordinateOscillation (siteAverage)
open ConditionalVarianceIntegral (kernelVariance)

def closedPatchProduct {N J : ℕ} (hJ : 0 < J)
    (A : Fin N → MeshIndex J) (B : Fin N → Patch) : Set (Configuration N) :=
  Set.pi univ (fun i ↦ closure (patchDomain J hJ (A i) (B i)))

theorem domain_shape {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (b : Patch) :
    TorusPatchDensity.domain (LocalPointEstimates.shape b) J hJ a =
      patchDomain J hJ a b := by
  cases b <;> rfl

theorem closedPatchProduct_nonempty {N J : ℕ} (hJ : 0 < J)
    (A : Fin N → MeshIndex J) (B : Fin N → Patch) :
    (closedPatchProduct hJ A B).Nonempty := by
  simpa only [closedPatchProduct, domain_shape] using
    closed_product_patches_nonempty hJ A (fun i ↦ LocalPointEstimates.shape (B i))

theorem jointLaw_absolutelyContinuous {n J : ℕ} (hJ : 0 < J)
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) :
    DeletedPairConditionals.jointLaw hJ A B d β ≪
      Measure.pi (fun i ↦ TorusPatchDensity.baseMeasure
        (LocalPointEstimates.shape (B i)) J hJ (A i)) := by
  simpa only [DeletedPairConditionals.jointLaw, LocalPointEstimates.baseMeasure_shape] using
    PositiveProductConditionals.productLaw_absolutelyContinuous
      (fun i ↦ patchMeasure J hJ (A i) (B i))
      (DeletedPairEnsemble.weight regularGreenRepresentative d β)

theorem measurePreserving_patchInclusion {n J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) :
    MeasurePreserving (patchInclusion hJ A B)
      (DeletedPairConditionals.patchLaw hJ hJ2 A B d β)
      (DeletedPairConditionals.jointLaw hJ A B d β) := by
  refine ⟨measurable_patchInclusion hJ A B, ?_⟩
  exact map_domainInclusion_domainMeasure
    (fun i ↦ patchDomain J hJ (A i) (B i))
    (fun i ↦ measurableSet_patchDomain J hJ (A i) (B i))
    (fun i ↦ patchPoint hJ hJ2 (A i) (B i)) _
    (DeletedPairConditionals.jointLaw_ae_mem_patches hJ hJ2 A B d β)

theorem jointLaw_eq_raw {n J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) :
    DeletedPairConditionals.jointLaw hJ A B d β =
      DeletedPairEnsemble.law (DeletedPairEnsemble.domainReference hJ A B)
        greenRealRepresentative d β :=
  (DeletedPairConditionals.jointLaw_eq_deleted hJ A B d β).trans
    (DeletedPairEnsemble.regular_domain_law_eq hJ hJ2 A B d β)

/-- All finite-measure and ordinary-gradient integrability gates for the
local function are conclusions, with no measurability demanded off the patch. -/
theorem joint_local_finite {n J : ℕ} (hn : 2 ≤ n + 1)
    (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) {β : ℝ}
    (hβ : 0 ≤ β) (hsub : β < 4) {f : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hf : ConfigurationPhysicalLipschitzOn L f (closedPatchProduct hJ A B)) :
    let ν := DeletedPairConditionals.jointLaw hJ A B d β
    IsProbabilityMeasure ν ∧ (∀ r : ℝ≥0∞, MemLp f r ν) ∧
      (∀ i : Fin (n + 1), ∀ r : ℝ≥0∞, MemLp (coordinateOrdinaryGradient f i) r ν) ∧
      Integrable (fun X ↦ ∑ i, ‖coordinateOrdinaryGradient f i X‖ ^ 2) ν := by
  let ν := DeletedPairConditionals.jointLaw hJ A B d β
  let hp : IsProbabilityMeasure ν :=
    DeletedPairConditionals.jointLaw_probability hJ hJ2 hn A B d hβ hsub
  have hac := jointLaw_absolutelyContinuous hJ A B d β
  have hf' : ConfigurationPhysicalLipschitzOn L f
      (Set.pi univ (fun i ↦ closure (TorusPatchDensity.domain
        (LocalPointEstimates.shape (B i)) J hJ (A i)))) := by
    simpa only [domain_shape, closedPatchProduct] using hf
  exact ⟨hp, fun r ↦ hf'.patch_memLp hJ A _ hac r,
    fun i r ↦ hf'.patch_gradient_memLp hJ A _ hac i r,
    hf'.patch_integrable_energy hJ A _ hac⟩

theorem raw_local_finite {n J : ℕ} (hn : 2 ≤ n + 1)
    (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) {β : ℝ}
    (hβ : 0 ≤ β) (hsub : β < 4) {f : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hf : ConfigurationPhysicalLipschitzOn L f (closedPatchProduct hJ A B)) :
    let ν := DeletedPairEnsemble.law (DeletedPairEnsemble.domainReference hJ A B)
      greenRealRepresentative d β
    IsProbabilityMeasure ν ∧ (∀ r : ℝ≥0∞, MemLp f r ν) ∧
      (∀ i : Fin (n + 1), ∀ r : ℝ≥0∞, MemLp (coordinateOrdinaryGradient f i) r ν) ∧
      Integrable (fun X ↦ ∑ i, ‖coordinateOrdinaryGradient f i X‖ ^ 2) ν := by
  simpa only [jointLaw_eq_raw hJ hJ2] using
    joint_local_finite hn hJ hJ2 A B d hβ hsub hf

/-- The one-site energy is literally the resampling of the corresponding
ordinary coordinate energy. There is no comparison of product norms. -/
theorem section_variance_le_siteAverage {n J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β β₀ : ℝ)
    (g : C(Configuration (n + 1), ℝ)) (i : Fin (n + 1)) (X : PatchCoordinates hJ A B)
    (hsite : FunctionEstimates β₀ J (B i)
      (Measure.map (Subtype.val : patchDomain J hJ (A i) (B i) → Torus)
        (DeletedPairConditionals.patchKernels hJ hJ2 A B d β i X))
      (fun z ↦ g (Function.update (patchInclusion hJ A B X) i z))) :
    let κ := DeletedPairConditionals.patchKernels hJ hJ2 A B d β
    kernelVariance κ (fun Y ↦ g (patchInclusion hJ A B Y)) i X ≤
      (poincareBound β₀ / (J : ℝ) ^ 2) * siteAverage κ
        (fun Y ↦ ‖coordinateOrdinaryGradient g i (patchInclusion hJ A B Y)‖ ^ 2) i X := by
  let κ := DeletedPairConditionals.patchKernels hJ hJ2 A B d β
  let s : Torus → ℝ := fun z ↦ g (Function.update (patchInclusion hJ A B X) i z)
  have hsm : Measurable s := by
    dsimp [s]
    fun_prop
  have hE : Measurable (fun z ↦ ‖torusOrdinaryGradient s z‖ ^ 2) :=
    (measurable_torusOrdinaryGradient s).norm.pow_const 2
  have hv := ProbabilityTheory.variance_map (μ := κ i X) (X := s)
    hsm.aemeasurable measurable_subtype_coe.aemeasurable
  have he := integral_map_of_stronglyMeasurable (μ := κ i X)
    (measurable_subtype_coe : Measurable
      (Subtype.val : patchDomain J hJ (A i) (B i) → Torus)) hE.stronglyMeasurable
  have h := hsite.uniform_variance
  change ProbabilityTheory.variance s (Measure.map Subtype.val (κ i X)) ≤
    (poincareBound β₀ / (J : ℝ) ^ 2) *
      (∫ z, ‖torusOrdinaryGradient s z‖ ^ 2 ∂Measure.map Subtype.val (κ i X)) at h
  rw [hv, he] at h
  simpa only [kernelVariance, siteAverage, Function.comp_def, patchInclusion,
    domainInclusion_update, coordinateOrdinaryGradient_update, s, κ] using h

/-- Integrating the actual conditional variance uses stationarity of the
proved conditional kernel. All terms are shown integrable before comparison. -/
theorem integral_section_variance_le_energy {n J : ℕ} (hn : 2 ≤ n + 1)
    (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) {β β₀ : ℝ}
    (hβ : 0 ≤ β) (hsub : β < 4)
    (g : C(Configuration (n + 1), ℝ)) {L : ℝ≥0}
    (hg : ConfigurationEuclideanLipschitzWith L g) (i : Fin (n + 1))
    (hsite : ∀ X : PatchCoordinates hJ A B,
      FunctionEstimates β₀ J (B i)
        (Measure.map (Subtype.val : patchDomain J hJ (A i) (B i) → Torus)
          (DeletedPairConditionals.patchKernels hJ hJ2 A B d β i X))
        (fun z ↦ g (Function.update (patchInclusion hJ A B X) i z))) :
    let μ := DeletedPairConditionals.patchLaw hJ hJ2 A B d β
    let κ := DeletedPairConditionals.patchKernels hJ hJ2 A B d β
    (∫ X, kernelVariance κ (fun Y ↦ g (patchInclusion hJ A B Y)) i X ∂μ) ≤
      (poincareBound β₀ / (J : ℝ) ^ 2) *
        (∫ X, ‖coordinateOrdinaryGradient g i (patchInclusion hJ A B X)‖ ^ 2 ∂μ) := by
  let μ := DeletedPairConditionals.patchLaw hJ hJ2 A B d β
  let ν := DeletedPairConditionals.jointLaw hJ A B d β
  let κ := DeletedPairConditionals.patchKernels hJ hJ2 A B d β
  let hp : IsProbabilityMeasure μ :=
    DeletedPairConditionals.patchLaw_probability hJ hJ2 hn A B d hβ hsub
  let hq : IsProbabilityMeasure ν :=
    DeletedPairConditionals.jointLaw_probability hJ hJ2 hn A B d hβ hsub
  let e : PatchCoordinates hJ A B → ℝ :=
    fun X ↦ ‖coordinateOrdinaryGradient g i (patchInclusion hJ A B X)‖ ^ 2
  have hm : MeasurePreserving (patchInclusion hJ A B) μ ν :=
    measurePreserving_patchInclusion hJ hJ2 A B d β
  have hem : Measurable e :=
    ((measurable_coordinateOrdinaryGradient g.continuous i).comp hm.measurable).norm.pow_const 2
  have hei : Integrable e μ := hm.integrable_comp_of_integrable
    (integrable_coordinate_energy hg ν i)
  have hmem : MemLp (fun X ↦ g (patchInclusion hJ A B X)) 2 μ :=
    MemLp.of_bound (g.continuous.measurable.comp hm.measurable).aestronglyMeasurable
      ‖g‖ (Eventually.of_forall fun X ↦ g.norm_coe_le_norm _)
  have hind := DeletedPairConditionals.independentSite_patchKernels hJ hJ2 A B d β
  have hstat := DeletedPairConditionals.preservesLaw_patchKernels hJ hJ2 hn A B d hβ hsub
  have hvi := ConditionalVarianceIntegral.integrable_kernelVariance κ μ hind hstat hmem i
  have hai := ConditionalVarianceIntegral.integrable_siteAverage κ μ hstat hem hei i
  calc
    _ ≤ ∫ X, (poincareBound β₀ / (J : ℝ) ^ 2) * siteAverage κ e i X ∂μ :=
      integral_mono hvi (hai.const_mul _) (fun X ↦
        section_variance_le_siteAverage hJ hJ2 A B d β β₀ g i X (hsite X))
    _ = _ := by
      rw [integral_const_mul, ConditionalVarianceIntegral.integral_siteAverage κ μ hstat hem hei i]

/-- Algebraic assembly helper. Its two inputs are discharged below by
DeletedConditionalVariance and DeletedPointEstimates for each source law. -/
theorem global_poincare_of_variance {n J : ℕ} (hn : 2 ≤ n + 1)
    (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) {β β₀ : ℝ}
    (hβ : 0 ≤ β) (hsub : β < 4)
    (g : C(Configuration (n + 1), ℝ)) {L : ℝ≥0}
    (hg : ConfigurationEuclideanLipschitzWith L g)
    (hvariance : ProbabilityTheory.variance (fun X ↦ g (patchInclusion hJ A B X))
      (DeletedPairConditionals.patchLaw hJ hJ2 A B d β) ≤
      2 * ∑ i, ∫ X, kernelVariance (DeletedPairConditionals.patchKernels hJ hJ2 A B d β)
        (fun Y ↦ g (patchInclusion hJ A B Y)) i X
          ∂DeletedPairConditionals.patchLaw hJ hJ2 A B d β)
    (hsite : ∀ i : Fin (n + 1), ∀ X : PatchCoordinates hJ A B,
      FunctionEstimates β₀ J (B i)
        (Measure.map (Subtype.val : patchDomain J hJ (A i) (B i) → Torus)
          (DeletedPairConditionals.patchKernels hJ hJ2 A B d β i X))
        (fun z ↦ g (Function.update (patchInclusion hJ A B X) i z))) :
    ProbabilityTheory.variance g (DeletedPairConditionals.jointLaw hJ A B d β) ≤
      (2 * poincareBound β₀ / (J : ℝ) ^ 2) *
        (∫ X, ∑ i, ‖coordinateOrdinaryGradient g i X‖ ^ 2
          ∂DeletedPairConditionals.jointLaw hJ A B d β) := by
  let μ := DeletedPairConditionals.patchLaw hJ hJ2 A B d β
  let ν := DeletedPairConditionals.jointLaw hJ A B d β
  let κ := DeletedPairConditionals.patchKernels hJ hJ2 A B d β
  let hq : IsProbabilityMeasure ν :=
    DeletedPairConditionals.jointLaw_probability hJ hJ2 hn A B d hβ hsub
  have hm : MeasurePreserving (patchInclusion hJ A B) μ ν :=
    measurePreserving_patchInclusion hJ hJ2 A B d β
  have hei (i : Fin (n + 1)) :
      Integrable (fun X ↦ ‖coordinateOrdinaryGradient g i (patchInclusion hJ A B X)‖ ^ 2) μ :=
    hm.integrable_comp_of_integrable (integrable_coordinate_energy hg ν i)
  have he : Measurable (fun X : Configuration (n + 1) ↦
      ∑ i, ‖coordinateOrdinaryGradient g i X‖ ^ 2) :=
    Finset.measurable_fun_sum _ fun i _ ↦
      (measurable_coordinateOrdinaryGradient g.continuous i).norm.pow_const 2
  have hint : (∫ X, ∑ i, ‖coordinateOrdinaryGradient g i (patchInclusion hJ A B X)‖ ^ 2 ∂μ) =
      ∫ X, ∑ i, ‖coordinateOrdinaryGradient g i X‖ ^ 2 ∂ν := by
    rw [← hm.map_eq]
    exact (integral_map_of_stronglyMeasurable hm.measurable he.stronglyMeasurable).symm
  calc
    _ = ProbabilityTheory.variance (fun X ↦ g (patchInclusion hJ A B X)) μ :=
      (hm.variance_fun_comp g.continuous.measurable.aemeasurable).symm
    _ ≤ 2 * ∑ i, ∫ X, kernelVariance κ (fun Y ↦ g (patchInclusion hJ A B Y)) i X ∂μ :=
      hvariance
    _ ≤ 2 * ∑ i, (poincareBound β₀ / (J : ℝ) ^ 2) *
        (∫ X, ‖coordinateOrdinaryGradient g i (patchInclusion hJ A B X)‖ ^ 2 ∂μ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun i _ ↦ integral_section_variance_le_energy
        hn hJ hJ2 A B d hβ hsub g hg i (hsite i)
    _ = _ := by
      rw [← Finset.mul_sum, ← integral_finsetSum _ (fun i _ ↦ hei i), hint]
      ring

theorem cells_global_poincare {n J : ℕ} (hn : 2 ≤ n + 1) {β β₀ δ : ℝ}
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hsub : β₀ < 4) (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (g : C(Configuration (n + 1), ℝ)) {L : ℝ≥0}
    (hg : ConfigurationEuclideanLipschitzWith L g) :
    let ν := DeletedPairConditionals.jointLaw (mesh_pos hmesh) η (fun _ ↦ .cell) d β
    ProbabilityTheory.variance g ν ≤ (2 * poincareBound β₀ / (J : ℝ) ^ 2) *
      (∫ X, ∑ i, ‖coordinateOrdinaryGradient g i X‖ ^ 2 ∂ν) := by
  let hJ := mesh_pos hmesh
  let μ := DeletedPairConditionals.patchLaw hJ (mesh_two_le hmesh) η (fun _ ↦ .cell) d β
  let hp : IsProbabilityMeasure μ := DeletedPairConditionals.patchLaw_probability
    hJ (mesh_two_le hmesh) hn η (fun _ ↦ .cell) d hβ (hβ₀.trans_lt hsub)
  have hmem : MemLp (fun X ↦ g (patchInclusion hJ η (fun _ ↦ .cell) X)) 2 μ :=
    MemLp.of_bound (g.continuous.measurable.comp
      (measurable_patchInclusion hJ η (fun _ ↦ .cell))).aestronglyMeasurable
      ‖g‖ (Eventually.of_forall fun X ↦ g.norm_coe_le_norm _)
  apply global_poincare_of_variance hn hJ (mesh_two_le hmesh) η (fun _ ↦ .cell)
    d hβ (hβ₀.trans_lt hsub) g hg
  · exact DeletedConditionalVariance.cells_variance hn d hβ hβ₀ hsub hδ₀ hδ hmesh η hη _ hmem
  · intro i X
    apply DeletedPointEstimates.labelKernel_functionEstimates d hβ hβ₀ hδ hmesh η hη i X
    intro z _hz w _hw
    exact hg.section (patchInclusion hJ η (fun _ ↦ .cell) X) i z (mem_univ _) w (mem_univ _)

theorem adjacent_global_poincare {n J : ℕ} (hn : 2 ≤ n + 1) {β β₀ δ : ℝ}
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hsub : β₀ < 4) (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (t : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η t a r)
    (g : C(Configuration (n + 1), ℝ)) {L : ℝ≥0}
    (hg : ConfigurationEuclideanLipschitzWith L g) :
    let A := Function.update η t a
    let B := adjacentShapes t r
    let ν := DeletedPairConditionals.jointLaw (mesh_pos hmesh) A B d β
    ProbabilityTheory.variance g ν ≤ (2 * poincareBound β₀ / (J : ℝ) ^ 2) *
      (∫ X, ∑ i, ‖coordinateOrdinaryGradient g i X‖ ^ 2 ∂ν) := by
  let hJ := mesh_pos hmesh
  let A := Function.update η t a
  let B := adjacentShapes t r
  let μ := DeletedPairConditionals.patchLaw hJ (mesh_two_le hmesh) A B d β
  let hp : IsProbabilityMeasure μ := DeletedPairConditionals.patchLaw_probability
    hJ (mesh_two_le hmesh) hn A B d hβ (hβ₀.trans_lt hsub)
  have hmem : MemLp (fun X ↦ g (patchInclusion hJ A B X)) 2 μ :=
    MemLp.of_bound (g.continuous.measurable.comp
      (measurable_patchInclusion hJ A B)).aestronglyMeasurable
      ‖g‖ (Eventually.of_forall fun X ↦ g.norm_coe_le_norm _)
  apply global_poincare_of_variance hn hJ (mesh_two_le hmesh) A B
    d hβ (hβ₀.trans_lt hsub) g hg
  · exact DeletedConditionalVariance.adjacent_variance
      hn d hβ hβ₀ hsub hδ₀ hδ hmesh η t a r hadm _ hmem
  · intro i X
    apply DeletedPointEstimates.adjacentKernel_functionEstimates d hβ hβ₀ hδ hmesh η t i a r hadm X
    intro z _hz w _hw
    exact hg.section (patchInclusion hJ A B X) i z (mem_univ _) w (mem_univ _)

/-- Locality transfer for the actual law. The extension estimate is used
only after the unconditional global source endpoints have been proved. -/
theorem localize_poincare {n J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β C : ℝ)
    {f : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hf : ConfigurationPhysicalLipschitzOn L f (closedPatchProduct hJ A B))
    (hglobal : ∀ g : C(Configuration (n + 1), ℝ),
      ConfigurationEuclideanLipschitzWith L g →
      ProbabilityTheory.variance g (DeletedPairConditionals.jointLaw hJ A B d β) ≤
        C * (∫ X, ∑ i, ‖coordinateOrdinaryGradient g i X‖ ^ 2
          ∂DeletedPairConditionals.jointLaw hJ A B d β)) :
    ProbabilityTheory.variance f (DeletedPairConditionals.jointLaw hJ A B d β) ≤
      C * (∫ X, ∑ i, ‖coordinateOrdinaryGradient f i X‖ ^ 2
        ∂DeletedPairConditionals.jointLaw hJ A B d β) := by
  obtain ⟨g, hg, hfg⟩ := hf.exists_extension (closedPatchProduct_nonempty hJ A B)
  have hval : f =ᵐ[DeletedPairConditionals.jointLaw hJ A B d β] g :=
    (DeletedPairConditionals.jointLaw_ae_mem_patches hJ hJ2 A B d β).mono fun X hX ↦
      hfg (fun i _ ↦ subset_closure (hX i))
  have heq : EqOn f g (Set.pi univ (fun i ↦ closure (TorusPatchDensity.domain
      (LocalPointEstimates.shape (B i)) J hJ (A i)))) := by
    simpa only [domain_shape, closedPatchProduct] using hfg
  have hgrad := ae_coordinateOrdinaryGradient_congr_on_patches hJ A
    (fun i ↦ LocalPointEstimates.shape (B i)) (jointLaw_absolutelyContinuous hJ A B d β) heq
  calc
    _ = ProbabilityTheory.variance g (DeletedPairConditionals.jointLaw hJ A B d β) :=
      ProbabilityTheory.variance_congr hval
    _ ≤ _ := hglobal g hg
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hgrad] with X hX
      exact Finset.sum_congr rfl (fun i _ ↦ by rw [hX i])

/-- Source fine-PI on the actual regular-Green joint law, for every
function Lipschitz only on the product of the prescribed closed cells. -/
theorem cells_joint_poincare {n J : ℕ} (hn : 2 ≤ n + 1) {β β₀ δ : ℝ}
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hsub : β₀ < 4) (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    {f : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hf : ConfigurationPhysicalLipschitzOn L f
      (closedPatchProduct (mesh_pos hmesh) η (fun _ ↦ .cell))) :
    let ν := DeletedPairConditionals.jointLaw (mesh_pos hmesh) η (fun _ ↦ .cell) d β
    ProbabilityTheory.variance f ν ≤ (2 * poincareBound β₀ / (J : ℝ) ^ 2) *
      (∫ X, ∑ i, ‖coordinateOrdinaryGradient f i X‖ ^ 2 ∂ν) :=
  localize_poincare (mesh_pos hmesh) (mesh_two_le hmesh) η (fun _ ↦ .cell) d β _ hf
    (fun g hg ↦ cells_global_poincare hn d hβ hβ₀ hsub hδ₀ hδ hmesh η hη g hg)

/-- Both admissible endpoint completions, every conditioned coordinate,
both orientations and periodic wraps use the same physical constant. -/
theorem adjacent_joint_poincare {n J : ℕ} (hn : 2 ≤ n + 1) {β β₀ δ : ℝ}
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hsub : β₀ < 4) (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (t : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η t a r)
    {f : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hf : ConfigurationPhysicalLipschitzOn L f (closedPatchProduct (mesh_pos hmesh)
      (Function.update η t a) (adjacentShapes t r))) :
    let A := Function.update η t a
    let B := adjacentShapes t r
    let ν := DeletedPairConditionals.jointLaw (mesh_pos hmesh) A B d β
    ProbabilityTheory.variance f ν ≤ (2 * poincareBound β₀ / (J : ℝ) ^ 2) *
      (∫ X, ∑ i, ‖coordinateOrdinaryGradient f i X‖ ^ 2 ∂ν) :=
  localize_poincare (mesh_pos hmesh) (mesh_two_le hmesh)
    (Function.update η t a) (adjacentShapes t r) d β _ hf
    (fun g hg ↦ adjacent_global_poincare hn d hβ hβ₀ hsub hδ₀ hδ hmesh η t a r hadm g hg)

/-- Literal source deleted-law density with the original Green
representative; taking d = none includes the original prescribed-cell law. -/
theorem cells_poincare {n J : ℕ} (hn : 2 ≤ n + 1) {β β₀ δ : ℝ}
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hsub : β₀ < 4) (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    {f : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hf : ConfigurationPhysicalLipschitzOn L f
      (closedPatchProduct (mesh_pos hmesh) η (fun _ ↦ .cell))) :
    let ν := DeletedPairEnsemble.law
      (DeletedPairEnsemble.domainReference (mesh_pos hmesh) η (fun _ ↦ .cell))
      greenRealRepresentative d β
    ProbabilityTheory.variance f ν ≤ (2 * poincareBound β₀ / (J : ℝ) ^ 2) *
      (∫ X, ∑ i, ‖coordinateOrdinaryGradient f i X‖ ^ 2 ∂ν) := by
  simpa only [jointLaw_eq_raw (mesh_pos hmesh) (mesh_two_le hmesh)] using
    cells_joint_poincare hn d hβ hβ₀ hsub hδ₀ hδ hmesh η hη hf

/-- Literal source deleted-law density for the adjacent restriction.
No regularity or measurability of f away from the closed product is assumed. -/
theorem adjacent_poincare {n J : ℕ} (hn : 2 ≤ n + 1) {β β₀ δ : ℝ}
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hsub : β₀ < 4) (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (t : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η t a r)
    {f : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hf : ConfigurationPhysicalLipschitzOn L f (closedPatchProduct (mesh_pos hmesh)
      (Function.update η t a) (adjacentShapes t r))) :
    let A := Function.update η t a
    let B := adjacentShapes t r
    let ν := DeletedPairEnsemble.law
      (DeletedPairEnsemble.domainReference (mesh_pos hmesh) A B) greenRealRepresentative d β
    ProbabilityTheory.variance f ν ≤ (2 * poincareBound β₀ / (J : ℝ) ^ 2) *
      (∫ X, ∑ i, ‖coordinateOrdinaryGradient f i X‖ ^ 2 ∂ν) := by
  simpa only [jointLaw_eq_raw (mesh_pos hmesh) (mesh_two_le hmesh)] using
    adjacent_joint_poincare hn d hβ hβ₀ hsub hδ₀ hδ hmesh η t a r hadm hf

/-- The no-deletion case stated directly for the normalized Gibbs
restriction to the actual prescribed label fiber. -/
theorem labelGibbs_poincare {n J : ℕ} (hn : 2 ≤ n + 1) {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    {f : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hf : ConfigurationPhysicalLipschitzOn L f
      (closedPatchProduct (mesh_pos hmesh) η (fun _ ↦ .cell))) :
    ProbabilityTheory.variance f (CellRestrictions.labelGibbsMeasure (mesh_pos hmesh) η β) ≤
      (2 * poincareBound β₀ / (J : ℝ) ^ 2) *
        (∫ X, ∑ i, ‖coordinateOrdinaryGradient f i X‖ ^ 2
          ∂CellRestrictions.labelGibbsMeasure (mesh_pos hmesh) η β) := by
  have he : DeletedPairConditionals.jointLaw (mesh_pos hmesh) η (fun _ ↦ .cell) none β =
      CellRestrictions.labelGibbsMeasure (mesh_pos hmesh) η β :=
    (measurePreserving_patchInclusion (mesh_pos hmesh) (mesh_two_le hmesh)
      η (fun _ ↦ .cell) none β).map_eq.symm.trans
        (DeletedPairConditionals.map_patchLaw_none_cells (mesh_pos hmesh) (mesh_two_le hmesh)
          hn η hβ (hβ₀.trans_lt hsub))
  simpa only [he] using
    cells_joint_poincare hn none hβ hβ₀ hsub hδ₀ hδ hmesh η hη hf

/-- The no-deletion adjacent case stated directly for the original
two-cell Gibbs restriction, with its actual unequal mixture weights. -/
theorem twoCellGibbs_poincare {n J : ℕ} (hn : 2 ≤ n + 1) {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (t : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η t a r)
    {f : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hf : ConfigurationPhysicalLipschitzOn L f (closedPatchProduct (mesh_pos hmesh)
      (Function.update η t a) (adjacentShapes t r))) :
    let ν := CellRestrictions.twoCellGibbsMeasure (mesh_pos hmesh) η t a
      (MeshAdjacentCells.nextCell J (mesh_pos hmesh) a r) β
    ProbabilityTheory.variance f ν ≤ (2 * poincareBound β₀ / (J : ℝ) ^ 2) *
      (∫ X, ∑ i, ‖coordinateOrdinaryGradient f i X‖ ^ 2 ∂ν) := by
  have he : DeletedPairConditionals.jointLaw (mesh_pos hmesh)
      (Function.update η t a) (adjacentShapes t r) none β =
      CellRestrictions.twoCellGibbsMeasure (mesh_pos hmesh) η t a
        (MeshAdjacentCells.nextCell J (mesh_pos hmesh) a r) β :=
    (measurePreserving_patchInclusion (mesh_pos hmesh) (mesh_two_le hmesh)
      (Function.update η t a) (adjacentShapes t r) none β).map_eq.symm.trans
        (DeletedPairConditionals.map_patchLaw_none_adjacent (mesh_pos hmesh) (mesh_two_le hmesh)
          hn η t a r hβ (hβ₀.trans_lt hsub))
  simpa only [he] using
    adjacent_joint_poincare hn none hβ hβ₀ hsub hδ₀ hδ hmesh η t a r hadm hf

end PeriodicAttractiveLogGas.DeletedConditionalPoincare
