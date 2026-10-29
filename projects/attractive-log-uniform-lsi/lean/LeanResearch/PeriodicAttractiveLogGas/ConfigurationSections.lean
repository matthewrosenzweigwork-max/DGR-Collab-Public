import LeanResearch.PeriodicAttractiveLogGas.ConfigurationMcShane
import LeanResearch.PeriodicAttractiveLogGas.TorusPatchDensity

/-! Physical coordinate sections and their literal ordinary gradients.
The joint measurability proof uses the parameterized ordinary derivative;
the configuration metric retains the unscaled Euclidean sum of squares. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal

namespace PeriodicAttractiveLogGas

theorem configurationEuclideanDist_update {N : ℕ} (X : Configuration N)
    (i : Fin N) (z w : Torus) :
    configurationEuclideanDist (Function.update X i z) (Function.update X i w) =
      torusEuclideanDist z w := by
  unfold configurationEuclideanDist configurationEuclideanNorm torusEuclideanDist torusEuclideanNorm
  rw [Fintype.sum_prod_type]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [Function.update_of_ne hji]
  · simp

/-- Lipschitz continuity only on the specified physical configuration set. -/
def ConfigurationPhysicalLipschitzOn {N : ℕ} (L : ℝ≥0)
    (f : Configuration N → ℝ) (D : Set (Configuration N)) : Prop :=
  ∀ X ∈ D, ∀ Y ∈ D, |f X - f Y| ≤ (L : ℝ) * configurationEuclideanDist X Y

theorem ConfigurationPhysicalLipschitzOn.section {N : ℕ} {L : ℝ≥0}
    {f : Configuration N → ℝ} {D : Fin N → Set Torus}
    (hf : ConfigurationPhysicalLipschitzOn L f (Set.pi univ D))
    (X : Configuration N) (i : Fin N) (hX : ∀ k, k ≠ i → X k ∈ D k) :
    PhysicalLipschitzOn L (fun z ↦ f (Function.update X i z)) (D i) := by
  intro z hz w hw
  have hmem (y : Torus) (hy : y ∈ D i) : Function.update X i y ∈ Set.pi univ D := by
    intro k hk
    by_cases hki : k = i
    · subst k
      simpa only [Function.update_self] using hy
    · simpa only [Function.update_of_ne hki] using hX k hki
  simpa only [configurationEuclideanDist_update] using hf _ (hmem z hz) _ (hmem w hw)

theorem ConfigurationEuclideanLipschitzWith.section {N : ℕ} {L : ℝ≥0}
    {f : Configuration N → ℝ} (hf : ConfigurationEuclideanLipschitzWith L f)
    (X : Configuration N) (i : Fin N) :
    PhysicalLipschitzOn L (fun z ↦ f (Function.update X i z)) univ := by
  intro z hz w hw
  simpa only [Real.dist_eq, configurationEuclideanDist_update] using
    hf (Function.update X i z) (Function.update X i w)

/-- Literal coordinate partial gradient, including its total representative
at nondifferentiability points. No particle-number or mesh factor is inserted. -/
def coordinateOrdinaryGradient {N : ℕ} (f : Configuration N → ℝ)
    (i : Fin N) (X : Configuration N) : PlanarSpace :=
  torusOrdinaryGradient (fun z ↦ f (Function.update X i z)) (X i)

@[simp] theorem coordinateOrdinaryGradient_update {N : ℕ}
    (f : Configuration N → ℝ) (i : Fin N) (X : Configuration N) (z : Torus) :
    coordinateOrdinaryGradient f i (Function.update X i z) =
      torusOrdinaryGradient (fun w ↦ f (Function.update X i w)) z := by
  simp only [coordinateOrdinaryGradient, Function.update_self, Function.update_idem]

theorem measurable_coordinateOrdinaryGradient {N : ℕ} {f : Configuration N → ℝ}
    (hf : Continuous f) (i : Fin N) : Measurable (coordinateOrdinaryGradient f i) := by
  have hc : Continuous (fun p : Configuration N × PlanarSpace ↦
      f (Function.update p.1 i (torusQuotient p.2))) := by
    have hq := isOpenQuotientMap_torusQuotient.continuous
    fun_prop
  have hd := measurable_fderiv_with_param ℝ
    (f := fun X : Configuration N ↦ fun y : PlanarSpace ↦
      f (Function.update X i (torusQuotient y))) hc
  have hs : Measurable (fun X : Configuration N ↦ (X, centeredLift (X i))) :=
    measurable_id.prodMk (measurable_centeredLift.comp (measurable_pi_apply i))
  exact (InnerProductSpace.toDual ℝ PlanarSpace).symm.continuous.measurable.comp (hd.comp hs)

theorem norm_coordinateOrdinaryGradient_le {N : ℕ} {L : ℝ≥0}
    {f : Configuration N → ℝ} (hf : ConfigurationEuclideanLipschitzWith L f)
    (i : Fin N) (X : Configuration N) : ‖coordinateOrdinaryGradient f i X‖ ≤ (L : ℝ) := by
  have hl : LipschitzWith L (fun y : PlanarSpace ↦
      f (Function.update X i (torusQuotient y))) := by
    rw [← lipschitzOnWith_univ]
    exact (hf.section X i).lift (fun _ _ ↦ mem_univ _)
  rw [coordinateOrdinaryGradient, torusOrdinaryGradient, norm_rectangleOrdinaryGradient]
  exact norm_fderiv_le_of_lipschitz ℝ hl

theorem memLp_coordinateOrdinaryGradient {N : ℕ} {L : ℝ≥0}
    {f : Configuration N → ℝ} (hf : ConfigurationEuclideanLipschitzWith L f)
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (i : Fin N) (r : ℝ≥0∞) :
    MemLp (coordinateOrdinaryGradient f i) r μ :=
  MemLp.of_bound (measurable_coordinateOrdinaryGradient hf.continuous i).aestronglyMeasurable
    (L : ℝ) (Eventually.of_forall (norm_coordinateOrdinaryGradient_le hf i))

theorem integrable_coordinate_energy {N : ℕ} {L : ℝ≥0}
    {f : Configuration N → ℝ} (hf : ConfigurationEuclideanLipschitzWith L f)
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (i : Fin N) :
    Integrable (fun X ↦ ‖coordinateOrdinaryGradient f i X‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm
    (measurable_coordinateOrdinaryGradient hf.continuous i).aestronglyMeasurable).mp
      (memLp_coordinateOrdinaryGradient hf μ i 2)

theorem ConfigurationPhysicalLipschitzOn.exists_extension {N : ℕ} {L : ℝ≥0}
    {f : Configuration N → ℝ} {D : Set (Configuration N)}
    (hf : ConfigurationPhysicalLipschitzOn L f D) (hD : D.Nonempty) :
    ∃ g : C(Configuration N, ℝ), ConfigurationEuclideanLipschitzWith L g ∧ EqOn f g D := by
  have hsub : ∀ X Y : D, dist (f X) (f Y) ≤
      (L : ℝ) * configurationEuclideanDist (X : Configuration N) Y := by
    intro X Y
    simpa only [Real.dist_eq] using hf X X.property Y Y.property
  refine ⟨configurationMcShaneContinuousMap hD (fun X : D ↦ f X) hsub,
    configurationMcShane_lipschitz hD (fun X : D ↦ f X) hsub, ?_⟩
  intro X hX
  exact (configurationMcShane_eq hD (fun X : D ↦ f X) hsub ⟨X, hX⟩).symm

/-- Neighborhood membership is proved using the open quotient chart and
the reference rectangle's null boundary. It is not a boundary core claim. -/
theorem TorusPatchDensity.ae_closed_domain_mem_nhds (b : TorusPatchDensity.Shape)
    (J : ℕ) (hJ : 0 < J) (a : MeshCells.MeshIndex J) :
    ∀ᵐ z ∂TorusPatchDensity.baseMeasure b J hJ a,
      closure (TorusPatchDensity.domain b J hJ a) ∈ 𝓝 z := by
  have hm := TorusPatchDensity.measurePreserving_chart b J hJ a
  have hi : ∀ᵐ z ∂TorusPatchDensity.baseMeasure b J hJ a,
      z ∈ interior (closure (TorusPatchDensity.domain b J hJ a)) := by
    rw [← hm.map_eq]
    apply (ae_map_iff hm.aemeasurable isOpen_interior.measurableSet).mpr
    filter_upwards [RectangleDilation.ae_closed_mem_nhds (TorusPatchDensity.kind b)] with Z hZ
    change TorusPatchDensity.chart b J a Z ∈ interior _
    rw [mem_interior_iff_mem_nhds, ← TorusPatchDensity.chart_image_closed]
    exact ((MeshAdjacentCells.isOpenMap_meshChart J hJ a).comp
      (TorusPatchDensity.orientation b).toHomeomorph.isOpenMap).image_mem_nhds hZ
  exact hi.mono fun z hz ↦ mem_interior_iff_mem_nhds.mp hz

theorem coordinateOrdinaryGradient_congr_on_product {N : ℕ}
    {f g : Configuration N → ℝ} {D : Fin N → Set Torus}
    (hfg : EqOn f g (Set.pi univ D)) (X : Configuration N) (i : Fin N)
    (hX : ∀ k, k ≠ i → X k ∈ D k) (hi : D i ∈ 𝓝 (X i)) :
    coordinateOrdinaryGradient f i X = coordinateOrdinaryGradient g i X := by
  have he : (fun y : PlanarSpace ↦ f (Function.update X i (torusQuotient y))) =ᶠ[𝓝 (centeredLift (X i))]
      (fun y : PlanarSpace ↦ g (Function.update X i (torusQuotient y))) := by
    have ht : Tendsto torusQuotient (𝓝 (centeredLift (X i))) (𝓝 (X i)) := by
      simpa only [torusQuotient_centeredLift] using
        isOpenQuotientMap_torusQuotient.continuous.continuousAt.tendsto
          (x := centeredLift (X i))
    filter_upwards [ht hi] with y hy
    change torusQuotient y ∈ D i at hy
    apply hfg
    intro k hk
    by_cases hki : k = i
    · subst k
      simpa only [Function.update_self] using hy
    · simpa only [Function.update_of_ne hki] using hX k hki
  exact congrArg (InnerProductSpace.toDual ℝ PlanarSpace).symm he.fderiv_eq

theorem ae_closed_product_patch_nhds {N J : ℕ} (hJ : 0 < J)
    (a : Fin N → MeshCells.MeshIndex J) (b : Fin N → TorusPatchDensity.Shape)
    {μ : Measure (Configuration N)}
    (hμ : μ ≪ Measure.pi (fun k ↦ TorusPatchDensity.baseMeasure (b k) J hJ (a k))) :
    ∀ᵐ X ∂μ, ∀ i, closure (TorusPatchDensity.domain (b i) J hJ (a i)) ∈ 𝓝 (X i) := by
  apply hμ.ae_le
  apply ae_all_iff.mpr
  intro i
  have hm := measurePreserving_eval (fun k ↦ TorusPatchDensity.baseMeasure (b k) J hJ (a k)) i
  exact hm.quasiMeasurePreserving.ae (TorusPatchDensity.ae_closed_domain_mem_nhds (b i) J hJ (a i))

/-- Any two extensions have the same literal coordinate gradients almost
everywhere for every law absolutely continuous with respect to the patch product. -/
theorem ae_coordinateOrdinaryGradient_congr_on_patches {N J : ℕ} (hJ : 0 < J)
    (a : Fin N → MeshCells.MeshIndex J) (b : Fin N → TorusPatchDensity.Shape)
    {μ : Measure (Configuration N)}
    (hμ : μ ≪ Measure.pi (fun k ↦ TorusPatchDensity.baseMeasure (b k) J hJ (a k)))
    {f g : Configuration N → ℝ}
    (hfg : EqOn f g (Set.pi univ (fun k ↦ closure (TorusPatchDensity.domain (b k) J hJ (a k))))) :
    ∀ᵐ X ∂μ, ∀ i, coordinateOrdinaryGradient f i X = coordinateOrdinaryGradient g i X := by
  filter_upwards [ae_closed_product_patch_nhds hJ a b hμ] with X hX
  intro i
  exact coordinateOrdinaryGradient_congr_on_product hfg X i
    (fun k _ ↦ mem_of_mem_nhds (hX k)) (hX i)

theorem closed_product_patches_nonempty {N J : ℕ} (hJ : 0 < J)
    (a : Fin N → MeshCells.MeshIndex J) (b : Fin N → TorusPatchDensity.Shape) :
    (Set.pi univ (fun k ↦ closure (TorusPatchDensity.domain (b k) J hJ (a k)))).Nonempty := by
  obtain ⟨X, hX⟩ := (ae_closed_product_patch_nhds hJ a b Measure.AbsolutelyContinuous.rfl).exists
  exact ⟨X, fun k _ ↦ mem_of_mem_nhds (hX k)⟩

theorem ConfigurationPhysicalLipschitzOn.patch_gradient_memLp {N J : ℕ} (hJ : 0 < J)
    (a : Fin N → MeshCells.MeshIndex J) (b : Fin N → TorusPatchDensity.Shape)
    {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    (hμ : μ ≪ Measure.pi (fun k ↦ TorusPatchDensity.baseMeasure (b k) J hJ (a k)))
    {L : ℝ≥0} {f : Configuration N → ℝ}
    (hf : ConfigurationPhysicalLipschitzOn L f
      (Set.pi univ (fun k ↦ closure (TorusPatchDensity.domain (b k) J hJ (a k)))))
    (i : Fin N) (r : ℝ≥0∞) : MemLp (coordinateOrdinaryGradient f i) r μ := by
  obtain ⟨g, hg, hfg⟩ := hf.exists_extension (closed_product_patches_nonempty hJ a b)
  have he := (ae_coordinateOrdinaryGradient_congr_on_patches hJ a b hμ hfg).mono fun X hX ↦ hX i
  exact (memLp_congr_ae he).mpr (memLp_coordinateOrdinaryGradient hg μ i r)

theorem ConfigurationPhysicalLipschitzOn.patch_memLp {N J : ℕ} (hJ : 0 < J)
    (a : Fin N → MeshCells.MeshIndex J) (b : Fin N → TorusPatchDensity.Shape)
    {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    (hμ : μ ≪ Measure.pi (fun k ↦ TorusPatchDensity.baseMeasure (b k) J hJ (a k)))
    {L : ℝ≥0} {f : Configuration N → ℝ}
    (hf : ConfigurationPhysicalLipschitzOn L f
      (Set.pi univ (fun k ↦ closure (TorusPatchDensity.domain (b k) J hJ (a k)))))
    (r : ℝ≥0∞) : MemLp f r μ := by
  obtain ⟨g, hg, hfg⟩ := hf.exists_extension (closed_product_patches_nonempty hJ a b)
  have he : f =ᵐ[μ] g := (ae_closed_product_patch_nhds hJ a b hμ).mono
    fun X hX ↦ hfg (fun k _ ↦ mem_of_mem_nhds (hX k))
  exact (memLp_congr_ae he).mpr
    (MemLp.of_bound g.continuous.aestronglyMeasurable ‖g‖
      (Eventually.of_forall g.norm_coe_le_norm))

theorem ConfigurationPhysicalLipschitzOn.patch_integrable_energy {N J : ℕ} (hJ : 0 < J)
    (a : Fin N → MeshCells.MeshIndex J) (b : Fin N → TorusPatchDensity.Shape)
    {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    (hμ : μ ≪ Measure.pi (fun k ↦ TorusPatchDensity.baseMeasure (b k) J hJ (a k)))
    {L : ℝ≥0} {f : Configuration N → ℝ}
    (hf : ConfigurationPhysicalLipschitzOn L f
      (Set.pi univ (fun k ↦ closure (TorusPatchDensity.domain (b k) J hJ (a k))))) :
    Integrable (fun X ↦ ∑ i, ‖coordinateOrdinaryGradient f i X‖ ^ 2) μ := by
  apply integrable_finsetSum
  intro i hi
  have hm := hf.patch_gradient_memLp hJ a b hμ i 2
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm

end PeriodicAttractiveLogGas
