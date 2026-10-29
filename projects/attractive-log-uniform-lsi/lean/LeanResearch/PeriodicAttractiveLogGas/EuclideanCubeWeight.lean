import LeanResearch.PeriodicAttractiveLogGas.FixedParticleAOne
import LeanResearch.PeriodicAttractiveLogGas.ConditionalSourceCharts

/-! Transfer of the A1 estimate to the original Euclidean configuration
space. Grouping coordinates is used only for measure transport. All norms
and derivatives in the subsequent weighted estimates remain Euclidean. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace PeriodicAttractiveLogGas.EuclideanCubeWeight
open PhysicalCubes CubeProbability PeriodicWeightRegularity ConditionalSourceCharts
  MovingPoleNumerators

variable {ι : Type*} [Fintype ι]

def law (c : EuclideanSpace ℝ ι) (ℓ : ℝ) : Measure (EuclideanSpace ℝ ι) :=
  (volume (cube c ℓ))⁻¹ • volume.restrict (cube c ℓ)

theorem law_probability (c : EuclideanSpace ℝ ι) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    IsProbabilityMeasure (law c ℓ) := by
  constructor
  rw [law, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  apply ENNReal.inv_mul_cancel
  · rw [cube_volume c hℓ.le]
    exact (ENNReal.ofReal_pos.mpr (pow_pos hℓ _)).ne'
  · exact (isCompact_cube c ℓ).measure_lt_top.ne

theorem integral_law (c : EuclideanSpace ℝ ι) (ℓ : ℝ)
    (F : EuclideanSpace ℝ ι → ℝ) :
    (∫ X, F X ∂law c ℓ) = (volume.real (cube c ℓ))⁻¹ * ∫ X in cube c ℓ, F X := by
  rw [law, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  rfl

theorem preimage_particleCube (N : ℕ) (c : Gradient N) (ℓ : ℝ) :
    (blockEquiv : Gradient N → Fin N → PlanarSpace) ⁻¹'
      particleCube N (blockEquiv c) ℓ = cube c ℓ := by
  ext X
  change (∀ i, i ∈ univ → blockEquiv X i ∈ cube (blockEquiv c i) ℓ) ↔ X ∈ cube c ℓ
  simp only [mem_univ, forall_const, mem_cube, blockEquiv_apply, sourceProjection_apply]
  exact ⟨fun h ik => h ik.1 ik.2, fun h i j => h (i,j)⟩

/-- Normalized Euclidean cube volume is exactly the product of normalized
planar square volumes. Haar uniqueness is used only before normalization;
no Pi norm is substituted for the physical Euclidean norm. -/
theorem measurePreserving_blocks_law (N : ℕ) (c₀ : Gradient N) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    MeasurePreserving (blockEquiv : Gradient N → Fin N → PlanarSpace)
      (law c₀ ℓ) (productLaw N (blockEquiv c₀) ℓ) := by
  let e : Gradient N ≃L[ℝ] (Fin N → PlanarSpace) := blockEquiv
  let S := cube c₀ ℓ
  let T := particleCube N (e c₀) ℓ
  let ν : Measure (Fin N → PlanarSpace) := volume
  have hpre : e ⁻¹' T = S := preimage_particleCube N c₀ ℓ
  have hT₀ : ν T ≠ 0 := by
    rw [show ν T = ENNReal.ofReal (ℓ ^ (2 * N)) from particleCube_volume N (e c₀) hℓ.le]
    exact (ENNReal.ofReal_pos.mpr (pow_pos hℓ _)).ne'
  have hTtop : ν T ≠ ⊤ := (isCompact_particleCube N (e c₀) ℓ).measure_lt_top.ne
  let c : ℝ≥0 := Measure.addHaarScalarFactor ((volume : Measure (Gradient N)).map e) ν
  have hhaar : (volume : Measure (Gradient N)).map e = (c : ℝ≥0∞) • ν :=
    Measure.isAddLeftInvariant_eq_smul _ _
  have hr := e.toHomeomorph.measurableEmbedding.restrict_map (volume : Measure (Gradient N)) T
  change ((volume : Measure (Gradient N)).map e).restrict T =
    (volume.restrict (e ⁻¹' T)).map e at hr
  rw [hpre, hhaar, Measure.restrict_smul] at hr
  have hmap : (law c₀ ℓ).map e = ((volume S)⁻¹ * (c : ℝ≥0∞)) • ν.restrict T := by
    rw [law, Measure.map_smul _ e.continuous.measurable.aemeasurable, ← hr, smul_smul]
  have hp : IsProbabilityMeasure ((law c₀ ℓ).map e) := by
    letI := law_probability c₀ hℓ
    infer_instance
  have hn : (law c₀ ℓ).map e = (ν T)⁻¹ • ν.restrict T := by
    rw [hmap] at hp ⊢
    exact probability_smul_restrict_eq_normalized ν T _ hT₀ hTtop hp
  refine ⟨e.continuous.measurable, ?_⟩
  rw [hn, productLaw_eq N (e c₀) hℓ]
  congr 1
  exact congrArg Inv.inv (particleCube_volume N (e c₀) hℓ.le)

theorem quotient_blocks (N : ℕ) (X : Gradient N) :
    planarConfigurationQuotient N (blockEquiv X) = configurationQuotient N X := rfl

theorem blocks_quasiMeasurePreserving (N : ℕ) :
    Measure.QuasiMeasurePreserving (blockEquiv : Gradient N → Fin N → PlanarSpace) volume volume := by
  let e : Gradient N ≃L[ℝ] (Fin N → PlanarSpace) := blockEquiv
  let c : ℝ≥0 := Measure.addHaarScalarFactor ((volume : Measure (Gradient N)).map e)
    (volume : Measure (Fin N → PlanarSpace))
  have hhaar : (volume : Measure (Gradient N)).map e =
      (c : ℝ≥0∞) • (volume : Measure (Fin N → PlanarSpace)) :=
    Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨e.continuous.measurable, ?_⟩
  rw [hhaar]
  exact Measure.smul_absolutelyContinuous

def collisionSet (N : ℕ) : Set (Gradient N) :=
  configurationQuotient N ⁻¹' PeriodicAttractiveLogGas.collisionSet N

theorem collisionSet_eq_preimage (N : ℕ) :
    collisionSet N = (blockEquiv : Gradient N → Fin N → PlanarSpace) ⁻¹' liftedCollisionSet N := rfl

theorem collisionSet_closed (N : ℕ) : IsClosed (collisionSet N) := by
  rw [collisionSet_eq_preimage]
  exact (liftedCollisionSet_closed N).preimage (blockEquiv : Gradient N ≃L[ℝ] _).continuous

theorem collisionSet_null (N : ℕ) : volume (collisionSet N) = 0 := by
  rw [collisionSet_eq_preimage]
  exact (blocks_quasiMeasurePreserving N).preimage_null (liftedCollisionSet_null N)

def weight (N : ℕ) (a : ℝ) (X : Gradient N) : ℝ :=
  torusPairWeight N a (configurationQuotient N X)

theorem weight_eq_blocks (N : ℕ) (a : ℝ) (X : Gradient N) :
    weight N a X = torusPairWeight N a (planarConfigurationQuotient N (blockEquiv X)) := rfl

theorem measurable_weight (N : ℕ) (a : ℝ) : Measurable (weight N a) :=
  (measurable_torusPairWeight N a).comp
    ((continuous_planarConfigurationQuotient N).comp (blockEquiv : Gradient N ≃L[ℝ] _).continuous).measurable

theorem weight_nonneg (N : ℕ) (a : ℝ) (X : Gradient N) : 0 ≤ weight N a X :=
  torusPairWeight_nonneg _ _ _

theorem ae_one_le_weight (N : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    ∀ᵐ X : Gradient N ∂volume, 1 ≤ weight N a X :=
  (blocks_quasiMeasurePreserving N).ae (ae_one_le_lifted_weight N ha)

theorem continuousAt_weight (N : ℕ) (a : ℝ) {X : Gradient N}
    (hX : X ∉ collisionSet N) : ContinuousAt (weight N a) X :=
  (continuousAt_lifted_weight N a (X := blockEquiv X) hX).comp
    (blockEquiv : Gradient N ≃L[ℝ] _).continuous.continuousAt


/-- Actual Euclidean cube integrability is transported through the proved
normalized cube law before any integral comparison is used. -/
theorem integrableOn_weight_cube {N : ℕ} (hN : 2 ≤ N) {β₀ a ℓ : ℝ}
    (hsub : β₀ < 4) (ha : 0 ≤ a) (haa : a ≤ FixedWeightConstants.exponent N β₀)
    (hℓ : 0 < ℓ) (c : Gradient N) : IntegrableOn (weight N a) (cube c ℓ) volume := by
  have hi := integrable_torusWeight_productLaw N (by omega) (blockEquiv c) ha
    (FixedParticleAOne.exponent_subcritical hN hsub haa) hℓ
  have hh := (measurePreserving_blocks_law N c hℓ).integrable_comp_of_integrable hi
  change Integrable (weight N a) ((volume (cube c ℓ))⁻¹ • volume.restrict (cube c ℓ)) at hh
  exact (integrable_inv_smul_measure
    (show volume (cube c ℓ) ≠ 0 by rw [cube_volume c hℓ.le]; positivity)
    (isCompact_cube c ℓ).measure_lt_top.ne).mp hh

theorem locallyIntegrable_weight {N : ℕ} (hN : 2 ≤ N) {β₀ a : ℝ}
    (hsub : β₀ < 4) (ha : 0 ≤ a) (haa : a ≤ FixedWeightConstants.exponent N β₀) :
    LocallyIntegrable (weight N a) volume := by
  intro c
  refine ⟨cube c 2, ?_, integrableOn_weight_cube hN hsub ha haa (by norm_num) c⟩
  have hc : WithLp.ofLp ⁻¹' pi univ (fun j => Icc (c j - 1) (c j + 1)) ∈ 𝓝 c :=
    (EuclideanSpace.equiv (Fin N × Fin 2) ℝ).continuous.continuousAt.preimage_mem_nhds
      (set_pi_mem_nhds Set.finite_univ fun j _ => Icc_mem_nhds
        (by change c j - 1 < c j; linarith) (by change c j < c j + 1; linarith))
  simpa only [cube, show (2 : ℝ) / 2 = 1 by norm_num] using hc

/-- The all-cube A1 inequality in the original Euclidean physical space. -/
theorem cube_integral_le {N : ℕ} (hN : 2 ≤ N) {β₀ a ℓ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ha : 0 ≤ a)
    (haa : a ≤ FixedWeightConstants.exponent N β₀) (hℓ : 0 < ℓ)
    (c Y : Gradient N) (hY : Y ∈ cube c ℓ) (hYcol : Y ∉ collisionSet N) :
    (∫ X in cube c ℓ, weight N a X) ≤
      FixedParticleAOne.constant N β₀ * ℓ ^ (2 * N) * weight N a Y := by
  have hmem : blockEquiv Y ∈ particleCube N (blockEquiv c) ℓ := by
    change Y ∈ (blockEquiv : Gradient N → Fin N → PlanarSpace) ⁻¹' particleCube N (blockEquiv c) ℓ
    rwa [preimage_particleCube]
  have hh := FixedParticleAOne.cube_integral_le hN hβ₀ hsub ha haa hℓ
    (blockEquiv c) (blockEquiv Y) hmem hYcol
  have hm := (measurePreserving_blocks_law N c hℓ).integral_comp
    (blockEquiv : Gradient N ≃L[ℝ] (Fin N → PlanarSpace)).toHomeomorph.measurableEmbedding
    (fun X => torusPairWeight N a (planarConfigurationQuotient N X))
  rw [integral_law, integral_productLaw N (blockEquiv c) hℓ, smul_eq_mul] at hm
  have hvol : volume.real (cube c ℓ) = ℓ ^ (2 * N) := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] using cube_volume_real c hℓ.le
  rw [hvol] at hm
  have hm' := mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ hℓ.ne')) hm
  exact hm'.trans_le hh

/-- Original normalized reference law on the Euclidean unit cube. -/
theorem quotient_unit_cube (N : ℕ) (c : Gradient N) :
    MeasurePreserving (configurationQuotient N) (law c 1) (referenceMeasure N) := by
  simpa only [Nat.cast_one, Function.comp_def, quotient_blocks] using
    (PeriodicCubeVolume.quotient_productLaw_integer N (by norm_num : 0 < 1) (blockEquiv c)).comp
      (measurePreserving_blocks_law N c (by norm_num))

end PeriodicAttractiveLogGas.EuclideanCubeWeight

