import LeanResearch.PeriodicAttractiveLogGas.ProbabilityWeightSobolev
import LeanResearch.PeriodicAttractiveLogGas.SobolevEntropy

/-! The fixed-particle distance-weight probability and its exact transport
from a physical unit cube. Normalizers are justified by the collision
integrability and A1 estimates, including the zero exponent. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace PeriodicAttractiveLogGas.FixedWeightProbability
open PhysicalCubes WeightedCubeBounds

def normalizer (N : ℕ) (a : ℝ) : ℝ :=
  ∫ X, torusPairWeight N a X ∂referenceMeasure N

def raw (N : ℕ) (a : ℝ) : Measure (Configuration N) :=
  (referenceMeasure N).withDensity (fun X => ENNReal.ofReal (torusPairWeight N a X))

def law (N : ℕ) (a : ℝ) : Measure (Configuration N) :=
  (ENNReal.ofReal (normalizer N a))⁻¹ • raw N a

lemma normalizer_bounds {N : ℕ} (hN : 2 ≤ N) {β₀ a : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ha : 0 ≤ a)
    (haa : a ≤ FixedWeightConstants.exponent N β₀) :
    1 ≤ normalizer N a ∧ normalizer N a ≤ FixedParticleAOne.normalizationBound N β₀ :=
  FixedParticleAOne.normalization_bounds hN hβ₀ hsub ha haa

lemma raw_univ {N : ℕ} (hN : 2 ≤ N) {β₀ a : ℝ}
    (hsub : β₀ < 4) (ha : 0 ≤ a) (haa : a ≤ FixedWeightConstants.exponent N β₀) :
    raw N a univ = ENNReal.ofReal (normalizer N a) := by
  rw [raw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal (FixedParticleAOne.weight_integrable hN hsub ha haa)
    (Eventually.of_forall (torusPairWeight_nonneg N a))).symm

lemma raw_finite {N : ℕ} (hN : 2 ≤ N) {β₀ a : ℝ}
    (hsub : β₀ < 4) (ha : 0 ≤ a) (haa : a ≤ FixedWeightConstants.exponent N β₀) :
    IsFiniteMeasure (raw N a) :=
  ⟨by rw [raw_univ hN hsub ha haa]; exact ENNReal.ofReal_lt_top⟩

lemma law_probability {N : ℕ} (hN : 2 ≤ N) {β₀ a : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ha : 0 ≤ a)
    (haa : a ≤ FixedWeightConstants.exponent N β₀) : IsProbabilityMeasure (law N a) := by
  constructor
  rw [law, Measure.smul_apply, raw_univ hN hsub ha haa, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_pos.mpr (zero_lt_one.trans_le (normalizer_bounds hN hβ₀ hsub ha haa).1)).ne'
    ENNReal.ofReal_ne_top

lemma raw_eq_smul_law {N : ℕ} {a : ℝ} (hZ : 0 < normalizer N a) :
    raw N a = ENNReal.ofReal (normalizer N a) • law N a := by
  rw [law, smul_smul, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hZ).ne'
    ENNReal.ofReal_ne_top, one_smul]

lemma reference_le_raw (N : ℕ) {a : ℝ} (ha : 0 ≤ a) : referenceMeasure N ≤ raw N a := by
  calc
    referenceMeasure N = (referenceMeasure N).withDensity (fun _ => 1) := by simp
    _ ≤ raw N a := withDensity_mono ((PeriodicWeightRegularity.ae_one_le_reference_weight N ha).mono
      fun X hX => by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hX)

lemma raw_integral (N : ℕ) (a : ℝ) (F : Configuration N → ℝ) :
    (∫ X, F X ∂raw N a) = ∫ X, torusPairWeight N a X * F X ∂referenceMeasure N := by
  rw [raw, integral_withDensity_eq_integral_toReal_smul (measurable_torusPairWeight N a).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (torusPairWeight_nonneg N a _), smul_eq_mul]

lemma law_integral {N : ℕ} {a : ℝ} (hZ : 0 ≤ normalizer N a) (F : Configuration N → ℝ) :
    (∫ X, F X ∂law N a) = (normalizer N a)⁻¹ * ∫ X, F X ∂raw N a := by
  rw [law, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ, smul_eq_mul]

/-- Density transport proved from the actual pushforward identity. -/
lemma measurePreserving_withDensity {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    {μ : Measure α} {ν : Measure γ} {q : α → γ} (hq : MeasurePreserving q μ ν)
    {w : γ → ℝ≥0∞} (hw : Measurable w) :
    MeasurePreserving q (μ.withDensity (fun x => w (q x))) (ν.withDensity w) := by
  refine ⟨hq.measurable, ?_⟩
  ext S hS
  rw [Measure.map_apply hq.measurable hS, withDensity_apply _ (hS.preimage hq.measurable),
    withDensity_apply _ hS]
  exact hq.setLIntegral_comp_preimage hS hw

lemma quotient_cube (N : ℕ) (c : Gradient N) :
    MeasurePreserving (configurationQuotient N) (volume.restrict (cube c 1)) (referenceMeasure N) := by
  have hh := EuclideanCubeWeight.quotient_unit_cube N c
  simpa only [EuclideanCubeWeight.law, cube_volume c zero_le_one, one_pow,
    ENNReal.ofReal_one, inv_one, one_smul] using hh

lemma quotient_weighted_cube (N : ℕ) (a : ℝ) (c : Gradient N) :
    MeasurePreserving (configurationQuotient N)
      ((weightedMeasure (EuclideanCubeWeight.weight N a)).restrict (cube c 1)) (raw N a) := by
  have hh := measurePreserving_withDensity (quotient_cube N c)
    (measurable_torusPairWeight N a).ennreal_ofReal
  simpa only [weightedMeasure, restrict_withDensity (measurableSet_cube c 1),
    EuclideanCubeWeight.weight, raw] using hh

lemma integral_quotient_cube (N : ℕ) (c : Gradient N) {F : Configuration N → ℝ}
    (hF : Measurable F) :
    (∫ X in cube c 1, F (configurationQuotient N X)) = ∫ X, F X ∂referenceMeasure N := by
  have hh := quotient_cube N c
  rw [← hh.map_eq]
  exact (integral_map hh.aemeasurable hF.aestronglyMeasurable).symm

lemma integral_quotient_weighted_cube (N : ℕ) (a : ℝ) (c : Gradient N)
    {F : Configuration N → ℝ} (hF : Measurable F) :
    (∫ X in cube c 1, F (configurationQuotient N X)
      ∂weightedMeasure (EuclideanCubeWeight.weight N a)) = ∫ X, F X ∂raw N a := by
  have hh := quotient_weighted_cube N a c
  rw [← hh.map_eq]
  exact (integral_map hh.aemeasurable hF.aestronglyMeasurable).symm

end PeriodicAttractiveLogGas.FixedWeightProbability
