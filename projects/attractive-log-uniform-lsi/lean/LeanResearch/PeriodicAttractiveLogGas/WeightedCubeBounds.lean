import LeanResearch.PeriodicAttractiveLogGas.EuclideanCubeWeight
import Mathlib.MeasureTheory.Measure.WithDensity

/-! The precise cube-weight assumptions used in the weighted estimates.
The pointwise A1 bound holds off one fixed Lebesgue-null set. The lower
bound one is a separate normalization of the actual distance product,
not a definition of the general Muckenhoupt class. All assumptions are
instantiated below from the proved periodic fixed-particle estimates. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal BigOperators Topology
namespace PeriodicAttractiveLogGas.WeightedCubeBounds
open PhysicalCubes

variable {ι : Type*} [Fintype ι]

structure Bounds (w : EuclideanSpace ℝ ι → ℝ) (A : ℝ) (Z : Set (EuclideanSpace ℝ ι)) : Prop where
  measurable : Measurable w
  nonneg : ∀ x, 0 ≤ w x
  locally_integrable : LocallyIntegrable w volume
  lower : ∀ᵐ x ∂volume, 1 ≤ w x
  constant_ge_one : 1 ≤ A
  exceptional_null : volume Z = 0
  cube_bound : ∀ c : EuclideanSpace ℝ ι, ∀ ℓ : ℝ, 0 < ℓ →
    ∀ y ∈ cube c ℓ, y ∉ Z →
      (∫ x in cube c ℓ, w x) ≤ A * ℓ ^ Fintype.card ι * w y

def weightedMeasure (w : EuclideanSpace ℝ ι → ℝ) : Measure (EuclideanSpace ℝ ι) :=
  volume.withDensity (fun x => ENNReal.ofReal (w x))

variable {w : EuclideanSpace ℝ ι → ℝ} {A : ℝ} {Z : Set (EuclideanSpace ℝ ι)}

lemma Bounds.integrableOn_cube (h : Bounds w A Z) (c : EuclideanSpace ℝ ι) (ℓ : ℝ) :
    IntegrableOn w (cube c ℓ) volume :=
  h.locally_integrable.integrableOn_isCompact (isCompact_cube c ℓ)

lemma Bounds.integrableOn_closedBall (h : Bounds w A Z) (c : EuclideanSpace ℝ ι) (r : ℝ) :
    IntegrableOn w (closedBall c r) volume :=
  h.locally_integrable.integrableOn_isCompact (isCompact_closedBall c r)

lemma weightedMeasure_absolutelyContinuous (w : EuclideanSpace ℝ ι → ℝ) :
    weightedMeasure w ≪ volume := withDensity_absolutelyContinuous _ _

lemma Bounds.ae_weight_pos (h : Bounds w A Z) : ∀ᵐ x ∂volume, 0 < w x :=
  h.lower.mono fun x hx => zero_lt_one.trans_le hx

lemma Bounds.ae_density_ne_zero (h : Bounds w A Z) :
    ∀ᵐ x ∂volume, ENNReal.ofReal (w x) ≠ 0 :=
  h.ae_weight_pos.mono fun x hx => (ENNReal.ofReal_pos.mpr hx).ne'

lemma Bounds.volume_absolutelyContinuous (h : Bounds w A Z) : volume ≪ weightedMeasure w :=
  withDensity_absolutelyContinuous' h.measurable.ennreal_ofReal.aemeasurable h.ae_density_ne_zero

lemma weightedMeasure_sFinite (w : EuclideanSpace ℝ ι → ℝ) : SFinite (weightedMeasure w) :=
  sFinite_of_absolutelyContinuous (weightedMeasure_absolutelyContinuous w)

lemma Bounds.measure_cube (h : Bounds w A Z) (c : EuclideanSpace ℝ ι) (ℓ : ℝ) :
    weightedMeasure w (cube c ℓ) = ENNReal.ofReal (∫ x in cube c ℓ, w x) := by
  rw [weightedMeasure, withDensity_apply _ (measurableSet_cube c ℓ)]
  exact (ofReal_integral_eq_lintegral_ofReal (h.integrableOn_cube c ℓ)
    (Eventually.of_forall h.nonneg)).symm

lemma Bounds.measure_closedBall (h : Bounds w A Z) (c : EuclideanSpace ℝ ι) (r : ℝ) :
    weightedMeasure w (closedBall c r) = ENNReal.ofReal (∫ x in closedBall c r, w x) := by
  rw [weightedMeasure, withDensity_apply _ measurableSet_closedBall]
  exact (ofReal_integral_eq_lintegral_ofReal (h.integrableOn_closedBall c r)
    (Eventually.of_forall h.nonneg)).symm

lemma Bounds.measure_cube_lt_top (h : Bounds w A Z) (c : EuclideanSpace ℝ ι) (ℓ : ℝ) :
    weightedMeasure w (cube c ℓ) < ∞ := by rw [h.measure_cube]; exact ENNReal.ofReal_lt_top

lemma Bounds.measure_closedBall_lt_top (h : Bounds w A Z) (c : EuclideanSpace ℝ ι) (r : ℝ) :
    weightedMeasure w (closedBall c r) < ∞ := by rw [h.measure_closedBall]; exact ENNReal.ofReal_lt_top

lemma Bounds.measure_cube_le (h : Bounds w A Z) (c : EuclideanSpace ℝ ι) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {y : EuclideanSpace ℝ ι} (hy : y ∈ cube c ℓ) (hyZ : y ∉ Z) :
    weightedMeasure w (cube c ℓ) ≤ ENNReal.ofReal (A * ℓ ^ Fintype.card ι * w y) := by
  rw [h.measure_cube]
  exact ENNReal.ofReal_le_ofReal (h.cube_bound c ℓ hℓ y hy hyZ)

lemma closedBall_subset_cube (c : EuclideanSpace ℝ ι) (r : ℝ) :
    closedBall c r ⊆ cube c (2 * r) := by
  intro y hy
  apply (mem_cube c y (2 * r)).mpr
  intro j
  have hj : |y j - c j| ≤ ‖y - c‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (y - c) j
  have hh : ‖y - c‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hy
  linarith

/-- Ball estimates are consequences of the actual cube A1 estimate,
with no change in the Euclidean metric used for distance and gradient. -/
lemma Bounds.measure_closedBall_le (h : Bounds w A Z) (c : EuclideanSpace ℝ ι) {r : ℝ} (hr : 0 < r)
    {y : EuclideanSpace ℝ ι} (hy : y ∈ closedBall c r) (hyZ : y ∉ Z) :
    weightedMeasure w (closedBall c r) ≤ ENNReal.ofReal (A * (2 * r) ^ Fintype.card ι * w y) :=
  (measure_mono (closedBall_subset_cube c r)).trans
    (h.measure_cube_le c (by positivity) (closedBall_subset_cube c r hy) hyZ)

lemma Bounds.reference_lintegral_le (h : Bounds w A Z) (f : EuclideanSpace ℝ ι → ℝ≥0∞)
    (hf : Measurable f) : (∫⁻ x, f x) ≤ ∫⁻ x, f x ∂weightedMeasure w := by
  rw [weightedMeasure, lintegral_withDensity_eq_lintegral_mul _ h.measurable.ennreal_ofReal hf]
  apply lintegral_mono_ae
  filter_upwards [h.lower] with x hx
  have he : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (w x) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hx
  change f x ≤ ENNReal.ofReal (w x) * f x
  simpa only [one_mul] using mul_le_mul_of_nonneg_right he zero_le

/-- The original periodic distance product satisfies every hypothesis
used in the weighted argument, uniformly in the closed subcritical interval. -/
theorem periodic_bounds {N : ℕ} (hN : 2 ≤ N) {β₀ a : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ha : 0 ≤ a)
    (haa : a ≤ FixedWeightConstants.exponent N β₀) :
    Bounds (EuclideanCubeWeight.weight N a) (FixedParticleAOne.constant N β₀)
      (EuclideanCubeWeight.collisionSet N) := by
  refine ⟨EuclideanCubeWeight.measurable_weight N a, EuclideanCubeWeight.weight_nonneg N a,
    EuclideanCubeWeight.locallyIntegrable_weight hN hsub ha haa,
    EuclideanCubeWeight.ae_one_le_weight N ha, FixedParticleAOne.constant_ge_one N β₀,
    EuclideanCubeWeight.collisionSet_null N, ?_⟩
  intro c ℓ hℓ y hy hyZ
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] using
    EuclideanCubeWeight.cube_integral_le hN hβ₀ hsub ha haa hℓ c y hy hyZ

end PeriodicAttractiveLogGas.WeightedCubeBounds
