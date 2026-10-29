import DGRHS.Gaussian.SharpnessDensityPoint
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Coordinate cubes with actual Euclidean volume; native density points are
used in the coordinate sup norm, whose balls are genuine axis-aligned cubes. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def sharpnessClosedCube (a b : ι → ℝ) : Set (EuclideanSpace ℝ ι) :=
  WithLp.ofLp ⁻¹' Icc a b

lemma measurableSet_sharpnessClosedCube (a b : ι → ℝ) :
    MeasurableSet (sharpnessClosedCube a b) :=
  measurableSet_Icc.preimage (PiLp.volume_preserving_ofLp ι).measurable

lemma volume_sharpnessClosedCube (a b : ι → ℝ) :
    volume (sharpnessClosedCube a b) = ∏ i, ENNReal.ofReal (b i - a i) := by
  rw [sharpnessClosedCube, (PiLp.volume_preserving_ofLp ι).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]

def sharpnessCenteredCube (z : ι → ℝ) (r : ℝ) : Set (EuclideanSpace ℝ ι) :=
  sharpnessClosedCube (fun i => z i-r) (fun i => z i+r)

lemma volume_sharpnessCenteredCube (z : ι → ℝ) (r : ℝ) :
    volume (sharpnessCenteredCube z r) = ENNReal.ofReal (2*r) ^ Fintype.card ι := by
  rw [sharpnessCenteredCube, volume_sharpnessClosedCube]
  have he : (fun i => ENNReal.ofReal ((z i+r)-(z i-r))) =
      (fun _ : ι => ENNReal.ofReal (2*r)) := by
    funext i
    congr 1
    ring
  rw [he]
  simp

lemma sharpnessCenteredCube_eq_coordinate_ball (z : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    sharpnessCenteredCube z r = WithLp.ofLp ⁻¹' Metric.closedBall z r := by
  ext x
  simp only [sharpnessCenteredCube, sharpnessClosedCube, mem_preimage, mem_Icc,
    Pi.le_def, Metric.mem_closedBall, dist_pi_le_iff hr, Real.dist_eq, abs_le]
  constructor
  · rintro ⟨hl, hu⟩ i
    constructor <;> linarith [hl i, hu i]
  · intro h
    constructor <;> intro i <;> linarith [(h i).1, (h i).2]

lemma sharpness_cube_mass_le (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ)
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (z : ι → ℝ) (r : ℝ) :
    gaussianRieszDensityMeasure ρ (sharpnessCenteredCube z r) ≤
      ENNReal.ofReal M * ENNReal.ofReal (2*r) ^ Fintype.card ι := by
  have h := gaussianRieszDensityMeasure_le ρ M hρ (sharpnessCenteredCube z r)
  simpa only [Measure.smul_apply, smul_eq_mul, volume_sharpnessCenteredCube] using h

/-- The same genuine positive density level has an actual coordinate density
point. This removes any assumption of favorable dyadic mass from the construction. -/
theorem sharpness_exists_coordinate_density_point (ρ : EuclideanSpace ℝ ι → ℝ)
    (hρ : Measurable ρ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    ∃ a : ℝ, 0 < a ∧ ∃ z₀ : ι → ℝ, a ≤ ρ (WithLp.toLp 2 z₀) ∧
      ∀ {κ : Type*} {l : Filter κ} (w : κ → (ι → ℝ)) (r : κ → ℝ),
      Tendsto r l (𝓝[>] (0 : ℝ)) →
      (∀ᶠ j in l, z₀ ∈ Metric.closedBall (w j) (1 * r j)) →
      Tendsto (fun j => volume ({z : ι → ℝ | a ≤ ρ (WithLp.toLp 2 z)} ∩
          Metric.closedBall (w j) (r j)) / volume (Metric.closedBall (w j) (r j)))
        l (𝓝 (1 : ℝ≥0∞)) := by
  obtain ⟨a, ha, hpos⟩ := sharpness_exists_positive_density_level ρ
  let E := {x : EuclideanSpace ℝ ι | a ≤ ρ x}
  let S := {z : ι → ℝ | a ≤ ρ (WithLp.toLp 2 z)}
  have hE : MeasurableSet E := measurableSet_le measurable_const hρ
  have hS : MeasurableSet S := hE.preimage (PiLp.volume_preserving_toLp ι).measurable
  have hvol : volume S = volume E :=
    (PiLp.volume_preserving_toLp ι).measure_preimage hE.nullMeasurableSet
  have hne : volume.restrict S ≠ 0 := by
    intro hz
    have hu := congrArg (fun ν : Measure (ι → ℝ) => ν univ) hz
    have he : volume S = 0 := by simpa using hu
    exact hpos.ne' (hvol.symm.trans he)
  have : NeZero (volume.restrict S) := ⟨hne⟩
  obtain ⟨z₀,hz,hden⟩ := ((ae_restrict_mem hS).and
    (IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div volume S 1)).exists
  exact ⟨a, ha, z₀, hz, hden⟩

/-- An actual high-density, small-mass cube, at any prescribed positive upper
scale. Only the physical probability density and native density theorem enter. -/
theorem sharpness_exists_small_density_cube [Nonempty ι]
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρm : Measurable ρ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (ε R : ℝ) (hε : 0 < ε) (hR : 0 < R) :
    ∃ a : ℝ, 0 < a ∧ ∃ z : ι → ℝ, ∃ r : ℝ, 0 < r ∧ r < R ∧
      ENNReal.ofReal (1-ε) <
        volume ({w : ι → ℝ | a ≤ ρ (WithLp.toLp 2 w)} ∩ Metric.closedBall z r) /
          volume (Metric.closedBall z r) ∧
      gaussianRieszDensityMeasure ρ (sharpnessCenteredCube z r) ≤ ENNReal.ofReal (1/2 : ℝ) := by
  obtain ⟨a, ha, z, hz, hden⟩ := sharpness_exists_coordinate_density_point ρ hρm
  have hp : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := Filter.mem_inf_of_right (Set.Subset.refl _)
  have hd := hden (fun _ : ℝ => z) id tendsto_id (by
    filter_upwards [hp] with r hr
    simp [hr.le])
  have htarg : ENNReal.ofReal (1-ε) < (1 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_lt_one]
    linarith
  have hd' := hd.eventually (Ioi_mem_nhds htarg)
  have hc : Continuous (fun r : ℝ => M * (2*r) ^ Fintype.card ι) := by fun_prop
  have ht : Tendsto (fun r : ℝ => M * (2*r) ^ Fintype.card ι) (𝓝[>] 0) (𝓝 0) := by
    have ht' := hc.tendsto 0
    have he : M * (2*(0 : ℝ)) ^ Fintype.card ι = 0 := by simp
    rw [he] at ht'
    exact ht'.mono_left nhdsWithin_le_nhds
  have hb := ht.eventually (Iio_mem_nhds (show (0 : ℝ) < 1/2 by norm_num))
  have hrmax : ∀ᶠ r : ℝ in 𝓝[>] 0, r < R :=
    (eventually_lt_nhds hR).filter_mono inf_le_left
  obtain ⟨r, hr, hrR, hdensity, hbound⟩ := (hp.and (hrmax.and (hd'.and hb))).exists
  refine ⟨a, ha, z, r, hr, hrR, hdensity, ?_⟩
  calc
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal (2*r) ^ Fintype.card ι :=
      sharpness_cube_mass_le ρ M hρ z r
    _ = ENNReal.ofReal (M*(2*r)^Fintype.card ι) := by
      rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul hM]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbound.le

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.volume_sharpnessClosedCube
#print axioms DGRHS.Gaussian.sharpness_exists_coordinate_density_point
#check @DGRHS.Gaussian.sharpness_exists_coordinate_density_point

#print axioms DGRHS.Gaussian.sharpness_cube_mass_le
#print axioms DGRHS.Gaussian.sharpnessCenteredCube_eq_coordinate_ball

#print axioms DGRHS.Gaussian.sharpness_exists_small_density_cube
#check @DGRHS.Gaussian.sharpness_exists_small_density_cube
