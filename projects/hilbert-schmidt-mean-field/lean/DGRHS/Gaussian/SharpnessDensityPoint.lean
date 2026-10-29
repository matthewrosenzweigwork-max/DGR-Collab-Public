import DGRHS.Gaussian.GaussianShortRangeSourceL2
import Mathlib.MeasureTheory.Covering.DensityTheorem

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

/-- A genuine probability density has a positive-measure positive density level.
No lower mass or density-point conclusion is a premise. -/
theorem sharpness_exists_positive_density_level (ρ : EuclideanSpace ℝ ι → ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    ∃ a : ℝ, 0 < a ∧ 0 < volume {x | a ≤ ρ x} := by
  by_contra h
  simp only [not_exists, not_and, not_lt] at h
  have hz (n : ℕ) : volume {x : EuclideanSpace ℝ ι | 1 / (n + 1 : ℝ) ≤ ρ x} = 0 :=
    le_antisymm (h _ (by positivity)) zero_le
  have hae (n : ℕ) : ∀ᵐ x ∂volume, ρ x < 1 / (n + 1 : ℝ) := by
    rw [ae_iff]
    simpa only [not_lt] using hz n
  have hnonpos : ∀ᵐ x ∂volume, ρ x ≤ 0 := by
    filter_upwards [ae_all_iff.mpr hae] with x hx
    by_contra hn
    obtain ⟨n, hn'⟩ := exists_nat_one_div_lt (lt_of_not_ge hn)
    linarith [hx n]
  have hf : (fun x => ENNReal.ofReal (ρ x)) =ᵐ[volume] fun _ => 0 := by
    filter_upwards [hnonpos] with x hx
    exact ENNReal.ofReal_eq_zero.mpr hx
  have hzero : gaussianRieszDensityMeasure ρ = 0 := by
    unfold gaussianRieszDensityMeasure
    rw [withDensity_congr_ae hf]
    simp
  have hu : gaussianRieszDensityMeasure ρ univ = 1 := measure_univ
  rw [hzero] at hu
  simp at hu

/-- Native Lebesgue density supplies an actual point of the positive density level.
Measurable rho is a representative condition, not a favorable spatial-mass premise. -/
theorem sharpness_exists_density_point (ρ : EuclideanSpace ℝ ι → ℝ)
    (hρ : Measurable ρ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    ∃ a : ℝ, 0 < a ∧ ∃ x₀ : EuclideanSpace ℝ ι, a ≤ ρ x₀ ∧
      ∀ {κ : Type*} {l : Filter κ} (w : κ → EuclideanSpace ℝ ι) (r : κ → ℝ),
      Tendsto r l (𝓝[>] (0 : ℝ)) →
      (∀ᶠ j in l, x₀ ∈ Metric.closedBall (w j) (1 * r j)) →
      Tendsto (fun j => volume ({x | a ≤ ρ x} ∩ Metric.closedBall (w j) (r j)) /
        volume (Metric.closedBall (w j) (r j))) l (𝓝 (1 : ℝ≥0∞)) := by
  obtain ⟨a, ha, hpos⟩ := sharpness_exists_positive_density_level ρ
  let E := {x | a ≤ ρ x}
  have hE : MeasurableSet E := measurableSet_le measurable_const hρ
  have hne : volume.restrict E ≠ 0 := by
    intro hz
    have hu := congrArg (fun ν : Measure (EuclideanSpace ℝ ι) => ν univ) hz
    have he : volume E = 0 := by simpa using hu
    exact hpos.ne' he
  haveI : NeZero (volume.restrict E) := ⟨hne⟩
  obtain ⟨x₀,hx,hden⟩ := ((ae_restrict_mem hE).and
    (IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div volume E 1)).exists
  exact ⟨a, ha, x₀, hx, hden⟩

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_exists_positive_density_level
#print axioms DGRHS.Gaussian.sharpness_exists_density_point
#check @DGRHS.Gaussian.sharpness_exists_density_point
