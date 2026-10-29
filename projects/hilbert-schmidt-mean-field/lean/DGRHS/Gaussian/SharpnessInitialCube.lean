import DGRHS.Gaussian.SharpnessCubes
import DGRHS.Gaussian.SharpnessRieszSpatial

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma sharpness_cube_distance_le [Nonempty ι] (z : ι → ℝ) {r : ℝ} (hr : 0 ≤ r)
    {x y : EuclideanSpace ℝ ι} (hx : x ∈ sharpnessCenteredCube z r)
    (hy : y ∈ sharpnessCenteredCube z r) : ‖x-y‖ ≤ 2 * Fintype.card ι * r := by
  change (∀ i, z i-r ≤ x i) ∧ (∀ i, x i ≤ z i+r) at hx
  change (∀ i, z i-r ≤ y i) ∧ (∀ i, y i ≤ z i+r) at hy
  have hsq : ‖x-y‖ ^ 2 ≤ (Fintype.card ι : ℝ) * (2*r)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _ : ι, (2*r)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have habs : |x i-y i| ≤ 2*r := abs_le.mpr ⟨by linarith [(hx.1 i), (hy.2 i)],
          by linarith [(hx.2 i), (hy.1 i)]⟩
        simpa only [PiLp.sub_apply, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = _ := by simp
  have hd : (1 : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
  have hdd : (Fintype.card ι : ℝ) ≤ (Fintype.card ι : ℝ)^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hdd (sq_nonneg (2*r))
  have hp : 0 ≤ 2 * (Fintype.card ι : ℝ) * r := by positivity
  nlinarith [norm_nonneg (x-y)]

/-- Actual source Q0 data are constructed together: density arbitrarily close
to one, mass at most one half, and the SAME centered physical local comparison. -/
theorem sharpness_exists_initial_cube (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρm : Measurable ρ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∃ z : ι → ℝ, ∃ r : ℝ, 0 < r ∧
      ENNReal.ofReal (1-ε) <
        volume ({w : ι → ℝ | a ≤ ρ (WithLp.toLp 2 w)} ∩ Metric.closedBall z r) /
          volume (Metric.closedBall z r) ∧
      gaussianRieszDensityMeasure ρ (sharpnessCenteredCube z r) ≤ ENNReal.ofReal (1/2 : ℝ) ∧
      ∀ x y : EuclideanSpace ℝ ι, x ∈ sharpnessCenteredCube z r →
        y ∈ sharpnessCenteredCube z r → x ≠ y →
        gaussianRieszPhysicalPair s (x,y)/2 ≤
          hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s) (x,y) := by
  have hc : 0 < Fintype.card ι := by
    exact_mod_cast (show (0 : ℝ) < Fintype.card ι by linarith)
  have : Nonempty ι := Fintype.card_pos_iff.mp hc
  obtain ⟨R, hR, hpos⟩ := sharpness_exists_riesz_positive_radius s hs ha ρ M hM hρ
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hc
  obtain ⟨a, hap, z, r, hr, hrR, hden, hmass⟩ :=
    sharpness_exists_small_density_cube ρ hρm M hM hρ ε (R/(2*Fintype.card ι)) hε (by positivity)
  refine ⟨a, hap, z, r, hr, hden, hmass, ?_⟩
  intro x y hx hy hxy
  apply hpos x y hxy
  have hb := (lt_div_iff₀ (by positivity : 0 < (2 : ℝ)*Fintype.card ι)).mp hrR
  have hdist := sharpness_cube_distance_le z hr.le hx hy
  nlinarith

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_cube_distance_le
#print axioms DGRHS.Gaussian.sharpness_exists_initial_cube
#check @DGRHS.Gaussian.sharpness_exists_initial_cube
