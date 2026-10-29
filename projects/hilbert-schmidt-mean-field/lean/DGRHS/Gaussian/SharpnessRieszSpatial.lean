import DGRHS.Gaussian.SharpnessRieszRows
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Genuine local positivity of the SAME physical centered kernel, source
quantitativeDyadicCompression, before choosing any favorable partition. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

/-- A radius is actually constructed from singularity and the proper potential
bound; the favorable local comparison is not a theorem premise. -/
theorem sharpness_exists_riesz_positive_radius (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ∃ r : ℝ, 0 < r ∧ ∀ x y : EuclideanSpace ℝ ι, x ≠ y → ‖x-y‖ ≤ r →
      gaussianRieszPhysicalPair s (x,y) / 2 ≤
        hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s) (x,y) := by
  let B := gaussianRieszPhysicalPotentialConstant s M ι
  have hev : ∀ᶠ r : ℝ in 𝓝[>] 0, 4 * B * s ≤ r ^ (-s) :=
    (tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos hs)).eventually
      (eventually_ge_atTop (4 * B * s))
  have hrpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := Filter.mem_inf_of_right (Set.Subset.refl _)
  obtain ⟨r, hr, hpow⟩ := (hrpos.and hev).exists
  refine ⟨r, hr, ?_⟩
  intro x y hxy hd
  have hnorm : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hp := Real.rpow_le_rpow_of_nonpos hnorm hd (neg_nonpos.mpr hs.le)
  have hW : 4 * B ≤ gaussianRieszPhysicalPair s (x,y) := by
    unfold gaussianRieszPhysicalPair
    exact (le_div_iff₀ hs).2 (hpow.trans hp)
  have hx := sharpness_riesz_potential_bound s hs ha ρ M hM hρ x
  have hy := sharpness_riesz_potential_bound s hs ha ρ M hM hρ y
  have hm := sharpness_riesz_pair_mean_bound s hs ha ρ M hM hρ
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (a,b)
  have hsym : ∀ a b, W a b = W b a := sharpness_riesz_pair_symmetric s
  change W x y / 2 ≤ W x y - DGRHS.potential μ W x - DGRHS.secondPotential μ W y + _
  rw [DGRHS.secondPotential_eq_potential μ W hsym]
  dsimp [DGRHS.potential, W, μ, B] at *
  linarith [hx.2.2, hy.2.2, hm.1]

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_exists_riesz_positive_radius
#check @DGRHS.Gaussian.sharpness_exists_riesz_positive_radius
