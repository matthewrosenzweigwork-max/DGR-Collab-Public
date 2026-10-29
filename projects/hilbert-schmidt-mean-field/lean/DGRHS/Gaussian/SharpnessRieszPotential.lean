import DGRHS.Gaussian.GaussianRieszPhysicalPotential

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

/-- The SAME genuine Riesz potential is proper and bounded at EVERY point
throughout0<s<d, including the non-Hilbert--Schmidt sharpness range. The actual
short+long split uses only L1 integrability, never an L2-kernel assumption. -/
theorem sharpness_riesz_potential_bound (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (x : EuclideanSpace ℝ ι) :
    Integrable (fun y => gaussianRieszPhysicalPair s (x,y)) (gaussianRieszDensityMeasure ρ) ∧
    0 ≤ (∫ y,gaussianRieszPhysicalPair s (x,y) ∂gaussianRieszDensityMeasure ρ) ∧
    (∫ y,gaussianRieszPhysicalPair s (x,y) ∂gaussianRieszDensityMeasure ρ) ≤
      gaussianRieszPhysicalPotentialConstant s M ι := by
  let μ := gaussianRieszDensityMeasure ρ
  have hc : 0 < Fintype.card ι := by
    exact_mod_cast (show (0 : ℝ) < (Fintype.card ι : ℝ) by linarith)
  haveI : Nonempty ι := Fintype.card_pos_iff.mp hc
  haveI : NullSingletonClass μ := by unfold μ gaussianRieszDensityMeasure; infer_instance
  have he : (fun y => gaussianRieszPhysicalPair s (x,y)) =ᵐ[μ]
      (fun y => gaussianRieszEuclideanShortRange s 1 (x-y)+gaussianRieszEuclideanTruncation s 1 (x-y)) := by
    filter_upwards [μ.ae_ne x] with y hy
    exact gaussianRieszEuclidean_full_short_long_split s 1 hs (by norm_num) _ (sub_ne_zero.mpr hy.symm)
  have hiS := integrable_gaussianRieszShortRange_convolution s 1 (by norm_num) ha ρ M hρ x
  have hiL := integrable_gaussianRieszTruncation_convolution s 1 hs (by norm_num) μ x
  refine ⟨(hiS.add hiL).congr he.symm, integral_nonneg (fun y => ?_), ?_⟩
  · unfold gaussianRieszPhysicalPair
    positivity
  · rw [integral_congr_ae he, integral_add hiS hiL]
    have hS := gaussianRieszShortRange_convolution_le s 1 hs (by norm_num) ha ρ M hM hρ x
    have hL : (∫ y,gaussianRieszEuclideanTruncation s 1 (x-y) ∂μ) ≤ gaussianRieszSourceCoefficient s/s := by
      calc
        _ ≤ ∫ _ : EuclideanSpace ℝ ι, gaussianRieszSourceCoefficient s/s ∂μ :=
          integral_mono_ae hiL (integrable_const _) (Filter.Eventually.of_forall (fun y =>
            (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, Real.one_rpow, mul_one] using
              gaussianRieszEuclideanTruncation_le_diagonal s 1 hs (by norm_num) (x-y))))
        _ = _ := by simp
    simp only [Real.one_rpow, mul_one] at hS
    unfold gaussianRieszPhysicalPotentialConstant
    convert add_le_add hS hL using 1
    ring

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_riesz_potential_bound
#check @DGRHS.Gaussian.sharpness_riesz_potential_bound
