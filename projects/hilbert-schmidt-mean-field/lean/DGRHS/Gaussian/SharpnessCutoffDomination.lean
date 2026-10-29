import DGRHS.Gaussian.SharpnessRieszRows
import DGRHS.Gaussian.SharpnessRieszConvergence

noncomputable section
open MeasureTheory
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma sharpness_cutoff_potential_bound (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (x : EuclideanSpace ℝ ι) :
    0 ≤ (∫ y, gaussianRieszTruncatedPair s η (x,y) ∂gaussianRieszDensityMeasure ρ) ∧
    (∫ y, gaussianRieszTruncatedPair s η (x,y) ∂gaussianRieszDensityMeasure ρ) ≤
      gaussianRieszPhysicalPotentialConstant s M ι := by
  let μ := gaussianRieszDensityMeasure ρ
  have hc : 0 < Fintype.card ι := by
    exact_mod_cast (show (0 : ℝ) < Fintype.card ι by linarith)
  have : Nonempty ι := Fintype.card_pos_iff.mp hc
  have : NullSingletonClass μ := by unfold μ gaussianRieszDensityMeasure; infer_instance
  have hx := sharpness_riesz_potential_bound s hs ha ρ M hM hρ x
  have hi := integrable_gaussianRieszTruncation_convolution s η hs hη μ x
  have hb : ∀ᵐ y ∂μ, 0 ≤ gaussianRieszTruncatedPair s η (x,y) ∧
      gaussianRieszTruncatedPair s η (x,y) ≤ gaussianRieszPhysicalPair s (x,y) := by
    filter_upwards [μ.ae_ne x] with y hy
    exact ⟨(gaussianRieszEuclidean_truncation_bounds s η hs hη (x-y)
      (sub_ne_zero.mpr hy.symm)).1,
      (gaussianRieszEuclidean_truncation_bounds s η hs hη (x-y)
      (sub_ne_zero.mpr hy.symm)).2.1⟩
  exact ⟨integral_nonneg_of_ae (hb.mono fun _ h => h.1),
    (integral_mono_ae hi hx.1 (hb.mono fun _ h => h.2)).trans hx.2.2⟩

lemma sharpness_cutoff_pair_mean_bound (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    0 ≤ (∫ p, gaussianRieszTruncatedPair s η p ∂(gaussianRieszDensityMeasure ρ).prod
      (gaussianRieszDensityMeasure ρ)) ∧
    (∫ p, gaussianRieszTruncatedPair s η p ∂(gaussianRieszDensityMeasure ρ).prod
      (gaussianRieszDensityMeasure ρ)) ≤ gaussianRieszPhysicalPotentialConstant s M ι := by
  let μ := gaussianRieszDensityMeasure ρ
  have hi := (memLp_gaussianRieszTruncatedPair s η hs hη μ).integrable (by norm_num)
  rw [integral_prod _ hi]
  constructor
  · exact integral_nonneg (fun x => (sharpness_cutoff_potential_bound s η hs hη ha ρ M hM hρ x).1)
  · calc
      _ ≤ ∫ _ : EuclideanSpace ℝ ι, gaussianRieszPhysicalPotentialConstant s M ι ∂μ :=
        integral_mono_ae hi.integral_prod_left (integrable_const _)
          (Filter.Eventually.of_forall fun x =>
            (sharpness_cutoff_potential_bound s η hs hη ha ρ M hM hρ x).2)
      _ = _ := by simp

/-- An actual cutoff-independent proper L1 dominator for the centered Gaussian
approximations. This is derived from raw bounds and every proper section. -/
theorem sharpness_centered_cutoff_domination (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ∀ᵐ p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ),
      ‖hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszTruncatedPair s η) p‖ ≤
      gaussianRieszPhysicalPair s p + 3 * gaussianRieszPhysicalPotentialConstant s M ι := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι => gaussianRieszTruncatedPair s η (a,b)
  have hsym : ∀ a b, W a b = W b a := by
    intro a b
    unfold W gaussianRieszTruncatedPair gaussianRieszEuclideanTruncation
    rw [norm_sub_rev]
  have hm := sharpness_cutoff_pair_mean_bound s η hs hη ha ρ M hM hρ
  have hc : 0 < Fintype.card ι := by
    exact_mod_cast (show (0 : ℝ) < Fintype.card ι by linarith)
  have : Nonempty ι := Fintype.card_pos_iff.mp hc
  filter_upwards [ae_gaussianRieszDensity_pair_ne ρ] with p hp
  have hx := sharpness_cutoff_potential_bound s η hs hη ha ρ M hM hρ p.1
  have hy := sharpness_cutoff_potential_bound s η hs hη ha ρ M hM hρ p.2
  have hb := gaussianRieszEuclidean_truncation_bounds s η hs hη (p.1-p.2) (sub_ne_zero.mpr hp)
  have hbraw : W p.1 p.2 ≤ gaussianRieszPhysicalPair s p := hb.2.1
  have hcut : 0 ≤ W p.1 p.2 := hb.1
  have hw : 0 ≤ gaussianRieszPhysicalPair s p := by unfold gaussianRieszPhysicalPair; positivity
  have hB := hm.1.trans hm.2
  change |W p.1 p.2 - DGRHS.potential μ W p.1 - DGRHS.secondPotential μ W p.2 +
    (∫ q, gaussianRieszTruncatedPair s η q ∂μ.prod μ)| ≤ _
  rw [DGRHS.secondPotential_eq_potential μ W hsym]
  apply abs_le.mpr
  constructor <;> dsimp [DGRHS.potential, W, μ, gaussianRieszTruncatedPair] at * <;>
    linarith [hx.1, hx.2, hy.1, hy.2, hm.1, hm.2, hcut, hw, hB, hbraw]

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_cutoff_potential_bound
#print axioms DGRHS.Gaussian.sharpness_cutoff_pair_mean_bound
#print axioms DGRHS.Gaussian.sharpness_centered_cutoff_domination
#check @DGRHS.Gaussian.sharpness_centered_cutoff_domination
