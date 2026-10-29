import DGRHS.Gaussian.SharpnessRieszL1

/-! Source quantitativeDyadicCompression: actual Schur rows throughout 0<s<d.
No Hilbert--Schmidt assumption is imposed on the singular physical kernel. -/
noncomputable section
open MeasureTheory
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma sharpness_riesz_pair_symmetric (s : ℝ) (x y : EuclideanSpace ℝ ι) :
    gaussianRieszPhysicalPair s (x,y) = gaussianRieszPhysicalPair s (y,x) := by
  unfold gaussianRieszPhysicalPair
  rw [norm_sub_rev]

/-- The actual pair mean is finite, nonnegative, and bounded by the same
proper physical potential bound. -/
theorem sharpness_riesz_pair_mean_bound (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    0 ≤ (∫ p, gaussianRieszPhysicalPair s p ∂(gaussianRieszDensityMeasure ρ).prod
      (gaussianRieszDensityMeasure ρ)) ∧
    (∫ p, gaussianRieszPhysicalPair s p ∂(gaussianRieszDensityMeasure ρ).prod
      (gaussianRieszDensityMeasure ρ)) ≤ gaussianRieszPhysicalPotentialConstant s M ι := by
  let μ := gaussianRieszDensityMeasure ρ
  have hi := sharpness_riesz_pair_integrable s hs ha ρ M hM hρ
  constructor
  · apply integral_nonneg
    intro p
    unfold gaussianRieszPhysicalPair
    positivity
  · rw [integral_prod _ hi]
    calc
      _ ≤ ∫ _ : EuclideanSpace ℝ ι, gaussianRieszPhysicalPotentialConstant s M ι ∂μ :=
        integral_mono_ae hi.integral_prod_left (integrable_const _)
          (Filter.Eventually.of_forall fun x =>
            (sharpness_riesz_potential_bound s hs ha ρ M hM hρ x).2.2)
      _ = _ := by simp

/-- Every centered row is proper and its absolute integral is bounded,
even when the actual full kernel has divergent square integral. -/
theorem sharpness_centered_riesz_row_bound (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (x : EuclideanSpace ℝ ι) :
    Integrable (fun y => hoeffdingCentered (gaussianRieszDensityMeasure ρ)
      (gaussianRieszPhysicalPair s) (x,y)) (gaussianRieszDensityMeasure ρ) ∧
    (∫ y, |hoeffdingCentered (gaussianRieszDensityMeasure ρ)
      (gaussianRieszPhysicalPair s) (x,y)| ∂gaussianRieszDensityMeasure ρ) ≤
      4 * gaussianRieszPhysicalPotentialConstant s M ι := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (a,b)
  let F := DGRHS.potential μ W
  let m := ∫ p, gaussianRieszPhysicalPair s p ∂μ.prod μ
  have hi := sharpness_riesz_pair_integrable s hs ha ρ M hM hρ
  have hx := sharpness_riesz_potential_bound s hs ha ρ M hM hρ x
  have hm := sharpness_riesz_pair_mean_bound s hs ha ρ M hM hρ
  have hF := DGRHS.integrable_potential μ W hi
  have hsym : ∀ a b, W a b = W b a := sharpness_riesz_pair_symmetric s
  have he : (fun y => hoeffdingCentered μ (gaussianRieszPhysicalPair s) (x,y)) =
      (fun y => W x y - F x - F y + m) := by
    funext y
    change W x y - F x - DGRHS.secondPotential μ W y + m = _
    rw [DGRHS.secondPotential_eq_potential μ W hsym]
  have hrow : Integrable (fun y => hoeffdingCentered μ (gaussianRieszPhysicalPair s) (x,y)) μ := by
    rw [he]
    exact ((hx.1.sub (integrable_const _)).sub hF).add (integrable_const _)
  refine ⟨hrow, ?_⟩
  have hmajor : Integrable (fun y => W x y + F x + F y + m) μ :=
    ((hx.1.add (integrable_const _)).add hF).add (integrable_const _)
  calc
    _ ≤ ∫ y, W x y + F x + F y + m ∂μ := by
      apply integral_mono_ae hrow.abs hmajor
      apply Filter.Eventually.of_forall
      intro y
      have hy := sharpness_riesz_potential_bound s hs ha ρ M hM hρ y
      have hw : 0 ≤ W x y := by unfold W gaussianRieszPhysicalPair; positivity
      change |hoeffdingCentered μ (gaussianRieszPhysicalPair s) (x,y)| ≤ _
      rw [congrFun he y]
      apply abs_le.mpr
      constructor <;> dsimp [F, DGRHS.potential, m, μ, W] at * <;> linarith [hx.2.1, hy.2.1, hm.1]
    _ = 2 * F x + 2 * m := by
      rw [integral_add (f := fun y => W x y + F x + F y) (g := fun _ => m)
          ((hx.1.add (integrable_const _)).add hF) (integrable_const _),
        integral_add (f := fun y => W x y + F x) (g := F)
          (hx.1.add (integrable_const _)) hF,
        integral_add (f := fun y => W x y) (g := fun _ => F x) hx.1 (integrable_const _)]
      have hFm : (∫ y, F y ∂μ) = m := (integral_prod _ hi).symm
      simp only [integral_const, probReal_univ, one_smul]
      change F x + F x + (∫ y, F y ∂μ) + m = _
      rw [hFm]
      ring
    _ ≤ _ := by dsimp [F, DGRHS.potential, m, μ, W]; linarith [hx.2.2, hm.2]

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_riesz_pair_mean_bound
#print axioms DGRHS.Gaussian.sharpness_centered_riesz_row_bound
#check @DGRHS.Gaussian.sharpness_centered_riesz_row_bound
