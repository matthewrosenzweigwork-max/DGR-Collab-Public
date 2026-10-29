import DGRHS.Gaussian.GaussianLogBandBounds
import DGRHS.Gaussian.GaussianLogBandCanonical

/-! Actual mixed/joint square and SAME integral-operator
bounds of logarithmic bands, instantiated from physical short-range domination. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianLogBandRowControl (δ M : ℝ) (ι : Type*) [Fintype ι] : ℝ :=
  M*((δ^((Fintype.card ι : ℝ)/2)/((Fintype.card ι : ℝ)/2))^2*Real.pi^((Fintype.card ι : ℝ)/2))

lemma gaussianLogBandPair_square (η δ : ℝ)
    (hη : 0 < η) (hηδ : η ≤ δ) (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    Integrable (fun p => gaussianLogBandPair η δ p^2)
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) ∧
    (∫ p, gaussianLogBandPair η δ p^2
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) ≤
      gaussianLogBandRowControl δ M ι := by
  let μ := gaussianRieszDensityMeasure ρ
  have hm := (stronglyMeasurable_gaussianLogBandPair (ι := ι) η δ hη).pow 2
  have hr := fun x => gaussianLogBand_row_sq_bound η δ hη hηδ hd ρ M hM hρ x
  have hi : Integrable (fun p => gaussianLogBandPair η δ p^2) (μ.prod μ) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall (fun x => (hr x).1)
    · apply (integrable_const (gaussianLogBandRowControl δ M ι)).mono'
        hm.norm.integral_prod_right'.aestronglyMeasurable
      apply Filter.Eventually.of_forall
      intro x
      change ‖∫ y, ‖gaussianLogBandPair η δ (x,y)^2‖ ∂μ‖ ≤ _
      simp_rw [Real.norm_of_nonneg (sq_nonneg _)]
      rw [Real.norm_of_nonneg (integral_nonneg (fun y => sq_nonneg _))]
      exact (hr x).2
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ _ : EuclideanSpace ℝ ι, gaussianLogBandRowControl δ M ι ∂μ :=
      integral_mono_ae hi.integral_prod_left (integrable_const _)
        (Filter.Eventually.of_forall (fun x => (hr x).2))
    _ = _ := by simp

lemma memLp_gaussianLogBandPair (η δ : ℝ)
    (hη : 0 < η) (hηδ : η ≤ δ) (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    MemLp (gaussianLogBandPair η δ) 2
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) :=
  (memLp_two_iff_integrable_sq
    (stronglyMeasurable_gaussianLogBandPair η δ hη).aestronglyMeasurable).2
    (gaussianLogBandPair_square η δ hη hηδ hd ρ M hM hρ).1

lemma gaussianLogCenteredBand_square_controls (η δ : ℝ)
    (hη : 0 < η) (hηδ : η ≤ δ) (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    (∀ᵐ x ∂gaussianRieszDensityMeasure ρ,
      (∫ y, hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogBandPair η δ) (x,y)^2
        ∂gaussianRieszDensityMeasure ρ) ≤ 16*gaussianLogBandRowControl δ M ι) ∧
    (∫ p, hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogBandPair η δ) p^2
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) ≤
        16*gaussianLogBandRowControl δ M ι := by
  have hm := stronglyMeasurable_gaussianLogBandPair (ι := ι) η δ hη
  have h2 := memLp_gaussianLogBandPair η δ hη hηδ hd ρ M hM hρ
  constructor
  · exact ae_row_sq_hoeffdingCentered_le _ _ hm h2 _
      (Filter.Eventually.of_forall (fun x =>
        (gaussianLogBand_row_sq_bound η δ hη hηδ hd ρ M hM hρ x).2))
  · exact (integral_sq_hoeffdingCentered_le _ _ hm h2).trans
      (mul_le_mul_of_nonneg_left (gaussianLogBandPair_square η δ hη hηδ hd ρ M hM hρ).2 (by positivity))

lemma memLp_gaussianLogCenteredBand (η δ : ℝ)
    (hη : 0 < η) (hηδ : η ≤ δ) (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    MemLp (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogBandPair η δ)) 2
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) :=
  memLp_hoeffdingCentered _ _ (stronglyMeasurable_gaussianLogBandPair η δ hη)
    (memLp_gaussianLogBandPair η δ hη hηδ hd ρ M hM hρ)

set_option maxHeartbeats 1000000 in
lemma norm_gaussianLogCenteredBand_operator_le (η δ : ℝ)
    (hη : 0 < η) (hηδ : η ≤ δ) (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ‖DGRHS.Kernel.integralOperator
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogBandPair η δ))
      (memLp_gaussianLogCenteredBand η δ hη hηδ hd ρ M hM hρ)‖ ≤
        4*Real.sqrt (gaussianLogBandRowControl δ M ι) := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := hoeffdingCentered μ (gaussianLogBandPair (ι := ι) η δ)
  let hW := memLp_gaussianLogCenteredBand η δ hη hηδ hd ρ M hM hρ
  have hδ : 0 < δ := lt_of_lt_of_le hη hηδ
  have hK : 0 ≤ gaussianLogBandRowControl δ M ι := by
    unfold gaussianLogBandRowControl
    positivity
  have hb : ‖hW.toLp W‖^2 ≤ 16*gaussianLogBandRowControl δ M ι := by
    rw [DGRHS.Kernel.norm_toLp_sq]
    exact (gaussianLogCenteredBand_square_controls η δ hη hηδ hd ρ M hM hρ).2
  have hn : ‖hW.toLp W‖ ≤ 4*Real.sqrt (gaussianLogBandRowControl δ M ι) := by
    nlinarith [Real.sq_sqrt hK, Real.sqrt_nonneg (gaussianLogBandRowControl δ M ι), norm_nonneg (hW.toLp W)]
  exact (DGRHS.Kernel.norm_integralOperator_le W hW).trans hn

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianLogBandRowControl
#print axioms DGRHS.Gaussian.gaussianLogBandRowControl
#check DGRHS.Gaussian.gaussianLogBandPair_square
#print axioms DGRHS.Gaussian.gaussianLogBandPair_square
#check DGRHS.Gaussian.memLp_gaussianLogBandPair
#print axioms DGRHS.Gaussian.memLp_gaussianLogBandPair
#check DGRHS.Gaussian.gaussianLogCenteredBand_square_controls
#print axioms DGRHS.Gaussian.gaussianLogCenteredBand_square_controls
#check DGRHS.Gaussian.memLp_gaussianLogCenteredBand
#print axioms DGRHS.Gaussian.memLp_gaussianLogCenteredBand
#check DGRHS.Gaussian.norm_gaussianLogCenteredBand_operator_le
#print axioms DGRHS.Gaussian.norm_gaussianLogCenteredBand_operator_le
