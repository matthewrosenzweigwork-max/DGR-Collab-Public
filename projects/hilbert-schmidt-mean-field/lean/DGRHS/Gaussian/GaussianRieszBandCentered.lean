import DGRHS.Gaussian.GaussianRieszBandBounds
import DGRHS.Gaussian.HoeffdingRowL2

/-! Actual centered physical-band mixed and joint square estimates and SAME
source integral-operator norm. All raw bounds are instantiated from the physical
Gaussian short-range kernel, with no master/tail conclusions as premises. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianRieszBandPair (s η δ : ℝ) (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : ℝ :=
  gaussianRieszEuclideanBand s η δ (p.1-p.2)

def gaussianRieszBandRowControl (s δ M : ℝ) (ι : Type*) [Fintype ι] : ℝ :=
  M*(gaussianRieszSourceCoefficient s^2*Real.pi^((Fintype.card ι : ℝ)/2) /
    (((Fintype.card ι : ℝ)/2-s)^2))*δ^((Fintype.card ι : ℝ)-2*s)

lemma stronglyMeasurable_gaussianRieszBandPair (s η δ : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) : StronglyMeasurable (gaussianRieszBandPair (ι := ι) s η δ) :=
  (stronglyMeasurable_gaussianRieszEuclideanBand s η δ hs hη hηδ).comp_measurable (by fun_prop)

lemma gaussianRieszBandPair_square (s η δ : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    Integrable (fun p => gaussianRieszBandPair s η δ p^2)
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) ∧
    (∫ p, gaussianRieszBandPair s η δ p^2
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) ≤
      gaussianRieszBandRowControl s δ M ι := by
  let μ := gaussianRieszDensityMeasure ρ
  have hm := (stronglyMeasurable_gaussianRieszBandPair (ι := ι) s η δ hs hη hηδ).pow 2
  have hr := fun x => gaussianRieszEuclideanBand_row_sq_bound s η δ hs hη hηδ ha ρ M hM hρ x
  have hi : Integrable (fun p => gaussianRieszBandPair s η δ p^2) (μ.prod μ) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall (fun x => (hr x).1)
    · apply (integrable_const (gaussianRieszBandRowControl s δ M ι)).mono'
        hm.norm.integral_prod_right'.aestronglyMeasurable
      apply Filter.Eventually.of_forall
      intro x
      change ‖∫ y, ‖gaussianRieszBandPair s η δ (x,y)^2‖ ∂μ‖ ≤ _
      simp_rw [Real.norm_of_nonneg (sq_nonneg _)]
      rw [Real.norm_of_nonneg (integral_nonneg (fun y => sq_nonneg _))]
      exact (hr x).2
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ _ : EuclideanSpace ℝ ι, gaussianRieszBandRowControl s δ M ι ∂μ :=
      integral_mono_ae hi.integral_prod_left (integrable_const _)
        (Filter.Eventually.of_forall (fun x => (hr x).2))
    _ = _ := by simp

lemma memLp_gaussianRieszBandPair (s η δ : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    MemLp (gaussianRieszBandPair s η δ) 2
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) :=
  (memLp_two_iff_integrable_sq
    (stronglyMeasurable_gaussianRieszBandPair s η δ hs hη hηδ).aestronglyMeasurable).2
    (gaussianRieszBandPair_square s η δ hs hη hηδ ha ρ M hM hρ).1

lemma gaussianRieszCenteredBand_square_controls (s η δ : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    (∀ᵐ x ∂gaussianRieszDensityMeasure ρ,
      (∫ y, hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszBandPair s η δ) (x,y)^2
        ∂gaussianRieszDensityMeasure ρ) ≤ 16*gaussianRieszBandRowControl s δ M ι) ∧
    (∫ p, hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszBandPair s η δ) p^2
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) ≤
        16*gaussianRieszBandRowControl s δ M ι := by
  have hm := stronglyMeasurable_gaussianRieszBandPair (ι := ι) s η δ hs hη hηδ
  have h2 := memLp_gaussianRieszBandPair s η δ hs hη hηδ ha ρ M hM hρ
  constructor
  · exact ae_row_sq_hoeffdingCentered_le _ _ hm h2 _
      (Filter.Eventually.of_forall (fun x =>
        (gaussianRieszEuclideanBand_row_sq_bound s η δ hs hη hηδ ha ρ M hM hρ x).2))
  · exact (integral_sq_hoeffdingCentered_le _ _ hm h2).trans
      (mul_le_mul_of_nonneg_left (gaussianRieszBandPair_square s η δ hs hη hηδ ha ρ M hM hρ).2 (by positivity))

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianRieszBandPair
#print axioms DGRHS.Gaussian.gaussianRieszBandPair

#check DGRHS.Gaussian.gaussianRieszBandRowControl
#print axioms DGRHS.Gaussian.gaussianRieszBandRowControl

#check DGRHS.Gaussian.stronglyMeasurable_gaussianRieszBandPair
#print axioms DGRHS.Gaussian.stronglyMeasurable_gaussianRieszBandPair

#check DGRHS.Gaussian.gaussianRieszBandPair_square
#print axioms DGRHS.Gaussian.gaussianRieszBandPair_square

#check DGRHS.Gaussian.memLp_gaussianRieszBandPair
#print axioms DGRHS.Gaussian.memLp_gaussianRieszBandPair

#check DGRHS.Gaussian.gaussianRieszCenteredBand_square_controls
#print axioms DGRHS.Gaussian.gaussianRieszCenteredBand_square_controls
