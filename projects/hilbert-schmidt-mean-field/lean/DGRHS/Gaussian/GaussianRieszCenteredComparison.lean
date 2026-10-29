import DGRHS.Gaussian.GaussianRieszRemainder
import DGRHS.Gaussian.HoeffdingLinearity
import DGRHS.Gaussian.RieszGaussianEuclideanCentering
import DGRHS.Gaussian.FeatureKernel

/-! Actual full/truncated physical kernels, exact centered difference and SAME
integral-operator difference, with the derived cutoff-independent L2/op bound. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianRieszPhysicalPair (s : ℝ) (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : ℝ :=
  ‖p.1 - p.2‖ ^ (-s) / s

def gaussianRieszTruncatedPair (s η : ℝ) (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : ℝ :=
  gaussianRieszEuclideanTruncation s η (p.1 - p.2)

def gaussianRieszShortPair (s η : ℝ) (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : ℝ :=
  gaussianRieszEuclideanShortRange s η (p.1 - p.2)

lemma stronglyMeasurable_gaussianRieszPhysicalPair (s : ℝ) :
    StronglyMeasurable (gaussianRieszPhysicalPair (ι := ι) s) := by
  apply Measurable.stronglyMeasurable
  unfold gaussianRieszPhysicalPair
  fun_prop

lemma stronglyMeasurable_gaussianRieszTruncatedPair (s η : ℝ) (hs : 0 < s) (hη : 0 < η) :
    StronglyMeasurable (gaussianRieszTruncatedPair (ι := ι) s η) := by
  have hk := stronglyMeasurable_gaussianRieszEuclideanFourierFeature (ι := ι) s η hs hη
  have hm : StronglyMeasurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      inner ℝ (gaussianRieszEuclideanFourierFeature s η hs hη p.1)
        (gaussianRieszEuclideanFourierFeature s η hs hη p.2)) :=
    (hk.comp_measurable measurable_fst).inner (hk.comp_measurable measurable_snd)
  convert hm using 1
  funext p
  exact (inner_gaussianRieszEuclideanFourierFeature s η hs hη p.1 p.2).symm

lemma memLp_gaussianRieszTruncatedPair (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    MemLp (gaussianRieszTruncatedPair (ι := ι) s η) 2 (μ.prod μ) := by
  let k := gaussianRieszEuclideanFourierFeature (ι := ι) s η hs hη
  have hm : StronglyMeasurable k := stronglyMeasurable_gaussianRieszEuclideanFourierFeature s η hs hη
  have hk : MemLp k 2 μ := by
    apply (memLp_const (Real.sqrt (gaussianRieszSourceCoefficient s / s * η ^ (-s)))).of_le
      hm.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact (norm_gaussianRieszEuclideanFourierFeature s η hs hη x).le
  have he : gaussianRieszTruncatedPair s η = featureKernel k := by
    funext p
    exact (inner_gaussianRieszEuclideanFourierFeature s η hs hη p.1 p.2).symm
  rw [he]
  exact memLp_featureKernel k hm hk

lemma stronglyMeasurable_gaussianRieszShortPair (s η : ℝ) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s) :
    StronglyMeasurable (gaussianRieszShortPair (ι := ι) s η) :=
  (stronglyMeasurable_gaussianRieszEuclideanShortRange s η hη ha).comp_measurable (by fun_prop)

lemma memLp_gaussianRieszPhysicalPair (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    MemLp (gaussianRieszPhysicalPair (ι := ι) s) 2
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  have hshort := memLp_gaussianRieszEuclideanShortRange_source s 1 (by norm_num) ha ρ M hM hρ
  have hlong := memLp_gaussianRieszTruncatedPair s 1 hs (by norm_num) (gaussianRieszDensityMeasure ρ)
  have he : gaussianRieszShortPair s 1 + gaussianRieszTruncatedPair s 1
      =ᵐ[(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)] gaussianRieszPhysicalPair s := by
    filter_upwards [ae_gaussianRieszEuclideanShortRange_eq_physical_remainder s 1 hs (by norm_num) ha ρ] with p hp
    change gaussianRieszEuclideanShortRange s 1 (p.1-p.2) +
      gaussianRieszEuclideanTruncation s 1 (p.1-p.2) = ‖p.1-p.2‖ ^ (-s) / s
    linarith
  exact (memLp_congr_ae he).1 (hshort.add hlong)

lemma ae_gaussianRiesz_centered_difference (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s) -
      hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszTruncatedPair s η)
      =ᵐ[(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)]
        hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszShortPair s η) := by
  have hc := ae_hoeffdingCentered_congr (gaussianRieszDensityMeasure ρ) _ _
    (ae_gaussianRieszEuclideanShortRange_eq_physical_remainder s η hs hη ha ρ)
  have hl := ae_hoeffdingCentered_sub (gaussianRieszDensityMeasure ρ) _ _
    ((memLp_gaussianRieszPhysicalPair s hs ha ρ M hM hρ).integrable (by norm_num))
    ((memLp_gaussianRieszTruncatedPair s η hs hη (gaussianRieszDensityMeasure ρ)).integrable (by norm_num))
  exact (hc.trans hl).symm

lemma memLp_gaussianRieszCenteredPhysicalPair (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    MemLp (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s)) 2
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) :=
  memLp_hoeffdingCentered _ _ (stronglyMeasurable_gaussianRieszPhysicalPair s)
    (memLp_gaussianRieszPhysicalPair s hs ha ρ M hM hρ)

lemma memLp_gaussianRieszCenteredTruncatedPair (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    MemLp (hoeffdingCentered μ (gaussianRieszTruncatedPair (ι := ι) s η)) 2 (μ.prod μ) :=
  memLp_hoeffdingCentered _ _ (stronglyMeasurable_gaussianRieszTruncatedPair s η hs hη)
    (memLp_gaussianRieszTruncatedPair s η hs hη μ)

lemma memLp_gaussianRieszCenteredShortPair (s η : ℝ) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    MemLp (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszShortPair s η)) 2
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) :=
  memLp_hoeffdingCentered _ _ (stronglyMeasurable_gaussianRieszShortPair s η hη ha)
    (memLp_gaussianRieszEuclideanShortRange_source s η hη ha ρ M hM hρ)

set_option maxHeartbeats 1000000 in
lemma norm_gaussianRieszCenteredShortPair_le (s η : ℝ) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ‖(memLp_gaussianRieszCenteredShortPair s η hη ha ρ M hM hρ).toLp
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszShortPair s η))‖ ≤
      4 * gaussianRieszShortRangeRateConstant s M ι * η ^ ((Fintype.card ι : ℝ) / 2 - s) := by
  have hraw : ‖(memLp_gaussianRieszEuclideanShortRange_source s η hη ha ρ M hM hρ).toLp
      (gaussianRieszShortPair s η)‖ ≤
      gaussianRieszShortRangeRateConstant s M ι * η ^ ((Fintype.card ι : ℝ) / 2 - s) := by
    change ‖gaussianRieszShortRangeSourceL2 s η hη ha ρ M hM hρ‖ ≤ _
    exact norm_gaussianRieszShortRangeSourceL2_le s η hη ha ρ M hM hρ
  have hc := norm_hoeffdingCentered_le (gaussianRieszDensityMeasure ρ)
    (gaussianRieszShortPair s η) (stronglyMeasurable_gaussianRieszShortPair s η hη ha)
    (memLp_gaussianRieszEuclideanShortRange_source s η hη ha ρ M hM hρ)
  calc
    _ ≤ 4 * ‖(memLp_gaussianRieszEuclideanShortRange_source s η hη ha ρ M hM hρ).toLp
      (gaussianRieszShortPair s η)‖ := hc
    _ ≤ _ := by linarith

lemma gaussianRieszCenteredTruncatedPair_eq_source (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    hoeffdingCentered μ (gaussianRieszTruncatedPair s η) p =
      centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2 := by
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
    gaussianRieszTruncatedPair centeredGaussianRieszEuclideanTruncatedKernel
  change gaussianRieszEuclideanTruncation s η (p.1-p.2) -
    (∫ y, gaussianRieszEuclideanTruncation s η (p.1-y) ∂μ) -
    (∫ x, gaussianRieszEuclideanTruncation s η (x-p.2) ∂μ) +
    (∫ z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, gaussianRieszEuclideanTruncation s η (z.1-z.2) ∂μ.prod μ) =
    gaussianRieszEuclideanTruncation s η (p.1-p.2) -
    (∫ y, gaussianRieszEuclideanTruncation s η (p.1-y) ∂μ) -
    (∫ x, gaussianRieszEuclideanTruncation s η (x-p.2) ∂μ) +
    (∫ x, (∫ y, gaussianRieszEuclideanTruncation s η (x-y) ∂μ) ∂μ)
  congr 1
  exact integral_prod _ ((memLp_gaussianRieszTruncatedPair s η hs hη μ).integrable (by norm_num))

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianRieszPhysicalPair
#print axioms DGRHS.Gaussian.gaussianRieszPhysicalPair
#check DGRHS.Gaussian.gaussianRieszTruncatedPair
#print axioms DGRHS.Gaussian.gaussianRieszTruncatedPair
#check DGRHS.Gaussian.gaussianRieszShortPair
#print axioms DGRHS.Gaussian.gaussianRieszShortPair
#check DGRHS.Gaussian.stronglyMeasurable_gaussianRieszPhysicalPair
#print axioms DGRHS.Gaussian.stronglyMeasurable_gaussianRieszPhysicalPair
#check DGRHS.Gaussian.stronglyMeasurable_gaussianRieszTruncatedPair
#print axioms DGRHS.Gaussian.stronglyMeasurable_gaussianRieszTruncatedPair
#check DGRHS.Gaussian.memLp_gaussianRieszTruncatedPair
#print axioms DGRHS.Gaussian.memLp_gaussianRieszTruncatedPair
#check DGRHS.Gaussian.stronglyMeasurable_gaussianRieszShortPair
#print axioms DGRHS.Gaussian.stronglyMeasurable_gaussianRieszShortPair
#check DGRHS.Gaussian.memLp_gaussianRieszPhysicalPair
#print axioms DGRHS.Gaussian.memLp_gaussianRieszPhysicalPair
#check DGRHS.Gaussian.ae_gaussianRiesz_centered_difference
#print axioms DGRHS.Gaussian.ae_gaussianRiesz_centered_difference
#check DGRHS.Gaussian.memLp_gaussianRieszCenteredPhysicalPair
#print axioms DGRHS.Gaussian.memLp_gaussianRieszCenteredPhysicalPair
#check DGRHS.Gaussian.memLp_gaussianRieszCenteredTruncatedPair
#print axioms DGRHS.Gaussian.memLp_gaussianRieszCenteredTruncatedPair
#check DGRHS.Gaussian.memLp_gaussianRieszCenteredShortPair
#print axioms DGRHS.Gaussian.memLp_gaussianRieszCenteredShortPair
#check DGRHS.Gaussian.norm_gaussianRieszCenteredShortPair_le
#print axioms DGRHS.Gaussian.norm_gaussianRieszCenteredShortPair_le
#check DGRHS.Gaussian.gaussianRieszCenteredTruncatedPair_eq_source
#print axioms DGRHS.Gaussian.gaussianRieszCenteredTruncatedPair_eq_source
