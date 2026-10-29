import DGRHS.Gaussian.GaussianRieszBandFeature
import DGRHS.Gaussian.GaussianRieszRemainder

/-! Physical Euclidean positive band and genuine every-row L2 domination.
The short-range comparison is used only away from zero. Null singletons in
each actual density section justify the row bound, never a diagonal slice of
an AE product identity. -/
noncomputable section
open MeasureTheory Real
open scoped BigOperators ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianRieszEuclideanBand (s η δ : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  gaussianRieszEuclideanTruncation s η x - gaussianRieszEuclideanTruncation s δ x

lemma gaussianRieszEuclideanBand_eq_scaleKernel (s η δ : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (x : EuclideanSpace ℝ ι) :
    gaussianRieszEuclideanBand s η δ x =
      rieszGaussianBandKernel (gaussianRieszSourceCoefficient s) s η δ
        (gaussianRieszEuclideanCoordinates x) := by
  unfold gaussianRieszEuclideanBand
  rw [gaussianRieszEuclideanTruncation_coordinates, gaussianRieszEuclideanTruncation_coordinates,
    rieszGaussianBandKernel_eq_difference _ _ _ _ (gaussianRieszSourceCoefficient_pos s hs).le hs hη hηδ]

lemma gaussianRieszEuclideanBand_nonneg (s η δ : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (x : EuclideanSpace ℝ ι) :
    0 ≤ gaussianRieszEuclideanBand s η δ x := by
  rw [gaussianRieszEuclideanBand_eq_scaleKernel s η δ hs hη hηδ x]
  exact integral_nonneg (fun t => (Real.exp_pos _).le)

lemma gaussianRieszEuclideanBand_le_short (s η δ : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (x : EuclideanSpace ℝ ι) (hx : x ≠ 0) :
    gaussianRieszEuclideanBand s η δ x ≤ gaussianRieszEuclideanShortRange s δ x := by
  have hδ := lt_of_lt_of_le hη hηδ
  have h1 := gaussianRieszEuclidean_full_short_long_split s η hs hη x hx
  have h2 := gaussianRieszEuclidean_full_short_long_split s δ hs hδ x hx
  have hn := gaussianRieszEuclideanShortRange_nonneg s η hs x
  unfold gaussianRieszEuclideanBand
  linarith

lemma stronglyMeasurable_gaussianRieszEuclideanTruncation (s η : ℝ) (hs : 0 < s) (hη : 0 < η) :
    StronglyMeasurable (gaussianRieszEuclideanTruncation (ι := ι) s η) := by
  have hm : StronglyMeasurable (fun x : EuclideanSpace ℝ ι =>
      inner ℝ (gaussianRieszEuclideanFourierFeature s η hs hη x)
        (gaussianRieszEuclideanFourierFeature s η hs hη 0)) :=
    (stronglyMeasurable_gaussianRieszEuclideanFourierFeature s η hs hη).inner stronglyMeasurable_const
  simpa only [inner_gaussianRieszEuclideanFourierFeature, sub_zero] using hm

lemma stronglyMeasurable_gaussianRieszEuclideanBand (s η δ : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) :
    StronglyMeasurable (gaussianRieszEuclideanBand (ι := ι) s η δ) :=
  (stronglyMeasurable_gaussianRieszEuclideanTruncation s η hs hη).sub
    (stronglyMeasurable_gaussianRieszEuclideanTruncation s δ hs (lt_of_lt_of_le hη hηδ))

lemma ae_gaussianRieszEuclideanBand_sq_le_short_row (s η δ : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (x : EuclideanSpace ℝ ι) :
    ∀ᵐ y ∂gaussianRieszDensityMeasure ρ,
      gaussianRieszEuclideanBand s η δ (x-y)^2 ≤ gaussianRieszEuclideanShortRange s δ (x-y)^2 := by
  have hc : 0 < Fintype.card ι := by
    exact_mod_cast (show (0 : ℝ) < (Fintype.card ι : ℝ) by linarith)
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  letI : NullSingletonClass (gaussianRieszDensityMeasure ρ) := by
    unfold gaussianRieszDensityMeasure
    infer_instance
  filter_upwards [(gaussianRieszDensityMeasure ρ).ae_ne x] with y hy
  have hn := gaussianRieszEuclideanBand_nonneg s η δ hs hη hηδ (x-y)
  have hle := gaussianRieszEuclideanBand_le_short s η δ hs hη hηδ (x-y) (sub_ne_zero.mpr hy.symm)
  have hn2 := gaussianRieszEuclideanShortRange_nonneg s δ hs (x-y)
  nlinarith

lemma gaussianRieszEuclideanBand_row_sq_bound (s η δ : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (x : EuclideanSpace ℝ ι) :
    Integrable (fun y => gaussianRieszEuclideanBand s η δ (x-y)^2) (gaussianRieszDensityMeasure ρ) ∧
    (∫ y, gaussianRieszEuclideanBand s η δ (x-y)^2 ∂gaussianRieszDensityMeasure ρ) ≤
      M * (gaussianRieszSourceCoefficient s^2 * Real.pi^((Fintype.card ι : ℝ)/2) /
        (((Fintype.card ι : ℝ)/2-s)^2)) * δ^((Fintype.card ι : ℝ)-2*s) := by
  have hδ := lt_of_lt_of_le hη hηδ
  have hm := stronglyMeasurable_gaussianRieszEuclideanShortRange (ι := ι) s δ hδ ha
  have hi := (memLp_gaussianRieszEuclideanShortRange s δ hδ ha).integrable_sq
  have his := integrable_sq_sub_density ρ M hρ _ hi x
  have hb := ae_gaussianRieszEuclideanBand_sq_le_short_row s η δ hs hη hηδ ha ρ x
  have hmb := ((stronglyMeasurable_gaussianRieszEuclideanBand s η δ hs hη hηδ).comp_measurable (by fun_prop : Measurable (fun y : EuclideanSpace ℝ ι => x-y))).pow 2
  have hib := his.mono' hmb.aestronglyMeasurable (by
    filter_upwards [hb] with y hy
    change ‖gaussianRieszEuclideanBand s η δ (x-y)^2‖ ≤ _
    rwa [Real.norm_of_nonneg (sq_nonneg _)] )
  refine ⟨hib, ?_⟩
  calc
    _ ≤ ∫ y, gaussianRieszEuclideanShortRange s δ (x-y)^2 ∂gaussianRieszDensityMeasure ρ :=
      integral_mono_ae hib his hb
    _ ≤ M * ∫ z : EuclideanSpace ℝ ι, gaussianRieszEuclideanShortRange s δ z^2 :=
      integral_sq_sub_density_le ρ M hM hρ _ hi x
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left
        (integral_gaussianRieszEuclideanShortRange_sq_sharp (ι := ι) s δ hδ ha) hM
      simpa only [mul_assoc] using h

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianRieszEuclideanBand
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanBand

#check DGRHS.Gaussian.gaussianRieszEuclideanBand_eq_scaleKernel
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanBand_eq_scaleKernel

#check DGRHS.Gaussian.gaussianRieszEuclideanBand_nonneg
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanBand_nonneg

#check DGRHS.Gaussian.gaussianRieszEuclideanBand_le_short
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanBand_le_short

#check DGRHS.Gaussian.stronglyMeasurable_gaussianRieszEuclideanTruncation
#print axioms DGRHS.Gaussian.stronglyMeasurable_gaussianRieszEuclideanTruncation

#check DGRHS.Gaussian.stronglyMeasurable_gaussianRieszEuclideanBand
#print axioms DGRHS.Gaussian.stronglyMeasurable_gaussianRieszEuclideanBand

#check DGRHS.Gaussian.ae_gaussianRieszEuclideanBand_sq_le_short_row
#print axioms DGRHS.Gaussian.ae_gaussianRieszEuclideanBand_sq_le_short_row

#check DGRHS.Gaussian.gaussianRieszEuclideanBand_row_sq_bound
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanBand_row_sq_bound
