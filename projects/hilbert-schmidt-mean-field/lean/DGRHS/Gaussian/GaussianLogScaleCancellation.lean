import DGRHS.Gaussian.GaussianLogScaleSplit
import DGRHS.Gaussian.GaussianLogBandCanonical
import DGRHS.Gaussian.GaussianLogBandBounds

/-! Proper finite-scale source affine correction plus
low-frequency Gram diagonal cancels the infrared logarithm exactly. -/
noncomputable section
open MeasureTheory Real
open scoped BigOperators
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma integrable_gaussianLogBand_row (η δ : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] (x : EuclideanSpace ℝ ι) :
    Integrable (fun y => gaussianLogBandPair η δ (x,y)) μ := by
  have hm : StronglyMeasurable (fun y : EuclideanSpace ℝ ι => gaussianLogBandPair η δ (x,y)) :=
    (stronglyMeasurable_gaussianLogBandPair η δ hη).comp_measurable (by fun_prop)
  apply (integrable_const (Real.log (δ/η))).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro y
  change ‖gaussianLogBand η δ (x-y)‖ ≤ Real.log (δ/η)
  rw [Real.norm_of_nonneg (gaussianLogBand_nonneg η δ hη (x-y))]
  exact gaussianLogBand_le_mass η δ hη hηδ (x-y)

lemma gaussianLogShort_potential_split (δ T : ℝ) (hδ : 0 < δ) (hδT : δ ≤ T)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (x : EuclideanSpace ℝ ι) :
    (∫ y,gaussianLogShortPair T (x,y) ∂gaussianRieszDensityMeasure ρ) =
      (∫ y,gaussianLogShortPair δ (x,y) ∂gaussianRieszDensityMeasure ρ) +
      (∫ y,gaussianLogBandPair δ T (x,y) ∂gaussianRieszDensityMeasure ρ) := by
  have hc : 0 < Fintype.card ι := by exact_mod_cast hd
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  letI : NullSingletonClass (gaussianRieszDensityMeasure ρ) := by
    unfold gaussianRieszDensityMeasure;infer_instance
  have he : (fun y => gaussianLogShortPair T (x,y)) =ᵐ[gaussianRieszDensityMeasure ρ]
      (fun y => gaussianLogShortPair δ (x,y)+gaussianLogBandPair δ T (x,y)) := by
    filter_upwards [(gaussianRieszDensityMeasure ρ).ae_ne x] with y hy
    exact gaussianLogShortRange_split δ T hδ hδT (x-y) (sub_ne_zero.mpr hy.symm)
  have hi : Integrable (fun y => gaussianLogShortPair δ (x,y)) (gaussianRieszDensityMeasure ρ) :=
    integrable_gaussianLogShortRange_convolution δ hδ hd ρ M hρ x
  rw [integral_congr_ae he,integral_add hi (integrable_gaussianLogBand_row δ T hδ hδT _ x)]

lemma gaussianLogShort_pairMean_split (δ T : ℝ) (hδ : 0 < δ) (hδT : δ ≤ T)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    (∫ p,gaussianLogShortPair T p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) =
      (∫ p,gaussianLogShortPair δ p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) +
      (∫ p,gaussianLogBandPair δ T p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  have hc : 0 < Fintype.card ι := by exact_mod_cast hd
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  have he : gaussianLogShortPair T =ᵐ[(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)]
      gaussianLogShortPair δ+gaussianLogBandPair δ T := by
    filter_upwards [ae_gaussianRieszDensity_pair_ne ρ] with p hp
    exact gaussianLogShortRange_split δ T hδ hδT (p.1-p.2) (sub_ne_zero.mpr hp)
  have hi := (memLp_gaussianLogShortPair δ hδ hd ρ M hM hρ).integrable (by norm_num)
  rw [integral_congr_ae he]
  simp only [Pi.add_apply]
  exact integral_add hi (integrable_gaussianLogBandPair δ T hδ hδT _)

lemma gaussianLog_source_low_diagonal_cancellation (δ T β : ℝ)
    (hδ : 0 < δ) (hδT : δ ≤ T) (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (x : EuclideanSpace ℝ ι) :
    β*(∫ y,gaussianLogInfraredPair T (x,y) ∂gaussianRieszDensityMeasure ρ) +
      β/2*‖centeredGaussianLogBandFeature δ T hδ (gaussianRieszDensityMeasure ρ) x‖^2 -
      β/2*(∫ p,gaussianLogInfraredPair T p
        ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) =
    β*(∫ y,gaussianLogShortPair δ (x,y) ∂gaussianRieszDensityMeasure ρ) +
      β/2*(Real.log (T/δ)-gaussianLogCounterterm T) -
      β/2*(∫ p,gaussianLogShortPair δ p
        ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  have hT := lt_of_lt_of_le hδ hδT
  rw [gaussianLogInfrared_potential_eq_short_counterterm T hT hd ρ M hρ x,
    gaussianLogInfrared_pairMean_eq_short_counterterm T hT hd ρ M hM hρ,
    norm_sq_centeredGaussianLogBandFeature_eq δ T hδ hδT,
    gaussianLogShort_potential_split δ T hδ hδT hd ρ M hρ x,
    gaussianLogShort_pairMean_split δ T hδ hδT hd ρ M hM hρ]
  ring

lemma gaussianLog_source_low_diagonal_bound (δ T β : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hT : 1 ≤ T) (hβ : 0 ≤ β)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (x : EuclideanSpace ℝ ι) :
    β*(∫ y,gaussianLogInfraredPair T (x,y) ∂gaussianRieszDensityMeasure ρ) +
      β/2*‖centeredGaussianLogBandFeature δ T hδ (gaussianRieszDensityMeasure ρ) x‖^2 -
      β/2*(∫ p,gaussianLogInfraredPair T p
        ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) ≤
      β*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*δ^(Fintype.card ι : ℝ))) +
      β/2*(-Real.log δ+1/4) := by
  rw [gaussianLog_source_low_diagonal_cancellation δ T β hδ (hδ1.trans hT) hd ρ M hM hρ x]
  have hp : (∫ y,gaussianLogShortPair δ (x,y) ∂gaussianRieszDensityMeasure ρ) ≤
      M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*δ^(Fintype.card ι : ℝ)) :=
    gaussianLogShortRange_convolution_le δ hδ hd ρ M hM hρ x
  have hc := gaussianLogCounterterm_low_scale_bound δ T hδ hT
  have hm : 0 ≤ ∫ p,gaussianLogShortPair δ p
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ) :=
    integral_nonneg (fun p => gaussianLogShortRange_nonneg δ _)
  have h1 := mul_le_mul_of_nonneg_left hp hβ
  have h2 := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ β/2)
  have h3 := mul_nonneg (by positivity : 0 ≤ β/2) hm
  linarith

end DGRHS.Gaussian

#check DGRHS.Gaussian.integrable_gaussianLogBand_row
#print axioms DGRHS.Gaussian.integrable_gaussianLogBand_row
#check DGRHS.Gaussian.gaussianLogShort_potential_split
#print axioms DGRHS.Gaussian.gaussianLogShort_potential_split
#check DGRHS.Gaussian.gaussianLogShort_pairMean_split
#print axioms DGRHS.Gaussian.gaussianLogShort_pairMean_split
#check DGRHS.Gaussian.gaussianLog_source_low_diagonal_cancellation
#print axioms DGRHS.Gaussian.gaussianLog_source_low_diagonal_cancellation
#check DGRHS.Gaussian.gaussianLog_source_low_diagonal_bound
#print axioms DGRHS.Gaussian.gaussianLog_source_low_diagonal_bound
