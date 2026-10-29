import DGRHS.Gaussian.GaussianLogScaleCancellation
import DGRHS.Gaussian.GaussianLogInfraredExponent

/-! Supporting development: actual finite cutoff identification and proper source limits.
Raw equalities hold away from zero; every-row identities use genuine null singletons. -/
noncomputable section
open MeasureTheory Real Filter
open scoped Topology
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma gaussianLogBand_counterterm_eq_anchored_short (η T : ℝ)
    (hη : 0 < η) (hηT : η ≤ T) (x : EuclideanSpace ℝ ι) (hx : x ≠ 0) :
    gaussianLogBand η T x-gaussianLogCounterterm T =
      gaussianLogAnchored T ‖x‖-gaussianLogShortRange η x := by
  rw [gaussianLogAnchored_eq_short_counterterm T (hη.trans_le hηT) x hx,
    gaussianLogShortRange_split η T hη hηT x hx]
  ring

lemma integrable_gaussianLogTruncatedPair_source (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    Integrable (gaussianLogTruncatedPair η)
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) :=
  hpair.sub ((memLp_gaussianLogShortPair η hη hd ρ M hM hρ).integrable (by norm_num))

lemma gaussianLogTruncated_potential_eq (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (x : EuclideanSpace ℝ ι) :
    (∫ y,gaussianLogTruncatedPair η (x,y) ∂gaussianRieszDensityMeasure ρ) =
      logPhysicalPotential (gaussianRieszDensityMeasure ρ) x-
      ∫ y,gaussianLogShortPair η (x,y) ∂gaussianRieszDensityMeasure ρ := by
  unfold gaussianLogTruncatedPair
  exact integral_sub (logPhysical_source_proper_bounds hd ρ M hM hρ hpair x).1
    (integrable_gaussianLogShortRange_convolution η hη hd ρ M hρ x)

lemma gaussianLogBand_potential_counterterm_eq (η T : ℝ) (hη : 0 < η) (hηT : η ≤ T)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (x : EuclideanSpace ℝ ι) :
    (∫ y,gaussianLogBandPair η T (x,y) ∂gaussianRieszDensityMeasure ρ)-gaussianLogCounterterm T =
      (∫ y,gaussianLogInfraredPair T (x,y) ∂gaussianRieszDensityMeasure ρ)-
      (∫ y,gaussianLogShortPair η (x,y) ∂gaussianRieszDensityMeasure ρ) := by
  rw [gaussianLogInfrared_potential_eq_short_counterterm T (hη.trans_le hηT) hd ρ M hρ x,
    gaussianLogShort_potential_split η T hη hηT hd ρ M hρ x]
  ring

lemma gaussianLogBand_pairMean_counterterm_eq (η T : ℝ) (hη : 0 < η) (hηT : η ≤ T)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    (∫ p,gaussianLogBandPair η T p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))-
      gaussianLogCounterterm T =
      (∫ p,gaussianLogInfraredPair T p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))-
      (∫ p,gaussianLogShortPair η p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  rw [gaussianLogInfrared_pairMean_eq_short_counterterm T (hη.trans_le hηT) hd ρ M hM hρ,
    gaussianLogShort_pairMean_split η T hη hηT hd ρ M hM hρ]
  ring

lemma gaussianLogTruncated_pairMean_eq (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    (∫ p,gaussianLogTruncatedPair η p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) =
      (∫ p,logPhysicalPair p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))-
      (∫ p,gaussianLogShortPair η p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  unfold gaussianLogTruncatedPair
  exact integral_sub hpair ((memLp_gaussianLogShortPair η hη hd ρ M hM hρ).integrable (by norm_num))

lemma tendsto_gaussianLogCutoff_potential (η : ℝ) (hη : 0 < η)
    (T : ℕ → ℝ) (hT : Tendsto T atTop atTop) (hηT : ∀ j,η ≤ T j)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (x : EuclideanSpace ℝ ι) :
    Tendsto (fun j => (∫ y,gaussianLogBandPair η (T j) (x,y) ∂gaussianRieszDensityMeasure ρ)-
      gaussianLogCounterterm (T j)) atTop
      (𝓝 (∫ y,gaussianLogTruncatedPair η (x,y) ∂gaussianRieszDensityMeasure ρ)) := by
  have he : (fun j => (∫ y,gaussianLogBandPair η (T j) (x,y) ∂gaussianRieszDensityMeasure ρ)-
      gaussianLogCounterterm (T j)) =
      (fun j => (∫ y,gaussianLogInfraredPair (T j) (x,y) ∂gaussianRieszDensityMeasure ρ)-
      ∫ y,gaussianLogShortPair η (x,y) ∂gaussianRieszDensityMeasure ρ) := by
    funext j
    exact gaussianLogBand_potential_counterterm_eq η (T j) hη (hηT j) hd ρ M hρ x
  rw [he,gaussianLogTruncated_potential_eq η hη hd ρ M hM hρ hpair x]
  exact (tendsto_gaussianLogInfrared_potential T hT hd ρ M hM hρ hpair x).sub_const _

lemma tendsto_gaussianLogCutoff_pairMean (η : ℝ) (hη : 0 < η)
    (T : ℕ → ℝ) (hT : Tendsto T atTop atTop) (hηT : ∀ j,η ≤ T j)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    Tendsto (fun j => (∫ p,gaussianLogBandPair η (T j) p
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))-
      gaussianLogCounterterm (T j)) atTop
      (𝓝 (∫ p,gaussianLogTruncatedPair η p
        ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) := by
  have he : (fun j => (∫ p,gaussianLogBandPair η (T j) p
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))-
      gaussianLogCounterterm (T j)) =
      (fun j => (∫ p,gaussianLogInfraredPair (T j) p
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))-
      ∫ p,gaussianLogShortPair η p
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
    funext j
    exact gaussianLogBand_pairMean_counterterm_eq η (T j) hη (hηT j) hd ρ M hM hρ
  rw [he,gaussianLogTruncated_pairMean_eq η hη hd ρ M hM hρ hpair]
  exact (tendsto_gaussianLogInfrared_pairMean T hT hd ρ hpair).sub_const _

lemma gaussianLogBandCentered_eq_infrared_sub_short (η T : ℝ)
    (hη : 0 < η) (hηT : η ≤ T)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (hp : p.1 ≠ p.2) :
    hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogBandPair η T) p =
      hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogInfraredPair T) p -
        hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogShortPair η) p := by
  let μ := gaussianRieszDensityMeasure ρ
  have hraw := gaussianLogBand_counterterm_eq_anchored_short η T hη hηT
    (p.1-p.2) (sub_ne_zero.mpr hp)
  have h1 := gaussianLogBand_potential_counterterm_eq η T hη hηT hd ρ M hρ p.1
  have h2 := gaussianLogBand_potential_counterterm_eq η T hη hηT hd ρ M hρ p.2
  have hm := gaussianLogBand_pairMean_counterterm_eq η T hη hηT hd ρ M hM hρ
  have hb : (fun x => gaussianLogBandPair η T (x,p.2)) =
      (fun x => gaussianLogBandPair η T (p.2,x)) := by
    funext x; unfold gaussianLogBandPair gaussianLogBand; rw [norm_sub_rev]
  have hi : (fun x => gaussianLogInfraredPair T (x,p.2)) =
      (fun x => gaussianLogInfraredPair T (p.2,x)) := by
    funext x; unfold gaussianLogInfraredPair; rw [norm_sub_rev]
  have hs : (fun x => gaussianLogShortPair η (x,p.2)) =
      (fun x => gaussianLogShortPair η (p.2,x)) := by
    funext x; unfold gaussianLogShortPair gaussianLogShortRange; rw [norm_sub_rev]
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  rw [hb,hi,hs]
  change gaussianLogBand η T (p.1-p.2) -
    (∫ y,gaussianLogBandPair η T (p.1,y) ∂μ) -
    (∫ y,gaussianLogBandPair η T (p.2,y) ∂μ) +
    (∫ q,gaussianLogBandPair η T q ∂μ.prod μ) =
    (gaussianLogAnchored T ‖p.1-p.2‖ -
    (∫ y,gaussianLogInfraredPair T (p.1,y) ∂μ) -
    (∫ y,gaussianLogInfraredPair T (p.2,y) ∂μ) +
    (∫ q,gaussianLogInfraredPair T q ∂μ.prod μ)) -
    (gaussianLogShortRange η (p.1-p.2) -
    (∫ y,gaussianLogShortPair η (p.1,y) ∂μ) -
    (∫ y,gaussianLogShortPair η (p.2,y) ∂μ) +
    (∫ q,gaussianLogShortPair η q ∂μ.prod μ))
  linarith

lemma ae_tendsto_gaussianLogCenteredBand_to_cutoff (η : ℝ) (hη : 0 < η)
    (T : ℕ → ℝ) (hT : Tendsto T atTop atTop) (hηT : ∀ j,η ≤ T j)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    ∀ᵐ p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ),
      Tendsto (fun j => hoeffdingCentered (gaussianRieszDensityMeasure ρ)
        (gaussianLogBandPair η (T j)) p) atTop
        (𝓝 (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogTruncatedPair η) p)) := by
  have hc : 0 < Fintype.card ι := by exact_mod_cast hd
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  filter_upwards [ae_gaussianRieszDensity_pair_ne ρ,
    ae_logPhysical_centered_truncation_difference η hη hd ρ M hM hρ hpair] with p hp he
  have hf : (fun j => hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogBandPair η (T j)) p) =
      (fun j => hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogInfraredPair (T j)) p -
        hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogShortPair η) p) := by
    funext j
    exact gaussianLogBandCentered_eq_infrared_sub_short η (T j) hη (hηT j) hd ρ M hM hρ p hp
  rw [hf,he]
  exact (tendsto_gaussianLogInfraredCentered T hT hd ρ M hM hρ hpair p hp).sub_const _

end DGRHS.Gaussian
#check @DGRHS.Gaussian.gaussianLogBand_counterterm_eq_anchored_short
#print axioms DGRHS.Gaussian.gaussianLogBand_counterterm_eq_anchored_short
#check @DGRHS.Gaussian.integrable_gaussianLogTruncatedPair_source
#print axioms DGRHS.Gaussian.integrable_gaussianLogTruncatedPair_source
#check @DGRHS.Gaussian.gaussianLogTruncated_potential_eq
#print axioms DGRHS.Gaussian.gaussianLogTruncated_potential_eq
#check @DGRHS.Gaussian.gaussianLogBand_potential_counterterm_eq
#print axioms DGRHS.Gaussian.gaussianLogBand_potential_counterterm_eq
#check @DGRHS.Gaussian.gaussianLogBand_pairMean_counterterm_eq
#print axioms DGRHS.Gaussian.gaussianLogBand_pairMean_counterterm_eq
#check @DGRHS.Gaussian.gaussianLogTruncated_pairMean_eq
#print axioms DGRHS.Gaussian.gaussianLogTruncated_pairMean_eq
#check @DGRHS.Gaussian.tendsto_gaussianLogCutoff_potential
#print axioms DGRHS.Gaussian.tendsto_gaussianLogCutoff_potential
#check @DGRHS.Gaussian.tendsto_gaussianLogCutoff_pairMean
#print axioms DGRHS.Gaussian.tendsto_gaussianLogCutoff_pairMean
#check @DGRHS.Gaussian.gaussianLogBandCentered_eq_infrared_sub_short
#print axioms DGRHS.Gaussian.gaussianLogBandCentered_eq_infrared_sub_short
#check @DGRHS.Gaussian.ae_tendsto_gaussianLogCenteredBand_to_cutoff
#print axioms DGRHS.Gaussian.ae_tendsto_gaussianLogCenteredBand_to_cutoff
