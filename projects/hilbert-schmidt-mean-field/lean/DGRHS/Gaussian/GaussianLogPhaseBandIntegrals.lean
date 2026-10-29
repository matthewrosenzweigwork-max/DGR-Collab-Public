import DGRHS.Gaussian.GaussianLogPhaseCenteringAlgebra

/-! Supporting development. Proper finite-band raw phase integrals; no identification of
pointwise representatives of a Bochner L2 mean is assumed. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma integral_gaussianLogSpatialPhase_inner_band (η T : ℝ) (hη : 0 < η)
    (x y : EuclideanSpace ℝ ι) :
    (∫ p, inner ℝ (gaussianLogSpatialPhase x p) (gaussianLogSpatialPhase y p)
      ∂(gaussianLogBandMeasure η T).prod (finiteStandardGaussian ι)) =
      gaussianLogBand η T (x-y) := by
  letI := finite_gaussianLogBandMeasure η T hη
  calc
    _ = inner ℝ (gaussianLogBandFeature η T hη x) (gaussianLogBandFeature η T hη y) := by
      symm
      unfold gaussianLogBandFeature
      rw [L2.inner_def, integral_congr_ae (ae_inner_gaussianScaleMixtureFeature
        (gaussianLogBandMeasure η T) (gaussianRieszEuclideanCoordinates x)
        (gaussianRieszEuclideanCoordinates y))]
      rfl
    _ = _ := inner_gaussianLogBandFeature η T hη x y

lemma integral_gaussianLogSpatialPhase_mean_inner_band (η T : ℝ) (hη : 0 < η)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (x : EuclideanSpace ℝ ι) :
    (∫ p, inner ℝ (gaussianLogSpatialPhase x p) (gaussianLogSpatialPhaseMean μ p)
      ∂(gaussianLogBandMeasure η T).prod (finiteStandardGaussian ι)) =
      ∫ y, gaussianLogBandPair η T (x,y) ∂μ := by
  letI := finite_gaussianLogBandMeasure η T hη
  let ν := (gaussianLogBandMeasure η T).prod (finiteStandardGaussian ι)
  have hm : StronglyMeasurable (fun q : EuclideanSpace ℝ ι × (ℝ × (ι → ℝ)) =>
      inner ℝ (gaussianLogSpatialPhase x q.2) (gaussianLogSpatialPhase q.1 q.2)) :=
    ((measurable_gaussianScaleMixtureCharacter (gaussianRieszEuclideanCoordinates x)).stronglyMeasurable.comp_measurable
      measurable_snd).inner measurable_gaussianLogSpatialPhase_joint.stronglyMeasurable
  have hi : Integrable (fun q : EuclideanSpace ℝ ι × (ℝ × (ι → ℝ)) =>
      inner ℝ (gaussianLogSpatialPhase x q.2) (gaussianLogSpatialPhase q.1 q.2)) (μ.prod ν) := by
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun q => by
      simpa only [norm_gaussianLogSpatialPhase, one_mul] using
        norm_inner_le_norm (𝕜 := ℝ) (gaussianLogSpatialPhase x q.2) (gaussianLogSpatialPhase q.1 q.2))
  have he (p : ℝ × (ι → ℝ)) : inner ℝ (gaussianLogSpatialPhase x p) (gaussianLogSpatialPhaseMean μ p) =
      ∫ y, inner ℝ (gaussianLogSpatialPhase x p) (gaussianLogSpatialPhase y p) ∂μ := by
    unfold gaussianLogSpatialPhaseMean
    rw [integral_inner (integrable_gaussianLogSpatialPhase μ p)]
  simp_rw [he]
  rw [← integral_integral_swap hi]
  simp_rw [integral_gaussianLogSpatialPhase_inner_band η T hη]
  rfl

lemma integral_gaussianLogSpatialPhaseMean_sq_band (η T : ℝ) (hη : 0 < η)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    (∫ p, ‖gaussianLogSpatialPhaseMean μ p‖^2
      ∂(gaussianLogBandMeasure η T).prod (finiteStandardGaussian ι)) =
      ∫ x, (∫ y, gaussianLogBandPair η T (x,y) ∂μ) ∂μ := by
  letI := finite_gaussianLogBandMeasure η T hη
  let ν := (gaussianLogBandMeasure η T).prod (finiteStandardGaussian ι)
  have hm : StronglyMeasurable (gaussianLogSpatialPhaseMean μ) :=
    measurable_gaussianLogSpatialPhase_joint.stronglyMeasurable.integral_prod_left'
  have hsm : StronglyMeasurable (fun q : EuclideanSpace ℝ ι × (ℝ × (ι → ℝ)) =>
      inner ℝ (gaussianLogSpatialPhase q.1 q.2) (gaussianLogSpatialPhaseMean μ q.2)) :=
    measurable_gaussianLogSpatialPhase_joint.stronglyMeasurable.inner (hm.comp_measurable measurable_snd)
  have hi : Integrable (fun q : EuclideanSpace ℝ ι × (ℝ × (ι → ℝ)) =>
      inner ℝ (gaussianLogSpatialPhase q.1 q.2) (gaussianLogSpatialPhaseMean μ q.2)) (μ.prod ν) := by
    apply (integrable_const (1 : ℝ)).mono' hsm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun q => by
      have hb := norm_inner_le_norm (𝕜 := ℝ) (gaussianLogSpatialPhase q.1 q.2) (gaussianLogSpatialPhaseMean μ q.2)
      rw [norm_gaussianLogSpatialPhase, one_mul] at hb
      exact hb.trans (norm_gaussianLogSpatialPhaseMean_le μ q.2))
  have he (p : ℝ × (ι → ℝ)) : ‖gaussianLogSpatialPhaseMean μ p‖^2 =
      ∫ x, inner ℝ (gaussianLogSpatialPhase x p) (gaussianLogSpatialPhaseMean μ p) ∂μ := by
    calc
      _ = inner ℝ (gaussianLogSpatialPhaseMean μ p) (gaussianLogSpatialPhaseMean μ p) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = ∫ x, inner ℝ (gaussianLogSpatialPhaseMean μ p) (gaussianLogSpatialPhase x p) ∂μ := by
        rw [integral_inner (integrable_gaussianLogSpatialPhase μ p)]
        rfl
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun x => real_inner_comm _ _))
  simp_rw [he]
  rw [← integral_integral_swap hi]
  simp_rw [integral_gaussianLogSpatialPhase_mean_inner_band η T hη μ]

lemma integral_gaussianLogCenteredPhase_inner_band (η T : ℝ) (hη : 0 < η) (hηT : η ≤ T)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (x y : EuclideanSpace ℝ ι) :
    (∫ p, inner ℝ (gaussianLogCenteredPhase μ x p) (gaussianLogCenteredPhase μ y p)
      ∂(gaussianLogBandMeasure η T).prod (finiteStandardGaussian ι)) =
      hoeffdingCentered μ (gaussianLogBandPair η T) (x,y) := by
  letI := finite_gaussianLogBandMeasure η T hη
  let ν := (gaussianLogBandMeasure η T).prod (finiteStandardGaussian ι)
  let χ := fun z : EuclideanSpace ℝ ι => gaussianLogSpatialPhase z
  let m := gaussianLogSpatialPhaseMean μ
  have hm : StronglyMeasurable m :=
    measurable_gaussianLogSpatialPhase_joint.stronglyMeasurable.integral_prod_left'
  have hχ (z : EuclideanSpace ℝ ι) : StronglyMeasurable (χ z) :=
    (measurable_gaussianScaleMixtureCharacter (gaussianRieszEuclideanCoordinates z)).stronglyMeasurable
  have hi (f g : (ℝ × (ι → ℝ)) → ℂ) (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
      (hfb : ∀ p, ‖f p‖ ≤ 1) (hgb : ∀ p, ‖g p‖ ≤ 1) :
      Integrable (fun p => inner ℝ (f p) (g p)) ν := by
    apply (integrable_const (1 : ℝ)).mono' (hf.inner hg).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun p => (norm_inner_le_norm _ _).trans
      (by simpa only [one_mul] using mul_le_mul (hfb p) (hgb p) (norm_nonneg _) (by norm_num)))
  have hb (z : EuclideanSpace ℝ ι) (p : ℝ × (ι → ℝ)) : ‖χ z p‖ ≤ 1 := (norm_gaussianLogSpatialPhase z p).le
  have hmb (p : ℝ × (ι → ℝ)) : ‖m p‖ ≤ 1 := norm_gaussianLogSpatialPhaseMean_le μ p
  have hraw := hi (χ x) (χ y) (hχ x) (hχ y) (hb x) (hb y)
  have hl := hi (χ x) m (hχ x) hm (hb x) hmb
  have hr := hi m (χ y) hm (hχ y) hmb (hb y)
  have hmm := hi m m hm hm hmb hmb
  have hs : Integrable (fun p => ‖m p‖^2) ν := by
    simpa only [real_inner_self_eq_norm_sq] using hmm
  change (∫ p, inner ℝ (χ x p-m p) (χ y p-m p) ∂ν) = _
  have he (p : ℝ × (ι → ℝ)) : inner ℝ (χ x p-m p) (χ y p-m p) =
      inner ℝ (χ x p) (χ y p) - inner ℝ (χ x p) (m p) - inner ℝ (m p) (χ y p) + ‖m p‖^2 := by
    rw [inner_sub_left,inner_sub_right,inner_sub_right,real_inner_self_eq_norm_sq]
    ring
  simp_rw [he]
  have hsub : Integrable (fun p => inner ℝ (χ x p) (χ y p)-inner ℝ (χ x p) (m p)) ν := hraw.sub hl
  have hsub2 : Integrable (fun p => inner ℝ (χ x p) (χ y p)-inner ℝ (χ x p) (m p)-inner ℝ (m p) (χ y p)) ν := hsub.sub hr
  rw [integral_add hsub2 hs,integral_sub hsub hr,integral_sub hraw hl]
  have hcomm : (∫ p,inner ℝ (m p) (χ y p) ∂ν) = ∫ p,inner ℝ (χ y p) (m p) ∂ν :=
    integral_congr_ae (Filter.Eventually.of_forall (fun p => real_inner_comm _ _))
  rw [hcomm]
  change (∫ p,inner ℝ (gaussianLogSpatialPhase x p) (gaussianLogSpatialPhase y p) ∂ν) -
    (∫ p,inner ℝ (gaussianLogSpatialPhase x p) (gaussianLogSpatialPhaseMean μ p) ∂ν) -
    (∫ p,inner ℝ (gaussianLogSpatialPhase y p) (gaussianLogSpatialPhaseMean μ p) ∂ν) +
    (∫ p,‖gaussianLogSpatialPhaseMean μ p‖^2 ∂ν) = _
  rw [integral_gaussianLogSpatialPhase_inner_band η T hη,
    integral_gaussianLogSpatialPhase_mean_inner_band η T hη μ,
    integral_gaussianLogSpatialPhase_mean_inner_band η T hη μ,
    integral_gaussianLogSpatialPhaseMean_sq_band η T hη μ]
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  rw [integral_prod _ (integrable_gaussianLogBandPair η T hη hηT μ)]
  have he : (fun z => gaussianLogBandPair η T (y,z)) = (fun z => gaussianLogBandPair η T (z,y)) := by
    funext z
    unfold gaussianLogBandPair gaussianLogBand
    rw [norm_sub_rev]
  rw [he]
  rfl

lemma integral_gaussianLogCenteredPhase_sq_band (η T : ℝ) (hη : 0 < η) (hηT : η ≤ T)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (x : EuclideanSpace ℝ ι) :
    (∫ p, ‖gaussianLogCenteredPhase μ x p‖^2
      ∂(gaussianLogBandMeasure η T).prod (finiteStandardGaussian ι)) =
      ‖centeredGaussianLogBandFeature η T hη μ x‖^2 := by
  simp_rw [← real_inner_self_eq_norm_sq]
  rw [integral_gaussianLogCenteredPhase_inner_band η T hη hηT μ x x,
    inner_centeredGaussianLogBandFeature η T hη hηT μ x x]

end DGRHS.Gaussian
#check @DGRHS.Gaussian.integral_gaussianLogSpatialPhase_inner_band
#print axioms DGRHS.Gaussian.integral_gaussianLogSpatialPhase_inner_band
#check @DGRHS.Gaussian.integral_gaussianLogSpatialPhase_mean_inner_band
#print axioms DGRHS.Gaussian.integral_gaussianLogSpatialPhase_mean_inner_band
#check @DGRHS.Gaussian.integral_gaussianLogSpatialPhaseMean_sq_band
#print axioms DGRHS.Gaussian.integral_gaussianLogSpatialPhaseMean_sq_band
#check @DGRHS.Gaussian.integral_gaussianLogCenteredPhase_inner_band
#print axioms DGRHS.Gaussian.integral_gaussianLogCenteredPhase_inner_band
#check @DGRHS.Gaussian.integral_gaussianLogCenteredPhase_sq_band
#print axioms DGRHS.Gaussian.integral_gaussianLogCenteredPhase_sq_band
