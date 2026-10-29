import DGRHS.Gaussian.GaussianLogBandCentering

/-! Supporting development: actual jointly measurable spatially centered Fourier phase.
This does not assert square integrability under the infinite scale measure. -/
noncomputable section
open MeasureTheory Real
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianLogSpatialPhase (x : EuclideanSpace ℝ ι) (p : ℝ × (ι → ℝ)) : ℂ :=
  gaussianScaleMixtureCharacter (gaussianRieszEuclideanCoordinates x) p

def gaussianLogSpatialPhaseMean (μ : Measure (EuclideanSpace ℝ ι)) (p : ℝ × (ι → ℝ)) : ℂ :=
  ∫ x,gaussianLogSpatialPhase x p ∂μ

def gaussianLogCenteredPhase (μ : Measure (EuclideanSpace ℝ ι))
    (x : EuclideanSpace ℝ ι) (p : ℝ × (ι → ℝ)) : ℂ :=
  gaussianLogSpatialPhase x p-gaussianLogSpatialPhaseMean μ p

lemma norm_gaussianLogSpatialPhase (x : EuclideanSpace ℝ ι) (p : ℝ × (ι → ℝ)) :
    ‖gaussianLogSpatialPhase x p‖ = 1 := norm_gaussianScaleMixtureCharacter _ _

lemma measurable_gaussianLogSpatialPhase_joint :
    Measurable (fun q : EuclideanSpace ℝ ι × (ℝ × (ι → ℝ)) => gaussianLogSpatialPhase q.1 q.2) := by
  classical
  unfold gaussianLogSpatialPhase gaussianScaleMixtureCharacter gaussianRieszEuclideanCoordinates
    finiteGaussianFourierCharacter finiteFeatureEvaluation
  fun_prop

lemma integrable_gaussianLogSpatialPhase (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (p : ℝ × (ι → ℝ)) : Integrable (fun x => gaussianLogSpatialPhase x p) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_gaussianLogSpatialPhase_joint.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => (norm_gaussianLogSpatialPhase x p).le)

lemma norm_gaussianLogSpatialPhaseMean_le (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (p : ℝ × (ι → ℝ)) : ‖gaussianLogSpatialPhaseMean μ p‖ ≤ 1 := by
  unfold gaussianLogSpatialPhaseMean
  have hb : ‖∫ x, gaussianLogSpatialPhase x p ∂μ‖ ≤ ∫ x, ‖gaussianLogSpatialPhase x p‖ ∂μ :=
    norm_integral_le_integral_norm (fun x => gaussianLogSpatialPhase x p)
  simpa only [norm_gaussianLogSpatialPhase,integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] using hb

lemma stronglyMeasurable_gaussianLogCenteredPhase_joint (μ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ] :
    StronglyMeasurable (fun q : EuclideanSpace ℝ ι × (ℝ × (ι → ℝ)) => gaussianLogCenteredPhase μ q.1 q.2) := by
  have hm : StronglyMeasurable (gaussianLogSpatialPhaseMean μ) :=
    measurable_gaussianLogSpatialPhase_joint.stronglyMeasurable.integral_prod_left'
  exact measurable_gaussianLogSpatialPhase_joint.stronglyMeasurable.sub
    (hm.comp_measurable measurable_snd)

lemma norm_gaussianLogCenteredPhase_le (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (x : EuclideanSpace ℝ ι) (p : ℝ × (ι → ℝ)) : ‖gaussianLogCenteredPhase μ x p‖ ≤ 2 := by
  have h := norm_sub_le (gaussianLogSpatialPhase x p) (gaussianLogSpatialPhaseMean μ p)
  rw [norm_gaussianLogSpatialPhase] at h
  exact h.trans (by linarith [norm_gaussianLogSpatialPhaseMean_le μ p])

lemma integral_gaussianLogCenteredPhase_eq_zero (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (p : ℝ × (ι → ℝ)) : (∫ x,gaussianLogCenteredPhase μ x p ∂μ) = 0 := by
  unfold gaussianLogCenteredPhase
  rw [integral_sub (integrable_gaussianLogSpatialPhase μ p) (integrable_const _)]
  simp [gaussianLogSpatialPhaseMean]

end DGRHS.Gaussian

#check @DGRHS.Gaussian.gaussianLogSpatialPhase
#print axioms DGRHS.Gaussian.gaussianLogSpatialPhase
#check @DGRHS.Gaussian.gaussianLogSpatialPhaseMean
#print axioms DGRHS.Gaussian.gaussianLogSpatialPhaseMean
#check @DGRHS.Gaussian.gaussianLogCenteredPhase
#print axioms DGRHS.Gaussian.gaussianLogCenteredPhase
#check @DGRHS.Gaussian.norm_gaussianLogSpatialPhase
#print axioms DGRHS.Gaussian.norm_gaussianLogSpatialPhase
#check @DGRHS.Gaussian.measurable_gaussianLogSpatialPhase_joint
#print axioms DGRHS.Gaussian.measurable_gaussianLogSpatialPhase_joint
#check @DGRHS.Gaussian.integrable_gaussianLogSpatialPhase
#print axioms DGRHS.Gaussian.integrable_gaussianLogSpatialPhase
#check @DGRHS.Gaussian.norm_gaussianLogSpatialPhaseMean_le
#print axioms DGRHS.Gaussian.norm_gaussianLogSpatialPhaseMean_le
#check @DGRHS.Gaussian.stronglyMeasurable_gaussianLogCenteredPhase_joint
#print axioms DGRHS.Gaussian.stronglyMeasurable_gaussianLogCenteredPhase_joint
#check @DGRHS.Gaussian.norm_gaussianLogCenteredPhase_le
#print axioms DGRHS.Gaussian.norm_gaussianLogCenteredPhase_le
#check @DGRHS.Gaussian.integral_gaussianLogCenteredPhase_eq_zero
#print axioms DGRHS.Gaussian.integral_gaussianLogCenteredPhase_eq_zero
