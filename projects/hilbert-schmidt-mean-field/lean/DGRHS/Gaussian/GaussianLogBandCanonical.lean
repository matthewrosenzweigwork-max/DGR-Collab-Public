import DGRHS.Gaussian.GaussianLogBandCentering

/-! Actual bounded/canonical finite logarithmic bands for
an arbitrary probability source, derived from the same centered Fourier feature. -/
noncomputable section
open MeasureTheory Real
open scoped BigOperators ENNReal
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

lemma gaussianLogBandPair_symmetric (η δ : ℝ) (x y : EuclideanSpace ℝ ι) :
    gaussianLogBandPair η δ (x,y) = gaussianLogBandPair η δ (y,x) := by
  unfold gaussianLogBandPair gaussianLogBand
  rw [norm_sub_rev]

lemma gaussianLogCenteredBand_symmetric (η δ : ℝ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] (x y : EuclideanSpace ℝ ι) :
    hoeffdingCentered μ (gaussianLogBandPair η δ) (x,y) =
      hoeffdingCentered μ (gaussianLogBandPair η δ) (y,x) :=
  DGRHS.centeredKernel_symmetric μ (fun x y => gaussianLogBandPair η δ (x,y))
    (gaussianLogBandPair_symmetric η δ) x y

lemma stronglyMeasurable_gaussianLogBandPair (η δ : ℝ) (hη : 0 < η) :
    StronglyMeasurable (gaussianLogBandPair (ι := ι) η δ) := by
  have h1 : StronglyMeasurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      gaussianLogBandFeature η δ hη p.1) :=
    (stronglyMeasurable_gaussianLogBandFeature η δ hη).comp_measurable measurable_fst
  have h2 : StronglyMeasurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      gaussianLogBandFeature η δ hη p.2) :=
    (stronglyMeasurable_gaussianLogBandFeature η δ hη).comp_measurable measurable_snd
  have hm : StronglyMeasurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      inner ℝ (gaussianLogBandFeature η δ hη p.1) (gaussianLogBandFeature η δ hη p.2)) := h1.inner h2
  change StronglyMeasurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => gaussianLogBand η δ (p.1-p.2))
  simpa only [inner_gaussianLogBandFeature] using hm

lemma gaussianLogCenteredBand_canonical (η δ : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    ∀ᵐ x ∂μ,∫ y,hoeffdingCentered μ (gaussianLogBandPair η δ) (x,y) ∂μ = 0 :=
  DGRHS.integral_centeredKernel_right μ (fun x y => gaussianLogBandPair η δ (x,y))
    (integrable_gaussianLogBandPair η δ hη hηδ μ)

lemma norm_centeredGaussianLogBandFeature_le (η δ : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] (x : EuclideanSpace ℝ ι) :
    ‖centeredGaussianLogBandFeature η δ hη μ x‖ ≤
      2*‖gaussianLogBandFeature (ι := ι) η δ hη 0‖ := by
  have hi := integrable_gaussianLogBandFeature (ι := ι) η δ hη hηδ μ
  have hm : ‖∫ y,gaussianLogBandFeature η δ hη y ∂μ‖ ≤
      ‖gaussianLogBandFeature (ι := ι) η δ hη 0‖ := by
    calc
      _ ≤ ∫ y,‖gaussianLogBandFeature η δ hη y‖ ∂μ := norm_integral_le_integral_norm _
      _ = _ := by simp_rw [norm_gaussianLogBandFeature_eq η δ hη hηδ]; simp
  unfold centeredGaussianLogBandFeature
  exact (norm_sub_le _ _).trans (by
    rw [norm_gaussianLogBandFeature_eq η δ hη hηδ x]
    linarith)

lemma norm_sq_centeredGaussianLogBandFeature_le (η δ : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] (x : EuclideanSpace ℝ ι) :
    ‖centeredGaussianLogBandFeature η δ hη μ x‖^2 ≤ 4*Real.log (δ/η) := by
  have hb := pow_le_pow_left₀ (norm_nonneg _)
    (norm_centeredGaussianLogBandFeature_le η δ hη hηδ μ x) 2
  rw [mul_pow,norm_sq_gaussianLogBandFeature η δ hη hηδ] at hb
  norm_num only at hb
  exact hb

lemma norm_gaussianLogCenteredBand_le (η δ : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    ‖hoeffdingCentered μ (gaussianLogBandPair η δ) p‖ ≤ 4*Real.log (δ/η) := by
  rw [← inner_centeredGaussianLogBandFeature η δ hη hηδ μ p.1 p.2]
  calc
    _ ≤ ‖centeredGaussianLogBandFeature η δ hη μ p.1‖ *
        ‖centeredGaussianLogBandFeature η δ hη μ p.2‖ := norm_inner_le_norm _ _
    _ ≤ (2*‖gaussianLogBandFeature (ι := ι) η δ hη 0‖) *
        (2*‖gaussianLogBandFeature (ι := ι) η δ hη 0‖) :=
      mul_le_mul (norm_centeredGaussianLogBandFeature_le η δ hη hηδ μ p.1)
        (norm_centeredGaussianLogBandFeature_le η δ hη hηδ μ p.2) (norm_nonneg _) (by positivity)
    _ = _ := by
      have h0 := norm_sq_gaussianLogBandFeature (ι := ι) η δ hη hηδ 0
      nlinarith

lemma memLp_infty_gaussianLogCenteredBand (η δ : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    MemLp (hoeffdingCentered μ (gaussianLogBandPair η δ)) ∞ (μ.prod μ) := by
  have hD : 0 ≤ 4*Real.log (δ/η) := by
    have h0 := norm_sq_gaussianLogBandFeature (ι := ι) η δ hη hηδ 0
    nlinarith [sq_nonneg ‖gaussianLogBandFeature (ι := ι) η δ hη 0‖]
  apply (memLp_const (4*Real.log (δ/η))).of_le
    (stronglyMeasurable_hoeffdingCentered μ _ (stronglyMeasurable_gaussianLogBandPair η δ hη)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by
    rw [Real.norm_of_nonneg hD]
    exact norm_gaussianLogCenteredBand_le η δ hη hηδ μ p)

lemma gaussianLogCenteredBand_particle_cap (η δ : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 1 ≤ n) (ω : Fin n → EuclideanSpace ℝ ι) :
    iidNegativeStatistic n (hoeffdingCentered μ (gaussianLogBandPair η δ)) ω ≤ 2*Real.log (δ/η) := by
  have h := gaussianLogCenteredBand_particle_diagonal_cap η δ hη hηδ μ n hn ω
  have hs : (∑ i : Fin n,‖centeredGaussianLogBandFeature η δ hη μ (ω i)‖^2) ≤
      (n : ℝ)*(4*Real.log (δ/η)) := by
    calc
      _ ≤ ∑ _ : Fin n,4*Real.log (δ/η) :=
        Finset.sum_le_sum (fun i hi => norm_sq_centeredGaussianLogBandFeature_le η δ hη hηδ μ (ω i))
      _ = _ := by simp
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hn)
  apply h.trans
  rw [div_le_iff₀ (by positivity : 0 < 2*(n : ℝ))]
  nlinarith

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianLogBandPair_symmetric
#print axioms DGRHS.Gaussian.gaussianLogBandPair_symmetric
#check DGRHS.Gaussian.gaussianLogCenteredBand_symmetric
#print axioms DGRHS.Gaussian.gaussianLogCenteredBand_symmetric
#check DGRHS.Gaussian.stronglyMeasurable_gaussianLogBandPair
#print axioms DGRHS.Gaussian.stronglyMeasurable_gaussianLogBandPair
#check DGRHS.Gaussian.gaussianLogCenteredBand_canonical
#print axioms DGRHS.Gaussian.gaussianLogCenteredBand_canonical
#check DGRHS.Gaussian.norm_centeredGaussianLogBandFeature_le
#print axioms DGRHS.Gaussian.norm_centeredGaussianLogBandFeature_le
#check DGRHS.Gaussian.norm_sq_centeredGaussianLogBandFeature_le
#print axioms DGRHS.Gaussian.norm_sq_centeredGaussianLogBandFeature_le
#check DGRHS.Gaussian.norm_gaussianLogCenteredBand_le
#print axioms DGRHS.Gaussian.norm_gaussianLogCenteredBand_le
#check DGRHS.Gaussian.memLp_infty_gaussianLogCenteredBand
#print axioms DGRHS.Gaussian.memLp_infty_gaussianLogCenteredBand
#check DGRHS.Gaussian.gaussianLogCenteredBand_particle_cap
#print axioms DGRHS.Gaussian.gaussianLogCenteredBand_particle_cap
