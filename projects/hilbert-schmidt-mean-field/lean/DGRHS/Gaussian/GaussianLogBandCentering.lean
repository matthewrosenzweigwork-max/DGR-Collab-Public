import DGRHS.Gaussian.GaussianLogBand
import DGRHS.Gaussian.HoeffdingRowL2
import DGRHS.Gaussian.FeatureRatePhysical
import DGRHS.Gaussian.PhysicalStatisticAlgebra

/-! The actual finite logarithmic band's Bochner centered
Fourier feature, Gram identity and empirical diagonal correction. No Gaussian
covariance or diagonal cap is supplied as an assumption. -/
noncomputable section
open MeasureTheory Real
open scoped BigOperators
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

def gaussianLogBandPair (η δ : ℝ) (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : ℝ :=
  gaussianLogBand η δ (p.1-p.2)

lemma norm_gaussianLogBandFeature_eq (η δ : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (x : EuclideanSpace ℝ ι) :
    ‖gaussianLogBandFeature η δ hη x‖ = ‖gaussianLogBandFeature (ι := ι) η δ hη 0‖ := by
  have h1 := norm_sq_gaussianLogBandFeature η δ hη hηδ x
  have h0 := norm_sq_gaussianLogBandFeature (ι := ι) η δ hη hηδ 0
  nlinarith [norm_nonneg (gaussianLogBandFeature η δ hη x),
    norm_nonneg (gaussianLogBandFeature (ι := ι) η δ hη 0)]

lemma integrable_gaussianLogBandFeature (η δ : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    Integrable (gaussianLogBandFeature η δ hη) μ :=
  (integrable_const ‖gaussianLogBandFeature (ι := ι) η δ hη 0‖).mono'
    (stronglyMeasurable_gaussianLogBandFeature η δ hη).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => (norm_gaussianLogBandFeature_eq η δ hη hηδ x).le))

lemma integrable_gaussianLogBandPair (η δ : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    Integrable (gaussianLogBandPair η δ) (μ.prod μ) := by
  have hm : StronglyMeasurable (gaussianLogBandPair (ι := ι) η δ) := by
    change StronglyMeasurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      gaussianLogBand η δ (p.1-p.2))
    have hm1 : StronglyMeasurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
        gaussianLogBandFeature η δ hη p.1) :=
      (stronglyMeasurable_gaussianLogBandFeature η δ hη).comp_measurable measurable_fst
    have hm2 : StronglyMeasurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
        gaussianLogBandFeature η δ hη p.2) :=
      (stronglyMeasurable_gaussianLogBandFeature η δ hη).comp_measurable measurable_snd
    have hInner : StronglyMeasurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
        inner ℝ (gaussianLogBandFeature η δ hη p.1) (gaussianLogBandFeature η δ hη p.2)) := hm1.inner hm2
    simpa only [inner_gaussianLogBandFeature] using hInner
  apply (integrable_const (‖gaussianLogBandFeature (ι := ι) η δ hη 0‖^2)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by
    unfold gaussianLogBandPair
    rw [← inner_gaussianLogBandFeature η δ hη p.1 p.2]
    calc
      _ ≤ ‖gaussianLogBandFeature η δ hη p.1‖ * ‖gaussianLogBandFeature η δ hη p.2‖ := norm_inner_le_norm _ _
      _ = _ := by rw [norm_gaussianLogBandFeature_eq η δ hη hηδ p.1,
        norm_gaussianLogBandFeature_eq η δ hη hηδ p.2]; ring)

def centeredGaussianLogBandFeature (η δ : ℝ) (hη : 0 < η)
    (μ : Measure (EuclideanSpace ℝ ι)) (x : EuclideanSpace ℝ ι) :
    Lp ℂ 2 ((gaussianLogBandMeasure η δ).prod (finiteStandardGaussian ι)) :=
  gaussianLogBandFeature η δ hη x - ∫ y,gaussianLogBandFeature η δ hη y ∂μ

lemma inner_centeredGaussianLogBandFeature (η δ : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (a b : EuclideanSpace ℝ ι) :
    inner ℝ (centeredGaussianLogBandFeature η δ hη μ a)
      (centeredGaussianLogBandFeature η δ hη μ b) =
      hoeffdingCentered μ (gaussianLogBandPair η δ) (a,b) := by
  let κ := gaussianLogBandFeature (ι := ι) η δ hη
  let m := ∫ x,κ x ∂μ
  have hi : Integrable κ μ := integrable_gaussianLogBandFeature η δ hη hηδ μ
  have hp := integrable_gaussianLogBandPair η δ hη hηδ μ
  have hl (v : Lp ℂ 2 ((gaussianLogBandMeasure η δ).prod (finiteStandardGaussian ι))) :
      (∫ x,inner ℝ (κ x) v ∂μ) = inner ℝ m v := by
    simp_rw [real_inner_comm v (κ _)]
    rw [integral_inner hi]
    exact real_inner_comm _ _
  have hd : (∫ x,(∫ y,inner ℝ (κ x) (κ y) ∂μ) ∂μ) = inner ℝ m m := by
    simp_rw [integral_inner hi]
    exact hl m
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  rw [integral_prod _ hp]
  unfold gaussianLogBandPair
  simp_rw [← inner_gaussianLogBandFeature η δ hη]
  change inner ℝ (κ a-m) (κ b-m) = inner ℝ (κ a) (κ b) -
    (∫ y,inner ℝ (κ a) (κ y) ∂μ) - (∫ x,inner ℝ (κ x) (κ b) ∂μ) +
    (∫ x,(∫ y,inner ℝ (κ x) (κ y) ∂μ) ∂μ)
  rw [inner_sub_left,inner_sub_right,inner_sub_right,integral_inner hi,hl,hd]
  ring

lemma norm_sq_centeredGaussianLogBandFeature_eq (η δ : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (x : EuclideanSpace ℝ ι) :
    ‖centeredGaussianLogBandFeature η δ hη μ x‖^2 = Real.log (δ/η) -
      2*(∫ y,gaussianLogBandPair η δ (x,y) ∂μ) + ∫ p,gaussianLogBandPair η δ p ∂μ.prod μ := by
  have hg := inner_centeredGaussianLogBandFeature η δ hη hηδ μ x x
  have hraw := inner_gaussianLogBandFeature η δ hη x x
  have hdiag : gaussianLogBand (ι := ι) η δ 0 = Real.log (δ/η) := by
    rw [real_inner_self_eq_norm_sq,sub_self] at hraw
    exact hraw.symm.trans (norm_sq_gaussianLogBandFeature η δ hη hηδ x)
  have hs : (fun y => gaussianLogBandPair η δ (y,x)) = (fun y => gaussianLogBandPair η δ (x,y)) := by
    funext y; unfold gaussianLogBandPair gaussianLogBand; rw [norm_sub_rev]
  rw [real_inner_self_eq_norm_sq] at hg
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential at hg
  rw [hs] at hg
  change ‖centeredGaussianLogBandFeature η δ hη μ x‖^2 =
    gaussianLogBand η δ (x-x) - (∫ y,gaussianLogBandPair η δ (x,y) ∂μ) -
      (∫ y,gaussianLogBandPair η δ (x,y) ∂μ) + ∫ p,gaussianLogBandPair η δ p ∂μ.prod μ at hg
  rw [sub_self,hdiag] at hg
  linarith

lemma gaussianLogCenteredBand_particle_diagonal_cap (η δ : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 1 ≤ n) (ω : Fin n → EuclideanSpace ℝ ι) :
    iidNegativeStatistic n (hoeffdingCentered μ (gaussianLogBandPair η δ)) ω ≤
      (∑ i : Fin n,‖centeredGaussianLogBandFeature η δ hη μ (ω i)‖^2)/(2*(n : ℝ)) := by
  classical
  let k := centeredGaussianLogBandFeature η δ hη μ
  unfold iidNegativeStatistic iidCoupledSum DGRHS.Decoupling.offDiagonalSum
  simp_rw [← inner_centeredGaussianLogBandFeature η δ hη hηδ μ]
  change -(∑ i : Fin n,∑ j : Fin n,if i ≠ j then inner ℝ (k (ω i)) (k (ω j)) else 0) /
    (2*(n : ℝ)) ≤ (∑ i : Fin n,‖k (ω i)‖^2)/(2*(n : ℝ))
  simp_rw [ite_not]
  rw [feature_particle_off_diagonal_sum]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [sq_nonneg ‖∑ i : Fin n,k (ω i)‖]

end DGRHS.Gaussian

#check @DGRHS.Gaussian.gaussianLogBandPair
#print axioms DGRHS.Gaussian.gaussianLogBandPair

#check @DGRHS.Gaussian.norm_gaussianLogBandFeature_eq
#print axioms DGRHS.Gaussian.norm_gaussianLogBandFeature_eq

#check @DGRHS.Gaussian.integrable_gaussianLogBandFeature
#print axioms DGRHS.Gaussian.integrable_gaussianLogBandFeature

#check @DGRHS.Gaussian.integrable_gaussianLogBandPair
#print axioms DGRHS.Gaussian.integrable_gaussianLogBandPair

#check @DGRHS.Gaussian.centeredGaussianLogBandFeature
#print axioms DGRHS.Gaussian.centeredGaussianLogBandFeature

#check @DGRHS.Gaussian.inner_centeredGaussianLogBandFeature
#print axioms DGRHS.Gaussian.inner_centeredGaussianLogBandFeature

#check @DGRHS.Gaussian.norm_sq_centeredGaussianLogBandFeature_eq
#print axioms DGRHS.Gaussian.norm_sq_centeredGaussianLogBandFeature_eq

#check @DGRHS.Gaussian.gaussianLogCenteredBand_particle_diagonal_cap
#print axioms DGRHS.Gaussian.gaussianLogCenteredBand_particle_diagonal_cap

