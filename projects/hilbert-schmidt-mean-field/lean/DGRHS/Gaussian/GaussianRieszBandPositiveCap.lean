import DGRHS.Gaussian.GaussianRieszBandCenteringFeature
import DGRHS.Gaussian.FeatureRatePhysical

/-! Actual positive-band deterministic particle cap and master canonical/bounded
conditions. The centered Gram identity is proved for the same physical band. -/
noncomputable section
open MeasureTheory Real
open scoped BigOperators ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma gaussianRieszBandPair_symmetric (s η δ : ℝ) (x y : EuclideanSpace ℝ ι) :
    gaussianRieszBandPair s η δ (x,y) = gaussianRieszBandPair s η δ (y,x) := by
  unfold gaussianRieszBandPair gaussianRieszEuclideanBand gaussianRieszEuclideanTruncation
  rw [norm_sub_rev]

lemma gaussianRieszCenteredBand_symmetric (s η δ : ℝ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] (x y : EuclideanSpace ℝ ι) :
    hoeffdingCentered μ (gaussianRieszBandPair s η δ) (x,y) =
      hoeffdingCentered μ (gaussianRieszBandPair s η δ) (y,x) :=
  DGRHS.centeredKernel_symmetric μ (fun x y => gaussianRieszBandPair s η δ (x,y))
    (gaussianRieszBandPair_symmetric s η δ) x y

lemma gaussianRieszCenteredBand_canonical (s η δ : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ∀ᵐ x ∂gaussianRieszDensityMeasure ρ,
      ∫ y,hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszBandPair s η δ) (x,y)
        ∂gaussianRieszDensityMeasure ρ = 0 :=
  DGRHS.integral_centeredKernel_right _ (fun x y => gaussianRieszBandPair s η δ (x,y))
    ((memLp_gaussianRieszBandPair s η δ hs hη hηδ ha ρ M hM hρ).integrable (by norm_num))

lemma norm_sq_centeredGaussianRieszEuclideanBandFeature_le (s η δ : ℝ) (hs : 0 < s) (hη : 0 < η)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] (x : EuclideanSpace ℝ ι) :
    ‖centeredGaussianRieszEuclideanBandFeature s η δ hs hη μ x‖^2 ≤
      4*(gaussianRieszSourceCoefficient s/s*η^(-s)) := by
  have hD : 0 ≤ gaussianRieszSourceCoefficient s/s*η^(-s) := by
    have hc := (gaussianRieszSourceCoefficient_pos s hs).le
    positivity
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (norm_centeredGaussianRieszEuclideanBandFeature_le s η δ hs hη μ x) 2
  simpa only [mul_pow, Real.sq_sqrt hD, show (2 : ℝ)^2=4 by norm_num] using h

lemma norm_gaussianRieszCenteredBand_le (s η δ : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    ‖hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszBandPair s η δ) p‖ ≤
      4*(gaussianRieszSourceCoefficient s/s*η^(-s)) := by
  have hD : 0 ≤ gaussianRieszSourceCoefficient s/s*η^(-s) := by
    have hc := (gaussianRieszSourceCoefficient_pos s hs).le
    positivity
  rw [← inner_centeredGaussianRieszEuclideanBandFeature s η δ hs hη hηδ ha ρ M hM hρ p.1 p.2]
  calc
    _ ≤ ‖centeredGaussianRieszEuclideanBandFeature s η δ hs hη (gaussianRieszDensityMeasure ρ) p.1‖ *
        ‖centeredGaussianRieszEuclideanBandFeature s η δ hs hη (gaussianRieszDensityMeasure ρ) p.2‖ := norm_inner_le_norm _ _
    _ ≤ (2*Real.sqrt (gaussianRieszSourceCoefficient s/s*η^(-s))) *
        (2*Real.sqrt (gaussianRieszSourceCoefficient s/s*η^(-s))) :=
      mul_le_mul (norm_centeredGaussianRieszEuclideanBandFeature_le s η δ hs hη _ p.1)
        (norm_centeredGaussianRieszEuclideanBandFeature_le s η δ hs hη _ p.2) (norm_nonneg _) (by positivity)
    _ = _ := by nlinarith [Real.sq_sqrt hD]

lemma memLp_infty_gaussianRieszCenteredBand (s η δ : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    MemLp (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszBandPair s η δ)) ∞
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  have hD : 0 ≤ 4*(gaussianRieszSourceCoefficient s/s*η^(-s)) := by
    have hc := (gaussianRieszSourceCoefficient_pos s hs).le
    positivity
  apply (memLp_const (4*(gaussianRieszSourceCoefficient s/s*η^(-s)))).of_le
    (stronglyMeasurable_hoeffdingCentered _ _
      (stronglyMeasurable_gaussianRieszBandPair s η δ hs hη hηδ)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  rw [Real.norm_of_nonneg hD]
  exact norm_gaussianRieszCenteredBand_le s η δ hs hη hηδ ha ρ M hM hρ p

lemma gaussianRieszCenteredBand_particle_cap (s η δ : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηδ : η ≤ δ) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (n : ℕ) (hn : 1 ≤ n) (ω : Fin n → EuclideanSpace ℝ ι) :
    -(∑ i : Fin n, ∑ j : Fin n, if i=j then 0 else
      hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszBandPair s η δ) (ω i,ω j)) /
        (2*(n : ℝ)) ≤ 2*(gaussianRieszSourceCoefficient s/s*η^(-s)) := by
  let k := centeredGaussianRieszEuclideanBandFeature (ι := ι) s η δ hs hη (gaussianRieszDensityMeasure ρ)
  simp_rw [← inner_centeredGaussianRieszEuclideanBandFeature s η δ hs hη hηδ ha ρ M hM hρ]
  change -(∑ i : Fin n, ∑ j : Fin n, if i=j then 0 else inner ℝ (k (ω i)) (k (ω j))) /
    (2*(n : ℝ)) ≤ _
  rw [feature_particle_off_diagonal_sum]
  have hb : (∑ i : Fin n, ‖k (ω i)‖^2) ≤ (n : ℝ)*
      (4*(gaussianRieszSourceCoefficient s/s*η^(-s))) := by
    calc
      _ ≤ ∑ _ : Fin n, 4*(gaussianRieszSourceCoefficient s/s*η^(-s)) :=
        Finset.sum_le_sum (fun i hi => norm_sq_centeredGaussianRieszEuclideanBandFeature_le s η δ hs hη _ (ω i))
      _ = _ := by simp
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hn)
  rw [div_le_iff₀ (by positivity : 0 < 2*(n : ℝ))]
  nlinarith [sq_nonneg ‖∑ i : Fin n,k (ω i)‖]

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianRieszBandPair_symmetric
#print axioms DGRHS.Gaussian.gaussianRieszBandPair_symmetric

#check DGRHS.Gaussian.gaussianRieszCenteredBand_symmetric
#print axioms DGRHS.Gaussian.gaussianRieszCenteredBand_symmetric

#check DGRHS.Gaussian.gaussianRieszCenteredBand_canonical
#print axioms DGRHS.Gaussian.gaussianRieszCenteredBand_canonical

#check DGRHS.Gaussian.norm_sq_centeredGaussianRieszEuclideanBandFeature_le
#print axioms DGRHS.Gaussian.norm_sq_centeredGaussianRieszEuclideanBandFeature_le

#check DGRHS.Gaussian.norm_gaussianRieszCenteredBand_le
#print axioms DGRHS.Gaussian.norm_gaussianRieszCenteredBand_le

#check DGRHS.Gaussian.memLp_infty_gaussianRieszCenteredBand
#print axioms DGRHS.Gaussian.memLp_infty_gaussianRieszCenteredBand

#check DGRHS.Gaussian.gaussianRieszCenteredBand_particle_cap
#print axioms DGRHS.Gaussian.gaussianRieszCenteredBand_particle_cap
