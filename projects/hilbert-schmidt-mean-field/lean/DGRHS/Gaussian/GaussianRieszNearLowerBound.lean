import DGRHS.Gaussian.GaussianRieszBandScaling
import DGRHS.Gaussian.GaussianShortRangeConvolution

/-! Actual proper centered near-field lower bound, with source product-AE
positivity derived off the singular origin and never from a diagonal slice. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianRieszNearPair (s η α : ℝ) (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : ℝ :=
  gaussianRieszShortPair s α p - gaussianRieszShortPair s η p

lemma ae_gaussianRieszNearPair_eq_band (s η α : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηα : η ≤ α) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    gaussianRieszNearPair s η α =ᵐ[(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)]
      gaussianRieszBandPair s η α := by
  have hc : 0 < Fintype.card ι := by
    exact_mod_cast (show (0 : ℝ) < (Fintype.card ι : ℝ) by linarith)
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  filter_upwards [ae_gaussianRieszDensity_pair_ne ρ] with p hp
  have h1 := gaussianRieszEuclidean_full_short_long_split s η hs hη _ (sub_ne_zero.mpr hp)
  have h2 := gaussianRieszEuclidean_full_short_long_split s α hs (lt_of_lt_of_le hη hηα) _ (sub_ne_zero.mpr hp)
  unfold gaussianRieszNearPair gaussianRieszShortPair gaussianRieszBandPair gaussianRieszEuclideanBand
  linarith

lemma gaussianRieszNearPair_zero (s η : ℝ) : gaussianRieszNearPair (ι := ι) s η η = 0 := by
  funext p
  simp [gaussianRieszNearPair]

lemma ae_gaussianRieszCenteredNearPair_lower_bound (s η α : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηα : η ≤ α) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ∀ᵐ p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ),
      -hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszNearPair s η α) p ≤
        2*(M*(gaussianRieszSourceCoefficient s*(2*Real.pi)^((Fintype.card ι : ℝ)/2) /
          ((Fintype.card ι : ℝ)-s)*α^((Fintype.card ι : ℝ)-s))) := by
  let μ := gaussianRieszDensityMeasure ρ
  have hα := lt_of_lt_of_le hη hηα
  have ha1 : 0 < (Fintype.card ι : ℝ)-s := by
    have hc : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
    linarith
  have he := ae_gaussianRieszNearPair_eq_band s η α hs hη hηα ha ρ
  have hn : ∀ᵐ p ∂μ.prod μ, 0 ≤ gaussianRieszNearPair s η α p := by
    filter_upwards [he] with p hp
    rw [hp]
    exact gaussianRieszEuclideanBand_nonneg s η α hs hη hηα _
  have hm : 0 ≤ ∫ p,gaussianRieszNearPair s η α p ∂μ.prod μ := integral_nonneg_of_ae hn
  have hconv (x : EuclideanSpace ℝ ι) :
      (∫ y,gaussianRieszNearPair s η α (x,y) ∂μ) ≤
        M*(gaussianRieszSourceCoefficient s*(2*Real.pi)^((Fintype.card ι : ℝ)/2) /
          ((Fintype.card ι : ℝ)-s)*α^((Fintype.card ι : ℝ)-s)) := by
    unfold gaussianRieszNearPair gaussianRieszShortPair
    rw [integral_sub (integrable_gaussianRieszShortRange_convolution s α hα ha1 ρ M hρ x)
      (integrable_gaussianRieszShortRange_convolution s η hη ha1 ρ M hρ x)]
    have hb := gaussianRieszShortRange_convolution_le s α hs hα ha1 ρ M hM hρ x
    have hp : 0 ≤ ∫ y,gaussianRieszEuclideanShortRange s η (x-y) ∂μ :=
      integral_nonneg (fun y => gaussianRieszEuclideanShortRange_nonneg s η hs _)
    linarith
  have hsym (x y : EuclideanSpace ℝ ι) :
      gaussianRieszNearPair s η α (x,y)=gaussianRieszNearPair s η α (y,x) := by
    unfold gaussianRieszNearPair gaussianRieszShortPair
    rw [gaussianRieszShortRange_symmetric s α x y,gaussianRieszShortRange_symmetric s η x y]
  filter_upwards [hn] with p hp
  have h1 := hconv p.1
  have h2 := hconv p.2
  have he2 : (fun x => gaussianRieszNearPair s η α (x,p.2))=
      (fun x => gaussianRieszNearPair s η α (p.2,x)) := funext (fun x => hsym x p.2)
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  change -(gaussianRieszNearPair s η α p - (∫ y,gaussianRieszNearPair s η α (p.1,y) ∂μ) -
    (∫ x,gaussianRieszNearPair s η α (x,p.2) ∂μ) + (∫ z,gaussianRieszNearPair s η α z ∂μ.prod μ)) ≤ _
  rw [he2]
  linarith

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianRieszNearPair
#print axioms DGRHS.Gaussian.gaussianRieszNearPair

#check DGRHS.Gaussian.ae_gaussianRieszNearPair_eq_band
#print axioms DGRHS.Gaussian.ae_gaussianRieszNearPair_eq_band

#check DGRHS.Gaussian.gaussianRieszNearPair_zero
#print axioms DGRHS.Gaussian.gaussianRieszNearPair_zero

#check DGRHS.Gaussian.ae_gaussianRieszCenteredNearPair_lower_bound
#print axioms DGRHS.Gaussian.ae_gaussianRieszCenteredNearPair_lower_bound
