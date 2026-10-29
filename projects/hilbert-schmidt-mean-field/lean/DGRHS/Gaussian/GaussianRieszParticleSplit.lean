import DGRHS.Gaussian.GaussianRieszNearLowerBound
import DGRHS.Gaussian.GaussianRieszMasterNorms

/-! Actual cutoff decomposition after proper Hoeffding centering, and the
particle low-frequency cap. AE assertions transfer only through distinct iid
coordinates. This module supplies the physical comparison, not an assumed tail. -/
noncomputable section
open MeasureTheory Real
open scoped BigOperators ENNReal
namespace DGRHS.Gaussian
open DGRHS.Concentration

lemma ae_hoeffdingCentered_add {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (W V : X × X → ℝ)
    (hW : Integrable W (μ.prod μ)) (hV : Integrable V (μ.prod μ)) :
    hoeffdingCentered μ (W+V) =ᵐ[μ.prod μ] hoeffdingCentered μ W+hoeffdingCentered μ V := by
  filter_upwards [
    (measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hW.prod_right_ae,
    (measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hV.prod_right_ae,
    (measurePreserving_snd (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hW.prod_left_ae,
    (measurePreserving_snd (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hV.prod_left_ae] with p hWx hVx hWy hVy
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  simp only [Pi.add_apply]
  rw [integral_add hWx hVx,integral_add hWy hVy,integral_add hW hV]
  ring

variable {ι : Type*} [Fintype ι]

lemma gaussianRieszCenteredTruncated_particle_cap (s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 1 ≤ n) (ω : Fin n → EuclideanSpace ℝ ι) :
    iidNegativeStatistic n (hoeffdingCentered μ (gaussianRieszTruncatedPair s δ)) ω ≤
      2*(gaussianRieszSourceCoefficient s/s*δ^(-s)) := by
  classical
  let k := centeredGaussianRieszEuclideanFourierFeature (ι := ι) s δ hs hδ μ
  have he (x y : EuclideanSpace ℝ ι) :
      hoeffdingCentered μ (gaussianRieszTruncatedPair s δ) (x,y) = inner ℝ (k x) (k y) := by
    rw [gaussianRieszCenteredTruncatedPair_eq_source s δ hs hδ μ (x,y)]
    exact (inner_centeredGaussianRieszEuclideanFourierFeature s δ hs hδ μ x y).symm
  unfold iidNegativeStatistic iidCoupledSum DGRHS.Decoupling.offDiagonalSum
  simp_rw [he]
  simp only [ite_not]
  rw [feature_particle_off_diagonal_sum]
  have hb : (∑ i : Fin n, ‖k (ω i)‖^2) ≤ (n : ℝ)*
      (4*(gaussianRieszSourceCoefficient s/s*δ^(-s))) := by
    calc
      _ ≤ ∑ _ : Fin n, 4*(gaussianRieszSourceCoefficient s/s*δ^(-s)) :=
        Finset.sum_le_sum (fun i hi => norm_sq_centeredGaussianRieszEuclideanFourierFeature_le s δ hs hδ μ (ω i))
      _ = _ := by simp
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hn)
  rw [div_le_iff₀ (by positivity : 0 < 2*(n : ℝ))]
  nlinarith [sq_nonneg ‖∑ i : Fin n,k (ω i)‖]

lemma ae_gaussianRieszCenteredTruncated_split (s η α δ : ℝ) (hs : 0 < s)
    (hη : 0 < η) (hηα : η ≤ α) (hαδ : α ≤ δ)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszTruncatedPair s η)
      =ᵐ[(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)]
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszTruncatedPair s δ) +
          hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszBandPair s α δ)) +
            hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszNearPair s η α) := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := gaussianRieszTruncatedPair (ι := ι) s δ
  let V := gaussianRieszBandPair (ι := ι) s α δ
  let R := gaussianRieszNearPair (ι := ι) s η α
  have hα := lt_of_lt_of_le hη hηα
  have hδ := lt_of_lt_of_le hα hαδ
  have hW : Integrable W (μ.prod μ) := (memLp_gaussianRieszTruncatedPair s δ hs hδ μ).integrable (by norm_num)
  have hV : Integrable V (μ.prod μ) := (memLp_gaussianRieszBandPair s α δ hs hα hαδ ha ρ M hM hρ).integrable (by norm_num)
  have heR := ae_gaussianRieszNearPair_eq_band s η α hs hη hηα ha ρ
  have hR : Integrable R (μ.prod μ) :=
    ((memLp_gaussianRieszBandPair s η α hs hη hηα ha ρ M hM hρ).integrable (by norm_num)).congr heR.symm
  have he : gaussianRieszTruncatedPair s η =ᵐ[μ.prod μ] (W+V)+R := by
    filter_upwards [heR] with p hp
    change gaussianRieszTruncatedPair s η p = W p+V p+R p
    change gaussianRieszTruncatedPair s η p = W p+V p+gaussianRieszNearPair s η α p
    rw [hp]
    unfold W V gaussianRieszTruncatedPair gaussianRieszBandPair gaussianRieszEuclideanBand
    ring
  have h1 := ae_hoeffdingCentered_congr μ _ _ he
  have h2 := ae_hoeffdingCentered_add μ (W+V) R (hW.add hV) hR
  have h3 := ae_hoeffdingCentered_add μ W V hW hV
  filter_upwards [h1,h2,h3] with p hp1 hp2 hp3
  change _ = (hoeffdingCentered μ W p+hoeffdingCentered μ V p)+hoeffdingCentered μ R p
  rw [hp1,hp2]
  simp only [Pi.add_apply]
  rw [hp3]
  rfl

end DGRHS.Gaussian

#check DGRHS.Gaussian.ae_hoeffdingCentered_add
#print axioms DGRHS.Gaussian.ae_hoeffdingCentered_add

#check DGRHS.Gaussian.gaussianRieszCenteredTruncated_particle_cap
#print axioms DGRHS.Gaussian.gaussianRieszCenteredTruncated_particle_cap

#check DGRHS.Gaussian.ae_gaussianRieszCenteredTruncated_split
#print axioms DGRHS.Gaussian.ae_gaussianRieszCenteredTruncated_split
