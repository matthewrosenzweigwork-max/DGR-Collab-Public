import DGRHS.Gaussian.GaussianLogBandScaling
import DGRHS.Gaussian.GaussianLogScaleCancellation
import DGRHS.Gaussian.GaussianLogParticleSplit

/-! Supporting development. Genuine finite-band logarithmic cutoff exponents.
These finite integrals include their actual Gram diagonal. Identifications
with literal full-minus-short kernels apply away from the origin or source-AE. -/
noncomputable section
open MeasureTheory Real Set
open scoped BigOperators
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

lemma gaussianLogBand_split (η α T : ℝ) (hη : 0 < η) (hηα : η ≤ α) (hαT : α ≤ T)
    (x : EuclideanSpace ℝ ι) :
    gaussianLogBand η T x = gaussianLogBand η α x+gaussianLogBand α T x := by
  have hi := integrable_gaussianLogBandProfile η T hη x
  have he := integral_add_compl (s := Iic α) measurableSet_Iic hi
  rw [compl_Iic,Measure.restrict_restrict measurableSet_Iic,Measure.restrict_restrict measurableSet_Ioi] at he
  have hA : Iic α ∩ Ioc η T = Ioc η α := by
    ext t
    simp only [mem_inter_iff,mem_Iic,mem_Ioc]
    constructor
    · intro ht;exact ⟨ht.2.1,ht.1⟩
    · intro ht;exact ⟨ht.2,ht.1,ht.2.trans hαT⟩
  have hB : Ioi α ∩ Ioc η T = Ioc α T := by
    ext t
    simp only [mem_inter_iff,mem_Ioi,mem_Ioc]
    constructor
    · intro ht;exact ⟨ht.1,ht.2.2⟩
    · intro ht;exact ⟨ht.1,hηα.trans_lt ht.1,ht.2⟩
  rw [hA,hB] at he
  exact he.symm

lemma gaussianLogBand_potential_split (η δ T : ℝ) (hη : 0 < η) (hηδ : η ≤ δ) (hδT : δ ≤ T)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] (x : EuclideanSpace ℝ ι) :
    (∫ y,gaussianLogBandPair η T (x,y) ∂μ) =
      (∫ y,gaussianLogBandPair η δ (x,y) ∂μ)+(∫ y,gaussianLogBandPair δ T (x,y) ∂μ) := by
  have he : (fun y => gaussianLogBandPair η T (x,y)) =
      (fun y => gaussianLogBandPair η δ (x,y)+gaussianLogBandPair δ T (x,y)) := by
    funext y
    exact gaussianLogBand_split η δ T hη hηδ hδT (x-y)
  rw [he]
  exact integral_add (integrable_gaussianLogBand_row η δ hη hηδ μ x)
    (integrable_gaussianLogBand_row δ T (hη.trans_le hηδ) hδT μ x)

lemma gaussianLogBand_pairMean_split (η δ T : ℝ) (hη : 0 < η) (hηδ : η ≤ δ) (hδT : δ ≤ T)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    (∫ p,gaussianLogBandPair η T p ∂μ.prod μ) =
      (∫ p,gaussianLogBandPair η δ p ∂μ.prod μ)+(∫ p,gaussianLogBandPair δ T p ∂μ.prod μ) := by
  have he : gaussianLogBandPair (ι := ι) η T = gaussianLogBandPair η δ+gaussianLogBandPair δ T := by
    funext p
    exact gaussianLogBand_split η δ T hη hηδ hδT (p.1-p.2)
  rw [he]
  simp only [Pi.add_apply]
  exact integral_add (integrable_gaussianLogBandPair η δ hη hηδ μ)
    (integrable_gaussianLogBandPair δ T (hη.trans_le hηδ) hδT μ)

def gaussianLogCutoffApproxExponent (μ : Measure (EuclideanSpace ℝ ι))
    (β η T : ℝ) (n : ℕ) (ω : Fin n → EuclideanSpace ℝ ι) : ℝ :=
  β*iidNegativeStatistic n (hoeffdingCentered μ (gaussianLogBandPair η T)) ω +
    β/(n : ℝ)*(∑ i : Fin n,∫ y,gaussianLogBandPair η T (ω i,y) ∂μ) -
    β/2*(∫ p,gaussianLogBandPair η T p ∂μ.prod μ) -β/2*gaussianLogCounterterm T

lemma gaussianLog_cutoff_low_diagonal_cancellation (η δ T β : ℝ)
    (hη : 0 < η) (hηδ : η ≤ δ) (hδT : δ ≤ T)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] (x : EuclideanSpace ℝ ι) :
    β*(∫ y,gaussianLogBandPair η T (x,y) ∂μ) +
      β/2*‖centeredGaussianLogBandFeature δ T (hη.trans_le hηδ) μ x‖^2 -
      β/2*(∫ p,gaussianLogBandPair η T p ∂μ.prod μ) -β/2*gaussianLogCounterterm T =
    β*(∫ y,gaussianLogBandPair η δ (x,y) ∂μ) +
      β/2*(Real.log (T/δ)-gaussianLogCounterterm T) -
      β/2*(∫ p,gaussianLogBandPair η δ p ∂μ.prod μ) := by
  rw [norm_sq_centeredGaussianLogBandFeature_eq δ T (hη.trans_le hηδ) hδT,
    gaussianLogBand_potential_split η δ T hη hηδ hδT μ x,
    gaussianLogBand_pairMean_split η δ T hη hηδ hδT μ]
  ring

lemma gaussianLogBand_potential_le_short_bound (η δ : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (x : EuclideanSpace ℝ ι) :
    (∫ y,gaussianLogBandPair η δ (x,y) ∂gaussianRieszDensityMeasure ρ) ≤
      M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*δ^(Fintype.card ι : ℝ)) := by
  let μ := gaussianRieszDensityMeasure ρ
  have hc : 0 < Fintype.card ι := by exact_mod_cast hd
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  letI : NullSingletonClass μ := by unfold μ gaussianRieszDensityMeasure;infer_instance
  have hi : Integrable (fun y => gaussianLogShortRange δ (x-y)) μ :=
    integrable_gaussianLogShortRange_convolution δ (hη.trans_le hηδ) hd ρ M hρ x
  have hb : (∫ y,gaussianLogBandPair η δ (x,y) ∂μ) ≤
      ∫ y,gaussianLogShortRange δ (x-y) ∂μ := by
    apply integral_mono_ae (integrable_gaussianLogBand_row η δ hη hηδ μ x) hi
    filter_upwards [μ.ae_ne x] with y hy
    exact gaussianLogBand_le_short η δ hη hηδ (x-y) (sub_ne_zero.mpr hy.symm)
  exact hb.trans (gaussianLogShortRange_convolution_le δ (hη.trans_le hηδ) hd ρ M hM hρ x)

lemma gaussianLog_cutoff_low_diagonal_bound (η δ T β : ℝ)
    (hη : 0 < η) (hηδ : η ≤ δ) (hδ1 : δ ≤ 1) (hT : 1 ≤ T) (hβ : 0 ≤ β)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (x : EuclideanSpace ℝ ι) :
    β*(∫ y,gaussianLogBandPair η T (x,y) ∂gaussianRieszDensityMeasure ρ) +
      β/2*‖centeredGaussianLogBandFeature δ T (hη.trans_le hηδ) (gaussianRieszDensityMeasure ρ) x‖^2 -
      β/2*(∫ p,gaussianLogBandPair η T p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) -
      β/2*gaussianLogCounterterm T ≤
      β*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*δ^(Fintype.card ι : ℝ))) +
      β/2*(-Real.log δ+1/4) := by
  rw [gaussianLog_cutoff_low_diagonal_cancellation η δ T β hη hηδ (hδ1.trans hT)]
  have hp := gaussianLogBand_potential_le_short_bound η δ hη hηδ hd ρ M hM hρ x
  have hm : 0 ≤ ∫ p,gaussianLogBandPair η δ p
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ) :=
    integral_nonneg (fun p => gaussianLogBand_nonneg η δ hη (p.1-p.2))
  have hs := gaussianLogCounterterm_low_scale_bound δ T (hη.trans_le hηδ) hT
  have hpβ := mul_le_mul_of_nonneg_left hp hβ
  have hsβ := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ β/2)
  nlinarith [mul_nonneg hβ hm]

end DGRHS.Gaussian

#check @DGRHS.Gaussian.gaussianLogBand_split
#print axioms DGRHS.Gaussian.gaussianLogBand_split
#check @DGRHS.Gaussian.gaussianLogBand_potential_split
#print axioms DGRHS.Gaussian.gaussianLogBand_potential_split
#check @DGRHS.Gaussian.gaussianLogBand_pairMean_split
#print axioms DGRHS.Gaussian.gaussianLogBand_pairMean_split
#check @DGRHS.Gaussian.gaussianLogCutoffApproxExponent
#print axioms DGRHS.Gaussian.gaussianLogCutoffApproxExponent
#check @DGRHS.Gaussian.gaussianLog_cutoff_low_diagonal_cancellation
#print axioms DGRHS.Gaussian.gaussianLog_cutoff_low_diagonal_cancellation
#check @DGRHS.Gaussian.gaussianLogBand_potential_le_short_bound
#print axioms DGRHS.Gaussian.gaussianLogBand_potential_le_short_bound
#check @DGRHS.Gaussian.gaussianLog_cutoff_low_diagonal_bound
#print axioms DGRHS.Gaussian.gaussianLog_cutoff_low_diagonal_bound
