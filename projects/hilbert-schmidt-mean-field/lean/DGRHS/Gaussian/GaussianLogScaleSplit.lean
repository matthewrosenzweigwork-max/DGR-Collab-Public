import DGRHS.Gaussian.GaussianLogInfraredScalar
import DGRHS.Gaussian.GaussianLogInfraredConvergence
import DGRHS.Gaussian.GaussianLogBandCentering
import DGRHS.Gaussian.GaussianLogShortRangeSource

/-! Proper physical scale splits and every-x affine
potential identities. Raw spatial equalities are used only away from zero;
actual density sections remove their own singleton. -/
noncomputable section
open MeasureTheory Set Real
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma gaussianLogShortRange_split (α T : ℝ) (hα : 0 < α) (hαT : α ≤ T)
    (x : EuclideanSpace ℝ ι) (hx : x ≠ 0) :
    gaussianLogShortRange T x = gaussianLogShortRange α x + gaussianLogBand α T x := by
  have hi := integrableOn_gaussianLog_profile_short T ‖x‖ (hα.trans_le hαT) (norm_pos_iff.mpr hx)
  have he := integral_add_compl (s := Iic α) measurableSet_Iic hi
  rw [compl_Iic, Measure.restrict_restrict measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Ioi] at he
  have hA : Iic α ∩ Ioc (0 : ℝ) T = Ioc 0 α := by
    ext t; simp only [mem_inter_iff,mem_Iic,mem_Ioc]
    constructor
    · intro ht; exact ⟨ht.2.1,ht.1⟩
    · intro ht; exact ⟨ht.2,ht.1,ht.2.trans hαT⟩
  have hB : Ioi α ∩ Ioc (0 : ℝ) T = Ioc α T := by
    ext t; simp only [mem_inter_iff,mem_Ioi,mem_Ioc]
    constructor
    · intro ht; exact ⟨ht.1,ht.2.2⟩
    · intro ht; exact ⟨ht.1,hα.trans ht.1,ht.2⟩
  rw [hA,hB] at he
  exact he.symm

lemma gaussianLogAnchored_eq_short_counterterm (T : ℝ) (hT : 0 < T)
    (x : EuclideanSpace ℝ ι) (hx : x ≠ 0) :
    gaussianLogAnchored T ‖x‖ = gaussianLogShortRange T x - gaussianLogCounterterm T := by
  have hi := integrableOn_gaussianLog_profile_short T ‖x‖ hT (norm_pos_iff.mpr hx)
  have hj := integrableOn_gaussianLogCounterterm T hT
  unfold gaussianLogAnchored gaussianLogShortRange gaussianLogCounterterm
  simp_rw [mul_sub]
  exact integral_sub hi hj

lemma ae_gaussianLogInfraredPair_eq_short_counterterm (T : ℝ) (hT : 0 < T)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    gaussianLogInfraredPair T =ᵐ[(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)]
      (fun p => gaussianLogShortPair T p - gaussianLogCounterterm T) := by
  have hc : 0 < Fintype.card ι := by exact_mod_cast hd
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  filter_upwards [ae_gaussianRieszDensity_pair_ne ρ] with p hp
  exact gaussianLogAnchored_eq_short_counterterm T hT (p.1-p.2) (sub_ne_zero.mpr hp)

lemma ae_gaussianLogInfrared_row_eq_short_counterterm (T : ℝ) (hT : 0 < T)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (x : EuclideanSpace ℝ ι) :
    (fun y => gaussianLogInfraredPair T (x,y)) =ᵐ[gaussianRieszDensityMeasure ρ]
      (fun y => gaussianLogShortPair T (x,y) - gaussianLogCounterterm T) := by
  have hc : 0 < Fintype.card ι := by exact_mod_cast hd
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  letI : NullSingletonClass (gaussianRieszDensityMeasure ρ) := by
    unfold gaussianRieszDensityMeasure; infer_instance
  filter_upwards [(gaussianRieszDensityMeasure ρ).ae_ne x] with y hy
  exact gaussianLogAnchored_eq_short_counterterm T hT (x-y) (sub_ne_zero.mpr hy.symm)

lemma gaussianLogInfrared_potential_eq_short_counterterm (T : ℝ) (hT : 0 < T)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (x : EuclideanSpace ℝ ι) :
    (∫ y,gaussianLogInfraredPair T (x,y) ∂gaussianRieszDensityMeasure ρ) =
      (∫ y,gaussianLogShortPair T (x,y) ∂gaussianRieszDensityMeasure ρ) - gaussianLogCounterterm T := by
  rw [integral_congr_ae (ae_gaussianLogInfrared_row_eq_short_counterterm T hT hd ρ x)]
  have hi : Integrable (fun y => gaussianLogShortPair T (x,y)) (gaussianRieszDensityMeasure ρ) :=
    integrable_gaussianLogShortRange_convolution T hT hd ρ M hρ x
  rw [integral_sub hi (integrable_const _)]
  simp

lemma gaussianLogInfrared_pairMean_eq_short_counterterm (T : ℝ) (hT : 0 < T)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    (∫ p,gaussianLogInfraredPair T p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) =
      (∫ p,gaussianLogShortPair T p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) -
      gaussianLogCounterterm T := by
  rw [integral_congr_ae (ae_gaussianLogInfraredPair_eq_short_counterterm T hT hd ρ)]
  have hi := (memLp_gaussianLogShortPair T hT hd ρ M hM hρ).integrable (by norm_num)
  rw [integral_sub hi (integrable_const _)]
  simp

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianLogShortRange_split
#print axioms DGRHS.Gaussian.gaussianLogShortRange_split
#check DGRHS.Gaussian.gaussianLogAnchored_eq_short_counterterm
#print axioms DGRHS.Gaussian.gaussianLogAnchored_eq_short_counterterm
#check DGRHS.Gaussian.ae_gaussianLogInfraredPair_eq_short_counterterm
#print axioms DGRHS.Gaussian.ae_gaussianLogInfraredPair_eq_short_counterterm
#check DGRHS.Gaussian.ae_gaussianLogInfrared_row_eq_short_counterterm
#print axioms DGRHS.Gaussian.ae_gaussianLogInfrared_row_eq_short_counterterm
#check DGRHS.Gaussian.gaussianLogInfrared_potential_eq_short_counterterm
#print axioms DGRHS.Gaussian.gaussianLogInfrared_potential_eq_short_counterterm
#check DGRHS.Gaussian.gaussianLogInfrared_pairMean_eq_short_counterterm
#print axioms DGRHS.Gaussian.gaussianLogInfrared_pairMean_eq_short_counterterm
