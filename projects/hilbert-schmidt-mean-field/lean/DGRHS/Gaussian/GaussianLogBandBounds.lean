import DGRHS.Gaussian.GaussianLogInfraredScalar
import DGRHS.Gaussian.GaussianLogShortRangeSource

/-! Proper finite logarithmic bands and every-row square
bounds from the actual short kernel. All diagonal removals use the density
law's null singletons in each section; no product-AE diagonal slice is used. -/
noncomputable section
open MeasureTheory Real Set
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma integrable_gaussianLogBandProfile (η δ : ℝ) (hη : 0 < η)
    (x : EuclideanSpace ℝ ι) :
    IntegrableOn (fun t : ℝ => t⁻¹*Real.exp (-‖x‖^2/(2*t^2))) (Ioc η δ) := by
  apply (integrable_gaussianLogBandWeight η δ hη).mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := hη.trans ht.1
  rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr ht0.le) (Real.exp_pos _).le)]
  have he : Real.exp (-‖x‖^2/(2*t^2)) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
  simpa using mul_le_mul_of_nonneg_left he (inv_nonneg.mpr ht0.le)

lemma gaussianLogBand_nonneg (η δ : ℝ) (hη : 0 < η)
    (x : EuclideanSpace ℝ ι) : 0 ≤ gaussianLogBand η δ x := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact mul_nonneg (inv_nonneg.mpr (hη.trans ht.1).le) (Real.exp_pos _).le

lemma gaussianLogBand_le_mass (η δ : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (x : EuclideanSpace ℝ ι) : gaussianLogBand η δ x ≤ Real.log (δ/η) := by
  have hb : gaussianLogBand η δ x ≤ ∫ t : ℝ in Ioc η δ, t⁻¹ := by
    apply integral_mono_ae (integrable_gaussianLogBandProfile η δ hη x)
      (integrable_gaussianLogBandWeight η δ hη)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have he : Real.exp (-‖x‖^2/(2*t^2)) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
    simpa using mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (hη.trans ht.1).le)
  have hval : (∫ t : ℝ in Ioc η δ, t⁻¹) = Real.log (δ/η) := by
    rw [← intervalIntegral.integral_of_le hηδ]
    exact integral_inv_of_pos hη (hη.trans_le hηδ)
  exact hb.trans_eq hval

lemma stronglyMeasurable_gaussianLogBand (η δ : ℝ) (hη : 0 < η) :
    StronglyMeasurable (gaussianLogBand (ι := ι) η δ) := by
  have hm : StronglyMeasurable (fun x : EuclideanSpace ℝ ι =>
      inner ℝ (gaussianLogBandFeature η δ hη x) (gaussianLogBandFeature η δ hη 0)) :=
    (stronglyMeasurable_gaussianLogBandFeature η δ hη).inner stronglyMeasurable_const
  simpa only [inner_gaussianLogBandFeature, sub_zero] using hm

lemma gaussianLogBand_le_short (η δ : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (x : EuclideanSpace ℝ ι) (hx : x ≠ 0) :
    gaussianLogBand η δ x ≤ gaussianLogShortRange δ x := by
  let F : ℝ → ℝ := fun t => t⁻¹ * Real.exp (-‖x‖^2/(2*t^2))
  have hi : IntegrableOn F (Ioc 0 δ) :=
    integrableOn_gaussianLog_profile_short δ ‖x‖ (hη.trans_le hηδ) (norm_pos_iff.mpr hx)
  have he : Ioi η ∩ Ioc (0 : ℝ) δ = Ioc η δ := by
    ext t
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · intro ht; exact ⟨ht.1, ht.2.2⟩
    · intro ht; exact ⟨ht.1, hη.trans ht.1, ht.2⟩
  unfold gaussianLogBand gaussianLogShortRange
  change (∫ t in Ioc η δ, F t) ≤ ∫ t in Ioc 0 δ, F t
  rw [← he, ← Measure.restrict_restrict measurableSet_Ioi]
  apply integral_mono_measure Measure.restrict_le_self _ hi
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact mul_nonneg (inv_nonneg.mpr ht.1.le) (Real.exp_pos _).le

lemma ae_gaussianLogBand_sq_le_short_row (η δ : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (x : EuclideanSpace ℝ ι) :
    ∀ᵐ y ∂gaussianRieszDensityMeasure ρ,
      gaussianLogBand η δ (x-y)^2 ≤ gaussianLogShortRange δ (x-y)^2 := by
  have hc : 0 < Fintype.card ι := by exact_mod_cast hd
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  letI : NullSingletonClass (gaussianRieszDensityMeasure ρ) := by
    unfold gaussianRieszDensityMeasure
    infer_instance
  filter_upwards [(gaussianRieszDensityMeasure ρ).ae_ne x] with y hy
  have hn := gaussianLogBand_nonneg η δ hη (x-y)
  have hl := gaussianLogBand_le_short η δ hη hηδ (x-y) (sub_ne_zero.mpr hy.symm)
  have hn2 := gaussianLogShortRange_nonneg δ (x-y)
  nlinarith

lemma gaussianLogBand_row_sq_bound (η δ : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (x : EuclideanSpace ℝ ι) :
    Integrable (fun y => gaussianLogBand η δ (x-y)^2) (gaussianRieszDensityMeasure ρ) ∧
    (∫ y, gaussianLogBand η δ (x-y)^2 ∂gaussianRieszDensityMeasure ρ) ≤
      M*((δ^((Fintype.card ι : ℝ)/2)/((Fintype.card ι : ℝ)/2))^2*
        Real.pi^((Fintype.card ι : ℝ)/2)) := by
  have hδ := hη.trans_le hηδ
  have hi := (memLp_gaussianLogShortRange (ι := ι) δ hδ hd).integrable_sq
  have his := integrable_sq_sub_density ρ M hρ _ hi x
  have hb := ae_gaussianLogBand_sq_le_short_row η δ hη hηδ hd ρ x
  have hmb := ((stronglyMeasurable_gaussianLogBand (ι := ι) η δ hη).comp_measurable
    (by fun_prop : Measurable (fun y : EuclideanSpace ℝ ι => x-y))).pow 2
  have hib := his.mono' hmb.aestronglyMeasurable (by
    filter_upwards [hb] with y hy
    change ‖gaussianLogBand η δ (x-y)^2‖ ≤ _
    rwa [Real.norm_of_nonneg (sq_nonneg _)] )
  refine ⟨hib, ?_⟩
  calc
    _ ≤ ∫ y, gaussianLogShortRange δ (x-y)^2 ∂gaussianRieszDensityMeasure ρ :=
      integral_mono_ae hib his hb
    _ ≤ M*∫ z : EuclideanSpace ℝ ι, gaussianLogShortRange δ z^2 :=
      integral_sq_sub_density_le ρ M hM hρ _ hi x
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_gaussianLogShortRange_sq_le δ hδ hd) hM

end DGRHS.Gaussian

#check @DGRHS.Gaussian.integrable_gaussianLogBandProfile
#print axioms DGRHS.Gaussian.integrable_gaussianLogBandProfile

#check @DGRHS.Gaussian.gaussianLogBand_nonneg
#print axioms DGRHS.Gaussian.gaussianLogBand_nonneg

#check @DGRHS.Gaussian.gaussianLogBand_le_mass
#print axioms DGRHS.Gaussian.gaussianLogBand_le_mass

#check @DGRHS.Gaussian.stronglyMeasurable_gaussianLogBand
#print axioms DGRHS.Gaussian.stronglyMeasurable_gaussianLogBand

#check @DGRHS.Gaussian.gaussianLogBand_le_short
#print axioms DGRHS.Gaussian.gaussianLogBand_le_short

#check @DGRHS.Gaussian.ae_gaussianLogBand_sq_le_short_row
#print axioms DGRHS.Gaussian.ae_gaussianLogBand_sq_le_short_row

#check @DGRHS.Gaussian.gaussianLogBand_row_sq_bound
#print axioms DGRHS.Gaussian.gaussianLogBand_row_sq_bound

