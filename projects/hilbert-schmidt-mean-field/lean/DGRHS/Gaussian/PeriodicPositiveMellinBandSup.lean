import DGRHS.Gaussian.PeriodicPositiveMellinBandControl
import DGRHS.Gaussian.HoeffdingLinearity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed. Pointwise lower-cutoff bounds for the actual
positive heat band. These complement the upper-scale L2 controls; they do
not replace them. Every fixed row is proper before any pointwise constant
cancellation. This time-band proof is an explicit adaptation, not a proof
of the manuscript's separate Fourier-cutoff lemmas. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal
namespace DGRHS.Gaussian
variable {X : Type*} [MeasurableSpace X]

lemma norm_hoeffdingCentered_le_of_pointwise_bound
    (μ : Measure X) [IsProbabilityMeasure μ] (H : X × X → ℝ) (C : ℝ)
    (hC : ∀ q, ‖H q‖ ≤ C) (p : X × X) :
    ‖hoeffdingCentered μ H p‖ ≤ 4*C := by
  have hrow : ‖∫ y, H (p.1,y) ∂μ‖ ≤ C := by
    simpa using norm_integral_le_of_norm_le_const
      (μ := μ) (Eventually.of_forall (fun y => hC (p.1,y)))
  have hcol : ‖∫ x, H (x,p.2) ∂μ‖ ≤ C := by
    simpa using norm_integral_le_of_norm_le_const
      (μ := μ) (Eventually.of_forall (fun x => hC (x,p.2)))
  have hpair : ‖∫ q, H q ∂μ.prod μ‖ ≤ C := by
    simpa using norm_integral_le_of_norm_le_const
      (μ := μ.prod μ) (Eventually.of_forall hC)
  change ‖H p - (∫ y, H (p.1,y) ∂μ) - (∫ x, H (x,p.2) ∂μ) +
    (∫ q, H q ∂μ.prod μ)‖ ≤ _
  calc
    _ ≤ ‖H p - (∫ y, H (p.1,y) ∂μ) - (∫ x, H (x,p.2) ∂μ)‖ +
        ‖∫ q, H q ∂μ.prod μ‖ := norm_add_le _ _
    _ ≤ (‖H p - (∫ y, H (p.1,y) ∂μ)‖ + ‖∫ x, H (x,p.2) ∂μ‖) +
        ‖∫ q, H q ∂μ.prod μ‖ := by
      linarith [norm_sub_le (H p - (∫ y, H (p.1,y) ∂μ)) (∫ x, H (x,p.2) ∂μ)]
    _ ≤ ((‖H p‖ + ‖∫ y, H (p.1,y) ∂μ‖) + ‖∫ x, H (x,p.2) ∂μ‖) +
        ‖∫ q, H q ∂μ.prod μ‖ := by
      linarith [norm_sub_le (H p) (∫ y, H (p.1,y) ∂μ)]
    _ ≤ 4*C := by linarith [hC p]

/-- The bound derives properness at every point, so this cancellation is
pointwise even for measures with atoms. No product-AE diagonal assertion. -/
lemma hoeffdingCentered_sub_const_of_pointwise_bound
    (μ : Measure X) [IsProbabilityMeasure μ] (H : X × X → ℝ)
    (hH : StronglyMeasurable H) (C : ℝ) (hC : ∀ q, ‖H q‖ ≤ C)
    (c : ℝ) (p : X × X) :
    hoeffdingCentered μ (fun q => H q-c) p = hoeffdingCentered μ H p := by
  have hrow : Integrable (fun y => H (p.1,y)) μ :=
    (integrable_const C).mono'
      (hH.comp_measurable (show Measurable (fun y => (p.1,y)) by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall (fun y => hC (p.1,y)))
  have hcol : Integrable (fun x => H (x,p.2)) μ :=
    (integrable_const C).mono'
      (hH.comp_measurable (show Measurable (fun x => (x,p.2)) by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall (fun x => hC (x,p.2)))
  have hpair : Integrable H (μ.prod μ) :=
    (integrable_const C).mono' hH.aestronglyMeasurable (Eventually.of_forall hC)
  change H p-c - (∫ y, H (p.1,y)-c ∂μ) - (∫ x, H (x,p.2)-c ∂μ) +
      (∫ q, H q-c ∂μ.prod μ) =
    H p - (∫ y, H (p.1,y) ∂μ) - (∫ x, H (x,p.2) ∂μ) + (∫ q, H q ∂μ.prod μ)
  rw [integral_sub hrow (integrable_const c), integral_sub hcol (integrable_const c),
    integral_sub hpair (integrable_const c)]
  simp only [integral_const, probReal_univ, one_smul]
  ring

end DGRHS.Gaussian

namespace DGRHS.Periodic
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicPositiveMellinIntegrand_small_norm_bound (s τ t : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hτ : 0 ≤ τ) (x : PeriodicTorus ι) :
    ‖periodicPositiveMellinIntegrand (((Fintype.card ι : ℝ)-s)/2-1) τ t x‖ ≤
      periodicHeatDiagonalSmallConstant ι * t ^ (-s/2-1) := by
  let p : ℝ := ((Fintype.card ι : ℝ)-s)/2-1
  have hp : 0 ≤ t^p := Real.rpow_nonneg ht.le _
  calc
    _ = t^p * ‖(periodicGaussianHeat (t+τ) x).re‖ := by
      change ‖t^p * (periodicGaussianHeat (t+τ) x).re‖ = _
      rw [norm_mul, Real.norm_of_nonneg hp]
    _ ≤ t^p * ‖periodicGaussianHeat (t+τ) x‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hp
    _ ≤ t^p * (periodicHeatDiagonalSmallConstant ι * t ^ (-((Fintype.card ι : ℝ)/2))) :=
      mul_le_mul_of_nonneg_left (periodicGaussianHeat_shifted_small_bound t τ ht ht1 hτ x) hp
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_add ht]
      congr 1
      congr 1
      dsimp [p]
      ring

lemma periodicPositiveMellinBand_parameter_integrable (s τ δ a : ℝ)
    (hs : 0 < s) (hτ : 0 ≤ τ) (hδ : 0 < δ) (ha1 : a ≤ 1) (x : PeriodicTorus ι) :
    IntegrableOn (fun t : ℝ =>
      periodicPositiveMellinIntegrand (((Fintype.card ι : ℝ)-s)/2-1) τ t x) (Ioc δ a) := by
  have he : IntegrableOn (fun t : ℝ => periodicHeatDiagonalSmallConstant ι *
      t ^ (-s/2-1)) (Ioi δ) := (integrableOn_Ioi_rpow_of_lt (by linarith : -s/2-1 < -1) hδ).const_mul
    (periodicHeatDiagonalSmallConstant ι)
  apply (he.mono_set (show Ioc δ a ⊆ Ioi δ from fun _ ht => ht.1)).mono'
    ((periodicPositiveMellinIntegrand_measurable _ τ).comp
      (show Measurable (fun t : ℝ => (t,x)) by fun_prop)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact periodicPositiveMellinIntegrand_small_norm_bound s τ t (hδ.trans ht.1)
    (ht.2.trans ha1) hτ x

lemma periodicPositiveMellinBand_norm_bound (s τ δ a : ℝ)
    (hs : 0 < s) (hτ : 0 ≤ τ) (hδ : 0 < δ) (ha1 : a ≤ 1) (x : PeriodicTorus ι) :
    ‖periodicPositiveMellinBand (((Fintype.card ι : ℝ)-s)/2-1) τ δ a x‖ ≤
      periodicHeatDiagonalSmallConstant ι * (δ ^ (-s/2) / (s/2)) := by
  have hi := periodicPositiveMellinBand_parameter_integrable s τ δ a hs hτ hδ ha1 x
  have he : IntegrableOn (fun t : ℝ => periodicHeatDiagonalSmallConstant ι *
      t ^ (-s/2-1)) (Ioi δ) := (integrableOn_Ioi_rpow_of_lt (by linarith : -s/2-1 < -1) hδ).const_mul
    (periodicHeatDiagonalSmallConstant ι)
  have he' := he.mono_set (show Ioc δ a ⊆ Ioi δ from fun _ ht => ht.1)
  calc
    _ ≤ ∫ t : ℝ in Ioc δ a,
        ‖periodicPositiveMellinIntegrand (((Fintype.card ι : ℝ)-s)/2-1) τ t x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Ioc δ a, periodicHeatDiagonalSmallConstant ι * t ^ (-s/2-1) := by
      apply integral_mono_ae hi.norm he'
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact periodicPositiveMellinIntegrand_small_norm_bound s τ t (hδ.trans ht.1)
        (ht.2.trans ha1) hτ x
    _ ≤ ∫ t : ℝ in Ioi δ, periodicHeatDiagonalSmallConstant ι * t ^ (-s/2-1) := by
      apply setIntegral_mono_set he
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg periodicHeatDiagonalSmallConstant_nonneg
          (Real.rpow_nonneg (hδ.trans ht).le _)
      · exact Eventually.of_forall (fun t ht => ht.1)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -s/2-1 < -1) hδ]
      rw [show -s/2-1+1 = -(s/2) by ring]
      congr 1
      simp only [div_neg, neg_div, neg_neg]

lemma periodicRieszPositiveBand_norm_bound (s τ δ a : ℝ)
    (hs : 0 < s) (hτ : 0 ≤ τ) (hδ : 0 < δ) (ha1 : a ≤ 1) (x : PeriodicTorus ι) :
    ‖periodicRieszPositiveBand s τ δ a x‖ ≤
      periodicRieszMellinFactor ι s * periodicHeatDiagonalSmallConstant ι *
        (δ ^ (-s/2) / (s/2)) := by
  have hF := (periodicRieszMellinFactor_pos (ι := ι) s hs).le
  simpa only [periodicRieszPositiveBand, norm_mul, Real.norm_of_nonneg hF, mul_assoc] using
    mul_le_mul_of_nonneg_left
      (periodicPositiveMellinBand_norm_bound s τ δ a hs hτ hδ ha1 x) hF

/-- Every row, every column, and the pair kernel are proper for arbitrary
probability backgrounds. No density cap is needed for the positive cutoff. -/
lemma periodicRieszPositiveBand_pair_proper (s τ δ a : ℝ)
    (hs : 0 < s) (hτ : 0 ≤ τ) (hδ : 0 < δ) (ha1 : a ≤ 1)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] :
    (∀ x, Integrable (fun y => periodicRieszPositiveBand s τ δ a (x-y)) μ) ∧
    (∀ y, Integrable (fun x => periodicRieszPositiveBand s τ δ a (x-y)) μ) ∧
    Integrable (fun q : PeriodicTorus ι × PeriodicTorus ι =>
      periodicRieszPositiveBand s τ δ a (q.1-q.2)) (μ.prod μ) := by
  have hm := periodicRieszPositiveBand_measurable (ι := ι) s τ δ a
  have hb := periodicRieszPositiveBand_norm_bound (ι := ι) s τ δ a hs hτ hδ ha1
  refine ⟨?_,?_,?_⟩
  · intro x
    exact (integrable_const _).mono' (hm.comp (show Measurable (fun y => x-y) by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall (fun y => hb (x-y)))
  · intro y
    exact (integrable_const _).mono' (hm.comp (show Measurable (fun x => x-y) by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall (fun x => hb (x-y)))
  · exact (integrable_const _).mono' (hm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
      (Eventually.of_forall (fun q => hb (q.1-q.2)))

lemma periodicRieszPositiveBand_centered_norm_bound (s τ δ a : ℝ)
    (hs : 0 < s) (hτ : 0 ≤ τ) (hδ : 0 < δ) (ha1 : a ≤ 1)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    ‖hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι =>
      periodicRieszPositiveBand s τ δ a (q.1-q.2)) p‖ ≤
      4*(periodicRieszMellinFactor ι s * periodicHeatDiagonalSmallConstant ι *
        (δ ^ (-s/2) / (s/2))) :=
  norm_hoeffdingCentered_le_of_pointwise_bound μ _ _
    (fun q => periodicRieszPositiveBand_norm_bound s τ δ a hs hτ hδ ha1 (q.1-q.2)) p

lemma periodicRieszPositiveBand_centered_sub_const (s τ δ a c : ℝ)
    (hs : 0 < s) (hτ : 0 ≤ τ) (hδ : 0 < δ) (ha1 : a ≤ 1)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι =>
      periodicRieszPositiveBand s τ δ a (q.1-q.2)-c) p =
    hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι =>
      periodicRieszPositiveBand s τ δ a (q.1-q.2)) p :=
  hoeffdingCentered_sub_const_of_pointwise_bound μ _
    ((periodicRieszPositiveBand_measurable s τ δ a).stronglyMeasurable.comp_measurable
      (measurable_fst.sub measurable_snd)) _
    (fun q => periodicRieszPositiveBand_norm_bound s τ δ a hs hτ hδ ha1 (q.1-q.2)) c p

lemma periodicRieszPositiveBand_centered_memLp_infty (s τ δ a : ℝ)
    (hs : 0 < s) (hτ : 0 ≤ τ) (hδ : 0 < δ) (ha1 : a ≤ 1)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] :
    MemLp (hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι =>
      periodicRieszPositiveBand s τ δ a (q.1-q.2))) ∞ (μ.prod μ) := by
  have hD : 0 ≤ 4*(periodicRieszMellinFactor ι s * periodicHeatDiagonalSmallConstant ι *
      (δ ^ (-s/2) / (s/2))) := by
    have hF := (periodicRieszMellinFactor_pos (ι := ι) s hs).le
    have hC := periodicHeatDiagonalSmallConstant_nonneg (ι := ι)
    positivity
  apply (memLp_const (4*(periodicRieszMellinFactor ι s * periodicHeatDiagonalSmallConstant ι *
    (δ ^ (-s/2) / (s/2))))).of_le
    (stronglyMeasurable_hoeffdingCentered μ _
      ((periodicRieszPositiveBand_measurable s τ δ a).stronglyMeasurable.comp_measurable
        (measurable_fst.sub measurable_snd))).aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_of_nonneg hD]
  exact periodicRieszPositiveBand_centered_norm_bound s τ δ a hs hτ hδ ha1 μ p

lemma periodicRieszPositiveBand_scaled_centered_norm_bound (s τ δ a c : ℝ)
    (hs : 0 < s) (hτ : 0 ≤ τ) (hδ : 0 < δ) (ha1 : a ≤ 1)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    ‖c * hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι =>
      periodicRieszPositiveBand s τ δ a (q.1-q.2)) p‖ ≤
      4*|c| *(periodicRieszMellinFactor ι s * periodicHeatDiagonalSmallConstant ι *
        (δ ^ (-s/2) / (s/2))) := by
  rw [norm_mul, Real.norm_eq_abs]
  calc
    _ ≤ |c| *(4*(periodicRieszMellinFactor ι s * periodicHeatDiagonalSmallConstant ι *
        (δ ^ (-s/2) / (s/2)))) :=
      mul_le_mul_of_nonneg_left
        (periodicRieszPositiveBand_centered_norm_bound s τ δ a hs hτ hδ ha1 μ p) (abs_nonneg c)
    _ = _ := by ring

end DGRHS.Periodic
