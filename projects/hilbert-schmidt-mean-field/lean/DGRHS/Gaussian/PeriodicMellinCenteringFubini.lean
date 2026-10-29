import DGRHS.Gaussian.PeriodicPositiveMellinTail
import DGRHS.Gaussian.HoeffdingLinearity

/-! Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed. Proper centering commutes with the actual
positive-cutoff Mellin tail. The spatially uniform envelope is proved from
heat bounds in the application; it is not a desired centering/Fubini premise.
All pointwise rows and columns are proper before the swaps. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology
namespace DGRHS.Gaussian
universe u v
variable {T : Type u} {X : Type v} [MeasurableSpace T] [MeasurableSpace X]

lemma integrable_parameter_product_of_probability_envelope
    (ν : Measure T) [SFinite ν] (μ : Measure X) [IsProbabilityMeasure μ]
    (F : T × X → ℝ) (hF : StronglyMeasurable F) (B : T → ℝ)
    (hB : Integrable B ν) (hb : ∀ᵐ t ∂ν, ∀ x, ‖F (t,x)‖ ≤ B t) :
    Integrable F (ν.prod μ) := by
  apply (integrable_prod_iff hF.aestronglyMeasurable).2
  constructor
  · filter_upwards [hb] with t ht
    exact (integrable_const (B t)).mono'
      (hF.comp_measurable (show Measurable (fun x => (t,x)) by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall ht)
  · apply hB.mono' hF.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [hb] with t ht
    have hi : Integrable (fun x => F (t,x)) μ :=
      (integrable_const (B t)).mono'
        (hF.comp_measurable (show Measurable (fun x => (t,x)) by fun_prop)).aestronglyMeasurable
        (Eventually.of_forall ht)
    rw [Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg (F (t,x))))]
    calc
      _ ≤ ∫ _ : X, B t ∂μ := integral_mono_ae hi.norm (integrable_const _)
        (Eventually.of_forall ht)
      _ = _ := by simp

lemma integrable_parameter_section_of_envelope
    (ν : Measure T) (F : T × X → ℝ) (hF : StronglyMeasurable F) (B : T → ℝ)
    (hB : Integrable B ν) (hb : ∀ᵐ t ∂ν, ∀ x, ‖F (t,x)‖ ≤ B t) (x : X) :
    Integrable (fun t => F (t,x)) ν :=
  hB.mono' (hF.comp_measurable (show Measurable (fun t => (t,x)) by fun_prop)).aestronglyMeasurable
    (hb.mono (fun t ht => ht x))

lemma integrable_parameter_hoeffdingCentered_of_envelope
    (ν : Measure T) [SFinite ν] (μ : Measure X) [IsProbabilityMeasure μ]
    (H : T × (X × X) → ℝ) (hH : StronglyMeasurable H) (B : T → ℝ)
    (hB : Integrable B ν) (hb : ∀ᵐ t ∂ν, ∀ p, ‖H (t,p)‖ ≤ B t) (p : X × X) :
    Integrable (fun t => hoeffdingCentered μ (fun q => H (t,q)) p) ν := by
  have hpoint := integrable_parameter_section_of_envelope ν H hH B hB hb p
  have hleft : Integrable (fun q : T × X => H (q.1,(p.1,q.2))) (ν.prod μ) := by
    apply integrable_parameter_product_of_probability_envelope ν μ _
      (hH.comp_measurable (show Measurable (fun q : T × X => (q.1,(p.1,q.2))) by fun_prop)) B hB
    exact hb.mono (fun t ht x => ht (p.1,x))
  have hright : Integrable (fun q : T × X => H (q.1,(q.2,p.2))) (ν.prod μ) := by
    apply integrable_parameter_product_of_probability_envelope ν μ _
      (hH.comp_measurable (show Measurable (fun q : T × X => (q.1,(q.2,p.2))) by fun_prop)) B hB
    exact hb.mono (fun t ht x => ht (x,p.2))
  have hwhole := integrable_parameter_product_of_probability_envelope ν (μ.prod μ) H hH B hB hb
  exact ((hpoint.sub hleft.integral_prod_left).sub hright.integral_prod_left).add
    hwhole.integral_prod_left

lemma hoeffdingCentered_integral_parameter_of_envelope
    (ν : Measure T) [SFinite ν] (μ : Measure X) [IsProbabilityMeasure μ]
    (H : T × (X × X) → ℝ) (hH : StronglyMeasurable H) (B : T → ℝ)
    (hB : Integrable B ν) (hb : ∀ᵐ t ∂ν, ∀ p, ‖H (t,p)‖ ≤ B t) (p : X × X) :
    hoeffdingCentered μ (fun q => ∫ t, H (t,q) ∂ν) p =
      ∫ t, hoeffdingCentered μ (fun q => H (t,q)) p ∂ν := by
  have hpoint := integrable_parameter_section_of_envelope ν H hH B hB hb p
  have hleft : Integrable (fun q : T × X => H (q.1,(p.1,q.2))) (ν.prod μ) := by
    apply integrable_parameter_product_of_probability_envelope ν μ _
      (hH.comp_measurable (show Measurable (fun q : T × X => (q.1,(p.1,q.2))) by fun_prop)) B hB
    exact hb.mono (fun t ht x => ht (p.1,x))
  have hright : Integrable (fun q : T × X => H (q.1,(q.2,p.2))) (ν.prod μ) := by
    apply integrable_parameter_product_of_probability_envelope ν μ _
      (hH.comp_measurable (show Measurable (fun q : T × X => (q.1,(q.2,p.2))) by fun_prop)) B hB
    exact hb.mono (fun t ht x => ht (x,p.2))
  have hwhole := integrable_parameter_product_of_probability_envelope ν (μ.prod μ) H hH B hB hb
  change (∫ t, H (t,p) ∂ν) - (∫ y, (∫ t, H (t,(p.1,y)) ∂ν) ∂μ) -
      (∫ x, (∫ t, H (t,(x,p.2)) ∂ν) ∂μ) +
      (∫ q, (∫ t, H (t,q) ∂ν) ∂μ.prod μ) =
    ∫ t, H (t,p) - (∫ y, H (t,(p.1,y)) ∂μ) -
      (∫ x, H (t,(x,p.2)) ∂μ) + (∫ q, H (t,q) ∂μ.prod μ) ∂ν
  rw [← integral_integral_swap (f := fun t y => H (t,(p.1,y))) hleft,
    ← integral_integral_swap (f := fun t x => H (t,(x,p.2))) hright,
    ← integral_integral_swap (f := fun t q => H (t,q)) hwhole]
  have hiL : Integrable (fun t => ∫ y, H (t,(p.1,y)) ∂μ) ν :=
    hleft.integral_prod_left
  have hiR : Integrable (fun t => ∫ x, H (t,(x,p.2)) ∂μ) ν :=
    hright.integral_prod_left
  have hiQ : Integrable (fun t => ∫ q, H (t,q) ∂μ.prod μ) ν :=
    hwhole.integral_prod_left
  have hiSub : Integrable (fun t => H (t,p) - (∫ y, H (t,(p.1,y)) ∂μ)) ν :=
    hpoint.sub hiL
  have hiSubSub : Integrable (fun t => H (t,p) - (∫ y, H (t,(p.1,y)) ∂μ) -
      (∫ x, H (t,(x,p.2)) ∂μ)) ν := hiSub.sub hiR
  rw [integral_add hiSubSub hiQ, integral_sub hiSub hiR, integral_sub hpoint hiL]

lemma hoeffdingCentered_const_mul_pointwise
    (μ : Measure X) [IsProbabilityMeasure μ] (H : X × X → ℝ) (c : ℝ) (p : X × X) :
    hoeffdingCentered μ (fun q => c * H q) p = c * hoeffdingCentered μ H p := by
  simp only [hoeffdingCentered, DGRHS.centeredKernel, DGRHS.potential,
    DGRHS.secondPotential, integral_const_mul]
  ring

end DGRHS.Gaussian

namespace DGRHS.Periodic
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicRieszPairTailIntegrand (s τ : ℝ)
    (q : ℝ × (PeriodicTorus ι × PeriodicTorus ι)) : ℝ :=
  q.1 ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) *
    ((periodicGaussianHeat (q.1 + τ) (q.2.1 - q.2.2)).re - 1)

lemma periodicRieszPairTailIntegrand_measurable (s τ : ℝ) :
    Measurable (periodicRieszPairTailIntegrand (ι := ι) s τ) := by
  unfold periodicRieszPairTailIntegrand
  have hm : Measurable (fun q : ℝ × (PeriodicTorus ι × PeriodicTorus ι) =>
      (q.1 + τ,q.2.1 - q.2.2)) := by fun_prop
  exact (show Measurable (fun q : ℝ × (PeriodicTorus ι × PeriodicTorus ι) =>
      q.1 ^ (((Fintype.card ι : ℝ) - s) / 2 - 1)) by fun_prop).mul
    ((Complex.continuous_re.measurable.comp
      (periodicGaussianHeat_joint_measurable.comp hm)).sub measurable_const)

lemma periodicRieszPairTailIntegrand_uniform_bound (s τ ε : ℝ)
    (hτ : 0 ≤ τ) (hε : 0 < ε) :
    ∀ᵐ t ∂volume.restrict (Ioi ε), ∀ p : PeriodicTorus ι × PeriodicTorus ι,
      ‖periodicRieszPairTailIntegrand s τ (t,p)‖ ≤
        periodicHeatDiagonalGlobalConstant ι * t ^ (-s / 2 - 1) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  intro p
  exact periodicRieszMellin_tail_weight_bound s τ t (hε.trans ht) hτ (p.1 - p.2)

lemma periodicRieszPairTailIntegrand_envelope_integrable (s ε : ℝ)
    (hs : 0 < s) (hε : 0 < ε) :
    Integrable (fun t : ℝ => periodicHeatDiagonalGlobalConstant ι * t ^ (-s / 2 - 1))
      (volume.restrict (Ioi ε)) :=
  (integrableOn_Ioi_rpow_of_lt (by linarith : -s / 2 - 1 < -1) hε).const_mul _

lemma periodicRieszPairTailIntegrand_product_integrable (s τ ε : ℝ)
    (hs : 0 < s) (hτ : 0 ≤ τ) (hε : 0 < ε)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] :
    Integrable (periodicRieszPairTailIntegrand s τ)
      ((volume.restrict (Ioi ε)).prod (μ.prod μ)) :=
  integrable_parameter_product_of_probability_envelope _ _ _
    (periodicRieszPairTailIntegrand_measurable s τ).stronglyMeasurable _
    (periodicRieszPairTailIntegrand_envelope_integrable s ε hs hε)
    (periodicRieszPairTailIntegrand_uniform_bound s τ ε hτ hε)

/-- Proper parameter integration is derived for every fixed spatial pair.
The centering equality is pointwise, not merely product-AE. -/
lemma periodicRieszMellinTail_centering_commutes (s τ ε : ℝ)
    (hs : 0 < s) (hτ : 0 ≤ τ) (hε : 0 < ε)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    Integrable (fun t => hoeffdingCentered μ
      (fun q => periodicRieszPairTailIntegrand s τ (t,q)) p) (volume.restrict (Ioi ε)) ∧
    hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι =>
      periodicRieszMellinTail s τ ε (q.1 - q.2)) p =
      ∫ t : ℝ in Ioi ε, hoeffdingCentered μ
        (fun q => periodicRieszPairTailIntegrand s τ (t,q)) p := by
  have hm := (periodicRieszPairTailIntegrand_measurable (ι := ι) s τ).stronglyMeasurable
  have hi := periodicRieszPairTailIntegrand_envelope_integrable (ι := ι) s ε hs hε
  have hb := periodicRieszPairTailIntegrand_uniform_bound (ι := ι) s τ ε hτ hε
  exact ⟨integrable_parameter_hoeffdingCentered_of_envelope _ μ _ hm _ hi hb p,
    hoeffdingCentered_integral_parameter_of_envelope _ μ _ hm _ hi hb p⟩

end DGRHS.Periodic
