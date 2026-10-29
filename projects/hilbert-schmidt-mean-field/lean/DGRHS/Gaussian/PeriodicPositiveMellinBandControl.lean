import DGRHS.Gaussian.PeriodicPositiveMellinShortL2
import DGRHS.Gaussian.PeriodicBoundedBackgroundL2
import DGRHS.Gaussian.HoeffdingRowL2
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed. Actual finite positive heat bands and their
small row/joint/operator bounds. Positivity here is the checked Poisson
pointwise positivity of the FULL heat, not Fourier Gram positivity. No
band norm or favorable master field is supplied. Project heat time is u+tau;
source physical shift t means tau=4*pi^2*t. The later centered-tail cap and
master event comparison are separate. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal Topology
namespace DGRHS.Periodic
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Keep the zero mode in the positive raw band. -/
def periodicPositiveMellinBand (p τ δ a : ℝ) (x : PeriodicTorus ι) : ℝ :=
  ∫ t : ℝ in Ioc δ a, periodicPositiveMellinIntegrand p τ t x

lemma periodicPositiveMellinBand_measurable (p τ δ a : ℝ) :
    Measurable (periodicPositiveMellinBand (ι := ι) p τ δ a) := by
  exact (periodicPositiveMellinIntegrand_measurable p τ).stronglyMeasurable.integral_prod_left
    (μ := volume.restrict (Ioc δ a)) |>.measurable

lemma periodicPositiveMellinBand_nonneg (p τ δ a : ℝ) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ)
    (x : PeriodicTorus ι) : 0 ≤ periodicPositiveMellinBand p τ δ a x := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact periodicPositiveMellinIntegrand_nonneg p τ t hτ (hδ.trans_lt ht.1) x

/-- Only AE comparison is asserted: the short integral may be totalized at
an exceptional singular spatial point. No such identity is used on a diagonal. -/
lemma periodicPositiveMellinBand_ae_le_short (p τ δ a : ℝ) (hp : -1 < p)
    (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) :
    ∀ᵐ x : PeriodicTorus ι ∂periodicHaar ι,
      periodicPositiveMellinBand p τ δ a x ≤ periodicPositiveMellinShort p τ a x := by
  filter_upwards [(periodicPositiveMellinIntegrand_product_integrable
    (ι := ι) p τ a hp hτ).prod_left_ae] with x hx
  apply setIntegral_mono_set hx
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact periodicPositiveMellinIntegrand_nonneg p τ t hτ ht.1 x
  · exact Eventually.of_forall (fun t ht => ⟨hδ.trans_lt ht.1,ht.2⟩)

lemma periodicPositiveMellinBand_memLp (s τ δ a : ℝ)
    (hs : 2*s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    MemLp (periodicPositiveMellinBand (ι := ι) (((Fintype.card ι : ℝ)-s)/2-1) τ δ a)
      2 (periodicHaar ι) := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  apply (periodicPositiveMellinShort_memLp s a τ hs ha ha1 hτ).mono'
    (periodicPositiveMellinBand_measurable _ τ δ a).aestronglyMeasurable
  filter_upwards [periodicPositiveMellinBand_ae_le_short
    (ι := ι) (((Fintype.card ι : ℝ)-s)/2-1) τ δ a (by linarith) hτ hδ] with x hx
  simpa only [Real.norm_of_nonneg (periodicPositiveMellinBand_nonneg _ τ δ a hτ hδ x)] using hx

lemma periodicPositiveMellinBand_sq_mass_bound (s τ δ a : ℝ)
    (hs : 2*s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ x : PeriodicTorus ι,
      periodicPositiveMellinBand (((Fintype.card ι : ℝ)-s)/2-1) τ δ a x ^ 2 ∂periodicHaar ι) ≤
      periodicHeatDiagonalSmallConstant ι / (((Fintype.card ι : ℝ)/4-s/2)^2) *
        a ^ ((Fintype.card ι : ℝ)/2-s) := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  apply (integral_mono_ae
    (periodicPositiveMellinBand_memLp s τ δ a hs hτ hδ ha ha1).integrable_sq
    (periodicPositiveMellinShort_memLp s a τ hs ha ha1 hτ).integrable_sq ?_).trans
      (periodicPositiveMellinShort_sq_mass_bound s a τ hs ha ha1 hτ)
  filter_upwards [periodicPositiveMellinBand_ae_le_short
    (ι := ι) (((Fintype.card ι : ℝ)-s)/2-1) τ δ a (by linarith) hτ hδ] with x hx
  have hb := periodicPositiveMellinBand_nonneg
    (((Fintype.card ι : ℝ)-s)/2-1) τ δ a hτ hδ x
  have hp := periodicPositiveMellinShort_nonneg
    (((Fintype.card ι : ℝ)-s)/2-1) τ a hτ x
  nlinarith

def periodicRieszPositiveBand (s τ δ a : ℝ) (x : PeriodicTorus ι) : ℝ :=
  periodicRieszMellinFactor ι s *
    periodicPositiveMellinBand (((Fintype.card ι : ℝ)-s)/2-1) τ δ a x

lemma periodicRieszPositiveBand_measurable (s τ δ a : ℝ) :
    Measurable (periodicRieszPositiveBand (ι := ι) s τ δ a) :=
  (periodicPositiveMellinBand_measurable _ τ δ a).const_mul _

lemma periodicRieszPositiveBand_memLp (s τ δ a : ℝ)
    (hs : 2*s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    MemLp (periodicRieszPositiveBand (ι := ι) s τ δ a) 2 (periodicHaar ι) :=
  (periodicPositiveMellinBand_memLp s τ δ a hs hτ hδ ha ha1).const_mul _

lemma periodicRieszPositiveBand_sq_mass_bound (s τ δ a : ℝ)
    (hs : 2*s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ x : PeriodicTorus ι, periodicRieszPositiveBand s τ δ a x ^ 2 ∂periodicHaar ι) ≤
      (periodicRieszMellinFactor ι s)^2 * periodicHeatDiagonalSmallConstant ι /
        (((Fintype.card ι : ℝ)/4-s/2)^2) * a ^ ((Fintype.card ι : ℝ)/2-s) := by
  simp only [periodicRieszPositiveBand,mul_pow,integral_const_mul]
  have h := mul_le_mul_of_nonneg_left
    (periodicPositiveMellinBand_sq_mass_bound s τ δ a hs hτ hδ ha ha1)
    (sq_nonneg (periodicRieszMellinFactor ι s))
  convert h using 1 <;> ring

lemma periodicRow_memLp_of_density_cap (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (g : PeriodicTorus ι → ℝ)
    (hg : MemLp g 2 (periodicHaar ι)) (x : PeriodicTorus ι) :
    MemLp (fun y => g (x-y)) 2 (periodicCappedDensityMeasure ρ) :=
  (hg.comp_measurePreserving (periodicHaar_preserving_sub_left x)).of_measure_le_smul
    (by finiteness) (periodicCappedDensityMeasure_le ρ M hρ)

lemma periodicRow_sq_integral_le_of_density_cap (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (g : PeriodicTorus ι → ℝ) (hgm : StronglyMeasurable g)
    (hg : MemLp g 2 (periodicHaar ι)) (x : PeriodicTorus ι) :
    (∫ y, g (x-y)^2 ∂periodicCappedDensityMeasure ρ) ≤ M * ∫ y, g y^2 ∂periodicHaar ι := by
  have hp := hg.comp_measurePreserving (periodicHaar_preserving_sub_left x)
  have hi := hp.integrable_sq.smul_measure (c := ENNReal.ofReal M) (by finiteness)
  have hmono := integral_mono_measure (periodicCappedDensityMeasure_le ρ M hρ)
    (Eventually.of_forall (fun y => sq_nonneg (g (x-y)))) hi
  have hrow : (∫ y, g (x-y)^2 ∂periodicHaar ι) = ∫ y, g y^2 ∂periodicHaar ι := by
    have he := integral_map_of_stronglyMeasurable (μ := periodicHaar ι)
      (periodicHaar_preserving_sub_left x).measurable (hgm.pow 2)
    rw [(periodicHaar_preserving_sub_left x).map_eq] at he
    exact he.symm
  simpa only [integral_smul_measure,ENNReal.toReal_ofReal hM,smul_eq_mul,hrow] using hmono

/-- This improves the crude product-density factor M^2 to M by first using
one Haar-preserving row and then the probability of the outside measure. -/
lemma periodicCenteredPair_row_and_joint_sq_controls (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ)
    (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (g : PeriodicTorus ι → ℝ) (hgm : StronglyMeasurable g)
    (hg : MemLp g 2 (periodicHaar ι)) :
    (∀ᵐ x ∂periodicCappedDensityMeasure ρ,
      (∫ y, hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun p : PeriodicTorus ι × PeriodicTorus ι => g (p.1-p.2)) (x,y)^2
          ∂periodicCappedDensityMeasure ρ) ≤ 16*(M*∫ z, g z^2 ∂periodicHaar ι)) ∧
    (∫ p, hoeffdingCentered (periodicCappedDensityMeasure ρ)
      (fun q : PeriodicTorus ι × PeriodicTorus ι => g (q.1-q.2)) p^2
        ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) ≤
      16*(M*∫ z, g z^2 ∂periodicHaar ι) := by
  let μ := periodicCappedDensityMeasure ρ
  let W : PeriodicTorus ι × PeriodicTorus ι → ℝ := fun p => g (p.1-p.2)
  have hWm : StronglyMeasurable W := hgm.comp_measurable (measurable_fst.sub measurable_snd)
  have hW : MemLp W 2 (μ.prod μ) := periodicPair_memLp_of_density_cap ρ M hρ g hg
  have hr := ae_row_sq_hoeffdingCentered_le μ W hWm hW
    (M*∫ z, g z^2 ∂periodicHaar ι)
    (Eventually.of_forall (periodicRow_sq_integral_le_of_density_cap ρ M hM hρ g hgm hg))
  have hc := (memLp_hoeffdingCentered μ W hWm hW).integrable_sq
  refine ⟨hr,?_⟩
  change (∫ p, hoeffdingCentered μ W p ^ 2 ∂μ.prod μ) ≤ _
  rw [integral_prod (fun p : PeriodicTorus ι × PeriodicTorus ι =>
    hoeffdingCentered μ W p ^ 2) hc]
  calc
    _ ≤ ∫ _ : PeriodicTorus ι, 16*(M*∫ z, g z^2 ∂periodicHaar ι) ∂μ :=
      integral_mono_ae hc.integral_prod_left (integrable_const _) hr
    _ = _ := by simp

/-- Actual upper-scale control: independent of lower time and heat shift. -/
def periodicRieszBandRowControl (s a M : ℝ) (ι : Type*) [Fintype ι] : ℝ :=
  M * ((periodicRieszMellinFactor ι s)^2 * periodicHeatDiagonalSmallConstant ι /
    (((Fintype.card ι : ℝ)/4-s/2)^2)) * a ^ ((Fintype.card ι : ℝ)/2-s)

lemma periodicRieszPositiveBand_centered_square_controls (s τ δ a : ℝ)
    (hs : 2*s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ)
    (ha : 0 < a) (ha1 : a ≤ 1) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ)
    (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    (∀ᵐ x ∂periodicCappedDensityMeasure ρ,
      (∫ y, hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPositiveBand s τ δ a (p.1-p.2))
          (x,y)^2 ∂periodicCappedDensityMeasure ρ) ≤ 16*periodicRieszBandRowControl s a M ι) ∧
    (∫ p, hoeffdingCentered (periodicCappedDensityMeasure ρ)
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPositiveBand s τ δ a (q.1-q.2)) p^2
        ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) ≤
      16*periodicRieszBandRowControl s a M ι := by
  have h := periodicCenteredPair_row_and_joint_sq_controls ρ M hM hρ
    (periodicRieszPositiveBand s τ δ a) (periodicRieszPositiveBand_measurable s τ δ a).stronglyMeasurable
    (periodicRieszPositiveBand_memLp s τ δ a hs hτ hδ ha ha1)
  have hb : M*(∫ z, periodicRieszPositiveBand s τ δ a z^2 ∂periodicHaar ι) ≤
      periodicRieszBandRowControl s a M ι := by
    simpa only [periodicRieszBandRowControl,mul_assoc] using
      mul_le_mul_of_nonneg_left (periodicRieszPositiveBand_sq_mass_bound s τ δ a hs hτ hδ ha ha1) hM
  constructor
  · filter_upwards [h.1] with x hx
    exact hx.trans (mul_le_mul_of_nonneg_left hb (by norm_num))
  · exact h.2.trans (mul_le_mul_of_nonneg_left hb (by norm_num))

lemma exists_periodicRieszBand_small_scale (s c M ε : ℝ)
    (hs : 2*s < (Fintype.card ι : ℝ)) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      16*c^2*periodicRieszBandRowControl s a M ι < ε ∧
      4*|c| *Real.sqrt (periodicRieszBandRowControl s a M ι) < ε := by
  have hp : 0 < (Fintype.card ι : ℝ)/2-s := by linarith
  have ht : Tendsto (fun a : ℝ => periodicRieszBandRowControl s a M ι) (𝓝[>] 0) (𝓝 0) := by
    unfold periodicRieszBandRowControl
    have hr := (tendsto_id : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝[>] 0)).mono_right nhdsWithin_le_nhds
    simpa only [mul_zero,id_eq] using (hr.rpow_const_nhds_zero hp).const_mul
      (M*((periodicRieszMellinFactor ι s)^2 * periodicHeatDiagonalSmallConstant ι /
        (((Fintype.card ι : ℝ)/4-s/2)^2)))
  have htr : Tendsto (fun a => 16*c^2*periodicRieszBandRowControl s a M ι)
      (𝓝[>] 0) (𝓝 0) := by simpa only [mul_zero] using ht.const_mul (16*c^2)
  have hto : Tendsto (fun a => 4*|c| *Real.sqrt (periodicRieszBandRowControl s a M ι))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero,mul_zero,Function.comp_def] using
      ((Real.continuous_sqrt.tendsto 0).comp ht).const_mul (4*|c|)
  have he := (htr.eventually (gt_mem_nhds hε)).and (hto.eventually (gt_mem_nhds hε))
  have hpos : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a := self_mem_nhdsWithin
  have hrange : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a ∧ a < 1 :=
    hpos.and (nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ)<1)))
  obtain ⟨a,hb,hpos,hlt⟩ := (he.and hrange).exists
  exact ⟨a,hpos,hlt,hb.1,hb.2⟩


lemma periodicRieszPositiveBand_centered_memLp (s τ δ a : ℝ)
    (hs : 2*s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ)
    (ha : 0 < a) (ha1 : a ≤ 1) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    MemLp (hoeffdingCentered (periodicCappedDensityMeasure ρ)
      (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPositiveBand s τ δ a (p.1-p.2))) 2
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) :=
  memLp_hoeffdingCentered _ _
    ((periodicRieszPositiveBand_measurable s τ δ a).stronglyMeasurable.comp_measurable
      (measurable_fst.sub measurable_snd))
    (periodicPair_memLp_of_density_cap ρ M hρ _
      (periodicRieszPositiveBand_memLp s τ δ a hs hτ hδ ha ha1))

lemma periodicRieszPositiveBand_scaled_square_controls (s τ δ a c : ℝ)
    (hs : 2*s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ)
    (ha : 0 < a) (ha1 : a ≤ 1) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ)
    (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    (∀ᵐ x ∂periodicCappedDensityMeasure ρ,
      (∫ y, (c • hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPositiveBand s τ δ a (p.1-p.2)))
          (x,y)^2 ∂periodicCappedDensityMeasure ρ) ≤ 16*c^2*periodicRieszBandRowControl s a M ι) ∧
    (∫ p, (c • hoeffdingCentered (periodicCappedDensityMeasure ρ)
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPositiveBand s τ δ a (q.1-q.2))) p^2
        ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) ≤
      16*c^2*periodicRieszBandRowControl s a M ι := by
  obtain ⟨hr,hj⟩ := periodicRieszPositiveBand_centered_square_controls s τ δ a hs hτ hδ ha ha1 ρ M hM hρ
  constructor
  · filter_upwards [hr] with x hx
    simp_rw [Pi.smul_apply,smul_eq_mul,mul_pow]
    rw [integral_const_mul]
    nlinarith [mul_le_mul_of_nonneg_left hx (sq_nonneg c)]
  · simp_rw [Pi.smul_apply,smul_eq_mul,mul_pow]
    rw [integral_const_mul]
    nlinarith [mul_le_mul_of_nonneg_left hj (sq_nonneg c)]

lemma periodicRieszPositiveBand_scaled_operator_bound (s τ δ a c : ℝ)
    (hs : 2*s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ)
    (ha : 0 < a) (ha1 : a ≤ 1) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ)
    (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ‖DGRHS.Kernel.integralOperator
      (c • hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPositiveBand s τ δ a (p.1-p.2)))
      ((periodicRieszPositiveBand_centered_memLp s τ δ a hs hτ hδ ha ha1 ρ M hρ).const_smul c)‖ ≤
      4*|c| *Real.sqrt (periodicRieszBandRowControl s a M ι) := by
  let μ := periodicCappedDensityMeasure ρ
  let W := c • hoeffdingCentered μ
    (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPositiveBand s τ δ a (p.1-p.2))
  let hW := (periodicRieszPositiveBand_centered_memLp s τ δ a hs hτ hδ ha ha1 ρ M hρ).const_smul c
  have hK : 0 ≤ periodicRieszBandRowControl s a M ι := by
    unfold periodicRieszBandRowControl
    have hC := periodicHeatDiagonalSmallConstant_nonneg (ι := ι)
    positivity
  have hb : ‖hW.toLp W‖^2 ≤ 16*c^2*periodicRieszBandRowControl s a M ι := by
    rw [DGRHS.Kernel.norm_toLp_sq]
    exact (periodicRieszPositiveBand_scaled_square_controls s τ δ a c hs hτ hδ ha ha1 ρ M hM hρ).2
  have hright : 0 ≤ 4*|c| *Real.sqrt (periodicRieszBandRowControl s a M ι) := by positivity
  have hsquare : (4*|c| *Real.sqrt (periodicRieszBandRowControl s a M ι))^2 =
      16*c^2*periodicRieszBandRowControl s a M ι := by
    rw [mul_pow,mul_pow,sq_abs,Real.sq_sqrt hK]
    norm_num
  have hn : ‖hW.toLp W‖ ≤ 4*|c| *Real.sqrt (periodicRieszBandRowControl s a M ι) := by
    nlinarith [norm_nonneg (hW.toLp W)]
  exact (DGRHS.Kernel.norm_integralOperator_le W hW).trans hn

end DGRHS.Periodic
