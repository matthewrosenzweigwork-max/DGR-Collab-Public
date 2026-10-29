import DGRHS.Gaussian.PeriodicHeatDiagonalScale
import DGRHS.Gaussian.PeriodicPositiveMellinCutoff
import DGRHS.Gaussian.GaussianShortRangeL2

/-! Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed. The sharp short-time L2 rate follows from the
actual heat diagonal estimate, normalized Haar mass, the existing probability
scale law and its checked Jensen argument. No L2 or small-band estimate is
supplied as a hypothesis. Adaptation of GaussianShortRangeProductL2/ShortRangeL2;
project time is u, with heat u+tau and unshifted Mellin weight. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Classical BigOperators
namespace DGRHS.Periodic
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicGaussianHeat_shifted_real_small_bound (t τ : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hτ : 0 ≤ τ) (x : PeriodicTorus ι) :
    0 ≤ (periodicGaussianHeat (t+τ) x).re ∧
      (periodicGaussianHeat (t+τ) x).re ≤ periodicHeatDiagonalSmallConstant ι *
        t ^ (-((Fintype.card ι : ℝ)/2)) := by
  refine ⟨(periodicGaussianHeat_real_nonneg (t+τ) (add_pos_of_pos_of_nonneg ht hτ) x).1, ?_⟩
  exact (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans
    (periodicGaussianHeat_shifted_small_bound t τ ht ht1 hτ x))

lemma periodicGaussianHeat_shifted_real_sq_integrable (t τ : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hτ : 0 ≤ τ) :
    Integrable (fun x : PeriodicTorus ι => (periodicGaussianHeat (t+τ) x).re ^ 2)
      (periodicHaar ι) := by
  let B := periodicHeatDiagonalSmallConstant ι * t ^ (-((Fintype.card ι : ℝ)/2))
  have hB : 0 ≤ B := mul_nonneg periodicHeatDiagonalSmallConstant_nonneg
    (Real.rpow_nonneg ht.le _)
  apply (integrable_const (B^2)).mono'
    (((Complex.continuous_re.comp (periodicGaussianHeat_continuous (t+τ)
      (add_pos_of_pos_of_nonneg ht hτ))).pow 2).aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    change ‖(periodicGaussianHeat (t+τ) x).re ^ 2‖ ≤ B^2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hx := periodicGaussianHeat_shifted_real_small_bound t τ ht ht1 hτ x
    change (periodicGaussianHeat (t+τ) x).re ^ 2 ≤ B^2
    have hx1 := hx.1
    have hx2 : (periodicGaussianHeat (t+τ) x).re ≤ B := hx.2
    have hprod := mul_nonneg (sub_nonneg.mpr hx2) (add_nonneg hB hx1)
    nlinarith only [hprod]

lemma periodicGaussianHeat_shifted_real_sq_mass_le (t τ : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hτ : 0 ≤ τ) :
    (∫ x : PeriodicTorus ι, (periodicGaussianHeat (t+τ) x).re ^ 2 ∂periodicHaar ι) ≤
      periodicHeatDiagonalSmallConstant ι * t ^ (-((Fintype.card ι : ℝ)/2)) := by
  let B := periodicHeatDiagonalSmallConstant ι * t ^ (-((Fintype.card ι : ℝ)/2))
  calc
    _ ≤ ∫ x : PeriodicTorus ι, B*(periodicGaussianHeat (t+τ) x).re ∂periodicHaar ι := by
      apply integral_mono (periodicGaussianHeat_shifted_real_sq_integrable t τ ht ht1 hτ)
        (((periodicGaussianHeat_integrable (t+τ) (add_pos_of_pos_of_nonneg ht hτ)).re).const_mul B)
      intro x
      have hx := periodicGaussianHeat_shifted_real_small_bound t τ ht ht1 hτ x
      calc
        _ = (periodicGaussianHeat (t+τ) x).re * (periodicGaussianHeat (t+τ) x).re := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hx.2 hx.1
    _ = _ := by rw [integral_const_mul, periodicGaussianHeat_real_integral _
      (add_pos_of_pos_of_nonneg ht hτ), mul_one]

/-- Spatial L2 normalization is u^(d/4), not u^(d/2). -/
def periodicNormalizedHeatScale (τ t : ℝ) (x : PeriodicTorus ι) : ℝ :=
  t ^ ((Fintype.card ι : ℝ)/4) * (periodicGaussianHeat (t+τ) x).re

lemma periodicNormalizedHeatScale_measurable (τ : ℝ) :
    Measurable (fun q : ℝ × PeriodicTorus ι => periodicNormalizedHeatScale τ q.1 q.2) := by
  have hq : Measurable (fun q : ℝ × PeriodicTorus ι => (q.1+τ,q.2)) := by fun_prop
  exact (show Measurable (fun q : ℝ × PeriodicTorus ι => q.1 ^ ((Fintype.card ι : ℝ)/4)) by
    fun_prop).mul (Complex.continuous_re.measurable.comp
      (periodicGaussianHeat_joint_measurable.comp hq))

lemma periodicNormalizedHeatScale_sq_integrable (τ t : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hτ : 0 ≤ τ) :
    Integrable (fun x : PeriodicTorus ι => periodicNormalizedHeatScale τ t x ^ 2)
      (periodicHaar ι) := by
  simpa only [periodicNormalizedHeatScale,mul_pow] using
    (periodicGaussianHeat_shifted_real_sq_integrable t τ ht ht1 hτ).const_mul
      ((t ^ ((Fintype.card ι : ℝ)/4))^2)

lemma periodicNormalizedHeatScale_sq_mass_le (τ t : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hτ : 0 ≤ τ) :
    (∫ x : PeriodicTorus ι, periodicNormalizedHeatScale τ t x ^ 2 ∂periodicHaar ι) ≤
      periodicHeatDiagonalSmallConstant ι := by
  simp only [periodicNormalizedHeatScale,mul_pow,integral_const_mul]
  have h := mul_le_mul_of_nonneg_left
    (periodicGaussianHeat_shifted_real_sq_mass_le (ι := ι) t τ ht ht1 hτ)
    (sq_nonneg (t ^ ((Fintype.card ι : ℝ)/4)))
  apply h.trans_eq
  have hpow : (t ^ ((Fintype.card ι : ℝ)/4))^2 = t ^ ((Fintype.card ι : ℝ)/2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    norm_num
    <;> ring
  rw [hpow, mul_left_comm, ← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, mul_one]

lemma periodic_ae_scale_mem (a ε : ℝ) :
    ∀ᵐ t ∂gaussianShortRangeScaleMeasure a ε, t ∈ Ioc (0:ℝ) ε := by
  unfold gaussianShortRangeScaleMeasure
  apply withDensity_absolutelyContinuous
  exact ae_restrict_mem measurableSet_Ioc

lemma periodicNormalizedHeatScale_product_sq_integrable (a ε τ : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 ≤ τ) :
    Integrable (fun q : ℝ × PeriodicTorus ι => periodicNormalizedHeatScale τ q.1 q.2 ^ 2)
      ((gaussianShortRangeScaleMeasure a ε).prod (periodicHaar ι)) := by
  letI := probability_gaussianShortRangeScaleMeasure a ε ha hε
  have hm := (periodicNormalizedHeatScale_measurable (ι := ι) τ).pow_const 2
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · filter_upwards [periodic_ae_scale_mem a ε] with t ht
    exact periodicNormalizedHeatScale_sq_integrable τ t ht.1 (ht.2.trans hε1) hτ
  · apply (integrable_const (periodicHeatDiagonalSmallConstant ι)).mono'
      hm.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [periodic_ae_scale_mem a ε] with t ht
    simp_rw [Real.norm_of_nonneg (sq_nonneg _)]
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
    exact periodicNormalizedHeatScale_sq_mass_le τ t ht.1 (ht.2.trans hε1) hτ

def periodicNormalizedHeatScaleMean (a ε τ : ℝ) (x : PeriodicTorus ι) : ℝ :=
  ∫ t, periodicNormalizedHeatScale τ t x ∂gaussianShortRangeScaleMeasure a ε

lemma periodicNormalizedHeatScaleMean_stronglyMeasurable (a ε τ : ℝ)
    (ha : 0 < a) (hε : 0 < ε) :
    StronglyMeasurable (periodicNormalizedHeatScaleMean (ι := ι) a ε τ) := by
  letI := probability_gaussianShortRangeScaleMeasure a ε ha hε
  exact (periodicNormalizedHeatScale_measurable τ).stronglyMeasurable.integral_prod_left'

lemma periodicNormalizedHeatScaleMean_ae_sq_le (a ε τ : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 ≤ τ) :
    ∀ᵐ x : PeriodicTorus ι ∂periodicHaar ι,
      periodicNormalizedHeatScaleMean a ε τ x ^ 2 ≤
        ∫ t, periodicNormalizedHeatScale τ t x ^ 2 ∂gaussianShortRangeScaleMeasure a ε := by
  letI := probability_gaussianShortRangeScaleMeasure a ε ha hε
  have hi := periodicNormalizedHeatScale_product_sq_integrable (ι := ι) a ε τ ha hε hε1 hτ
  filter_upwards [hi.prod_left_ae] with x hx
  have hmx : Measurable (fun t : ℝ => periodicNormalizedHeatScale τ t x) :=
    (periodicNormalizedHeatScale_measurable (ι := ι) τ).comp
      (show Measurable (fun t : ℝ => (t, x)) by fun_prop)
  have hm : MemLp (fun t => periodicNormalizedHeatScale τ t x) 2
      (gaussianShortRangeScaleMeasure a ε) :=
    (memLp_two_iff_integrable_sq hmx.aestronglyMeasurable).2 hx
  exact integral_sq_mean_le _ (hm.integrable (by norm_num)) hx

lemma periodicNormalizedHeatScaleMean_memLp (a ε τ : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 ≤ τ) :
    MemLp (periodicNormalizedHeatScaleMean (ι := ι) a ε τ) 2 (periodicHaar ι) := by
  letI := probability_gaussianShortRangeScaleMeasure a ε ha hε
  have hm := periodicNormalizedHeatScaleMean_stronglyMeasurable (ι := ι) a ε τ ha hε
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
  apply (periodicNormalizedHeatScale_product_sq_integrable (ι := ι) a ε τ ha hε hε1 hτ).integral_prod_right.mono'
    (hm.pow 2).aestronglyMeasurable
  filter_upwards [periodicNormalizedHeatScaleMean_ae_sq_le (ι := ι) a ε τ ha hε hε1 hτ] with x hx
  change ‖periodicNormalizedHeatScaleMean a ε τ x ^ 2‖ ≤ _
  simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hx

lemma periodicNormalizedHeatScaleMean_sq_mass_le (a ε τ : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 ≤ τ) :
    (∫ x : PeriodicTorus ι, periodicNormalizedHeatScaleMean a ε τ x ^ 2 ∂periodicHaar ι) ≤
      periodicHeatDiagonalSmallConstant ι := by
  letI := probability_gaussianShortRangeScaleMeasure a ε ha hε
  have hi := periodicNormalizedHeatScale_product_sq_integrable (ι := ι) a ε τ ha hε hε1 hτ
  have hm := (memLp_two_iff_integrable_sq
    (periodicNormalizedHeatScaleMean_stronglyMeasurable (ι := ι) a ε τ ha hε).aestronglyMeasurable).1
    (periodicNormalizedHeatScaleMean_memLp (ι := ι) a ε τ ha hε hε1 hτ)
  calc
    _ ≤ ∫ x : PeriodicTorus ι, ∫ t, periodicNormalizedHeatScale τ t x ^ 2
        ∂gaussianShortRangeScaleMeasure a ε ∂periodicHaar ι :=
      integral_mono_ae hm hi.integral_prod_right
        (periodicNormalizedHeatScaleMean_ae_sq_le a ε τ ha hε hε1 hτ)
    _ = ∫ t, (∫ x : PeriodicTorus ι, periodicNormalizedHeatScale τ t x ^ 2 ∂periodicHaar ι)
        ∂gaussianShortRangeScaleMeasure a ε := (integral_integral_swap hi).symm
    _ ≤ ∫ _t, periodicHeatDiagonalSmallConstant ι ∂gaussianShortRangeScaleMeasure a ε := by
      apply integral_mono_ae hi.integral_prod_left (integrable_const _)
      filter_upwards [periodic_ae_scale_mem a ε] with t ht
      exact periodicNormalizedHeatScale_sq_mass_le τ t ht.1 (ht.2.trans hε1) hτ
    _ = _ := by simp

lemma periodicPositiveMellinShort_eq_scaleMean (s ε τ : ℝ)
    (hs : 2*s < (Fintype.card ι : ℝ)) (hε : 0 < ε) (x : PeriodicTorus ι) :
    periodicPositiveMellinShort (((Fintype.card ι : ℝ)-s)/2-1) τ ε x =
      (ε ^ ((Fintype.card ι : ℝ)/4-s/2) / ((Fintype.card ι : ℝ)/4-s/2)) *
        periodicNormalizedHeatScaleMean ((Fintype.card ι : ℝ)/4-s/2) ε τ x := by
  let a : ℝ := (Fintype.card ι : ℝ)/4-s/2
  have ha : 0 < a := by dsimp [a]; linarith
  have hc : (ε^a/a)*(a*ε^(-a))=1 := by
    rw [Real.rpow_neg hε.le]
    have he : ε^a ≠ 0 := (Real.rpow_pos_of_pos hε a).ne'
    field_simp [ha.ne',he]
  have ht (t : ℝ) (ht : 0 < t) :
      t ^ (a-1) * t ^ ((Fintype.card ι : ℝ)/4) = t ^ (((Fintype.card ι : ℝ)-s)/2-1) := by
    rw [← Real.rpow_add ht]
    congr 1
    dsimp [a]
    ring
  unfold periodicNormalizedHeatScaleMean
  rw [integral_gaussianShortRangeScaleMeasure a ε ha hε, ← integral_const_mul]
  unfold periodicPositiveMellinShort periodicPositiveMellinIntegrand
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht0
  unfold gaussianShortRangeScaleWeight periodicNormalizedHeatScale
  change _ = (ε^a/a)*((a*ε^(-a)*t^(a-1))*(t^((Fintype.card ι : ℝ)/4)*_))
  symm
  calc
    _ = ((ε^a/a)*(a*ε^(-a)))*(t^(a-1)*t^((Fintype.card ι : ℝ)/4))*
        (periodicGaussianHeat (t+τ) x).re := by ring
    _ = _ := by rw [hc,ht t ht0.1,one_mul]

lemma periodicPositiveMellinShort_memLp (s ε τ : ℝ)
    (hs : 2*s < (Fintype.card ι : ℝ)) (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 ≤ τ) :
    MemLp (periodicPositiveMellinShort (ι := ι) (((Fintype.card ι : ℝ)-s)/2-1) τ ε)
      2 (periodicHaar ι) := by
  have he := funext (periodicPositiveMellinShort_eq_scaleMean (ι := ι) s ε τ hs hε)
  rw [he]
  exact (periodicNormalizedHeatScaleMean_memLp _ ε τ (by linarith) hε hε1 hτ).const_mul _

lemma periodicPositiveMellinShort_sq_mass_bound (s ε τ : ℝ)
    (hs : 2*s < (Fintype.card ι : ℝ)) (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 ≤ τ) :
    (∫ x : PeriodicTorus ι,
      periodicPositiveMellinShort (((Fintype.card ι : ℝ)-s)/2-1) τ ε x ^ 2 ∂periodicHaar ι) ≤
      periodicHeatDiagonalSmallConstant ι /
        (((Fintype.card ι : ℝ)/4-s/2)^2) * ε ^ ((Fintype.card ι : ℝ)/2-s) := by
  simp_rw [periodicPositiveMellinShort_eq_scaleMean s ε τ hs hε,mul_pow]
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left
    (periodicNormalizedHeatScaleMean_sq_mass_le (ι := ι) ((Fintype.card ι : ℝ)/4-s/2) ε τ
      (by linarith) hε hε1 hτ)
    (sq_nonneg (ε ^ ((Fintype.card ι : ℝ)/4-s/2) / ((Fintype.card ι : ℝ)/4-s/2)))
  apply h.trans_eq
  rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]
  have he : ((Fintype.card ι : ℝ)/4-s/2)*((2:ℕ):ℝ) = (Fintype.card ι : ℝ)/2-s := by
    norm_num
    <;> ring
  rw [he]
  ring

lemma periodicRieszPositiveShort_memLp (s ε τ : ℝ)
    (hs : 2*s < (Fintype.card ι : ℝ)) (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 ≤ τ) :
    MemLp (periodicRieszPositiveShort (ι := ι) s τ ε) 2 (periodicHaar ι) :=
  (periodicPositiveMellinShort_memLp s ε τ hs hε hε1 hτ).const_mul _

lemma periodicRieszPositiveShort_sq_mass_bound (s ε τ : ℝ)
    (hs : 2*s < (Fintype.card ι : ℝ)) (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 ≤ τ) :
    (∫ x : PeriodicTorus ι, periodicRieszPositiveShort s τ ε x ^ 2 ∂periodicHaar ι) ≤
      (periodicRieszMellinFactor ι s)^2 * periodicHeatDiagonalSmallConstant ι /
        (((Fintype.card ι : ℝ)/4-s/2)^2) * ε ^ ((Fintype.card ι : ℝ)/2-s) := by
  simp only [periodicRieszPositiveShort,mul_pow,integral_const_mul]
  have h := mul_le_mul_of_nonneg_left (periodicPositiveMellinShort_sq_mass_bound
    (ι := ι) s ε τ hs hε hε1 hτ) (sq_nonneg (periodicRieszMellinFactor ι s))
  convert h using 1 <;> ring

end DGRHS.Periodic
