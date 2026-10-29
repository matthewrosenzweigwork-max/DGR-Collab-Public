import LeanResearch.PeriodicAttractiveLogGas.RectangleReflection
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Group.Integral

/-!
# Singular moments on the two normalized reference rectangles

Source Lemma 3.3 (`lem:point-weights`), lines 503--520 of the immutable
manuscript: the disk estimate and its finite weighted-Hölder consequence.
The proof uses the physical Euclidean norm on `PlanarSpace`. Both actual
reference measures are probability measures dominated by planar volume.

The real negative power is totalized at a pole. All moment statements are
unchanged by that null set. The lower bound is deliberately an a.e. statement;
it is not asserted at a pole. Repeated poles and zero weights are allowed.
The finite weighted-Hölder inequality is derived below from Mathlib's weighted
AM--GM theorem; no integrability of a product is assumed.

The original author supplied source only. Current central development evidence
and independent semantic/protected statuses are recorded separately.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal BigOperators Topology

namespace PeriodicAttractiveLogGas
namespace SingularRectangleMoments

/-- The totalized real singular factor. The pole has volume zero. -/
def inverseDistancePower (Y : PlanarSpace) (u : ℝ) (Z : PlanarSpace) : ℝ :=
  ‖Z - Y‖ ^ (-u)

theorem inverseDistancePower_nonneg (Y Z : PlanarSpace) (u : ℝ) :
    0 ≤ inverseDistancePower Y u Z :=
  Real.rpow_nonneg (norm_nonneg _) _

theorem measurable_inverseDistancePower (Y : PlanarSpace) (u : ℝ) :
    Measurable (inverseDistancePower Y u) :=
  ((measurable_id.sub measurable_const).norm.pow_const (-u))

theorem inverseDistancePower_pos {Y Z : PlanarSpace} (hZY : Z ≠ Y) (u : ℝ) :
    0 < inverseDistancePower Y u Z :=
  Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hZY)) _

theorem squareLebesgue_le_volume : squareLebesgue ≤ (volume : Measure PlanarSpace) :=
  Measure.restrict_le_self

theorem rectangleLebesgue_le_volume :
    rectangleLebesgue ≤ (volume : Measure PlanarSpace) := by
  calc
    rectangleLebesgue ≤ (1 : ℝ≥0∞) • volume.restrict closedDoubleRectangle := by
      unfold rectangleLebesgue
      gcongr
      norm_num
    _ ≤ volume := by simpa only [one_smul] using
      (Measure.restrict_le_self (μ := (volume : Measure PlanarSpace))
        (s := closedDoubleRectangle))

/-- All finitely many poles may be removed at once, including repeated poles. -/
theorem ae_avoid_poles {ι : Type*} [Fintype ι] {μ : Measure PlanarSpace}
    (hμ : μ ≪ volume) (Y : ι → PlanarSpace) :
    ∀ᵐ Z ∂μ, ∀ i, Z ≠ Y i :=
  ae_all_iff.mpr fun i ↦ hμ.ae_le ((volume : Measure PlanarSpace).ae_ne (Y i))

/-- Local integrability is proved before using the exact radial integral. -/
theorem integrableOn_unitBall_norm_rpow {u : ℝ} (hu : u < 2) :
    IntegrableOn (fun Z : PlanarSpace ↦ ‖Z‖ ^ (-u)) (ball 0 1) volume := by
  refine integrableOn_ball_of_norm_le_rpow (μ := (volume : Measure PlanarSpace))
    (C := 1) (α := u) (by simp) (by simpa using hu) ?_ ?_
  · exact ae_of_all _ fun Z ↦ by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg Z) _), one_mul]
  · exact (measurable_norm.pow_const (-u)).aestronglyMeasurable

/-- Exact disk integral with actual Euclidean Lebesgue normalization. -/
theorem integral_unitBall_norm_rpow {u : ℝ} (hu : u < 2) :
    (∫ Z in ball (0 : PlanarSpace) 1, ‖Z‖ ^ (-u)) =
      2 * Real.pi / (2 - u) := by
  have hvol : (volume : Measure PlanarSpace).real (ball 0 1) = Real.pi := by
    change (volume (ball (0 : PlanarSpace) 1)).toReal = Real.pi
    rw [EuclideanSpace.volume_ball_fin_two]
    simp [Real.pi_nonneg]
  have hradial :
      (∫ r in Ioi (0 : ℝ), r * (Iio (1 : ℝ)).indicator (fun t ↦ t ^ (-u)) r) =
        1 / (2 - u) := by
    calc
      _ = ∫ r in Ioi (0 : ℝ),
          (Iio (1 : ℝ)).indicator (fun t ↦ t * t ^ (-u)) r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        by_cases h : r < 1 <;> simp [Set.indicator, h]
      _ = ∫ r in Ioo (0 : ℝ) 1, r ^ (1 - u) := by
        rw [setIntegral_indicator measurableSet_Iio]
        change (∫ r in Ioo (0 : ℝ) 1, r * r ^ (-u)) = _
        apply setIntegral_congr_fun measurableSet_Ioo
        intro r hr
        calc
          r * r ^ (-u) = r ^ (1 : ℝ) * r ^ (-u) := by rw [Real.rpow_one]
          _ = r ^ (1 - u) := by rw [← Real.rpow_add hr.1]; congr 1
      _ = ∫ r in (0 : ℝ)..1, r ^ (1 - u) := by
        rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
      _ = 1 / (2 - u) := by
        rw [integral_rpow (Or.inl (by linarith : -1 < 1 - u))]
        have hne : 2 - u ≠ 0 := by linarith
        simp [show 1 - u + 1 = 2 - u by ring, Real.zero_rpow hne]
  calc
    _ = ∫ Z : PlanarSpace,
        (Iio (1 : ℝ)).indicator (fun t ↦ t ^ (-u)) ‖Z‖ := by
      rw [← integral_indicator measurableSet_ball]
      apply integral_congr_ae
      exact ae_of_all _ fun Z ↦ by
        by_cases h : ‖Z‖ < 1 <;> simp [Set.indicator, h]
    _ = 2 * Real.pi *
        ∫ r in Ioi (0 : ℝ), r * (Iio (1 : ℝ)).indicator (fun t ↦ t ^ (-u)) r := by
      rw [integral_fun_norm_addHaar (volume : Measure PlanarSpace)]
      simp only [finrank_euclideanSpace_fin, Nat.cast_ofNat, hvol, Nat.reduceSub,
        pow_one, smul_eq_mul, nsmul_eq_mul]
      ring
    _ = 2 * Real.pi / (2 - u) := by rw [hradial]; ring

/-- Unit-ball truncation, used to separate the integrable pole from the bounded tail. -/
def localInverseDistancePower (Y : PlanarSpace) (u : ℝ) : PlanarSpace → ℝ :=
  (ball Y 1).indicator (inverseDistancePower Y u)

theorem localInverseDistancePower_eq_translate (Y : PlanarSpace) (u : ℝ)
    (Z : PlanarSpace) :
    localInverseDistancePower Y u Z =
      (ball (0 : PlanarSpace) 1).indicator (fun W ↦ ‖W‖ ^ (-u)) (Z - Y) := by
  by_cases h : ‖Z - Y‖ < 1 <;>
    simp [localInverseDistancePower, inverseDistancePower, Set.indicator,
      Metric.mem_ball, dist_eq_norm, h]

theorem localInverseDistancePower_nonneg (Y Z : PlanarSpace) (u : ℝ) :
    0 ≤ localInverseDistancePower Y u Z := by
  by_cases h : Z ∈ ball Y 1 <;>
    simp [localInverseDistancePower, Set.indicator, h,
      inverseDistancePower_nonneg Y Z u]

theorem integrable_localInverseDistancePower (Y : PlanarSpace) {u : ℝ} (hu : u < 2) :
    Integrable (localInverseDistancePower Y u) volume := by
  have h : Integrable ((ball (0 : PlanarSpace) 1).indicator
      (fun W ↦ ‖W‖ ^ (-u))) volume :=
    (integrable_indicator_iff measurableSet_ball).mpr (integrableOn_unitBall_norm_rpow hu)
  exact (h.comp_sub_right Y).congr
    (ae_of_all _ fun Z ↦ (localInverseDistancePower_eq_translate Y u Z).symm)

theorem integral_localInverseDistancePower (Y : PlanarSpace) {u : ℝ} (hu : u < 2) :
    (∫ Z, localInverseDistancePower Y u Z) = 2 * Real.pi / (2 - u) := by
  rw [integral_congr_ae (ae_of_all _ (localInverseDistancePower_eq_translate Y u)),
    integral_sub_right_eq_self, integral_indicator measurableSet_ball,
    integral_unitBall_norm_rpow hu]

theorem inverseDistancePower_le_one_add_local (Y Z : PlanarSpace) {u : ℝ}
    (hu : 0 ≤ u) :
    inverseDistancePower Y u Z ≤ 1 + localInverseDistancePower Y u Z := by
  by_cases h : Z ∈ ball Y 1
  · simp only [localInverseDistancePower, Set.indicator_of_mem h]
    linarith
  · have hr : 1 ≤ ‖Z - Y‖ := by
      simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using h
    simpa only [localInverseDistancePower, Set.indicator_of_notMem h, add_zero,
      inverseDistancePower] using Real.rpow_le_one_of_one_le_of_nonpos hr (neg_nonpos.mpr hu)

/-- The singular-moment estimate applies to either normalized reference rectangle
because both are probability measures dominated by planar volume. -/
theorem inverseDistancePower_integrable_and_integral_le {μ : Measure PlanarSpace}
    [IsProbabilityMeasure μ] (hμ : μ ≤ volume) (Y : PlanarSpace) {u : ℝ}
    (hu0 : 0 ≤ u) (hu2 : u < 2) :
    Integrable (inverseDistancePower Y u) μ ∧
      (∫ Z, inverseDistancePower Y u Z ∂μ) ≤ 1 + 2 * Real.pi / (2 - u) := by
  have hv := integrable_localInverseDistancePower Y hu2
  have hm := hv.mono_measure hμ
  have hb : Integrable (fun Z ↦ 1 + localInverseDistancePower Y u Z) μ :=
    (integrable_const 1).add hm
  have hi : Integrable (inverseDistancePower Y u) μ := by
    refine hb.mono' (measurable_inverseDistancePower Y u).aestronglyMeasurable ?_
    exact ae_of_all _ fun Z ↦ by
      rw [Real.norm_of_nonneg (inverseDistancePower_nonneg Y Z u)]
      exact inverseDistancePower_le_one_add_local Y Z hu0
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ Z, 1 + localInverseDistancePower Y u Z ∂μ :=
      integral_mono_ae hi hb (ae_of_all _ fun Z ↦ inverseDistancePower_le_one_add_local Y Z hu0)
    _ = 1 + ∫ Z, localInverseDistancePower Y u Z ∂μ := by
      rw [integral_add (integrable_const 1) hm]
      simp
    _ ≤ 1 + ∫ Z, localInverseDistancePower Y u Z := by
      exact add_le_add le_rfl (integral_mono_measure hμ
        (ae_of_all _ fun Z ↦ localInverseDistancePower_nonneg Y Z u) hv)
    _ = 1 + 2 * Real.pi / (2 - u) := by rw [integral_localInverseDistancePower Y hu2]

theorem square_inverseDistancePower_integrable_and_integral_le (Y : PlanarSpace)
    {u : ℝ} (hu0 : 0 ≤ u) (hu2 : u < 2) :
    Integrable (inverseDistancePower Y u) squareLebesgue ∧
      (∫ Z, inverseDistancePower Y u Z ∂squareLebesgue) ≤
        1 + 2 * Real.pi / (2 - u) :=
  inverseDistancePower_integrable_and_integral_le squareLebesgue_le_volume Y hu0 hu2

theorem rectangle_inverseDistancePower_integrable_and_integral_le (Y : PlanarSpace)
    {u : ℝ} (hu0 : 0 ≤ u) (hu2 : u < 2) :
    Integrable (inverseDistancePower Y u) rectangleLebesgue ∧
      (∫ Z, inverseDistancePower Y u Z ∂rectangleLebesgue) ≤
        1 + 2 * Real.pi / (2 - u) :=
  inverseDistancePower_integrable_and_integral_le rectangleLebesgue_le_volume Y hu0 hu2

/-- Generalized finite Hölder for nonnegative real functions, including zero
weights. Positive individual integrals are used only to normalize factors.
Product integrability is a conclusion. Weighted AM--GM supplies the domination. -/
theorem finite_weighted_holder {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) (w : ι → ℝ) (f : ι → α → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hm : ∀ i, Measurable (f i)) (hn : ∀ i x, 0 ≤ f i x)
    (hi : ∀ i, Integrable (f i) μ) (hp : ∀ i, 0 < ∫ x, f i x ∂μ) :
    Integrable (fun x ↦ ∏ i, f i x ^ w i) μ ∧
      (∫ x, ∏ i, f i x ^ w i ∂μ) ≤ ∏ i, (∫ x, f i x ∂μ) ^ w i := by
  classical
  let I : ι → ℝ := fun i ↦ ∫ x, f i x ∂μ
  let P : ℝ := ∏ i, I i ^ w i
  let q : α → ℝ := fun x ↦ ∏ i, (f i x / I i) ^ w i
  let A : α → ℝ := fun x ↦ ∑ i, w i * (f i x / I i)
  have hIp : ∀ i, 0 < I i := hp
  have hP : 0 < P := Finset.prod_pos fun i _ ↦ Real.rpow_pos_of_pos (hIp i) _
  have hqn : ∀ x, 0 ≤ q x := fun x ↦
    Finset.prod_nonneg fun i _ ↦ Real.rpow_nonneg (div_nonneg (hn i x) (hIp i).le) _
  have hqm : Measurable q :=
    Finset.measurable_prod _ fun i _ ↦ ((hm i).div_const (I i)).pow_const (w i)
  have hAi : Integrable A μ :=
    integrable_finsetSum _ fun i _ ↦ ((hi i).div_const (I i)).const_mul (w i)
  have hqA : ∀ x, q x ≤ A x := fun x ↦
    Real.geom_mean_le_arith_mean_weighted Finset.univ w (fun i ↦ f i x / I i)
      (fun i _ ↦ hw i) hw1 (fun i _ ↦ div_nonneg (hn i x) (hIp i).le)
  have hqi : Integrable q μ := hAi.mono' hqm.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by rw [Real.norm_of_nonneg (hqn x)]; exact hqA x)
  have hqeq : ∀ x, q x = (∏ i, f i x ^ w i) / P := by
    intro x
    calc
      q x = ∏ i, f i x ^ w i / I i ^ w i := by
        apply Finset.prod_congr rfl
        intro i hi
        exact Real.div_rpow (hn i x) (hIp i).le (w i)
      _ = _ := Finset.prod_div_distrib _ _
  have hfactor : ∀ x, (∏ i, f i x ^ w i) = P * q x := by
    intro x
    rw [hqeq x]
    field_simp [hP.ne']
  have hfi : Integrable (fun x ↦ ∏ i, f i x ^ w i) μ :=
    (hqi.const_mul P).congr (ae_of_all _ fun x ↦ (hfactor x).symm)
  have hAone : (∫ x, A x ∂μ) = 1 := by
    change (∫ x, ∑ i, w i * (f i x / I i) ∂μ) = 1
    rw [integral_finsetSum _ fun i _ ↦ ((hi i).div_const (I i)).const_mul (w i)]
    calc
      _ = ∑ i, w i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_const_mul, integral_div]
        change w i * (I i / I i) = w i
        simp [(hIp i).ne']
      _ = 1 := hw1
  refine ⟨hfi, ?_⟩
  calc
    _ = P * ∫ x, q x ∂μ := by
      rw [integral_congr_ae (ae_of_all _ hfactor), integral_const_mul]
    _ ≤ P * ∫ x, A x ∂μ :=
      mul_le_mul_of_nonneg_left (integral_mono_ae hqi hAi (ae_of_all _ hqA)) hP.le
    _ = P := by rw [hAone, mul_one]

/-- The real product appearing in the source, with no distinctness requirement. -/
def poleProduct {ι : Type*} [Fintype ι] (Y : ι → PlanarSpace) (w : ι → ℝ)
    (Z : PlanarSpace) : ℝ :=
  ∏ i, inverseDistancePower (Y i) (w i) Z

theorem poleProduct_nonneg {ι : Type*} [Fintype ι] (Y : ι → PlanarSpace)
    (w : ι → ℝ) (Z : PlanarSpace) : 0 ≤ poleProduct Y w Z :=
  Finset.prod_nonneg fun i _ ↦ inverseDistancePower_nonneg (Y i) Z (w i)

theorem measurable_poleProduct {ι : Type*} [Fintype ι] (Y : ι → PlanarSpace)
    (w : ι → ℝ) : Measurable (poleProduct Y w) :=
  Finset.measurable_prod _ fun i _ ↦ measurable_inverseDistancePower (Y i) (w i)

theorem weights_eq_zero_of_sum_eq_zero {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hκ : ∑ i, w i = 0) : ∀ i, w i = 0 := by
  intro i
  exact le_antisymm
    (calc w i ≤ ∑ j, w j := Finset.single_le_sum (fun j _ ↦ hw j) (Finset.mem_univ i)
          _ = 0 := hκ) (hw i)

theorem poleProduct_eq_one_of_sum_eq_zero {ι : Type*} [Fintype ι]
    (Y : ι → PlanarSpace) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hκ : ∑ i, w i = 0) (Z : PlanarSpace) : poleProduct Y w Z = 1 := by
  have hw0 := weights_eq_zero_of_sum_eq_zero w hw hκ
  simp [poleProduct, inverseDistancePower, hw0]

theorem integral_inverseDistancePower_pos {μ : Measure PlanarSpace}
    [IsProbabilityMeasure μ] (hμ : μ ≤ volume) (Y : PlanarSpace) {u : ℝ}
    (hu0 : 0 ≤ u) (hu2 : u < 2) :
    0 < ∫ Z, inverseDistancePower Y u Z ∂μ := by
  have hi := (inverseDistancePower_integrable_and_integral_le hμ Y hu0 hu2).1
  have hn : 0 ≤ ∫ Z, inverseDistancePower Y u Z ∂μ :=
    integral_nonneg (fun Z ↦ inverseDistancePower_nonneg Y Z u)
  have hp : ∀ᵐ Z ∂μ, 0 < inverseDistancePower Y u Z := by
    filter_upwards [hμ.absolutelyContinuous.ae_le
      ((volume : Measure PlanarSpace).ae_ne Y)] with Z hZ
    exact inverseDistancePower_pos hZ u
  by_contra h
  have hz : (∫ Z, inverseDistancePower Y u Z ∂μ) = 0 := le_antisymm (le_of_not_gt h) hn
  have heq := (integral_eq_zero_iff_of_nonneg
    (fun Z ↦ inverseDistancePower_nonneg Y Z u) hi).mp hz
  obtain ⟨Z, hZ0, hZp⟩ := (heq.and hp).exists
  change inverseDistancePower Y u Z = 0 at hZ0
  exact (ne_of_gt hZp) hZ0

/-- The exact source generalized-Hölder step for positive total weight.
The product on the right may include zero weights: their factors equal one.
The full moment is proved integrable, rather than assigned the totalized value
of an undefined Bochner integral. -/
theorem poleProduct_moment_of_sum_pos {ι : Type*} [Fintype ι]
    {μ : Measure PlanarSpace} [IsProbabilityMeasure μ] (hμ : μ ≤ volume)
    (Y : ι → PlanarSpace) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hκ : 0 < ∑ i, w i) {s : ℝ} (hs : 0 < s) (hsκ : s * (∑ i, w i) < 2) :
    Integrable (fun Z ↦ poleProduct Y w Z ^ s) μ ∧
      (∫ Z, poleProduct Y w Z ^ s ∂μ) ≤
        ∏ i, (∫ Z, inverseDistancePower (Y i) (s * (∑ j, w j)) Z ∂μ) ^
          (w i / (∑ j, w j)) ∧
      (∫ Z, poleProduct Y w Z ^ s ∂μ) ≤
        1 + 2 * Real.pi / (2 - s * (∑ i, w i)) := by
  classical
  let κ : ℝ := ∑ i, w i
  let a : ι → ℝ := fun i ↦ w i / κ
  let f : ι → PlanarSpace → ℝ := fun i ↦ inverseDistancePower (Y i) (s * κ)
  let C : ℝ := 1 + 2 * Real.pi / (2 - s * κ)
  have hk : 0 < κ := hκ
  have ha : ∀ i, 0 ≤ a i := fun i ↦ div_nonneg (hw i) hk.le
  have ha1 : ∑ i, a i = 1 := by
    dsimp [a]
    rw [← Finset.sum_div]
    exact div_self hk.ne'
  have hsκ0 : 0 ≤ s * κ := mul_nonneg hs.le hk.le
  have hm : ∀ i, Measurable (f i) := fun i ↦ measurable_inverseDistancePower (Y i) (s * κ)
  have hn : ∀ i Z, 0 ≤ f i Z := fun i Z ↦ inverseDistancePower_nonneg (Y i) Z (s * κ)
  have hi : ∀ i, Integrable (f i) μ := fun i ↦
    (inverseDistancePower_integrable_and_integral_le hμ (Y i) hsκ0 hsκ).1
  have hp : ∀ i, 0 < ∫ Z, f i Z ∂μ := fun i ↦
    integral_inverseDistancePower_pos hμ (Y i) hsκ0 hsκ
  have hb : ∀ i, (∫ Z, f i Z ∂μ) ≤ C := fun i ↦
    (inverseDistancePower_integrable_and_integral_le hμ (Y i) hsκ0 hsκ).2
  have hden : 0 < 2 - s * κ := by linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have heq : ∀ Z, poleProduct Y w Z ^ s = ∏ i, f i Z ^ a i := by
    intro Z
    rw [poleProduct, ← Real.finsetProd_rpow Finset.univ
      (fun i ↦ inverseDistancePower (Y i) (w i) Z)
      (fun i _ ↦ inverseDistancePower_nonneg (Y i) Z (w i)) s]
    apply Finset.prod_congr rfl
    intro i hi
    change (‖Z - Y i‖ ^ (-w i)) ^ s = (‖Z - Y i‖ ^ (-(s * κ))) ^ (w i / κ)
    rw [← Real.rpow_mul (norm_nonneg _), ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    field_simp [hk.ne']
  obtain ⟨hprod, hholder⟩ := finite_weighted_holder μ a f ha ha1 hm hn hi hp
  have hmoment : Integrable (fun Z ↦ poleProduct Y w Z ^ s) μ :=
    hprod.congr (ae_of_all _ fun Z ↦ (heq Z).symm)
  have hsource : (∫ Z, poleProduct Y w Z ^ s ∂μ) ≤
      ∏ i, (∫ Z, f i Z ∂μ) ^ a i := by
    rw [integral_congr_ae (ae_of_all _ heq)]
    exact hholder
  refine ⟨hmoment, hsource, ?_⟩
  calc
    _ ≤ ∏ i, (∫ Z, f i Z ∂μ) ^ a i := hsource
    _ ≤ ∏ i, C ^ a i := Finset.prod_le_prod₀
      (fun i _ ↦ Real.rpow_nonneg (hp i).le _)
      (fun i _ ↦ Real.rpow_le_rpow (hp i).le (hb i) (ha i))
    _ = C := by rw [← Real.rpow_sum_of_pos hC a Finset.univ, ha1, Real.rpow_one]

/-- The moment estimate includes zero total weight and the empty pole family. -/
theorem poleProduct_moment {ι : Type*} [Fintype ι]
    {μ : Measure PlanarSpace} [IsProbabilityMeasure μ] (hμ : μ ≤ volume)
    (Y : ι → PlanarSpace) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    {s : ℝ} (hs : 0 < s) (hsκ : s * (∑ i, w i) < 2) :
    Integrable (fun Z ↦ poleProduct Y w Z ^ s) μ ∧
      (∫ Z, poleProduct Y w Z ^ s ∂μ) ≤
        1 + 2 * Real.pi / (2 - s * (∑ i, w i)) := by
  have hk0 : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ ↦ hw i
  rcases eq_or_lt_of_le hk0 with hk | hk
  · have hk' : ∑ i, w i = 0 := hk.symm
    have heq : (fun Z ↦ poleProduct Y w Z ^ s) = (fun _ : PlanarSpace ↦ (1 : ℝ)) := by
      funext Z
      rw [poleProduct_eq_one_of_sum_eq_zero Y w hw hk', Real.one_rpow]
    rw [heq]
    refine ⟨integrable_const 1, ?_⟩
    simp only [integral_const, probReal_univ, one_smul, hk', mul_zero, sub_zero]
    have := Real.pi_nonneg
    linarith
  · obtain ⟨hi, _, hb⟩ := poleProduct_moment_of_sum_pos hμ Y w hw hk hs hsκ
    exact ⟨hi, hb⟩

/-- The source normalization integral bound, uniform over all pole positions
and all nonnegative weight families of total at most one quarter. -/
theorem poleProduct_first_moment {ι : Type*} [Fintype ι]
    {μ : Measure PlanarSpace} [IsProbabilityMeasure μ] (hμ : μ ≤ volume)
    (Y : ι → PlanarSpace) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hκ : ∑ i, w i ≤ 1 / 4) :
    Integrable (poleProduct Y w) μ ∧
      (∫ Z, poleProduct Y w Z ∂μ) ≤ 1 + 8 * Real.pi / 7 := by
  obtain ⟨hi, hb⟩ := poleProduct_moment hμ Y w hw (s := 1) (by norm_num) (by linarith)
  simp only [Real.rpow_one, one_mul] at hi hb
  refine ⟨hi, hb.trans ?_⟩
  have hd : (7 / 4 : ℝ) ≤ 2 - ∑ i, w i := by linarith
  have hh := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * Real.pi)
    (by norm_num : (0 : ℝ) < 7 / 4) hd
  calc
    1 + 2 * Real.pi / (2 - ∑ i, w i) ≤ 1 + 2 * Real.pi / (7 / 4) := add_le_add le_rfl hh
    _ = 1 + 8 * Real.pi / 7 := by ring

/-- The fourth real moment in the source, with the exact uniform constant. -/
theorem poleProduct_fourth_moment {ι : Type*} [Fintype ι]
    {μ : Measure PlanarSpace} [IsProbabilityMeasure μ] (hμ : μ ≤ volume)
    (Y : ι → PlanarSpace) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hκ : ∑ i, w i ≤ 1 / 4) :
    Integrable (fun Z ↦ |poleProduct Y w Z| ^ (4 : ℕ)) μ ∧
      (∫ Z, |poleProduct Y w Z| ^ (4 : ℕ) ∂μ) ≤ 1 + 2 * Real.pi := by
  obtain ⟨hi, hb⟩ := poleProduct_moment hμ Y w hw (s := 4) (by norm_num) (by linarith)
  have heq : (fun Z ↦ |poleProduct Y w Z| ^ (4 : ℕ)) =
      (fun Z ↦ poleProduct Y w Z ^ (4 : ℝ)) := by
    funext Z
    rw [abs_of_nonneg (poleProduct_nonneg Y w Z)]
    exact (Real.rpow_natCast (poleProduct Y w Z) 4).symm
  rw [heq]
  refine ⟨hi, hb.trans ?_⟩
  have hd : (1 : ℝ) ≤ 2 - 4 * ∑ i, w i := by linarith
  have hh := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * Real.pi) zero_lt_one hd
  simpa only [div_one] using add_le_add le_rfl hh

theorem square_poleProduct_moment {ι : Type*} [Fintype ι]
    (Y : ι → PlanarSpace) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    {s : ℝ} (hs : 0 < s) (hsκ : s * (∑ i, w i) < 2) :
    Integrable (fun Z ↦ poleProduct Y w Z ^ s) squareLebesgue ∧
      (∫ Z, poleProduct Y w Z ^ s ∂squareLebesgue) ≤
        1 + 2 * Real.pi / (2 - s * (∑ i, w i)) :=
  poleProduct_moment squareLebesgue_le_volume Y w hw hs hsκ

theorem rectangle_poleProduct_moment {ι : Type*} [Fintype ι]
    (Y : ι → PlanarSpace) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    {s : ℝ} (hs : 0 < s) (hsκ : s * (∑ i, w i) < 2) :
    Integrable (fun Z ↦ poleProduct Y w Z ^ s) rectangleLebesgue ∧
      (∫ Z, poleProduct Y w Z ^ s ∂rectangleLebesgue) ≤
        1 + 2 * Real.pi / (2 - s * (∑ i, w i)) :=
  poleProduct_moment rectangleLebesgue_le_volume Y w hw hs hsκ

/-- Pointwise lower bound only away from the pole set. This restriction is
essential for totalized real negative powers. -/
theorem poleProduct_lower_of_ne_poles {ι : Type*} [Fintype ι]
    (Y : ι → PlanarSpace) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    {D : ℝ} (hD : 0 < D) {Z : PlanarSpace} (hZ : ∀ i, Z ≠ Y i)
    (hd : ∀ i, ‖Z - Y i‖ ≤ D) :
    D ^ (-(∑ i, w i)) ≤ poleProduct Y w Z := by
  calc
    D ^ (-(∑ i, w i)) = ∏ i, D ^ (-w i) := by
      rw [← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hD]
    _ ≤ poleProduct Y w Z := Finset.prod_le_prod₀
      (fun i _ ↦ Real.rpow_nonneg hD.le _)
      (fun i _ ↦ Real.rpow_le_rpow_of_nonpos
        (norm_pos_iff.mpr (sub_ne_zero.mpr (hZ i))) (hd i) (neg_nonpos.mpr (hw i)))

/-- The source lower bound with its actual measure-theoretic meaning. Only
absolute continuity is required here, and no separation of the poles is used. -/
theorem ae_poleProduct_lower {ι : Type*} [Fintype ι] {μ : Measure PlanarSpace}
    (hμ : μ ≪ volume) (Y : ι → PlanarSpace) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    {D : ℝ} (hD : 0 < D) (hd : ∀ᵐ Z ∂μ, ∀ i, ‖Z - Y i‖ ≤ D) :
    ∀ᵐ Z ∂μ, D ^ (-(∑ i, w i)) ≤ poleProduct Y w Z := by
  filter_upwards [ae_avoid_poles hμ Y, hd] with Z hZ hdZ
  exact poleProduct_lower_of_ne_poles Y w hw hD hZ hdZ

/-- The lower bound can be integrated after the separately proved first-moment
integrability; in particular, normalization is strictly positive. -/
theorem integral_poleProduct_lower {ι : Type*} [Fintype ι]
    {μ : Measure PlanarSpace} [IsProbabilityMeasure μ] (hμ : μ ≤ volume)
    (Y : ι → PlanarSpace) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hκ : ∑ i, w i ≤ 1 / 4) {D : ℝ} (hD : 0 < D)
    (hd : ∀ᵐ Z ∂μ, ∀ i, ‖Z - Y i‖ ≤ D) :
    D ^ (-(∑ i, w i)) ≤ ∫ Z, poleProduct Y w Z ∂μ := by
  have hi := (poleProduct_first_moment hμ Y w hw hκ).1
  have h := integral_mono_ae (integrable_const (D ^ (-(∑ i, w i)))) hi
    (ae_poleProduct_lower hμ.absolutelyContinuous Y w hw hD hd)
  simpa using h

end SingularRectangleMoments
end PeriodicAttractiveLogGas
