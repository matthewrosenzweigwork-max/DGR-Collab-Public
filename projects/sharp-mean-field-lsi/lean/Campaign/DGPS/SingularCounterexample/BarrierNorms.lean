import DGPS.SingularCounterexample.PoissonPeak
import DGPS.SingularCounterexample.Scales
import DGPS.SingularCounterexample.BarrierKernel
import DGPS.Examples.PositiveH1.Nonlinear
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import SharpSymmetricLSI.Paper.CosineSharpPoincare

/-!
# Norm estimates for the Poisson peaks and singular barrier
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.SingularCounterexample

/-- The weighted Fourier norm associated with `MemCircleHs`, on its finite-norm domain. -/
noncomputable def circleHsNorm (s : ℝ) (f : Circle → ℝ) : ℝ :=
  Real.sqrt (∑' n : ℤ, circleHsWeight s n * ‖coeff1 f n‖ ^ 2)

private theorem continuous_poissonPeak {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Continuous (poissonPeak r) :=
  SharpLSI.continuous_of_liftT' (poissonPeak_smooth_periodic hr0 hr1).continuous

theorem memLp_poissonPeak {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (p : ℝ≥0∞) :
    MemLp (poissonPeak r) p (haar 1) :=
  Examples.PositiveH1.Nonlinear.memLp_of_cont (continuous_poissonPeak hr0 hr1) p

theorem integrable_poissonPeak_rpow {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (p : ℝ) :
    Integrable (fun x => (poissonPeak r x) ^ p) (haar 1) :=
  Examples.PositiveH1.Nonlinear.integrable_of_cont
    ((continuous_poissonPeak hr0 hr1).rpow_const
      (fun x => Or.inl (poissonPeak_pos hr0 hr1 x).ne'))

private theorem poissonPeak_rpow_le {r p : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hp : 1 ≤ p) (x : Circle) : (poissonPeak r x) ^ p ≤ poissonPeak r x := by
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge
    (poissonPeak_pos hr0 hr1 x) (poissonPeak_le_one hr0 hr1 x) hp

private theorem hasSum_geometric_natAbs {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    HasSum (fun n : ℤ => t ^ n.natAbs) ((1 + t) / (1 - t)) := by
  have hp : HasSum (fun n : ℕ => t ^ (Int.natAbs (n : ℤ))) ((1 - t)⁻¹) := by
    simpa using hasSum_geometric_of_lt_one ht0 ht1
  have hn : HasSum (fun n : ℕ => t ^ (Int.natAbs (-((n : ℤ) + 1))))
      (t * (1 - t)⁻¹) := by
    convert (hasSum_geometric_of_lt_one ht0 ht1).mul_left t using 1
    funext n
    rw [show -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) by omega]
    change t ^ (n + 1) = t * t ^ n
    rw [pow_succ]
    ring
  have hs := HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => t ^ n.natAbs) hp hn
  convert hs using 1
  field_simp

private theorem hasSum_sq_geometric_natAbs {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    HasSum (fun n : ℤ => (n : ℝ) ^ 2 * t ^ n.natAbs)
      (2 * t * (1 + t) / (1 - t) ^ 3) := by
  have hnorm : ‖t‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg ht0] using ht1
  have h := hasSum_sq_mul_geometric_of_norm_lt_one hnorm
  have hp : HasSum (fun n : ℕ => ((n : ℤ) : ℝ) ^ 2 * t ^ (Int.natAbs (n : ℤ)))
      (t * (1 + t) / (1 - t) ^ 3) := by simpa using h
  have htail : HasSum (fun n : ℕ => (n + 1 : ℝ) ^ 2 * t ^ (n + 1))
      (t * (1 + t) / (1 - t) ^ 3) := by
    have hh := (hasSum_nat_add_iff' 1).mpr h
    simpa using hh
  have hn : HasSum
      (fun n : ℕ => ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2 *
        t ^ (Int.natAbs (-((n : ℤ) + 1))))
      (t * (1 + t) / (1 - t) ^ 3) := by
    convert htail using 1
    funext n
    rw [show -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) by omega]
    rw [Int.natAbs_neg, Int.natAbs_natCast]
    push_cast
    ring
  have hs := HasSum.of_nat_of_neg_add_one
    (f := fun n : ℤ => (n : ℝ) ^ 2 * t ^ n.natAbs) hp hn
  convert hs using 1
  ring

private theorem rpow_le_one_add {x s : ℝ} (hx : 0 ≤ x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    x ^ s ≤ 1 + x := by
  by_cases hx1 : x ≤ 1
  · exact (Real.rpow_le_one hx hx1 hs0).trans (by linarith)
  · exact (Real.rpow_le_self_of_one_le (le_of_lt (lt_of_not_ge hx1)) hs1).trans
      (by linarith)

/-- Rescale frequencies by a positive width before replacing the fractional weight by a
quadratic weight. This retains the exact width exponent in the peak estimate. -/
private theorem circleHsWeight_le_rescaled {δ s : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (n : ℤ) :
    circleHsWeight s n ≤ δ ^ (-2 * s) * (2 + δ ^ 2 * (2 * Real.pi * (n : ℝ)) ^ 2) := by
  have hδsq : δ ^ 2 ≤ 1 := by nlinarith
  have h := rpow_le_one_add
    (mul_nonneg (sq_nonneg δ) (show 0 ≤ 1 + (2 * Real.pi * (n : ℝ)) ^ 2 by positivity))
    hs0 hs1
  have hprod : (δ ^ 2 * (1 + (2 * Real.pi * (n : ℝ)) ^ 2)) ^ s =
      δ ^ (2 * s) * circleHsWeight s n := by
    unfold circleHsWeight
    rw [Real.mul_rpow (sq_nonneg δ) (by positivity), ← Real.rpow_natCast δ 2,
      ← Real.rpow_mul hδ0.le]
    norm_num
  rw [hprod] at h
  have hbound : δ ^ (2 * s) * circleHsWeight s n ≤
      2 + δ ^ 2 * (2 * Real.pi * (n : ℝ)) ^ 2 := by nlinarith
  have hinv : δ ^ (-2 * s) * δ ^ (2 * s) = 1 := by
    rw [← Real.rpow_add hδ0, show -2 * s + 2 * s = 0 by ring, Real.rpow_zero]
  calc
    circleHsWeight s n = δ ^ (-2 * s) * (δ ^ (2 * s) * circleHsWeight s n) := by
      rw [← mul_assoc, hinv, one_mul]
    _ ≤ δ ^ (-2 * s) * (2 + δ ^ 2 * (2 * Real.pi * (n : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hδ0.le _)

private theorem geometric_natAbs_le_width {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∑' n : ℤ, (r ^ 2) ^ n.natAbs) ≤ 2 / (1 - r) := by
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hden : 0 < 1 - r ^ 2 := sub_pos.mpr hr2
  have hδ : 0 < 1 - r := sub_pos.mpr hr1
  have hdd : 1 - r ≤ 1 - r ^ 2 := by
    nlinarith [mul_nonneg hr0.le (sub_nonneg.mpr hr1.le)]
  rw [(hasSum_geometric_natAbs (sq_nonneg r) hr2).tsum_eq]
  apply (div_le_div_iff₀ hden hδ).2
  calc
    (1 + r ^ 2) * (1 - r) ≤ 2 * (1 - r) :=
      mul_le_mul_of_nonneg_right (by linarith) hδ.le
    _ ≤ 2 * (1 - r ^ 2) := mul_le_mul_of_nonneg_left hdd (by norm_num)

private theorem sq_geometric_natAbs_le_width {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∑' n : ℤ, (n : ℝ) ^ 2 * (r ^ 2) ^ n.natAbs) ≤ 4 / (1 - r) ^ 3 := by
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hden : 0 < 1 - r ^ 2 := sub_pos.mpr hr2
  have hδ : 0 < 1 - r := sub_pos.mpr hr1
  have hdd : 1 - r ≤ 1 - r ^ 2 := by
    nlinarith [mul_nonneg hr0.le (sub_nonneg.mpr hr1.le)]
  have hcube : (1 - r) ^ 3 ≤ (1 - r ^ 2) ^ 3 := by gcongr
  have hnumer : 2 * r ^ 2 * (1 + r ^ 2) ≤ 4 := by
    have hprod : r ^ 2 * (1 + r ^ 2) ≤ 2 := by
      calc
        r ^ 2 * (1 + r ^ 2) ≤ 1 * (1 + r ^ 2) :=
          mul_le_mul_of_nonneg_right hr2.le (by positivity)
        _ ≤ 2 := by nlinarith
    nlinarith
  rw [(hasSum_sq_geometric_natAbs (sq_nonneg r) hr2).tsum_eq]
  apply (div_le_div_iff₀ (pow_pos hden 3) (pow_pos hδ 3)).2
  calc
    (2 * r ^ 2 * (1 + r ^ 2)) * (1 - r) ^ 3 ≤ 4 * (1 - r) ^ 3 :=
      mul_le_mul_of_nonneg_right hnumer (pow_nonneg hδ.le 3)
    _ ≤ 4 * (1 - r ^ 2) ^ 3 := mul_le_mul_of_nonneg_left hcube (by norm_num)


private theorem peakScale_bounds {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    0 ≤ poissonPeakScale r ∧ poissonPeakScale r ≤ 1 - r := by
  have hδ : 0 < 1 - r := sub_pos.mpr hr1
  have hd : 0 < 1 + r := by linarith
  unfold poissonPeakScale
  refine ⟨div_nonneg hδ.le hd.le, (div_le_iff₀ hd).2 ?_⟩
  nlinarith [mul_nonneg hδ.le hr0.le]

private theorem weighted_geometric_peak_bound {r s : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Summable (fun n : ℤ => circleHsWeight s n *
      ((poissonPeakScale r) ^ 2 * (r ^ 2) ^ n.natAbs)) ∧
      (∑' n : ℤ, circleHsWeight s n *
        ((poissonPeakScale r) ^ 2 * (r ^ 2) ^ n.natAbs)) ≤
          (4 + 16 * Real.pi ^ 2) * (1 - r) ^ (1 - 2 * s) := by
  let δ := 1 - r
  let a := poissonPeakScale r
  let t := r ^ 2
  have hδ : 0 < δ := sub_pos.mpr hr1
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith
  have ht0 : 0 ≤ t := sq_nonneg r
  have ht1 : t < 1 := by dsimp [t]; nlinarith
  let F : ℤ → ℝ := fun n => a ^ 2 * δ ^ (-2 * s) *
    (2 * t ^ n.natAbs + δ ^ 2 * (2 * Real.pi) ^ 2 * ((n : ℝ) ^ 2 * t ^ n.natAbs))
  have hF : HasSum F (a ^ 2 * δ ^ (-2 * s) *
      (2 * ((1 + t) / (1 - t)) + δ ^ 2 * (2 * Real.pi) ^ 2 *
        (2 * t * (1 + t) / (1 - t) ^ 3))) :=
    (((hasSum_geometric_natAbs ht0 ht1).mul_left 2).add
      ((hasSum_sq_geometric_natAbs ht0 ht1).mul_left (δ ^ 2 * (2 * Real.pi) ^ 2))).mul_left
        (a ^ 2 * δ ^ (-2 * s))
  have hpoint (n : ℤ) : circleHsWeight s n * (a ^ 2 * t ^ n.natAbs) ≤ F n := by
    calc
      circleHsWeight s n * (a ^ 2 * t ^ n.natAbs) ≤
          (δ ^ (-2 * s) * (2 + δ ^ 2 * (2 * Real.pi * (n : ℝ)) ^ 2)) *
            (a ^ 2 * t ^ n.natAbs) :=
        mul_le_mul_of_nonneg_right (circleHsWeight_le_rescaled hδ hδ1 hs0 hs1 n)
          (mul_nonneg (sq_nonneg a) (pow_nonneg ht0 _))
      _ = F n := by dsimp [F]; ring
  have hsum : Summable (fun n : ℤ => circleHsWeight s n * (a ^ 2 * t ^ n.natAbs)) :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity)) hpoint hF.summable
  refine ⟨hsum, ?_⟩
  have hG0 := geometric_natAbs_le_width hr0 hr1
  have hG2 := sq_geometric_natAbs_le_width hr0 hr1
  rw [(hasSum_geometric_natAbs ht0 ht1).tsum_eq] at hG0
  rw [(hasSum_sq_geometric_natAbs ht0 ht1).tsum_eq] at hG2
  have hinner : 2 * ((1 + t) / (1 - t)) + δ ^ 2 * (2 * Real.pi) ^ 2 *
      (2 * t * (1 + t) / (1 - t) ^ 3) ≤ (4 + 16 * Real.pi ^ 2) / δ := by
    calc
      _ ≤ 2 * (2 / δ) + δ ^ 2 * (2 * Real.pi) ^ 2 * (4 / δ ^ 3) := by gcongr
      _ = (4 + 16 * Real.pi ^ 2) / δ := by field_simp; ring
  have ha := peakScale_bounds hr0 hr1
  have haSq : a ^ 2 ≤ δ ^ 2 := by
    simpa only [pow_two] using mul_le_mul ha.2 ha.2 ha.1 hδ.le
  calc
    (∑' n : ℤ, circleHsWeight s n * (a ^ 2 * t ^ n.natAbs)) ≤ ∑' n : ℤ, F n :=
      Summable.tsum_le_tsum hpoint hsum hF.summable
    _ = a ^ 2 * δ ^ (-2 * s) *
        (2 * ((1 + t) / (1 - t)) + δ ^ 2 * (2 * Real.pi) ^ 2 *
          (2 * t * (1 + t) / (1 - t) ^ 3)) := hF.tsum_eq
    _ ≤ a ^ 2 * δ ^ (-2 * s) * ((4 + 16 * Real.pi ^ 2) / δ) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = a ^ 2 * (δ ^ (-2 * s) * ((4 + 16 * Real.pi ^ 2) / δ)) := by ring
    _ ≤ δ ^ 2 * (δ ^ (-2 * s) * ((4 + 16 * Real.pi ^ 2) / δ)) :=
      mul_le_mul_of_nonneg_right haSq (by positivity)
    _ = (4 + 16 * Real.pi ^ 2) * δ ^ (1 - 2 * s) := by
      rw [show -2 * s = -(2 * s) by ring, Real.rpow_neg hδ.le,
        Real.rpow_sub hδ 1 (2 * s), Real.rpow_one]
      field_simp


private theorem peak_coeff_norm_sq {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (n : ℤ) :
    ‖coeff1 (poissonPeak r) n‖ ^ 2 =
      (poissonPeakScale r) ^ 2 * (r ^ 2) ^ n.natAbs := by
  rw [coeff_poissonPeak hr0 hr1 n]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- The exact coefficient formula and weighted geometric estimate put every peak in the
frozen fractional Sobolev domain. -/
theorem poissonPeak_mem_hs {r s : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1 / 2) : MemCircleHs s (poissonPeak r) := by
  refine ⟨memLp_poissonPeak hr0 hr1 2, ?_⟩
  have h := (weighted_geometric_peak_bound hr0 hr1 hs0 (by linarith : s ≤ 1)).1
  simpa only [peak_coeff_norm_sq hr0 hr1] using h

/-- SLC-O003: the normalized Poisson peak has the exact fractional Sobolev width exponent.
The displayed constant is independent of both the radius and the Sobolev exponent. -/
theorem poissonPeak_hs_norm_le {r s : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1 / 2) :
    circleHsNorm s (poissonPeak r) ≤ Real.sqrt (4 + 16 * Real.pi ^ 2) *
      (1 - r) ^ ((1 / 2 : ℝ) - s) := by
  have hδ : 0 < 1 - r := sub_pos.mpr hr1
  have h := (weighted_geometric_peak_bound hr0 hr1 hs0 (by linarith : s ≤ 1)).2
  have hbound : (∑' n : ℤ, circleHsWeight s n * ‖coeff1 (poissonPeak r) n‖ ^ 2) ≤
      (4 + 16 * Real.pi ^ 2) * (1 - r) ^ (1 - 2 * s) := by
    simpa only [peak_coeff_norm_sq hr0 hr1] using h
  unfold circleHsNorm
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  calc
    _ ≤ (4 + 16 * Real.pi ^ 2) * (1 - r) ^ (1 - 2 * s) := hbound
    _ = (Real.sqrt (4 + 16 * Real.pi ^ 2) *
        (1 - r) ^ ((1 / 2 : ℝ) - s)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity),
        show 1 - 2 * s = ((1 / 2 : ℝ) - s) * (2 : ℝ) by ring,
        Real.rpow_mul hδ.le]
      norm_num

private theorem eLpNorm_le_tsum_bounds {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (f : ℕ → X → E) (g : X → E) (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : AEStronglyMeasurable g μ) (b : ℕ → ℝ) (hb0 : ∀ n, 0 ≤ b n)
    (hbsum : Summable b) (hbound : ∀ n, eLpNorm (f n) p μ ≤ ENNReal.ofReal (b n))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun N => ∑ n ∈ Finset.range N, f n x) atTop (𝓝 (g x))) :
    eLpNorm g p μ ≤ ENNReal.ofReal (∑' n, b n) := by
  refine Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall fun N => ?_)
    (fun N => Finset.aestronglyMeasurable_fun_sum (Finset.range N) (fun n _ => hf n)) hg hlim
  calc
    eLpNorm (fun x => ∑ n ∈ Finset.range N, f n x) p μ ≤
        ∑ n ∈ Finset.range N, eLpNorm (f n) p μ := by
      have hfun : (fun x => ∑ n ∈ Finset.range N, f n x) = ∑ n ∈ Finset.range N, f n := by
        funext x
        simp only [Finset.sum_apply]
      rw [hfun]
      exact eLpNorm_sum_le hp
    _ ≤ ∑ n ∈ Finset.range N, ENNReal.ofReal (b n) :=
      Finset.sum_le_sum (fun n _ => hbound n)
    _ = ENNReal.ofReal (∑ n ∈ Finset.range N, b n) :=
      (ENNReal.ofReal_sum_of_nonneg (fun n _ => hb0 n)).symm
    _ ≤ ENNReal.ofReal (∑' n, b n) :=
      ENNReal.ofReal_le_ofReal (Summable.sum_le_tsum (Finset.range N) (fun n _ => hb0 n) hbsum)


private noncomputable def weightedCoeff (s : ℝ) (f : Circle → ℝ) (n : ℤ) : ℂ :=
  Real.sqrt (circleHsWeight s n) • coeff1 f n

private theorem weightedCoeff_norm_sq (s : ℝ) (f : Circle → ℝ) (n : ℤ) :
    ‖weightedCoeff s f n‖ ^ 2 = circleHsWeight s n * ‖coeff1 f n‖ ^ 2 := by
  have hw : 0 ≤ circleHsWeight s n := Real.rpow_nonneg (by positivity) _
  rw [weightedCoeff, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hw]

private theorem memLp_weightedCoeff_iff (s : ℝ) (f : Circle → ℝ) :
    MemLp (weightedCoeff s f) 2 (Measure.count : Measure ℤ) ↔
      Summable (fun n : ℤ => circleHsWeight s n * ‖coeff1 f n‖ ^ 2) := by
  have hm : AEStronglyMeasurable (weightedCoeff s f) (Measure.count : Measure ℤ) :=
    (measurable_of_countable _).aestronglyMeasurable
  have hnorm (n : ℤ) : ‖‖weightedCoeff s f n‖ ^ 2‖ =
      circleHsWeight s n * ‖coeff1 f n‖ ^ 2 := by
    rw [Real.norm_of_nonneg (sq_nonneg ‖weightedCoeff s f n‖), weightedCoeff_norm_sq]
  rw [memLp_two_iff_integrable_sq_norm hm, integrable_count_iff]
  simp only [hnorm]

private theorem eLpNorm_weightedCoeff_eq (s : ℝ) (f : Circle → ℝ)
    (hsum : Summable (fun n : ℤ => circleHsWeight s n * ‖coeff1 f n‖ ^ 2)) :
    eLpNorm (weightedCoeff s f) 2 (Measure.count : Measure ℤ) =
      ENNReal.ofReal (circleHsNorm s f) := by
  have hm := (memLp_weightedCoeff_iff s f).mpr hsum
  have hI : (∫ n, ‖weightedCoeff s f n‖ ^ 2 ∂(Measure.count : Measure ℤ)) =
      ∑' n : ℤ, circleHsWeight s n * ‖coeff1 f n‖ ^ 2 := by
    rw [integral_countable hm.norm.integrable_sq]
    simp [weightedCoeff_norm_sq]
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hm]
  norm_num
  rw [hI, circleHsNorm, Real.sqrt_eq_rpow]


private theorem eLpNorm_barrierBlock_le_peak (n : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (barrierBlock n) p (haar 1) ≤
      ENNReal.ofReal (4 * height n) * eLpNorm (poissonPeak (radius n)) p (haar 1) := by
  let q := poissonPeak (radius n)
  let d := torusPoint (separation n)
  have hr0 : 0 < radius n := by linarith [radius_ge_half n]
  have hq : AEStronglyMeasurable q (haar 1) :=
    (memLp_poissonPeak hr0 (radius_lt_one n) p).aestronglyMeasurable
  have hleft : eLpNorm (fun x => q (x - d)) p (haar 1) = eLpNorm q p (haar 1) := by
    simpa only [Function.comp_def] using
      (eLpNorm_comp_measurePreserving (p := p) hq (measurePreserving_sub_right (haar 1) d))
  have hright : eLpNorm (fun x => q (x + d)) p (haar 1) = eLpNorm q p (haar 1) := by
    simpa only [Function.comp_def] using
      (eLpNorm_comp_measurePreserving (p := p) hq (measurePreserving_add_right (haar 1) d))
  have hsum : eLpNorm (fun x => 2 * q x + q (x - d) + q (x + d)) p (haar 1) ≤
      4 * eLpNorm q p (haar 1) := by
    change eLpNorm (((2 : ℝ) • q + fun x => q (x - d)) + fun x => q (x + d)) p (haar 1) ≤ _
    calc
      _ ≤ eLpNorm ((2 : ℝ) • q + fun x => q (x - d)) p (haar 1) +
          eLpNorm (fun x => q (x + d)) p (haar 1) :=
        eLpNorm_add_le (f := (2 : ℝ) • q + fun x => q (x - d))
          (g := fun x => q (x + d)) hp
      _ ≤ (eLpNorm ((2 : ℝ) • q) p (haar 1) +
          eLpNorm (fun x => q (x - d)) p (haar 1)) +
          eLpNorm (fun x => q (x + d)) p (haar 1) := by
        have hi := eLpNorm_add_le (f := (2 : ℝ) • q)
          (g := fun x => q (x - d)) (μ := haar 1) hp
        exact add_le_add hi le_rfl
      _ = 4 * eLpNorm q p (haar 1) := by
        rw [eLpNorm_const_smul, hleft, hright]
        rw [Real.enorm_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
        norm_num
        ring
  change eLpNorm (height n • (fun x => 2 * q x + q (x - d) + q (x + d))) p (haar 1) ≤ _
  rw [eLpNorm_const_smul, Real.enorm_of_nonneg (height_pos n).le]
  calc
    _ ≤ ENNReal.ofReal (height n) * (4 * eLpNorm q p (haar 1)) := by gcongr
    _ = ENNReal.ofReal (4 * height n) * eLpNorm q p (haar 1) := by
      rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (4 : ℝ))]
      norm_num [mul_assoc, mul_comm, mul_left_comm]


/-- SLC-O001: every real power at least one has peak mass at most the width. -/
theorem integral_poissonPeak_rpow_le {r p : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hp : 1 ≤ p) : (∫ x, (poissonPeak r x) ^ p ∂haar 1) ≤ 1 - r := by
  calc
    (∫ x, (poissonPeak r x) ^ p ∂haar 1) ≤ ∫ x, poissonPeak r x ∂haar 1 :=
      integral_mono (integrable_poissonPeak_rpow hr0 hr1 p)
        ((memLp_poissonPeak hr0 hr1 1).integrable le_rfl)
        (poissonPeak_rpow_le hr0 hr1 hp)
    _ = poissonPeakScale r := integral_poissonPeak hr0 hr1
    _ ≤ 1 - r := (peakScale_bounds hr0 hr1).2

theorem eLpNorm_poissonPeak_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ⊤) :
    eLpNorm (poissonPeak r) p (haar 1) ≤ ENNReal.ofReal ((1 - r) ^ p.toReal⁻¹) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpR : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hpfin hp
  rw [MemLp.eLpNorm_eq_integral_rpow_norm hp0 hpfin (memLp_poissonPeak hr0 hr1 p)]
  apply ENNReal.ofReal_le_ofReal
  have hnorm (x : Circle) : ‖poissonPeak r x‖ = poissonPeak r x :=
    Real.norm_of_nonneg (poissonPeak_pos hr0 hr1 x).le
  simp_rw [hnorm]
  exact Real.rpow_le_rpow
    (integral_nonneg fun x => Real.rpow_nonneg (poissonPeak_pos hr0 hr1 x).le _)
    (integral_poissonPeak_rpow_le hr0 hr1 hpR) (inv_nonneg.mpr ENNReal.toReal_nonneg)


/-- SLC-O002: the singular barrier belongs to every fixed finite probability-Haar Lp space. -/
theorem barrier_memLp {p : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ⊤) :
    MemLp barrier p (haar 1) := by
  classical
  have hpR : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hpfin hp
  have hα : 0 < p.toReal⁻¹ := inv_pos.mpr (lt_of_lt_of_le zero_lt_one hpR)
  let b : ℕ → ℝ := fun n => 4 * height n * (width n) ^ p.toReal⁻¹
  have hb0 (n : ℕ) : 0 ≤ b n :=
    mul_nonneg (mul_nonneg (by norm_num) (height_pos n).le)
      (Real.rpow_nonneg (width_pos n).le _)
  have hbsum : Summable b := by
    simpa only [b, mul_assoc] using (height_width_rpow_summable hα).mul_left (4 : ℝ)
  have hbound (n : ℕ) : eLpNorm (barrierBlock n) p (haar 1) ≤ ENNReal.ofReal (b n) := by
    have hr0 : 0 < radius n := by linarith [radius_ge_half n]
    have hq := eLpNorm_poissonPeak_le hr0 (radius_lt_one n) hp hpfin
    rw [show 1 - radius n = width n by simp [radius]] at hq
    calc
      _ ≤ ENNReal.ofReal (4 * height n) *
          eLpNorm (poissonPeak (radius n)) p (haar 1) := eLpNorm_barrierBlock_le_peak n hp
      _ ≤ ENNReal.ofReal (4 * height n) *
          ENNReal.ofReal ((width n) ^ p.toReal⁻¹) := by gcongr
      _ = ENNReal.ofReal (b n) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (height_pos n).le)]
  have hlim : ∀ᵐ x ∂haar 1,
      Tendsto (fun N => ∑ n ∈ Finset.range N, barrierBlock n x) atTop (𝓝 (barrier x)) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (haar_singleton_zero (0 : Circle))] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    rw [barrier, ite_eq_right hx0]
    exact (barrierBlock_summable hx0).tendsto_sum_tsum_nat
  have hnorm := eLpNorm_le_tsum_bounds hp (fun n => barrierBlock n) barrier
    (fun n => (barrierBlock_continuous n).aestronglyMeasurable)
    barrier_measurable.aestronglyMeasurable b hb0 hbsum hbound hlim
  exact lt_of_le_of_lt hnorm ENNReal.ofReal_lt_top


private theorem coeff1_const_mul (c : ℝ) (f : Circle → ℝ) (k : ℤ) :
    coeff1 (fun x => c * f x) k = (c : ℂ) * coeff1 f k :=
  SharpLSI.cf_const_mul' f c (freqZ k)

private theorem norm_coeff_barrierBlock_le (n : ℕ) (k : ℤ) :
    ‖coeff1 (barrierBlock n) k‖ ≤ 4 * height n * ‖coeff1 (poissonPeak (radius n)) k‖ := by
  have hr0 : 0 < radius n := by linarith [radius_ge_half n]
  have hscale := (peakScale_bounds hr0 (radius_lt_one n)).1
  let A := 4 * height n * poissonPeakScale (radius n) * radius n ^ k.natAbs
  let θ := Real.pi * (k : ℝ) * separation n
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (height_pos n).le) hscale) (pow_nonneg hr0.le _)
  have hv : 0 ≤ poissonPeakScale (radius n) * radius n ^ k.natAbs :=
    mul_nonneg hscale (pow_nonneg hr0.le _)
  have hcos : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  rw [coeff_barrierBlock n k, coeff_poissonPeak hr0 (radius_lt_one n) k]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  change |A * Real.cos θ ^ 2| ≤ 4 * height n *
    |poissonPeakScale (radius n) * radius n ^ k.natAbs|
  rw [abs_of_nonneg (mul_nonneg hA (sq_nonneg _)), abs_of_nonneg hv]
  calc
    A * Real.cos θ ^ 2 ≤ A * 1 := mul_le_mul_of_nonneg_left hcos hA
    _ = 4 * height n * (poissonPeakScale (radius n) * radius n ^ k.natAbs) := by
      dsimp [A]
      ring

private theorem weightedCoeff_norm (s : ℝ) (f : Circle → ℝ) (k : ℤ) :
    ‖weightedCoeff s f k‖ = Real.sqrt (circleHsWeight s k) * ‖coeff1 f k‖ := by
  rw [weightedCoeff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]


private theorem eLpNorm_weightedCoeff_barrierBlock_le (n : ℕ) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1 / 2) :
    eLpNorm (weightedCoeff s (barrierBlock n)) 2 (Measure.count : Measure ℤ) ≤
      ENNReal.ofReal ((4 * Real.sqrt (4 + 16 * Real.pi ^ 2)) * height n *
        (width n) ^ ((1 / 2 : ℝ) - s)) := by
  let q := poissonPeak (radius n)
  have hr0 : 0 < radius n := by linarith [radius_ge_half n]
  have h4 : 0 ≤ (4 : ℝ) * height n := mul_nonneg (by norm_num) (height_pos n).le
  have hpoint (k : ℤ) : ‖weightedCoeff s (barrierBlock n) k‖ ≤
      ‖(4 * height n : ℝ) • weightedCoeff s q k‖ := by
    have hscalar (z : ℂ) : ‖(4 * height n : ℝ) • z‖ = (4 * height n) * ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h4]
    rw [weightedCoeff_norm s (barrierBlock n) k, hscalar, weightedCoeff_norm s q k]
    calc
      _ ≤ Real.sqrt (circleHsWeight s k) * (4 * height n * ‖coeff1 q k‖) :=
        mul_le_mul_of_nonneg_left (norm_coeff_barrierBlock_le n k) (Real.sqrt_nonneg _)
      _ = (4 * height n) * (Real.sqrt (circleHsWeight s k) * ‖coeff1 q k‖) := by ring
  have hmajor : eLpNorm (weightedCoeff s (barrierBlock n)) 2 (Measure.count : Measure ℤ) ≤
      eLpNorm ((4 * height n : ℝ) • weightedCoeff s q) 2 (Measure.count : Measure ℤ) :=
    eLpNorm_mono_ae (measurable_of_countable _).aestronglyMeasurable
      (Filter.Eventually.of_forall hpoint)
  rw [eLpNorm_const_smul (4 * height n : ℝ) (weightedCoeff s q) 2 (Measure.count : Measure ℤ),
    Real.enorm_of_nonneg h4,
    eLpNorm_weightedCoeff_eq s q (poissonPeak_mem_hs hr0 (radius_lt_one n) hs0 hs1).2] at hmajor
  have hpeak := poissonPeak_hs_norm_le hr0 (radius_lt_one n) hs0 hs1
  rw [show 1 - radius n = width n by simp [radius]] at hpeak
  calc
    _ ≤ ENNReal.ofReal (4 * height n) * ENNReal.ofReal (circleHsNorm s q) := hmajor
    _ ≤ ENNReal.ofReal (4 * height n) *
        ENNReal.ofReal (Real.sqrt (4 + 16 * Real.pi ^ 2) * (width n) ^ ((1 / 2 : ℝ) - s)) := by
      gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul h4]
      congr 1
      ring


private theorem hsTerm_const_mul (c s : ℝ) (f : Circle → ℝ) (k : ℤ) :
    circleHsWeight s k * ‖coeff1 (fun x => c * f x) k‖ ^ 2 =
      c ^ 2 * (circleHsWeight s k * ‖coeff1 f k‖ ^ 2) := by
  rw [coeff1_const_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

private theorem memCircleHs_const_mul {s : ℝ} {f : Circle → ℝ}
    (hf : MemCircleHs s f) (c : ℝ) : MemCircleHs s (fun x => c * f x) := by
  refine ⟨hf.1.const_mul c, ?_⟩
  simpa only [hsTerm_const_mul c s f] using hf.2.mul_left (c ^ 2)

private theorem circleHsNorm_const_mul {s : ℝ} {f : Circle → ℝ}
    (hf : MemCircleHs s f) (c : ℝ) :
    circleHsNorm s (fun x => c * f x) = |c| * circleHsNorm s f := by
  unfold circleHsNorm
  simp_rw [hsTerm_const_mul c s f]
  rw [(hf.2.hasSum.mul_left (c ^ 2)).tsum_eq,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

private theorem memCircleHs_mono {s t : ℝ} {f : Circle → ℝ}
    (hst : s ≤ t) (hf : MemCircleHs t f) : MemCircleHs s f := by
  refine ⟨hf.1, Summable.of_nonneg_of_le ?_ ?_ hf.2⟩
  · intro k
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)
  · intro k
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le
        (show 1 ≤ 1 + (2 * Real.pi * (k : ℝ)) ^ 2 by nlinarith [sq_nonneg (2 * Real.pi * (k : ℝ))])
        hst) (sq_nonneg _)

/-- Scalar multiplication tends to zero in every fixed finite Lp norm of the barrier. -/
theorem barrier_smul_tendsto_Lp {p : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ⊤) :
    Tendsto (fun η : ℝ => eLpNorm (fun x => η * barrier x) p (haar 1))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let C := (eLpNorm barrier p (haar 1)).toReal
  have hfinite := (barrier_memLp hp hpfin).eLpNorm_ne_top
  have ht : Tendsto (fun η : ℝ => η * C) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using ((tendsto_id : Tendsto (fun η : ℝ => η) (𝓝 0) (𝓝 0)).mono_left
      nhdsWithin_le_nhds).mul_const C
  have hm : Tendsto (fun η : ℝ => ENNReal.ofReal (η * C)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp ht
  refine hm.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hη0 : 0 ≤ η := (show 0 < η from hη).le
  symm
  calc
    eLpNorm (fun x => η * barrier x) p (haar 1) =
        ‖η‖ₑ * eLpNorm barrier p (haar 1) := eLpNorm_const_smul η barrier p (haar 1)
    _ = ENNReal.ofReal η * ENNReal.ofReal C := by
      rw [Real.enorm_of_nonneg hη0, ENNReal.ofReal_toReal hfinite]
    _ = ENNReal.ofReal (η * C) := (ENNReal.ofReal_mul hη0).symm


private theorem hsNorm_smul_tendsto {s : ℝ} {f : Circle → ℝ} (hf : MemCircleHs s f) :
    Tendsto (fun η : ℝ => circleHsNorm s (fun x => η * f x)) (𝓝 0) (𝓝 0) := by
  have ht : Tendsto (fun η : ℝ => |η| * circleHsNorm s f) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using (continuous_abs.mul_const (circleHsNorm s f)).tendsto (0 : ℝ)
  exact ht.congr' (Filter.Eventually.of_forall fun η => (circleHsNorm_const_mul hf η).symm)


/-- The nonnegative part of the subcritical Sobolev estimate. -/
private theorem barrier_mem_hs_nonneg {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1 / 2) :
    MemCircleHs s barrier := by
  let C := 4 * Real.sqrt (4 + 16 * Real.pi ^ 2)
  let b : ℕ → ℝ := fun n => C * height n * (width n) ^ ((1 / 2 : ℝ) - s)
  have hα : 0 < (1 / 2 : ℝ) - s := sub_pos.mpr hs1
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hb0 (n : ℕ) : 0 ≤ b n :=
    mul_nonneg (mul_nonneg hC (height_pos n).le) (Real.rpow_nonneg (width_pos n).le _)
  have hbsum : Summable b := by
    simpa only [b, mul_assoc] using (height_width_rpow_summable hα).mul_left C
  have hbound (n : ℕ) :
      eLpNorm (weightedCoeff s (barrierBlock n)) 2 (Measure.count : Measure ℤ) ≤
        ENNReal.ofReal (b n) := by
    simpa only [b, C] using eLpNorm_weightedCoeff_barrierBlock_le n hs0 hs1
  have hlim : ∀ᵐ k ∂(Measure.count : Measure ℤ),
      Tendsto (fun N => ∑ n ∈ Finset.range N, weightedCoeff s (barrierBlock n) k) atTop
        (𝓝 (weightedCoeff s barrier k)) := by
    refine Filter.Eventually.of_forall fun k => ?_
    have hs : HasSum (fun n : ℕ => weightedCoeff s (barrierBlock n) k)
        (weightedCoeff s barrier k) :=
      HasSum.const_smul (Real.sqrt (circleHsWeight s k)) (hasSum_coeff_barrier k)
    exact hs.tendsto_sum_nat
  have hnorm := eLpNorm_le_tsum_bounds (p := 2) (μ := (Measure.count : Measure ℤ))
    (by norm_num) (fun n => weightedCoeff s (barrierBlock n)) (weightedCoeff s barrier)
    (fun n => (measurable_of_countable _).aestronglyMeasurable)
    (measurable_of_countable _).aestronglyMeasurable b hb0 hbsum hbound hlim
  refine ⟨barrier_memLp (p := 2) (by norm_num) (by norm_num), ?_⟩
  exact (memLp_weightedCoeff_iff s barrier).mp (lt_of_le_of_lt hnorm ENNReal.ofReal_lt_top)

/-- SLC-O004: every real subcritical Sobolev order is admissible. Negative orders follow
from the zero-order estimate. -/
theorem barrier_mem_hs {s : ℝ} (hs : s < 1 / 2) : MemCircleHs s barrier := by
  by_cases hs0 : 0 ≤ s
  · exact barrier_mem_hs_nonneg hs0 hs
  · exact memCircleHs_mono (t := 0) (le_of_lt (lt_of_not_ge hs0))
      (barrier_mem_hs_nonneg (s := 0) (by norm_num) (by norm_num))

theorem barrier_smul_mem_hs {s : ℝ} (hs : s < 1 / 2) (η : ℝ) :
    MemCircleHs s (fun x => η * barrier x) :=
  memCircleHs_const_mul (barrier_mem_hs hs) η

/-- Scalar multiplication tends to zero in every fixed subcritical Sobolev norm. -/
theorem barrier_smul_tendsto_Hs {s : ℝ} (hs : s < 1 / 2) :
    Tendsto (fun η : ℝ => circleHsNorm s (fun x => η * barrier x))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  (hsNorm_smul_tendsto (barrier_mem_hs hs)).mono_left nhdsWithin_le_nhds

end DGPS.SingularCounterexample
