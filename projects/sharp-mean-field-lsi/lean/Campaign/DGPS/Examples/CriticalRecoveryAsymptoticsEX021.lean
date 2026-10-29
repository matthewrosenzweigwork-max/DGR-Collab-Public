import DGPS.Examples.SixthOrderCentering
import DGPS.Lipschitz.WeightedGenerator
import DGPS.Examples.AttractiveXY
import DGPS.Examples.AttractiveXYCritical

/-!
# Scalar formulas for critical von Mises recovery (EX021)

The functions below are the exact expressions in the source route. The Bessel-tail and quotient
bounds reuse the already proved same-series estimates from EX053; this introduces no hypothesis
on the trial family.
-/

open MeasureTheory Real Filter Topology
open scoped ENNReal NNReal ContDiff
open DGPS.Examples.AttractiveXY
open DGPS.Circle.BesselMoments
open DGPS.Examples.SixthOrderCentering

namespace DGPS.Examples.CriticalRecoveryAsymptoticsEX021

/-- The critical free-energy gap of the positive von Mises law, in its exact Bessel form. -/
noncomputable def vonMisesGapEX021 (t : ℝ) : ℝ :=
  t * besselRatio t - Real.log (besselI 0 t) - besselRatio t ^ 2

/-- The scalar expression predicted by the score difference and the sine-square moment. -/
noncomputable def vonMisesDissipationEX021 (t : ℝ) : ℝ :=
  4 * Real.pi ^ 2 * (t - 2 * besselRatio t) ^ 2 * (besselRatio t / t)

/-- The quotient formed from the actual entropy gap and the displayed scalar dissipation expression. -/
noncomputable def vonMisesQuotientEX021 (t : ℝ) : ℝ :=
  vonMisesDissipationEX021 t / (2 * vonMisesGapEX021 t)

/-- The actual positive von Mises density transported to the model torus. -/
noncomputable def vonMisesTorusDensityEX021 (t : ℝ) (x : DGPS.Torus 1) : ℝ :=
  besselDensity t (DGPS.Circle.AngularNormalization.angEquiv x)

theorem vonMisesTorusDensity_pos_EX021 (t : ℝ) (x : DGPS.Torus 1) :
    0 < vonMisesTorusDensityEX021 t x := by
  unfold vonMisesTorusDensityEX021 DGPS.Circle.BesselMoments.besselDensity
  exact div_pos (Real.exp_pos _) (besselI_zero_pos t)

theorem vonMisesTorusDensity_mass_EX021 (t : ℝ) :
    ∫ x, vonMisesTorusDensityEX021 t x ∂DGPS.haar 1 = 1 := by
  change ∫ x, besselDensity t (DGPS.Circle.AngularNormalization.angEquiv x) ∂DGPS.haar 1 = 1
  rw [DGPS.Circle.AngularNormalization.integral_comp_angEquiv (besselDensity t)]
  have hI : ∫ θ, Real.exp (t * angCos θ) ∂DGPS.Circle.AngularNormalization.angHaar =
      besselI 0 t := by
    calc
      ∫ θ, Real.exp (t * angCos θ) ∂DGPS.Circle.AngularNormalization.angHaar =
          ∫ θ, Real.exp (t * angCos θ) * angCos θ ^ 0 ∂DGPS.Circle.AngularNormalization.angHaar := by simp
      _ = besselI 0 t := (besselI_zero t).symm
  unfold besselDensity
  rw [integral_div, hI]
  exact div_self (besselI_zero_pos t).ne'

theorem vonMisesTorusDensity_cosMoment_EX021 (t : ℝ) :
    ∫ x, (xyMode x).re * vonMisesTorusDensityEX021 t x ∂DGPS.haar 1 = besselRatio t := by
  calc
    ∫ x, (xyMode x).re * vonMisesTorusDensityEX021 t x ∂DGPS.haar 1 =
        ∫ x, angCos (DGPS.Circle.AngularNormalization.angEquiv x) *
          besselDensity t (DGPS.Circle.AngularNormalization.angEquiv x) ∂DGPS.haar 1 := by
      apply integral_congr_ae
      filter_upwards with x
      rw [DGPS.Examples.AttractiveXYCritical.xyMode_re_eq_angCos_xyc]
      simp [vonMisesTorusDensityEX021]
    _ = besselRatio t := by
      rw [DGPS.Circle.AngularNormalization.integral_comp_angEquiv
        (fun θ => angCos θ * besselDensity t θ)]
      exact (besselRatio_eq_mean t).symm

/-- The EX002 quotient has the required cubic jet, with an explicit uniform tail bound. -/
theorem besselRatio_jet_EX021 (t : ℝ) (ht : |t| ≤ 1) :
    |besselRatio t - (t / 2 - t ^ 3 / 16)| ≤ |t| ^ 5 := by
  let a : ℝ := t ^ 2 / 4
  have ha0 : 0 ≤ a := by positivity
  have ha : a ≤ 1 / 4 := by
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [sq_abs t, abs_nonneg t]
    dsimp [a]; linarith
  obtain ⟨e0, e0'⟩ := DGPS.Examples.SixthOrderCentering.besselI_zero_expand t ht
  obtain ⟨e1, e1'⟩ := DGPS.Examples.SixthOrderCentering.besselI1Over_expand t ht
  obtain ⟨-, hq⟩ := DGPS.Examples.SixthOrderCentering.quotient_core a (besselI 0 t)
    (besselI1Over t) ha0 ha e0 e0' e1 e1'
  have hpoly :
      |DGPS.Examples.SixthOrderCentering.quotientPoly a - (1 / 2 - a / 4)| ≤ a ^ 2 / 4 := by
    rw [show DGPS.Examples.SixthOrderCentering.quotientPoly a - (1 / 2 - a / 4) =
      a ^ 2 / 6 - 11 * a ^ 3 / 96 by
        unfold DGPS.Examples.SixthOrderCentering.quotientPoly; ring]
    calc
      |a ^ 2 / 6 - 11 * a ^ 3 / 96| ≤ |a ^ 2 / 6| + |11 * a ^ 3 / 96| := abs_sub _ _
      _ = a ^ 2 / 6 + 11 * a ^ 3 / 96 := by
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      _ ≤ a ^ 2 / 4 := by
        nlinarith [mul_nonneg (sq_nonneg a) (by linarith : 0 ≤ 1 / 4 - a)]
  have hq' :
      |besselI1Over t / besselI 0 t - (1 / 2 - a / 4)| ≤ 4 * a ^ 4 + a ^ 2 / 4 := by
    calc
      |besselI1Over t / besselI 0 t - (1 / 2 - a / 4)| =
          |(besselI1Over t / besselI 0 t - DGPS.Examples.SixthOrderCentering.quotientPoly a) +
            (DGPS.Examples.SixthOrderCentering.quotientPoly a - (1 / 2 - a / 4))| := by
              congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add hq hpoly
  have hid : besselRatio t = t * (besselI1Over t / besselI 0 t) := by
    unfold besselRatio
    rw [DGPS.Examples.SixthOrderCentering.besselI_one_eq_mul]
    ring
  rw [hid]
  have hmain :
      |t * (besselI1Over t / besselI 0 t) - t * (1 / 2 - a / 4)| =
        |t| * |besselI1Over t / besselI 0 t - (1 / 2 - a / 4)| := by
    rw [← mul_sub, abs_mul]
  have ht5 : |t| * (4 * a ^ 4 + a ^ 2 / 4) ≤ |t| ^ 5 := by
    have hr0 : 0 ≤ |t| := abs_nonneg t
    have hr1 : |t| ≤ 1 := ht
    have hr4 : |t| ^ 4 <= 1 := by
      calc |t| ^ 4 <= 1 ^ 4 := by gcongr
        _ = 1 := by norm_num
    have hr9 : |t| ^ 9 ≤ |t| ^ 5 := by
      calc
        |t| ^ 9 = |t| ^ 5 * |t| ^ 4 := by ring
        _ ≤ |t| ^ 5 * 1 := mul_le_mul_of_nonneg_left hr4 (by positivity)
        _ = |t| ^ 5 := by ring
    dsimp [a]
    rw [← sq_abs t]
    nlinarith [hr9]
  calc
    |t * (besselI1Over t / besselI 0 t) - (t / 2 - t ^ 3 / 16)| =
        |t * (besselI1Over t / besselI 0 t) - t * (1 / 2 - a / 4)| := by
          congr 1; dsimp [a]; ring
    _ = |t| * |besselI1Over t / besselI 0 t - (1 / 2 - a / 4)| := hmain
    _ ≤ |t| * (4 * a ^ 4 + a ^ 2 / 4) := mul_le_mul_of_nonneg_left hq' (abs_nonneg _)
    _ ≤ |t| ^ 5 := ht5


/-- The logarithm of I₀ has its quartic jet with a uniform sixth-order remainder. -/
theorem besselI0_log_jet_EX021 (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    |Real.log (besselI 0 t) - (t ^ 2 / 4 - t ^ 4 / 64)| ≤ t ^ 6 := by
  let a : ℝ := t ^ 2 / 4
  let u : ℝ := besselI 0 t - 1
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 / 16 := by dsimp [a]; nlinarith
  have ht : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; linarith
  obtain ⟨e0, e0'⟩ := DGPS.Examples.SixthOrderCentering.besselI_zero_expand t ht
  have e0a : 0 ≤ besselI 0 t - (1 + a + a ^ 2 / 4 + a ^ 3 / 36) := e0
  have e0b : besselI 0 t - (1 + a + a ^ 2 / 4 + a ^ 3 / 36) ≤ 2 * a ^ 4 := e0'
  have hexp : 0 ≤ u - (a + a ^ 2 / 4) ∧ u - (a + a ^ 2 / 4) ≤ a ^ 3 := by
    have he : u - (a + a ^ 2 / 4) =
        a ^ 3 / 36 + (besselI 0 t - (1 + a + a ^ 2 / 4 + a ^ 3 / 36)) := by
      dsimp [u]; ring
    rw [he]
    constructor
    · exact add_nonneg (by positivity) e0a
    · calc
        a ^ 3 / 36 +
            (besselI 0 t - (1 + a + a ^ 2 / 4 + a ^ 3 / 36)) ≤
            a ^ 3 / 36 + 2 * a ^ 4 := by linarith [e0b]
        _ ≤ a ^ 3 := by
          have h4 : 2 * a ^ 4 ≤ a ^ 3 / 2 := by
            nlinarith [mul_nonneg (pow_nonneg ha0 3)
              (by linarith : 0 ≤ 1 / 4 - a)]
          nlinarith [pow_nonneg ha0 3]
  have hu0 : 0 ≤ u := by
    have : 0 ≤ a + a ^ 2 / 4 := by positivity
    linarith [hexp.1]
  have hu1 : u ≤ 2 * a := by
    have hrem := hexp.2
    nlinarith [sq_nonneg a]
  have hu2 : u ≤ 1 / 2 := by nlinarith
  have hlt : |-u| < 1 := by rw [abs_neg, abs_of_nonneg hu0]; linarith
  have hlog0 := Real.abs_log_sub_add_sum_range_le hlt 2
  have heq : |Real.log (1 + u) - (u - u ^ 2 / 2)| =
      |(∑ i ∈ Finset.range 2, (-u) ^ (i + 1) / ((i : ℝ) + 1)) +
        Real.log (1 - -u)| := by
    congr 1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    ring_nf
  have hlog : |Real.log (1 + u) - (u - u ^ 2 / 2)| ≤ u ^ 3 / (1 - u) := by
    rw [heq]
    simpa [abs_neg, abs_of_nonneg hu0] using hlog0
  have hlog' : |Real.log (1 + u) - (u - u ^ 2 / 2)| ≤ 2 * u ^ 3 := by
    calc
      _ ≤ u ^ 3 / (1 - u) := hlog
      _ ≤ 2 * u ^ 3 := by
        rw [div_le_iff₀ (by linarith : 0 < 1 - u)]
        nlinarith [pow_nonneg hu0 3]
  have hdiff1 : |u - a| ≤ a ^ 2 / 2 := by
    have he : u - a = a ^ 2 / 4 + (u - (a + a ^ 2 / 4)) := by ring
    rw [abs_le]
    constructor <;> rw [he] <;> nlinarith [hexp.1, hexp.2]
  have hdiff2 : |u + a| ≤ 3 * a := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have hdiff3 : |u ^ 2 - a ^ 2| ≤ (a ^ 2 / 2) * (3 * a) := by
    rw [show u ^ 2 - a ^ 2 = (u - a) * (u + a) by ring, abs_mul]
    exact mul_le_mul hdiff1 hdiff2 (abs_nonneg _) (by positivity)
  have hbase : |(u - u ^ 2 / 2) - (a - a ^ 2 / 4)| ≤ 2 * a ^ 3 := by
    have he : (u - u ^ 2 / 2) - (a - a ^ 2 / 4) =
        (u - (a + a ^ 2 / 4)) - (u ^ 2 - a ^ 2) / 2 := by ring
    rw [he]
    have hrem : |u - (a + a ^ 2 / 4)| ≤ a ^ 3 := by
      rw [abs_le]
      exact ⟨by linarith [hexp.1], hexp.2⟩
    calc
      _ ≤ |u - (a + a ^ 2 / 4)| + |(u ^ 2 - a ^ 2) / 2| := abs_sub _ _
      _ ≤ a ^ 3 + ((a ^ 2 / 2) * (3 * a)) / 2 := by
        exact add_le_add hrem (calc
          |(u ^ 2 - a ^ 2) / 2| = |u ^ 2 - a ^ 2| / 2 := by
            rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          _ ≤ ((a ^ 2 / 2) * (3 * a)) / 2 :=
            div_le_div_of_nonneg_right hdiff3 (by norm_num))
      _ ≤ 2 * a ^ 3 := by nlinarith [pow_nonneg ha0 3, hexp.2]
  have htotal : |Real.log (1 + u) - (a - a ^ 2 / 4)| ≤ 18 * a ^ 3 := by
    calc
      _ = |(Real.log (1 + u) - (u - u ^ 2 / 2)) +
          ((u - u ^ 2 / 2) - (a - a ^ 2 / 4))| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ 2 * u ^ 3 + 2 * a ^ 3 := add_le_add hlog' hbase
      _ ≤ 18 * a ^ 3 := by
        have hu3 : u ^ 3 ≤ 8 * a ^ 3 := by
          calc
            u ^ 3 ≤ (2 * a) ^ 3 := by gcongr
            _ = 8 * a ^ 3 := by ring
        nlinarith [hu3]
  have he : a - a ^ 2 / 4 = t ^ 2 / 4 - t ^ 4 / 64 := by dsimp [a]; ring
  rw [← he]
  have huEq : 1 + u = besselI 0 t := by dsimp [u]; ring
  rw [← huEq]
  have ha3 : 18 * a ^ 3 ≤ t ^ 6 := by dsimp [a]; nlinarith
  exact htotal.trans ha3


/-- The critical gap has the stated quartic jet and a strict positive lower bound for small t. -/
theorem vonMisesGap_jet_EX021 (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) :
    |vonMisesGapEX021 t - t ^ 4 / 64| ≤ 5 * t ^ 6 := by
  let p : ℝ := t / 2 - t ^ 3 / 16
  let g : ℝ := besselRatio t
  have hjet := besselRatio_jet_EX021 t (by rw [abs_of_pos ht0]; linarith)
  have hgjet : |g - p| ≤ t ^ 5 := by simpa [g, p, abs_of_pos ht0] using hjet
  have hp : |p| ≤ t / 2 := by
    have ht2 : t ^ 2 ≤ 1 / 4 := by nlinarith [ht1]
    have hp0 : 0 ≤ p := by dsimp [p]; nlinarith [ht2, ht0]
    rw [abs_of_nonneg hp0]
    dsimp [p]
    nlinarith [sq_nonneg t, ht1]
  have hg : |g| ≤ t := by
    calc
      |g| ≤ |g - p| + |p| := by
        have := abs_sub_le g p 0
        simpa using this
      _ ≤ t ^ 5 + t / 2 := add_le_add hgjet hp
      _ ≤ t := by
        have ht4 : t ^ 4 ≤ 1 / 16 := by
          have ht2 : t ^ 2 ≤ 1 / 4 := by nlinarith [ht1]
          nlinarith [ht2]
        have ht5 : t ^ 5 ≤ t / 16 := by
          calc t ^ 5 = t * t ^ 4 := by ring
            _ ≤ t * (1 / 16) := mul_le_mul_of_nonneg_left ht4 ht0.le
            _ = t / 16 := by ring
        nlinarith [ht5]
  have htg : |t * g - (t ^ 2 / 2 - t ^ 4 / 16)| ≤ t ^ 6 := by
    have he : t * g - (t ^ 2 / 2 - t ^ 4 / 16) = t * (g - p) := by
      dsimp [p]; ring
    rw [he, abs_mul, abs_of_pos ht0]
    calc
      t * |g - p| ≤ t * t ^ 5 := mul_le_mul_of_nonneg_left hgjet ht0.le
      _ = t ^ 6 := by ring
  have hgsq : |g ^ 2 - (t ^ 2 / 4 - t ^ 4 / 16)| ≤ 2 * t ^ 6 := by
    have he : g ^ 2 - (t ^ 2 / 4 - t ^ 4 / 16) =
        (g ^ 2 - p ^ 2) + t ^ 6 / 256 := by dsimp [p]; ring
    rw [he]
    have ht6 : 0 ≤ t ^ 6 / 256 := by positivity
    calc
      _ ≤ |g ^ 2 - p ^ 2| + |t ^ 6 / 256| := abs_add_le _ _
      _ = |g - p| * |g + p| + t ^ 6 / 256 := by
        rw [show g ^ 2 - p ^ 2 = (g - p) * (g + p) by ring, abs_mul,
          abs_of_nonneg ht6]
      _ ≤ t ^ 5 * (t + t / 2) + t ^ 6 / 256 := by
        gcongr
        · calc |g + p| ≤ |g| + |p| := abs_add_le _ _
          _ ≤ t + t / 2 := add_le_add hg hp
      _ ≤ 2 * t ^ 6 := by ring_nf; nlinarith [sq_nonneg t, ht1]
  have hlog := besselI0_log_jet_EX021 t (by positivity) ht1
  have he : vonMisesGapEX021 t - t ^ 4 / 64 =
      (t * g - (t ^ 2 / 2 - t ^ 4 / 16)) -
      (Real.log (besselI 0 t) - (t ^ 2 / 4 - t ^ 4 / 64)) -
      (g ^ 2 - (t ^ 2 / 4 - t ^ 4 / 16)) := by
    dsimp [vonMisesGapEX021, g]; ring
  rw [he]
  have htri :
      |(t * g - (t ^ 2 / 2 - t ^ 4 / 16)) -
          (Real.log (besselI 0 t) - (t ^ 2 / 4 - t ^ 4 / 64)) -
          (g ^ 2 - (t ^ 2 / 4 - t ^ 4 / 16))| ≤
        |t * g - (t ^ 2 / 2 - t ^ 4 / 16)| +
          |Real.log (besselI 0 t) - (t ^ 2 / 4 - t ^ 4 / 64)| +
          |g ^ 2 - (t ^ 2 / 4 - t ^ 4 / 16)| := by
    calc
      _ = |(t * g - (t ^ 2 / 2 - t ^ 4 / 16)) -
          ((Real.log (besselI 0 t) - (t ^ 2 / 4 - t ^ 4 / 64)) +
            (g ^ 2 - (t ^ 2 / 4 - t ^ 4 / 16)))| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
      _ ≤ |t * g - (t ^ 2 / 2 - t ^ 4 / 16)| +
          (|Real.log (besselI 0 t) - (t ^ 2 / 4 - t ^ 4 / 64)| +
            |g ^ 2 - (t ^ 2 / 4 - t ^ 4 / 16)|) :=
          add_le_add le_rfl (abs_add_le _ _)
      _ = _ := by ring
  calc
    _ ≤ |t * g - (t ^ 2 / 2 - t ^ 4 / 16)| +
        |Real.log (besselI 0 t) - (t ^ 2 / 4 - t ^ 4 / 64)| +
        |g ^ 2 - (t ^ 2 / 4 - t ^ 4 / 16)| := htri
    _ ≤ 5 * t ^ 6 := by linarith [htg, hlog, hgsq, pow_nonneg ht0.le 6]

/-- The critical score formula has the stated sixth-order jet. -/
theorem vonMisesDissipation_jet_EX021 (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) :
    |vonMisesDissipationEX021 t - (4 * Real.pi ^ 2) * t ^ 6 / 128| ≤
      3 * (4 * Real.pi ^ 2) * t ^ 8 := by
  let g : ℝ := besselRatio t
  let s : ℝ := t - 2 * g
  let v : ℝ := g / t
  have hjet := besselRatio_jet_EX021 t (by rw [abs_of_pos ht0]; linarith)
  have hgjet : |g - (t / 2 - t ^ 3 / 16)| ≤ t ^ 5 := by
    simpa [g, abs_of_pos ht0] using hjet
  have hs : |s - t ^ 3 / 8| ≤ 2 * t ^ 5 := by
    have he : s - t ^ 3 / 8 = -2 * (g - (t / 2 - t ^ 3 / 16)) := by
      dsimp [s]; ring
    rw [he, abs_mul]
    norm_num
    nlinarith [hgjet]
  have hs0 : |s| ≤ t ^ 3 := by
    calc
      |s| ≤ |s - t ^ 3 / 8| + |t ^ 3 / 8| := by
        have := abs_sub_le s (t ^ 3 / 8) 0
        simpa using this
      _ ≤ 2 * t ^ 5 + t ^ 3 / 8 := by
        have ht3 : 0 ≤ t ^ 3 := by positivity
        have habs : |t ^ 3 / 8| = t ^ 3 / 8 := by
          rw [abs_div, abs_of_nonneg ht3]; norm_num
        rw [habs]
        exact add_le_add hs le_rfl
      _ ≤ t ^ 3 := by
        have ht2 : t ^ 2 ≤ 1 / 4 := by nlinarith [ht1]
        nlinarith [ht2, mul_nonneg (pow_nonneg ht0.le 3) ht0.le]
  have hv : |v - 1 / 2| ≤ t ^ 2 := by
    have he : v - 1 / 2 = (g - (t / 2 - t ^ 3 / 16)) / t - t ^ 2 / 16 := by
      dsimp [v]; field_simp [ne_of_gt ht0]; ring
    rw [he]
    have hdiv : |(g - (t / 2 - t ^ 3 / 16)) / t| ≤ t ^ 4 := by
      rw [abs_div, abs_of_pos ht0]
      exact (div_le_iff₀ ht0).2 (by nlinarith [hgjet])
    calc
      _ ≤ |(g - (t / 2 - t ^ 3 / 16)) / t| + |t ^ 2 / 16| := abs_sub _ _
      _ ≤ t ^ 4 + t ^ 2 / 16 := by
        have habs : |t ^ 2 / 16| = t ^ 2 / 16 := abs_of_nonneg (by positivity)
        rw [habs]
        exact add_le_add hdiv le_rfl
      _ ≤ t ^ 2 := by
        have ht2 : t ^ 2 ≤ 1 / 4 := by nlinarith [ht1]
        nlinarith [ht2, sq_nonneg t]
  have hv0 : |v| ≤ 1 := by
    calc
      |v| ≤ |v - 1 / 2| + |(1 / 2 : ℝ)| := by
        have := abs_sub_le v (1 / 2 : ℝ) 0
        simpa using this
      _ ≤ t ^ 2 + 1 / 2 := by norm_num; linarith [hv]
      _ ≤ 1 := by nlinarith [sq_nonneg t, ht1]
  have hsq : |s ^ 2 - (t ^ 3 / 8) ^ 2| ≤ (9 / 4 : ℝ) * t ^ 8 := by
    rw [show s ^ 2 - (t ^ 3 / 8) ^ 2 = (s - t ^ 3 / 8) * (s + t ^ 3 / 8) by ring,
      abs_mul]
    have hsum : |s + t ^ 3 / 8| ≤ (9 / 8 : ℝ) * t ^ 3 := by
      calc
        |s + t ^ 3 / 8| ≤ |s| + |t ^ 3 / 8| := abs_add_le _ _
        _ ≤ t ^ 3 + t ^ 3 / 8 := by
          have ht3 : 0 ≤ t ^ 3 := by positivity
          have habs : |t ^ 3 / 8| = t ^ 3 / 8 := by
            rw [abs_div, abs_of_nonneg ht3]; norm_num
          rw [habs]
          exact add_le_add hs0 (by norm_num [abs_of_nonneg ht3])
        _ = (9 / 8 : ℝ) * t ^ 3 := by ring
    calc
      |s - t ^ 3 / 8| * |s + t ^ 3 / 8| ≤
          (2 * t ^ 5) * ((9 / 8 : ℝ) * t ^ 3) := mul_le_mul hs hsum
            (abs_nonneg _) (by positivity)
      _ ≤ (9 / 4 : ℝ) * t ^ 8 := by
        have ht3 : 0 ≤ t ^ 3 := by positivity
        nlinarith [ht3]
  have hprod : |s ^ 2 * v - t ^ 6 / 128| ≤ 3 * t ^ 8 := by
    have he : s ^ 2 * v - t ^ 6 / 128 =
        (s ^ 2 - (t ^ 3 / 8) ^ 2) * v + (t ^ 3 / 8) ^ 2 * (v - 1 / 2) := by
      dsimp [s, v]
      field_simp [ne_of_gt ht0]
      ring
    have hB : |(t ^ 3 / 8) ^ 2| = t ^ 6 / 64 := by
      rw [abs_of_nonneg (by positivity : 0 ≤ (t ^ 3 / 8) ^ 2)]
      ring
    rw [he]
    calc
      _ ≤ |s ^ 2 - (t ^ 3 / 8) ^ 2| * |v| +
          |(t ^ 3 / 8) ^ 2| * |v - 1 / 2| := by
        calc
          |(s ^ 2 - (t ^ 3 / 8) ^ 2) * v +
              (t ^ 3 / 8) ^ 2 * (v - 1 / 2)| ≤
            |(s ^ 2 - (t ^ 3 / 8) ^ 2) * v| +
              |(t ^ 3 / 8) ^ 2 * (v - 1 / 2)| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul]
      _ ≤ (9 / 4 : ℝ) * t ^ 8 * 1 + (t ^ 6 / 64) * t ^ 2 := by
        rw [hB]
        exact add_le_add
          (mul_le_mul hsq hv0 (abs_nonneg _) (by positivity))
          (mul_le_mul le_rfl hv (abs_nonneg _) (by positivity))
      _ ≤ 3 * t ^ 8 := by nlinarith
  have hscale : 0 ≤ 4 * Real.pi ^ 2 := by positivity
  have hrewrite :
      4 * Real.pi ^ 2 * (t - 2 * besselRatio t) ^ 2 * (besselRatio t / t) -
        4 * Real.pi ^ 2 * t ^ 6 / 128 =
      (4 * Real.pi ^ 2) * (s ^ 2 * v - t ^ 6 / 128) := by
    dsimp [s, v]
    ring
  rw [vonMisesDissipationEX021, hrewrite, abs_mul, abs_of_nonneg hscale]
  calc
    (4 * Real.pi ^ 2) * |s ^ 2 * v - t ^ 6 / 128| ≤
        (4 * Real.pi ^ 2) * (3 * t ^ 8) :=
      mul_le_mul_of_nonneg_left hprod hscale
    _ = _ := by ring


/-- A concrete positive gap and quadratic quotient asymptotic on a right neighborhood of zero. -/
theorem vonMisesQuotient_jet_EX021 (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 100) :
    0 < vonMisesGapEX021 t ∧
      |vonMisesQuotientEX021 t - (4 * Real.pi ^ 2) * t ^ 2 / 4| ≤
        400 * (4 * Real.pi ^ 2) * t ^ 4 := by
  have hG := vonMisesGap_jet_EX021 t ht0 (by linarith [ht1])
  have hGpos : t ^ 4 / 128 ≤ vonMisesGapEX021 t := by
    have ht2 : t ^ 2 ≤ 1 / 10000 := by
      have hprod : 0 ≤ t * (1 / 100 - t) :=
        mul_nonneg ht0.le (by linarith [ht1])
      nlinarith
    have ht4 : 5 * t ^ 6 ≤ t ^ 4 / 128 := by
      have hnonneg : 0 ≤ t ^ 4 := by positivity
      have hcoef : (5 : ℝ) * t ^ 2 ≤ 1 / 128 := by nlinarith [ht2]
      calc
        5 * t ^ 6 = (5 * t ^ 2) * t ^ 4 := by ring
        _ ≤ (1 / 128) * t ^ 4 := mul_le_mul_of_nonneg_right hcoef hnonneg
        _ = t ^ 4 / 128 := by ring
    have hGlo := (abs_le.mp hG).1
    linarith
  have hGstrict : 0 < vonMisesGapEX021 t := by
    have ht4 : 0 < t ^ 4 := pow_pos ht0 4
    have : 0 < t ^ 4 / 128 := by positivity
    exact lt_of_lt_of_le this hGpos
  have hD := vonMisesDissipation_jet_EX021 t ht0 (by linarith [ht1])
  have ha0 : 0 < 4 * Real.pi ^ 2 := by positivity
  have hnum :
      |(vonMisesDissipationEX021 t - (4 * Real.pi ^ 2) * t ^ 6 / 128) -
        ((4 * Real.pi ^ 2) * t ^ 2 / 2) *
          (vonMisesGapEX021 t - t ^ 4 / 64)| ≤
        (11 / 2 : ℝ) * (4 * Real.pi ^ 2) * t ^ 8 := by
    calc
      _ ≤ |vonMisesDissipationEX021 t - (4 * Real.pi ^ 2) * t ^ 6 / 128| +
          |((4 * Real.pi ^ 2) * t ^ 2 / 2) *
            (vonMisesGapEX021 t - t ^ 4 / 64)| := abs_sub _ _
      _ ≤ 3 * (4 * Real.pi ^ 2) * t ^ 8 +
          ((4 * Real.pi ^ 2) * t ^ 2 / 2) * (5 * t ^ 6) := by
        have hc : 0 ≤ ((4 * Real.pi ^ 2) * t ^ 2 / 2) := by positivity
        have hterm :
            |((4 * Real.pi ^ 2) * t ^ 2 / 2) *
                (vonMisesGapEX021 t - t ^ 4 / 64)| ≤
              ((4 * Real.pi ^ 2) * t ^ 2 / 2) * (5 * t ^ 6) := by
          rw [abs_mul, abs_of_nonneg hc]
          exact mul_le_mul_of_nonneg_left hG hc
        exact add_le_add hD hterm
      _ = (11 / 2 : ℝ) * (4 * Real.pi ^ 2) * t ^ 8 := by ring
  have hcancel :
      vonMisesQuotientEX021 t - (4 * Real.pi ^ 2) * t ^ 2 / 4 =
        ((vonMisesDissipationEX021 t - (4 * Real.pi ^ 2) * t ^ 6 / 128) -
          ((4 * Real.pi ^ 2) * t ^ 2 / 2) *
            (vonMisesGapEX021 t - t ^ 4 / 64)) /
          (2 * vonMisesGapEX021 t) := by
    dsimp [vonMisesQuotientEX021]
    field_simp [ne_of_gt hGstrict]
    ring
  refine ⟨hGstrict, ?_⟩
  rw [hcancel, abs_div, abs_of_pos (mul_pos (by norm_num) hGstrict)]
  apply (div_le_iff₀ (mul_pos (by norm_num) hGstrict)).2
  have hratio : t ^ 8 / (2 * vonMisesGapEX021 t) ≤ 64 * t ^ 4 := by
    have hden : 0 < 2 * vonMisesGapEX021 t := mul_pos (by norm_num) hGstrict
    apply (div_le_iff₀ hden).2
    have h := mul_le_mul_of_nonneg_left hGpos (by positivity : 0 ≤ 128 * t ^ 4)
    calc
      t ^ 8 = (128 * t ^ 4) * (t ^ 4 / 128) := by ring
      _ ≤ (128 * t ^ 4) * vonMisesGapEX021 t := h
      _ = 64 * t ^ 4 * (2 * vonMisesGapEX021 t) := by ring
  calc
    |(vonMisesDissipationEX021 t - (4 * Real.pi ^ 2) * t ^ 6 / 128) -
        ((4 * Real.pi ^ 2) * t ^ 2 / 2) *
          (vonMisesGapEX021 t - t ^ 4 / 64)| ≤
        (11 / 2 : ℝ) * (4 * Real.pi ^ 2) * t ^ 8 := hnum
    _ ≤ 400 * (4 * Real.pi ^ 2) * t ^ 4 *
        (2 * vonMisesGapEX021 t) := by
          have hden : 0 < 2 * vonMisesGapEX021 t := mul_pos (by norm_num) hGstrict
          have ht8 : t ^ 8 ≤ 64 * t ^ 4 * (2 * vonMisesGapEX021 t) :=
            (div_le_iff₀ hden).mp hratio
          have hscale : 0 ≤ (11 / 2 : ℝ) * (4 * Real.pi ^ 2) := by positivity
          calc
            (11 / 2 : ℝ) * (4 * Real.pi ^ 2) * t ^ 8 ≤
                (11 / 2 : ℝ) * (4 * Real.pi ^ 2) *
                  (64 * t ^ 4 * (2 * vonMisesGapEX021 t)) :=
              mul_le_mul_of_nonneg_left ht8 hscale
            _ ≤ 400 * (4 * Real.pi ^ 2) * t ^ 4 *
                (2 * vonMisesGapEX021 t) := by
              have hc : (11 / 2 : ℝ) * 64 ≤ 400 := by norm_num
              calc
                (11 / 2 : ℝ) * (4 * Real.pi ^ 2) *
                    (64 * t ^ 4 * (2 * vonMisesGapEX021 t)) =
                    ((11 / 2 : ℝ) * 64) *
                      ((4 * Real.pi ^ 2) * t ^ 4 *
                        (2 * vonMisesGapEX021 t)) := by ring
                _ ≤ 400 * ((4 * Real.pi ^ 2) * t ^ 4 *
                    (2 * vonMisesGapEX021 t)) :=
                  mul_le_mul_of_nonneg_right hc (by positivity)
                _ = _ := by ring

theorem vonMisesTorusDensity_exp_EX021 (t : ℝ) (x : DGPS.Torus 1) :
    vonMisesTorusDensityEX021 t x =
      (besselI 0 t)⁻¹ * Real.exp (t * (xyMode x).re) := by
  unfold vonMisesTorusDensityEX021 DGPS.Circle.BesselMoments.besselDensity
  rw [DGPS.Examples.AttractiveXYCritical.xyMode_re_eq_angCos_xyc]
  rw [div_eq_mul_inv]
  ring

theorem vonMisesTorusDensity_continuous_EX021 (t : ℝ) :
    Continuous (vonMisesTorusDensityEX021 t) := by
  rw [funext (vonMisesTorusDensity_exp_EX021 t)]
  exact continuous_const.mul (Real.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_re.comp continuous_xyMode)))

theorem xyMode_neg_EX021 (x : DGPS.Torus 1) :
    xyMode (-x) = star (xyMode x) := by
  simpa [xyMode_zero] using xyMode_sub (0 : DGPS.Torus 1) x

theorem vonMisesTorusDensity_even_EX021 (t : ℝ) (x : DGPS.Torus 1) :
    vonMisesTorusDensityEX021 t (-x) = vonMisesTorusDensityEX021 t x := by
  rw [vonMisesTorusDensity_exp_EX021, vonMisesTorusDensity_exp_EX021, xyMode_neg_EX021]
  simp

theorem vonMisesTorusDensity_sinMoment_EX021 (t : ℝ) :
    ∫ x, (xyMode x).im * vonMisesTorusDensityEX021 t x ∂DGPS.haar 1 = 0 := by
  have hInv : (DGPS.haar 1).IsNegInvariant := Pi.isNegInvariant_volume
  have hodd : ∀ x : DGPS.Torus 1,
      (xyMode (-x)).im * vonMisesTorusDensityEX021 t (-x) =
        -((xyMode x).im * vonMisesTorusDensityEX021 t x) := by
    intro x
    rw [xyMode_neg_EX021, vonMisesTorusDensity_even_EX021]
    simp
  have h := integral_neg_eq_self
    (fun x : DGPS.Torus 1 => (xyMode x).im * vonMisesTorusDensityEX021 t x)
    (DGPS.haar 1)
  simp_rw [hodd] at h
  rw [integral_neg] at h
  linarith

/-- The exact weighted sine-square moment of the actual torus von Mises density. -/
theorem vonMisesTorusDensity_sinSqMoment_EX021 (t : ℝ) (ht : 0 < t) :
    ∫ x, (xyMode x).im ^ 2 * vonMisesTorusDensityEX021 t x ∂DGPS.haar 1 =
      besselRatio t / t := by
  let c : DGPS.Torus 1 → ℝ := xyTrig 1 0 0
  let s : DGPS.Torus 1 → ℝ := xyTrig 0 1 0
  let q : DGPS.Torus 1 → ℝ := vonMisesTorusDensityEX021 t
  have hcS : DGPS.IsSmoothPeriodic c := by
    simpa [c] using isSmoothPeriodic_xyTrig 1 0 0
  have hsS : DGPS.IsSmoothPeriodic s := by
    simpa [s] using isSmoothPeriodic_xyTrig 0 1 0
  have hqExpr : q = fun x =>
      (besselI 0 t)⁻¹ * Real.exp (t * c x) := by
    funext x
    dsimp [q, c]
    rw [vonMisesTorusDensity_exp_EX021]
    simp [xyTrig]
  have harg : ContDiff ℝ ∞ (fun y : Fin 1 → ℝ => t * c (DGPS.torusLift y)) := by
    change ContDiff ℝ ∞ (fun y : Fin 1 → ℝ => t * xyTrig 1 0 0 (DGPS.torusLift y))
    exact contDiff_const.mul (by
      change ContDiff ℝ ∞ ((xyTrig 1 0 0) ∘ DGPS.torusLift)
      exact hcS)
  have hexp : ContDiff ℝ ∞ (fun y : Fin 1 → ℝ => Real.exp (t * c (DGPS.torusLift y))) :=
    contDiff_exp.comp harg
  have hqS : DGPS.IsSmoothPeriodic q := by
    unfold DGPS.IsSmoothPeriodic
    rw [hqExpr]
    exact contDiff_const.mul hexp
  have hcder (x : DGPS.Torus 1) : DGPS.coordPartial 0 c x = -2 * Real.pi * s x := by
    dsimp [c, s]
    rw [DGPS.Examples.AttractiveXY.coordPartial_xyTrig]
    simp [xyTrig]
  have hsder (x : DGPS.Torus 1) : DGPS.coordPartial 0 s x = 2 * Real.pi * c x := by
    dsimp [c, s]
    rw [DGPS.Examples.AttractiveXY.coordPartial_xyTrig]
    simp [xyTrig]
  have hqder (x : DGPS.Torus 1) :
      DGPS.coordPartial 0 q x = -2 * Real.pi * t * s x * q x := by
    rw [hqExpr]
    have hx : DifferentiableAt ℝ (c ∘ DGPS.torusLift) (SharpLSI.secT x) :=
      (hcS.differentiable (by simp)) _
    rw [DGPS.Lipschitz.WeightedGenerator.coordPartial_exp_comp
      ((besselI 0 t)⁻¹) t 0 x hx, hcder]
    ring
  have hibp := DGPS.integral_mul_coordPartial_of_smooth hsS hqS 0
  have hleft :
      ∫ x, s x * DGPS.coordPartial 0 q x ∂DGPS.haar 1 =
        (-2 * Real.pi * t) *
          ∫ x, s x ^ 2 * q x ∂DGPS.haar 1 := by
    have hfun : ∀ x, s x * DGPS.coordPartial 0 q x =
        (-2 * Real.pi * t) * (s x ^ 2 * q x) := by
      intro x
      rw [hqder]
      ring
    calc
      ∫ x, s x * DGPS.coordPartial 0 q x ∂DGPS.haar 1 =
          ∫ x, (-2 * Real.pi * t) * (s x ^ 2 * q x) ∂DGPS.haar 1 :=
            integral_congr_ae (Filter.Eventually.of_forall hfun)
      _ = _ := integral_const_mul _ _
  have hright :
      ∫ x, DGPS.coordPartial 0 s x * q x ∂DGPS.haar 1 =
        (2 * Real.pi) *
          ∫ x, c x * q x ∂DGPS.haar 1 := by
    have hfun : ∀ x, DGPS.coordPartial 0 s x * q x =
        (2 * Real.pi) * (c x * q x) := by
      intro x
      rw [hsder]
      ring
    calc
      ∫ x, DGPS.coordPartial 0 s x * q x ∂DGPS.haar 1 =
          ∫ x, (2 * Real.pi) * (c x * q x) ∂DGPS.haar 1 :=
            integral_congr_ae (Filter.Eventually.of_forall hfun)
      _ = _ := integral_const_mul _ _
  have hibp' := hibp
  have hcos : ∫ x, c x * q x ∂DGPS.haar 1 = besselRatio t := by
    have hfun : (fun x => c x * q x) =
        (fun x => (xyMode x).re * vonMisesTorusDensityEX021 t x) := by
      funext x
      dsimp [c, q]
      simp [xyTrig, DGPS.Examples.AttractiveXYCritical.xyMode_re_eq_angCos_xyc]
    rw [hfun]
    exact vonMisesTorusDensity_cosMoment_EX021 t
  rw [hleft, hright, hcos] at hibp'
  have hcancel :
      (2 * Real.pi) *
        (t * (∫ x, s x ^ 2 * q x ∂DGPS.haar 1) - besselRatio t) = 0 := by
    nlinarith [hibp']
  have hmoment :
      t * (∫ x, s x ^ 2 * q x ∂DGPS.haar 1) = besselRatio t := by
    have hpi : 2 * Real.pi ≠ 0 := by positivity
    have hz := (mul_eq_zero.mp hcancel).resolve_left hpi
    linarith
  have hsin : ∀ x, s x = (xyMode x).im := by
    intro x
    simp [s, xyTrig]
  rw [show (fun x => (xyMode x).im ^ 2 * q x) =
    fun x => s x ^ 2 * q x by funext x; rw [hsin x]]
  calc
    ∫ x, s x ^ 2 * q x ∂DGPS.haar 1 =
        (t * (∫ x, s x ^ 2 * q x ∂DGPS.haar 1)) / t := by
          field_simp [ne_of_gt ht]
    _ = besselRatio t / t := by rw [hmoment]

/-- The critical score difference between q_t and its EX018 frozen law, in the angular
coordinate. The frozen field is the one at the actual first moment (g(t),0). -/
noncomputable def vonMisesScoreDifferenceEX021 (t : ℝ) (x : DGPS.Torus 1) : ℝ :=
  DGPS.coordPartial 0
    (xyTrig t 0 0 - xyTrig (2 * besselRatio t) 0 0) x

theorem vonMisesScoreDifference_formula_EX021 (t : ℝ) (x : DGPS.Torus 1) :
    vonMisesScoreDifferenceEX021 t x =
      -2 * Real.pi * (t - 2 * besselRatio t) * (xyMode x).im := by
  have he : xyTrig t 0 0 - xyTrig (2 * besselRatio t) 0 0 =
      xyTrig (t - 2 * besselRatio t) 0 0 := by
    funext y
    simp [xyTrig]
    ring
  unfold vonMisesScoreDifferenceEX021
  rw [he, DGPS.Examples.AttractiveXY.coordPartial_xyTrig]
  simp [xyTrig]

/-- The squared EX018 score discrepancy averaged against the actual positive von Mises density. -/
noncomputable def actualVonMisesDissipationEX021 (t : ℝ) : ℝ :=
  ∫ x, vonMisesScoreDifferenceEX021 t x ^ 2 *
    vonMisesTorusDensityEX021 t x ∂DGPS.haar 1

theorem actualVonMisesDissipation_formula_EX021 (t : ℝ) (ht : 0 < t) :
    actualVonMisesDissipationEX021 t = vonMisesDissipationEX021 t := by
  have hscore : ∀ x,
      vonMisesScoreDifferenceEX021 t x ^ 2 *
          vonMisesTorusDensityEX021 t x =
        (4 * Real.pi ^ 2) * (t - 2 * besselRatio t) ^ 2 *
          ((xyMode x).im ^ 2 * vonMisesTorusDensityEX021 t x) := by
    intro x
    rw [vonMisesScoreDifference_formula_EX021]
    ring
  unfold actualVonMisesDissipationEX021
  calc
    (∫ x, vonMisesScoreDifferenceEX021 t x ^ 2 *
        vonMisesTorusDensityEX021 t x ∂DGPS.haar 1) =
      ∫ x, (4 * Real.pi ^ 2) * (t - 2 * besselRatio t) ^ 2 *
        ((xyMode x).im ^ 2 * vonMisesTorusDensityEX021 t x) ∂DGPS.haar 1 :=
          integral_congr_ae (Filter.Eventually.of_forall hscore)
    _ = (4 * Real.pi ^ 2) * (t - 2 * besselRatio t) ^ 2 *
        ∫ x, (xyMode x).im ^ 2 * vonMisesTorusDensityEX021 t x ∂DGPS.haar 1 :=
          integral_const_mul _ _
    _ = vonMisesDissipationEX021 t := by
      rw [vonMisesTorusDensity_sinSqMoment_EX021 t ht]
      unfold vonMisesDissipationEX021
      ring

/-- The probability measure with the actual von Mises density q_t against Haar. -/
noncomputable def vonMisesMeasureEX021 (t : ℝ) : MeasureTheory.Measure (DGPS.Torus 1) :=
  (DGPS.haar 1).withDensity (fun x => ENNReal.ofReal (vonMisesTorusDensityEX021 t x))

theorem vonMisesMeasure_isProbabilityEX021 (t : ℝ) :
    IsProbabilityMeasure (vonMisesMeasureEX021 t) := by
  have hq : Continuous (vonMisesTorusDensityEX021 t) := vonMisesTorusDensity_continuous_EX021 t
  have hi : Integrable (vonMisesTorusDensityEX021 t) (DGPS.haar 1) :=
    hq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnonneg : ∀ᵐ x ∂DGPS.haar 1,
      0 ≤ vonMisesTorusDensityEX021 t x :=
    Filter.Eventually.of_forall fun x =>
      (vonMisesTorusDensity_pos_EX021 t x).le
  constructor
  unfold vonMisesMeasureEX021
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hnonneg,
    vonMisesTorusDensity_mass_EX021, ENNReal.ofReal_one]

noncomputable def vonMisesProbabilityEX021 (t : ℝ) : ProbabilityMeasure (DGPS.Torus 1) :=
  ⟨vonMisesMeasureEX021 t, vonMisesMeasure_isProbabilityEX021 t⟩

theorem integral_vonMisesProbabilityEX021 (t : ℝ) {f : DGPS.Torus 1 → ℝ}
    (hf : Continuous f) :
    ∫ x, f x ∂(vonMisesProbabilityEX021 t : Measure (DGPS.Torus 1)) =
      ∫ x, vonMisesTorusDensityEX021 t x * f x ∂DGPS.haar 1 := by
  have hq : Continuous (vonMisesTorusDensityEX021 t) := vonMisesTorusDensity_continuous_EX021 t
  have hm : Measurable fun x : DGPS.Torus 1 =>
      ENNReal.ofReal (vonMisesTorusDensityEX021 t x) :=
    ENNReal.measurable_ofReal.comp hq.measurable
  have ht : ∀ᵐ x ∂DGPS.haar 1,
      ENNReal.ofReal (vonMisesTorusDensityEX021 t x) < ⊤ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hi : Integrable
      (fun x => vonMisesTorusDensityEX021 t x * f x) (DGPS.haar 1) :=
    (hq.mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change ∫ x, f x ∂((DGPS.haar 1).withDensity
      (fun x => ENNReal.ofReal (vonMisesTorusDensityEX021 t x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul hm ht]
  simp_rw [ENNReal.toReal_ofReal (vonMisesTorusDensity_pos_EX021 t _).le, smul_eq_mul]

theorem vonMisesProbability_firstMomentsEX021 (t : ℝ) :
    xyZ1 (vonMisesProbabilityEX021 t : Measure (DGPS.Torus 1)) = besselRatio t ∧
      xyZ2 (vonMisesProbabilityEX021 t : Measure (DGPS.Torus 1)) = 0 := by
  constructor
  · change ∫ x, (Complex.re ∘ xyMode) x ∂
      (vonMisesProbabilityEX021 t : Measure _) = besselRatio t
    rw [integral_vonMisesProbabilityEX021 t
      (Complex.continuous_re.comp continuous_xyMode)]
    simp only [Function.comp_apply]
    rw [integral_congr_ae (Filter.Eventually.of_forall fun x =>
      mul_comm (vonMisesTorusDensityEX021 t x) (xyMode x).re)]
    exact vonMisesTorusDensity_cosMoment_EX021 t
  · change ∫ x, (Complex.im ∘ xyMode) x ∂
      (vonMisesProbabilityEX021 t : Measure _) = 0
    rw [integral_vonMisesProbabilityEX021 t
      (Complex.continuous_im.comp continuous_xyMode)]
    simp only [Function.comp_apply]
    rw [integral_congr_ae (Filter.Eventually.of_forall fun x =>
      mul_comm (vonMisesTorusDensityEX021 t x) (xyMode x).im)]
    exact vonMisesTorusDensity_sinMoment_EX021 t

theorem besselDensity_log_EX021 (t : ℝ) (θ : DGPS.Circle.AngularNormalization.AngCircle) :
    Real.log (besselDensity t θ) =
      t * angCos θ - Real.log (besselI 0 t) := by
  unfold besselDensity
  rw [Real.log_div (Real.exp_pos _).ne' (besselI_zero_pos t).ne']
  rw [Real.log_exp]

theorem vonMisesTorus_logDensity_EX021 (t : ℝ) (x : DGPS.Torus 1) :
    Real.log (vonMisesTorusDensityEX021 t x) =
      t * (xyMode x).re - Real.log (besselI 0 t) := by
  rw [vonMisesTorusDensityEX021, besselDensity_log_EX021]
  rw [← DGPS.Examples.AttractiveXYCritical.xyMode_re_eq_angCos_xyc]


/-- The score difference is the derivative of the log density ratio against the EX018 frozen law. -/
theorem vonMisesScoreDifference_logRatio_EX021 (t : ℝ) (x : DGPS.Torus 1) :
    vonMisesScoreDifferenceEX021 t x =
      DGPS.coordPartial 0
        (fun y => Real.log (vonMisesTorusDensityEX021 t y) -
          Real.log ((xyFrozenLaw 2 0
            (vonMisesProbabilityEX021 t : Measure (DGPS.Torus 1))).density y)) x := by
  have hm := vonMisesProbability_firstMomentsEX021 t
  have href : xyFrozenLaw 2 0
      (vonMisesProbabilityEX021 t : Measure (DGPS.Torus 1)) =
      xyFrozen (2 * besselRatio t) 0 := by
    unfold xyFrozenLaw
    rw [hm.1, hm.2]
    simp
  have hlogq : (fun y => Real.log (vonMisesTorusDensityEX021 t y)) =
      xyTrig t 0 (-Real.log (besselI 0 t)) := by
    funext y
    rw [vonMisesTorus_logDensity_EX021]
    simp [xyTrig]
    ring
  have hlogp : (fun y => Real.log
      ((xyFrozenLaw 2 0 (vonMisesProbabilityEX021 t : Measure (DGPS.Torus 1))).density y)) =
      xyTrig (2 * besselRatio t) 0
        (-Real.log (xyPartition (2 * besselRatio t) 0)) := by
    rw [href]
    funext y
    exact log_xyFrozen_density (2 * besselRatio t) 0 y
  have he : xyTrig t 0 0 - xyTrig (2 * besselRatio t) 0 0 =
      xyTrig (t - 2 * besselRatio t) 0 0 := by
    funext y
    simp [xyTrig]
    ring
  have hdiff :
      (fun y => Real.log (vonMisesTorusDensityEX021 t y) -
        Real.log ((xyFrozenLaw 2 0
          (vonMisesProbabilityEX021 t : Measure (DGPS.Torus 1))).density y)) =
        xyTrig (t - 2 * besselRatio t) 0
          (-Real.log (besselI 0 t) + Real.log (xyPartition (2 * besselRatio t) 0)) := by
    funext y
    rw [congrFun hlogq y, congrFun hlogp y]
    simp [xyTrig]
    ring
  unfold vonMisesScoreDifferenceEX021
  rw [he]
  rw [hdiff, DGPS.Examples.AttractiveXY.coordPartial_xyTrig,
    DGPS.Examples.AttractiveXY.coordPartial_xyTrig]

noncomputable def vonMisesEntropyEX021 (t : ℝ) : ℝ :=
  ∫ x, vonMisesTorusDensityEX021 t x *
    Real.log (vonMisesTorusDensityEX021 t x) ∂DGPS.haar 1

theorem vonMisesEntropy_formula_EX021 (t : ℝ) :
    vonMisesEntropyEX021 t = t * besselRatio t - Real.log (besselI 0 t) := by
  have hq : Continuous (vonMisesTorusDensityEX021 t) := vonMisesTorusDensity_continuous_EX021 t
  have hc : Continuous (fun x : DGPS.Torus 1 => (xyMode x).re) :=
    Complex.continuous_re.comp continuous_xyMode
  have hqcI : Integrable
      (fun x => vonMisesTorusDensityEX021 t x * (xyMode x).re) (DGPS.haar 1) :=
    (hq.mul hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hconstI : Integrable
      (fun x : DGPS.Torus 1 => Real.log (besselI 0 t) * vonMisesTorusDensityEX021 t x)
      (DGPS.haar 1) :=
    (continuous_const.mul hq).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpoint : ∀ x, vonMisesTorusDensityEX021 t x *
      Real.log (vonMisesTorusDensityEX021 t x) =
      t * (vonMisesTorusDensityEX021 t x * (xyMode x).re) -
        Real.log (besselI 0 t) * vonMisesTorusDensityEX021 t x := by
    intro x
    rw [vonMisesTorus_logDensity_EX021]
    ring
  have hmom : ∫ x, vonMisesTorusDensityEX021 t x * (xyMode x).re ∂DGPS.haar 1 =
      besselRatio t := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm
      (vonMisesTorusDensityEX021 t x) (xyMode x).re)]
    exact vonMisesTorusDensity_cosMoment_EX021 t
  unfold vonMisesEntropyEX021
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [integral_sub (hqcI.const_mul t) hconstI]
  have hmass : ∫ x, vonMisesTorusDensityEX021 t x ∂DGPS.haar 1 =
      1 := vonMisesTorusDensity_mass_EX021 t
  rw [integral_const_mul, integral_const_mul, hmom, hmass]
  ring


/-- The entropy of the actual positive von Mises density is its relative entropy against Haar. -/
theorem vonMisesEntropy_eq_relativeEntropy_EX021 (t : ℝ) :
    DGPS.relativeEntropy (vonMisesProbabilityEX021 t : Measure (DGPS.Torus 1))
      (DGPS.haar 1) =
      ENNReal.ofReal (vonMisesEntropyEX021 t) := by
  have hq : Continuous (vonMisesTorusDensityEX021 t) := vonMisesTorusDensity_continuous_EX021 t
  have hqI : Integrable (vonMisesTorusDensityEX021 t) (DGPS.haar 1) :=
    hq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnonneg : 0 ≤ᵐ[DGPS.haar 1] vonMisesTorusDensityEX021 t :=
    Filter.Eventually.of_forall fun x =>
      (vonMisesTorusDensity_pos_EX021 t x).le
  have hc : Continuous (fun x : DGPS.Torus 1 => (xyMode x).re) :=
    Complex.continuous_re.comp continuous_xyMode
  have hlogfun :
      (fun x => vonMisesTorusDensityEX021 t x *
        Real.log (vonMisesTorusDensityEX021 t x)) =
      fun x => vonMisesTorusDensityEX021 t x *
        (t * (xyMode x).re - Real.log (besselI 0 t)) := by
    funext x
    rw [vonMisesTorus_logDensity_EX021]
  have hlogI : Integrable
      (fun x => vonMisesTorusDensityEX021 t x *
        Real.log (vonMisesTorusDensityEX021 t x)) (DGPS.haar 1) := by
    rw [hlogfun]
    exact ((hq.mul ((continuous_const.mul hc).sub continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hRE :
      DGPS.relativeEntropy (vonMisesMeasureEX021 t) (DGPS.haar 1) =
        DGPS.homogeneousEntropy (DGPS.haar 1) (vonMisesTorusDensityEX021 t) :=
    DGPS.relativeEntropy_withDensity hnonneg hq.measurable.aemeasurable
  calc
    DGPS.relativeEntropy
        (vonMisesProbabilityEX021 t : Measure (DGPS.Torus 1)) (DGPS.haar 1) =
      DGPS.homogeneousEntropy (DGPS.haar 1) (vonMisesTorusDensityEX021 t) := by
        change DGPS.relativeEntropy (vonMisesMeasureEX021 t) (DGPS.haar 1) = _
        exact hRE
    _ = ENNReal.ofReal (vonMisesEntropyEX021 t) := by
      rw [DGPS.homogeneousEntropy_eq_formula hnonneg hqI hlogI,
        vonMisesTorusDensity_mass_EX021]
      simp [vonMisesEntropyEX021]

theorem freeEnergy_vonMises_formula_EX021 (t : ℝ) :
    DGPS.freeEnergy (DGPS.Models.attractiveXY 2 0) (vonMisesProbabilityEX021 t) =
      ((ENNReal.ofReal (vonMisesEntropyEX021 t) : ℝ≥0∞) : EReal) +
        ((1 - besselRatio t ^ 2 : ℝ) : EReal) := by
  rw [DGPS.Examples.AttractiveXY.freeEnergy_attractiveXY]
  have hm := vonMisesProbability_firstMomentsEX021 t
  rw [hm.1, hm.2, vonMisesEntropy_eq_relativeEntropy_EX021]
  congr 1
  ring_nf

noncomputable def actualVonMisesGapEX021 (t : ℝ) : ℝ :=
  vonMisesEntropyEX021 t - besselRatio t ^ 2

theorem actualVonMisesGap_eq_EX021 (t : ℝ) :
    actualVonMisesGapEX021 t = vonMisesGapEX021 t := by
  rw [actualVonMisesGapEX021, vonMisesEntropy_formula_EX021]
  rfl

noncomputable def actualVonMisesQuotientEX021 (t : ℝ) : ℝ :=
  actualVonMisesDissipationEX021 t / (2 * actualVonMisesGapEX021 t)

theorem actualVonMisesQuotient_eq_EX021 (t : ℝ) (ht : 0 < t) :
    actualVonMisesQuotientEX021 t = vonMisesQuotientEX021 t := by
  rw [actualVonMisesQuotientEX021, actualVonMisesDissipation_formula_EX021 t ht,
    actualVonMisesGap_eq_EX021]
  rfl

end DGPS.Examples.CriticalRecoveryAsymptoticsEX021
