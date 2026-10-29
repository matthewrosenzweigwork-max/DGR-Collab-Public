import DGPS.SingularCounterexample.Interfaces
import DGPS.Examples.PositiveH1.Fourier
import FullLabeledLSI.Examples.E01h1_Poisson

open MeasureTheory
open SharpLSI
open scoped ContDiff

namespace DGPS.SingularCounterexample

/-- The frequency-one cosine on the circle, in the legacy Fourier convention. -/
noncomputable abbrev c1 (x : Circle) : ℝ := SharpLSI.FL.Ex.LaneD.cm 1 x

theorem c1_torusPoint (t : ℝ) : c1 (torusPoint t) = Real.cos (2 * Real.pi * t) := by
  simpa [c1, torusPoint, DGPS.torusLift] using SharpLSI.FL.Ex.LaneD.cm_lift 1 t

theorem c1_le_one (x : Circle) : c1 x ≤ 1 := by
  have h := SharpLSI.FL.Ex.LaneD.cm_abs_le 1 x
  exact (abs_le.mp h).2

theorem c1_zero : c1 (0 : Circle) = 1 := by
  have h0 : torusPoint 0 = (0 : Circle) := by
    ext i
    simp [torusPoint, DGPS.torusLift, SharpLSI.liftT]
  rw [← h0]
  simpa using c1_torusPoint 0

theorem c1_even (x : Circle) : c1 (-x) = c1 x := by
  exact SharpLSI.FL.Ex.LaneD.cm_neg 1 x

theorem poissonDenominator_decomp (r : ℝ) (x : Circle) :
    1 - 2 * r * c1 x + r ^ 2 = (1 - r) ^ 2 + 2 * r * (1 - c1 x) := by
  ring

theorem poissonDenominator_pos {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (x : Circle) :
    0 < 1 - 2 * r * c1 x + r ^ 2 := by
  rw [poissonDenominator_decomp]
  have hsq : 0 < (1 - r) ^ 2 := sq_pos_of_ne_zero (ne_of_gt (sub_pos.mpr hr1))
  have hterm : 0 ≤ 2 * r * (1 - c1 x) := by
    exact mul_nonneg (by positivity) (sub_nonneg.mpr (c1_le_one x))
  linarith

/-- The normalized Poisson peak of radius `r` on the circle. -/
noncomputable def poissonPeak (r : ℝ) (x : Circle) : ℝ :=
  (1 - r) ^ 2 / (1 - 2 * r * c1 x + r ^ 2)

theorem poissonPeak_pos {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (x : Circle) :
    0 < poissonPeak r x := by
  unfold poissonPeak
  exact div_pos (sq_pos_of_ne_zero (ne_of_gt (sub_pos.mpr hr1)))
    (poissonDenominator_pos hr0 hr1 x)

theorem poissonPeak_le_one {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (x : Circle) :
    poissonPeak r x ≤ 1 := by
  unfold poissonPeak
  rw [div_le_iff₀ (poissonDenominator_pos hr0 hr1 x), poissonDenominator_decomp]
  have hterm : 0 ≤ 2 * r * (1 - c1 x) := by
    exact mul_nonneg (by positivity) (sub_nonneg.mpr (c1_le_one x))
  nlinarith

theorem poissonPeak_zero {r : ℝ} (hr1 : r < 1) : poissonPeak r 0 = 1 := by
  rw [poissonPeak, c1_zero]
  rw [show 1 - 2 * r * 1 + r ^ 2 = (1 - r) ^ 2 by ring]
  exact div_self (pow_ne_zero 2 (ne_of_gt (sub_pos.mpr hr1)))

theorem poissonPeak_even (r : ℝ) (x : Circle) : poissonPeak r (-x) = poissonPeak r x := by
  simp [poissonPeak, c1_even]

theorem poissonPeak_smooth_periodic {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    IsSmoothPeriodic (poissonPeak r) := by
  unfold IsSmoothPeriodic
  change ContDiff ℝ ∞ (fun v : Fin 1 → ℝ => poissonPeak r (DGPS.torusLift v))
  have hcos : ContDiff ℝ ∞ (fun v : Fin 1 → ℝ => Real.cos (2 * Real.pi * v 0)) :=
    Real.contDiff_cos.comp (contDiff_const.mul (contDiff_apply ℝ ℝ 0))
  have hden : ContDiff ℝ ∞
      (fun v : Fin 1 → ℝ => 1 - 2 * r * Real.cos (2 * Real.pi * v 0) + r ^ 2) := by
    have hden' : ContDiff ℝ ∞
        (fun v : Fin 1 → ℝ => 1 - (2 * r) * Real.cos (2 * Real.pi * v 0) + r ^ 2) :=
      (contDiff_const.sub (contDiff_const.mul hcos)).add contDiff_const
    simpa [mul_assoc] using hden'
  have hden_ne : ∀ v : Fin 1 → ℝ,
      1 - 2 * r * Real.cos (2 * Real.pi * v 0) + r ^ 2 ≠ 0 := by
    intro v
    have h := poissonDenominator_pos hr0 hr1 (torusPoint (v 0))
    rw [c1_torusPoint] at h
    exact (ne_of_gt h)
  have hform : (fun v : Fin 1 → ℝ => poissonPeak r (DGPS.torusLift v)) =
      fun v => (1 - r) ^ 2 / (1 - 2 * r * Real.cos (2 * Real.pi * v 0) + r ^ 2) := by
    funext v
    have hlift : DGPS.torusLift v = torusPoint (v 0) := by
      simpa [torusPoint, DGPS.torusLift] using SharpLSI.FL.Ex.LaneD.lift_eq v
    rw [hlift, poissonPeak, c1_torusPoint]
  rw [hform]
  exact contDiff_const.div hden hden_ne

noncomputable def poissonPeakScale (r : ℝ) : ℝ := (1 - r) / (1 + r)

noncomputable def poissonPeakSeriesTerm (r : ℝ) (x : Circle) (j : ℕ) : ℝ :=
  2 * poissonPeakScale r * r ^ (j + 1) *
    DGPS.Examples.PositiveH1.Fourier.cosMode (j + 1) x

theorem poisson_cosMode_eq_legacy (n : ℕ) (x : Circle) :
    DGPS.Examples.PositiveH1.Fourier.cosMode n x =
      SharpLSI.FL.Ex.LaneD.cm (n : ℤ) x := by
  obtain ⟨t, ht⟩ := DGPS.Examples.PositiveH1.Fourier.torus_exists_lift x
  rw [ht, DGPS.Examples.PositiveH1.Fourier.cosMode_lift,
    SharpLSI.FL.Ex.LaneD.cm_lift]
  push_cast
  rfl

private theorem laneD_fourier_nat_pow (m : ℕ) (x : AddCircle (1 : ℝ)) :
    fourier (m : ℤ) x = (fourier 1 x) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hm : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by omega
      rw [hm, fourier_add, ih, pow_succ]

theorem poissonPeak_series_tail {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (x : Circle) :
    HasSum (poissonPeakSeriesTerm r x) (poissonPeak r x - poissonPeakScale r) := by
  let c : ℝ := poissonPeakScale r
  set z : ℂ := fourier 1 (x 0) with hzdef
  set w : ℂ := (r : ℂ) * z with hwdef
  have hz : ‖z‖ = 1 := by simp [hzdef]
  have hwn : ‖w‖ < 1 := by
    rw [hwdef, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, hz,
      abs_of_pos hr0]
    simpa using hr1
  have hgeom := (hasSum_geometric_of_norm_lt_one hwn).mul_left w
  have hgeom' := hgeom.mul_left (2 * c : ℂ)
  have hreal := Complex.hasSum_re hgeom'
  have hterm (j : ℕ) : ((2 * c : ℂ) * (w * w ^ j)).re = poissonPeakSeriesTerm r x j := by
    rw [← pow_succ', hwdef, mul_pow, ← Complex.ofReal_pow, hzdef,
      ← laneD_fourier_nat_pow]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul]
    simp only [poissonPeakSeriesTerm]
    rw [poisson_cosMode_eq_legacy]
    simp [c, SharpLSI.FL.Ex.LaneD.cm]
    ring
  have hwr : w.re = r * c1 x := by
    rw [hwdef, Complex.mul_re]
    simp [hzdef, c1, SharpLSI.FL.Ex.LaneD.cm]
  have hwi : w.im = r * SharpLSI.FL.Ex.LaneD.sm 1 x := by
    rw [hwdef, Complex.mul_im]
    simp [hzdef, SharpLSI.FL.Ex.LaneD.sm]
  have hunit : c1 x ^ 2 + (SharpLSI.FL.Ex.LaneD.sm 1 x) ^ 2 = 1 := by
    have hre : z.re = c1 x := by rfl
    have him : z.im = SharpLSI.FL.Ex.LaneD.sm 1 x := by rfl
    have h := Complex.sq_norm z
    rw [Complex.normSq_apply, hre, him] at h
    rw [hz] at h
    nlinarith
  have hden : Complex.normSq (1 - w) = 1 - 2 * r * c1 x + r ^ 2 := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, hwr, hwi]
    nlinarith [hunit]
  have hInvRe : (1 - w)⁻¹.re =
      (1 - r * c1 x) / (1 - 2 * r * c1 x + r ^ 2) := by
    rw [Complex.inv_re, Complex.sub_re, Complex.one_re, hwr, hden]
  have hInvIm : (1 - w)⁻¹.im =
      (r * SharpLSI.FL.Ex.LaneD.sm 1 x) / (1 - 2 * r * c1 x + r ^ 2) := by
    rw [Complex.inv_im, Complex.sub_im, Complex.one_im, hwi, hden]
    ring
  have hratio : (w * (1 - w)⁻¹).re =
      (r * c1 x - r ^ 2) / (1 - 2 * r * c1 x + r ^ 2) := by
    rw [Complex.mul_re, hwr, hwi, hInvRe, hInvIm]
    let D : ℝ := 1 - 2 * r * c1 x + r ^ 2
    have hD : D ≠ 0 := ne_of_gt (poissonDenominator_pos hr0 hr1 x)
    have hnum : r * c1 x * (1 - r * c1 x) -
        (r * SharpLSI.FL.Ex.LaneD.sm 1 x) ^ 2 = r * c1 x - r ^ 2 := by
      have hunit' := congrArg (fun a : ℝ => r ^ 2 * a) hunit
      nlinarith [hunit']
    calc
      r * c1 x * ((1 - r * c1 x) / D) -
          (r * SharpLSI.FL.Ex.LaneD.sm 1 x) *
            (r * SharpLSI.FL.Ex.LaneD.sm 1 x / D) =
          (r * c1 x * (1 - r * c1 x) -
            (r * SharpLSI.FL.Ex.LaneD.sm 1 x) ^ 2) / D := by
        field_simp [hD]
      _ = (r * c1 x - r ^ 2) / D := by rw [hnum]
  have hcscale : c * (1 - r ^ 2) = (1 - r) ^ 2 := by
    dsimp [c, poissonPeakScale]
    have hne : 1 + r ≠ 0 := ne_of_gt (by linarith)
    field_simp [hne]
    ring
  have hvalue : ((2 * c : ℂ) * (w * (1 - w)⁻¹)).re =
      poissonPeak r x - poissonPeakScale r := by
    have hmul : ((2 * c : ℂ) * (w * (1 - w)⁻¹)).re =
        2 * c * (w * (1 - w)⁻¹).re := by
      simp [Complex.mul_re]
    rw [hmul, hratio, poissonPeak]
    have hid : 2 * c * (r * c1 x - r ^ 2) =
        (1 - r) ^ 2 - c * (1 - 2 * r * c1 x + r ^ 2) := by
      rw [← hcscale]
      ring
    field_simp [ne_of_gt (poissonDenominator_pos hr0 hr1 x)]
    nlinarith [hid]
  have hseries : HasSum (poissonPeakSeriesTerm r x)
      (((2 * c : ℂ) * (w * (1 - w)⁻¹)).re) := by
    convert hreal using 1
    · funext j
      exact (hterm j).symm
  rw [hvalue] at hseries
  simpa [c] using hseries

theorem poissonPeak_series {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (x : Circle) :
    poissonPeak r x = poissonPeakScale r *
      (1 + 2 * ∑' j : ℕ, r ^ (j + 1) *
        DGPS.Examples.PositiveH1.Fourier.cosMode (j + 1) x) := by
  have hs := poissonPeak_series_tail hr0 hr1 x
  have hfactor : (∑' j : ℕ, poissonPeakSeriesTerm r x j) =
      2 * poissonPeakScale r * (∑' j : ℕ, r ^ (j + 1) *
        DGPS.Examples.PositiveH1.Fourier.cosMode (j + 1) x) := by
    calc
      (∑' j : ℕ, poissonPeakSeriesTerm r x j) =
          ∑' j : ℕ, (2 * poissonPeakScale r) * (r ^ (j + 1) *
            DGPS.Examples.PositiveH1.Fourier.cosMode (j + 1) x) := by
        apply tsum_congr
        intro j
        simp [poissonPeakSeriesTerm]
        ring
      _ = 2 * poissonPeakScale r * (∑' j : ℕ, r ^ (j + 1) *
          DGPS.Examples.PositiveH1.Fourier.cosMode (j + 1) x) := by
        rw [tsum_mul_left]
  calc
    poissonPeak r x = poissonPeakScale r + ∑' j : ℕ, poissonPeakSeriesTerm r x j := by
      have h := hs.tsum_eq
      linarith
    _ = poissonPeakScale r *
        (1 + 2 * ∑' j : ℕ, r ^ (j + 1) *
          DGPS.Examples.PositiveH1.Fourier.cosMode (j + 1) x) := by
      rw [hfactor]
      ring

private theorem circle_cosine_term_coeff (A : ℝ) (n : ℕ) (k : Fin 1 → ℤ) :
    ∫ x : Circle, UnitAddTorus.mFourier (-k) x *
        ((A * DGPS.Examples.PositiveH1.Fourier.cosMode n x : ℝ) : ℂ) ∂DGPS.haar 1 =
      ((A / 2 : ℝ) : ℂ) *
        ((if -k + DGPS.Examples.PositiveH1.Fourier.freq n = 0 then 1 else 0) +
          (if -k + -DGPS.Examples.PositiveH1.Fourier.freq n = 0 then 1 else 0)) := by
  have hfun : ∀ y : Circle, UnitAddTorus.mFourier (-k) y *
      ((A * DGPS.Examples.PositiveH1.Fourier.cosMode n y : ℝ) : ℂ) =
      ((A / 2 : ℝ) : ℂ) *
        (UnitAddTorus.mFourier (-k + DGPS.Examples.PositiveH1.Fourier.freq n) y +
          UnitAddTorus.mFourier (-k + -DGPS.Examples.PositiveH1.Fourier.freq n) y) := by
    intro y
    rw [Complex.ofReal_mul, DGPS.Examples.PositiveH1.Fourier.cosMode_ofReal,
      UnitAddTorus.mFourier_add, UnitAddTorus.mFourier_add]
    push_cast
    ring
  simp_rw [hfun]
  rw [integral_const_mul, integral_add
    (DGPS.Examples.PositiveH1.Fourier.integrable_mFourier _)
    (DGPS.Examples.PositiveH1.Fourier.integrable_mFourier _),
    DGPS.Examples.PositiveH1.Fourier.integral_mFourier,
    DGPS.Examples.PositiveH1.Fourier.integral_mFourier]

private theorem poissonPeak_term_coeff {r : ℝ} (k : ℤ) (j : ℕ) :
    ∫ x : Circle, UnitAddTorus.mFourier (-freqZ k) x *
        ((poissonPeakSeriesTerm r x j : ℝ) : ℂ) ∂DGPS.haar 1 =
      (((2 * poissonPeakScale r * r ^ (j + 1)) / 2 : ℝ) : ℂ) *
        ((if -freqZ k + DGPS.Examples.PositiveH1.Fourier.freq (Nat.succ j) = 0 then 1 else 0) +
          (if -freqZ k + -DGPS.Examples.PositiveH1.Fourier.freq (Nat.succ j) = 0 then 1 else 0)) := by
  simpa [poissonPeakSeriesTerm] using
    (circle_cosine_term_coeff (2 * poissonPeakScale r * r ^ (j + 1))
      (Nat.succ j) (freqZ k))

private theorem poissonPeak_integral_series {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (k : ℤ) :
    HasSum (fun j : ℕ => ∫ x : Circle,
        UnitAddTorus.mFourier (-freqZ k) x * ((poissonPeakSeriesTerm r x j : ℝ) : ℂ)
          ∂DGPS.haar 1)
      (∫ x : Circle, UnitAddTorus.mFourier (-freqZ k) x *
        ((poissonPeak r x - poissonPeakScale r : ℝ) : ℂ) ∂DGPS.haar 1) := by
  have hscale : 0 < poissonPeakScale r := by
    unfold poissonPeakScale
    exact div_pos (sub_pos.mpr hr1) (by linarith)
  have hbound : Summable (fun j : ℕ => 2 * poissonPeakScale r * r ^ (j + 1)) := by
    have hg := (summable_geometric_of_lt_one hr0.le hr1).mul_right r
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
      hg.mul_left (2 * poissonPeakScale r)
  have hint : ∀ j : ℕ, Integrable (fun x : Circle =>
      UnitAddTorus.mFourier (-freqZ k) x * ((poissonPeakSeriesTerm r x j : ℝ) : ℂ))
      (DGPS.haar 1) := by
    intro j
    apply DGPS.integrable_mFourier_mul
    have hc : Continuous (fun x : Circle => poissonPeakSeriesTerm r x j) := by
      change Continuous (fun x => (2 * poissonPeakScale r * r ^ (j + 1)) *
        DGPS.Examples.PositiveH1.Fourier.cosMode (j + 1) x)
      exact continuous_const.mul (DGPS.Examples.PositiveH1.Fourier.continuous_cosMode _)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnorm : ∀ j : ℕ, ∀ x : Circle,
      ‖UnitAddTorus.mFourier (-freqZ k) x *
        ((poissonPeakSeriesTerm r x j : ℝ) : ℂ)‖ ≤ 2 * poissonPeakScale r * r ^ (j + 1) := by
    intro j x
    rw [norm_mul, norm_mFourier_apply, one_mul, Complex.norm_real, Real.norm_eq_abs,
      poissonPeakSeriesTerm, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ 2 * poissonPeakScale r),
      abs_of_nonneg (pow_nonneg hr0.le _)]
    calc
      2 * poissonPeakScale r * r ^ (j + 1) *
          |DGPS.Examples.PositiveH1.Fourier.cosMode (j + 1) x| ≤
        2 * poissonPeakScale r * r ^ (j + 1) * 1 :=
          mul_le_mul_of_nonneg_left
            (DGPS.Examples.PositiveH1.Fourier.cosMode_abs_le _ _) (by positivity)
      _ = 2 * poissonPeakScale r * r ^ (j + 1) := by ring
  refine hasSum_integral_of_dominated_convergence
    (fun j _ => 2 * poissonPeakScale r * r ^ (j + 1)) ?_ ?_ ?_ ?_ ?_
  · intro j
    exact hint j |>.aestronglyMeasurable
  · intro j
    exact Filter.Eventually.of_forall (hnorm j)
  · exact Filter.Eventually.of_forall (fun _ => hbound)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun x =>
      (Complex.hasSum_ofReal.mpr (poissonPeak_series_tail hr0 hr1 x)).mul_left
        (UnitAddTorus.mFourier (-freqZ k) x))

private noncomputable def poissonPeakCoeffTerm (r : ℝ) (k : ℤ) (j : ℕ) : ℂ :=
  (((2 * poissonPeakScale r * r ^ (j + 1)) / 2 : ℝ) : ℂ) *
    ((if k = ((j + 1 : ℕ) : ℤ) then (1 : ℂ) else 0) +
      (if k = -((j + 1 : ℕ) : ℤ) then (1 : ℂ) else 0))

private theorem poissonPeak_term_coeff_eq {r : ℝ} (k : ℤ) (j : ℕ) :
    ∫ x : Circle, UnitAddTorus.mFourier (-freqZ k) x *
        ((poissonPeakSeriesTerm r x j : ℝ) : ℂ) ∂DGPS.haar 1 =
      poissonPeakCoeffTerm r k j := by
  rw [poissonPeak_term_coeff]
  · have hp : -freqZ k + DGPS.Examples.PositiveH1.Fourier.freq (j + 1) = 0 ↔
        k = ((j + 1 : ℕ) : ℤ) := by
      constructor
      · intro h
        have h0 := congrFun h 0
        have h0' : -k + ((j + 1 : ℕ) : ℤ) = 0 := by
          simpa [freqZ, DGPS.Examples.PositiveH1.Fourier.freq] using h0
        omega
      · intro h
        ext i
        simp [freqZ, DGPS.Examples.PositiveH1.Fourier.freq, h]
    have hn : -freqZ k + -DGPS.Examples.PositiveH1.Fourier.freq (j + 1) = 0 ↔
        k = -((j + 1 : ℕ) : ℤ) := by
      constructor
      · intro h
        have h0 := congrFun h 0
        have h0' : -k - ((j + 1 : ℕ) : ℤ) = 0 := by
          have h0'' : -k + (-1 - (j : ℤ)) = 0 := by
            simpa [freqZ, DGPS.Examples.PositiveH1.Fourier.freq,
              Nat.cast_succ, sub_eq_add_neg] using h0
          omega
        omega
      · intro h
        ext i
        simp [freqZ, DGPS.Examples.PositiveH1.Fourier.freq, h]
    simp [poissonPeakCoeffTerm, hp, hn]

theorem coeff_poissonPeak {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (k : ℤ) :
    coeff1 (poissonPeak r) k =
      (((poissonPeakScale r * r ^ Int.natAbs k : ℝ) : ℂ)) := by
  have hsum := poissonPeak_integral_series hr0 hr1 k
  simp_rw [poissonPeak_term_coeff_eq] at hsum
  have hqcont : Continuous (poissonPeak r) := by
    have hc : Continuous c1 := SharpLSI.FL.Ex.LaneD.cm_cont 1
    have hd : Continuous (fun x : Circle => 1 - 2 * r * c1 x + r ^ 2) := by
      fun_prop
    unfold poissonPeak
    exact continuous_const.div hd (fun x => ne_of_gt (poissonDenominator_pos hr0 hr1 x))
  have hqint : Integrable (poissonPeak r) (DGPS.haar 1) :=
    hqcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hqmint : Integrable (fun x : Circle => poissonPeak r x - poissonPeakScale r)
      (DGPS.haar 1) := by
    apply (hqcont.sub continuous_const).integrable_of_hasCompactSupport
    exact HasCompactSupport.of_compactSpace _
  have hchar := DGPS.Examples.PositiveH1.Fourier.integrable_mFourier (-freqZ k)
  have hsplit : ∫ x : Circle, UnitAddTorus.mFourier (-freqZ k) x *
      ((poissonPeak r x : ℝ) : ℂ) ∂DGPS.haar 1 =
      (∫ x : Circle, UnitAddTorus.mFourier (-freqZ k) x *
        ((poissonPeakScale r : ℝ) : ℂ) ∂DGPS.haar 1) +
      (∫ x : Circle, UnitAddTorus.mFourier (-freqZ k) x *
        ((poissonPeak r x - poissonPeakScale r : ℝ) : ℂ) ∂DGPS.haar 1) := by
    rw [← integral_add (DGPS.integrable_mFourier_mul (integrable_const _) (-freqZ k))
      (DGPS.integrable_mFourier_mul hqmint (-freqZ k))]
    apply integral_congr_ae
    filter_upwards [] with x
    push_cast
    ring
  have hconstant : ∫ x : Circle, UnitAddTorus.mFourier (-freqZ k) x *
      ((poissonPeakScale r : ℝ) : ℂ) ∂DGPS.haar 1 =
      ((poissonPeakScale r : ℝ) : ℂ) * (if k = 0 then 1 else 0) := by
    rw [integral_mul_const, DGPS.Examples.PositiveH1.Fourier.integral_mFourier]
    by_cases hk : k = 0
    · subst k
      have hzero : -freqZ 0 = 0 := by
        ext i
        simp [freqZ]
      rw [ite_eq_left hzero]
      simp
    · have hnonzero : -freqZ k ≠ 0 := by
        intro h
        have h0 := congrFun h 0
        simp [freqZ] at h0
        omega
      rw [ite_eq_right hnonzero]
      simp [hk]
  have hcoeff : coeff1 (poissonPeak r) k =
      ((poissonPeakScale r : ℝ) : ℂ) * (if k = 0 then 1 else 0) +
        ∑' j : ℕ, poissonPeakCoeffTerm r k j := by
    rw [coeff1_eq_fourierCoeff, DGPS.Examples.PositiveH1.Fourier.fourierCoeff_eq_integral,
      hsplit, hconstant, ← hsum.tsum_eq]
  rcases (show k = 0 ∨ 0 < k ∨ k < 0 by omega) with hk | hk | hk
  · subst k
    have hzero : ∀ j : ℕ, poissonPeakCoeffTerm r 0 j = 0 := by
      intro j
      have hpos : ¬ (0 : ℤ) = (j : ℤ) + 1 := by omega
      have hneg : ¬ (0 : ℤ) = -((j : ℤ) + 1) := by omega
      unfold poissonPeakCoeffTerm
      simp only [Nat.cast_add, Nat.cast_one]
      rw [ite_eq_right hpos, ite_eq_right hneg]
      simp
    have htsum : (∑' j : ℕ, poissonPeakCoeffTerm r 0 j) = 0 := by
      simp_rw [hzero]
      simp
    rw [hcoeff, htsum]
    simp
  · let b : ℕ := Int.natAbs k - 1
    have hcast : (Int.natAbs k : ℤ) = k := Int.natAbs_of_nonneg (le_of_lt hk)
    have hnatpos : 0 < Int.natAbs k := by omega
    have hb : b + 1 = Int.natAbs k := by
      dsimp [b]
      omega
    have hindex : ((b + 1 : ℕ) : ℤ) = k := by
      rw [hb]
      exact hcast
    have hzero : ∀ j : ℕ, j ≠ b → poissonPeakCoeffTerm r k j = 0 := by
      intro j hj
      have hpos : k ≠ (j : ℤ) + 1 := by
        intro heq
        apply hj
        have hsum : ((j : ℤ) + 1) = (Int.natAbs k : ℤ) := by
          calc
            (j : ℤ) + 1 = k := heq.symm
            _ = (Int.natAbs k : ℤ) := hcast.symm
        have : j + 1 = Int.natAbs k := by exact_mod_cast hsum
        dsimp [b]
        omega
      have hneg : k ≠ -((j : ℤ) + 1) := by
        intro heq
        have hm : 0 < ((j + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos j
        omega
      unfold poissonPeakCoeffTerm
      simp only [Nat.cast_add, Nat.cast_one]
      rw [ite_eq_right hpos, ite_eq_right hneg]
      simp
    have hsingle : HasSum (fun j : ℕ => poissonPeakCoeffTerm r k j)
        (poissonPeakCoeffTerm r k b) :=
      hasSum_single (f := fun j : ℕ => poissonPeakCoeffTerm r k j) b hzero
    have hat : poissonPeakCoeffTerm r k b =
        ((poissonPeakScale r * r ^ Int.natAbs k : ℝ) : ℂ) := by
      have htrue : k = ((b + 1 : ℕ) : ℤ) := hindex.symm
      have hfalse : k ≠ -((b + 1 : ℕ) : ℤ) := by
        have hm : 0 < ((b + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos b
        omega
      unfold poissonPeakCoeffTerm
      rw [ite_eq_left htrue, ite_eq_right hfalse, hb]
      push_cast
      ring_nf
    calc
      coeff1 (poissonPeak r) k =
          ((poissonPeakScale r : ℝ) : ℂ) * (if k = 0 then 1 else 0) +
            ∑' j : ℕ, poissonPeakCoeffTerm r k j := hcoeff
      _ = ((poissonPeakScale r * r ^ Int.natAbs k : ℝ) : ℂ) := by
        rw [hsum.tsum_eq, hsum.unique hsingle]
        simp [ne_of_gt hk, hat]
  · let b : ℕ := Int.natAbs k - 1
    have hcast : (Int.natAbs k : ℤ) = -k := Int.ofNat_natAbs_of_nonpos (le_of_lt hk)
    have hnatpos : 0 < Int.natAbs k := by omega
    have hb : b + 1 = Int.natAbs k := by
      dsimp [b]
      omega
    have hindex : ((b + 1 : ℕ) : ℤ) = -k := by
      rw [hb]
      exact hcast
    have hzero : ∀ j : ℕ, j ≠ b → poissonPeakCoeffTerm r k j = 0 := by
      intro j hj
      have hpos : k ≠ (j : ℤ) + 1 := by
        intro heq
        have hm : 0 < ((j + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos j
        omega
      have hneg : k ≠ -((j : ℤ) + 1) := by
        intro heq
        apply hj
        have hsum : ((j : ℤ) + 1) = (Int.natAbs k : ℤ) := by
          calc
            (j : ℤ) + 1 = -k := by omega
            _ = (Int.natAbs k : ℤ) := hcast.symm
        have : j + 1 = Int.natAbs k := by exact_mod_cast hsum
        dsimp [b]
        omega
      unfold poissonPeakCoeffTerm
      simp only [Nat.cast_add, Nat.cast_one]
      rw [ite_eq_right hpos, ite_eq_right hneg]
      simp
    have hsingle : HasSum (fun j : ℕ => poissonPeakCoeffTerm r k j)
        (poissonPeakCoeffTerm r k b) :=
      hasSum_single (f := fun j : ℕ => poissonPeakCoeffTerm r k j) b hzero
    have hat : poissonPeakCoeffTerm r k b =
        ((poissonPeakScale r * r ^ Int.natAbs k : ℝ) : ℂ) := by
      have hfalse : k ≠ ((b + 1 : ℕ) : ℤ) := by
        have hm : 0 < ((b + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos b
        omega
      have htrue : k = -((b + 1 : ℕ) : ℤ) := by
        rw [hindex]
        ring
      unfold poissonPeakCoeffTerm
      rw [ite_eq_right hfalse, ite_eq_left htrue, hb]
      push_cast
      ring_nf
    calc
      coeff1 (poissonPeak r) k =
          ((poissonPeakScale r : ℝ) : ℂ) * (if k = 0 then 1 else 0) +
            ∑' j : ℕ, poissonPeakCoeffTerm r k j := hcoeff
      _ = ((poissonPeakScale r * r ^ Int.natAbs k : ℝ) : ℂ) := by
        rw [hsum.tsum_eq, hsum.unique hsingle]
        simp [ne_of_lt hk, hat]

/-! ### Fourier positivity, mass, and translations -/

/-- Every Fourier coefficient of the normalized Poisson peak is a positive real. -/
theorem coeff_poissonPeak_pos {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (k : ℤ) :
    (coeff1 (poissonPeak r) k).im = 0 ∧ 0 < (coeff1 (poissonPeak r) k).re := by
  rw [coeff_poissonPeak hr0 hr1 k]
  constructor
  · rfl
  · change 0 < poissonPeakScale r * r ^ Int.natAbs k
    exact mul_pos (by
      unfold poissonPeakScale
      exact div_pos (sub_pos.mpr hr1) (by linarith)) (pow_pos hr0 _)

theorem poissonPeak_has_pos_nonzero_fourier {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    HasPosNonzeroFourier (poissonPeak r) := by
  intro k _
  exact coeff_poissonPeak_pos hr0 hr1 k

/-- Haar mass of the normalized Poisson peak. -/
theorem integral_poissonPeak {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∫ x : Circle, poissonPeak r x ∂DGPS.haar 1 = poissonPeakScale r := by
  have hz : coeff1 (poissonPeak r) 0 =
      ((∫ x : Circle, poissonPeak r x ∂DGPS.haar 1 : ℝ) : ℂ) := by
    change DGPS.fourierCoeff (poissonPeak r) (0 : Fin 1 → ℤ) = _
    rw [DGPS.Examples.PositiveH1.Fourier.fourierCoeff_eq_integral]
    simp only [neg_zero, UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, one_mul]
    exact integral_complex_ofReal
  exact Complex.ofReal_injective (hz.symm.trans (by simpa using coeff_poissonPeak hr0 hr1 0))

/-- Translation by `a` multiplies the Fourier coefficient by the corresponding character. -/
theorem coeff_poissonPeak_translate {r : ℝ} (_hr0 : 0 < r) (_hr1 : r < 1)
    (a : Circle) (k : ℤ) :
    coeff1 (fun x => poissonPeak r (x - a)) k =
      UnitAddTorus.mFourier (-freqZ k) a * coeff1 (poissonPeak r) k := by
  rw [coeff1_eq_fourierCoeff,
    DGPS.Examples.PositiveH1.Fourier.fourierCoeff_eq_integral]
  have hshift :
      ∫ x : Circle, UnitAddTorus.mFourier (-freqZ k) x *
          ((poissonPeak r (x - a) : ℝ) : ℂ) ∂DGPS.haar 1 =
        ∫ y : Circle, UnitAddTorus.mFourier (-freqZ k) (y + a) *
          ((poissonPeak r y : ℝ) : ℂ) ∂DGPS.haar 1 := by
    have h := integral_sub_right_eq_self (μ := DGPS.haar 1)
      (fun y : Circle => UnitAddTorus.mFourier (-freqZ k) (y + a) *
        ((poissonPeak r y : ℝ) : ℂ)) a
    calc
      _ = ∫ x : Circle,
          UnitAddTorus.mFourier (-freqZ k) ((x - a) + a) *
            ((poissonPeak r (x - a) : ℝ) : ℂ) ∂DGPS.haar 1 := by
          congr 1
          funext x
          simp
      _ = _ := h
  rw [hshift]
  calc
    (∫ y : Circle, UnitAddTorus.mFourier (-freqZ k) (y + a) *
        ((poissonPeak r y : ℝ) : ℂ) ∂DGPS.haar 1) =
      ∫ y : Circle, UnitAddTorus.mFourier (-freqZ k) a *
        (UnitAddTorus.mFourier (-freqZ k) y * ((poissonPeak r y : ℝ) : ℂ))
          ∂DGPS.haar 1 := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [DGPS.mFourier_add_pt]
        ring
    _ = UnitAddTorus.mFourier (-freqZ k) a *
        ∫ y : Circle, UnitAddTorus.mFourier (-freqZ k) y *
          ((poissonPeak r y : ℝ) : ℂ) ∂DGPS.haar 1 := by
        rw [← integral_const_mul]
    _ = UnitAddTorus.mFourier (-freqZ k) a * coeff1 (poissonPeak r) k := by
        rw [coeff1_eq_fourierCoeff,
          DGPS.Examples.PositiveH1.Fourier.fourierCoeff_eq_integral]

/-- The quadratic upper bound for the loss of the cosine near its maximum. -/
theorem one_sub_cos_two_pi_mul_le (t : ℝ) :
    1 - Real.cos (2 * Real.pi * t) ≤ 2 * Real.pi ^ 2 * t ^ 2 := by
  have hcos : 1 - Real.cos (2 * Real.pi * t) = 2 * Real.sin (Real.pi * t) ^ 2 := by
    rw [show 2 * Real.pi * t = 2 * (Real.pi * t) by ring, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * t)]
  rw [hcos]
  have hsin : Real.sin (Real.pi * t) ^ 2 ≤ (Real.pi * t) ^ 2 := Real.sin_sq_le_sq
  nlinarith [hsin]

/-- The matching quadratic lower bound on a half-period representative. -/
theorem one_sub_cos_two_pi_mul_ge {t : ℝ} (ht : |t| ≤ 1 / 2) :
    8 * t ^ 2 ≤ 1 - Real.cos (2 * Real.pi * t) := by
  have harg : |2 * Real.pi * t| ≤ Real.pi := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos Real.pi_pos]
    calc
      2 * Real.pi * |t| ≤ 2 * Real.pi * (1 / 2) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = Real.pi := by ring
  have h := Real.cos_le_one_sub_mul_cos_sq harg
  have hscale : 2 / Real.pi ^ 2 * (2 * Real.pi * t) ^ 2 = 8 * t ^ 2 := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [hscale] at h
  nlinarith

private theorem exists_small_circle_rep (x : Circle) :
    ∃ t : ℝ, |t| ≤ 1 / 2 ∧ x = torusPoint t ∧ torusDist x 0 = |t| := by
  let s := SharpLSI.secT x 0
  have hs : s ∈ Set.Ioc (0 : ℝ) 1 := by
    dsimp [s, SharpLSI.secT]
    simpa using (AddCircle.measurableEquivIoc 1 0 (x 0)).property
  have hsec : SharpLSI.secT x = fun _ : Fin 1 => s := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have hsx : torusPoint s = x := by
    change DGPS.torusLift (fun _ : Fin 1 => s) = x
    rw [← hsec]
    exact SharpLSI.liftT_secT x
  have hperiod : torusPoint (s - 1) = torusPoint s := by
    have hper : ((s - 1 : ℝ) : UnitAddCircle) = (s : UnitAddCircle) := by
      calc
        ((s - 1 : ℝ) : UnitAddCircle) = (((s - 1) + 1 : ℝ) : UnitAddCircle) :=
          (AddCircle.coe_add_period (p := 1) (x := s - 1)).symm
        _ = (s : UnitAddCircle) := by congr 1; ring
    ext i
    exact hper
  let t : ℝ := if s ≤ 1 / 2 then s else s - 1
  have htlo : -(1 / 2) ≤ t := by
    dsimp [t]
    split_ifs <;> norm_num at * <;> linarith [hs.1, hs.2]
  have hthi : t ≤ 1 / 2 := by
    dsimp [t]
    split_ifs <;> norm_num at * <;> linarith [hs.1, hs.2]
  have ht : |t| ≤ 1 / 2 := abs_le.mpr ⟨htlo, hthi⟩
  have hxt : torusPoint t = x := by
    dsimp [t]
    split_ifs with h
    · exact hsx
    · exact hperiod.trans hsx
  have hzero : (0 : Circle) = DGPS.torusLift (fun _ : Fin 1 => (0 : ℝ)) := by
    ext i
    simp [DGPS.torusLift, SharpLSI.liftT]
  have hdist : torusDist (torusPoint t) 0 = |t| := by
    rw [hzero, torusDist_liftT_eq (by intro j; simpa using ht)]
    have hsum : (∑ j : Fin 1, (t - 0) ^ 2) = t ^ 2 := by simp
    rw [hsum, Real.sqrt_sq_eq_abs]
  exact ⟨t, ht, hxt.symm, by rw [← hxt]; exact hdist⟩

/-- A Poisson peak stays uniformly positive within its natural scale of the center.

This holds for every `0 < r < 1`; no lower bound on `r` is needed. -/
theorem poissonPeak_near_peak_lower {r eps : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (heps : eps = 1 - r) (x : Circle) (hdist : dist x 0 ≤ eps) :
    1 / 65 ≤ poissonPeak r x := by
  have heps0 : 0 < eps := by rw [heps]; exact sub_pos.mpr hr1
  obtain ⟨t, ht, hxt, htorus⟩ := exists_small_circle_rep x
  have htorus_le : torusDist x 0 ≤ eps := by
    calc
      torusDist x 0 ≤ dist x 0 := by
        simpa using (torusDist_comparison x 0).2
      _ ≤ eps := hdist
  have hteps : |t| ≤ eps := by rw [← htorus]; exact htorus_le
  have htSq : t ^ 2 ≤ eps ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hteps)
      (add_nonneg (abs_nonneg t) (le_of_lt heps0))
    nlinarith [sq_abs t]
  have hcos : c1 x = Real.cos (2 * Real.pi * t) := by
    rw [hxt]
    exact c1_torusPoint t
  have hden : 1 - 2 * r * c1 x + r ^ 2 ≤ 65 * eps ^ 2 := by
    rw [poissonDenominator_decomp, hcos]
    have hterm : 2 * r * (1 - Real.cos (2 * Real.pi * t)) ≤ 4 * Real.pi ^ 2 * eps ^ 2 := by
      have hfactor : 2 * Real.pi ^ 2 * t ^ 2 ≤ 2 * Real.pi ^ 2 * eps ^ 2 :=
        mul_le_mul_of_nonneg_left htSq (by positivity)
      calc
        2 * r * (1 - Real.cos (2 * Real.pi * t)) ≤
            2 * r * (2 * Real.pi ^ 2 * t ^ 2) :=
          mul_le_mul_of_nonneg_left (one_sub_cos_two_pi_mul_le t) (by positivity)
        _ ≤ 2 * r * (2 * Real.pi ^ 2 * eps ^ 2) :=
          mul_le_mul_of_nonneg_left hfactor (by positivity)
        _ ≤ 2 * (2 * Real.pi ^ 2 * eps ^ 2) := by
          have hmul := mul_le_mul_of_nonneg_right (le_of_lt hr1)
            (show 0 ≤ 2 * Real.pi ^ 2 * eps ^ 2 by positivity)
          nlinarith [hmul]
        _ = 4 * Real.pi ^ 2 * eps ^ 2 := by ring
    calc
      (1 - r) ^ 2 + 2 * r * (1 - Real.cos (2 * Real.pi * t)) ≤
          eps ^ 2 + 4 * Real.pi ^ 2 * eps ^ 2 := by
        rw [← heps]
        nlinarith [hterm]
      _ ≤ 65 * eps ^ 2 := by
        have hpi : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
        nlinarith [sq_nonneg eps]
  have hq : poissonPeak r x = eps ^ 2 / (1 - 2 * r * c1 x + r ^ 2) := by
    rw [poissonPeak, ← heps]
  rw [hq, le_div_iff₀ (poissonDenominator_pos hr0 hr1 x)]
  nlinarith [hden]

/-- Away from the center, the Poisson peak has a quadratic tail bound. -/
theorem poissonPeak_away_upper {r eps d : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (heps : eps = 1 - r) (hepshalf : eps ≤ 1 / 2) (hd0 : 0 < d) (x : Circle)
    (hdist : d ≤ dist x 0) :
    poissonPeak r x ≤ eps ^ 2 / (8 * d ^ 2) := by
  obtain ⟨t, ht, hxt, htorus⟩ := exists_small_circle_rep x
  have hdist_torus : d ≤ torusDist x 0 :=
    hdist.trans (torusDist_comparison x 0).1
  have hdt : d ≤ |t| := by rw [← htorus]; exact hdist_torus
  have htSq : d ^ 2 ≤ t ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hdt) (add_nonneg (abs_nonneg t) hd0.le)
    nlinarith [sq_abs t]
  have hcos : c1 x = Real.cos (2 * Real.pi * t) := by
    rw [hxt]
    exact c1_torusPoint t
  have hcosLower := one_sub_cos_two_pi_mul_ge ht
  have hB : 0 ≤ 1 - Real.cos (2 * Real.pi * t) := by nlinarith [hcosLower]
  have h2r : 1 ≤ 2 * r := by linarith
  have hden : 8 * d ^ 2 ≤ 1 - 2 * r * c1 x + r ^ 2 := by
    rw [poissonDenominator_decomp, hcos]
    calc
      8 * d ^ 2 ≤ 8 * t ^ 2 := by nlinarith [htSq]
      _ ≤ 1 - Real.cos (2 * Real.pi * t) := hcosLower
      _ ≤ 2 * r * (1 - Real.cos (2 * Real.pi * t)) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr h2r) hB]
      _ ≤ (1 - r) ^ 2 + 2 * r * (1 - Real.cos (2 * Real.pi * t)) := by
        nlinarith [sq_nonneg (1 - r)]
  have hq : poissonPeak r x = eps ^ 2 / (1 - 2 * r * c1 x + r ^ 2) := by
    rw [poissonPeak, ← heps]
  rw [hq, div_le_div_iff₀ (poissonDenominator_pos hr0 hr1 x)
    (by positivity : 0 < 8 * d ^ 2)]
  exact mul_le_mul_of_nonneg_left hden (sq_nonneg eps)

end DGPS.SingularCounterexample
