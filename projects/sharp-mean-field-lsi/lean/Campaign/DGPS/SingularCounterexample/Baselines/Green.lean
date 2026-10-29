import DGPS.SingularCounterexample.Interfaces
import DGPS.Examples.PositiveH1.Nonlinear
import Mathlib.NumberTheory.ZetaValues

/-!
# The zero-diagonal periodic Green kernel

We use the Bernoulli polynomial representative, expressed in terms of distance from zero.
On `[0,1]` it is `(t²-t)/2`, so it is the required `(t²-t+1/6)/2` shifted by its value at zero.
The Fourier calculation reuses Mathlib's periodized Bernoulli coefficient formula.
Perturbed-kernel positivity and collision statements are specialized in `Main.lean`, preserving
the import direction from the baseline to the headline theorem.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace DGPS.SingularCounterexample

/-- SLC-G003: the periodic Green kernel with its value at zero subtracted. -/
noncomputable def greenKernel (x : Circle) : ℝ :=
  (‖x 0‖ ^ 2 - ‖x 0‖) / 2

@[simp] theorem greenKernel_zero : greenKernel 0 = 0 := by
  simp [greenKernel]

theorem greenKernel_even (x : Circle) : greenKernel (-x) = greenKernel x := by
  simp [greenKernel]

theorem greenKernel_continuous : Continuous greenKernel := by
  have h : Continuous (fun x : Circle => ‖x 0‖) := (continuous_apply 0).norm
  exact ((h.pow 2).sub h).div_const 2

theorem greenKernel_measurable : Measurable greenKernel := greenKernel_continuous.measurable

theorem greenKernel_bounds (x : Circle) : -(1 / 8 : ℝ) ≤ greenKernel x ∧ greenKernel x ≤ 0 := by
  have h0 : 0 ≤ ‖x 0‖ := norm_nonneg _
  have h1 : ‖x 0‖ ≤ 1 / 2 := by
    simpa using AddCircle.norm_le_half_period (p := (1 : ℝ)) (x := x 0) one_ne_zero
  unfold greenKernel
  constructor
  · nlinarith [sq_nonneg (‖x 0‖ - 1 / 2)]
  · nlinarith [mul_nonneg h0 (show 0 ≤ 1 - ‖x 0‖ by linarith)]

theorem greenKernel_abs_le (x : Circle) : |greenKernel x| ≤ 1 / 8 := by
  rw [abs_le]
  exact ⟨(greenKernel_bounds x).1, (greenKernel_bounds x).2.trans (by norm_num)⟩

/-- The exact shifted Bernoulli representative, including both endpoints. -/
theorem greenKernel_torusPoint_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    greenKernel (torusPoint t) = (t ^ 2 - t) / 2 := by
  change (‖(t : UnitAddCircle)‖ ^ 2 - ‖(t : UnitAddCircle)‖) / 2 = _
  by_cases h : t ≤ 1 / 2
  · have hn : ‖(t : UnitAddCircle)‖ = t := by
      rw [(AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).mpr
        (by simpa [abs_of_nonneg ht.1] using h), abs_of_nonneg ht.1]
    rw [hn]
  · have he : (t : UnitAddCircle) = ((t - 1 : ℝ) : UnitAddCircle) := by
      simp [AddCircle.coe_period]
    have hn : ‖(t : UnitAddCircle)‖ = 1 - t := by
      rw [he, (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).mpr
        (by rw [abs_of_nonpos (by linarith [ht.2] : t - 1 ≤ 0)]; norm_num; linarith),
        abs_of_nonpos (by linarith [ht.2] : t - 1 ≤ 0)]
      ring
    rw [hn]
    ring

theorem greenKernel_torusPoint_shifted_bernoulli {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    greenKernel (torusPoint t) = (t ^ 2 - t + 1 / 6) / 2 - (1 / 6) / 2 := by
  rw [greenKernel_torusPoint_Icc ht]
  ring

theorem greenKernel_eq_periodizedBernoulli (x : Circle) :
    greenKernel x = (periodizedBernoulli 2 (x 0) - 1 / 6) / 2 := by
  let t : ℝ := AddCircle.equivIco 1 0 (x 0)
  have ht : t ∈ Ico (0 : ℝ) 1 := by
    simpa only [t, zero_add] using (AddCircle.equivIco 1 0 (x 0)).property
  have hp : torusPoint t = x := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact AddCircle.coe_equivIco
  rw [← hp, greenKernel_torusPoint_Icc ⟨ht.1, ht.2.le⟩]
  change (t ^ 2 - t) / 2 = (AddCircle.liftIco 1 0 (bernoulliFun 2) (t : UnitAddCircle) - 1 / 6) / 2
  rw [AddCircle.liftIco_coe_apply (by simpa using ht), bernoulliFun_two]
  norm_num

/-- A Lipschitz bound in the Euclidean circle quotient metric. -/
theorem greenKernel_lipschitz : TorusLipschitzWith (1 / 2) greenKernel := by
  intro x y
  have hx : ‖x 0‖ ≤ 1 / 2 := by
    simpa using AddCircle.norm_le_half_period (p := (1 : ℝ)) (x := x 0) one_ne_zero
  have hy : ‖y 0‖ ≤ 1 / 2 := by
    simpa using AddCircle.norm_le_half_period (p := (1 : ℝ)) (x := y 0) one_ne_zero
  have hsum : |‖x 0‖ + ‖y 0‖ - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [norm_nonneg (x 0), norm_nonneg (y 0)]
  have hform : greenKernel x - greenKernel y =
      (‖x 0‖ - ‖y 0‖) * (‖x 0‖ + ‖y 0‖ - 1) / 2 := by
    unfold greenKernel
    ring
  rw [hform, abs_div, abs_mul]
  calc
    |‖x 0‖ - ‖y 0‖| * |‖x 0‖ + ‖y 0‖ - 1| / |(2 : ℝ)|
        ≤ |‖x 0‖ - ‖y 0‖| / 2 := by
          rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact div_le_div_of_nonneg_right
            (mul_le_of_le_one_right (abs_nonneg _) hsum) (by norm_num)
    _ ≤ ‖x 0 - y 0‖ / 2 := by
      gcongr
      exact abs_norm_sub_norm_le _ _
    _ = (1 / 2) * torusDist x y := by
      rw [torusDist_one]
      ring

private theorem greenKernel_contDiffAt_fundamental {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ContDiffAt ℝ ∞ (fun s : ℝ => greenKernel (torusPoint s)) t := by
  have hp : ContDiff ℝ ∞ (fun s : ℝ => (s ^ 2 - s) / 2) := by fun_prop
  apply hp.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht0 ht1] with s hs
  exact greenKernel_torusPoint_Icc ⟨hs.1.le, hs.2.le⟩

/-- Smoothness of the periodic real lift away from the collision class. -/
theorem greenKernel_smooth_off_collision :
    ContDiffOn ℝ ∞ (fun t : ℝ => greenKernel (torusPoint t))
      {t : ℝ | torusPoint t ≠ (0 : Circle)} := by
  intro t ht
  let u := SharpLSI.secT (torusPoint t) 0
  have hu : u ∈ Ioc (0 : ℝ) 1 := by
    simpa only [u, SharpLSI.secT, zero_add] using
      ((AddCircle.measurableEquivIoc 1 0) ((torusPoint t) 0)).property
  have hup : torusPoint u = torusPoint t :=
    (Examples.PositiveH1.Nonlinear.lift1_coord (SharpLSI.secT (torusPoint t))).symm.trans
      (SharpLSI.liftT_secT (torusPoint t))
  have hu1 : u < 1 := by
    refine lt_of_le_of_ne hu.2 ?_
    intro heq
    have hpoint1 : torusPoint 1 = (0 : Circle) := by
      funext i
      change ((1 : ℝ) : UnitAddCircle) = 0
      exact AddCircle.coe_period (p := (1 : ℝ))
    exact ht (hup.symm.trans (by simpa only [heq] using hpoint1))
  obtain ⟨k, hk⟩ := Examples.PositiveH1.Nonlinear.lift1_eq_iff hup.symm
  have hperiod : Function.Periodic torusPoint 1 := Examples.PositiveH1.Nonlinear.lift1_add_one
  have hshift (s : ℝ) : torusPoint (s - (k : ℝ)) = torusPoint s := by
    simpa only [Int.cast_neg, mul_one, sub_eq_add_neg] using hperiod.int_mul (-k) s
  have hbase : ContDiffAt ℝ ∞ (fun s : ℝ => greenKernel (torusPoint s)) (t - (k : ℝ)) := by
    have htk : t - (k : ℝ) = u := by linarith only [hk]
    rw [htk]
    exact greenKernel_contDiffAt_fundamental hu.1 hu1
  have hc := hbase.comp t (contDiffAt_id.sub contDiffAt_const)
  have hfun : (fun s : ℝ => greenKernel (torusPoint (s - (k : ℝ)))) =
      fun s : ℝ => greenKernel (torusPoint s) := by
    funext s
    rw [hshift]
  change ContDiffAt ℝ ∞ (fun s : ℝ => greenKernel (torusPoint (s - (k : ℝ)))) t at hc
  rw [hfun] at hc
  exact hc.contDiffWithinAt

private theorem coeff1_coordinate (f : UnitAddCircle → ℝ) (hf : Continuous f) (n : ℤ) :
    coeff1 (fun x : Circle => f (x 0)) n = _root_.fourierCoeff (Complex.ofReal ∘ f) n := by
  have hfreq (x : Circle) : UnitAddTorus.mFourier (-freqZ n) x = fourier (-n) (x 0) := by
    simp [UnitAddTorus.mFourier, freqZ]
  rw [coeff1_eq_fourierCoeff, Examples.PositiveH1.Fourier.fourierCoeff_eq_integral]
  simp_rw [hfreq]
  rw [DGPS.haar_eq_pi_haarAddCircle]
  simpa only [_root_.fourierCoeff, Function.comp_apply, smul_eq_mul] using
    (integral_comp_eval (μ := fun _ : Fin 1 => (AddCircle.haarAddCircle : Measure UnitAddCircle))
      (i := 0) (f := fun x : UnitAddCircle => fourier (-n) x * (f x : ℂ))
      (((map_continuous (fourier (-n))).mul (Complex.continuous_ofReal.comp hf)).aestronglyMeasurable))

private theorem coeff1_bernoulli_green (n : ℤ) (hn : n ≠ 0) :
    coeff1 (fun x : Circle => (periodizedBernoulli 2 (x 0) - 1 / 6) / 2) n =
      (((1 / (4 * Real.pi ^ 2 * (n : ℝ) ^ 2) : ℝ)) : ℂ) := by
  rw [coeff1_coordinate (fun y : UnitAddCircle => (periodizedBernoulli 2 y - 1 / 6) / 2)
    (((periodizedBernoulli.continuous (by norm_num : 2 ≠ 1)).sub
      (continuous_const : Continuous (fun _ : UnitAddCircle => (1 / 6 : ℝ)))).div_const 2) n]
  have hb : Integrable (fun x : UnitAddCircle => (periodizedBernoulli 2 x : ℂ)) AddCircle.haarAddCircle :=
    (Complex.continuous_ofReal.comp (periodizedBernoulli.continuous (by norm_num : 2 ≠ 1))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfour : Integrable (fun x : UnitAddCircle => fourier (-n) x) AddCircle.haarAddCircle :=
    (map_continuous (fourier (-n))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ x : UnitAddCircle, fourier (-n) x * (((periodizedBernoulli 2 x - 1/6)/2 : ℝ) : ℂ)
      ∂AddCircle.haarAddCircle) = _
  have hsplit : (fun x : UnitAddCircle => fourier (-n) x * (((periodizedBernoulli 2 x - 1/6)/2 : ℝ) : ℂ)) =
      fun x => (fourier (-n) x * (periodizedBernoulli 2 x : ℂ) - fourier (-n) x / 6) / 2 := by
    funext x
    push_cast
    ring
  have hbf : Integrable (fun x : UnitAddCircle => fourier (-n) x * (periodizedBernoulli 2 x : ℂ)) AddCircle.haarAddCircle := by
    simpa only [smul_eq_mul] using hb.fourier_smul (-n)
  rw [hsplit, integral_div, integral_sub hbf (hfour.div_const 6), integral_div]
  have hi : (∫ x : UnitAddCircle, fourier (-n) x ∂AddCircle.haarAddCircle) = 0 := by
    have h := congrFun (fourierCoeff_fourier (T := (1:ℝ)) 0) n
    simpa [_root_.fourierCoeff, hn, Pi.single_apply, fourier_zero] using h
  have hc := fourierCoeff_bernoulli_eq (by norm_num : 2 ≠ 0) n
  change (∫ x : UnitAddCircle, fourier (-n) x * (periodizedBernoulli 2 x : ℂ) ∂AddCircle.haarAddCircle) = _ at hc
  rw [hc, hi]
  push_cast
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat, mul_one, zero_div, sub_zero]
  simp only [mul_pow, Complex.I_sq]
  ring

/-- SLC-G005: the nonzero coefficients use the frozen unit-circle Fourier normalization. -/
theorem coeff1_greenKernel (n : ℤ) (hn : n ≠ 0) :
    coeff1 greenKernel n = (((1 / (4 * Real.pi ^ 2 * (n : ℝ) ^ 2) : ℝ)) : ℂ) := by
  have hfun : greenKernel =
      (fun x : Circle => (periodizedBernoulli 2 (x 0) - 1 / 6) / 2) :=
    funext greenKernel_eq_periodizedBernoulli
  rw [hfun]
  exact coeff1_bernoulli_green n hn

theorem greenKernel_fourier_pos : HasPosNonzeroFourier greenKernel := by
  intro n hn
  rw [coeff1_greenKernel n hn]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  constructor
  · rfl
  · change 0 < 1 / (4 * Real.pi ^ 2 * (n : ℝ) ^ 2)
    positivity

/-- SLC-G006: the exact periodic Green specialization of the generic baseline interface. -/
noncomputable def greenBaseline : BaselineKernel where
  g := greenKernel
  measurable_g := greenKernel_measurable
  bounded_g := ⟨1 / 8, by norm_num, greenKernel_abs_le⟩
  even_g := greenKernel_even
  zero_g := greenKernel_zero
  fourier_nonneg := fun n hn =>
    ⟨(greenKernel_fourier_pos n hn).1, (greenKernel_fourier_pos n hn).2.le⟩

end DGPS.SingularCounterexample
