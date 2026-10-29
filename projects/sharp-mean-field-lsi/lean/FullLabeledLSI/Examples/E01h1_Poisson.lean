import FullLabeledLSI.Examples.E01h0_Defs
import FullLabeledLSI.Examples.E01g0_Classify

/-!
# Lane D, Task B1: the Poisson-type kernel as an explicit cosine series

Statement skeleton (to be proved).  `r = 1/100`, `C = poissonKernel`,
`C(x) = ∑_{j ≥ 1} 32 r^j cos(2π (2j) x)`.
-/

open MeasureTheory Complex UnitAddTorus Filter Topology
open scoped Real ComplexConjugate ContDiff ENNReal

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

/-! ### Helper lemmas -/


theorem fourier_two_pow (m : ℕ) (y : UnitAddCircle) :
    fourier (2 * (m : ℤ)) y = (fourier 2 y) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have : (2 * ((m + 1 : ℕ) : ℤ)) = 2 * (m : ℤ) + 2 := by push_cast; ring
    rw [this, fourier_add, ih, pow_succ]

theorem poisson_denom_pos (c : ℝ) (hc : |c| ≤ 1) : 0 < 1 - 2 * (1 / 100 : ℝ) * c + (1 / 100 : ℝ) ^ 2 := by
  have := abs_le.mp hc
  nlinarith [this.1, this.2]


theorem cm_lift (n : ℤ) (t : ℝ) : cm n (liftT fun _ => t) = Real.cos (2 * π * n * t) := by
  unfold cm liftT
  show (fourier n ((t : ℝ) : UnitAddCircle)).re = _
  rw [fourier_coe_apply]
  have : (2 * π * Complex.I * n * t / (1:ℝ) : ℂ) = ((2 * π * n * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

theorem sm_lift (n : ℤ) (t : ℝ) : sm n (liftT fun _ => t) = Real.sin (2 * π * n * t) := by
  unfold sm liftT
  show (fourier n ((t : ℝ) : UnitAddCircle)).im = _
  rw [fourier_coe_apply]
  have : (2 * π * Complex.I * n * t / (1:ℝ) : ℂ) = ((2 * π * n * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_im]

theorem lift_rep (x : Torus 1) : liftT (fun _ : Fin 1 => rep x) = x := by
  funext i
  have : i = 0 := Subsingleton.elim _ _
  subst this
  exact (QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℝ)) (x 0)).choose_spec

theorem cm_rep (n : ℤ) (x : Torus 1) : cm n x = Real.cos (2 * π * n * rep x) := by
  rw [← cm_lift, lift_rep]

theorem sm_rep (n : ℤ) (x : Torus 1) : sm n x = Real.sin (2 * π * n * rep x) := by
  rw [← sm_lift, lift_rep]

theorem cm_abs_le (n : ℤ) (x : Torus 1) : |cm n x| ≤ 1 := by
  have := Complex.abs_re_le_norm (fourier n (x 0))
  simpa [cm] using this

theorem sm_abs_le (n : ℤ) (x : Torus 1) : |sm n x| ≤ 1 := by
  have := Complex.abs_im_le_norm (fourier n (x 0))
  simpa [sm] using this

theorem cm_neg (n : ℤ) (x : Torus 1) : cm n (-x) = cm n x := by
  rw [← lift_rep x]
  have : -liftT (fun _ : Fin 1 => rep x) = liftT (fun _ : Fin 1 => -rep x) := by
    funext i; simp [liftT]
  rw [this, cm_lift, cm_lift]
  rw [show 2 * π * (n : ℝ) * -rep x = -(2 * π * (n : ℝ) * rep x) by ring, Real.cos_neg]

theorem lift_eq (v : Fin 1 → ℝ) : liftT v = liftT (fun _ : Fin 1 => v 0) := by
  funext i
  have : i = 0 := Subsingleton.elim _ _
  subst this; rfl

theorem int_fourier (a : ℤ) : ∫ x : Torus 1, fourier a (x 0) = if a = 0 then 1 else 0 := by
  have h := integral_mFourier' (K1 a)
  simp only [mFourier_K1] at h
  rw [h]
  by_cases ha : a = 0
  · subst ha; simp [K1_zero]
  · simp [ha, K1_ne_zero ha]

theorem four_cont (a : ℤ) : Continuous fun x : Torus 1 => fourier a (x 0) :=
  (fourier a).continuous.comp (continuous_apply 0)

theorem cm_cont (a : ℤ) : Continuous fun x : Torus 1 => cm a x :=
  Complex.continuous_re.comp (four_cont a)

theorem int_fourier_mul_cm (n k : ℤ) :
    ∫ x : Torus 1, fourier (-n) (x 0) * ((cm k x : ℝ) : ℂ) =
      ((if k - n = 0 then 1 else 0) + (if -k - n = 0 then 1 else 0)) / 2 := by
  have e : ∀ x : Torus 1, fourier (-n) (x 0) * ((cm k x : ℝ) : ℂ) =
      (fourier (k + -n) (x 0) + fourier (-k + -n) (x 0)) / 2 := by
    intro x
    rw [cm, Complex.re_eq_add_conj, ← fourier_neg, fourier_add, fourier_add]
    ring
  simp_rw [e]
  rw [integral_div, integral_add, int_fourier, int_fourier]
  · simp only [← sub_eq_add_neg]
  · exact (four_cont _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (four_cont _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)


/-! ### Helper lemmas, part 2 -/

theorem poisson_series_aux (x : Torus 1) :
    HasSum (fun j : ℕ => 32 * (1 / 100 : ℝ) ^ (j + 1) * cm (2 * ((j : ℤ) + 1)) x) (poissonKernel x) := by
  set z : ℂ := fourier 2 (x 0) with hz
  have hzn : ‖z‖ = 1 := by simp [hz]
  set w : ℂ := ((1 / 100 : ℝ) : ℂ) * z with hw
  have hwn : ‖w‖ < 1 := by
    rw [hw, norm_mul, hzn]; simp [Complex.norm_real]; norm_num
  have h1 := (hasSum_geometric_of_norm_lt_one hwn).mul_left w
  have h2 := (h1.mul_left (32 : ℂ))
  have h3 := Complex.hasSum_re h2
  have hterm : ∀ j : ℕ, (32 * (w * w ^ j)).re = 32 * (1 / 100 : ℝ) ^ (j + 1) * cm (2 * ((j : ℤ) + 1)) x := by
    intro j
    have e : (2 * ((j : ℤ) + 1)) = 2 * ((j + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [cm, e, fourier_two_pow, ← hz, ← pow_succ', hw, mul_pow, ← Complex.ofReal_pow]
    have : (32 : ℂ) * (((1 / 100 : ℝ) ^ (j + 1) : ℝ) * z ^ (j + 1)) =
      ((32 * (1 / 100 : ℝ) ^ (j + 1) : ℝ) : ℂ) * z ^ (j + 1) := by push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  simp_rw [hterm] at h3
  convert h3 using 1
  -- value
  have hre : z.re ^ 2 + z.im ^ 2 = 1 := by
    have := Complex.sq_norm z
    rw [hzn, Complex.normSq_apply] at this
    nlinarith
  have hc : cosMode 2 x = z.re := rfl
  have hD := poisson_denom_pos z.re (by
    have := Complex.abs_re_le_norm z; rw [hzn] at this; exact this)
  unfold poissonKernel
  rw [hc]
  have hne : (1 - 2 * (1 / 100 : ℝ) * z.re + (1 / 100 : ℝ) ^ 2) ≠ 0 := hD.ne'
  have hval : (32 * (w * (1 - w)⁻¹)).re = 32 * ((w * (1 - w)⁻¹).re) := by
    simp
  rw [hval, Complex.mul_re, Complex.inv_re, Complex.inv_im]
  simp only [hw, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
  simp only [zero_mul, sub_zero, zero_sub, neg_neg, add_zero, neg_mul_neg]
  have hN : (1 - 1 / 100 * z.re) * (1 - 1 / 100 * z.re) + 1 / 100 * z.im * (1 / 100 * z.im)
     = 1 - 2 * (1 / 100 : ℝ) * z.re + (1 / 100 : ℝ) ^ 2 := by nlinarith [hre]
  rw [hN]
  generalize hNd : 1 - 2 * (1 / 100 : ℝ) * z.re + (1 / 100 : ℝ) ^ 2 = N at hne ⊢
  have e1 : 16 * ((1 - (1 / 100 : ℝ) ^ 2) / N - 1) = 16 * ((1 - (1 / 100 : ℝ) ^ 2) - N) / N := by
    field_simp
  have e2 : 32 * (1 / 100 * z.re * ((1 - 1 / 100 * z.re) / N) - 1 / 100 * z.im * (1 / 100 * z.im / N))
      = 32 * (1 / 100 * z.re * (1 - 1 / 100 * z.re) - 1 / 100 * z.im * (1 / 100 * z.im)) / N := by
    field_simp
  rw [e1, e2]
  congr 1
  rw [← hNd]
  nlinarith [hre]



/-! #### Term-by-term integration: Fourier coefficients -/

theorem four_poisson_term_int (n : ℤ) (j : ℕ) :
    ∫ x : Torus 1, fourier (-n) (x 0) * ((32 * (1 / 100 : ℝ) ^ (j + 1) * cm (2 * ((j : ℤ) + 1)) x : ℝ) : ℂ) =
      ((32 * (1 / 100 : ℝ) ^ (j + 1) : ℝ) : ℂ) *
        (((if 2 * ((j : ℤ) + 1) - n = 0 then 1 else 0) +
          (if -(2 * ((j : ℤ) + 1)) - n = 0 then 1 else 0)) / 2) := by
  have e : ∀ x : Torus 1, fourier (-n) (x 0) * ((32 * (1 / 100 : ℝ) ^ (j + 1) * cm (2 * ((j : ℤ) + 1)) x : ℝ) : ℂ) =
      ((32 * (1 / 100 : ℝ) ^ (j + 1) : ℝ) : ℂ) * (fourier (-n) (x 0) * ((cm (2 * ((j : ℤ) + 1)) x : ℝ) : ℂ)) := by
    intro x; push_cast; ring
  simp_rw [e]
  rw [integral_const_mul, int_fourier_mul_cm]

theorem chat_hasSum (n : ℤ) :
    HasSum (fun j : ℕ => ∫ x : Torus 1, fourier (-n) (x 0) *
        ((32 * (1 / 100 : ℝ) ^ (j + 1) * cm (2 * ((j : ℤ) + 1)) x : ℝ) : ℂ))
      (∫ x : Torus 1, fourier (-n) (x 0) * ((poissonKernel x : ℝ) : ℂ)) := by
  refine hasSum_integral_of_dominated_convergence (fun j _ => 32 * (1 / 100 : ℝ) ^ (j + 1)) ?_ ?_ ?_ ?_ ?_
  · intro j
    exact ((four_cont (-n)).mul (Complex.continuous_ofReal.comp
      (continuous_const.mul (cm_cont _)))).aestronglyMeasurable
  · intro j
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have h1 : ‖fourier (-n) (x 0)‖ = 1 := by simp
    rw [h1, one_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 32 * (1 / 100 : ℝ) ^ (j + 1))]
    exact mul_le_of_le_one_right (by positivity) (cm_abs_le _ _)
  · exact Eventually.of_forall fun x => by
      simpa [pow_succ] using
        ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num)).mul_right
          (1 / 100 : ℝ)).mul_left 32
  · exact integrable_const _
  · exact Eventually.of_forall fun x =>
      (Complex.hasSum_ofReal.mpr (poisson_series_aux x)).mul_left _

/-- If exactly one term `b` can contribute, the Fourier coefficient is the real part of that term. -/
theorem chat_of_unique (n : ℤ) (b : ℕ)
    (hb : ∀ j : ℕ, j ≠ b → 2 * ((j : ℤ) + 1) ≠ n ∧ -(2 * ((j : ℤ) + 1)) ≠ n) :
    chat poissonKernel n =
      (((32 * (1 / 100 : ℝ) ^ (b + 1) : ℝ) : ℂ) *
        (((if 2 * ((b : ℤ) + 1) - n = 0 then 1 else 0) +
          (if -(2 * ((b : ℤ) + 1)) - n = 0 then 1 else 0)) / 2)).re := by
  have hs := chat_hasSum n
  simp_rw [four_poisson_term_int] at hs
  have h1 := hasSum_single (f := fun j : ℕ => ((32 * (1 / 100 : ℝ) ^ (j + 1) : ℝ) : ℂ) *
        (((if 2 * ((j : ℤ) + 1) - n = 0 then 1 else 0) +
          (if -(2 * ((j : ℤ) + 1)) - n = 0 then 1 else 0)) / 2)) b (by
    intro j hj
    obtain ⟨h2, h3⟩ := hb j hj
    have c1 : ¬ (2 * ((j : ℤ) + 1) - n = 0) := fun h => h2 (by omega)
    have c2 : ¬ (-(2 * ((j : ℤ) + 1)) - n = 0) := fun h => h3 (by omega)
    simp [c1, c2])
  have := hs.unique h1
  unfold chat
  rw [this]

theorem chat_poisson_zero_aux (n : ℤ) (hn : ∀ j : ℕ, 2 * ((j : ℤ) + 1) ≠ n ∧ -(2 * ((j : ℤ) + 1)) ≠ n) :
    chat poissonKernel n = 0 := by
  have := chat_of_unique n 0 (fun j _ => hn j)
  rw [this]
  have c1 : ¬ (2 * (((0 : ℕ) : ℤ) + 1) - n = 0) := fun h => (hn 0).1 (by simp only [Nat.cast_zero] at h ⊢; omega)
  have c2 : ¬ (-(2 * (((0 : ℕ) : ℤ) + 1)) - n = 0) := fun h => (hn 0).2 (by simp only [Nat.cast_zero] at h ⊢; omega)
  rw [if_neg c1, if_neg c2]
  simp

/-! #### Term-by-term differentiation -/

theorem hasSum_shift0 {f : ℕ → ℝ} {a : ℝ} (h0 : f 0 = 0) (h : HasSum (fun j => f (j + 1)) a) :
    HasSum f a := by
  refine (hasSum_nat_add_iff' 1).mp ?_
  simpa [h0] using h

theorem summable_pow_shift (k : ℕ) :
    Summable fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ k * (1 / 100 : ℝ) ^ (j + 1) := by
  have := summable_pow_mul_geometric_of_norm_lt_one k (r := (1 / 100 : ℝ)) (by norm_num)
  exact (summable_nat_add_iff 1).mpr this

/-- coefficients `32 r^(j+1)` -/
noncomputable def pcoef (j : ℕ) : ℝ := 32 * (1 / 100 : ℝ) ^ (j + 1)

/-- frequencies `4π (j+1)` -/
noncomputable def pfreq (j : ℕ) : ℝ := 4 * π * ((j : ℝ) + 1)

theorem summable_pc (k : ℕ) : Summable fun j : ℕ => pcoef j * pfreq j ^ k := by
  refine ((summable_pow_shift k).mul_left (32 * (4 * π) ^ k)).congr (fun j => ?_)
  simp only [pcoef, pfreq]
  push_cast
  have : (4 * π * ((j : ℝ) + 1)) ^ k = (4 * π) ^ k * ((j : ℝ) + 1) ^ k := mul_pow _ _ _
  rw [this]
  ring

theorem hasDerivAt_cos_series (c fr : ℕ → ℝ) (hc : Summable fun j => |c j|)
    (hcfr : Summable fun j => |c j * fr j|) (t : ℝ) :
    HasDerivAt (fun s => ∑' j, c j * Real.cos (fr j * s))
      (∑' j, -(c j * fr j) * Real.sin (fr j * t)) t := by
  refine hasDerivAt_tsum (g := fun j s => c j * Real.cos (fr j * s))
    (g' := fun j s => -(c j * fr j) * Real.sin (fr j * s)) (y₀ := 0) hcfr ?_ ?_ ?_ t
  · intro j y
    have h1 : HasDerivAt (fun s => fr j * s) (fr j) y := by
      simpa using (hasDerivAt_id y).const_mul (fr j)
    have := (h1.cos).const_mul (c j)
    convert this using 1
    ring
  · intro j y
    rw [Real.norm_eq_abs, abs_mul, abs_neg]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  · simpa using hc.of_abs

theorem hasDerivAt_sin_series (c fr : ℕ → ℝ) (hc : Summable fun j => |c j|)
    (hcfr : Summable fun j => |c j * fr j|) (t : ℝ) :
    HasDerivAt (fun s => ∑' j, c j * Real.sin (fr j * s))
      (∑' j, (c j * fr j) * Real.cos (fr j * t)) t := by
  refine hasDerivAt_tsum (g := fun j s => c j * Real.sin (fr j * s))
    (g' := fun j s => (c j * fr j) * Real.cos (fr j * s)) (y₀ := 0) hcfr ?_ ?_ ?_ t
  · intro j y
    have h1 : HasDerivAt (fun s => fr j * s) (fr j) y := by
      simpa using (hasDerivAt_id y).const_mul (fr j)
    have := (h1.sin).const_mul (c j)
    convert this using 1
    ring
  · intro j y
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  · simp

theorem pf_cast (j : ℕ) : 2 * π * ((2 * ((j : ℤ) + 1) : ℤ) : ℝ) = pfreq j := by
  simp only [pfreq]; push_cast; ring

theorem poisson_lift_series (t : ℝ) :
    poissonKernel (liftT fun _ : Fin 1 => t) = ∑' j : ℕ, pcoef j * Real.cos (pfreq j * t) := by
  rw [← (poisson_series_aux (liftT fun _ : Fin 1 => t)).tsum_eq]
  congr 1
  funext j
  rw [cm_lift, pf_cast]
  rfl

theorem sum_pc_abs0 : Summable fun j : ℕ => |pcoef j| := by
  simpa using (summable_pc 0).abs

theorem sum_pc_abs1 : Summable fun j : ℕ => |pcoef j * pfreq j| := by
  simpa using (summable_pc 1).abs

theorem sum_pc_abs2 : Summable fun j : ℕ => |pcoef j * pfreq j * pfreq j| := by
  have := (summable_pc 2).abs
  refine this.congr (fun j => ?_)
  ring_nf

theorem dT_formula (y : Torus 1) :
    dT poissonKernel y = ∑' j : ℕ, -(pcoef j * pfreq j) * Real.sin (pfreq j * rep y) := by
  unfold dT
  have : (fun t : ℝ => poissonKernel (liftT fun _ : Fin 1 => t)) =
      fun t => ∑' j : ℕ, pcoef j * Real.cos (pfreq j * t) := funext poisson_lift_series
  rw [this]
  exact (hasDerivAt_cos_series pcoef pfreq sum_pc_abs0 sum_pc_abs1 (rep y)).deriv

theorem dT_formula' (y : Torus 1) :
    dT poissonKernel y = ∑' j : ℕ, -(pcoef j * pfreq j) * sm (2 * ((j : ℤ) + 1)) y := by
  rw [dT_formula]
  congr 1
  funext j
  rw [sm_rep, pf_cast]

theorem dT_lift (t : ℝ) :
    dT poissonKernel (liftT fun _ : Fin 1 => t) =
      ∑' j : ℕ, -(pcoef j * pfreq j) * Real.sin (pfreq j * t) := by
  rw [dT_formula']
  congr 1
  funext j
  rw [sm_lift, pf_cast]

theorem dT2_formula (y : Torus 1) :
    dT (dT poissonKernel) y =
      ∑' j : ℕ, (-(pcoef j * pfreq j) * pfreq j) * Real.cos (pfreq j * rep y) := by
  have hd : ∀ (f : Torus 1 → ℝ) (y : Torus 1), dT f y = deriv (fun t : ℝ => f (liftT fun _ : Fin 1 => t)) (rep y) :=
    fun _ _ => rfl
  rw [hd (dT poissonKernel) y]
  have : (fun t : ℝ => dT poissonKernel (liftT fun _ : Fin 1 => t)) =
      fun t => ∑' j : ℕ, -(pcoef j * pfreq j) * Real.sin (pfreq j * t) := funext dT_lift
  rw [this]
  refine (hasDerivAt_sin_series (fun j => -(pcoef j * pfreq j)) pfreq ?_ ?_ (rep y)).deriv
  · simpa using sum_pc_abs1
  · simpa [mul_assoc] using sum_pc_abs2

/-! ### Frozen theorems -/

/-- Locally uniform (here: for each point) cosine series of the Poisson kernel. -/
theorem poisson_series (x : Torus 1) :
    HasSum (fun j : ℕ => 32 * (1 / 100 : ℝ) ^ (j + 1) * cm (2 * ((j : ℤ) + 1)) x) (poissonKernel x) :=
  poisson_series_aux x

theorem poisson_zero : poissonKernel 0 = 32 / 99 := by
  have h : cosMode 2 (0 : Torus 1) = 1 := by
    simp [cosMode, fourier_eval_zero]
  unfold poissonKernel
  rw [h]
  norm_num

theorem poisson_good : GoodKernel poissonKernel where
  smooth := by
    unfold IsSmoothT
    have h : (poissonKernel ∘ liftT) = fun v : Fin 1 → ℝ => 16 * ((1 - (1 / 100 : ℝ) ^ 2) /
        (1 - 2 * (1 / 100 : ℝ) * Real.cos (2 * π * ((2 : ℤ) : ℝ) * v 0) + (1 / 100 : ℝ) ^ 2) - 1) := by
      funext v
      rw [Function.comp, lift_eq]
      unfold poissonKernel
      rw [cosMode_eq_cm, cm_lift]
      norm_num
    rw [h]
    have hcos : ContDiff ℝ ∞ (fun v : Fin 1 → ℝ => Real.cos (2 * π * ((2 : ℤ) : ℝ) * v 0)) :=
      Real.contDiff_cos.comp (contDiff_const.mul (contDiff_apply ℝ ℝ 0))
    refine contDiff_const.mul ((contDiff_const.div
      ((contDiff_const.sub (contDiff_const.mul hcos)).add contDiff_const) (fun v => ?_)).sub contDiff_const)
    exact (poisson_denom_pos _ (Real.abs_cos_le_one _)).ne'
  even := fun x => by
    unfold poissonKernel
    rw [cosMode_eq_cm, cosMode_eq_cm, cm_neg]
  meanZero := by
    have h := chat_poisson_zero_aux 0 (fun j => ⟨by omega, by omega⟩)
    unfold chat at h
    simpa [fourier_zero, integral_complex_ofReal] using h

/-- `dT C = -128π ∑_j j r^j sin(4π j x)` (the `j = 0` term is zero). -/
theorem dT_poisson_series (x : Torus 1) :
    HasSum (fun j : ℕ => -(128 * π) * (j : ℝ) * (1 / 100 : ℝ) ^ j * sm (2 * (j : ℤ)) x)
      (dT poissonKernel x) := by
  have hsum : Summable fun j : ℕ => -(pcoef j * pfreq j) * sm (2 * ((j : ℤ) + 1)) x := by
    refine Summable.of_norm_bounded sum_pc_abs1 (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_neg]
    exact mul_le_of_le_one_right (abs_nonneg _) (sm_abs_le _ _)
  have hs : HasSum (fun j : ℕ => -(pcoef j * pfreq j) * sm (2 * ((j : ℤ) + 1)) x) (dT poissonKernel x) := by
    rw [dT_formula']; exact hsum.hasSum
  refine hasSum_shift0 (by simp) ?_
  convert hs using 1
  funext j
  simp only [pcoef, pfreq]
  push_cast
  ring_nf

/-- `C'' = -∑_j 32 r^j (4π j)² cos(4π j x)` (the `j = 0` term is zero). -/
theorem dT2_poisson_series (x : Torus 1) :
    HasSum (fun j : ℕ => -(32 : ℝ) * (1 / 100 : ℝ) ^ j * (4 * π * j) ^ 2 * cm (2 * (j : ℤ)) x)
      (dT (dT poissonKernel) x) := by
  have hc : ∀ j : ℕ, Real.cos (pfreq j * rep x) = cm (2 * ((j : ℤ) + 1)) x := by
    intro j; rw [cm_rep, pf_cast]
  have hsum : Summable fun j : ℕ => (-(pcoef j * pfreq j) * pfreq j) * cm (2 * ((j : ℤ) + 1)) x := by
    refine Summable.of_norm_bounded sum_pc_abs2 (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, neg_mul, abs_neg]
    exact mul_le_of_le_one_right (abs_nonneg _) (cm_abs_le _ _)
  have hs : HasSum (fun j : ℕ => (-(pcoef j * pfreq j) * pfreq j) * cm (2 * ((j : ℤ) + 1)) x)
      (dT (dT poissonKernel) x) := by
    rw [dT2_formula]
    simp_rw [hc]
    exact hsum.hasSum
  refine hasSum_shift0 (by simp) ?_
  convert hs using 1
  funext j
  simp only [pcoef, pfreq]
  push_cast
  ring_nf

theorem chat_poisson_even (j : ℤ) (hj : j ≠ 0) :
    chat poissonKernel (2 * j) = 16 * (1 / 100 : ℝ) ^ j.natAbs := by
  have key := chat_of_unique (2 * j) (j.natAbs - 1) (fun k hk => ⟨by omega, by omega⟩)
  rw [key]
  have hpos : 0 < j.natAbs := Int.natAbs_pos.mpr hj
  have e : j.natAbs - 1 + 1 = j.natAbs := Nat.sub_add_cancel hpos
  rcases lt_or_gt_of_ne hj with h | h
  · have c1 : ¬ (2 * (((j.natAbs - 1 : ℕ) : ℤ) + 1) - 2 * j = 0) := by omega
    have c2 : (-(2 * (((j.natAbs - 1 : ℕ) : ℤ) + 1)) - 2 * j = 0) := by omega
    rw [if_neg c1, if_pos c2, e]
    rw [show ((0 : ℂ) + 1) / 2 = ((1 / 2 : ℝ) : ℂ) by push_cast; norm_num, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    ring
  · have c1 : (2 * (((j.natAbs - 1 : ℕ) : ℤ) + 1) - 2 * j = 0) := by omega
    have c2 : ¬ (-(2 * (((j.natAbs - 1 : ℕ) : ℤ) + 1)) - 2 * j = 0) := by omega
    rw [if_pos c1, if_neg c2, e]
    rw [show ((1 : ℂ) + 0) / 2 = ((1 / 2 : ℝ) : ℂ) by push_cast; norm_num, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    ring

theorem chat_poisson_odd (n : ℤ) (hn : Odd n) : chat poissonKernel n = 0 := by
  obtain ⟨m, hm⟩ := hn
  exact chat_poisson_zero_aux n (fun j => ⟨by omega, by omega⟩)

theorem chat_poisson_zero : chat poissonKernel 0 = 0 :=
  chat_poisson_zero_aux 0 (fun j => ⟨by omega, by omega⟩)

end SharpLSI.FL.Ex.LaneD
