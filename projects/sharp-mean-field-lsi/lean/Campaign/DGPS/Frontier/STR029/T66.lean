import DGPS.Analysis.PeriodicHolder
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# STR029.66: Parameter calculus in a fixed spatial norm

Task id: STR029.66 (node STR029), "Parameter calculus in a fixed spatial norm".

Statement. For each fixed integer `m`, differentiation `C^{m+1} -> C^m` and `P_0` are bounded
linear, and multiplication in `C^m` is bounded bilinear with norm at most `2^m`. Thus the right
side of the branch equation, `N(h, r, u) = P_0[3 h sin 3t * u' - u'^2 / 2 - r u]`, is `C^3` into
`C^m` whenever `u` is a periodic Haar-mean-zero family that is `C^3` into `C^{m+1}` and `r` is a
real `C^3` function. The proof also gives
`‖N(h, r, u)‖_{C^m} <= (|r| + 6 |h| 2^m S_m) ‖u‖_{C^{m+1}} + 2^m ‖u‖_{C^{m+1}}^2`
with `S_m = sum_{j = 0}^m 3^j`.

Provides:
* `DGPS.Frontier.STR029.str029_66_parameter_calculus_fixed_spatial_norm`: the combined statement for
  a fixed `m`: the bounded linear maps `dCLM_STR02966 m`, `P0CLM_STR02966 m` (norms at most `1` and
  `2`), the bounded bilinear map `mulCLM_STR02966 m` (norm at most `2^m`), the pointwise formula
  for `rhs64_STR02966`, its `C^3` dependence on the parameters, and the displayed bound.
* `DGPS.Frontier.STR029.str029_66_parameter_calculus_fixed_spatial_norm_deriv`: `d/dt` from `C^{m+1}`
  to `C^m` is the bounded linear map `dCLM_STR02966 m`, pointwise `deriv`, of norm at most `1`.
* `DGPS.Frontier.STR029.str029_66_parameter_calculus_fixed_spatial_norm_incl`: the inclusion
  `C^{m+1} -> C^m` is the bounded linear map `inclCLM_STR02966 m` of norm at most `1`.
* `DGPS.Frontier.STR029.str029_66_parameter_calculus_fixed_spatial_norm_P0`: `P_0 f = f - mean f` on
  `C^m` is the bounded linear map `P0CLM_STR02966 m` of norm at most `2`.
* `DGPS.Frontier.STR029.str029_66_parameter_calculus_fixed_spatial_norm_mul`: pointwise product on
  `C^m` is the bounded bilinear map `mulCLM_STR02966 m` of norm at most `2^m`.
* `DGPS.Frontier.STR029.str029_66_parameter_calculus_fixed_spatial_norm_rhs_formula`: the pointwise
  formula of `rhs64_STR02966 m h r u`, which is the composition of the maps above.
* `DGPS.Frontier.STR029.str029_66_parameter_calculus_fixed_spatial_norm_contDiffOn`: for `r` real
  `C^3` and `u` `C^3` into `C^{m+1}` on a parameter set `s`, the right side is `C^3` into `C^m`
  on `s`.
* `DGPS.Frontier.STR029.str029_66_parameter_calculus_fixed_spatial_norm_bound`: the displayed bound
  for mean-zero `u`.

R5 notes:
* Concrete carriers. The spatial variable is the angle `t` with period `2 pi`, matching the
  `t`-versions of node STR029 (`meanT_STR02901` in T01). `PerCm_STR02966 m` is the space of
  `2 pi`-periodic `C^m` functions `ℝ -> ℝ` (a subtype of `ℝ -> ℝ` with the submodule structure),
  normed by `‖f‖ = sum_{j <= m} ‖f^{(j)}‖_inf`, with `‖.‖_inf` the periodic sup norm `supNorm`
  of `DGPS.Analysis.PeriodicHolder` (reused, not redefined). This is the standard `C^m` norm; the
  statement does not fix a different one.
* The Haar mean on the circle is the literal expression `(2 pi)^{-1} * ∫_0^{2 pi} f`, written
  `meanCm_STR02966`. It is the same expression as `meanT_STR02901`; the heavy module T01 is not
  loaded just for this one-line definition.
* The families `u` and `r` depend on the real parameter `h`. The smoothness claim is stated on an
  arbitrary parameter set `s` (use the branch interval, or the whole line) as `ContDiffOn ℝ 3`
  of the families into the normed spaces `PerCm_STR02966 (m + 1)` and `ℝ`. Differentiability on
  an open set is the case `s` open.
* The smoothness conclusion does not use the mean-zero hypothesis (it holds for every `C^3`
  family `u`), so the statement is stronger than the literal one. The mean-zero hypothesis
  is used in the bound only: for mean-zero `u` one has `P_0 (r u) = r u`, which gives the coefficient
  `|r|` instead of `2 |r|`. The right side `rhs64_STR02966` applies `P_0` to the whole bracket, as
  in the displayed formula, so no mean-zero reading is built into the definition.
* Periodicity of the families is built into the carriers: every `u h` lies in `PerCm_STR02966 (m+1)`.
* Operator form. The maps are stated as explicit continuous linear maps with value equations and
  norm bounds, not as bare existence claims: `dCLM_STR02966`, `inclCLM_STR02966`, `P0CLM_STR02966`
  and the continuous bilinear `mulCLM_STR02966`, built with `LinearMap.mkContinuous` and
  `LinearMap.mkContinuous₂`. The norm bound for multiplication is proved by induction on `m` using
  `cmN_succ_STR02966` (`‖f‖_{C^{m+1}} = ‖f‖_inf + ‖f'‖_{C^m}`), because there is no iterated Leibniz
  rule to reuse; the constant `2^m` is the stated one.
* The fixed element is `sin 3t`, with `‖sin 3t‖_{C^m} <= S_m = sum_{j <= m} 3^j`. The factor `3 h`
  multiplies it as a scalar, so the parameter `h` enters linearly.
* The bound `(|r| + 6 |h| 2^m S_m) ‖u‖ + 2^m ‖u‖^2` is the one in the node text; its derivation
  uses `‖P_0‖ <= 2`.
* Smoothness is shown by composing the continuous linear maps with the family `u`
  (`ContinuousLinearMap.contDiff.comp_contDiffOn`), with `ContDiffOn.clm_apply` for the bilinear
  term, and then `ContDiffOn.smul`, `ContDiffOn.sub`.
-/

open DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.STR029

/-! ### The regularity predicate and the `C^m` norm of a function -/

/-- `f` is `2π`-periodic and of class `C^m`. -/
def IsPerCm_STR02966 (m : ℕ) (f : ℝ → ℝ) : Prop :=
  Function.Periodic f (2 * Real.pi) ∧ ContDiff ℝ m f

/-- The `C^m` norm of a function: `∑_{j ≤ m} ‖f^{(j)}‖_∞`. -/
noncomputable def cmN_STR02966 (m : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), supNorm (iteratedDeriv j f)

/-- The mean over one period (Haar mean on the circle in the angle variable). -/
noncomputable def meanCm_STR02966 (f : ℝ → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..(2 * Real.pi), f t

/-- `S_m = ∑_{j = 0}^m 3^j`. -/
noncomputable def S_STR02966 (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (3 : ℝ) ^ j

theorem cmN_succ_STR02966 (m : ℕ) (f : ℝ → ℝ) :
    cmN_STR02966 (m + 1) f = supNorm f + cmN_STR02966 m (deriv f) := by
  unfold cmN_STR02966
  rw [Finset.sum_range_succ' _ (m + 1)]
  simp only [iteratedDeriv_succ', iteratedDeriv_zero]
  ring

theorem cmN_zero_STR02966 (f : ℝ → ℝ) : cmN_STR02966 0 f = supNorm f := by
  simp [cmN_STR02966]

theorem cmN_nonneg_STR02966 (m : ℕ) (f : ℝ → ℝ) : 0 ≤ cmN_STR02966 m f :=
  Finset.sum_nonneg fun _ _ => supNorm_nonneg _

theorem supNorm_le_cmN_STR02966 (m : ℕ) (f : ℝ → ℝ) : supNorm f ≤ cmN_STR02966 m f := by
  cases m with
  | zero => rw [cmN_zero_STR02966]
  | succ m => rw [cmN_succ_STR02966]; linarith [cmN_nonneg_STR02966 m (deriv f)]

theorem cmN_le_succ_STR02966 (m : ℕ) (f : ℝ → ℝ) :
    cmN_STR02966 m f ≤ cmN_STR02966 (m + 1) f := by
  unfold cmN_STR02966
  rw [Finset.sum_range_succ _ (m + 1)]
  linarith [supNorm_nonneg (iteratedDeriv (m + 1) f)]

theorem S_succ_STR02966 (m : ℕ) : S_STR02966 (m + 1) = 1 + 3 * S_STR02966 m := by
  unfold S_STR02966
  rw [Finset.sum_range_succ' _ (m + 1), Finset.mul_sum]
  simp only [pow_succ, pow_zero]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem S_zero_STR02966 : S_STR02966 0 = 1 := by
  simp [S_STR02966]

theorem S_nonneg_STR02966 (m : ℕ) : 0 ≤ S_STR02966 m :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem supNorm_smul_STR02966 (c : ℝ) (f : ℝ → ℝ) : supNorm (c • f) = |c| * supNorm f := by
  unfold supNorm
  rw [Real.mul_iSup_of_nonneg (abs_nonneg c)]
  refine iSup_congr fun x => ?_
  simp [abs_mul]

theorem cmN_smul_STR02966 (m : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    cmN_STR02966 m (c • f) = |c| * cmN_STR02966 m f := by
  induction m generalizing f with
  | zero => simp only [cmN_zero_STR02966, supNorm_smul_STR02966]
  | succ m ih =>
    have hd : deriv (c • f) = c • deriv f := by
      funext x
      exact deriv_const_mul_field c
    rw [cmN_succ_STR02966, cmN_succ_STR02966, hd, ih, supNorm_smul_STR02966]
    ring

theorem supNorm_const_STR02966 (c : ℝ) : supNorm (fun _ => c) = |c| := by
  unfold supNorm
  rw [ciSup_const]

theorem cmN_const_STR02966 (m : ℕ) (c : ℝ) : cmN_STR02966 m (fun _ => c) = |c| := by
  induction m generalizing c with
  | zero => rw [cmN_zero_STR02966, supNorm_const_STR02966]
  | succ m ih =>
    have hd : deriv (fun _ : ℝ => c) = fun _ => 0 := by
      funext x
      exact deriv_const x c
    rw [cmN_succ_STR02966, hd, ih 0, supNorm_const_STR02966]
    simp

theorem periodic_deriv_STR02966 {f : ℝ → ℝ} (hp : Function.Periodic f (2 * Real.pi)) :
    Function.Periodic (deriv f) (2 * Real.pi) := by
  intro x
  have h : (fun y => f (y + 2 * Real.pi)) = f := funext hp
  have h2 := deriv_comp_add_const f (2 * Real.pi) x
  rw [h] at h2
  exact h2.symm

/-! ### Closure properties of the class `C^m` of periodic functions -/

theorem isPerCm_of_le_STR02966 {m n : ℕ} (h : m ≤ n) {f : ℝ → ℝ} (hf : IsPerCm_STR02966 n f) :
    IsPerCm_STR02966 m f :=
  ⟨hf.1, hf.2.of_le (by exact_mod_cast h)⟩

theorem isPerCm_deriv_STR02966 {m : ℕ} {f : ℝ → ℝ} (hf : IsPerCm_STR02966 (m + 1) f) :
    IsPerCm_STR02966 m (deriv f) := by
  refine ⟨periodic_deriv_STR02966 hf.1, ?_⟩
  have h : ContDiff ℝ ((m : WithTop ℕ∞) + 1) f := by exact_mod_cast hf.2
  exact (contDiff_succ_iff_deriv.mp h).2.2

theorem isPerCm_differentiable_STR02966 {m : ℕ} {f : ℝ → ℝ} (hf : IsPerCm_STR02966 (m + 1) f) :
    Differentiable ℝ f := by
  have h : ContDiff ℝ ((m : WithTop ℕ∞) + 1) f := by exact_mod_cast hf.2
  exact (contDiff_succ_iff_deriv.mp h).1

theorem isPerCm_add_STR02966 {m : ℕ} {f g : ℝ → ℝ} (hf : IsPerCm_STR02966 m f)
    (hg : IsPerCm_STR02966 m g) : IsPerCm_STR02966 m (f + g) :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

theorem isPerCm_smul_STR02966 {m : ℕ} {f : ℝ → ℝ} (c : ℝ) (hf : IsPerCm_STR02966 m f) :
    IsPerCm_STR02966 m (c • f) :=
  ⟨fun x => by simp only [Pi.smul_apply, hf.1 x], hf.2.const_smul c⟩

theorem isPerCm_mul_STR02966 {m : ℕ} {f g : ℝ → ℝ} (hf : IsPerCm_STR02966 m f)
    (hg : IsPerCm_STR02966 m g) : IsPerCm_STR02966 m (f * g) :=
  ⟨fun x => by simp only [Pi.mul_apply, hf.1 x, hg.1 x], hf.2.mul hg.2⟩

theorem isPerCm_const_STR02966 (m : ℕ) (c : ℝ) : IsPerCm_STR02966 m (fun _ => c) :=
  ⟨fun _ => rfl, contDiff_const⟩

theorem isPerCm_zero_STR02966 (m : ℕ) : IsPerCm_STR02966 m 0 :=
  isPerCm_const_STR02966 m 0

theorem isPerCm_sub_const_STR02966 {m : ℕ} {f : ℝ → ℝ} (hf : IsPerCm_STR02966 m f) (c : ℝ) :
    IsPerCm_STR02966 m (fun x => f x - c) :=
  ⟨fun x => by simp only [hf.1 x], hf.2.sub contDiff_const⟩

theorem bdd_of_isPerCm_STR02966 {m : ℕ} {f : ℝ → ℝ} (hf : IsPerCm_STR02966 m f) : Bdd f := by
  have hf0 := isPerCm_of_le_STR02966 (Nat.zero_le m) hf
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi)).exists_bound_of_continuousOn
    hf0.2.continuous.continuousOn
  refine ⟨max M 0, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hf0.1.exists_mem_Ico₀ (by positivity) x
  rw [hxy]
  exact (hM y ⟨hy.1, hy.2.le⟩).trans (le_max_left _ _)

theorem abs_le_supNorm_STR02966 {m : ℕ} {f : ℝ → ℝ} (hf : IsPerCm_STR02966 m f) (x : ℝ) :
    |f x| ≤ supNorm f :=
  (bdd_of_isPerCm_STR02966 hf).abs_le_supNorm x

/-! ### Triangle inequality and product bound for the `C^m` norm -/

theorem supNorm_add_le_STR02966 {m : ℕ} {f g : ℝ → ℝ} (hf : IsPerCm_STR02966 m f)
    (hg : IsPerCm_STR02966 m g) : supNorm (f + g) ≤ supNorm f + supNorm g :=
  supNorm_le fun x => by
    simp only [Pi.add_apply]
    exact (abs_add_le _ _).trans
      (add_le_add (abs_le_supNorm_STR02966 hf x) (abs_le_supNorm_STR02966 hg x))

theorem supNorm_mul_le_STR02966 {m : ℕ} {f g : ℝ → ℝ} (hf : IsPerCm_STR02966 m f)
    (hg : IsPerCm_STR02966 m g) : supNorm (f * g) ≤ supNorm f * supNorm g :=
  supNorm_le fun x => by
    simp only [Pi.mul_apply, abs_mul]
    exact mul_le_mul (abs_le_supNorm_STR02966 hf x) (abs_le_supNorm_STR02966 hg x)
      (abs_nonneg _) (supNorm_nonneg _)

theorem cmN_add_le_STR02966 (m : ℕ) : ∀ {f g : ℝ → ℝ}, IsPerCm_STR02966 m f →
    IsPerCm_STR02966 m g → cmN_STR02966 m (f + g) ≤ cmN_STR02966 m f + cmN_STR02966 m g := by
  induction m with
  | zero =>
    intro f g hf hg
    rw [cmN_zero_STR02966, cmN_zero_STR02966, cmN_zero_STR02966]
    exact supNorm_add_le_STR02966 hf hg
  | succ m ih =>
    intro f g hf hg
    have hd : deriv (f + g) = deriv f + deriv g := by
      funext x
      exact deriv_add (isPerCm_differentiable_STR02966 hf x) (isPerCm_differentiable_STR02966 hg x)
    rw [cmN_succ_STR02966, cmN_succ_STR02966, cmN_succ_STR02966, hd]
    have h1 := supNorm_add_le_STR02966 hf hg
    have h2 := ih (isPerCm_deriv_STR02966 hf) (isPerCm_deriv_STR02966 hg)
    linarith

theorem cmN_mul_le_STR02966 (m : ℕ) : ∀ {f g : ℝ → ℝ}, IsPerCm_STR02966 m f →
    IsPerCm_STR02966 m g → cmN_STR02966 m (f * g) ≤ 2 ^ m * cmN_STR02966 m f * cmN_STR02966 m g := by
  induction m with
  | zero =>
    intro f g hf hg
    rw [cmN_zero_STR02966, cmN_zero_STR02966, cmN_zero_STR02966]
    simpa using supNorm_mul_le_STR02966 hf hg
  | succ m ih =>
    intro f g hf hg
    have hd : deriv (f * g) = deriv f * g + f * deriv g := by
      funext x
      exact deriv_mul (isPerCm_differentiable_STR02966 hf x) (isPerCm_differentiable_STR02966 hg x)
    have hf' := isPerCm_deriv_STR02966 hf
    have hg' := isPerCm_deriv_STR02966 hg
    have hfm := isPerCm_of_le_STR02966 (Nat.le_succ m) hf
    have hgm := isPerCm_of_le_STR02966 (Nat.le_succ m) hg
    have e1 := cmN_add_le_STR02966 m (isPerCm_mul_STR02966 hf' hgm) (isPerCm_mul_STR02966 hfm hg')
    have e2 := ih hf' hgm
    have e3 := ih hfm hg'
    have e4 := supNorm_mul_le_STR02966 hf hg
    have hA : cmN_STR02966 m f ≤ supNorm f + cmN_STR02966 m (deriv f) := by
      have := cmN_le_succ_STR02966 m f
      rwa [cmN_succ_STR02966] at this
    have hB : cmN_STR02966 m g ≤ supNorm g + cmN_STR02966 m (deriv g) := by
      have := cmN_le_succ_STR02966 m g
      rwa [cmN_succ_STR02966] at this
    rw [cmN_succ_STR02966, hd, cmN_succ_STR02966 m f, cmN_succ_STR02966 m g]
    have hp1 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    have hp : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by ring
    rw [hp]
    have ha := supNorm_nonneg f
    have hb := supNorm_nonneg g
    have ha' := cmN_nonneg_STR02966 m (deriv f)
    have hb' := cmN_nonneg_STR02966 m (deriv g)
    have hA0 := cmN_nonneg_STR02966 m f
    have hB0 := cmN_nonneg_STR02966 m g
    have hp0 : (0 : ℝ) ≤ 2 ^ m := by linarith
    have s1 : 2 ^ m * cmN_STR02966 m (deriv f) * cmN_STR02966 m g ≤
        2 ^ m * cmN_STR02966 m (deriv f) * (supNorm g + cmN_STR02966 m (deriv g)) :=
      mul_le_mul_of_nonneg_left hB (mul_nonneg hp0 ha')
    have s2 : 2 ^ m * cmN_STR02966 m f * cmN_STR02966 m (deriv g) ≤
        2 ^ m * (supNorm f + cmN_STR02966 m (deriv f)) * cmN_STR02966 m (deriv g) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hp0) hb'
    have s3 : supNorm f * supNorm g ≤ 2 ^ m * (supNorm f * supNorm g) :=
      le_mul_of_one_le_left (mul_nonneg ha hb) hp1
    nlinarith [mul_nonneg ha hb, mul_nonneg (sub_nonneg.2 hp1) (mul_nonneg ha hb),
      mul_nonneg hp0 (mul_nonneg ha hb'), mul_nonneg hp0 (mul_nonneg ha' hb)]

/-! ### The Haar mean -/

theorem abs_meanCm_le_STR02966 {m : ℕ} {f : ℝ → ℝ} (hf : IsPerCm_STR02966 m f) :
    |meanCm_STR02966 f| ≤ supNorm f := by
  unfold meanCm_STR02966
  have hpi : 0 < 2 * Real.pi := by positivity
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
    (f := f) (C := supNorm f) (fun x _ => by
      rw [Real.norm_eq_abs]
      exact abs_le_supNorm_STR02966 hf x)
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hpi] at h
  rw [abs_mul, abs_inv, abs_of_pos hpi]
  calc (2 * Real.pi)⁻¹ * |∫ t in (0 : ℝ)..(2 * Real.pi), f t|
      ≤ (2 * Real.pi)⁻¹ * (supNorm f * (2 * Real.pi)) := by gcongr
    _ = supNorm f := by field_simp

theorem meanCm_add_STR02966 {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    meanCm_STR02966 (f + g) = meanCm_STR02966 f + meanCm_STR02966 g := by
  unfold meanCm_STR02966
  simp only [Pi.add_apply]
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _),
    mul_add]

theorem meanCm_smul_STR02966 (c : ℝ) (f : ℝ → ℝ) :
    meanCm_STR02966 (c • f) = c * meanCm_STR02966 f := by
  unfold meanCm_STR02966
  simp only [Pi.smul_apply, smul_eq_mul, intervalIntegral.integral_const_mul]
  ring

theorem meanCm_const_STR02966 (c : ℝ) : meanCm_STR02966 (fun _ => c) = c := by
  unfold meanCm_STR02966
  rw [intervalIntegral.integral_const]
  have hpi : 0 < 2 * Real.pi := by positivity
  simp only [sub_zero, smul_eq_mul]
  field_simp

/-! ### The normed spaces `C^m` of `2π`-periodic functions -/

/-- The real vector space of `2π`-periodic functions of class `C^m`. -/
def perCmSubmodule_STR02966 (m : ℕ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {g | IsPerCm_STR02966 m g}
  add_mem' := fun ha hb => isPerCm_add_STR02966 ha hb
  zero_mem' := isPerCm_zero_STR02966 m
  smul_mem' := fun c _ hf => isPerCm_smul_STR02966 c hf

/-- The concrete space `C^m` of `2π`-periodic functions. -/
def PerCm_STR02966 (m : ℕ) : Type := ↥(perCmSubmodule_STR02966 m)

instance (m : ℕ) : AddCommGroup (PerCm_STR02966 m) :=
  inferInstanceAs (AddCommGroup ↥(perCmSubmodule_STR02966 m))

instance (m : ℕ) : Module ℝ (PerCm_STR02966 m) :=
  inferInstanceAs (Module ℝ ↥(perCmSubmodule_STR02966 m))

/-- The function underlying an element. -/
def PerCm_STR02966.val {m : ℕ} (f : PerCm_STR02966 m) : ℝ → ℝ :=
  Subtype.val (p := fun g => g ∈ perCmSubmodule_STR02966 m) f

/-- Build an element from a function with the defining properties. -/
def PerCm_STR02966.mk {m : ℕ} (g : ℝ → ℝ) (h : IsPerCm_STR02966 m g) : PerCm_STR02966 m :=
  Subtype.mk (p := fun g => g ∈ perCmSubmodule_STR02966 m) g h

theorem PerCm_STR02966.isPerCm {m : ℕ} (f : PerCm_STR02966 m) : IsPerCm_STR02966 m f.val :=
  Subtype.property (p := fun g => g ∈ perCmSubmodule_STR02966 m) f

theorem PerCm_STR02966.ext {m : ℕ} {f g : PerCm_STR02966 m} (h : f.val = g.val) : f = g :=
  Subtype.ext h

theorem PerCm_STR02966.val_mk {m : ℕ} (g : ℝ → ℝ) (h : IsPerCm_STR02966 m g) :
    (PerCm_STR02966.mk g h).val = g := rfl

theorem PerCm_STR02966.val_add {m : ℕ} (f g : PerCm_STR02966 m) : (f + g).val = f.val + g.val :=
  rfl

theorem PerCm_STR02966.val_sub {m : ℕ} (f g : PerCm_STR02966 m) : (f - g).val = f.val - g.val :=
  rfl

theorem PerCm_STR02966.val_smul {m : ℕ} (c : ℝ) (f : PerCm_STR02966 m) :
    (c • f).val = c • f.val := rfl

theorem PerCm_STR02966.val_zero {m : ℕ} : (0 : PerCm_STR02966 m).val = fun _ => 0 := rfl

noncomputable instance (m : ℕ) : Norm (PerCm_STR02966 m) := ⟨fun f => cmN_STR02966 m f.val⟩

theorem PerCm_STR02966.norm_def {m : ℕ} (f : PerCm_STR02966 m) :
    ‖f‖ = cmN_STR02966 m f.val := rfl

theorem normCore_STR02966 (m : ℕ) : NormedSpace.Core ℝ (PerCm_STR02966 m) where
  norm_nonneg f := cmN_nonneg_STR02966 m _
  norm_smul c f := by
    rw [Real.norm_eq_abs, PerCm_STR02966.norm_def, PerCm_STR02966.norm_def,
      PerCm_STR02966.val_smul, cmN_smul_STR02966]
  norm_triangle f g := by
    simp only [PerCm_STR02966.norm_def, PerCm_STR02966.val_add]
    exact cmN_add_le_STR02966 m f.isPerCm g.isPerCm
  norm_eq_zero_iff f := by
    rw [PerCm_STR02966.norm_def]
    constructor
    · intro h
      apply PerCm_STR02966.ext
      funext x
      have h1 := supNorm_le_cmN_STR02966 m f.val
      have h2 := supNorm_nonneg f.val
      have h3 := abs_le_supNorm_STR02966 f.isPerCm x
      have : |f.val x| ≤ 0 := by linarith
      simpa [PerCm_STR02966.val_zero] using this
    · intro h
      rw [h, PerCm_STR02966.val_zero, cmN_const_STR02966]
      simp

noncomputable instance (m : ℕ) : NormedAddCommGroup (PerCm_STR02966 m) :=
  NormedAddCommGroup.ofCore (normCore_STR02966 m)

noncomputable instance (m : ℕ) : NormedSpace ℝ (PerCm_STR02966 m) :=
  NormedSpace.ofCore (normCore_STR02966 m)

theorem PerCm_STR02966.supNorm_le_norm {m : ℕ} (f : PerCm_STR02966 m) : supNorm f.val ≤ ‖f‖ :=
  supNorm_le_cmN_STR02966 m f.val

/-! ### The bounded linear and bilinear maps -/

/-- Differentiation `C^{m+1} → C^m` as a linear map. -/
noncomputable def dLin_STR02966 (m : ℕ) : PerCm_STR02966 (m + 1) →ₗ[ℝ] PerCm_STR02966 m where
  toFun f := PerCm_STR02966.mk (deriv f.val) (isPerCm_deriv_STR02966 f.isPerCm)
  map_add' f g := by
    apply PerCm_STR02966.ext
    show deriv (f.val + g.val) = deriv f.val + deriv g.val
    funext x
    exact deriv_add (isPerCm_differentiable_STR02966 f.isPerCm x)
      (isPerCm_differentiable_STR02966 g.isPerCm x)
  map_smul' c f := by
    apply PerCm_STR02966.ext
    show deriv (c • f.val) = c • deriv f.val
    funext x
    exact deriv_const_mul_field c

/-- Differentiation `C^{m+1} → C^m` as a bounded linear map. -/
noncomputable def dCLM_STR02966 (m : ℕ) : PerCm_STR02966 (m + 1) →L[ℝ] PerCm_STR02966 m :=
  (dLin_STR02966 m).mkContinuous 1 fun f => by
    show cmN_STR02966 m (deriv f.val) ≤ 1 * cmN_STR02966 (m + 1) f.val
    rw [cmN_succ_STR02966, one_mul]
    linarith [supNorm_nonneg f.val]

/-- The inclusion `C^{m+1} → C^m` as a linear map. -/
noncomputable def inclLin_STR02966 (m : ℕ) : PerCm_STR02966 (m + 1) →ₗ[ℝ] PerCm_STR02966 m where
  toFun f := PerCm_STR02966.mk f.val (isPerCm_of_le_STR02966 (Nat.le_succ m) f.isPerCm)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The inclusion `C^{m+1} → C^m` as a bounded linear map. -/
noncomputable def inclCLM_STR02966 (m : ℕ) : PerCm_STR02966 (m + 1) →L[ℝ] PerCm_STR02966 m :=
  (inclLin_STR02966 m).mkContinuous 1 fun f => by
    show cmN_STR02966 m f.val ≤ 1 * cmN_STR02966 (m + 1) f.val
    rw [one_mul]
    exact cmN_le_succ_STR02966 m f.val

/-- The projection `P_0 f = f - ∫ f dm` as a linear map on `C^m`. -/
noncomputable def P0Lin_STR02966 (m : ℕ) : PerCm_STR02966 m →ₗ[ℝ] PerCm_STR02966 m where
  toFun f := PerCm_STR02966.mk (fun x => f.val x - meanCm_STR02966 f.val)
    (isPerCm_sub_const_STR02966 f.isPerCm _)
  map_add' f g := by
    apply PerCm_STR02966.ext
    show (fun x => (f.val + g.val) x - meanCm_STR02966 (f.val + g.val)) =
      fun x => (f.val x - meanCm_STR02966 f.val) + (g.val x - meanCm_STR02966 g.val)
    rw [meanCm_add_STR02966 f.isPerCm.2.continuous g.isPerCm.2.continuous]
    funext x
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    apply PerCm_STR02966.ext
    show (fun x => (c • f.val) x - meanCm_STR02966 (c • f.val)) =
      fun x => c * (f.val x - meanCm_STR02966 f.val)
    rw [meanCm_smul_STR02966]
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem P0Lin_val_STR02966 {m : ℕ} (f : PerCm_STR02966 m) :
    (P0Lin_STR02966 m f).val = fun x => f.val x - meanCm_STR02966 f.val := rfl

/-- The projection `P_0` as a bounded linear map on `C^m`. -/
noncomputable def P0CLM_STR02966 (m : ℕ) : PerCm_STR02966 m →L[ℝ] PerCm_STR02966 m :=
  (P0Lin_STR02966 m).mkContinuous 2 fun f => by
    show cmN_STR02966 m (fun x => f.val x - meanCm_STR02966 f.val) ≤ 2 * cmN_STR02966 m f.val
    have h : (fun x => f.val x - meanCm_STR02966 f.val) =
        f.val + fun _ => -meanCm_STR02966 f.val := by
      funext x
      simp [sub_eq_add_neg]
    rw [h]
    have h1 := cmN_add_le_STR02966 m f.isPerCm (isPerCm_const_STR02966 m (-meanCm_STR02966 f.val))
    rw [cmN_const_STR02966, abs_neg] at h1
    have h2 := abs_meanCm_le_STR02966 f.isPerCm
    have h3 := supNorm_le_cmN_STR02966 m f.val
    linarith

/-- Pointwise multiplication on `C^m` as a bilinear map. -/
noncomputable def mulLin_STR02966 (m : ℕ) :
    PerCm_STR02966 m →ₗ[ℝ] PerCm_STR02966 m →ₗ[ℝ] PerCm_STR02966 m :=
  LinearMap.mk₂ ℝ (fun f g => PerCm_STR02966.mk (f.val * g.val)
      (isPerCm_mul_STR02966 f.isPerCm g.isPerCm))
    (fun f₁ f₂ g => by
      apply PerCm_STR02966.ext
      show (f₁.val + f₂.val) * g.val = f₁.val * g.val + f₂.val * g.val
      exact add_mul _ _ _)
    (fun c f g => by
      apply PerCm_STR02966.ext
      show (c • f.val) * g.val = c • (f.val * g.val)
      exact smul_mul_assoc _ _ _)
    (fun f g₁ g₂ => by
      apply PerCm_STR02966.ext
      show f.val * (g₁.val + g₂.val) = f.val * g₁.val + f.val * g₂.val
      exact mul_add _ _ _)
    (fun c f g => by
      apply PerCm_STR02966.ext
      show f.val * (c • g.val) = c • (f.val * g.val)
      exact mul_smul_comm _ _ _)

/-- Pointwise multiplication on `C^m` as a bounded bilinear map, of norm at most `2^m`. -/
noncomputable def mulCLM_STR02966 (m : ℕ) :
    PerCm_STR02966 m →L[ℝ] PerCm_STR02966 m →L[ℝ] PerCm_STR02966 m :=
  (mulLin_STR02966 m).mkContinuous₂ (2 ^ m) fun f g =>
    cmN_mul_le_STR02966 m f.isPerCm g.isPerCm

theorem dCLM_val_STR02966 {m : ℕ} (f : PerCm_STR02966 (m + 1)) :
    (dCLM_STR02966 m f).val = deriv f.val := rfl

theorem inclCLM_val_STR02966 {m : ℕ} (f : PerCm_STR02966 (m + 1)) :
    (inclCLM_STR02966 m f).val = f.val := rfl

theorem P0CLM_val_STR02966 {m : ℕ} (f : PerCm_STR02966 m) :
    (P0CLM_STR02966 m f).val = fun x => f.val x - meanCm_STR02966 f.val := rfl

theorem mulCLM_val_STR02966 {m : ℕ} (f g : PerCm_STR02966 m) :
    (mulCLM_STR02966 m f g).val = f.val * g.val := rfl

theorem dCLM_norm_le_STR02966 (m : ℕ) : ‖dCLM_STR02966 m‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem inclCLM_norm_le_STR02966 (m : ℕ) : ‖inclCLM_STR02966 m‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem P0CLM_norm_le_STR02966 (m : ℕ) : ‖P0CLM_STR02966 m‖ ≤ 2 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

theorem mulCLM_norm_le_STR02966 (m : ℕ) : ‖mulCLM_STR02966 m‖ ≤ 2 ^ m :=
  LinearMap.mkContinuous₂_norm_le _ (by positivity) _

/-! ### The explicit right side of the branch equation -/

theorem periodic_sin3_STR02966 : Function.Periodic (fun t : ℝ => Real.sin (3 * t)) (2 * Real.pi) := by
  intro x
  have h : 3 * (x + 2 * Real.pi) = 3 * x + (3 : ℕ) * (2 * Real.pi) := by push_cast; ring
  show Real.sin (3 * (x + 2 * Real.pi)) = Real.sin (3 * x)
  rw [h, Real.sin_add_nat_mul_two_pi]

theorem periodic_cos3_STR02966 : Function.Periodic (fun t : ℝ => Real.cos (3 * t)) (2 * Real.pi) := by
  intro x
  have h : 3 * (x + 2 * Real.pi) = 3 * x + (3 : ℕ) * (2 * Real.pi) := by push_cast; ring
  show Real.cos (3 * (x + 2 * Real.pi)) = Real.cos (3 * x)
  rw [h, Real.cos_add_nat_mul_two_pi]

theorem isPerCm_sin3_STR02966 (m : ℕ) : IsPerCm_STR02966 m (fun t : ℝ => Real.sin (3 * t)) :=
  ⟨periodic_sin3_STR02966, Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)⟩

theorem deriv_sin3_STR02966 :
    deriv (fun t : ℝ => Real.sin (3 * t)) = (3 : ℝ) • fun t : ℝ => Real.cos (3 * t) := by
  funext t
  have h1 : HasDerivAt (fun t : ℝ => 3 * t) 3 t := by
    simpa using (hasDerivAt_id t).const_mul (3 : ℝ)
  have h : HasDerivAt (fun t : ℝ => Real.sin (3 * t)) (Real.cos (3 * t) * 3) t := by
    simpa using h1.sin
  rw [h.deriv, Pi.smul_apply, smul_eq_mul]
  ring

theorem deriv_cos3_STR02966 :
    deriv (fun t : ℝ => Real.cos (3 * t)) = (-3 : ℝ) • fun t : ℝ => Real.sin (3 * t) := by
  funext t
  have h1 : HasDerivAt (fun t : ℝ => 3 * t) 3 t := by
    simpa using (hasDerivAt_id t).const_mul (3 : ℝ)
  have h : HasDerivAt (fun t : ℝ => Real.cos (3 * t)) (-Real.sin (3 * t) * 3) t := by
    simpa using h1.cos
  rw [h.deriv, Pi.smul_apply, smul_eq_mul]
  ring

theorem cmN_sin3_cos3_le_STR02966 (m : ℕ) :
    cmN_STR02966 m (fun t : ℝ => Real.sin (3 * t)) ≤ S_STR02966 m ∧
      cmN_STR02966 m (fun t : ℝ => Real.cos (3 * t)) ≤ S_STR02966 m := by
  induction m with
  | zero =>
    rw [cmN_zero_STR02966, cmN_zero_STR02966, S_zero_STR02966]
    exact ⟨supNorm_le fun x => Real.abs_sin_le_one _, supNorm_le fun x => Real.abs_cos_le_one _⟩
  | succ m ih =>
    have h1 : supNorm (fun t : ℝ => Real.sin (3 * t)) ≤ 1 :=
      supNorm_le fun x => Real.abs_sin_le_one _
    have h2 : supNorm (fun t : ℝ => Real.cos (3 * t)) ≤ 1 :=
      supNorm_le fun x => Real.abs_cos_le_one _
    have a3 : |(3 : ℝ)| = 3 := abs_of_pos (by norm_num)
    have a3' : |(-3 : ℝ)| = 3 := by rw [abs_neg]; exact a3
    rw [S_succ_STR02966, cmN_succ_STR02966, cmN_succ_STR02966, deriv_sin3_STR02966,
      deriv_cos3_STR02966, cmN_smul_STR02966, cmN_smul_STR02966, a3, a3']
    constructor <;> linarith [ih.1, ih.2]

/-- The element `t ↦ sin (3 t)` of `C^m`. -/
noncomputable def sin3_STR02966 (m : ℕ) : PerCm_STR02966 m :=
  PerCm_STR02966.mk (fun t : ℝ => Real.sin (3 * t)) (isPerCm_sin3_STR02966 m)

theorem sin3_norm_le_STR02966 (m : ℕ) : ‖sin3_STR02966 m‖ ≤ S_STR02966 m :=
  (cmN_sin3_cos3_le_STR02966 m).1

/-- The right side `N(h, r, u) = P_0[3 h sin 3t · u' - u'^2 / 2 - r u]` of the branch equation, as a
composition of the bounded maps `d/dt`, the inclusion, the product and `P_0`; the output lies in
`C^m` when `u` lies in `C^{m+1}`. -/
noncomputable def rhs64_STR02966 (m : ℕ) (h r : ℝ) (u : PerCm_STR02966 (m + 1)) :
    PerCm_STR02966 m :=
  P0CLM_STR02966 m
    ((3 * h) • mulCLM_STR02966 m (sin3_STR02966 m) (dCLM_STR02966 m u)
      - (1 / 2 : ℝ) • mulCLM_STR02966 m (dCLM_STR02966 m u) (dCLM_STR02966 m u)
      - r • inclCLM_STR02966 m u)

theorem rhs64_formula_STR02966 (m : ℕ) (h r : ℝ) (u : PerCm_STR02966 (m + 1)) (x : ℝ) :
    (rhs64_STR02966 m h r u).val x =
      (3 * h * Real.sin (3 * x) * deriv u.val x - 1 / 2 * (deriv u.val x) ^ 2 - r * u.val x) -
        meanCm_STR02966 (fun t => 3 * h * Real.sin (3 * t) * deriv u.val t
          - 1 / 2 * (deriv u.val t) ^ 2 - r * u.val t) := by
  have key : ((3 * h) • mulCLM_STR02966 m (sin3_STR02966 m) (dCLM_STR02966 m u)
      - (1 / 2 : ℝ) • mulCLM_STR02966 m (dCLM_STR02966 m u) (dCLM_STR02966 m u)
      - r • inclCLM_STR02966 m u).val =
        fun t => 3 * h * Real.sin (3 * t) * deriv u.val t
          - 1 / 2 * (deriv u.val t) ^ 2 - r * u.val t := by
    funext t
    simp only [PerCm_STR02966.val_sub, PerCm_STR02966.val_smul, mulCLM_val_STR02966,
      dCLM_val_STR02966, inclCLM_val_STR02966, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply,
      smul_eq_mul]
    show 3 * h * (Real.sin (3 * t) * deriv u.val t) - 1 / 2 * (deriv u.val t * deriv u.val t)
      - r * u.val t = _
    ring
  rw [rhs64_STR02966, P0CLM_val_STR02966]
  simp only [key]

theorem rhs64_norm_le_STR02966 (m : ℕ) (h r : ℝ) (u : PerCm_STR02966 (m + 1))
    (hu : meanCm_STR02966 u.val = 0) :
    ‖rhs64_STR02966 m h r u‖ ≤
      (|r| + 6 * |h| * 2 ^ m * S_STR02966 m) * ‖u‖ + 2 ^ m * ‖u‖ ^ 2 := by
  have hP0 : P0CLM_STR02966 m (inclCLM_STR02966 m u) = inclCLM_STR02966 m u := by
    apply PerCm_STR02966.ext
    show (fun x => u.val x - meanCm_STR02966 u.val) = u.val
    rw [hu]
    funext x
    simp
  have hrhs : rhs64_STR02966 m h r u =
      P0CLM_STR02966 m ((3 * h) • mulCLM_STR02966 m (sin3_STR02966 m) (dCLM_STR02966 m u)
        - (1 / 2 : ℝ) • mulCLM_STR02966 m (dCLM_STR02966 m u) (dCLM_STR02966 m u))
        - r • inclCLM_STR02966 m u := by
    unfold rhs64_STR02966
    rw [map_sub, map_smul, hP0]
  have hnu := norm_nonneg u
  have hS := sin3_norm_le_STR02966 m
  have hS0 := S_nonneg_STR02966 m
  have hD : ‖dCLM_STR02966 m u‖ ≤ ‖u‖ := by
    calc ‖dCLM_STR02966 m u‖ ≤ ‖dCLM_STR02966 m‖ * ‖u‖ := (dCLM_STR02966 m).le_opNorm u
      _ ≤ 1 * ‖u‖ := by gcongr; exact dCLM_norm_le_STR02966 m
      _ = ‖u‖ := one_mul _
  have hI : ‖inclCLM_STR02966 m u‖ ≤ ‖u‖ := by
    calc ‖inclCLM_STR02966 m u‖ ≤ ‖inclCLM_STR02966 m‖ * ‖u‖ := (inclCLM_STR02966 m).le_opNorm u
      _ ≤ 1 * ‖u‖ := by gcongr; exact inclCLM_norm_le_STR02966 m
      _ = ‖u‖ := one_mul _
  have hmul : ∀ a b : PerCm_STR02966 m,
      ‖mulCLM_STR02966 m a b‖ ≤ 2 ^ m * ‖a‖ * ‖b‖ := fun a b =>
    calc ‖mulCLM_STR02966 m a b‖ ≤ ‖mulCLM_STR02966 m‖ * ‖a‖ * ‖b‖ :=
          (mulCLM_STR02966 m).le_opNorm₂ a b
      _ ≤ 2 ^ m * ‖a‖ * ‖b‖ := by gcongr; exact mulCLM_norm_le_STR02966 m
  have hD0 := norm_nonneg (dCLM_STR02966 m u)
  have hp0 : (0 : ℝ) ≤ 2 ^ m := by positivity
  have hM1 : ‖mulCLM_STR02966 m (sin3_STR02966 m) (dCLM_STR02966 m u)‖ ≤ 2 ^ m * S_STR02966 m * ‖u‖ :=
    calc _ ≤ 2 ^ m * ‖sin3_STR02966 m‖ * ‖dCLM_STR02966 m u‖ := hmul _ _
      _ ≤ 2 ^ m * S_STR02966 m * ‖u‖ := by gcongr
  have hM2 : ‖mulCLM_STR02966 m (dCLM_STR02966 m u) (dCLM_STR02966 m u)‖ ≤ 2 ^ m * ‖u‖ * ‖u‖ :=
    calc _ ≤ 2 ^ m * ‖dCLM_STR02966 m u‖ * ‖dCLM_STR02966 m u‖ := hmul _ _
      _ ≤ 2 ^ m * ‖u‖ * ‖u‖ := by gcongr
  have hA : ‖(3 * h) • mulCLM_STR02966 m (sin3_STR02966 m) (dCLM_STR02966 m u)
        - (1 / 2 : ℝ) • mulCLM_STR02966 m (dCLM_STR02966 m u) (dCLM_STR02966 m u)‖ ≤
      3 * |h| * (2 ^ m * S_STR02966 m * ‖u‖) + 1 / 2 * (2 ^ m * ‖u‖ * ‖u‖) := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      gcongr
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      gcongr
  have hB : ‖r • inclCLM_STR02966 m u‖ ≤ |r| * ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    gcongr
  rw [hrhs]
  refine (norm_sub_le _ _).trans ?_
  have hP := (P0CLM_STR02966 m).le_opNorm ((3 * h) • mulCLM_STR02966 m (sin3_STR02966 m)
      (dCLM_STR02966 m u) - (1 / 2 : ℝ) • mulCLM_STR02966 m (dCLM_STR02966 m u)
      (dCLM_STR02966 m u))
  have hP2 := P0CLM_norm_le_STR02966 m
  have hA0 := norm_nonneg ((3 * h) • mulCLM_STR02966 m (sin3_STR02966 m)
      (dCLM_STR02966 m u) - (1 / 2 : ℝ) • mulCLM_STR02966 m (dCLM_STR02966 m u)
      (dCLM_STR02966 m u))
  have hP3 : ‖P0CLM_STR02966 m ((3 * h) • mulCLM_STR02966 m (sin3_STR02966 m)
      (dCLM_STR02966 m u) - (1 / 2 : ℝ) • mulCLM_STR02966 m (dCLM_STR02966 m u)
      (dCLM_STR02966 m u))‖ ≤ 2 * ‖(3 * h) • mulCLM_STR02966 m (sin3_STR02966 m)
      (dCLM_STR02966 m u) - (1 / 2 : ℝ) • mulCLM_STR02966 m (dCLM_STR02966 m u)
      (dCLM_STR02966 m u)‖ :=
    hP.trans (mul_le_mul_of_nonneg_right hP2 hA0)
  nlinarith [abs_nonneg h, abs_nonneg r]

/-! ### Smoothness of the right side in the parameters -/

theorem rhs64_contDiffOn_STR02966 (m : ℕ) {s : Set ℝ} {r : ℝ → ℝ}
    {u : ℝ → PerCm_STR02966 (m + 1)} (hr : ContDiffOn ℝ 3 r s) (hu : ContDiffOn ℝ 3 u s) :
    ContDiffOn ℝ 3 (fun h => rhs64_STR02966 m h (r h) (u h)) s := by
  have hDu : ContDiffOn ℝ 3 (fun h => dCLM_STR02966 m (u h)) s :=
    (dCLM_STR02966 m).contDiff.comp_contDiffOn hu
  have hI : ContDiffOn ℝ 3 (fun h => inclCLM_STR02966 m (u h)) s :=
    (inclCLM_STR02966 m).contDiff.comp_contDiffOn hu
  have hM1 : ContDiffOn ℝ 3
      (fun h => mulCLM_STR02966 m (sin3_STR02966 m) (dCLM_STR02966 m (u h))) s :=
    ((mulCLM_STR02966 m) (sin3_STR02966 m)).contDiff.comp_contDiffOn hDu
  have hM2 : ContDiffOn ℝ 3
      (fun h => mulCLM_STR02966 m (dCLM_STR02966 m (u h)) (dCLM_STR02966 m (u h))) s :=
    ((mulCLM_STR02966 m).contDiff.comp_contDiffOn hDu).clm_apply hDu
  have h3h : ContDiffOn ℝ 3 (fun h : ℝ => 3 * h) s :=
    (contDiff_const.mul contDiff_id).contDiffOn
  have hA := (h3h.smul hM1).sub ((contDiffOn_const (c := (1 / 2 : ℝ))).smul hM2)
  have hB := hA.sub (hr.smul hI)
  exact (P0CLM_STR02966 m).contDiff.comp_contDiffOn hB

/-! ### Public statements -/

/-- Differentiation `C^{m+1} → C^m` is the bounded linear map `dCLM_STR02966 m` of norm at most
`1`, acting by the pointwise derivative. -/
theorem str029_66_parameter_calculus_fixed_spatial_norm_deriv (m : ℕ) :
    (∀ f : PerCm_STR02966 (m + 1), (dCLM_STR02966 m f).val = deriv f.val) ∧
      ‖dCLM_STR02966 m‖ ≤ 1 :=
  ⟨fun _ => rfl, dCLM_norm_le_STR02966 m⟩

/-- The inclusion `C^{m+1} → C^m` is the bounded linear map `inclCLM_STR02966 m` of norm at most
`1`. -/
theorem str029_66_parameter_calculus_fixed_spatial_norm_incl (m : ℕ) :
    (∀ f : PerCm_STR02966 (m + 1), (inclCLM_STR02966 m f).val = f.val) ∧
      ‖inclCLM_STR02966 m‖ ≤ 1 :=
  ⟨fun _ => rfl, inclCLM_norm_le_STR02966 m⟩

/-- `P_0 f = f - ∫ f dm` on `C^m` is the bounded linear map `P0CLM_STR02966 m` of norm at most
`2`. -/
theorem str029_66_parameter_calculus_fixed_spatial_norm_P0 (m : ℕ) :
    (∀ f : PerCm_STR02966 m,
        (P0CLM_STR02966 m f).val = fun x => f.val x - meanCm_STR02966 f.val) ∧
      ‖P0CLM_STR02966 m‖ ≤ 2 :=
  ⟨fun _ => rfl, P0CLM_norm_le_STR02966 m⟩

/-- Pointwise multiplication on `C^m` is the bounded bilinear map `mulCLM_STR02966 m` of norm at
most `2^m`. -/
theorem str029_66_parameter_calculus_fixed_spatial_norm_mul (m : ℕ) :
    (∀ f g : PerCm_STR02966 m, (mulCLM_STR02966 m f g).val = f.val * g.val) ∧
      ‖mulCLM_STR02966 m‖ ≤ 2 ^ m :=
  ⟨fun _ _ => rfl, mulCLM_norm_le_STR02966 m⟩

/-- The pointwise formula for the right side:
`N(h, r, u) = P_0[3 h sin 3t · u' - u'^2 / 2 - r u]`. -/
theorem str029_66_parameter_calculus_fixed_spatial_norm_rhs_formula (m : ℕ) (h r : ℝ)
    (u : PerCm_STR02966 (m + 1)) (x : ℝ) :
    (rhs64_STR02966 m h r u).val x =
      (3 * h * Real.sin (3 * x) * deriv u.val x - 1 / 2 * (deriv u.val x) ^ 2 - r * u.val x) -
        meanCm_STR02966 (fun t => 3 * h * Real.sin (3 * t) * deriv u.val t
          - 1 / 2 * (deriv u.val t) ^ 2 - r * u.val t) :=
  rhs64_formula_STR02966 m h r u x

/-- If `r` is real `C^3` and `u` is `C^3` into `C^{m+1}` on a parameter set `s`, then the right
side is `C^3` into `C^m` on `s`. -/
theorem str029_66_parameter_calculus_fixed_spatial_norm_contDiffOn (m : ℕ) {s : Set ℝ}
    {r : ℝ → ℝ} {u : ℝ → PerCm_STR02966 (m + 1)} (hr : ContDiffOn ℝ 3 r s)
    (hu : ContDiffOn ℝ 3 u s) :
    ContDiffOn ℝ 3 (fun h => rhs64_STR02966 m h (r h) (u h)) s :=
  rhs64_contDiffOn_STR02966 m hr hu

/-- The `C^m` bound for a mean-zero `u`:
`‖N(h, r, u)‖ ≤ (|r| + 6 |h| 2^m S_m) ‖u‖ + 2^m ‖u‖^2`. -/
theorem str029_66_parameter_calculus_fixed_spatial_norm_bound (m : ℕ) (h r : ℝ)
    (u : PerCm_STR02966 (m + 1)) (hu : meanCm_STR02966 u.val = 0) :
    ‖rhs64_STR02966 m h r u‖ ≤
      (|r| + 6 * |h| * 2 ^ m * S_STR02966 m) * ‖u‖ + 2 ^ m * ‖u‖ ^ 2 :=
  rhs64_norm_le_STR02966 m h r u hu

/-- STR029.66: for each fixed `m`, differentiation `C^{m+1} → C^m` and `P_0` are bounded linear,
multiplication in `C^m` is bounded bilinear of norm at most `2^m`, and hence the right side of the
branch equation is `C^3` into `C^m` for every `C^3` family `u` into `C^{m+1}` (periodic, and
mean-zero for the bound) and every real `C^3` function `r`; moreover it obeys the displayed bound. -/
theorem str029_66_parameter_calculus_fixed_spatial_norm (m : ℕ) :
    ((∀ f : PerCm_STR02966 (m + 1), (dCLM_STR02966 m f).val = deriv f.val) ∧
        ‖dCLM_STR02966 m‖ ≤ 1) ∧
      ((∀ f : PerCm_STR02966 m,
          (P0CLM_STR02966 m f).val = fun x => f.val x - meanCm_STR02966 f.val) ∧
        ‖P0CLM_STR02966 m‖ ≤ 2) ∧
      ((∀ f g : PerCm_STR02966 m, (mulCLM_STR02966 m f g).val = f.val * g.val) ∧
        ‖mulCLM_STR02966 m‖ ≤ 2 ^ m) ∧
      (∀ (h r : ℝ) (u : PerCm_STR02966 (m + 1)) (x : ℝ),
        (rhs64_STR02966 m h r u).val x =
          (3 * h * Real.sin (3 * x) * deriv u.val x - 1 / 2 * (deriv u.val x) ^ 2
              - r * u.val x) -
            meanCm_STR02966 (fun t => 3 * h * Real.sin (3 * t) * deriv u.val t
              - 1 / 2 * (deriv u.val t) ^ 2 - r * u.val t)) ∧
      (∀ (s : Set ℝ) (r : ℝ → ℝ) (u : ℝ → PerCm_STR02966 (m + 1)),
        ContDiffOn ℝ 3 r s → ContDiffOn ℝ 3 u s →
          ContDiffOn ℝ 3 (fun h => rhs64_STR02966 m h (r h) (u h)) s) ∧
      (∀ (h r : ℝ) (u : PerCm_STR02966 (m + 1)), meanCm_STR02966 u.val = 0 →
        ‖rhs64_STR02966 m h r u‖ ≤
          (|r| + 6 * |h| * 2 ^ m * S_STR02966 m) * ‖u‖ + 2 ^ m * ‖u‖ ^ 2) :=
  ⟨str029_66_parameter_calculus_fixed_spatial_norm_deriv m,
    str029_66_parameter_calculus_fixed_spatial_norm_P0 m,
    str029_66_parameter_calculus_fixed_spatial_norm_mul m,
    fun h r u x => str029_66_parameter_calculus_fixed_spatial_norm_rhs_formula m h r u x,
    fun _ _ _ hr hu => str029_66_parameter_calculus_fixed_spatial_norm_contDiffOn m hr hu,
    fun h r u hu => str029_66_parameter_calculus_fixed_spatial_norm_bound m h r u hu⟩

end DGPS.Frontier.STR029
