import DGPS.Frontier.STR029.T53
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# STR029.13: Periodic right inverse of the range operator

Task id: STR029.13. Title: Periodic right inverse of the range operator (node STR029, size L).

Statement (specification): for `f ∈ Y` put `v(t) = ∫_0^t sin(t - s) f(s) ds`, `a = 2 ∫ v cos t dm`,
`b = 2 ∫ v sin t dm` and `w = v - a cos t - b sin t`. Then `w ∈ E` and `w'' + w = f`.

Provides (every declaration is in the namespace `DGPS.Frontier.STR029`):
* `DGPS.Frontier.STR029.str029_13_periodic_right_inverse_range_operator`: for every `[HolderExponent α]` and
  `f ∈ Y` (`InY_STR02913 α f`), the function `w = wRight_STR02913 f` lies in `E` (`InEspace_STR02913 α w`) and
  `w'' + w = f` pointwise.
* `DGPS.Frontier.STR029.str029_13_periodic_right_inverse_range_operator_half`: the same for the literal
  exponent `α = 1/2` of the specification.
* `DGPS.Frontier.STR029.str029_13_periodic_right_inverse_range_operator_periodic`: `v` and `v'` are `2π`-periodic,
  so the formula on `ℝ` is the periodic extension of `v|[0, 2π]`.
* `DGPS.Frontier.STR029.str029_13_periodic_right_inverse_range_operator_endpoints`: `v(0) = v'(0) = v(2π) = v'(2π) = 0`.
* `DGPS.Frontier.STR029.str029_13_periodic_right_inverse_range_operator_ode`: `v'' = f - v` pointwise, with
  `v' = ∫_0^t cos(t - s) f(s) ds`.
* `DGPS.Frontier.STR029.str029_13_periodic_right_inverse_range_operator_mean`: `∫ v dm = 0`.
* `DGPS.Frontier.STR029.InY_STR02913`, `DGPS.Frontier.STR029.InEspace_STR02913`: the carriers `Y` and `E`.
* `DGPS.Frontier.STR029.vRight_STR02913`, `aCoef_STR02913`, `bCoef_STR02913`, `wRight_STR02913`: `v`, `a`, `b`, `w`.

R5 notes:
* Carriers are the concrete ones of `.01` and `.53`, functions `ℝ → ℝ` in the variable `t = 2πx`. `Y` is
  `InY_STR02913 α f`: `IsC0Alpha_STR02953 α f` (`2π`-periodic with finite circular Hölder constant) together with
  `InE_STR02901 f` (`∫ f dm = ∫ f cos dm = ∫ f sin dm = 0`). `E` is `InEspace_STR02913 α w`:
  `IsC2Alpha_STR02901 α w` together with `InE_STR02901 w`. Haar integrals are `meanT_STR02901`
  (normalized interval integral over `[0, 2π]`). Neither carrier is a bundled normed space; membership is the
  predicate, as for `.53`.
* Exponent: the specification fixes `α = 1/2`. As in `.01` and `.53` the main theorem is proved for every
  `[HolderExponent α]` (`0 < α < 1`), which contains `α = 1/2`; the literal case is `_half`. This generalizes
  the exponent only and adds no hypothesis. Only `0 < α < 1` is used.
* `v` is defined by the interval integral `∫_0^t sin(t - s) f(s) ds` for every real `t` (reversed
  orientation for `t < 0`). The specification defines `v` on `[0, 2π]` and extends it periodically; the lemma
  `_periodic` shows that, for `f ∈ Y`, the formula is already `2π`-periodic, so the two readings agree on all
  of `ℝ`. The coefficients `a`, `b` use only values of `v` on `[0, 2π]` (through `meanT_STR02901`).
* `w'' + w = f` is read as `deriv (deriv w) t + w t = f t` for every real `t`, in the variable `t`.
  Membership `w ∈ C^{2,α}` is the concrete `IsC2Alpha_STR02901 α w` (periodic, twice differentiable with
  continuous second derivative of finite circular Hölder constant).
* Proof route: the Mathlib parameter-integral differentiation is avoided by the identity
  `sin(t - s) = sin t cos s - cos t sin s`, so `v = sin t C(t) - cos t S(t)` with the primitives
  `C(t) = ∫_0^t cos s f(s) ds`, `S(t) = ∫_0^t sin s f(s) ds`, differentiated by the fundamental theorem of
  calculus for continuous integrands. The orthogonality of `f` to `cos` and `sin` makes `C`, `S` periodic.
  The Hölder bound of `w'' = f - w` follows from the one of `f` and the Lipschitz bound of the periodic `C^1`
  function `w`.
* The statement of the specification takes `f ∈ Y`, a function of `C^{0,α}`; continuity of `f` is derived
  from the Hölder bound, not assumed.
-/

open DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.STR029

/-- The carrier `Y`: `C^{0,α}` functions orthogonal to `1`, `cos t`, `sin t`. -/
def InY_STR02913 (α : ℝ) (f : ℝ → ℝ) : Prop :=
  IsC0Alpha_STR02953 α f ∧ InE_STR02901 f

/-- The carrier `E`: `C^{2,α}` functions orthogonal to `1`, `cos t`, `sin t`. -/
def InEspace_STR02913 (α : ℝ) (w : ℝ → ℝ) : Prop :=
  IsC2Alpha_STR02901 α w ∧ InE_STR02901 w

/-- The primitive `t ↦ ∫_0^t g`. -/
noncomputable def prim_STR02913 (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, g s

/-- `v(t) = ∫_0^t sin(t - s) f(s) ds`. -/
noncomputable def vRight_STR02913 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, Real.sin (t - s) * f s

/-- The derivative `v'(t) = cos t C(t) + sin t S(t)` written through the primitives. -/
noncomputable def vDeriv_STR02913 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.cos t * prim_STR02913 (fun s => Real.cos s * f s) t +
    Real.sin t * prim_STR02913 (fun s => Real.sin s * f s) t

/-- The coefficient `a = 2 ∫ v cos t dm`. -/
noncomputable def aCoef_STR02913 (f : ℝ → ℝ) : ℝ :=
  2 * meanT_STR02901 (fun t => vRight_STR02913 f t * Real.cos t)

/-- The coefficient `b = 2 ∫ v sin t dm`. -/
noncomputable def bCoef_STR02913 (f : ℝ → ℝ) : ℝ :=
  2 * meanT_STR02901 (fun t => vRight_STR02913 f t * Real.sin t)

/-- `w = v - a cos t - b sin t`. -/
noncomputable def wRight_STR02913 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  vRight_STR02913 f t - aCoef_STR02913 f * Real.cos t - bCoef_STR02913 f * Real.sin t

/-- `w` with arbitrary coefficients. -/
noncomputable def wGen_STR02913 (f : ℝ → ℝ) (a b t : ℝ) : ℝ :=
  vRight_STR02913 f t - a * Real.cos t - b * Real.sin t

/-- The derivative of `wGen_STR02913`. -/
noncomputable def wGen1_STR02913 (f : ℝ → ℝ) (a b t : ℝ) : ℝ :=
  vDeriv_STR02913 f t + a * Real.sin t - b * Real.cos t

/-! ### Primitives -/

theorem prim_hasDerivAt_STR02913 {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ) :
    HasDerivAt (prim_STR02913 g) (g t) t :=
  (Continuous.integral_hasStrictDerivAt (a := 0) hg t).hasDerivAt

theorem prim_periodic_STR02913 {g : ℝ → ℝ} (hg : Continuous g)
    (hper : Function.Periodic g (2 * Real.pi)) (h0 : ∫ s in (0 : ℝ)..(2 * Real.pi), g s = 0) :
    Function.Periodic (prim_STR02913 g) (2 * Real.pi) := by
  intro t
  unfold prim_STR02913
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := MeasureTheory.volume) 0 t)
    (hg.intervalIntegrable (μ := MeasureTheory.volume) t (t + 2 * Real.pi))
  have h2 := hper.intervalIntegral_add_eq t 0
  rw [zero_add] at h2
  linarith

theorem integral_zero_of_meanT_STR02913 {g : ℝ → ℝ} (h : meanT_STR02901 g = 0) :
    ∫ s in (0 : ℝ)..(2 * Real.pi), g s = 0 := by
  unfold meanT_STR02901 at h
  rcases mul_eq_zero.1 h with h | h
  · exact absurd h (by positivity)
  · exact h

theorem vRight_eq_STR02913 {f : ℝ → ℝ} (hfc : Continuous f) (t : ℝ) :
    vRight_STR02913 f t = Real.sin t * prim_STR02913 (fun s => Real.cos s * f s) t -
      Real.cos t * prim_STR02913 (fun s => Real.sin s * f s) t := by
  unfold vRight_STR02913 prim_STR02913
  have e : ∀ s, Real.sin (t - s) * f s =
      Real.sin t * (Real.cos s * f s) - Real.cos t * (Real.sin s * f s) := by
    intro s; rw [Real.sin_sub]; ring
  simp only [e]
  rw [intervalIntegral.integral_sub ((by fun_prop : Continuous fun s => Real.sin t * (Real.cos s * f s)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun s => Real.cos t * (Real.sin s * f s)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem vRight_hasDerivAt_STR02913 {f : ℝ → ℝ} (hfc : Continuous f) (t : ℝ) :
    HasDerivAt (vRight_STR02913 f) (vDeriv_STR02913 f t) t ∧
      HasDerivAt (vDeriv_STR02913 f) (f t - vRight_STR02913 f t) t := by
  have hC := prim_hasDerivAt_STR02913 (g := fun s => Real.cos s * f s) (by fun_prop) t
  have hS := prim_hasDerivAt_STR02913 (g := fun s => Real.sin s * f s) (by fun_prop) t
  have hveq : vRight_STR02913 f = fun t => Real.sin t * prim_STR02913 (fun s => Real.cos s * f s) t -
      Real.cos t * prim_STR02913 (fun s => Real.sin s * f s) t := funext (vRight_eq_STR02913 hfc)
  refine ⟨?_, ?_⟩
  · rw [hveq]
    refine (((Real.hasDerivAt_sin t).mul hC).sub ((Real.hasDerivAt_cos t).mul hS)).congr_deriv ?_
    unfold vDeriv_STR02913
    ring
  · refine (((Real.hasDerivAt_cos t).mul hC).add ((Real.hasDerivAt_sin t).mul hS)).congr_deriv ?_
    rw [vRight_eq_STR02913 hfc t]
    linear_combination (f t) * Real.sin_sq_add_cos_sq t

theorem vRight_periodic_STR02913 {f : ℝ → ℝ} (hfc : Continuous f)
    (hfp : Function.Periodic f (2 * Real.pi)) (hf : InE_STR02901 f) :
    Function.Periodic (vRight_STR02913 f) (2 * Real.pi) ∧
      Function.Periodic (vDeriv_STR02913 f) (2 * Real.pi) := by
  have hc0 : ∫ s in (0 : ℝ)..(2 * Real.pi), Real.cos s * f s = 0 := by
    have := integral_zero_of_meanT_STR02913 hf.2.1
    simpa only [mul_comm] using this
  have hs0 : ∫ s in (0 : ℝ)..(2 * Real.pi), Real.sin s * f s = 0 := by
    have := integral_zero_of_meanT_STR02913 hf.2.2
    simpa only [mul_comm] using this
  have hcp : Function.Periodic (fun s => Real.cos s * f s) (2 * Real.pi) := fun s => by
    simp only [Real.cos_add_two_pi, hfp s]
  have hsp : Function.Periodic (fun s => Real.sin s * f s) (2 * Real.pi) := fun s => by
    simp only [Real.sin_add_two_pi, hfp s]
  have hC := prim_periodic_STR02913 (by fun_prop) hcp hc0
  have hS := prim_periodic_STR02913 (by fun_prop) hsp hs0
  refine ⟨fun t => ?_, fun t => ?_⟩
  · rw [vRight_eq_STR02913 hfc, vRight_eq_STR02913 hfc, Real.sin_add_two_pi, Real.cos_add_two_pi,
      hC t, hS t]
  · unfold vDeriv_STR02913
    rw [Real.sin_add_two_pi, Real.cos_add_two_pi, hC t, hS t]

theorem vRight_mean_STR02913 {f : ℝ → ℝ} (hfc : Continuous f)
    (hfp : Function.Periodic f (2 * Real.pi)) (hf : InE_STR02901 f) :
    meanT_STR02901 (vRight_STR02913 f) = 0 := by
  have hper := (vRight_periodic_STR02913 hfc hfp hf).2
  have hv : Continuous (vRight_STR02913 f) :=
    continuous_iff_continuousAt.2 fun t => (vRight_hasDerivAt_STR02913 hfc t).1.continuousAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 2 * Real.pi)
    (f := vDeriv_STR02913 f) (f' := fun t => f t - vRight_STR02913 f t)
    (fun x _ => (vRight_hasDerivAt_STR02913 hfc x).2)
    ((hfc.sub hv).intervalIntegrable _ _)
  have h2 := hper 0
  rw [zero_add] at h2
  rw [h2, sub_self, intervalIntegral.integral_sub (hfc.intervalIntegrable _ _)
    (hv.intervalIntegrable _ _)] at hFTC
  have hf0 := integral_zero_of_meanT_STR02913 hf.1
  rw [hf0] at hFTC
  have hI : ∫ s in (0 : ℝ)..(2 * Real.pi), vRight_STR02913 f s = 0 := by linarith
  unfold meanT_STR02901
  rw [hI, mul_zero]

/-! ### Trigonometric integrals over one period -/

theorem I_cos_STR02913 : ∫ t in (0 : ℝ)..(2 * Real.pi), Real.cos t = 0 := by
  rw [integral_cos]; simp

theorem I_sin_STR02913 : ∫ t in (0 : ℝ)..(2 * Real.pi), Real.sin t = 0 := by
  rw [integral_sin]; simp

theorem I_cc_STR02913 : ∫ t in (0 : ℝ)..(2 * Real.pi), Real.cos t * Real.cos t = Real.pi := by
  simp only [← sq]
  rw [integral_cos_sq]; simp

theorem I_ss_STR02913 : ∫ t in (0 : ℝ)..(2 * Real.pi), Real.sin t * Real.sin t = Real.pi := by
  simp only [← sq]
  rw [integral_sin_sq]; simp

theorem I_sc_STR02913 : ∫ t in (0 : ℝ)..(2 * Real.pi), Real.sin t * Real.cos t = 0 := by
  rw [integral_sin_mul_cos₁]; simp

theorem I_cs_STR02913 : ∫ t in (0 : ℝ)..(2 * Real.pi), Real.cos t * Real.sin t = 0 := by
  simpa only [mul_comm] using I_sc_STR02913

/-- Mean of the corrected function. -/
theorem meanT_wGen_STR02913 {v : ℝ → ℝ} (hv : Continuous v) (a b : ℝ) :
    meanT_STR02901 (fun t => v t - a * Real.cos t - b * Real.sin t) = meanT_STR02901 v := by
  unfold meanT_STR02901
  rw [intervalIntegral.integral_sub ((by fun_prop : Continuous fun t => v t - a * Real.cos t).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t => b * Real.sin t).intervalIntegrable _ _),
    intervalIntegral.integral_sub (hv.intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t => a * Real.cos t).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, I_cos_STR02913,
    I_sin_STR02913]
  ring

theorem meanT_wGen_cos_STR02913 {v : ℝ → ℝ} (hv : Continuous v) (a b : ℝ) :
    meanT_STR02901 (fun t => (v t - a * Real.cos t - b * Real.sin t) * Real.cos t) =
      meanT_STR02901 (fun t => v t * Real.cos t) - (2 * Real.pi)⁻¹ * (a * Real.pi) := by
  unfold meanT_STR02901
  have e : ∀ t, (v t - a * Real.cos t - b * Real.sin t) * Real.cos t =
      (v t * Real.cos t - a * (Real.cos t * Real.cos t)) - b * (Real.sin t * Real.cos t) := by
    intro t; ring
  simp only [e]
  rw [intervalIntegral.integral_sub ((by fun_prop : Continuous fun t => v t * Real.cos t - a * (Real.cos t * Real.cos t)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t => b * (Real.sin t * Real.cos t)).intervalIntegrable _ _),
    intervalIntegral.integral_sub ((by fun_prop : Continuous fun t => v t * Real.cos t).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t => a * (Real.cos t * Real.cos t)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, I_cc_STR02913,
    I_sc_STR02913]
  ring

theorem meanT_wGen_sin_STR02913 {v : ℝ → ℝ} (hv : Continuous v) (a b : ℝ) :
    meanT_STR02901 (fun t => (v t - a * Real.cos t - b * Real.sin t) * Real.sin t) =
      meanT_STR02901 (fun t => v t * Real.sin t) - (2 * Real.pi)⁻¹ * (b * Real.pi) := by
  unfold meanT_STR02901
  have e : ∀ t, (v t - a * Real.cos t - b * Real.sin t) * Real.sin t =
      (v t * Real.sin t - a * (Real.cos t * Real.sin t)) - b * (Real.sin t * Real.sin t) := by
    intro t; ring
  simp only [e]
  rw [intervalIntegral.integral_sub ((by fun_prop : Continuous fun t => v t * Real.sin t - a * (Real.cos t * Real.sin t)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t => b * (Real.sin t * Real.sin t)).intervalIntegrable _ _),
    intervalIntegral.integral_sub ((by fun_prop : Continuous fun t => v t * Real.sin t).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t => a * (Real.cos t * Real.sin t)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, I_cs_STR02913,
    I_ss_STR02913]
  ring

/-! ### Derivatives of `w` -/

theorem wGen_hasDerivAt_STR02913 {f : ℝ → ℝ} (hfc : Continuous f) (a b t : ℝ) :
    HasDerivAt (wGen_STR02913 f a b) (wGen1_STR02913 f a b t) t ∧
      HasDerivAt (wGen1_STR02913 f a b) (f t - wGen_STR02913 f a b t) t := by
  obtain ⟨h1, h2⟩ := vRight_hasDerivAt_STR02913 hfc t
  refine ⟨?_, ?_⟩
  · refine (h1.sub ((Real.hasDerivAt_cos t).const_mul a)).sub
      ((Real.hasDerivAt_sin t).const_mul b) |>.congr_deriv ?_
    unfold wGen1_STR02913
    ring
  · refine (h2.add ((Real.hasDerivAt_sin t).const_mul a)).sub
      ((Real.hasDerivAt_cos t).const_mul b) |>.congr_deriv ?_
    unfold wGen_STR02913
    ring

theorem deriv_wGen_STR02913 {f : ℝ → ℝ} (hfc : Continuous f) (a b : ℝ) :
    deriv (wGen_STR02913 f a b) = wGen1_STR02913 f a b ∧
      deriv (wGen1_STR02913 f a b) = fun t => f t - wGen_STR02913 f a b t := by
  refine ⟨funext fun t => (wGen_hasDerivAt_STR02913 hfc a b t).1.deriv,
    funext fun t => (wGen_hasDerivAt_STR02913 hfc a b t).2.deriv⟩

theorem wGen_periodic_STR02913 {f : ℝ → ℝ} (hv : Function.Periodic (vRight_STR02913 f) (2 * Real.pi))
    (a b : ℝ) : Function.Periodic (wGen_STR02913 f a b) (2 * Real.pi) := fun t => by
  unfold wGen_STR02913
  rw [hv t, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem wGen1_periodic_STR02913 {f : ℝ → ℝ} (hv : Function.Periodic (vDeriv_STR02913 f) (2 * Real.pi))
    (a b : ℝ) : Function.Periodic (wGen1_STR02913 f a b) (2 * Real.pi) := fun t => by
  unfold wGen1_STR02913
  rw [hv t, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-! ### Public statements -/

theorem str029_13_periodic_right_inverse_range_operator_periodic {α : ℝ} [HolderExponent α]
    {f : ℝ → ℝ} (hf : InY_STR02913 α f) :
    Function.Periodic (vRight_STR02913 f) (2 * Real.pi) ∧
      Function.Periodic (vDeriv_STR02913 f) (2 * Real.pi) :=
  vRight_periodic_STR02913 (continuous_of_circHolderBdd_STR02953 HolderExponent.pos hf.1.2) hf.1.1 hf.2

theorem str029_13_periodic_right_inverse_range_operator_ode {α : ℝ} [HolderExponent α]
    {f : ℝ → ℝ} (hf : InY_STR02913 α f) :
    deriv (vRight_STR02913 f) = vDeriv_STR02913 f ∧
      deriv (deriv (vRight_STR02913 f)) = (fun t => f t - vRight_STR02913 f t) ∧
      ∀ t, vDeriv_STR02913 f t = ∫ s in (0 : ℝ)..t, Real.cos (t - s) * f s := by
  have hfc := continuous_of_circHolderBdd_STR02953 HolderExponent.pos hf.1.2
  have h1 : deriv (vRight_STR02913 f) = vDeriv_STR02913 f :=
    funext fun t => (vRight_hasDerivAt_STR02913 hfc t).1.deriv
  refine ⟨h1, ?_, fun t => ?_⟩
  · rw [h1]
    exact funext fun t => (vRight_hasDerivAt_STR02913 hfc t).2.deriv
  · unfold vDeriv_STR02913 prim_STR02913
    have e : ∀ s, Real.cos (t - s) * f s =
        Real.cos t * (Real.cos s * f s) + Real.sin t * (Real.sin s * f s) := by
      intro s; rw [Real.cos_sub]; ring
    simp only [e]
    rw [intervalIntegral.integral_add ((by fun_prop : Continuous fun s => Real.cos t * (Real.cos s * f s)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun s => Real.sin t * (Real.sin s * f s)).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem str029_13_periodic_right_inverse_range_operator_endpoints {α : ℝ} [HolderExponent α]
    {f : ℝ → ℝ} (hf : InY_STR02913 α f) :
    vRight_STR02913 f 0 = 0 ∧ deriv (vRight_STR02913 f) 0 = 0 ∧
      vRight_STR02913 f (2 * Real.pi) = 0 ∧ deriv (vRight_STR02913 f) (2 * Real.pi) = 0 := by
  obtain ⟨hvp, hdp⟩ := str029_13_periodic_right_inverse_range_operator_periodic hf
  obtain ⟨hd, -, -⟩ := str029_13_periodic_right_inverse_range_operator_ode hf
  have hfc := continuous_of_circHolderBdd_STR02953 HolderExponent.pos hf.1.2
  have v0 : vRight_STR02913 f 0 = 0 := by simp [vRight_STR02913]
  have d0 : vDeriv_STR02913 f 0 = 0 := by simp [vDeriv_STR02913, prim_STR02913]
  have v1 := hvp 0
  have d1 := hdp 0
  rw [zero_add] at v1 d1
  rw [hd]
  exact ⟨v0, d0, by rw [v1, v0], by rw [d1, d0]⟩

theorem str029_13_periodic_right_inverse_range_operator_mean {α : ℝ} [HolderExponent α]
    {f : ℝ → ℝ} (hf : InY_STR02913 α f) : meanT_STR02901 (vRight_STR02913 f) = 0 :=
  vRight_mean_STR02913 (continuous_of_circHolderBdd_STR02953 HolderExponent.pos hf.1.2) hf.1.1 hf.2

/-- Main statement: `w ∈ E` and `w'' + w = f`. -/
theorem str029_13_periodic_right_inverse_range_operator {α : ℝ} [HolderExponent α]
    {f : ℝ → ℝ} (hf : InY_STR02913 α f) :
    InEspace_STR02913 α (wRight_STR02913 f) ∧
      ∀ t, deriv (deriv (wRight_STR02913 f)) t + wRight_STR02913 f t = f t := by
  have hα := HolderExponent.pos (α := α)
  have hα1 := HolderExponent.lt_one (α := α)
  have hfc := continuous_of_circHolderBdd_STR02953 hα hf.1.2
  obtain ⟨hvp, hdp⟩ := str029_13_periodic_right_inverse_range_operator_periodic hf
  have hmean := str029_13_periodic_right_inverse_range_operator_mean hf
  set a := aCoef_STR02913 f with ha
  set b := bCoef_STR02913 f with hb
  have hw : wRight_STR02913 f = wGen_STR02913 f a b := rfl
  obtain ⟨hd1, hd2⟩ := deriv_wGen_STR02913 hfc a b
  have hv : Continuous (vRight_STR02913 f) :=
    continuous_iff_continuousAt.2 fun t => (vRight_hasDerivAt_STR02913 hfc t).1.continuousAt
  have hwc : Continuous (wGen_STR02913 f a b) :=
    continuous_iff_continuousAt.2 fun t => (wGen_hasDerivAt_STR02913 hfc a b t).1.continuousAt
  have hw1c : Continuous (wGen1_STR02913 f a b) :=
    continuous_iff_continuousAt.2 fun t => (wGen_hasDerivAt_STR02913 hfc a b t).2.continuousAt
  have hdd : deriv (deriv (wGen_STR02913 f a b)) = f + (-1 : ℝ) • wGen_STR02913 f a b := by
    rw [hd1, hd2]
    funext t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hwper := wGen_periodic_STR02913 hvp a b
  have hw1per := wGen1_periodic_STR02913 hdp a b
  have hbdd : Bdd (deriv (wGen_STR02913 f a b)) := by
    rw [hd1]; exact bdd_of_periodic_continuous_STR02953 hw1per hw1c
  have hwC0 := (c0_of_deriv_STR02953 hα hα1.le hwper
    (fun t => (wGen_hasDerivAt_STR02913 hfc a b t).1.differentiableAt) hbdd).1
  have hC2 : IsC2Alpha_STR02901 α (wGen_STR02913 f a b) := by
    refine ⟨hwper, fun t => (wGen_hasDerivAt_STR02913 hfc a b t).1.differentiableAt, ?_, ?_, ?_⟩
    · rw [hd1]
      exact fun t => (wGen_hasDerivAt_STR02913 hfc a b t).2.differentiableAt
    · rw [hdd]
      exact (hfc.add (continuous_const.mul hwc))
    · rw [hdd]
      exact (c0_add_STR02953 hα hf.1 (c0_smul_STR02953 hα (-1) hwC0).1).1.2
  have hEw : InE_STR02901 (wGen_STR02913 f a b) := by
    refine ⟨?_, ?_, ?_⟩
    · exact (meanT_wGen_STR02913 hv a b).trans hmean
    · have := meanT_wGen_cos_STR02913 hv a b
      show meanT_STR02901 (fun t => (vRight_STR02913 f t - a * Real.cos t - b * Real.sin t) *
        Real.cos t) = 0
      rw [this, ha]
      unfold aCoef_STR02913
      field_simp
      ring
    · have := meanT_wGen_sin_STR02913 hv a b
      show meanT_STR02901 (fun t => (vRight_STR02913 f t - a * Real.cos t - b * Real.sin t) *
        Real.sin t) = 0
      rw [this, hb]
      unfold bCoef_STR02913
      field_simp
      ring
  rw [hw]
  refine ⟨⟨hC2, hEw⟩, fun t => ?_⟩
  rw [hdd]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The same statement for the literal exponent `α = 1/2` of the specification. -/
theorem str029_13_periodic_right_inverse_range_operator_half {f : ℝ → ℝ}
    (hf : InY_STR02913 (1 / 2 : ℝ) f) :
    InEspace_STR02913 (1 / 2 : ℝ) (wRight_STR02913 f) ∧
      ∀ t, deriv (deriv (wRight_STR02913 f)) t + wRight_STR02913 f t = f t := by
  have : HolderExponent (1 / 2 : ℝ) := holderExponent_half_STR02901
  exact str029_13_periodic_right_inverse_range_operator hf

end DGPS.Frontier.STR029
