import DGPS.Analysis.PeriodicHolder
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# STR029.65: Bounded inverse of the second derivative

Task id: STR029.65 (node STR029), "Bounded inverse of the second derivative".

Statement (specification): for every integer `m ≥ 0` there is one compatible linear operator `B` from
mean-zero periodic `C^m` functions to mean-zero periodic `C^{m+2}` functions such that `(B f)'' = f` and
`‖B f‖_{C^{m+2}} ≤ (16π² + 4π + 1) ‖f‖_{C^m}`, where `‖f‖_{C^m} = ∑_{j=0}^m ‖f^{(j)}‖∞`. The mean-zero
periodic solution is unique.

Provides (every declaration is in the namespace `DGPS.Frontier.STR029`):
* `DGPS.Frontier.STR029.str029_65_bounded_inverse_second_derivative`: the main theorem. For every
  `m : ℕ` there is a linear map `B` from `meanZeroPerC_STR02965 m` to `meanZeroPerC_STR02965 (m + 2)`
  with `(B f)'' = f`, the bound `‖B f‖_{C^{m+2}} ≤ (16π² + 4π + 1) ‖f‖_{C^m}`, uniqueness of the
  mean-zero periodic `C²` solution of `v'' = f` (it equals `B f`), and `B f = invD2_STR02965 f` (the one
  formula of the proof, which does not depend on `m`).
* `DGPS.Frontier.STR029.str029_65_bounded_inverse_second_derivative_unique`: two mean-zero periodic
  `C²` functions with the same second derivative are equal.
* `DGPS.Frontier.STR029.str029_65_bounded_inverse_second_derivative_compatible`: for `m ≤ n`, any
  right inverses `B₁` (on `C^m`) and `B₂` (on `C^n`) of the second derivative agree on `C^n`.
* `DGPS.Frontier.STR029.meanZeroPerC_STR02965`: the carrier, the `ℝ`-submodule of `ℝ → ℝ` of
  `2π`-periodic `C^m` functions with Haar mean zero.
* `DGPS.Frontier.STR029.cmNorm_STR02965`: the norm `∑_{j=0}^m ‖f^{(j)}‖∞` of the specification.
* `DGPS.Frontier.STR029.meanT_STR02965`: the normalized period integral `∫ f dm`, `m(dt) = dt/(2π)`.
* `DGPS.Frontier.STR029.invD2_STR02965`: the explicit formula `B f = v - mean v` of the proof.
* `DGPS.Frontier.STR029.prim_STR02965`, `DGPS.Frontier.STR029.firstPrim_STR02965`: the primitive
  `F(t) = ∫_0^t f` and the centred primitive `F - a` (equal to `(B f)'`).

R5 notes:
* Carriers and variable. The specification fixes the angle `t = 2πx` with `a₀ = 4π²` and `m(dt) = dt/(2π)`,
  and says that until `.01` is checked all analytic tasks use concrete `2π`-periodic functions and
  normalized Lebesgue integrals. So the carrier is the set of functions `ℝ → ℝ` with
  `Function.Periodic f (2π)`, `ContDiff ℝ m f` and `meanT_STR02965 f = 0`; nothing about the optimizer
  chart, `Par`, `Wsp`, `AbsoluteDensity`, entropy, Fisher information or the angular-to-physical rate
  normalization enters this purely analytic task. Periodic Sobolev infrastructure is not used.
* The carrier is packaged as a `Submodule ℝ (ℝ → ℝ)` so that "linear operator from ... to ..." is a
  genuine `LinearMap` between the two carriers. The carriers carry no topology; "bounded" is the explicit
  norm inequality of the statement, with the literal constant `16π² + 4π + 1` (equal to `4L² + 2L + 1`,
  `L = 2π`).
* Mean. `meanT_STR02965 f = (2π)⁻¹ ∫_0^{2π} f` is the same expression as `meanT_STR02901` of `.01`; it is
  restated here (with the interval integral) because `.01` pulls in the whole optimizer development.
  "Mean-zero" is `meanT_STR02965 f = 0`.
* Norm. `‖f‖_{C^m}` is `∑ j ∈ range (m+1), supNorm (iteratedDeriv j f)` with the campaign's
  `DGPS.Analysis.PeriodicHolder.supNorm` (`⨆ x, |g x|`, value `0` for unbounded functions). On the carriers
  every `f^{(j)}` with `j ≤ m` is continuous and periodic, hence bounded, so that junk value is never used.
  Derivatives are `iteratedDeriv`; the second derivative in the conclusion is `deriv (deriv _)`, as in
  `.01`, `.14` and `.69`.
* "One compatible linear operator" is read as follows. For each `m` the operator `B` is a linear map
  between the stated carriers, and it is the restriction of one function-level formula that does not depend
  on `m`: the main theorem asserts `B f = invD2_STR02965 f` for all `f`, which is the specification's
  closing remark "the formula does not depend on `m`". The separate lemma `..._compatible` expresses
  compatibility without the formula: right inverses for `m ≤ n` coincide on `C^n ⊆ C^m`.
* Uniqueness is stated for the larger class of mean-zero `2π`-periodic functions `v` that are `C²` with
  `v'' = f` (a `C^{m+2}` function is `C²`), so it also covers solutions known to be only `C²`, as needed in
  the bootstrap of `.67`. This strengthens the literal "mean-zero periodic solution" (in the carrier) and
  adds no hypothesis. No condition on `f` beyond membership in the carrier is used.
* Construction. `B f = v - mean v` with `F(t) = ∫_0^t f`, `a = mean F`, `v(t) = ∫_0^t (F - a)`, as in the
  written proof (interval integrals; the Mathlib convention for non-integrable integrands is never used,
  since every integrand is continuous). Linearity of `B` is derived from uniqueness (both `B(f + g)` and
  `B f + B g` are mean-zero periodic `C²` solutions), not from integral manipulations; this changes only
  the route.
* The cases `m = 0` and higher use the same proof; the tail of the norm uses
  `(B f)^{(j+2)} = f^{(j)}`, obtained from `iteratedDeriv_succ'`.
-/

open Function DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.STR029

/-! ### Definitions -/

/-- The normalized period integral `∫ f dm`, `m(dt) = dt / (2π)`. -/
noncomputable def meanT_STR02965 (f : ℝ → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..(2 * Real.pi), f t

/-- The primitive `F(t) = ∫_0^t f`. -/
noncomputable def prim_STR02965 (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, f s

/-- The centred primitive `F - a`, `a = mean F`; it is `(B f)'`. -/
noncomputable def firstPrim_STR02965 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  prim_STR02965 f t - meanT_STR02965 (prim_STR02965 f)

/-- The formula `B f = v - mean v` with `v(t) = ∫_0^t (F - a)`. -/
noncomputable def invD2_STR02965 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  prim_STR02965 (firstPrim_STR02965 f) t -
    meanT_STR02965 (prim_STR02965 (firstPrim_STR02965 f))

/-- The norm `‖f‖_{C^m} = ∑_{j=0}^m ‖f^{(j)}‖∞`. -/
noncomputable def cmNorm_STR02965 (m : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), supNorm (iteratedDeriv j f)

/-! ### The normalized period integral -/

theorem meanT_add_STR02965 {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    meanT_STR02965 (f + g) = meanT_STR02965 f + meanT_STR02965 g := by
  unfold meanT_STR02965
  have h := intervalIntegral.integral_add (μ := MeasureTheory.volume) (a := 0) (b := 2 * Real.pi)
    (hf.intervalIntegrable 0 (2 * Real.pi)) (hg.intervalIntegrable 0 (2 * Real.pi))
  simp only [Pi.add_apply]
  rw [h, mul_add]

theorem meanT_smul_STR02965 (c : ℝ) (f : ℝ → ℝ) :
    meanT_STR02965 (c • f) = c * meanT_STR02965 f := by
  unfold meanT_STR02965
  simp only [Pi.smul_apply, smul_eq_mul, intervalIntegral.integral_const_mul]
  ring

theorem periodic_smul_STR02965 (c : ℝ) {f : ℝ → ℝ} {T : ℝ} (hf : Periodic f T) :
    Periodic (c • f) T := fun x => by
  show c • f (x + T) = c • f x
  rw [hf x]

theorem meanT_const_STR02965 (c : ℝ) : meanT_STR02965 (fun _ => c) = c := by
  unfold meanT_STR02965
  have h : (2 * Real.pi) ≠ 0 := Real.two_pi_pos.ne'
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp

theorem integral_eq_zero_of_meanT_STR02965 {g : ℝ → ℝ} (h : meanT_STR02965 g = 0) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), g t = 0 :=
  (mul_eq_zero.1 h).resolve_left (inv_ne_zero Real.two_pi_pos.ne')

/-- The mean of a constant shift. -/
theorem meanT_shift_STR02965 {w : ℝ → ℝ} (hw : Continuous w) (c : ℝ) :
    meanT_STR02965 (fun t => w t + c) = meanT_STR02965 w + c := by
  have h : (fun t => w t + c) = w + (fun _ => c) := rfl
  rw [h, meanT_add_STR02965 hw continuous_const, meanT_const_STR02965]

theorem meanT_sub_self_STR02965 {g : ℝ → ℝ} (hg : Continuous g) :
    meanT_STR02965 (fun t => g t - meanT_STR02965 g) = 0 := by
  have h : (fun t => g t - meanT_STR02965 g) = fun t => g t + (-meanT_STR02965 g) := by
    funext t
    rw [sub_eq_add_neg]
  rw [h, meanT_shift_STR02965 hg]
  ring

theorem meanT_abs_le_STR02965 {g : ℝ → ℝ} {M : ℝ} (hM : ∀ x, |g x| ≤ M) :
    |meanT_STR02965 g| ≤ M := by
  unfold meanT_STR02965
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
    (f := g) (C := M) (fun x _ => by rw [Real.norm_eq_abs]; exact hM x)
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos Real.two_pi_pos] at h
  rw [abs_mul, abs_inv, abs_of_pos Real.two_pi_pos]
  calc (2 * Real.pi)⁻¹ * |∫ t in (0 : ℝ)..(2 * Real.pi), g t|
      ≤ (2 * Real.pi)⁻¹ * (M * (2 * Real.pi)) := by gcongr
    _ = M := by field_simp

/-! ### The primitive -/

theorem prim_hasDerivAt_STR02965 {f : ℝ → ℝ} (hc : Continuous f) (t : ℝ) :
    HasDerivAt (prim_STR02965 f) (f t) t :=
  (hc.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem prim_continuous_STR02965 {f : ℝ → ℝ} (hc : Continuous f) :
    Continuous (prim_STR02965 f) :=
  continuous_iff_continuousAt.2 fun t => (prim_hasDerivAt_STR02965 hc t).continuousAt

theorem prim_periodic_STR02965 {f : ℝ → ℝ} (hc : Continuous f) (hp : Periodic f (2 * Real.pi))
    (h0 : ∫ s in (0 : ℝ)..(2 * Real.pi), f s = 0) : Periodic (prim_STR02965 f) (2 * Real.pi) := by
  intro t
  unfold prim_STR02965
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume) (a := 0) (b := t)
    (c := t + 2 * Real.pi) (f := f) (hc.intervalIntegrable 0 t)
    (hc.intervalIntegrable t (t + 2 * Real.pi))
  have h2 := hp.intervalIntegral_add_eq t 0
  rw [zero_add] at h2
  rw [← h1, h2, h0, add_zero]

/-- A bound on one period of a periodic function holds everywhere. -/
theorem periodic_bound_STR02965 {G : ℝ → ℝ} (hper : Periodic G (2 * Real.pi)) {B : ℝ}
    (h : ∀ t ∈ Set.Icc 0 (2 * Real.pi), |G t| ≤ B) (t : ℝ) : |G t| ≤ B := by
  obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ico₀ Real.two_pi_pos t
  rw [hxy]
  exact h y (Set.Ico_subset_Icc_self hy)

theorem prim_abs_le_STR02965 {f : ℝ → ℝ} (hc : Continuous f) (hp : Periodic f (2 * Real.pi))
    (h0 : ∫ s in (0 : ℝ)..(2 * Real.pi), f s = 0) {M : ℝ} (hM : ∀ x, |f x| ≤ M) (t : ℝ) :
    |prim_STR02965 f t| ≤ 2 * Real.pi * M := by
  refine periodic_bound_STR02965 (prim_periodic_STR02965 hc hp h0) (fun s hs => ?_) t
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := s)
    (f := f) (C := M) (fun x _ => by rw [Real.norm_eq_abs]; exact hM x)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs.1] at h
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  calc |prim_STR02965 f s| ≤ M * s := h
    _ ≤ M * (2 * Real.pi) := mul_le_mul_of_nonneg_left hs.2 hM0
    _ = 2 * Real.pi * M := by ring

/-! ### The centred primitive and the inverse -/

theorem firstPrim_hasDerivAt_STR02965 {f : ℝ → ℝ} (hc : Continuous f) (t : ℝ) :
    HasDerivAt (firstPrim_STR02965 f) (f t) t :=
  (prim_hasDerivAt_STR02965 hc t).sub_const _

theorem firstPrim_continuous_STR02965 {f : ℝ → ℝ} (hc : Continuous f) :
    Continuous (firstPrim_STR02965 f) :=
  (prim_continuous_STR02965 hc).sub continuous_const

theorem firstPrim_periodic_STR02965 {f : ℝ → ℝ} (hc : Continuous f)
    (hp : Periodic f (2 * Real.pi)) (h0 : meanT_STR02965 f = 0) :
    Periodic (firstPrim_STR02965 f) (2 * Real.pi) := by
  intro t
  unfold firstPrim_STR02965
  rw [prim_periodic_STR02965 hc hp (integral_eq_zero_of_meanT_STR02965 h0) t]

theorem firstPrim_abs_le_STR02965 {f : ℝ → ℝ} (hc : Continuous f) (hp : Periodic f (2 * Real.pi))
    (h0 : meanT_STR02965 f = 0) {M : ℝ} (hM : ∀ x, |f x| ≤ M) (t : ℝ) :
    |firstPrim_STR02965 f t| ≤ 2 * (2 * Real.pi * M) := by
  have h1 := prim_abs_le_STR02965 hc hp (integral_eq_zero_of_meanT_STR02965 h0) hM
  have h2 := meanT_abs_le_STR02965 (g := prim_STR02965 f) (M := 2 * Real.pi * M) h1
  unfold firstPrim_STR02965
  calc |prim_STR02965 f t - meanT_STR02965 (prim_STR02965 f)|
      ≤ |prim_STR02965 f t| + |meanT_STR02965 (prim_STR02965 f)| := abs_sub _ _
    _ ≤ 2 * Real.pi * M + 2 * Real.pi * M := add_le_add (h1 t) h2
    _ = 2 * (2 * Real.pi * M) := by ring

theorem invD2_hasDerivAt_STR02965 {f : ℝ → ℝ} (hc : Continuous f) (t : ℝ) :
    HasDerivAt (invD2_STR02965 f) (firstPrim_STR02965 f t) t :=
  (prim_hasDerivAt_STR02965 (firstPrim_continuous_STR02965 hc) t).sub_const _

theorem deriv_invD2_STR02965 {f : ℝ → ℝ} (hc : Continuous f) :
    deriv (invD2_STR02965 f) = firstPrim_STR02965 f :=
  funext fun t => (invD2_hasDerivAt_STR02965 hc t).deriv

theorem deriv_firstPrim_STR02965 {f : ℝ → ℝ} (hc : Continuous f) :
    deriv (firstPrim_STR02965 f) = f :=
  funext fun t => (firstPrim_hasDerivAt_STR02965 hc t).deriv

theorem deriv_deriv_invD2_STR02965 {f : ℝ → ℝ} (hc : Continuous f) :
    deriv (deriv (invD2_STR02965 f)) = f := by
  rw [deriv_invD2_STR02965 hc, deriv_firstPrim_STR02965 hc]

theorem invD2_continuous_STR02965 {f : ℝ → ℝ} (hc : Continuous f) :
    Continuous (invD2_STR02965 f) :=
  (prim_continuous_STR02965 (firstPrim_continuous_STR02965 hc)).sub continuous_const

theorem firstPrim_integral_STR02965 {f : ℝ → ℝ} (hc : Continuous f) :
    ∫ s in (0 : ℝ)..(2 * Real.pi), firstPrim_STR02965 f s = 0 :=
  integral_eq_zero_of_meanT_STR02965 (meanT_sub_self_STR02965 (prim_continuous_STR02965 hc))

theorem invD2_periodic_STR02965 {f : ℝ → ℝ} (hc : Continuous f) (hp : Periodic f (2 * Real.pi))
    (h0 : meanT_STR02965 f = 0) : Periodic (invD2_STR02965 f) (2 * Real.pi) := by
  intro t
  unfold invD2_STR02965
  rw [prim_periodic_STR02965 (firstPrim_continuous_STR02965 hc)
    (firstPrim_periodic_STR02965 hc hp h0) (firstPrim_integral_STR02965 hc) t]

theorem invD2_meanT_STR02965 {f : ℝ → ℝ} (hc : Continuous f) :
    meanT_STR02965 (invD2_STR02965 f) = 0 :=
  meanT_sub_self_STR02965 (prim_continuous_STR02965 (firstPrim_continuous_STR02965 hc))

theorem not_top_STR02965 (n : ℕ) : ((n : ℕ) : WithTop ℕ∞) ≠ (⊤ : WithTop ℕ∞) := by
  exact_mod_cast WithTop.coe_ne_top (a := (n : ℕ∞))

theorem firstPrim_contDiff_STR02965 (n : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ ((n : WithTop ℕ∞) + 1) (firstPrim_STR02965 f) := by
  have hc := hf.continuous
  rw [contDiff_succ_iff_deriv]
  refine ⟨fun t => (firstPrim_hasDerivAt_STR02965 hc t).differentiableAt, fun h => ?_, ?_⟩
  · exact absurd h (not_top_STR02965 n)
  · rw [deriv_firstPrim_STR02965 hc]
    exact hf

theorem invD2_contDiff_STR02965 (n : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ ((n : WithTop ℕ∞) + 1 + 1) (invD2_STR02965 f) := by
  have hc := hf.continuous
  rw [contDiff_succ_iff_deriv]
  refine ⟨fun t => (invD2_hasDerivAt_STR02965 hc t).differentiableAt, fun h => ?_, ?_⟩
  · simp at h
  · rw [deriv_invD2_STR02965 hc]
    exact firstPrim_contDiff_STR02965 n hf

/-! ### The carrier -/

/-- The mean-zero `2π`-periodic `C^m` functions of the angle `t`, as a submodule of `ℝ → ℝ`. -/
noncomputable def meanZeroPerC_STR02965 (m : ℕ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | Periodic f (2 * Real.pi) ∧ ContDiff ℝ m f ∧ meanT_STR02965 f = 0}
  add_mem' := by
    rintro f g ⟨hfp, hfd, hf0⟩ ⟨hgp, hgd, hg0⟩
    exact ⟨hfp.add hgp, hfd.add hgd, by
      rw [meanT_add_STR02965 hfd.continuous hgd.continuous, hf0, hg0, add_zero]⟩
  zero_mem' := by
    refine ⟨fun _ => rfl, contDiff_const, ?_⟩
    exact meanT_const_STR02965 0
  smul_mem' := by
    rintro c f ⟨hfp, hfd, hf0⟩
    exact ⟨periodic_smul_STR02965 c hfp, hfd.const_smul c, by
      rw [meanT_smul_STR02965, hf0, mul_zero]⟩

theorem mem_meanZeroPerC_STR02965 {m : ℕ} {f : ℝ → ℝ} :
    f ∈ meanZeroPerC_STR02965 m ↔
      Periodic f (2 * Real.pi) ∧ ContDiff ℝ m f ∧ meanT_STR02965 f = 0 := Iff.rfl

theorem meanZeroPerC_mono_STR02965 {m n : ℕ} (h : m ≤ n) :
    meanZeroPerC_STR02965 n ≤ meanZeroPerC_STR02965 m := by
  rintro f ⟨hp, hd, h0⟩
  exact ⟨hp, hd.of_le (by exact_mod_cast h), h0⟩

theorem invD2_mem_STR02965 (m : ℕ) {f : ℝ → ℝ} (hf : f ∈ meanZeroPerC_STR02965 m) :
    invD2_STR02965 f ∈ meanZeroPerC_STR02965 (m + 2) := by
  obtain ⟨hp, hd, h0⟩ := hf
  have hc := hd.continuous
  refine ⟨invD2_periodic_STR02965 hc hp h0, ?_, invD2_meanT_STR02965 hc⟩
  have h := invD2_contDiff_STR02965 m hd
  have e : ((m + 2 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 + 1 := by
    push_cast
    ring
  rw [e]
  exact h

/-! ### Uniqueness -/

theorem diff_of_c2_STR02965 {a : ℝ → ℝ} (ha : ContDiff ℝ 2 a) :
    Differentiable ℝ a ∧ Differentiable ℝ (deriv a) := by
  have h := (contDiff_succ_iff_deriv (n := 1)).1 ha
  exact ⟨h.1, h.2.2.differentiable one_ne_zero⟩

/-- Uniqueness of the mean-zero periodic solution of `v'' = f` among `C²` functions. -/
theorem str029_65_bounded_inverse_second_derivative_unique {v w : ℝ → ℝ}
    (hvp : Periodic v (2 * Real.pi)) (hv2 : ContDiff ℝ 2 v) (hv0 : meanT_STR02965 v = 0)
    (hwp : Periodic w (2 * Real.pi)) (hw2 : ContDiff ℝ 2 w) (hw0 : meanT_STR02965 w = 0)
    (h : deriv (deriv v) = deriv (deriv w)) : v = w := by
  obtain ⟨hvd, hvd'⟩ := diff_of_c2_STR02965 hv2
  obtain ⟨hwd, hwd'⟩ := diff_of_c2_STR02965 hw2
  -- the first derivative of `v - w` is constant
  have hder2 : ∀ t, HasDerivAt (fun s => deriv v s - deriv w s) 0 t := fun t => by
    have h1 := (hvd' t).hasDerivAt.sub (hwd' t).hasDerivAt
    rwa [show deriv (deriv v) t - deriv (deriv w) t = 0 by rw [congrFun h t]; ring] at h1
  have hk : ∀ t, deriv v t - deriv w t = deriv v 0 - deriv w 0 := fun t =>
    is_const_of_deriv_eq_zero (f := fun s => deriv v s - deriv w s)
      (fun s => (hvd' s).sub (hwd' s)) (fun s => (hder2 s).deriv) t 0
  set k : ℝ := deriv v 0 - deriv w 0 with hkdef
  -- `v - w - k t` has zero derivative, hence is constant; periodicity gives `k = 0`
  have hG : ∀ t, HasDerivAt (fun s => v s - w s - k * s) 0 t := fun t => by
    have h1 := ((hvd t).hasDerivAt.sub (hwd t).hasDerivAt).sub ((hasDerivAt_id t).const_mul k)
    have e : deriv v t - deriv w t - k * 1 = 0 := by rw [hk t]; ring
    exact h1.congr_deriv e
  have hGc : (v (2 * Real.pi) - w (2 * Real.pi) - k * (2 * Real.pi)) = v 0 - w 0 - k * 0 :=
    is_const_of_deriv_eq_zero (f := fun s => v s - w s - k * s)
      (fun s => (hG s).differentiableAt) (fun s => (hG s).deriv) _ _
  have hv0' : v (2 * Real.pi) = v 0 := by simpa using hvp 0
  have hw0' : w (2 * Real.pi) = w 0 := by simpa using hwp 0
  have hk0 : k = 0 := by
    have : k * (2 * Real.pi) = 0 := by rw [hv0', hw0'] at hGc; linarith
    exact (mul_eq_zero.1 this).resolve_right Real.two_pi_pos.ne'
  -- so `v - w` is constant
  have hu : ∀ t, HasDerivAt (fun s => v s - w s) 0 t := fun t => by
    have h1 := (hvd t).hasDerivAt.sub (hwd t).hasDerivAt
    rwa [hk t, hk0] at h1
  have hconst : ∀ t, v t - w t = v 0 - w 0 := fun t =>
    is_const_of_deriv_eq_zero (f := fun s => v s - w s)
      (fun s => (hu s).differentiableAt) (fun s => (hu s).deriv) t 0
  have hvw : v = fun t => w t + (v 0 - w 0) := by
    funext t
    linarith [hconst t]
  have hmean := meanT_shift_STR02965 hwd.continuous (v 0 - w 0)
  rw [← hvw, hv0, hw0] at hmean
  have hc0 : v 0 - w 0 = 0 := by linarith
  rw [hvw, hc0]
  funext t
  simp

/-! ### The operator and its bounds -/

theorem invD2_eq_STR02965 {f v : ℝ → ℝ} (hc : Continuous f) (hp : Periodic f (2 * Real.pi))
    (h0 : meanT_STR02965 f = 0) (hvp : Periodic v (2 * Real.pi)) (hv2 : ContDiff ℝ 2 v)
    (hv0 : meanT_STR02965 v = 0) (hvf : deriv (deriv v) = f) : v = invD2_STR02965 f := by
  have hI2 : ContDiff ℝ 2 (invD2_STR02965 f) := by
    have h := invD2_contDiff_STR02965 0 (contDiff_zero.2 hc)
    have e : (((0 : ℕ) : WithTop ℕ∞) + 1 + 1) = 2 := by norm_num
    rwa [e] at h
  exact str029_65_bounded_inverse_second_derivative_unique hvp hv2 hv0
    (invD2_periodic_STR02965 hc hp h0) hI2 (invD2_meanT_STR02965 hc)
    (by rw [hvf, deriv_deriv_invD2_STR02965 hc])

theorem deriv_deriv_add_STR02965 {a b : ℝ → ℝ} (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b) :
    deriv (deriv (a + b)) = deriv (deriv a) + deriv (deriv b) := by
  obtain ⟨had, had'⟩ := diff_of_c2_STR02965 ha
  obtain ⟨hbd, hbd'⟩ := diff_of_c2_STR02965 hb
  have h1 : deriv (a + b) = deriv a + deriv b := by
    funext t
    exact deriv_add (had t) (hbd t)
  rw [h1]
  funext t
  exact deriv_add (had' t) (hbd' t)

theorem deriv_deriv_smul_STR02965 {a : ℝ → ℝ} (ha : ContDiff ℝ 2 a) (c : ℝ) :
    deriv (deriv (c • a)) = c • deriv (deriv a) := by
  obtain ⟨had, had'⟩ := diff_of_c2_STR02965 ha
  have h1 : deriv (c • a) = c • deriv a := by
    funext t
    exact deriv_const_smul c (had t)
  rw [h1]
  funext t
  exact deriv_const_smul c (had' t)

theorem invD2_two_STR02965 {f : ℝ → ℝ} (hc : Continuous f) : ContDiff ℝ 2 (invD2_STR02965 f) := by
  have h := invD2_contDiff_STR02965 0 (contDiff_zero.2 hc)
  have e : (((0 : ℕ) : WithTop ℕ∞) + 1 + 1) = 2 := by norm_num
  rwa [e] at h

theorem invD2_add_STR02965 {f g : ℝ → ℝ} (hfc : Continuous f) (hfp : Periodic f (2 * Real.pi))
    (hf0 : meanT_STR02965 f = 0) (hgc : Continuous g) (hgp : Periodic g (2 * Real.pi))
    (hg0 : meanT_STR02965 g = 0) :
    invD2_STR02965 (f + g) = invD2_STR02965 f + invD2_STR02965 g := by
  symm
  refine invD2_eq_STR02965 (hfc.add hgc) (hfp.add hgp) ?_ ((invD2_periodic_STR02965 hfc hfp hf0).add
    (invD2_periodic_STR02965 hgc hgp hg0)) ((invD2_two_STR02965 hfc).add (invD2_two_STR02965 hgc))
    ?_ ?_
  · rw [meanT_add_STR02965 hfc hgc, hf0, hg0, add_zero]
  · rw [meanT_add_STR02965 (invD2_continuous_STR02965 hfc) (invD2_continuous_STR02965 hgc),
      invD2_meanT_STR02965 hfc, invD2_meanT_STR02965 hgc, add_zero]
  · rw [deriv_deriv_add_STR02965 (invD2_two_STR02965 hfc) (invD2_two_STR02965 hgc),
      deriv_deriv_invD2_STR02965 hfc, deriv_deriv_invD2_STR02965 hgc]

theorem invD2_smul_STR02965 (c : ℝ) {f : ℝ → ℝ} (hfc : Continuous f)
    (hfp : Periodic f (2 * Real.pi)) (hf0 : meanT_STR02965 f = 0) :
    invD2_STR02965 (c • f) = c • invD2_STR02965 f := by
  symm
  refine invD2_eq_STR02965 (continuous_const.smul hfc) (periodic_smul_STR02965 c hfp) ?_
    (periodic_smul_STR02965 c (invD2_periodic_STR02965 hfc hfp hf0))
    ((invD2_two_STR02965 hfc).const_smul c)
    ?_ ?_
  · rw [meanT_smul_STR02965, hf0, mul_zero]
  · rw [meanT_smul_STR02965, invD2_meanT_STR02965 hfc, mul_zero]
  · rw [deriv_deriv_smul_STR02965 (invD2_two_STR02965 hfc), deriv_deriv_invD2_STR02965 hfc]

/-- The norm of `g` in `C^{m+2}` splits as `‖g‖∞ + ‖g'‖∞ + ‖g''‖_{C^m}`. -/
theorem cmNorm_add_two_STR02965 (m : ℕ) {g f : ℝ → ℝ} (hg : deriv (deriv g) = f) :
    cmNorm_STR02965 (m + 2) g = supNorm g + supNorm (deriv g) + cmNorm_STR02965 m f := by
  have e : ∀ i : ℕ, iteratedDeriv (i + 1 + 1) g = iteratedDeriv i f := fun i => by
    rw [iteratedDeriv_succ', iteratedDeriv_succ', hg]
  unfold cmNorm_STR02965
  rw [Finset.sum_range_succ' _ (m + 2), Finset.sum_range_succ' _ (m + 1)]
  simp only [e, iteratedDeriv_zero, iteratedDeriv_one, zero_add]
  ring

theorem bdd_of_continuous_periodic_STR02965 {f : ℝ → ℝ} (hc : Continuous f)
    (hp : Periodic f (2 * Real.pi)) : Bdd f := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (hp.isBounded_of_continuous Real.two_pi_pos.ne' hc)
  exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC (f x) ⟨x, rfl⟩⟩

theorem cmNorm_bound_STR02965 (m : ℕ) {f : ℝ → ℝ} (hf : f ∈ meanZeroPerC_STR02965 m) :
    cmNorm_STR02965 (m + 2) (invD2_STR02965 f) ≤
      (16 * Real.pi ^ 2 + 4 * Real.pi + 1) * cmNorm_STR02965 m f := by
  obtain ⟨hp, hd, h0⟩ := hf
  have hc := hd.continuous
  have hbdd := bdd_of_continuous_periodic_STR02965 hc hp
  have hM : ∀ x, |f x| ≤ supNorm f := hbdd.abs_le_supNorm
  have hM0 : 0 ≤ supNorm f := supNorm_nonneg f
  -- bounds for the centred primitive and for the inverse
  have h1 := firstPrim_abs_le_STR02965 hc hp h0 hM
  have hI := prim_abs_le_STR02965 (firstPrim_continuous_STR02965 hc)
    (firstPrim_periodic_STR02965 hc hp h0) (firstPrim_integral_STR02965 hc) h1
  have hmI := meanT_abs_le_STR02965 (g := prim_STR02965 (firstPrim_STR02965 f)) hI
  have h2 : ∀ t, |invD2_STR02965 f t| ≤ 2 * Real.pi * (2 * (2 * Real.pi * supNorm f)) * 2 := by
    intro t
    unfold invD2_STR02965
    calc |prim_STR02965 (firstPrim_STR02965 f) t -
          meanT_STR02965 (prim_STR02965 (firstPrim_STR02965 f))|
        ≤ |prim_STR02965 (firstPrim_STR02965 f) t| +
            |meanT_STR02965 (prim_STR02965 (firstPrim_STR02965 f))| := abs_sub _ _
      _ ≤ 2 * Real.pi * (2 * (2 * Real.pi * supNorm f)) +
            2 * Real.pi * (2 * (2 * Real.pi * supNorm f)) := add_le_add (hI t) hmI
      _ = 2 * Real.pi * (2 * (2 * Real.pi * supNorm f)) * 2 := by ring
  have s0 : supNorm (invD2_STR02965 f) ≤ 2 * Real.pi * (2 * (2 * Real.pi * supNorm f)) * 2 :=
    supNorm_le h2
  have s1 : supNorm (deriv (invD2_STR02965 f)) ≤ 2 * (2 * Real.pi * supNorm f) := by
    rw [deriv_invD2_STR02965 hc]
    exact supNorm_le h1
  have hsplit := cmNorm_add_two_STR02965 m (deriv_deriv_invD2_STR02965 hc)
  -- `‖f‖∞ ≤ ‖f‖_{C^m}`
  have hle : supNorm f ≤ cmNorm_STR02965 m f := by
    have := Finset.single_le_sum (f := fun j => supNorm (iteratedDeriv j f))
      (fun j _ => supNorm_nonneg _) (Finset.mem_range.2 (Nat.succ_pos m))
    simpa [cmNorm_STR02965, iteratedDeriv_zero] using this
  rw [hsplit]
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  nlinarith [mul_le_mul_of_nonneg_left hle hM0, mul_nonneg hpi hM0, mul_nonneg (mul_nonneg hpi hpi) hM0,
    mul_nonneg hpi (sub_nonneg.2 hle), mul_nonneg (mul_nonneg hpi hpi) (sub_nonneg.2 hle)]

/-! ### Main theorem -/

/-- **STR029.65.** For every `m`, a linear map `B` from mean-zero periodic `C^m` functions to
mean-zero periodic `C^{m+2}` functions with `(B f)'' = f`, the bound
`‖B f‖_{C^{m+2}} ≤ (16π² + 4π + 1) ‖f‖_{C^m}`, uniqueness of the mean-zero periodic (`C²`) solution of
`v'' = f`, and `B f = invD2_STR02965 f` (compatibility in `m`). -/
theorem str029_65_bounded_inverse_second_derivative (m : ℕ) :
    ∃ B : meanZeroPerC_STR02965 m →ₗ[ℝ] meanZeroPerC_STR02965 (m + 2),
      (∀ f, deriv (deriv (B f : ℝ → ℝ)) = (f : ℝ → ℝ)) ∧
      (∀ f, cmNorm_STR02965 (m + 2) (B f : ℝ → ℝ) ≤
        (16 * Real.pi ^ 2 + 4 * Real.pi + 1) * cmNorm_STR02965 m (f : ℝ → ℝ)) ∧
      (∀ (f : meanZeroPerC_STR02965 m) (v : ℝ → ℝ), Periodic v (2 * Real.pi) → ContDiff ℝ 2 v →
        meanT_STR02965 v = 0 → deriv (deriv v) = (f : ℝ → ℝ) → v = (B f : ℝ → ℝ)) ∧
      (∀ f, (B f : ℝ → ℝ) = invD2_STR02965 (f : ℝ → ℝ)) := by
  refine ⟨{ toFun := fun f => ⟨invD2_STR02965 (f : ℝ → ℝ), invD2_mem_STR02965 m f.2⟩
            map_add' := fun f g => Subtype.ext ?_
            map_smul' := fun c f => Subtype.ext ?_ }, ?_, ?_, ?_, ?_⟩
  · exact invD2_add_STR02965 f.2.2.1.continuous f.2.1 f.2.2.2 g.2.2.1.continuous g.2.1 g.2.2.2
  · exact invD2_smul_STR02965 c f.2.2.1.continuous f.2.1 f.2.2.2
  · intro f
    exact deriv_deriv_invD2_STR02965 f.2.2.1.continuous
  · intro f
    exact cmNorm_bound_STR02965 m f.2
  · intro f v hvp hv2 hv0 hvf
    exact invD2_eq_STR02965 f.2.2.1.continuous f.2.1 f.2.2.2 hvp hv2 hv0 hvf
  · intro f
    rfl

/-- Compatibility: right inverses of the second derivative for `m ≤ n` agree on `C^n ⊆ C^m`. -/
theorem str029_65_bounded_inverse_second_derivative_compatible {m n : ℕ} (hmn : m ≤ n)
    (B₁ : meanZeroPerC_STR02965 m →ₗ[ℝ] meanZeroPerC_STR02965 (m + 2))
    (B₂ : meanZeroPerC_STR02965 n →ₗ[ℝ] meanZeroPerC_STR02965 (n + 2))
    (h₁ : ∀ f, deriv (deriv (B₁ f : ℝ → ℝ)) = (f : ℝ → ℝ))
    (h₂ : ∀ f, deriv (deriv (B₂ f : ℝ → ℝ)) = (f : ℝ → ℝ))
    (f : meanZeroPerC_STR02965 n) :
    (B₂ f : ℝ → ℝ) = (B₁ ⟨f, meanZeroPerC_mono_STR02965 hmn f.2⟩ : ℝ → ℝ) := by
  symm
  have hB₁ := (B₁ ⟨f, meanZeroPerC_mono_STR02965 hmn f.2⟩).2
  have hB₂ := (B₂ f).2
  refine str029_65_bounded_inverse_second_derivative_unique hB₁.1
    (hB₁.2.1.of_le (by exact_mod_cast Nat.le_add_left 2 m)) hB₁.2.2 hB₂.1
    (hB₂.2.1.of_le (by exact_mod_cast Nat.le_add_left 2 n)) hB₂.2.2 ?_
  rw [h₁, h₂]

end DGPS.Frontier.STR029
