import DGPS.Frontier.STR029.T13
import DGPS.Frontier.STR029.T51
import DGPS.Frontier.STR029.T52
import DGPS.Frontier.STR029.T69

/-!
# STR029.14 — Bounded isomorphism on the complement

Task id: STR029.14. Title: Bounded isomorphism on the complement.

Statement: the map `w ↦ w'' + w` is a bounded linear bijection from `E` onto `Y`, where `E` is the
closed complement of `span{1, cos, sin}` in the periodic `C^{2,1/2}` space and `Y` is the closed
complement of `span{1, cos, sin}` in the periodic `C^{0,1/2}` space. Its inverse has operator norm
at most `C0 = 1 + 30π + 10π²` for the Hölder norms of the specification.

Provides:
* `DGPS.Frontier.STR029.str029_14_bounded_isomorphism_complement`: there is a continuous linear
  equivalence `e : E ≃L[ℝ] Y` with `(e w).val = w'' + w` for every `w ∈ E`, and the operator norm
  of its inverse `e.symm : Y →L[ℝ] E` is at most `1 + 30π + 10π²`.

R5 notes:
* Carriers. `E` and `Y` are `E_STR02969` and `Y_STR02969` from `.69`: the submodules of
  `PeriodicC2_STR02969` and `PeriodicHolder_STR02968` cut out by the three constraints
  `∫ f dm = ∫ f cos dm = ∫ f sin dm = 0` with `dm = dt/(2π)` over one period. They are realised as
  the kernels of these functionals, not through the projection `Pf` written in the specification.
* Norms. The `C^{2,1/2}` norm is `c2Norm`, namely `‖u‖∞ + ‖u'‖∞ + ‖u''‖∞ + [u'']_{1/2}` with the
  circular distance. The `C^{0,1/2}` norm is `‖f‖∞ + [f]_{1/2}`, which equals the `PeriodicHolder`
  norm identically (`c0Norm` of `.53`).
* Domain. Functions are concrete `2π`-periodic `ℝ → ℝ`, with `C^{2,1/2}` meaning `C^2` with a
  circular-Hölder second derivative (`IsC2Alpha_STR02901`). No periodic Sobolev representative
  is used at this node.
* Forward map. `∂²+1` is the function `w ↦ w'' + w`. Its membership in `Y` uses integration by
  parts with periodic boundary terms. The `cos` and `sin` identities hold for every periodic `C^2`
  function, and the mean identity uses `∫ w dm = 0` from `w ∈ E`.
* Inverse. Surjectivity and the inverse formula come from `.13` (`wRight`). Injectivity comes from
  `.52` (kernel uniqueness), which uses `∫ w cos dm = ∫ w sin dm = 0`. The norm bound is `.51`
  applied to the inverse, which is a map `Y → E`.
* Bounded linear bijection. Stated as a `ContinuousLinearEquiv`, which gives continuity of both
  directions. The inverse's operator norm is the explicit constant `C0`. The forward bound
  constant `2 + π^(1/2)` used internally is not a public claim.
* The constant `C0 = 1 + 30π + 10π²` is the `.51` constant, and it is not re-derived here.
* Completeness of `E` and `Y` is imported from `.69` and supplied as `CompleteSpace` instances for
  the open-mapping step inside `ContinuousLinearEquiv.ofBijective`.
-/

open MeasureTheory DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.STR029

/-! ### Regularity, Hölder bounds and the forward map -/

theorem contDiff_two_STR02914 {w : ℝ → ℝ} (hw : IsC2Alpha_STR02901 (1 / 2 : ℝ) w) :
    ContDiff ℝ 2 w := by
  have h1 : ContDiff ℝ 1 (deriv w) := contDiff_one_iff_deriv.2 ⟨hw.2.2.1, hw.2.2.2.1⟩
  exact (contDiff_succ_iff_deriv (n := 1)).2 ⟨hw.2.1, fun h => absurd h (by decide), h1⟩

theorem c0_self_STR02914 {w : ℝ → ℝ} (hw : IsC2Alpha_STR02901 (1 / 2 : ℝ) w) :
    IsC0Alpha_STR02953 (1 / 2 : ℝ) w ∧
      c0Norm_STR02953 (1 / 2 : ℝ) w ≤
        supNorm w + Real.pi ^ (1 - (1 / 2 : ℝ)) * supNorm (deriv w) :=
  c0_of_deriv_STR02953 (α := 1 / 2) (by norm_num) (by norm_num) hw.1 hw.2.1
    (bdd_parts_STR02969 hw).2.1

/-- The `C^{0,1/2}` norm of `w'' + w` is bounded by a constant times the `C^{2,1/2}` norm of `w`. -/
theorem fwd_isC0_bound_STR02914 {w : ℝ → ℝ} (hw : IsC2Alpha_STR02901 (1 / 2 : ℝ) w) :
    IsC0Alpha_STR02953 (1 / 2 : ℝ) (deriv (deriv w) + w) ∧
      c0Norm_STR02953 (1 / 2 : ℝ) (deriv (deriv w) + w) ≤
        (2 + Real.pi ^ (1 - (1 / 2 : ℝ))) * c2Norm_STR02901 (1 / 2 : ℝ) w := by
  obtain ⟨hC0w, hbw⟩ := c0_self_STR02914 hw
  obtain ⟨hC0s, hs⟩ := c0_add_STR02953 (α := 1 / 2) (by norm_num) (c0_second_STR02969 hw) hC0w
  have hL := le_c2Norm_STR02969 w
  have hp : 0 ≤ Real.pi ^ (1 - (1 / 2 : ℝ)) := Real.rpow_nonneg Real.pi_pos.le _
  have hmul := mul_le_mul_of_nonneg_left hL.2.1 hp
  have hd2 : c0Norm_STR02953 (1 / 2 : ℝ) (deriv (deriv w)) =
      supNorm (deriv (deriv w)) + circHolder_STR02901 (1 / 2 : ℝ) (deriv (deriv w)) := rfl
  refine ⟨hC0s, ?_⟩
  rw [add_mul]
  linarith [hL.1, hL.2.2, hs, hbw, hmul, hd2]

theorem fwd_isPerHolder_STR02914 {w : ℝ → ℝ} (hw : IsC2Alpha_STR02901 (1 / 2 : ℝ) w) :
    IsPerHolder_STR02968 (1 / 2 : ℝ) (deriv (deriv w) + w) := by
  have hC := (fwd_isC0_bound_STR02914 hw).1
  exact ⟨hC.1, continuous_of_circHolderBdd_STR02953 (by norm_num) hC.2, hC.2⟩

/-- The forward map `w ↦ w'' + w` on `C^{2,1/2}`, as an element of `C^{0,1/2}`. -/
noncomputable def fwdP_STR02914 (w : PeriodicC2_STR02969) : PeriodicHolder_STR02968 :=
  PeriodicHolder_STR02968.mk (deriv (deriv w.val) + w.val) (fwd_isPerHolder_STR02914 w.isC2)

theorem fwdP_val_STR02914 (w : PeriodicC2_STR02969) :
    (fwdP_STR02914 w).val = deriv (deriv w.val) + w.val :=
  rfl

theorem phext_STR02914 {f g : PeriodicHolder_STR02968} (h : f.val = g.val) : f = g :=
  Subtype.ext h

theorem fwd_add_STR02914 {f g : ℝ → ℝ} (hf : IsC2Alpha_STR02901 (1 / 2 : ℝ) f)
    (hg : IsC2Alpha_STR02901 (1 / 2 : ℝ) g) :
    deriv (deriv (f + g)) + (f + g) = deriv (deriv f) + f + (deriv (deriv g) + g) := by
  rw [deriv_add_fun_STR02969 hf.2.1 hg.2.1, deriv_add_fun_STR02969 hf.2.2.1 hg.2.2.1]
  abel

theorem fwd_smul_STR02914 (c : ℝ) {f : ℝ → ℝ} (hf : IsC2Alpha_STR02901 (1 / 2 : ℝ) f) :
    deriv (deriv (c • f)) + c • f = c • (deriv (deriv f) + f) := by
  rw [deriv_smul_fun_STR02969 c hf.2.1, deriv_smul_fun_STR02969 c hf.2.2.1, smul_add]

/-- The forward map as a linear map `C^{2,1/2} → C^{0,1/2}`. -/
noncomputable def fwdLin_STR02914 : PeriodicC2_STR02969 →ₗ[ℝ] PeriodicHolder_STR02968 where
  toFun := fwdP_STR02914
  map_add' v w := by
    apply phext_STR02914
    simp only [fwdP_val_STR02914, PeriodicHolder_STR02968.val_add, PeriodicC2_STR02969.val_add]
    exact fwd_add_STR02914 v.isC2 w.isC2
  map_smul' c v := by
    apply phext_STR02914
    simp only [RingHom.id_apply, fwdP_val_STR02914, PeriodicHolder_STR02968.val_smul,
      PeriodicC2_STR02969.val_smul]
    exact fwd_smul_STR02914 c v.isC2

/-! ### Orthogonality of `w'' + w` by integration by parts -/

theorem inE_parts_STR02914 {w : ℝ → ℝ} (h : InE_STR02901 w) :
    meanT_STR02901 w = 0 ∧ meanT_STR02901 (fun t => w t * Real.cos t) = 0 ∧
      meanT_STR02901 (fun t => w t * Real.sin t) = 0 :=
  h

theorem int_mean_fwd_STR02914 {w : ℝ → ℝ} (hw : IsC2Alpha_STR02901 (1 / 2 : ℝ) w) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), deriv (deriv w) t = 0 := by
  have hD1 : deriv w (2 * Real.pi) = deriv w 0 := by simpa using periodic_deriv_STR02901 hw.1 0
  rw [intervalIntegral.integral_deriv_eq_sub (a := 0) (b := 2 * Real.pi)
    (fun x _ => hw.2.2.1 x) (hw.2.2.2.1.intervalIntegrable _ _), hD1, sub_self]

theorem int_cos_fwd_STR02914 {w : ℝ → ℝ} (hw : IsC2Alpha_STR02901 (1 / 2 : ℝ) w) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv (deriv w) t * Real.cos t + w t * Real.cos t) = 0 := by
  have hD1 : deriv w (2 * Real.pi) = deriv w 0 := by simpa using periodic_deriv_STR02901 hw.1 0
  have hw1 : w (2 * Real.pi) = w 0 := by simpa using hw.1 0
  have hD2 : Continuous (deriv (deriv w)) := hw.2.2.2.1
  have hD1c : Continuous (deriv w) := hw.2.2.1.continuous
  have ibp1 : ∫ t in (0 : ℝ)..(2 * Real.pi),
      (deriv (deriv w) t * Real.cos t + deriv w t * -Real.sin t)
        = deriv w (2 * Real.pi) * Real.cos (2 * Real.pi) - deriv w 0 * Real.cos 0 :=
    intervalIntegral.integral_deriv_mul_eq_sub (fun x _ => (hw.2.2.1 x).hasDerivAt)
      (fun x _ => Real.hasDerivAt_cos x) (hD2.intervalIntegrable _ _)
      (Real.continuous_sin.neg.intervalIntegrable _ _)
  have ibp2 : ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv w t * Real.sin t + w t * Real.cos t)
      = w (2 * Real.pi) * Real.sin (2 * Real.pi) - w 0 * Real.sin 0 :=
    intervalIntegral.integral_deriv_mul_eq_sub (fun x _ => (hw.2.1 x).hasDerivAt)
      (fun x _ => Real.hasDerivAt_sin x) (hD1c.intervalIntegrable _ _)
      (Real.continuous_cos.intervalIntegrable _ _)
  have s1 : ∫ t in (0 : ℝ)..(2 * Real.pi),
      (deriv (deriv w) t * Real.cos t + deriv w t * -Real.sin t)
        = (∫ t in (0 : ℝ)..(2 * Real.pi), deriv (deriv w) t * Real.cos t)
          + ∫ t in (0 : ℝ)..(2 * Real.pi), deriv w t * -Real.sin t :=
    intervalIntegral.integral_add ((hD2.mul Real.continuous_cos).intervalIntegrable _ _)
      ((hD1c.mul Real.continuous_sin.neg).intervalIntegrable _ _)
  have n1 : ∫ t in (0 : ℝ)..(2 * Real.pi), deriv w t * -Real.sin t
      = -∫ t in (0 : ℝ)..(2 * Real.pi), deriv w t * Real.sin t := by
    simp only [mul_neg, intervalIntegral.integral_neg]
  have s2 : ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv w t * Real.sin t + w t * Real.cos t)
      = (∫ t in (0 : ℝ)..(2 * Real.pi), deriv w t * Real.sin t)
          + ∫ t in (0 : ℝ)..(2 * Real.pi), w t * Real.cos t :=
    intervalIntegral.integral_add ((hD1c.mul Real.continuous_sin).intervalIntegrable _ _)
      ((hw.2.1.continuous.mul Real.continuous_cos).intervalIntegrable _ _)
  have e1 : (∫ t in (0 : ℝ)..(2 * Real.pi), deriv (deriv w) t * Real.cos t)
      + ∫ t in (0 : ℝ)..(2 * Real.pi), deriv w t * -Real.sin t = 0 := by
    rw [← s1, ibp1, hD1, Real.cos_two_pi, Real.cos_zero]
    ring
  have e2 : (∫ t in (0 : ℝ)..(2 * Real.pi), deriv w t * Real.sin t)
      + ∫ t in (0 : ℝ)..(2 * Real.pi), w t * Real.cos t = 0 := by
    rw [← s2, ibp2, hw1, Real.sin_two_pi, Real.sin_zero]
    ring
  have s0 : ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv (deriv w) t * Real.cos t + w t * Real.cos t)
      = (∫ t in (0 : ℝ)..(2 * Real.pi), deriv (deriv w) t * Real.cos t)
          + ∫ t in (0 : ℝ)..(2 * Real.pi), w t * Real.cos t :=
    intervalIntegral.integral_add ((hD2.mul Real.continuous_cos).intervalIntegrable _ _)
      ((hw.2.1.continuous.mul Real.continuous_cos).intervalIntegrable _ _)
  rw [s0]
  linarith [e1, e2, n1]

theorem int_sin_fwd_STR02914 {w : ℝ → ℝ} (hw : IsC2Alpha_STR02901 (1 / 2 : ℝ) w) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv (deriv w) t * Real.sin t + w t * Real.sin t) = 0 := by
  have hD1 : deriv w (2 * Real.pi) = deriv w 0 := by simpa using periodic_deriv_STR02901 hw.1 0
  have hw1 : w (2 * Real.pi) = w 0 := by simpa using hw.1 0
  have hD2 : Continuous (deriv (deriv w)) := hw.2.2.2.1
  have hD1c : Continuous (deriv w) := hw.2.2.1.continuous
  have ibp3 : ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv (deriv w) t * Real.sin t + deriv w t * Real.cos t)
      = deriv w (2 * Real.pi) * Real.sin (2 * Real.pi) - deriv w 0 * Real.sin 0 :=
    intervalIntegral.integral_deriv_mul_eq_sub (fun x _ => (hw.2.2.1 x).hasDerivAt)
      (fun x _ => Real.hasDerivAt_sin x) (hD2.intervalIntegrable _ _)
      (Real.continuous_cos.intervalIntegrable _ _)
  have ibp4 : ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv w t * Real.cos t + w t * -Real.sin t)
      = w (2 * Real.pi) * Real.cos (2 * Real.pi) - w 0 * Real.cos 0 :=
    intervalIntegral.integral_deriv_mul_eq_sub (fun x _ => (hw.2.1 x).hasDerivAt)
      (fun x _ => Real.hasDerivAt_cos x) (hD1c.intervalIntegrable _ _)
      (Real.continuous_sin.neg.intervalIntegrable _ _)
  have s3 : ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv (deriv w) t * Real.sin t + deriv w t * Real.cos t)
      = (∫ t in (0 : ℝ)..(2 * Real.pi), deriv (deriv w) t * Real.sin t)
          + ∫ t in (0 : ℝ)..(2 * Real.pi), deriv w t * Real.cos t :=
    intervalIntegral.integral_add ((hD2.mul Real.continuous_sin).intervalIntegrable _ _)
      ((hD1c.mul Real.continuous_cos).intervalIntegrable _ _)
  have s4 : ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv w t * Real.cos t + w t * -Real.sin t)
      = (∫ t in (0 : ℝ)..(2 * Real.pi), deriv w t * Real.cos t)
          + ∫ t in (0 : ℝ)..(2 * Real.pi), w t * -Real.sin t :=
    intervalIntegral.integral_add ((hD1c.mul Real.continuous_cos).intervalIntegrable _ _)
      ((hw.2.1.continuous.mul Real.continuous_sin.neg).intervalIntegrable _ _)
  have n2 : ∫ t in (0 : ℝ)..(2 * Real.pi), w t * -Real.sin t
      = -∫ t in (0 : ℝ)..(2 * Real.pi), w t * Real.sin t := by
    simp only [mul_neg, intervalIntegral.integral_neg]
  have e3 : (∫ t in (0 : ℝ)..(2 * Real.pi), deriv (deriv w) t * Real.sin t)
      + ∫ t in (0 : ℝ)..(2 * Real.pi), deriv w t * Real.cos t = 0 := by
    rw [← s3, ibp3, hD1, Real.sin_two_pi, Real.sin_zero]
    ring
  have e4 : (∫ t in (0 : ℝ)..(2 * Real.pi), deriv w t * Real.cos t)
      + ∫ t in (0 : ℝ)..(2 * Real.pi), w t * -Real.sin t = 0 := by
    rw [← s4, ibp4, hw1, Real.cos_two_pi, Real.cos_zero]
    ring
  have s5 : ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv (deriv w) t * Real.sin t + w t * Real.sin t)
      = (∫ t in (0 : ℝ)..(2 * Real.pi), deriv (deriv w) t * Real.sin t)
          + ∫ t in (0 : ℝ)..(2 * Real.pi), w t * Real.sin t :=
    intervalIntegral.integral_add ((hD2.mul Real.continuous_sin).intervalIntegrable _ _)
      ((hw.2.1.continuous.mul Real.continuous_sin).intervalIntegrable _ _)
  rw [s5]
  linarith [e3, e4, n2]

/-- `w'' + w` is orthogonal to `1`, `cos`, `sin` when `w` is orthogonal to `1`. -/
theorem inE_fwd_STR02914 {w : ℝ → ℝ} (hw : IsC2Alpha_STR02901 (1 / 2 : ℝ) w)
    (hE : InE_STR02901 w) : InE_STR02901 (deriv (deriv w) + w) := by
  have hm : meanT_STR02901 w = 0 := (inE_parts_STR02914 hE).1
  have hsplit : ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv (deriv w) t + w t)
      = (∫ t in (0 : ℝ)..(2 * Real.pi), deriv (deriv w) t)
          + ∫ t in (0 : ℝ)..(2 * Real.pi), w t :=
    intervalIntegral.integral_add (hw.2.2.2.1.intervalIntegrable _ _)
      (hw.2.1.continuous.intervalIntegrable _ _)
  unfold InE_STR02901
  refine ⟨?_, ?_, ?_⟩
  · unfold meanT_STR02901 at hm ⊢
    simp only [Pi.add_apply]
    rw [hsplit, int_mean_fwd_STR02914 hw, zero_add]
    exact hm
  · unfold meanT_STR02901
    simp only [Pi.add_apply, add_mul]
    rw [int_cos_fwd_STR02914 hw, mul_zero]
  · unfold meanT_STR02901
    simp only [Pi.add_apply, add_mul]
    rw [int_sin_fwd_STR02914 hw, mul_zero]

/-! ### The forward map into `Y` and the bounded linear map on `E` -/

theorem fwd_mem_STR02914 (x : E_STR02969) : fwdLin_STR02914 (x : PeriodicC2_STR02969) ∈ Y_STR02969 :=
  (str029_69_completeness_closed_complements_range_spaces_Y.1 _).mpr
    (inE_fwd_STR02914 (x : PeriodicC2_STR02969).isC2
      ((str029_69_completeness_closed_complements_range_spaces_E.1 (x : PeriodicC2_STR02969)).mp
        x.2))

/-- The forward map `E → Y`. -/
noncomputable def fwdE_STR02914 : E_STR02969 →ₗ[ℝ] Y_STR02969 :=
  LinearMap.codRestrict Y_STR02969 (fwdLin_STR02914.comp E_STR02969.subtype) fwd_mem_STR02914

/-- The bounded linear forward map `E → Y`. -/
noncomputable def fwdCLM_STR02914 : E_STR02969 →L[ℝ] Y_STR02969 :=
  LinearMap.mkContinuous fwdE_STR02914 (2 + Real.pi ^ (1 - (1 / 2 : ℝ)))
    fun x => (fwd_isC0_bound_STR02914 (x : PeriodicC2_STR02969).isC2).2

/-! ### The right inverse, its membership in `E`, and the inverse identity -/

theorem inY_STR02914 (g : Y_STR02969) : InY_STR02913 (1 / 2 : ℝ) (g : PeriodicHolder_STR02968).val :=
  ⟨⟨(PeriodicHolder_STR02968.isPerHolder g.1).1, (PeriodicHolder_STR02968.isPerHolder g.1).2.2⟩,
    (str029_69_completeness_closed_complements_range_spaces_Y.1 g.1).mp g.2⟩

noncomputable def wPC_STR02914 (g : Y_STR02969) : PeriodicC2_STR02969 :=
  PeriodicC2_STR02969.mk (wRight_STR02913 (g : PeriodicHolder_STR02968).val)
    (str029_13_periodic_right_inverse_range_operator_half (inY_STR02914 g)).1.1

theorem wPC_mem_STR02914 (g : Y_STR02969) : wPC_STR02914 g ∈ E_STR02969 :=
  (str029_69_completeness_closed_complements_range_spaces_E.1 (wPC_STR02914 g)).mpr
    (str029_13_periodic_right_inverse_range_operator_half (inY_STR02914 g)).1.2

/-- The right inverse of `.13` as an element of `E`. -/
noncomputable def wE_STR02914 (g : Y_STR02969) : E_STR02969 :=
  ⟨wPC_STR02914 g, wPC_mem_STR02914 g⟩

theorem fwdCLM_wE_STR02914 (g : Y_STR02969) : fwdCLM_STR02914 (wE_STR02914 g) = g := by
  apply Subtype.ext
  apply phext_STR02914
  funext t
  exact (str029_13_periodic_right_inverse_range_operator_half (inY_STR02914 g)).2 t

theorem fwdCLM_surjective_STR02914 : Function.Surjective fwdCLM_STR02914 :=
  fun g => ⟨wE_STR02914 g, fwdCLM_wE_STR02914 g⟩

/-- Injectivity of the forward map, by kernel uniqueness of `.52`. -/
theorem fwdCLM_injective_STR02914 : Function.Injective fwdCLM_STR02914 := by
  refine (injective_iff_map_eq_zero fwdCLM_STR02914).2 fun x hx => ?_
  have h0 : deriv (deriv (x : PeriodicC2_STR02969).val) + (x : PeriodicC2_STR02969).val = 0 :=
    congrArg (fun y : Y_STR02969 => (y : PeriodicHolder_STR02968).val) hx
  have hE := (str029_69_completeness_closed_complements_range_spaces_E.1
    (x : PeriodicC2_STR02969)).mp x.2
  have hw0 : (x : PeriodicC2_STR02969).val = 0 :=
    str029_52_kernel_uniqueness_range_operator (x : PeriodicC2_STR02969).val
      (contDiff_two_STR02914 (x : PeriodicC2_STR02969).isC2)
      (x : PeriodicC2_STR02969).isC2.1 (fun t => congrFun h0 t)
      (inE_parts_STR02914 hE).2.1 (inE_parts_STR02914 hE).2.2
  exact Subtype.ext (PeriodicC2_STR02969.val_eq_zero.1 hw0)

/-- The continuous linear equivalence `E ≃L[ℝ] Y` given by the forward map. -/
noncomputable def bij_STR02914 : E_STR02969 ≃L[ℝ] Y_STR02969 :=
  haveI : CompleteSpace E_STR02969 := str029_69_completeness_closed_complements_range_spaces_E.2.2
  haveI : CompleteSpace Y_STR02969 := str029_69_completeness_closed_complements_range_spaces_Y.2.2
  ContinuousLinearEquiv.ofBijective fwdCLM_STR02914
    (LinearMap.ker_eq_bot.mpr fwdCLM_injective_STR02914)
    (LinearMap.range_eq_top.mpr fwdCLM_surjective_STR02914)

theorem bij_wE_STR02914 (g : Y_STR02969) : bij_STR02914 (wE_STR02914 g) = g :=
  fwdCLM_wE_STR02914 g

theorem bij_symm_wE_STR02914 (g : Y_STR02969) : bij_STR02914.symm g = wE_STR02914 g := by
  rw [ContinuousLinearEquiv.symm_apply_eq, bij_wE_STR02914]

/-- The operator norm of the inverse is at most `C0`, by `.51`. -/
theorem bij_symm_norm_STR02914 :
    ‖(bij_STR02914.symm : Y_STR02969 →L[ℝ] E_STR02969)‖ ≤ 1 + 30 * Real.pi + 10 * Real.pi ^ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g => ?_
  show ‖bij_STR02914.symm g‖ ≤ (1 + 30 * Real.pi + 10 * Real.pi ^ 2) * ‖g‖
  rw [bij_symm_wE_STR02914]
  exact str029_51_explicit_holder_norm_bound_range_inverse (inY_STR02914 g)

/-- STR029.14: `∂²+1 : E → Y` is a bounded linear bijection whose inverse has norm at most
`1 + 30π + 10π²`. -/
theorem str029_14_bounded_isomorphism_complement :
    ∃ e : E_STR02969 ≃L[ℝ] Y_STR02969,
      (∀ w : E_STR02969, ((e w : Y_STR02969) : PeriodicHolder_STR02968).val =
          deriv (deriv (w : PeriodicC2_STR02969).val) + (w : PeriodicC2_STR02969).val) ∧
        ‖(e.symm : Y_STR02969 →L[ℝ] E_STR02969)‖ ≤ 1 + 30 * Real.pi + 10 * Real.pi ^ 2 :=
  ⟨bij_STR02914, fun _ => rfl, bij_symm_norm_STR02914⟩

end DGPS.Frontier.STR029
