import Mathlib

/-!
# Section 4.2 (lane s42; R14): the smooth map `h ↦ log(1 + h)` on `C(X)`

For a compact space `X`, the Nemytskii map `h ↦ log(1 + h)` is `C^∞` on the open set
`{h ∈ C(X) : 1 + h > 0}` of the Banach algebra `C(X)` (sup norm), with derivative
`k ↦ k / (1 + h)`. (The manuscript works in `W^{1,∞}`; the reduction is done in `C(X)` and the
gradient is recovered afterwards from the reduced equation.)
-/

noncomputable section
open Filter Topology Asymptotics
open scoped ContDiff

namespace SharpLSI

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- `{h : 1 + h > 0}`. -/
def posSet : Set C(X, ℝ) := {h | ∀ x, 0 < 1 + h x}

theorem exists_pos_lower {h : C(X, ℝ)} (hh : h ∈ posSet) : ∃ m > 0, ∀ x, m ≤ 1 + h x := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨1, one_pos, fun x => (IsEmpty.false x).elim⟩
  · obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
      (continuous_const.add h.continuous).continuousOn
    exact ⟨1 + h x₀, hh x₀, fun x => hx₀ (Set.mem_univ x)⟩

theorem abs_apply_sub_le (f g : C(X, ℝ)) (x : X) : |f x - g x| ≤ ‖f - g‖ := by
  rw [← Real.norm_eq_abs, ← ContinuousMap.sub_apply]
  exact ContinuousMap.norm_coe_le_norm _ x

theorem isOpen_posSet : IsOpen (posSet (X := X)) := by
  rw [Metric.isOpen_iff]
  intro h hh
  obtain ⟨m, hm, hmx⟩ := exists_pos_lower hh
  refine ⟨m, hm, fun h' hh' x => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hh'
  have := abs_apply_sub_le h' h x
  have := hmx x
  have := neg_abs_le (h' x - h x)
  linarith

open Classical in
/-- `log(1 + h)` (and `0` outside `posSet`). -/
def logC (h : C(X, ℝ)) : C(X, ℝ) :=
  if hh : ∀ x, 0 < 1 + h x then
    ⟨fun x => Real.log (1 + h x), (continuous_const.add h.continuous).log fun x => (hh x).ne'⟩
  else 0

theorem logC_apply {h : C(X, ℝ)} (hh : h ∈ posSet) (x : X) : logC h x = Real.log (1 + h x) := by
  simp only [logC, dif_pos (show ∀ x, 0 < 1 + h x from hh)]
  rfl

theorem logC_zero : logC (0 : C(X, ℝ)) = 0 := by
  ext x
  rw [logC_apply (fun x => by simp)]
  simp

theorem isUnit_one_add {h : C(X, ℝ)} (hh : h ∈ posSet) : IsUnit (1 + h) :=
  (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr fun x => by
    simp only [ContinuousMap.add_apply, ContinuousMap.one_apply]; exact (hh x).ne'

theorem ringInverse_apply {f : C(X, ℝ)} (hf : IsUnit f) (x : X) :
    Ring.inverse f x = (f x)⁻¹ := by
  have h1 : Ring.inverse f * f = 1 := Ring.inverse_mul_cancel f hf
  have h2 : Ring.inverse f x * f x = 1 := by
    have := congrArg (fun g : C(X, ℝ) => g x) h1
    simpa using this
  exact eq_inv_of_mul_eq_one_left h2

/-- The derivative `k ↦ k/(1+h)`. -/
def logCDeriv (h : C(X, ℝ)) : C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  ContinuousLinearMap.mul ℝ C(X, ℝ) (Ring.inverse (1 + h))

theorem abs_log_one_add_sub_le {s : ℝ} (hs : |s| ≤ 1 / 2) :
    |Real.log (1 + s) - s| ≤ 2 * s ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -s) (by rw [abs_neg]; linarith) 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero,
    div_one, sub_neg_eq_add, abs_neg] at h
  have e : |-s + Real.log (1 + s)| = |Real.log (1 + s) - s| := by ring_nf
  rw [e] at h
  have hd : |s| ^ 2 / (1 - |s|) ≤ 2 * s ^ 2 := by
    rw [div_le_iff₀ (by linarith), sq_abs]
    nlinarith [sq_nonneg s, abs_nonneg s]
  linarith

theorem hasFDerivAt_logC {h : C(X, ℝ)} (hh : h ∈ posSet) :
    HasFDerivAt logC (logCDeriv h) h := by
  obtain ⟨m, hm, hmx⟩ := exists_pos_lower hh
  have hu := isUnit_one_add hh
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro ε hε
  have hball : Metric.ball (0 : C(X, ℝ)) (min (m / 2) (ε * m ^ 2 / 2)) ∈ 𝓝 (0 : C(X, ℝ)) :=
    Metric.ball_mem_nhds _ (lt_min (by positivity) (by positivity))
  filter_upwards [hball] with k hk
  rw [Metric.mem_ball, dist_zero_right] at hk
  have hk1 : ‖k‖ < m / 2 := hk.trans_le (min_le_left _ _)
  have hk2 : ‖k‖ < ε * m ^ 2 / 2 := hk.trans_le (min_le_right _ _)
  have hkx : ∀ x, |k x| ≤ ‖k‖ := fun x => by
    rw [← Real.norm_eq_abs]; exact ContinuousMap.norm_coe_le_norm k x
  have hhk : h + k ∈ posSet := fun x => by
    have := hkx x; have := hmx x; have := neg_abs_le (k x)
    simp only [ContinuousMap.add_apply]; linarith
  -- pointwise bound
  have hpt : ∀ x, |(logC (h + k) - logC h - logCDeriv h k) x| ≤ 2 * ‖k‖ ^ 2 / m ^ 2 := by
    intro x
    have ha : m ≤ 1 + h x := hmx x
    have ha0 : 0 < 1 + h x := hm.trans_le ha
    set s := k x / (1 + h x) with hs
    have hsb : |s| ≤ ‖k‖ / m := by
      rw [hs, abs_div, abs_of_pos ha0]
      exact div_le_div₀ (norm_nonneg _) (hkx x) hm ha
    have hs2 : |s| ≤ 1 / 2 := hsb.trans (by rw [div_le_iff₀ hm]; linarith)
    have e1 : (logC (h + k) - logC h - logCDeriv h k) x = Real.log (1 + s) - s := by
      simp only [ContinuousMap.sub_apply, logC_apply hhk, logC_apply hh, logCDeriv,
        ContinuousLinearMap.mul_apply', ContinuousMap.mul_apply, ringInverse_apply hu,
        ContinuousMap.add_apply, ContinuousMap.one_apply]
      have e2 : 1 + (h x + k x) = (1 + h x) * (1 + s) := by
        rw [hs]; field_simp; ring
      rw [e2, Real.log_mul ha0.ne' (by have := neg_abs_le s; linarith), hs]
      ring
    rw [e1]
    refine (abs_log_one_add_sub_le hs2).trans ?_
    have : s ^ 2 ≤ (‖k‖ / m) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hsb 2
    calc 2 * s ^ 2 ≤ 2 * (‖k‖ / m) ^ 2 := by linarith
      _ = 2 * ‖k‖ ^ 2 / m ^ 2 := by ring
  have hnorm : ‖logC (h + k) - logC h - logCDeriv h k‖ ≤ 2 * ‖k‖ ^ 2 / m ^ 2 :=
    (ContinuousMap.norm_le _ (by positivity)).mpr fun x => by
      rw [Real.norm_eq_abs]; exact hpt x
  refine hnorm.trans ?_
  have hk0 := norm_nonneg k
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem fderiv_logC {h : C(X, ℝ)} (hh : h ∈ posSet) : fderiv ℝ logC h = logCDeriv h :=
  (hasFDerivAt_logC hh).fderiv

theorem contDiffAt_logCDeriv {h : C(X, ℝ)} (hh : h ∈ posSet) :
    ContDiffAt ℝ ∞ logCDeriv h := by
  have hu := isUnit_one_add hh
  have h1 : ContDiffAt ℝ ∞ (fun g : C(X, ℝ) => Ring.inverse (1 + g)) h := by
    have := contDiffAt_ringInverse ℝ (n := ∞) hu.unit
    rw [IsUnit.unit_spec] at this
    exact this.comp h (contDiffAt_const.add contDiffAt_id)
  have h2 : ContDiff ℝ ∞ (fun f : C(X, ℝ) => ContinuousLinearMap.mul ℝ C(X, ℝ) f) := by
    exact ContinuousLinearMap.contDiff _
  exact h2.contDiffAt.comp h h1

/-- **`h ↦ log(1+h)` is `C^∞` on `posSet`.** -/
theorem contDiffOn_logC : ContDiffOn ℝ ∞ (logC (X := X)) posSet := by
  rw [contDiffOn_infty_iff_fderiv_of_isOpen isOpen_posSet]
  refine ⟨fun h hh => (hasFDerivAt_logC hh).differentiableAt.differentiableWithinAt, ?_⟩
  refine ContDiffOn.congr (f := logCDeriv) (fun h hh => (contDiffAt_logCDeriv hh).contDiffWithinAt)
    fun h hh => fderiv_logC hh

theorem contDiffAt_logC {h : C(X, ℝ)} (hh : h ∈ posSet) : ContDiffAt ℝ ∞ logC h :=
  contDiffOn_logC.contDiffAt (isOpen_posSet.mem_nhds hh)

theorem logCDeriv_zero : logCDeriv (0 : C(X, ℝ)) = ContinuousLinearMap.id ℝ C(X, ℝ) := by
  ext k x
  simp [logCDeriv]

end SharpLSI
