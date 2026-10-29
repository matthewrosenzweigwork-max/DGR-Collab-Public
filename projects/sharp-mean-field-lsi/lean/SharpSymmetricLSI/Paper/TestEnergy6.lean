import SharpSymmetricLSI.Paper.CondForce1

/-!
# R33 groundwork: weighted `L¹` errors from `L²` errors

`∫ w|Y| dP ≤ ‖w‖_{L^p} (M^{q-1} ‖Y‖_{L²})^{1/q}` for `|Y| ≤ M` (Hölder, then `|Y|^q ≤ M^{q-1}|Y|`
and Cauchy–Schwarz); used with `w = p_N` the centered Gibbs density.
-/

open MeasureTheory Filter Topology Real

namespace SharpLSI

theorem integral_weight_abs_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {w Y : Ω → ℝ} (hw0 : ∀ x, 0 ≤ w x) (hwm : Measurable w) {K : ℝ}
    (hwb : ∀ x, w x ≤ K) (hYm : Measurable Y) {M : ℝ} (hM : 0 ≤ M) (hYb : ∀ x, |Y x| ≤ M)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∫ x, w x * |Y x| ∂P ≤
      (∫ x, w x ^ p ∂P) ^ (1 / p) * (M ^ (q - 1) * (∫ x, Y x ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ (1 / q) := by
  have hp0 : 0 < p := hpq.pos
  have hq1 : 1 < q := hpq.symm.lt
  have hwL : ∀ r, MemLp w r P := fun r => MemLp.of_bound hwm.aestronglyMeasurable K
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x)]; exact hwb x)
  have hYL : ∀ r, MemLp (fun x => |Y x|) r P := fun r => MemLp.of_bound hYm.abs.aestronglyMeasurable M
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_abs]; exact hYb x)
  have h1 := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (Eventually.of_forall hw0)
    (Eventually.of_forall fun x => abs_nonneg (Y x)) (hwL _) (hYL _)
  refine h1.trans (mul_le_mul_of_nonneg_left ?_
    (rpow_nonneg (integral_nonneg fun x => rpow_nonneg (hw0 x) _) _))
  refine rpow_le_rpow (integral_nonneg fun x => rpow_nonneg (abs_nonneg _) _) ?_ (by positivity)
  have hpt : ∀ x, |Y x| ^ q ≤ M ^ (q - 1) * |Y x| := fun x => by
    have e : |Y x| ^ q = |Y x| ^ (q - 1) * |Y x| := by
      conv_lhs => rw [show q = (q - 1) + 1 by ring]
      rw [rpow_add_one' (abs_nonneg _) (by linarith)]
    rw [e]
    exact mul_le_mul_of_nonneg_right (rpow_le_rpow (abs_nonneg _) (hYb x) (by linarith))
      (abs_nonneg _)
  have hYint : Integrable (fun x => |Y x|) P :=
    integrable_of_bdd hYm.abs fun x => by rw [abs_abs]; exact hYb x
  have hcs : ∫ x, |Y x| ∂P ≤ (∫ x, Y x ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (Eventually.of_forall fun x => abs_nonneg (Y x))
      (Eventually.of_forall fun _ => zero_le_one) (hYL _) (memLp_const (1 : ℝ))
    simp only [mul_one, one_rpow, integral_const, probReal_univ, smul_eq_mul] at h
    have e : ∀ x, |Y x| ^ (2 : ℝ) = Y x ^ 2 := fun x => by rw [rpow_two, sq_abs]
    simp_rw [e] at h
    simpa using h
  calc ∫ x, |Y x| ^ q ∂P ≤ ∫ x, M ^ (q - 1) * |Y x| ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => rpow_nonneg (abs_nonneg _) _)
          (hYint.const_mul _) (Eventually.of_forall hpt)
    _ = M ^ (q - 1) * ∫ x, |Y x| ∂P := integral_const_mul _ _
    _ ≤ M ^ (q - 1) * (∫ x, Y x ^ 2 ∂P) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hcs (rpow_nonneg hM _)

end SharpLSI
