/- Unchecked draft: supporting real regularized product from square summability.
Actual integral-operator eigenvalue instantiation must be provided separately. -/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Tactic
open Filter
open scoped Topology
namespace DGRHS.Kernel
variable {ι : Type*}
noncomputable def regularizedLog (x : ℝ) : ℝ := Real.log (1+x)-x
noncomputable def regularizedDet (x : ι → ℝ) : ℝ := ∏' i, (1+x i)*Real.exp (-x i)

lemma abs_regularizedLog_le_sq {x : ℝ} (hx : |x| ≤ 1/2) :
    |regularizedLog x| ≤ 2*x^2 := by
  have hsmall : |-x| < 1 := by simpa using (lt_of_le_of_lt hx (by norm_num : (1/2:ℝ)<1))
  have h := Real.abs_log_sub_add_sum_range_le hsmall 1
  have h' : |regularizedLog x| ≤ x^2/(1-|x|) := by
    simpa [regularizedLog, sub_eq_add_neg, add_comm, sq_abs] using h
  have hd : 0 < 1-|x| := by linarith
  calc
    |regularizedLog x| ≤ x^2/(1-|x|) := h'
    _ ≤ 2*x^2 := (div_le_iff₀ hd).2 (by nlinarith [sq_nonneg x])

lemma summable_regularizedLog {x : ι → ℝ} (hx : Summable (fun i ↦ x i ^ 2)) :
    Summable (fun i ↦ regularizedLog (x i)) := by
  apply (hx.mul_left 2).of_norm_bounded_eventually
  filter_upwards [hx.tendsto_cofinite_zero.eventually_lt_const (by norm_num : (0:ℝ)<1/4)] with i hi
  have habs : |x i| ≤ 1/2 := by nlinarith [sq_abs (x i), abs_nonneg (x i)]
  simpa only [Real.norm_eq_abs] using abs_regularizedLog_le_sq habs

lemma hasProd_regularizedDet {x : ι → ℝ} (hx : Summable (fun i ↦ x i ^ 2))
    (hpos : ∀ i, 0 < 1+x i) :
    HasProd (fun i ↦ (1+x i)*Real.exp (-x i))
      (Real.exp (∑' i, regularizedLog (x i))) := by
  apply (summable_regularizedLog hx).hasSum.rexp.congr_fun
  intro i
  simp [regularizedLog, sub_eq_add_neg, Real.exp_add, Real.exp_log (hpos i)]

lemma regularizedDet_eq_exp {x : ι → ℝ} (hx : Summable (fun i ↦ x i ^ 2))
    (hpos : ∀ i, 0 < 1+x i) :
    regularizedDet x = Real.exp (∑' i, regularizedLog (x i)) :=
  (hasProd_regularizedDet hx hpos).tprod_eq

lemma regularizedDet_pos {x : ι → ℝ} (hx : Summable (fun i ↦ x i ^ 2))
    (hpos : ∀ i, 0 < 1+x i) : 0 < regularizedDet x := by
  rw [regularizedDet_eq_exp hx hpos]
  exact Real.exp_pos _

lemma log_regularizedDet {x : ι → ℝ} (hx : Summable (fun i ↦ x i ^ 2))
    (hpos : ∀ i, 0 < 1+x i) :
    Real.log (regularizedDet x) = ∑' i, (Real.log (1+x i)-x i) := by
  rw [regularizedDet_eq_exp hx hpos, Real.log_exp]
  rfl
end DGRHS.Kernel
#print axioms DGRHS.Kernel.summable_regularizedLog
#print axioms DGRHS.Kernel.hasProd_regularizedDet
#print axioms DGRHS.Kernel.regularizedDet_pos
#print axioms DGRHS.Kernel.log_regularizedDet
