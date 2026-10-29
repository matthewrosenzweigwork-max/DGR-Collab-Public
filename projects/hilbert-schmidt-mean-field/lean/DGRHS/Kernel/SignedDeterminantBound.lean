/- Quantitative source constant control for a signed HS spectrum.
Original doubled attractive margin supplies the uniform absolute bound;
the genuine HS identity supplies square summability and its total.
No trace or whole-spectrum dependence is substituted for source controls. -/
import DGRHS.Kernel.RegularizedDeterminant
import Mathlib.Topology.Algebra.InfiniteSum.Order
noncomputable section
namespace DGRHS.Kernel
variable {ι : Type*}

lemma abs_regularizedLog_le_sq_margin {x r : ℝ} (hx : |x|≤r) (hr : r<1) :
    |regularizedLog x| ≤ x^2/(1-r) := by
  have hsmall : |-x|<1 := by simpa only [abs_neg] using hx.trans_lt hr
  have h := Real.abs_log_sub_add_sum_range_le hsmall 1
  have h' : |regularizedLog x| ≤ x^2/(1-|x|) := by
    simpa [regularizedLog,sub_eq_add_neg,add_comm,sq_abs] using h
  exact h'.trans (div_le_div_of_nonneg_left (sq_nonneg x)
    (by linarith) (by linarith))

lemma neg_tsum_regularizedLog_le_sq_margin {x : ι → ℝ} {r : ℝ}
    (hs : Summable (fun i => x i^2)) (hx : ∀ i,|x i|≤r) (hr : r<1) :
    -(∑' i,regularizedLog (x i)) ≤ (∑' i,x i^2)/(1-r) := by
  have hl := summable_regularizedLog hs
  have hab : Summable (fun i => |regularizedLog (x i)|) := by
    simpa only [Real.norm_eq_abs] using hl.norm
  have h1 := hl.neg.tsum_le_tsum (fun i => neg_le_abs (regularizedLog (x i))) hab
  have h2 := hab.tsum_le_tsum (fun i => abs_regularizedLog_le_sq_margin (hx i) hr)
    (hs.div_const (1-r))
  simpa only [tsum_neg,tsum_div_const] using h1.trans h2

theorem inv_sqrt_regularizedDet_le_sq_margin {x : ι → ℝ} {r : ℝ}
    (hs : Summable (fun i => x i^2)) (hx : ∀ i,|x i|≤r) (hr : r<1) :
    (Real.sqrt (regularizedDet x))⁻¹ ≤
      Real.exp ((∑' i,x i^2)/(2*(1-r))) := by
  have hp : ∀ i,0<1+x i := fun i => by
    have hxi : -r≤x i := by linarith [neg_abs_le (x i),hx i]
    linarith
  rw [regularizedDet_eq_exp hs hp]
  have he : Real.sqrt (Real.exp (∑' i,regularizedLog (x i))) =
      Real.exp ((∑' i,regularizedLog (x i))/2) := by
    calc
      _ = Real.exp (Real.log (Real.sqrt (Real.exp (∑' i,regularizedLog (x i))))) :=
        (Real.exp_log (Real.sqrt_pos.mpr (Real.exp_pos _))).symm
      _ = _ := by rw [Real.log_sqrt (Real.exp_pos _).le,Real.log_exp]
  rw [he,←Real.exp_neg]
  apply Real.exp_le_exp.mpr
  have hb := div_le_div_of_nonneg_right
    (neg_tsum_regularizedLog_le_sq_margin hs hx hr) (show (0:ℝ)≤2 by norm_num)
  convert hb using 1 <;> field_simp <;> ring

end DGRHS.Kernel
#check @DGRHS.Kernel.inv_sqrt_regularizedDet_le_sq_margin
#print axioms DGRHS.Kernel.abs_regularizedLog_le_sq_margin
#print axioms DGRHS.Kernel.neg_tsum_regularizedLog_le_sq_margin
#print axioms DGRHS.Kernel.inv_sqrt_regularizedDet_le_sq_margin
