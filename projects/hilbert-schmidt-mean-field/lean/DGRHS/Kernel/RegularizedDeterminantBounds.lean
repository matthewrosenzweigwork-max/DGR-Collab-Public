/- Preparation: quantitative regularized product bounds for nonnegative sequences.
Actual operator positivity and spectral parameter instantiation remain separate. -/
import DGRHS.Kernel.RegularizedDeterminant
import Mathlib.Topology.Algebra.InfiniteSum.Order
namespace DGRHS.Kernel
variable {ι : Type*}
lemma regularizedLog_nonpos {x : ℝ} (hx : 0 ≤ x) : regularizedLog x ≤ 0 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < 1+x by linarith)
  dsimp [regularizedLog]
  linarith

lemma neg_half_sq_le_regularizedLog {x : ℝ} (hx : 0 ≤ x) :
    -(x ^ 2)/2 ≤ regularizedLog x := by
  have h := Real.le_log_one_add_of_nonneg hx
  have hd : 0 < x+2 := by linarith
  have hlow : x-x^2/2 ≤ 2*x/(x+2) := by
    apply (le_div_iff₀ hd).2
    nlinarith [mul_nonneg hx (sq_nonneg x)]
  dsimp [regularizedLog]
  linarith

theorem log_regularizedDet_bounds {x : ι → ℝ}
    (hx : Summable (fun i ↦ x i ^ 2)) (hnonneg : ∀ i, 0 ≤ x i) :
    -(∑' i, x i ^ 2)/2 ≤ Real.log (regularizedDet x) ∧
      Real.log (regularizedDet x) ≤ 0 := by
  have hpos : ∀ i, 0 < 1+x i := fun i ↦ by linarith [hnonneg i]
  rw [log_regularizedDet hx hpos]
  constructor
  · have h := ((hx.neg).div_const 2).tsum_le_tsum
        (fun i ↦ neg_half_sq_le_regularizedLog (hnonneg i)) (summable_regularizedLog hx)
    simpa only [tsum_div_const, tsum_neg, regularizedLog] using h
  · exact tsum_nonpos (fun i ↦ regularizedLog_nonpos (hnonneg i))

theorem regularizedDet_bounds {x : ι → ℝ}
    (hx : Summable (fun i ↦ x i ^ 2)) (hnonneg : ∀ i, 0 ≤ x i) :
    Real.exp (-(∑' i, x i ^ 2)/2) ≤ regularizedDet x ∧ regularizedDet x ≤ 1 := by
  have hp : 0 < regularizedDet x := regularizedDet_pos hx (fun i ↦ by linarith [hnonneg i])
  obtain ⟨hl, hu⟩ := log_regularizedDet_bounds hx hnonneg
  constructor
  · simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr hl
  · simpa only [Real.exp_log hp, Real.exp_zero] using Real.exp_le_exp.mpr hu
end DGRHS.Kernel
#print axioms DGRHS.Kernel.regularizedDet_bounds
