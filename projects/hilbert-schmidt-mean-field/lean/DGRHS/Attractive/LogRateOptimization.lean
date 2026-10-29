/- Conservative positive-power cutoff selection for the source's unspecified
algebraic rate. Reuses the already checked logarithmic cutoff arithmetic at
sqrt(N), retaining both N^-1/2 fixed-cutoff and one-body errors. -/
import DGRHS.Concentration.SourceCutoffRate
noncomputable section
open MeasureTheory
namespace DGRHS.Attractive
open DGRHS.Concentration

def attractiveLogRatePower (C r : ℝ) : ℝ :=
  min (sourceLogRatePower C*r) (1/2:ℝ)/2

def attractiveLogRateCutoff (C n : ℝ) : ℝ := sourceLogRateCutoff C (Real.sqrt n)

lemma attractiveLogRatePower_bounds (C r : ℝ) (hC : 0<C) (hr : 0<r) :
    0<attractiveLogRatePower C r ∧ attractiveLogRatePower C r≤1/4 := by
  have ha := (sourceLogRatePower_bounds C hC).1
  constructor
  · exact div_pos (lt_min (mul_pos ha hr) (by norm_num)) (by norm_num)
  · dsimp [attractiveLogRatePower]
    have h := min_le_right (sourceLogRatePower C*r) (1/2:ℝ)
    linarith

lemma attractiveLogRateCutoff_bound (A C D r n : ℝ)
    (hA : 0≤A) (hC : 0<C) (hD : 0≤D) (hr : 0<r) (hn : 1≤n) :
    0<attractiveLogRateCutoff C n ∧ attractiveLogRateCutoff C n≤1 ∧
    2*A*(attractiveLogRateCutoff C n)^r+
      C*Real.exp (C*(1+Real.log (1/attractiveLogRateCutoff C n)))/Real.sqrt n+
      D/Real.sqrt n ≤
      (2*A+C*Real.exp C+D)*(Real.exp 1+1)^(attractiveLogRatePower C r)*
        (Real.exp 1+n)^(-attractiveLogRatePower C r) := by
  have hn0 : 0<n := lt_of_lt_of_le zero_lt_one hn
  have hs : 1≤Real.sqrt n := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn
  obtain ⟨hη,hη1,_,_,_⟩ := sourceLogRateCutoff_identities C (Real.sqrt n) r hC hs
  obtain ⟨hp,hbound⟩ := sourceLogRateCutoff_bound A C r (Real.sqrt n) hA hC hr hs
  obtain ⟨hc,hcquarter⟩ := attractiveLogRatePower_bounds C r hC hr
  have hpw : (Real.sqrt n)^(-min (sourceLogRatePower C*r) (1/2:ℝ))=
      n^(-attractiveLogRatePower C r) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hn0.le]
    congr 1
    dsimp [attractiveLogRatePower]
    ring
  rw [hpw] at hbound
  have hhalf : 1/Real.sqrt n≤n^(-attractiveLogRatePower C r) := by
    rw [Real.sqrt_eq_rpow,one_div,←Real.rpow_neg hn0.le]
    apply Real.rpow_le_rpow_of_exponent_le hn
    linarith
  have hshift : n^(-attractiveLogRatePower C r)≤
      (Real.exp 1+1)^(attractiveLogRatePower C r)*
        (Real.exp 1+n)^(-attractiveLogRatePower C r) :=
    inverse_rpow_comparison (Real.exp 1+n) n (Real.exp 1+1)
      (attractiveLogRatePower C r) (by positivity) hn0 (by positivity) hc.le
      (by nlinarith [mul_nonneg (Real.exp_pos (1:ℝ)).le (sub_nonneg.mpr hn)])
  refine ⟨hη,hη1,?_⟩
  change 2*A*(sourceLogRateCutoff C (Real.sqrt n))^r+
    C*Real.exp (C*(1+Real.log (1/sourceLogRateCutoff C (Real.sqrt n))))/Real.sqrt n+
    D/Real.sqrt n≤_
  calc
    _ ≤ (2*A+C*Real.exp C)*n^(-attractiveLogRatePower C r)+
      D*n^(-attractiveLogRatePower C r) :=
      add_le_add hbound (by simpa only [div_eq_mul_inv,one_div,one_mul] using
        mul_le_mul_of_nonneg_left hhalf hD)
    _ = (2*A+C*Real.exp C+D)*n^(-attractiveLogRatePower C r) := by ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hshift
        (show 0≤2*A+C*Real.exp C+D by positivity)
end DGRHS.Attractive
#check @DGRHS.Attractive.attractiveLogRateCutoff_bound
#print axioms DGRHS.Attractive.attractiveLogRatePower_bounds
#print axioms DGRHS.Attractive.attractiveLogRateCutoff_bound
