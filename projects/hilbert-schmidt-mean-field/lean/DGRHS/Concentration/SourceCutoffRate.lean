import DGRHS.Concentration.PartitionRate

/- Scalar cutoff optimization from preserved source lines 1960–1986.
These estimates do not assume a partition rate or determinant continuity. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace DGRHS.Concentration

def sourceRieszRateCutoff (C s n : ℝ) : ℝ :=
  (Real.log n / (2*C)) ^ (-1/s)

lemma sourceRieszRateCutoff_pos (C s n : ℝ) (hC : 0<C) (hn : 1<n) :
    0 < sourceRieszRateCutoff C s n := by
  exact Real.rpow_pos_of_pos (div_pos (Real.log_pos hn) (by positivity)) _

lemma sourceRieszRateCutoff_identities (C s n : ℝ) (hC : 0<C)
    (hs : 0<s) (hn : 1<n) (r : ℝ) :
    (sourceRieszRateCutoff C s n)^(-s) = Real.log n/(2*C) ∧
    (sourceRieszRateCutoff C s n)^r = (2*C)^(r/s)*(Real.log n)^(-(r/s)) ∧
    Real.exp (C*(sourceRieszRateCutoff C s n)^(-s))/n = n^(-(1/2:ℝ)) := by
  have hl : 0<Real.log n := Real.log_pos hn
  have hb : 0<Real.log n/(2*C) := div_pos hl (by positivity)
  have hpower : (sourceRieszRateCutoff C s n)^(-s) = Real.log n/(2*C) := by
    unfold sourceRieszRateCutoff
    rw [← Real.rpow_mul hb.le]
    have he : (-1/s)*(-s) = 1 := by field_simp
    rw [he,Real.rpow_one]
  refine ⟨hpower,?_,?_⟩
  · unfold sourceRieszRateCutoff
    rw [← Real.rpow_mul hb.le]
    have he : (-1/s)*r = -(r/s) := by ring
    rw [he,Real.div_rpow hl.le (by positivity),Real.rpow_neg (by positivity : 0≤2*C),div_inv_eq_mul]
    ring
  · rw [hpower,Real.rpow_def_of_pos (by linarith : 0<n)]
    have he : C*(Real.log n/(2*C)) = Real.log n/2 := by field_simp
    rw [he,← Real.exp_log (by linarith : 0<n),← Real.exp_sub,Real.log_exp]
    congr 1
    ring

def sourceLogRatePower (C : ℝ) : ℝ := min 1 (1/(2*C))
def sourceLogRateCutoff (C n : ℝ) : ℝ := n^(-sourceLogRatePower C)

lemma sourceLogRatePower_bounds (C : ℝ) (hC : 0<C) :
    0<sourceLogRatePower C ∧ sourceLogRatePower C≤1 ∧ C*sourceLogRatePower C≤1/2 := by
  have hb : 0<1/(2*C) := by positivity
  refine ⟨lt_min zero_lt_one hb,min_le_left _ _,?_⟩
  have h := mul_le_mul_of_nonneg_left (min_le_right (1:ℝ) (1/(2*C))) hC.le
  have he : C*(1/(2*C)) = 1/2 := by field_simp
  exact he ▸ h

lemma sourceLogRateCutoff_identities (C n r : ℝ) (hC : 0<C) (hn : 1≤n) :
    0<sourceLogRateCutoff C n ∧ sourceLogRateCutoff C n≤1 ∧
    Real.log (1/sourceLogRateCutoff C n) = sourceLogRatePower C * Real.log n ∧
    (sourceLogRateCutoff C n)^r = n^(-sourceLogRatePower C*r) ∧
    Real.exp (C*(1+Real.log (1/sourceLogRateCutoff C n)))/n ≤
      Real.exp C*n^(-(1/2:ℝ)) := by
  have hn0 : 0<n := lt_of_lt_of_le zero_lt_one hn
  obtain ⟨ha,ha1,hCa⟩ := sourceLogRatePower_bounds C hC
  have hη : 0<sourceLogRateCutoff C n := Real.rpow_pos_of_pos hn0 _
  have hlog : Real.log (1/sourceLogRateCutoff C n) = sourceLogRatePower C*Real.log n := by
    rw [one_div,Real.log_inv]
    unfold sourceLogRateCutoff
    rw [Real.log_rpow hn0]
    ring
  refine ⟨hη,?_,hlog,?_,?_⟩
  · unfold sourceLogRateCutoff
    have h := Real.rpow_le_rpow_of_exponent_le hn (show -sourceLogRatePower C≤0 by linarith)
    simpa only [Real.rpow_zero] using h
  · unfold sourceLogRateCutoff
    rw [← Real.rpow_mul hn0.le]
  · rw [hlog]
    have he : Real.exp (C*(1+sourceLogRatePower C*Real.log n))/n =
        Real.exp C*n^(C*sourceLogRatePower C-1) := by
      rw [Real.rpow_sub_one hn0.ne',Real.rpow_def_of_pos hn0,← mul_div_assoc,← Real.exp_add]
      congr 2 <;> ring
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos C).le
    apply Real.rpow_le_rpow_of_exponent_le hn
    linarith

/-- A positive multiplicative comparison controls inverse powers, with all
nonzero denominators proved from the actual positive bases. -/
lemma inverse_rpow_comparison (x y A q : ℝ) (hx : 0<x) (hy : 0<y)
    (hA : 0<A) (hq : 0≤q) (hxy : x≤A*y) : y^(-q)≤A^q*x^(-q) := by
  have hp := Real.rpow_le_rpow hx.le hxy hq
  rw [Real.mul_rpow hA.le hy.le] at hp
  rw [Real.rpow_neg hy.le,Real.rpow_neg hx.le,← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hx q)).2
  have hd : x^q/y^q≤A^q := (div_le_iff₀ (Real.rpow_pos_of_pos hy q)).2 hp
  simpa only [div_eq_mul_inv,mul_comm] using hd

/-- Explicit absorption of the N^(-1/2) cutoff error into the source
logarithmic Riesz rate. No asymptotic rate estimate is a hypothesis. -/
lemma half_power_le_log_rate (n q : ℝ) (hn : 1≤n) (hq : 0<q) :
    n^(-(1/2:ℝ)) ≤ (Real.log (Real.exp 1+1)+2*q)^q *
      (Real.log (Real.exp 1+n))^(-q) := by
  have hn0 : 0<n := lt_of_lt_of_le zero_lt_one hn
  let ε : ℝ := 1/(2*q)
  have hε : 0<ε := by dsimp [ε]; positivity
  have hL : 0<Real.log (Real.exp 1+1) := Real.log_pos (by linarith [Real.exp_pos (1:ℝ)])
  have hx : 0<Real.log (Real.exp 1+n) := Real.log_pos (by linarith [Real.exp_pos (1:ℝ)])
  have hA : 0<Real.log (Real.exp 1+1)+2*q := by positivity
  have hLog : Real.log (Real.exp 1+n) ≤
      (Real.log (Real.exp 1+1)+2*q)*n^ε := by
    have hm : Real.exp 1+n≤(Real.exp 1+1)*n := by
      nlinarith [mul_nonneg (Real.exp_pos (1:ℝ)).le (sub_nonneg.mpr hn)]
    have hlog := Real.log_le_log (by positivity : 0<Real.exp 1+n) hm
    rw [Real.log_mul (by positivity : Real.exp 1+1≠0) hn0.ne'] at hlog
    have hr := Real.log_le_rpow_div hn0.le hε
    have hp := Real.one_le_rpow hn hε.le
    have hlm : Real.log (Real.exp 1+1)≤Real.log (Real.exp 1+1)*n^ε := by
      nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hp)]
    have hεeq : 1/ε=2*q := by dsimp [ε]; field_simp
    calc
      _ ≤ Real.log (Real.exp 1+1)+Real.log n := hlog
      _ ≤ Real.log (Real.exp 1+1)*n^ε+n^ε/ε := add_le_add hlm hr
      _ = _ := by rw [div_eq_mul_inv,← one_div,hεeq]; ring
  have h := inverse_rpow_comparison (Real.log (Real.exp 1+n)) (n^ε)
    (Real.log (Real.exp 1+1)+2*q) q hx (Real.rpow_pos_of_pos hn0 ε) hA hq.le hLog
  rw [← Real.rpow_mul hn0.le] at h
  have he : ε*(-q)=-(1/2:ℝ) := by dsimp [ε]; field_simp
  simpa only [he] using h

lemma log_rate_shift (n q : ℝ) (hn : 2≤n) (hq : 0≤q) :
    (Real.log n)^(-q) ≤
      (1+Real.log (Real.exp 1+1)/Real.log 2)^q *
        (Real.log (Real.exp 1+n))^(-q) := by
  have hn0 : 0<n := by linarith
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0<Real.log (Real.exp 1+1) := Real.log_pos (by linarith [Real.exp_pos (1:ℝ)])
  have hlogn : 0<Real.log n := Real.log_pos (by linarith)
  have hx : 0<Real.log (Real.exp 1+n) := Real.log_pos (by linarith [Real.exp_pos (1:ℝ)])
  have hA : 0<1+Real.log (Real.exp 1+1)/Real.log 2 := by positivity
  apply inverse_rpow_comparison _ _ _ _ hx hlogn hA hq
  have hm : Real.exp 1+n≤(Real.exp 1+1)*n := by
    nlinarith [mul_nonneg (Real.exp_pos (1:ℝ)).le (show 0≤n-1 by linarith)]
  have hl := Real.log_le_log (by positivity : 0<Real.exp 1+n) hm
  rw [Real.log_mul (by positivity : Real.exp 1+1≠0) hn0.ne'] at hl
  have hln := Real.log_le_log (by norm_num : (0:ℝ)<2) hn
  have hmul := mul_le_mul_of_nonneg_left hln (div_nonneg hL.le h2.le)
  rw [div_mul_cancel₀ _ h2.ne'] at hmul
  nlinarith

/-- The actual Riesz cutoff gives the complete explicit large-N source rate,
including absorption of its finite-dimensional Laplace error. -/
theorem sourceRieszRateCutoff_bound (A C s r n : ℝ) (hA : 0≤A)
    (hC : 0<C) (hs : 0<s) (hr : 0<r) (hn : 2≤n) :
    2*A*(sourceRieszRateCutoff C s n)^r+
      C*Real.exp (C*(sourceRieszRateCutoff C s n)^(-s))/n ≤
    (2*A*(2*C)^(r/s)*(1+Real.log (Real.exp 1+1)/Real.log 2)^(r/s)+
      C*(Real.log (Real.exp 1+1)+2*(r/s))^(r/s))*
        (Real.log (Real.exp 1+n))^(-(r/s)) := by
  have hn1 : 1<n := by linarith
  have hq : 0<r/s := div_pos hr hs
  obtain ⟨_,hη,hExp⟩ := sourceRieszRateCutoff_identities C s n hC hs hn1 r
  have hsft := log_rate_shift n (r/s) hn hq.le
  have hhalf := half_power_le_log_rate n (r/s) (by linarith) hq
  rw [hη,show C*Real.exp (C*(sourceRieszRateCutoff C s n)^(-s))/n =
    C*(Real.exp (C*(sourceRieszRateCutoff C s n)^(-s))/n) by ring,hExp]
  calc
    _ = (2*A*(2*C)^(r/s))*(Real.log n)^(-(r/s))+C*n^(-(1/2:ℝ)) := by ring
    _ ≤ (2*A*(2*C)^(r/s))*
        ((1+Real.log (Real.exp 1+1)/Real.log 2)^(r/s)*(Real.log (Real.exp 1+n))^(-(r/s)))+
        C*((Real.log (Real.exp 1+1)+2*(r/s))^(r/s)*(Real.log (Real.exp 1+n))^(-(r/s))) :=
      add_le_add (mul_le_mul_of_nonneg_left hsft (by positivity))
        (mul_le_mul_of_nonneg_left hhalf hC.le)
    _ = _ := by ring

/-- The source logarithmic cutoff has a positive algebraic exponent, with
its N^(-1/2) Laplace error retained in the explicit minimum. -/
theorem sourceLogRateCutoff_bound (A C r n : ℝ) (hA : 0≤A)
    (hC : 0<C) (hr : 0<r) (hn : 1≤n) :
    0<min (sourceLogRatePower C*r) (1/2:ℝ) ∧
    2*A*(sourceLogRateCutoff C n)^r+
      C*Real.exp (C*(1+Real.log (1/sourceLogRateCutoff C n)))/n ≤
      (2*A+C*Real.exp C)*n^(-min (sourceLogRatePower C*r) (1/2:ℝ)) := by
  obtain ⟨ha,_,_⟩ := sourceLogRatePower_bounds C hC
  obtain ⟨_,_,_,hη,hExp⟩ := sourceLogRateCutoff_identities C n r hC hn
  refine ⟨lt_min (mul_pos ha hr) (by norm_num),?_⟩
  have hp : n^(-sourceLogRatePower C*r)≤n^(-min (sourceLogRatePower C*r) (1/2:ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hn
    have h := min_le_left (sourceLogRatePower C*r) (1/2:ℝ)
    linarith
  have hh : n^(-(1/2:ℝ))≤n^(-min (sourceLogRatePower C*r) (1/2:ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hn
    have h := min_le_right (sourceLogRatePower C*r) (1/2:ℝ)
    linarith
  rw [hη]
  calc
    _ ≤ 2*A*n^(-sourceLogRatePower C*r)+C*(Real.exp C*n^(-(1/2:ℝ))) := by
      apply add_le_add le_rfl
      have h := mul_le_mul_of_nonneg_left hExp hC.le
      convert h using 1; ring
    _ ≤ 2*A*n^(-min (sourceLogRatePower C*r) (1/2:ℝ))+
      (C*Real.exp C)*n^(-min (sourceLogRatePower C*r) (1/2:ℝ)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hp (by positivity))
        (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (by positivity : 0≤C*Real.exp C))
    _ = _ := by ring

#print axioms DGRHS.Concentration.sourceRieszRateCutoff_pos
#check @DGRHS.Concentration.sourceRieszRateCutoff_pos
#print axioms DGRHS.Concentration.sourceRieszRateCutoff_identities
#check @DGRHS.Concentration.sourceRieszRateCutoff_identities
#print axioms DGRHS.Concentration.sourceLogRatePower_bounds
#check @DGRHS.Concentration.sourceLogRatePower_bounds
#print axioms DGRHS.Concentration.sourceLogRateCutoff_identities
#check @DGRHS.Concentration.sourceLogRateCutoff_identities
#print axioms DGRHS.Concentration.inverse_rpow_comparison
#check @DGRHS.Concentration.inverse_rpow_comparison
#print axioms DGRHS.Concentration.half_power_le_log_rate
#check @DGRHS.Concentration.half_power_le_log_rate
#print axioms DGRHS.Concentration.log_rate_shift
#check @DGRHS.Concentration.log_rate_shift
#print axioms DGRHS.Concentration.sourceRieszRateCutoff_bound
#check @DGRHS.Concentration.sourceRieszRateCutoff_bound
#print axioms DGRHS.Concentration.sourceLogRateCutoff_bound
#check @DGRHS.Concentration.sourceLogRateCutoff_bound
end DGRHS.Concentration
