import DGRHS.Gaussian.PeriodicD1AbelDomination
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! UNCOMPILED REPAIRED COPY (Claude complete physical d1 return, 2026-10-03).
Repairs: real-part term identity via `re_ofReal_mul`/`add_conj` (simp could not close it);
`push_cast; rfl` (no goals) replaced; missing `|n+1|` simp fact added.
Statements unchanged unless stated. Original header follows.
 Draft actual Abel logarithm series. Native complex log has real part
log(norm) at every point; no branch identity for a product or inverse is used.
Positive radii below one keep the native Taylor series inside its exact domain. -/
noncomputable section
open MeasureTheory
namespace DGRHS.Periodic

lemma periodicD1_abel_complex_hasSum (r : ℝ) (hr0 : 0≤r) (hr : r<1)
    (z : ℂ) (hz : ‖z‖=1) :
    HasSum (fun n : ℕ => ((r:ℂ)*z)^(n+1)/((n:ℂ)+1))
      (-Complex.log (1-(r:ℂ)*z)) := by
  apply Complex.hasSum_taylorSeries_neg_log'
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr0,hz,mul_one] using hr

lemma periodicD1_abel_real_series (r : ℝ) (hr0 : 0≤r) (hr : r<1)
    (z : ℂ) (hz : ‖z‖=1) :
    -Real.log ‖(1:ℂ)-(r:ℂ)*z‖=
      ∑' n : ℕ,(((r:ℂ)*z)^(n+1)/((n:ℂ)+1)).re := by
  have hs := periodicD1_abel_complex_hasSum r hr0 hr z hz
  have h := congrArg Complex.re hs.tsum_eq
  rw [Complex.re_tsum hs.summable,Complex.neg_re,Complex.log_re] at h
  exact h.symm

/-- The actual circle logarithm along a radius. At radius one, its collision
value is the native totalized log value; AE statements will remove that point. -/
def periodicD1AbelCircle (r : ℝ) (x : UnitAddCircle) : ℝ :=
  -Real.log ‖(1:ℂ)-(r:ℂ)*fourier 1 x‖

lemma periodicD1AbelCircle_series (r : ℝ) (hr0 : 0≤r) (hr : r<1)
    (x : UnitAddCircle) :
    periodicD1AbelCircle r x=
      ∑' n : ℕ,(((r:ℂ)*fourier 1 x)^(n+1)/((n:ℂ)+1)).re :=
  periodicD1_abel_real_series r hr0 hr _ (by simp [fourier_apply])

lemma periodicD1AbelCircle_domination (r : ℝ) (hr : (1:ℝ)/2≤r) (hr1 : r≤1)
    (x : UnitAddCircle) (hx : fourier 1 x≠1) :
    |periodicD1AbelCircle r x|≤Real.log 2+|periodicD1AbelCircle 1 x| := by
  simpa only [periodicD1AbelCircle,Complex.ofReal_one,one_mul,abs_neg] using
    periodicD1_abel_log_domination r hr hr1 (fourier 1 x) (by simp [fourier_apply]) hx

lemma periodicD1_fourier_nat_pow (n : ℕ) (x : UnitAddCircle) :
    fourier (n:ℤ) x=(fourier 1 x)^n := by
  induction n with
  | zero => simp [fourier_zero]
  | succ n ih => rw [Nat.cast_succ,fourier_add,ih,pow_succ]

lemma periodicD1_abel_term_re (r : ℝ) (n : ℕ) (x : UnitAddCircle) :
    (((((r:ℂ)*fourier 1 x)^(n+1)/((n:ℂ)+1)).re:ℝ):ℂ)=
      ((r^(n+1)/((n:ℝ)+1)/2:ℝ):ℂ)*
        (fourier ((n:ℤ)+1) x+fourier (-((n:ℤ)+1)) x) := by
  have he : ((r:ℂ)*fourier 1 x)^(n+1)/((n:ℂ)+1)=
      ((r^(n+1)/((n:ℝ)+1):ℝ):ℂ)*(fourier 1 x)^(n+1) := by
    push_cast
    first
    | (rw [mul_pow]; ring)
    | ring
  rw [he,Complex.re_ofReal_mul,←periodicD1_fourier_nat_pow,Nat.cast_succ,fourier_neg,
    Complex.add_conj]
  push_cast
  ring

lemma periodicD1_abel_term_norm (r : ℝ) (hr : 0≤r) (n : ℕ) (x : UnitAddCircle) :
    ‖((r:ℂ)*fourier 1 x)^(n+1)/((n:ℂ)+1)‖=r^(n+1)/((n:ℝ)+1) := by
  have hn : ‖fourier 1 x‖=1 := by simp [fourier_apply]
  have hc : (n:ℂ)+1=(((n:ℝ)+1:ℝ):ℂ) := by
    simp only [Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one]
  rw [hc,norm_div,norm_pow,norm_mul,Complex.norm_real,Complex.norm_real]
  simp [Real.norm_eq_abs,abs_of_nonneg hr,hn,abs_of_nonneg (by positivity : (0:ℝ)≤(n:ℝ)+1)]

lemma periodicD1_abel_coeff_summable (r : ℝ) (hr0 : 0≤r) (hr : r<1) :
    Summable (fun n : ℕ => r^(n+1)/((n:ℝ)+1)) := by
  have hg : Summable (fun n : ℕ => r^n) :=
    summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs,abs_of_nonneg hr0] using hr)
  have hs : Summable (fun n : ℕ => r^(n+1)) := by
    simpa only [pow_succ] using hg.mul_right r
  apply hs.of_nonneg_of_le
  · intro n
    positivity
  · intro n
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
    have hn : (0:ℝ)≤n := Nat.cast_nonneg n
    nlinarith [mul_nonneg hn (pow_nonneg hr0 (n+1))]

lemma periodicD1_abel_real_term_norm_le (r : ℝ) (hr : 0≤r)
    (n : ℕ) (x : UnitAddCircle) :
    ‖(((((r:ℂ)*fourier 1 x)^(n+1)/((n:ℂ)+1)).re:ℝ):ℂ)‖≤
      r^(n+1)/((n:ℝ)+1) := by
  rw [Complex.norm_real,Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans_eq (periodicD1_abel_term_norm r hr n x)

end DGRHS.Periodic
