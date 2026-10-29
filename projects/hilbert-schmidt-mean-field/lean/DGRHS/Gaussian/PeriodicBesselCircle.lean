import DGRHS.Gaussian.PeriodicCosineTrial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Group.Integral

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.Periodic

lemma periodic_cosh_quartic_lower (r : ℝ) : 1+r^2/2+r^4/24 ≤ Real.cosh r := by
  have h := (Real.hasSum_cosh r).summable.sum_le_tsum (Finset.range 3)
    (fun n _ => div_nonneg (by rw [pow_mul]; positivity) (Nat.cast_nonneg _))
  rw [(Real.hasSum_cosh r).tsum_eq] at h
  norm_num [Finset.sum_range_succ] at h
  exact h

lemma periodic_log_one_add_quadratic_lower {x : ℝ} (hx : 0 ≤ x) :
    x-x^2/2 ≤ Real.log (1+x) := by
  apply le_trans _ (Real.le_log_one_add_of_nonneg hx)
  apply (le_div_iff₀ (by linarith : 0 < x+2)).mpr
  nlinarith [mul_nonneg (sq_nonneg x) hx]

lemma periodicCircle_double_cos_sq (n : ℤ) (x : UnitAddCircle) :
    (fourier n x).re^2 = (1+(fourier (2*n) x).re)/2 := by
  let z := fourier n x
  have hz : ‖z‖=1 := by simp [z,fourier_apply]
  have hsq : z.re^2+z.im^2=1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [hz] at h
    simp only [Complex.normSq_apply,pow_two] at h ⊢
    nlinarith
  have hmul : (fourier (2*n) x).re=z.re^2-z.im^2 := by
    have h : fourier (2*n) x=z*z := by
      simpa [z,two_mul] using (fourier_add (m := n) (n := n) (x := x))
    rw [h,Complex.mul_re];ring
  change z.re^2=(1+(fourier (2*n) x).re)/2
  rw [hmul]
  nlinarith

lemma periodicCircle_cos_fourth (x : UnitAddCircle) :
    (fourier 1 x).re^4=(3+4*(fourier 2 x).re+(fourier 4 x).re)/8 := by
  have h1 := periodicCircle_double_cos_sq 1 x
  have h2 := periodicCircle_double_cos_sq 2 x
  change (fourier 1 x).re^2=(1+(fourier 2 x).re)/2 at h1
  change (fourier 2 x).re^2=(1+(fourier 4 x).re)/2 at h2
  have hp := congrArg (fun t : ℝ => t^2) h1
  nlinarith [hp]

lemma periodicCircle_cos_fourth_moment :
    (∫ x : UnitAddCircle,(fourier 1 x).re^4 ∂AddCircle.haarAddCircle)=3/8 := by
  have hi2 : Integrable (fourier (T := 1) 2) AddCircle.haarAddCircle :=
    (fourier 2).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi4 : Integrable (fourier (T := 1) 4) AddCircle.haarAddCircle :=
    (fourier 4).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [periodicCircle_cos_fourth]
  rw [integral_div]
  have hs : Integrable (fun x : UnitAddCircle => (3:ℝ)+4*RCLike.re (fourier 2 x)) AddCircle.haarAddCircle :=
    (integrable_const _).add (hi2.re.const_mul _)
  change (∫ x : UnitAddCircle,(3:ℝ)+4*RCLike.re (fourier 2 x)+RCLike.re (fourier 4 x) ∂AddCircle.haarAddCircle)/8=3/8
  rw [integral_add hs hi4.re,integral_add (integrable_const _) (hi2.re.const_mul _),
    integral_const_mul,integral_re hi2,integral_re hi4,
    periodicCircle_fourier_integral,periodicCircle_fourier_integral]
  norm_num

/-- The source I0 is the actual normalized Haar circle exponential integral. -/
def periodicBesselI0 (z : ℝ) : ℝ :=
  ∫ x : UnitAddCircle,Real.exp (z*(fourier 1 x).re) ∂AddCircle.haarAddCircle

lemma periodicBessel_exp_integrable (z : ℝ) :
    Integrable (fun x : UnitAddCircle => Real.exp (z*(fourier 1 x).re)) AddCircle.haarAddCircle := by
  have h : Continuous (fun x : UnitAddCircle => Real.exp (z*(fourier 1 x).re)) := by fun_prop
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma periodicBesselI0_pos (z : ℝ) : 0 < periodicBesselI0 z :=
  integral_exp_pos (periodicBessel_exp_integrable z)

lemma periodicBesselI0_eq_cosh (z : ℝ) :
    periodicBesselI0 z = ∫ x : UnitAddCircle,Real.cosh (z*(fourier 1 x).re) ∂AddCircle.haarAddCircle := by
  have hs (x : UnitAddCircle) : (fourier 1 (x+((1/2:ℝ):UnitAddCircle))).re=-(fourier 1 x).re := by
    have h := fourier_add_half_inv_index (T := 1) (n := 1) (by norm_num) (by norm_num) x
    simpa using congrArg Complex.re h
  have hneg : periodicBesselI0 z = periodicBesselI0 (-z) := by
    have h := integral_add_right_eq_self (μ := (AddCircle.haarAddCircle : Measure UnitAddCircle))
      (fun x : UnitAddCircle => Real.exp (z*(fourier 1 x).re)) ((1/2:ℝ):UnitAddCircle)
    simp only [hs,mul_neg,neg_mul] at h
    simpa only [periodicBesselI0,neg_mul] using h.symm
  simp_rw [Real.cosh_eq]
  rw [integral_div,integral_add (periodicBessel_exp_integrable z)]
  · simp_rw [←neg_mul]
    change periodicBesselI0 z=(periodicBesselI0 z+periodicBesselI0 (-z))/2
    rw [←hneg];ring
  · simpa only [neg_mul] using periodicBessel_exp_integrable (-z)

lemma periodicBesselI0_polynomial_lower (z : ℝ) :
    (1+z^2/8)^2 ≤ periodicBesselI0 z := by
  have h1 : Integrable (fun x : UnitAddCircle => (fourier 1 x).re^2) AddCircle.haarAddCircle := by
    have h : Continuous (fun x : UnitAddCircle => (fourier 1 x).re^2) := by fun_prop
    exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h2 : Integrable (fun x : UnitAddCircle => (fourier 1 x).re^4) AddCircle.haarAddCircle := by
    have h : Continuous (fun x : UnitAddCircle => (fourier 1 x).re^4) := by fun_prop
    exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp : Integrable (fun x : UnitAddCircle => 1+z^2/2*(fourier 1 x).re^2+z^4/24*(fourier 1 x).re^4) AddCircle.haarAddCircle :=
    ((integrable_const _).add (h1.const_mul _)).add (h2.const_mul _)
  have hc : Integrable (fun x : UnitAddCircle => Real.cosh (z*(fourier 1 x).re)) AddCircle.haarAddCircle := by
    have h : Continuous (fun x : UnitAddCircle => Real.cosh (z*(fourier 1 x).re)) := by fun_prop
    exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := integral_mono_ae hp hc (Filter.Eventually.of_forall fun x => by
    convert periodic_cosh_quartic_lower (z*(fourier 1 x).re) using 1 <;> ring)
  rw [←periodicBesselI0_eq_cosh] at h
  have hsec : (∫ x : UnitAddCircle,(fourier 1 x).re^2 ∂AddCircle.haarAddCircle)=1/2 := by
    simp_rw [periodicCircle_cos_sq]
    have hi : Integrable (fourier (T := 1) 2) AddCircle.haarAddCircle :=
      (fourier 2).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [integral_div]
    change (∫ x : UnitAddCircle,(1:ℝ)+RCLike.re (fourier 2 x) ∂AddCircle.haarAddCircle)/2=1/2
    rw [integral_add (integrable_const _) hi.re,integral_re hi,periodicCircle_fourier_integral]
    norm_num
  have hs : Integrable (fun x : UnitAddCircle => 1+z^2/2*(fourier 1 x).re^2) AddCircle.haarAddCircle :=
    (integrable_const _).add (h1.const_mul _)
  rw [integral_add hs (h2.const_mul _),integral_add (integrable_const _) (h1.const_mul _),
    integral_const_mul,integral_const_mul,hsec,periodicCircle_cos_fourth_moment] at h
  norm_num at h
  nlinarith

/-- Global quartic lower bound, derived from the actual circle integral.
This alternative is stronger than the source asymptotic O(z^6) expansion. -/
theorem periodicBesselI0_log_quartic_lower (z : ℝ) :
    z^2/4-z^4/64 ≤ Real.log (periodicBesselI0 z) := by
  have hq : 0 < 1+z^2/8 := by positivity
  have h := Real.log_le_log (sq_pos_of_pos hq) (periodicBesselI0_polynomial_lower z)
  rw [Real.log_pow] at h
  have hl := periodic_log_one_add_quadratic_lower (x := z^2/8) (by positivity)
  norm_num at h
  nlinarith

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicCircle_cos_fourth_moment
#print axioms DGRHS.Periodic.periodicBesselI0_log_quartic_lower
#check @DGRHS.Periodic.periodicBesselI0_log_quartic_lower
