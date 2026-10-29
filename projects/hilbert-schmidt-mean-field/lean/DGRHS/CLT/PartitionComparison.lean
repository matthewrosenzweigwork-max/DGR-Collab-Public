/- Quantitative endpoint comparison avoids an unproved determinant-continuity
premise: actual exponential differences are controlled by proper second moments.
Physical uniform exponential bounds must be derived before source application. -/
import DGRHS.Kernel.Separated
import DGRHS.CLT.ExponentialMomentTransfer
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace DGRHS.CLT

lemma abs_exp_sub_exp_le (x y : ℝ) :
    |Real.exp x-Real.exp y| ≤ |x-y| * (Real.exp x+Real.exp y) := by
  have ordered (a b : ℝ) (hab : a ≤ b) :
      |Real.exp a-Real.exp b| ≤ |a-b| * (Real.exp a+Real.exp b) := by
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_monotone hab)),
      abs_of_nonpos (sub_nonpos.mpr hab)]
    have he : Real.exp b * Real.exp (a-b) = Real.exp a := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (a-b)) (Real.exp_pos b).le
    rw [he] at h
    nlinarith [Real.exp_pos a,Real.exp_pos b]
  by_cases h : x ≤ y
  · exact ordered x y h
  · simpa only [abs_sub_comm,add_comm] using ordered y x (le_of_not_ge h)

lemma integral_mul_le_toLp_norms {S : Type*} [MeasurableSpace S] {μ : Measure S}
    {f g : S → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x*g x ∂μ) ≤ ‖hf.toLp f‖*‖hg.toLp g‖ := by
  have he : (∫ x, f x*g x ∂μ) = inner ℝ (hf.toLp f) (hg.toLp g) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
    simp [hx,hy,mul_comm]
  rw [he]
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (hf.toLp f) (hg.toLp g))

lemma toLp_norm_eq_sqrt_second_moment {S : Type*} [MeasurableSpace S] {μ : Measure S}
    {f : S → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ = Real.sqrt (∫ x, f x^2 ∂μ) := by
  rw [← DGRHS.Kernel.norm_toLp_sq hf,Real.sqrt_sq (norm_nonneg _)]

lemma partition_exp_difference_le_second_moments {S : Type*} [MeasurableSpace S]
    {μ : Measure S} [IsProbabilityMeasure μ] (X Y : S → ℝ)
    (hd : MemLp (fun x => X x-Y x) 2 μ)
    (hx : MemLp (fun x => Real.exp (X x)) 2 μ)
    (hy : MemLp (fun x => Real.exp (Y x)) 2 μ) :
    |(∫ x, Real.exp (X x) ∂μ)-(∫ x, Real.exp (Y x) ∂μ)| ≤
      Real.sqrt (∫ x, (X x-Y x)^2 ∂μ) *
        (Real.sqrt (∫ x, Real.exp (2*X x) ∂μ)+Real.sqrt (∫ x, Real.exp (2*Y x) ∂μ)) := by
  have hdabs : MemLp (fun x => |X x-Y x|) 2 μ := by
    simpa only [Real.norm_eq_abs] using hd.norm
  have hx1 := hx.integrable (by norm_num)
  have hy1 := hy.integrable (by norm_num)
  have hprodX := hdabs.integrable_mul hx
  have hprodY := hdabs.integrable_mul hy
  calc
    _ = |∫ x, Real.exp (X x)-Real.exp (Y x) ∂μ| := by rw [integral_sub hx1 hy1]
    _ ≤ ∫ x, |Real.exp (X x)-Real.exp (Y x)| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => Real.exp (X x)-Real.exp (Y x)) (μ := μ)
    _ ≤ ∫ x, |X x-Y x| * Real.exp (X x)+|X x-Y x| * Real.exp (Y x) ∂μ := by
      apply integral_mono (hx1.sub hy1).norm (hprodX.add hprodY)
      intro x
      simpa only [Real.norm_eq_abs,Pi.sub_apply,Pi.mul_apply,Pi.add_apply,mul_add] using abs_exp_sub_exp_le (X x) (Y x)
    _ = (∫ x, |X x-Y x| * Real.exp (X x) ∂μ)+(∫ x, |X x-Y x| * Real.exp (Y x) ∂μ) :=
      integral_add hprodX hprodY
    _ ≤ ‖hdabs.toLp (fun x => |X x-Y x|)‖ *
        (‖hx.toLp (fun x => Real.exp (X x))‖+‖hy.toLp (fun x => Real.exp (Y x))‖) := by
      have h1 := integral_mul_le_toLp_norms hdabs hx
      have h2 := integral_mul_le_toLp_norms hdabs hy
      nlinarith
    _ = _ := by
      rw [toLp_norm_eq_sqrt_second_moment hdabs,toLp_norm_eq_sqrt_second_moment hx,
        toLp_norm_eq_sqrt_second_moment hy]
      simp_rw [sq_abs,← Real.exp_nat_mul]
      norm_num
end DGRHS.CLT
#print axioms DGRHS.CLT.abs_exp_sub_exp_le
#print axioms DGRHS.CLT.integral_mul_le_toLp_norms
#print axioms DGRHS.CLT.toLp_norm_eq_sqrt_second_moment
#print axioms DGRHS.CLT.partition_exp_difference_le_second_moments
#check @DGRHS.CLT.partition_exp_difference_le_second_moments
