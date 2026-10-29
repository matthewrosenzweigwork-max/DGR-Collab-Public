/- UNCHECKED outside frozen proof. Deterministic telescoping estimate used
in source prop:boundedFeatureQuadLaplace, Step 3. Both bases are bounded by the
actual positive quantity a_N; no convergence conclusion or Gaussian estimate
is assumed here. The paper endpoint must supply these bounds from its moment
hypothesis, together with the actual fourth-order expansion and parity. -/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic
noncomputable section
open Complex
namespace DGRHS.Gaussian

lemma norm_power_difference (a b : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (n : ℕ) :
    ‖a^(n+1)-b^(n+1)‖ ≤ (n+1 : ℝ)*r^n*‖a-b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : ‖a^(n+1)‖ ≤ r^(n+1) := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) ha _
    calc
      ‖a^(n+1+1)-b^(n+1+1)‖ =
          ‖(a-b)*a^(n+1)+b*(a^(n+1)-b^(n+1))‖ := by
        congr 1
        rw [pow_succ,pow_succ]
        ring
      _ ≤ ‖a-b‖*‖a^(n+1)‖ + ‖b‖*‖a^(n+1)-b^(n+1)‖ := by
        simpa only [norm_mul] using norm_add_le
          ((a-b)*a^(n+1)) (b*(a^(n+1)-b^(n+1)))
      _ ≤ ‖a-b‖*r^(n+1) + r*((n+1 : ℝ)*r^n*‖a-b‖) := by
        gcongr
      _ = (n+1+1 : ℝ)*r^(n+1)*‖a-b‖ := by
        rw [pow_succ]
        ring
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one]

lemma norm_power_difference_of_bound (a b : ℂ) (r A : ℝ)
    (hr : 1 ≤ r) (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r)
    (N : ℕ) (hN : 1 ≤ N) (hA : r^N ≤ A) :
    ‖a^N-b^N‖ ≤ (N : ℝ)*A*‖a-b‖ := by
  have hn : N-1+1=N := Nat.sub_add_cancel hN
  have h := norm_power_difference a b r (by linarith) ha hb (N-1)
  rw [hn] at h
  have hcast : ((N-1 : ℕ) : ℝ) + 1 = N := by exact_mod_cast hn
  rw [hcast] at h
  have hp : r^(N-1) ≤ A := by
    apply le_trans _ hA
    exact pow_le_pow_right₀ hr (Nat.sub_le N 1)
  apply h.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg N)) (norm_nonneg _)

lemma norm_exp_increment_difference (a u : ℂ) (δ : ℝ)
    (hu : ‖u‖ ≤ 1) (hδ : ‖a-(1+u)‖ ≤ δ) :
    ‖a-Complex.exp u‖ ≤ δ+‖u‖^2 := by
  calc
    ‖a-Complex.exp u‖ = ‖(a-(1+u)) + ((1+u)-Complex.exp u)‖ := by congr 1; ring
    _ ≤ ‖a-(1+u)‖ + ‖(1+u)-Complex.exp u‖ := norm_add_le _ _
    _ ≤ δ + ‖u‖^2 := by
      gcongr
      have h := Complex.norm_exp_sub_one_sub_id_le hu
      have he : (1+u)-Complex.exp u = -(Complex.exp u-1-u) := by ring
      simpa only [he,norm_neg] using h

/-- A global imaginary-exponential second remainder, obtained from the pinned
local estimate plus the unit modulus outside its unit ball. The harmless
constant 3 replaces the sharper source constant 1/2; the source's unspecified
Cβ therefore retains exactly the same hypotheses and N rate. -/
lemma norm_imaginary_exp_remainder (t : ℝ) :
    ‖Complex.exp (Complex.I*(t : ℂ))-1-Complex.I*(t : ℂ)‖ ≤ 3*t^2 := by
  have hz : ‖Complex.I*(t : ℂ)‖ = |t| := by simp
  by_cases ht : |t| ≤ 1
  · have h := Complex.norm_exp_sub_one_sub_id_le (x := Complex.I*(t : ℂ))
      (by simpa only [hz] using ht)
    rw [hz,sq_abs] at h
    nlinarith [sq_nonneg t]
  · have ht' : 1 < |t| := lt_of_not_ge ht
    have htriangle : ‖Complex.exp (Complex.I*(t : ℂ))-1-Complex.I*(t : ℂ)‖ ≤
        2+|t| := by
      apply (norm_sub_le _ _).trans
      apply le_trans (add_le_add_left (norm_sub_le _ _) _)
      simp only [Complex.norm_exp_I_mul_ofReal,norm_one,hz]
      norm_num
    have hsq : |t|^2 = t^2 := sq_abs t
    nlinarith [sq_nonneg (|t|-1)]

lemma norm_power_exp_difference (a u : ℂ) (r A δ : ℝ)
    (hr : 1 ≤ r) (ha : ‖a‖ ≤ r) (he : ‖Complex.exp u‖ ≤ r)
    (N : ℕ) (hN : 1 ≤ N) (hA : r^N ≤ A)
    (hu : ‖u‖ ≤ 1) (hδ : ‖a-(1+u)‖ ≤ δ) :
    ‖a^N-Complex.exp ((N : ℂ)*u)‖ ≤ (N : ℝ)*A*(δ+‖u‖^2) := by
  have hA0 : 0 ≤ A := (pow_nonneg (by linarith : 0 ≤ r) N).trans hA
  rw [Complex.exp_nat_mul]
  apply (norm_power_difference_of_bound a (Complex.exp u) r A hr ha he N hN hA).trans
  exact mul_le_mul_of_nonneg_left (norm_exp_increment_difference a u δ hu hδ)
    (mul_nonneg (Nat.cast_nonneg N) hA0)

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.norm_power_difference
#print axioms DGRHS.Gaussian.norm_imaginary_exp_remainder
#print axioms DGRHS.Gaussian.norm_power_exp_difference
