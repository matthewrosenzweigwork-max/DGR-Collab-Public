import LeanResearch.PeriodicAttractiveLogGas.FibreEntropy

/-! Finite entropy calculus for the supplied local-box proof, source2203–2211:
convexity under averaging and bounded-density comparison, with zero means. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.FiniteEntropyCalculus
open FibreEntropy

def deviation (x a : ℝ) : ℝ := x * (Real.log x - Real.log a) - x + a

theorem deviation_nonneg {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) :
    0 ≤ deviation x a := by
  by_cases hz : x = 0
  · simp [hz, deviation, ha.le]
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
  have hh := Real.log_le_sub_one_of_pos (div_pos ha hxp)
  rw [Real.log_div ha.ne' hz] at hh
  have hm := mul_le_mul_of_nonneg_left hh hx
  have hid : x * (a / x - 1) = a - x := by field_simp
  rw [hid] at hm
  unfold deviation
  nlinarith only [hm]

@[simp] theorem deviation_self (a : ℝ) : deviation a a = 0 := by simp [deviation]

theorem mean_nonneg {α : Type*} [Fintype α] {w F : α → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hF : ∀ x, 0 ≤ F x) : 0 ≤ ∑ x, w x * F x :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (hF x)

theorem eq_zero_of_mean_zero {α : Type*} [Fintype α] {w F : α → ℝ}
    (hw : ∀ x, 0 < w x) (hF : ∀ x, 0 ≤ F x)
    (hz : (∑ x, w x * F x) = 0) : F = fun _ => 0 := by
  classical
  funext x
  have hh : w x * F x ≤ 0 := by
    rw [← hz]
    exact Finset.single_le_sum (fun y _ => mul_nonneg (hw y).le (hF y)) (Finset.mem_univ x)
  by_contra h
  have hp : 0 < F x := lt_of_le_of_ne (hF x) (Ne.symm h)
  exact (not_lt_of_ge hh) (mul_pos (hw x) hp)

theorem finiteEntropy_log_form {α : Type*} [Fintype α] (w F : α → ℝ) :
    finiteEntropy w F = ∑ x, w x * (F x *
      (Real.log (F x) - Real.log (∑ y, w y * F y))) := by
  simp only [finiteEntropy, mul_sub, Finset.sum_sub_distrib, ← mul_assoc, ← Finset.sum_mul]

/-- The exact variational integrand identity, for an actual probability. -/
theorem deviation_sum {α : Type*} [Fintype α] (w F : α → ℝ)
    (hw : (∑ x, w x) = 1) (a : ℝ) :
    (∑ x, w x * deviation (F x) a) =
      finiteEntropy w F + deviation (∑ x, w x * F x) a := by
  simp only [deviation, finiteEntropy, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← mul_assoc, ← Finset.sum_mul, hw, one_mul]
  ring

theorem finiteEntropy_le_deviation {α : Type*} [Fintype α] (w F : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw1 : (∑ x, w x) = 1) (hF : ∀ x, 0 ≤ F x)
    {a : ℝ} (ha : 0 < a) :
    finiteEntropy w F ≤ ∑ x, w x * deviation (F x) a := by
  rw [deviation_sum w F hw1]
  exact le_add_of_nonneg_right (deviation_nonneg (mean_nonneg hw hF) ha)

/-- Scalar log-sum inequality, including either zero summand. -/
theorem two_term_log_sum {x y A B : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hA : 0 < A) (hB : 0 < B) :
    (x + y) * (Real.log (x + y) - Real.log (A + B)) ≤
      x * (Real.log x - Real.log A) + y * (Real.log y - Real.log B) := by
  by_cases hz : x + y = 0
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    simp [hx0, hy0]
  have hp : 0 < x + y := lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hz)
  have hs : 0 < A + B := add_pos hA hB
  have ha := deviation_nonneg hx (div_pos (mul_pos hA hp) hs)
  have hb := deviation_nonneg hy (div_pos (mul_pos hB hp) hs)
  unfold deviation at ha hb
  rw [Real.log_div (mul_ne_zero hA.ne' hz) hs.ne', Real.log_mul hA.ne' hz] at ha
  rw [Real.log_div (mul_ne_zero hB.ne' hz) hs.ne', Real.log_mul hB.ne' hz] at hb
  have he : A * (x + y) / (A + B) + B * (x + y) / (A + B) = x + y := by
    field_simp
  nlinarith only [ha, hb, he]

/-- Convexity in its homogeneous subadditive form. The weight need not
have mass one; positivity treats zero means without division. -/
theorem finiteEntropy_add_le {α : Type*} [Fintype α] (w F G : α → ℝ)
    (hw : ∀ x, 0 < w x) (hF : ∀ x, 0 ≤ F x) (hG : ∀ x, 0 ≤ G x) :
    finiteEntropy w (fun x => F x + G x) ≤ finiteEntropy w F + finiteEntropy w G := by
  classical
  by_cases hA : (∑ x, w x * F x) = 0
  · have hf := eq_zero_of_mean_zero hw hF hA
    simp [hf, finiteEntropy]
  by_cases hB : (∑ x, w x * G x) = 0
  · have hg := eq_zero_of_mean_zero hw hG hB
    simp [hg, finiteEntropy]
  have hAp : 0 < ∑ x, w x * F x :=
    lt_of_le_of_ne (mean_nonneg (fun x => (hw x).le) hF) (Ne.symm hA)
  have hBp : 0 < ∑ x, w x * G x :=
    lt_of_le_of_ne (mean_nonneg (fun x => (hw x).le) hG) (Ne.symm hB)
  have hs : (∑ x, w x * (F x + G x)) = (∑ x, w x * F x) + ∑ x, w x * G x := by
    simp only [mul_add, Finset.sum_add_distrib]
  rw [finiteEntropy_log_form, finiteEntropy_log_form, finiteEntropy_log_form, hs]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    mul_le_mul_of_nonneg_left (two_term_log_sum (hF x) (hG x) hAp hBp) (hw x).le)
  simpa only [mul_add, Finset.sum_add_distrib] using hh

theorem mulLog_scale (c x : ℝ) :
    (c * x) * Real.log (c * x) = c * (x * Real.log x) + c * x * Real.log c := by
  by_cases hc0 : c = 0
  · simp [hc0]
  by_cases hx0 : x = 0
  · simp [hx0]
  rw [Real.log_mul hc0 hx0]
  ring

theorem finiteEntropy_smul {α : Type*} [Fintype α] (w F : α → ℝ) (c : ℝ) :
    finiteEntropy w (fun x => c * F x) = c * finiteEntropy w F := by
  have hs : (∑ x, w x * (c * F x)) = c * ∑ x, w x * F x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  unfold finiteEntropy
  rw [hs, mulLog_scale]
  simp_rw [mulLog_scale]
  simp only [mul_add, Finset.sum_add_distrib]
  simp_rw [show ∀ x, w x * (c * (F x * Real.log (F x))) = c * (w x * (F x * Real.log (F x)))
    from fun x => by ring]
  simp_rw [show ∀ x, w x * (c * F x * Real.log c) = c * (w x * F x) * Real.log c
    from fun x => by ring]
  rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem finiteEntropy_finset_sum {α ι : Type*} [Fintype α]
    (w : α → ℝ) (F : ι → α → ℝ) (hw : ∀ x, 0 < w x)
    (hF : ∀ i x, 0 ≤ F i x) (s : Finset ι) :
    finiteEntropy w (fun x => ∑ i ∈ s, F i x) ≤ ∑ i ∈ s, finiteEntropy w (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [finiteEntropy]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (finiteEntropy_add_le w (F i) (fun x => ∑ j ∈ s, F j x) hw (hF i)
      (fun x => Finset.sum_nonneg fun j _ => hF j x)).trans (add_le_add le_rfl ih)

/-- Finite averaging convexity; homogeneity means no normalization of λ is needed. -/
theorem finiteEntropy_weighted_sum {α ι : Type*} [Fintype α] [Fintype ι]
    (w : α → ℝ) (F : ι → α → ℝ) (q : ι → ℝ) (hw : ∀ x, 0 < w x)
    (hF : ∀ i x, 0 ≤ F i x) (hq : ∀ i, 0 ≤ q i) :
    finiteEntropy w (fun x => ∑ i, q i * F i x) ≤ ∑ i, q i * finiteEntropy w (F i) := by
  have hh := finiteEntropy_finset_sum w (fun i x => q i * F i x) hw
    (fun i x => mul_nonneg (hq i) (hF i x)) Finset.univ
  simpa only [finiteEntropy_smul] using hh

/-- The nonnegative variational integrand gives the actual finite probability
density comparison, including a function of zero mean. -/
theorem finiteEntropy_density_comparison {α : Type*} [Fintype α]
    (w v F : α → ℝ) (hw : ∀ x, 0 < w x) (hw1 : (∑ x, w x) = 1)
    (hv : ∀ x, 0 ≤ v x) (hv1 : (∑ x, v x) = 1) {C : ℝ}
    (hvw : ∀ x, v x ≤ C * w x) (hF : ∀ x, 0 ≤ F x) :
    finiteEntropy v F ≤ C * finiteEntropy w F := by
  by_cases hz : (∑ x, w x * F x) = 0
  · have hf := eq_zero_of_mean_zero hw hF hz
    simp [hf, finiteEntropy]
  have hS : 0 < ∑ x, w x * F x :=
    lt_of_le_of_ne (mean_nonneg (fun x => (hw x).le) hF) (Ne.symm hz)
  calc
    finiteEntropy v F ≤ ∑ x, v x * deviation (F x) (∑ y, w y * F y) :=
      finiteEntropy_le_deviation v F hv hv1 hF hS
    _ ≤ ∑ x, (C * w x) * deviation (F x) (∑ y, w y * F y) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hvw x)
        (deviation_nonneg (hF x) hS)
    _ = C * finiteEntropy w F := by
      rw [show (∑ x, (C * w x) * deviation (F x) (∑ y, w y * F y)) =
          C * ∑ x, w x * deviation (F x) (∑ y, w y * F y) by
        simp only [Finset.mul_sum, mul_assoc]]
      rw [deviation_sum w F hw1, deviation_self, add_zero]

/-- Exact finite product chain rule for the original homogeneous entropy. -/
theorem finiteEntropy_product_chain {α β : Type*} [Fintype α] [Fintype β]
    (w : α → ℝ) (v : β → ℝ) (F : α × β → ℝ) :
    finiteEntropy (fun p => w p.1 * v p.2) F =
      (∑ a, w a * finiteEntropy v (fun b => F (a,b))) +
        finiteEntropy w (fun a => ∑ b, v b * F (a,b)) := by
  simp only [finiteEntropy, Fintype.sum_prod_type, mul_sub,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  ring

/-- Two-factor tensorization, without a probability normalization assumption. -/
theorem finiteEntropy_product_le {α β : Type*} [Fintype α] [Fintype β]
    (w : α → ℝ) (v : β → ℝ) (F : α × β → ℝ)
    (hw : ∀ a, 0 < w a) (hv : ∀ b, 0 ≤ v b) (hF : ∀ p, 0 ≤ F p) :
    finiteEntropy (fun p => w p.1 * v p.2) F ≤
      (∑ a, w a * finiteEntropy v (fun b => F (a,b))) +
        ∑ b, v b * finiteEntropy w (fun a => F (a,b)) := by
  rw [finiteEntropy_product_chain]
  exact add_le_add le_rfl (finiteEntropy_weighted_sum w (fun b a => F (a,b)) v hw
    (fun b a => hF (a,b)) hv)

end PeriodicAttractiveLogGas.FiniteEntropyCalculus
