import LeanResearch.PeriodicAttractiveLogGas.IntervalLogSobolev
import LeanResearch.PeriodicAttractiveLogGas.FiniteEntropyCalculus
import Mathlib.Data.Fin.Tuple.Basic

/-! Literal finite product boxes in the supplied proof at source2203–2211.
The energy averages the unit-rate one-coordinate path forms. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.FiniteBoxLogSobolev
open FibreEntropy FiniteEntropyCalculus

abbrev Box (D n : ℕ) := Fin D → Fin (n + 1)

def uniformWeight (D n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ)⁻¹ ^ D

def average (D n : ℕ) (F : Box D n → ℝ) : ℝ := ∑ x, uniformWeight D n * F x

theorem uniformWeight_pos (D n : ℕ) : 0 < uniformWeight D n := by
  unfold uniformWeight
  positivity

@[simp] theorem uniformWeight_one (n : ℕ) :
    uniformWeight 1 n = ((n + 1 : ℕ) : ℝ)⁻¹ := by simp [uniformWeight]

theorem uniformWeight_succ (D n : ℕ) :
    uniformWeight (D + 1) n = ((n + 1 : ℕ) : ℝ)⁻¹ * uniformWeight D n := by
  simp [uniformWeight, pow_succ']

theorem sum_cons (D n : ℕ) (F : Box (D + 1) n → ℝ) :
    (∑ x, F x) = ∑ a : Fin (n + 1), ∑ x : Box D n, F (Fin.cons a x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (D + 1) => Fin (n + 1))).sum_comp F,
    Fintype.sum_prod_type]
  rfl

theorem average_succ (D n : ℕ) (F : Box (D + 1) n → ℝ) :
    average (D + 1) n F =
      ∑ a : Fin (n + 1), ((n + 1 : ℕ) : ℝ)⁻¹ * average D n (fun x => F (Fin.cons a x)) := by
  unfold average
  rw [sum_cons]
  simp only [uniformWeight_succ, Finset.mul_sum, mul_assoc]

@[simp] theorem average_const (D n : ℕ) (c : ℝ) :
    average D n (fun _ => c) = c := by
  simp only [average, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul, uniformWeight, Nat.cast_pow]
  have hm : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hm, one_pow, one_mul]

theorem average_add (D n : ℕ) (F G : Box D n → ℝ) :
    average D n (fun x => F x + G x) = average D n F + average D n G := by
  simp only [average, mul_add, Finset.sum_add_distrib]

theorem average_mul (D n : ℕ) (c : ℝ) (F : Box D n → ℝ) :
    average D n (fun x => c * F x) = c * average D n F := by
  simp only [average, Finset.mul_sum, mul_left_comm]

theorem average_mono (D n : ℕ) {F G : Box D n → ℝ} (h : ∀ x, F x ≤ G x) :
    average D n F ≤ average D n G :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (uniformWeight_pos D n).le

theorem finiteEntropy_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (w F : β → ℝ) :
    finiteEntropy (fun x => w (e x)) (fun x => F (e x)) = finiteEntropy w F := by
  unfold finiteEntropy
  rw [e.sum_comp (fun x => w x * (F x * Real.log (F x))),
    e.sum_comp (fun x => w x * F x)]

def boxEntropy (D n : ℕ) (f : Box D n → ℝ) : ℝ :=
  finiteEntropy (fun _ => uniformWeight D n) (fun x => f x ^ 2)

/-- Literal uniform unit-rate energy of one finite interval. -/
def lineEnergy (n : ℕ) (f : Fin (n + 1) → ℝ) : ℝ :=
  (∑ k : Fin n, (f k.succ - f k.castSucc) ^ 2) / (n + 1 : ℕ)

/-- Sum of conditional one-coordinate path forms on the actual product space. -/
def boxEnergy (D n : ℕ) (f : Box D n → ℝ) : ℝ :=
  average D n (fun x => ∑ i : Fin D, lineEnergy n (fun a => f (Function.update x i a)))

theorem lineEnergy_nonneg (n : ℕ) (f : Fin (n + 1) → ℝ) : 0 ≤ lineEnergy n f :=
  div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)

theorem boxEnergy_nonneg (D n : ℕ) (f : Box D n → ℝ) : 0 ≤ boxEnergy D n f := by
  unfold boxEnergy average
  exact Finset.sum_nonneg fun x _ => mul_nonneg (uniformWeight_pos D n).le
    (Finset.sum_nonneg fun i _ => lineEnergy_nonneg n _)

theorem boxEnergy_succ (D n : ℕ) (f : Box (D + 1) n → ℝ) :
    boxEnergy (D + 1) n f =
      (∑ a : Fin (n + 1), ((n + 1 : ℕ) : ℝ)⁻¹ *
        boxEnergy D n (fun x => f (Fin.cons a x))) +
      average D n (fun x => lineEnergy n (fun a => f (Fin.cons a x))) := by
  unfold boxEnergy
  rw [average_succ]
  have he (a : Fin (n + 1)) (x : Box D n) :
      (∑ i : Fin (D + 1), lineEnergy n (fun b => f (Function.update (Fin.cons a x) i b))) =
      lineEnergy n (fun b => f (Fin.cons b x)) +
        ∑ i : Fin D, lineEnergy n (fun b => f (Fin.cons a (Function.update x i b))) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.update_cons_zero, ← Fin.cons_update]
  simp_rw [he, average_add]
  simp only [mul_add, Finset.sum_add_distrib]
  have hs : (∑ a : Fin (n + 1), ((n + 1 : ℕ) : ℝ)⁻¹ *
      average D n (fun x => lineEnergy n (fun b => f (Fin.cons b x)))) =
      average D n (fun x => lineEnergy n (fun b => f (Fin.cons b x))) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hm : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hs, add_comm]

theorem boxEntropy_succ_le (D n : ℕ) (f : Box (D + 1) n → ℝ) :
    boxEntropy (D + 1) n f ≤
      (∑ a : Fin (n + 1), ((n + 1 : ℕ) : ℝ)⁻¹ *
        boxEntropy D n (fun x => f (Fin.cons a x))) +
      average D n (fun x => finiteEntropy
        (fun _ : Fin (n + 1) => ((n + 1 : ℕ) : ℝ)⁻¹)
        (fun a => f (Fin.cons a x) ^ 2)) := by
  have hh := finiteEntropy_product_le
    (fun _ : Fin (n + 1) => ((n + 1 : ℕ) : ℝ)⁻¹)
    (fun _ : Box D n => uniformWeight D n)
    (fun p => f (Fin.cons p.1 p.2) ^ 2)
    (fun _ => by positivity) (fun _ => (uniformWeight_pos D n).le) (fun _ => sq_nonneg _)
  have he : finiteEntropy
      (fun _ : Fin (n + 1) × Box D n => ((n + 1 : ℕ) : ℝ)⁻¹ * uniformWeight D n)
      (fun p => f (Fin.cons p.1 p.2) ^ 2) = boxEntropy (D + 1) n f := by
    rw [← uniformWeight_succ]
    exact finiteEntropy_equiv (Fin.consEquiv (fun _ : Fin (D + 1) => Fin (n + 1)))
      (fun _ : Box (D + 1) n => uniformWeight (D + 1) n) (fun x => f x ^ 2)
  rw [he] at hh
  exact hh

theorem interval_real_lsi (n : ℕ) (f : Fin (n + 1) → ℝ) :
    finiteEntropy (fun _ : Fin (n + 1) => ((n + 1 : ℕ) : ℝ)⁻¹) (fun x => f x ^ 2) ≤
      (2 + 1 / Real.exp 1) * (n + 1 : ℕ) ^ 2 * lineEnergy n f := by
  have hh := IntervalLogSobolev.interval_lsi_fin n f
  rw [entropy_finiteMeasure _ _ (fun _ => by positivity) (fun _ => sq_nonneg _)] at hh
  exact_mod_cast hh

/-- Every product of intervals of the same length, every real test, with the same side-length
factor as one interval. Dimension zero and singleton sides are included. -/
theorem box_lsi (D n : ℕ) (f : Box D n → ℝ) :
    boxEntropy D n f ≤ (2 + 1 / Real.exp 1) * (n + 1 : ℕ) ^ 2 * boxEnergy D n f := by
  induction D with
  | zero =>
    simp [boxEntropy, boxEnergy, average, uniformWeight, finiteEntropy]
  | succ D ih =>
    let C : ℝ := (2 + 1 / Real.exp 1) * (n + 1 : ℕ) ^ 2
    calc
      boxEntropy (D + 1) n f ≤ _ := boxEntropy_succ_le D n f
      _ ≤ (∑ a : Fin (n + 1), ((n + 1 : ℕ) : ℝ)⁻¹ *
          (C * boxEnergy D n (fun x => f (Fin.cons a x)))) +
          average D n (fun x => C * lineEnergy n (fun a => f (Fin.cons a x))) := by
        apply add_le_add
        · exact Finset.sum_le_sum fun a _ =>
            mul_le_mul_of_nonneg_left (ih (fun x => f (Fin.cons a x))) (by positivity)
        · exact average_mono D n fun x => interval_real_lsi n _
      _ = _ := by
        rw [average_mul, boxEnergy_succ, mul_add]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring


/-- Swapping the sampled coordinate with its old value is an actual involution. -/
def resampleSwap (D n : ℕ) (i : Fin D) : (Fin (n + 1) × Box D n) ≃ (Fin (n + 1) × Box D n) where
  toFun p := (p.2 i, Function.update p.2 i p.1)
  invFun p := (p.2 i, Function.update p.2 i p.1)
  left_inv p := by
    apply Prod.ext
    · simp
    · funext j
      by_cases h : j = i <;> simp [Function.update, h]
  right_inv p := by
    apply Prod.ext
    · simp
    · funext j
      by_cases h : j = i <;> simp [Function.update, h]

theorem sum_update (D n : ℕ) (i : Fin D) (F : Box D n → ℝ) :
    (∑ x : Box D n, ∑ a : Fin (n + 1), F (Function.update x i a)) =
      (n + 1 : ℕ) * ∑ x : Box D n, F x := by
  have hh := (resampleSwap D n i).sum_comp (fun p => F p.2)
  change (∑ p : Fin (n + 1) × Box D n, F (Function.update p.2 i p.1)) =
    ∑ p : Fin (n + 1) × Box D n, F p.2 at hh
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at hh
  rw [Finset.sum_comm]
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh

/-- One forward coordinate edge; it is zero at the last vertex. Thus each
undirected edge in a product path graph is represented exactly once. -/
def forwardSquare {D n : ℕ} (f : Box D n → ℝ) (x : Box D n) (i : Fin D) : ℝ :=
  if h : (x i).val < n then
    (f (Function.update x i ⟨(x i).val + 1, by omega⟩) - f x) ^ 2 else 0

theorem forwardSquare_nonneg {D n : ℕ} (f : Box D n → ℝ) (x : Box D n) (i : Fin D) :
    0 ≤ forwardSquare f x i := by
  unfold forwardSquare
  split
  · exact sq_nonneg _
  · exact le_rfl

@[simp] theorem forwardSquare_update_last {D n : ℕ} (f : Box D n → ℝ) (x : Box D n) (i : Fin D) :
    forwardSquare f (Function.update x i (Fin.last n)) i = 0 := by
  simp [forwardSquare]

@[simp] theorem forwardSquare_update_castSucc {D n : ℕ}
    (f : Box D n → ℝ) (x : Box D n) (i : Fin D) (k : Fin n) :
    forwardSquare f (Function.update x i k.castSucc) i =
      (f (Function.update x i k.succ) - f (Function.update x i k.castSucc)) ^ 2 := by
  simp only [forwardSquare, Function.update_self, Fin.val_castSucc]
  rw [dite_eq_left k.isLt, Function.update_idem]
  rfl

theorem lineEnergy_as_forward {D n : ℕ} (f : Box D n → ℝ) (x : Box D n) (i : Fin D) :
    lineEnergy n (fun a => f (Function.update x i a)) =
      (∑ a : Fin (n + 1), forwardSquare f (Function.update x i a) i) / (n + 1 : ℕ) := by
  rw [Fin.sum_univ_castSucc]
  simp only [forwardSquare_update_last, forwardSquare_update_castSucc, add_zero, lineEnergy]

theorem boxEnergy_eq_forward (D n : ℕ) (f : Box D n → ℝ) :
    boxEnergy D n f = ∑ x : Box D n, uniformWeight D n * ∑ i : Fin D, forwardSquare f x i := by
  have hi (i : Fin D) : (∑ x : Box D n, lineEnergy n (fun a => f (Function.update x i a))) =
      ∑ x : Box D n, forwardSquare f x i := by
    simp_rw [lineEnergy_as_forward]
    rw [← Finset.sum_div, sum_update D n i (fun x => forwardSquare f x i)]
    have hm : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  unfold boxEnergy average
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  calc
    _ = ∑ i : Fin D, ∑ x : Box D n, lineEnergy n (fun a => f (Function.update x i a)) := Finset.sum_comm
    _ = ∑ i : Fin D, ∑ x : Box D n, forwardSquare f x i := by simp only [hi]
    _ = _ := Finset.sum_comm

/-- The literal once-counted positive-coordinate energy with the supplied
vertex weights and forward rates. No probability renormalization is built in. -/
def weightedEnergy (D n : ℕ) (w : Box D n → ℝ) (r : Box D n → Fin D → ℝ)
    (f : Box D n → ℝ) : ℝ :=
  ∑ x, ∑ i, w x * r x i * forwardSquare f x i

theorem energy_density_comparison (D n : ℕ) (w : Box D n → ℝ)
    (r : Box D n → Fin D → ℝ) (f : Box D n → ℝ)
    (hw : ∀ x, 0 ≤ w x) {C r₀ : ℝ} (hC : 0 ≤ C) (hr₀ : 0 < r₀)
    (huw : ∀ x, uniformWeight D n ≤ C * w x)
    (hr : ∀ x i, (x i).val < n → r₀ ≤ r x i) :
    boxEnergy D n f ≤ C / r₀ * weightedEnergy D n w r f := by
  have hpoint (x : Box D n) (i : Fin D) :
      r₀ * (uniformWeight D n * forwardSquare f x i) ≤
        C * (w x * r x i * forwardSquare f x i) := by
    by_cases he : (x i).val < n
    · have hh : r₀ * uniformWeight D n ≤ C * (w x * r x i) := by
        calc
          _ ≤ r₀ * (C * w x) := mul_le_mul_of_nonneg_left (huw x) hr₀.le
          _ = (C * w x) * r₀ := by ring
          _ ≤ (C * w x) * r x i := mul_le_mul_of_nonneg_left (hr x i he) (mul_nonneg hC (hw x))
          _ = _ := by ring
      have hh' := mul_le_mul_of_nonneg_right hh (forwardSquare_nonneg f x i)
      nlinarith only [hh']
    · simp [forwardSquare, he]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint x i))
  have hfinal : r₀ * boxEnergy D n f ≤ C * weightedEnergy D n w r f := by
    rw [boxEnergy_eq_forward]
    simpa only [weightedEnergy, Finset.mul_sum, mul_assoc] using hs
  calc
    _ ≤ (C * weightedEnergy D n w r f) / r₀ :=
      (le_div_iff₀ hr₀).mpr (by simpa only [mul_comm] using hfinal)
    _ = _ := by ring

/-- Density oscillation and actual coordinate-rate lower bounds transfer the
proved uniform cube inequality. The coefficient contains no hidden dimension
or normalization factor. -/
theorem weighted_box_lsi (D n : ℕ) (w : Box D n → ℝ) (r : Box D n → Fin D → ℝ)
    (f : Box D n → ℝ) (hw : ∀ x, 0 ≤ w x) (hw1 : (∑ x, w x) = 1)
    {C r₀ : ℝ} (hC : 0 ≤ C) (hr₀ : 0 < r₀)
    (hwu : ∀ x, w x ≤ C * uniformWeight D n)
    (huw : ∀ x, uniformWeight D n ≤ C * w x)
    (hr : ∀ x i, (x i).val < n → r₀ ≤ r x i) :
    finiteEntropy w (fun x => f x ^ 2) ≤
      C ^ 2 * (2 + 1 / Real.exp 1) * (n + 1 : ℕ) ^ 2 / r₀ * weightedEnergy D n w r f := by
  have hu1 : (∑ _ : Box D n, uniformWeight D n) = 1 := by
    simpa only [average, mul_one] using average_const D n (1 : ℝ)
  have hE := energy_density_comparison D n w r f hw hC hr₀ huw hr
  have hK : 0 ≤ (2 + 1 / Real.exp 1) * (n + 1 : ℕ) ^ 2 := by positivity
  calc
    _ ≤ C * boxEntropy D n f :=
      finiteEntropy_density_comparison (fun _ => uniformWeight D n) w (fun x => f x ^ 2)
        (fun _ => uniformWeight_pos D n) hu1 hw hw1 hwu (fun _ => sq_nonneg _)
    _ ≤ C * ((2 + 1 / Real.exp 1) * (n + 1 : ℕ) ^ 2 * boxEnergy D n f) :=
      mul_le_mul_of_nonneg_left (box_lsi D n f) hC
    _ ≤ C * ((2 + 1 / Real.exp 1) * (n + 1 : ℕ) ^ 2 *
        (C / r₀ * weightedEnergy D n w r f)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE hK) hC
    _ = _ := by ring

theorem weightedEnergy_nonneg (D n : ℕ) (w : Box D n → ℝ)
    (r : Box D n → Fin D → ℝ) (f : Box D n → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hr : ∀ x i, (x i).val < n → 0 ≤ r x i) :
    0 ≤ weightedEnergy D n w r f := by
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro i _
  by_cases he : (x i).val < n
  · exact mul_nonneg (mul_nonneg (hw x) (hr x i he)) (forwardSquare_nonneg f x i)
  · simp [forwardSquare, he]

/-- The bound is also stated in the manuscript's actual extended entropy,
on the literal finite weighted measure, with the same once-counted energy. -/
theorem weighted_box_entropy (D n : ℕ) (w : Box D n → ℝ) (r : Box D n → Fin D → ℝ)
    (f : Box D n → ℝ) (hw : ∀ x, 0 ≤ w x) (hw1 : (∑ x, w x) = 1)
    {C r₀ : ℝ} (hC : 0 ≤ C) (hr₀ : 0 < r₀)
    (hwu : ∀ x, w x ≤ C * uniformWeight D n)
    (huw : ∀ x, uniformWeight D n ≤ C * w x)
    (hr : ∀ x i, (x i).val < n → r₀ ≤ r x i) :
    entropy (finiteMeasure w) (fun x => f x ^ 2) ≤
      ((C ^ 2 * (2 + 1 / Real.exp 1) * (n + 1 : ℕ) ^ 2 / r₀ *
        weightedEnergy D n w r f : ℝ) : EReal) := by
  rw [entropy_finiteMeasure w _ hw (fun _ => sq_nonneg _)]
  exact_mod_cast weighted_box_lsi D n w r f hw hw1 hC hr₀ hwu huw hr

/-- On boxes whose squared side length is at most K N, rates at least c N
give a conditional ordinary LSI coefficient independent of N and the box.
Both probability and the two density comparisons remain explicit. -/
theorem weighted_box_entropy_uniform (D n N : ℕ) (hN : 0 < N)
    (w : Box D n → ℝ) (r : Box D n → Fin D → ℝ) (f : Box D n → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw1 : (∑ x, w x) = 1)
    {C c K : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hside : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ K * N)
    (hwu : ∀ x, w x ≤ C * uniformWeight D n)
    (huw : ∀ x, uniformWeight D n ≤ C * w x)
    (hr : ∀ x i, (x i).val < n → c * N ≤ r x i) :
    entropy (finiteMeasure w) (fun x => f x ^ 2) ≤
      ((C ^ 2 * (2 + 1 / Real.exp 1) * K / c * weightedEnergy D n w r f : ℝ) : EReal) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hden := mul_pos hc hNr
  have hE := weightedEnergy_nonneg D n w r f hw (fun x i hi => hden.le.trans (hr x i hi))
  have hcoef : C ^ 2 * (2 + 1 / Real.exp 1) * (n + 1 : ℕ) ^ 2 / (c * N) ≤
      C ^ 2 * (2 + 1 / Real.exp 1) * K / c := by
    apply (div_le_iff₀ hden).mpr
    calc
      _ ≤ (C ^ 2 * (2 + 1 / Real.exp 1)) * (K * N) :=
        mul_le_mul_of_nonneg_left hside (by positivity)
      _ = _ := by field_simp
  have hh := (weighted_box_lsi D n w r f hw hw1 hC hden hwu huw hr).trans
    (mul_le_mul_of_nonneg_right hcoef hE)
  rw [entropy_finiteMeasure w _ hw (fun _ => sq_nonneg _)]
  exact_mod_cast hh

end PeriodicAttractiveLogGas.FiniteBoxLogSobolev
