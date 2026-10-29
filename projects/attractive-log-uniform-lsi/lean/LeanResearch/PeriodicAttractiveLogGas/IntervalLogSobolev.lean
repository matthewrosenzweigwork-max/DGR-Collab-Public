import LeanResearch.PeriodicAttractiveLogGas.FibreEntropy
import LeanResearch.PeriodicAttractiveLogGas.Rothaus
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Intervals

/-! The ordinary interval logarithmic Sobolev inequality supplied at manuscript
2195–2203. The proof uses telescoping, the centered supremum bound, the entropy
bound B/e, and the already proved exact Rothaus inequality. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace PeriodicAttractiveLogGas.IntervalLogSobolev
open FibreEntropy

theorem entropy_scalar_bound {S B : ℝ} (hS : 0 ≤ S) (hB : 0 < B) :
    S * (Real.log B - Real.log S) ≤ B / Real.exp 1 := by
  by_cases hs : S = 0
  · simp only [hs, zero_mul]
    positivity
  have hsp : 0 < S := lt_of_le_of_ne hS (Ne.symm hs)
  have he := Real.exp_pos (1 : ℝ)
  have hh := Real.log_le_sub_one_of_pos (div_pos hB (mul_pos hsp he))
  rw [Real.log_div hB.ne' (mul_ne_zero hs he.ne'),
    Real.log_mul hs he.ne', Real.log_exp] at hh
  have hm := mul_le_mul_of_nonneg_left hh hS
  have hid : S * (B / (S * Real.exp 1) - 1) = B / Real.exp 1 - S := by
    field_simp
  rw [hid] at hm
  nlinarith only [hm]

/-- Finite entropy bounded by a genuine pointwise bound, also at zero mean. -/
theorem finiteEntropy_le_bound {α : Type*} [Fintype α] (w G : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hG : ∀ x, 0 ≤ G x) {B : ℝ}
    (hB : 0 ≤ B) (hGB : ∀ x, G x ≤ B) :
    finiteEntropy w G ≤ B / Real.exp 1 := by
  classical
  by_cases hb : B = 0
  · have hz : G = fun _ => 0 := funext fun x => le_antisymm (hb ▸ hGB x) (hG x)
    simp [hz, hb, finiteEntropy]
  have hbp : 0 < B := lt_of_le_of_ne hB (Ne.symm hb)
  let S := ∑ x, w x * G x
  have hS : 0 ≤ S := Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (hG x)
  have hl : (∑ x, w x * (G x * Real.log (G x))) ≤ S * Real.log B := by
    dsimp only [S]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : G x = 0
    · simp only [hx, zero_mul, mul_zero, le_refl]
    · have hp : 0 < G x := lt_of_le_of_ne (hG x) (Ne.symm hx)
      have hh := mul_le_mul_of_nonneg_left (Real.log_le_log hp (hGB x))
        (mul_nonneg (hw x) (hG x))
      simpa only [mul_assoc] using hh
  have hs := entropy_scalar_bound hS hbp
  unfold finiteEntropy
  change (∑ x, w x * (G x * Real.log (G x))) - S * Real.log S ≤ _
  nlinarith only [hl, hs]

def intervalMean (n : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ i : Fin (n + 1), f i) / (n + 1 : ℕ)

/-- Unit-rate path energy under the actual uniform law on n+1 vertices. -/
def pathEnergy (n : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ k ∈ Finset.range n, (f (k + 1) - f k) ^ 2) / (n + 1 : ℕ)

theorem pathEnergy_nonneg (n : ℕ) (f : ℕ → ℝ) : 0 ≤ pathEnergy n f :=
  div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)

theorem interval_difference_sq_le (n : ℕ) (f : ℕ → ℝ) {i j : ℕ}
    (hi : i ≤ n) (hj : j ≤ n) :
    (f j - f i) ^ 2 ≤ (n : ℝ) * ∑ k ∈ Finset.range n, (f (k + 1) - f k) ^ 2 := by
  have ordered (a b : ℕ) (hab : a ≤ b) (hb : b ≤ n) :
      (f b - f a) ^ 2 ≤ (n : ℝ) * ∑ k ∈ Finset.range n, (f (k + 1) - f k) ^ 2 := by
    have hh := sq_sum_le_card_mul_sum_sq (s := Finset.Ico a b)
      (f := fun k => f (k + 1) - f k)
    rw [Finset.sum_Ico_sub f hab, Nat.card_Ico] at hh
    have hsub : Finset.Ico a b ⊆ Finset.range n := by
      intro k hk
      exact Finset.mem_range.mpr ((Finset.mem_Ico.mp hk).2.trans_le hb)
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => sq_nonneg (f (k + 1) - f k))
    have hc : ((b - a : ℕ) : ℝ) ≤ n := by exact_mod_cast (Nat.sub_le b a).trans hb
    exact hh.trans (mul_le_mul hc hs
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _))
  rcases le_total i j with hij | hji
  · exact ordered i j hij hj
  · have he : (f j - f i) ^ 2 = (f i - f j) ^ 2 := by ring
    rw [he]
    exact ordered j i hji hi

/-- The centered supremum estimate from telescoping, with the source m² factor. -/
theorem centered_sq_le (n : ℕ) (f : ℕ → ℝ) (i : Fin (n + 1)) :
    (f i - intervalMean n f) ^ 2 ≤ (n + 1 : ℕ) ^ 2 * pathEnergy n f := by
  let M : ℝ := (n + 1 : ℕ)
  let E : ℝ := ∑ k ∈ Finset.range n, (f (k + 1) - f k) ^ 2
  have hM : 0 < M := by dsimp [M]; positivity
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum : (∑ j : Fin (n + 1), (f i - f j)) = M * (f i - intervalMean n f) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, intervalMean]
    dsimp only [M]
    field_simp
  have hc := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun j : Fin (n + 1) => f i - f j)
  rw [hsum, Finset.card_univ, Fintype.card_fin] at hc
  have hp : (∑ j : Fin (n + 1), (f i - f j) ^ 2) ≤ M * ((n : ℝ) * E) := by
    calc
      _ ≤ ∑ _ : Fin (n + 1), (n : ℝ) * E := by
        apply Finset.sum_le_sum
        intro j _
        exact interval_difference_sq_le n f (Nat.le_of_lt_succ j.isLt)
          (Nat.le_of_lt_succ i.isLt)
      _ = _ := by simp [M]
  have hp' := mul_le_mul_of_nonneg_left hp hM.le
  have hn : (n : ℝ) ≤ M := by dsimp [M]; norm_num
  have hb : (f i - intervalMean n f) ^ 2 ≤ (n : ℝ) * E := by
    by_contra h
    have hpos := mul_pos (sq_pos_of_pos hM) (sub_pos.mpr (lt_of_not_ge h))
    change (M * (f i - intervalMean n f)) ^ 2 ≤ M * _ at hc
    nlinarith only [hc, hp', hpos]
  have hnE := mul_le_mul_of_nonneg_right hn hE
  calc
    _ ≤ M * E := hb.trans hnE
    _ = _ := by dsimp [M, E, pathEnergy]; field_simp

/-- The precise ordinary interval inequality in the supplied local-box proof. -/
theorem interval_lsi (n : ℕ) (f : ℕ → ℝ) :
    entropy (finiteMeasure (fun _ : Fin (n + 1) => ((n + 1 : ℕ) : ℝ)⁻¹))
      (fun i => f i ^ 2) ≤
        (((2 + 1 / Real.exp 1) * (n + 1 : ℕ) ^ 2 * pathEnergy n f : ℝ) : EReal) := by
  let M : ℝ := (n + 1 : ℕ)
  let μ := finiteMeasure (fun _ : Fin (n + 1) => M⁻¹)
  have hM : 0 < M := by dsimp [M]; positivity
  let : IsProbabilityMeasure μ := by
    simpa only [Fintype.card_fin] using
      uniform_finiteMeasure_probability (α := Fin (n + 1)) (by simp)
  have hi (g : Fin (n + 1) → ℝ) : (∫ i, g i ∂μ) = (∑ i, g i) / M := by
    rw [integral_finiteMeasure _ _ (fun _ => inv_nonneg.mpr hM.le)]
    rw [← Finset.mul_sum]
    ring
  have hm : (∫ i : Fin (n + 1), f i ∂μ) = intervalMean n f := hi _
  let B : ℝ := (n + 1 : ℕ) ^ 2 * pathEnergy n f
  have hB : 0 ≤ B := mul_nonneg (sq_nonneg _) (pathEnergy_nonneg n f)
  have hb (i : Fin (n + 1)) : (f i - intervalMean n f) ^ 2 ≤ B := centered_sq_le n f i
  have hent : entropy μ (fun i : Fin (n + 1) => (f i - intervalMean n f) ^ 2) ≤
      ((B / Real.exp 1 : ℝ) : EReal) := by
    rw [entropy_finiteMeasure _ _ (fun _ => inv_nonneg.mpr hM.le) (fun _ => sq_nonneg _)]
    exact_mod_cast finiteEntropy_le_bound (fun _ : Fin (n + 1) => M⁻¹)
      (fun i => (f i - intervalMean n f) ^ 2) (fun _ => inv_nonneg.mpr hM.le)
      (fun _ => sq_nonneg _) hB hb
  have hv : (∫ i : Fin (n + 1), (f i - intervalMean n f) ^ 2 ∂μ) ≤ B := by
    rw [hi]
    apply (div_le_iff₀ hM).mpr
    calc
      _ ≤ ∑ _ : Fin (n + 1), B := Finset.sum_le_sum fun i _ => hb i
      _ = _ := by simp [M, mul_comm]
  have hbounded : ∃ C : ℝ, ∀ i : Fin (n + 1), |f i| ≤ C := by
    refine ⟨∑ j : Fin (n + 1), |f j|, fun i => ?_⟩
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin (n + 1) => |f j|) (fun j _ => abs_nonneg (f j)) (Finset.mem_univ i)
  have hr := rothaus_centering (μ := μ) (f := fun i : Fin (n + 1) => f i)
    (measurable_of_finite _) hbounded
  rw [hm] at hr
  calc
    _ ≤ _ := hr
    _ ≤ ((B / Real.exp 1 : ℝ) : EReal) + ((2 * B : ℝ) : EReal) := by
      apply add_le_add hent
      exact_mod_cast mul_le_mul_of_nonneg_left hv (show (0 : ℝ) ≤ 2 by norm_num)
    _ = _ := by rw [← EReal.coe_add]; congr 1; dsimp only [B]; ring

/-- Every function on the finite interval is included, with the literal
successive-edge path form. For n=0 the right side and entropy are zero. -/
theorem interval_lsi_fin (n : ℕ) (f : Fin (n + 1) → ℝ) :
    entropy (finiteMeasure (fun _ : Fin (n + 1) => ((n + 1 : ℕ) : ℝ)⁻¹))
      (fun i => f i ^ 2) ≤
        (((2 + 1 / Real.exp 1) * (n + 1 : ℕ) ^ 2 *
          ((∑ k : Fin n, (f k.succ - f k.castSucc) ^ 2) / (n + 1 : ℕ)) : ℝ) : EReal) := by
  let g : ℕ → ℝ := fun k => if h : k < n + 1 then f ⟨k, h⟩ else 0
  have hg (k : Fin (n + 1)) : g k = f k := by simp only [g, dite_eq_left k.isLt]
  have he : pathEnergy n g =
      (∑ k : Fin n, (f k.succ - f k.castSucc) ^ 2) / (n + 1 : ℕ) := by
    unfold pathEnergy
    rw [← Fin.sum_univ_eq_sum_range]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    have ha : g (k + 1) = f k.succ := hg k.succ
    have hb : g k = f k.castSucc := hg k.castSucc
    rw [ha, hb]
  simpa only [hg, he] using interval_lsi n g

end PeriodicAttractiveLogGas.IntervalLogSobolev
