import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Intervals

/-! Actual finite counts in the counting subsection of `thm:canonical-pairs`.
Multiplicity vectors and words have total length `2 * k` and no singleton
entry/symbol. Analytic moments and canonicality are not inputs to these counts. -/

noncomputable section
open Finset
open scoped BigOperators

namespace PeriodicAttractiveLogGas.CanonicalPairCounts

/-- Actual multiplicity vectors, represented by finitely supported maps on
the finite alphabet. Membership retains exactly the source conditions. -/
def multiplicityVectors (m k : ℕ) : Finset (Fin m →₀ ℕ) :=
  ((Finset.univ : Finset (Fin m)).finsuppAntidiag (2 * k)).filter
    (fun a => ∀ i, a i ≠ 1)

def A (m k : ℕ) : ℕ := (multiplicityVectors m k).card

/-- Number of occurrences of a symbol in an actual word. -/
def wordMultiplicity {m k : ℕ} (w : Fin (2 * k) → Fin m) (i : Fin m) : ℕ :=
  (Finset.univ.filter (fun j => w j = i)).card

def singletonFreeWords (m k : ℕ) : Finset (Fin (2 * k) → Fin m) :=
  Finset.univ.filter (fun w => ∀ i, wordMultiplicity w i ≠ 1)

def B (m k : ℕ) : ℕ := (singletonFreeWords m k).card

def nonzeroSupport {m : ℕ} (a : Fin m → ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => a i ≠ 0)

@[simp] theorem mem_multiplicityVectors {m k : ℕ} {a : Fin m →₀ ℕ} :
    a ∈ multiplicityVectors m k ↔ (∑ i, a i) = 2 * k ∧ ∀ i, a i ≠ 1 := by
  simp [multiplicityVectors, Finset.mem_finsuppAntidiag]

@[simp] theorem mem_singletonFreeWords {m k : ℕ} {w : Fin (2 * k) → Fin m} :
    w ∈ singletonFreeWords m k ↔ ∀ i, wordMultiplicity w i ≠ 1 := by
  simp [singletonFreeWords]

@[simp] theorem mem_nonzeroSupport {m : ℕ} {a : Fin m → ℕ} {i : Fin m} :
    i ∈ nonzeroSupport a ↔ a i ≠ 0 := by simp [nonzeroSupport]

theorem sum_nonzeroSupport {m : ℕ} (a : Fin m → ℕ) :
    ∑ i ∈ nonzeroSupport a, a i = ∑ i, a i := by
  exact Finset.sum_filter_ne_zero (f := a) Finset.univ

theorem support_card_le {m k : ℕ} {a : Fin m → ℕ}
    (hsum : (∑ i, a i) = 2 * k) (hno : ∀ i, a i ≠ 1) :
    (nonzeroSupport a).card ≤ min m k := by
  apply le_min (by simpa using Finset.card_le_card (Finset.subset_univ (nonzeroSupport a)))
  have htwo : 2 * (nonzeroSupport a).card ≤ 2 * k := by
    calc
      2 * (nonzeroSupport a).card = ∑ i ∈ nonzeroSupport a, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ nonzeroSupport a, a i := Finset.sum_le_sum (fun i hi => by
        have h0 := mem_nonzeroSupport.mp hi
        have h1 := hno i
        omega)
      _ = 2 * k := (sum_nonzeroSupport a).trans hsum
  omega

theorem support_nonempty {m k : ℕ} {a : Fin m → ℕ} (hk : 1 ≤ k)
    (hsum : (∑ i, a i) = 2 * k) : (nonzeroSupport a).Nonempty := by
  by_contra h
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  have hz := (sum_nonzeroSupport a).trans hsum
  rw [he] at hz
  simp only [Finset.sum_empty] at hz
  omega

theorem sum_wordMultiplicity {m k : ℕ} (w : Fin (2 * k) → Fin m) :
    (∑ i, wordMultiplicity w i) = 2 * k := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin (2 * k))))
    (t := (Finset.univ : Finset (Fin m))) (f := w) (fun _ _ => Finset.mem_univ _)
  simpa [wordMultiplicity] using h.symm

theorem word_support_card_le {m k : ℕ} {w : Fin (2 * k) → Fin m}
    (hw : w ∈ singletonFreeWords m k) :
    (nonzeroSupport (wordMultiplicity w)).card ≤ min m k :=
  support_card_le (sum_wordMultiplicity w) (mem_singletonFreeWords.mp hw)

theorem B_le_all_words (m k : ℕ) : B m k ≤ m ^ (2 * k) := by
  have h := Finset.card_le_card
    (Finset.filter_subset (s := (Finset.univ : Finset (Fin (2 * k) → Fin m)))
      (p := fun w => ∀ i, wordMultiplicity w i ≠ 1))
  simpa [B, singletonFreeWords, Fintype.card_fun] using h

/-- Exact support-fiber decomposition; no estimate is built into the definition. -/
theorem A_eq_sum_support_fibers (m k : ℕ) :
    A m k = ∑ s : Finset (Fin m),
      ((multiplicityVectors m k).filter
        (fun (a : Fin m →₀ ℕ) => nonzeroSupport (fun i => a i) = s)).card := by
  unfold A
  exact Finset.card_eq_sum_card_fiberwise
    (f := fun (a : Fin m →₀ ℕ) => nonzeroSupport (fun i => a i))
    (fun _ _ => Finset.mem_univ _)

theorem B_eq_sum_support_fibers (m k : ℕ) :
    B m k = ∑ s : Finset (Fin m),
      ((singletonFreeWords m k).filter (fun w => nonzeroSupport (wordMultiplicity w) = s)).card := by
  exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)

theorem word_value_mem_support {m k : ℕ} (w : Fin (2 * k) → Fin m) (j : Fin (2 * k)) :
    w j ∈ nonzeroSupport (wordMultiplicity w) := by
  rw [mem_nonzeroSupport, wordMultiplicity]
  exact Finset.card_ne_zero.mpr ⟨j, by simp⟩

/-- A word using precisely `s` injects into all words on the alphabet `s`. -/
theorem word_support_fiber_le (m k : ℕ) (s : Finset (Fin m)) :
    ((singletonFreeWords m k).filter
      (fun w => nonzeroSupport (wordMultiplicity w) = s)).card ≤ s.card ^ (2 * k) := by
  let T := (singletonFreeWords m k).filter
    (fun w => nonzeroSupport (wordMultiplicity w) = s)
  let f : T → (Fin (2 * k) → s) := fun w j =>
    ⟨w.val j, by
      have hs := (Finset.mem_filter.mp w.prop).2
      rw [← hs]
      exact word_value_mem_support w.val j⟩
  have hinj : Function.Injective f := by
    intro w v h
    apply Subtype.ext
    funext j
    exact congrArg Subtype.val (congrFun h j)
  have hcard := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using hcard

/-- Subtracting two on the occupied support is an exact stars-and-bars
bijection, including multiplicities equal to two. -/
theorem multiplicity_support_fiber_card (m k : ℕ) (s : Finset (Fin m))
    (hsk : s.card ≤ k) :
    ((multiplicityVectors m k).filter
      (fun (a : Fin m →₀ ℕ) => nonzeroSupport (fun i => a i) = s)).card =
      (s.card + (2 * k - 2 * s.card) - 1).choose (2 * k - 2 * s.card) := by
  let T := (multiplicityVectors m k).filter
    (fun (a : Fin m →₀ ℕ) => nonzeroSupport (fun i => a i) = s)
  let peel : (Fin m →₀ ℕ) → (Fin m →₀ ℕ) :=
    Finsupp.mapRange (fun n : ℕ => n - 2) rfl
  let fill : (Fin m →₀ ℕ) → (Fin m →₀ ℕ) :=
    fun b => Finsupp.indicator s (fun i _ => b i + 2)
  have hdata {a : Fin m →₀ ℕ} (ha : a ∈ T) :
      (∑ i, a i) = 2 * k ∧ (∀ i, a i ≠ 1) ∧ nonzeroSupport (fun i => a i) = s := by
    rcases Finset.mem_filter.mp ha with ⟨ha, hs⟩
    exact ⟨(mem_multiplicityVectors.mp ha).1, (mem_multiplicityVectors.mp ha).2, hs⟩
  have hge {a : Fin m →₀ ℕ} (ha : a ∈ T) {i : Fin m} (hi : i ∈ s) : 2 ≤ a i := by
    have hd := hdata ha
    have h0 : a i ≠ 0 := mem_nonzeroSupport.mp (hd.2.2 ▸ hi)
    have h1 := hd.2.1 i
    omega
  have hzero {a : Fin m →₀ ℕ} (ha : a ∈ T) {i : Fin m} (hi : i ∉ s) : a i = 0 := by
    have hd := hdata ha
    by_contra hn
    exact hi (hd.2.2 ▸ mem_nonzeroSupport.mpr hn)
  have hpeel {a : Fin m →₀ ℕ} (ha : a ∈ T) :
      peel a ∈ s.finsuppAntidiag (2 * k - 2 * s.card) := by
    apply Finset.mem_finsuppAntidiag.mpr
    constructor
    · change (∑ i ∈ s, (a i - 2)) = _
      rw [Finset.sum_tsub_distrib s (fun i hi => hge ha hi)]
      have hs : (∑ i ∈ s, a i) = 2 * k := by
        rw [← (hdata ha).2.2, sum_nonzeroSupport]
        exact (hdata ha).1
      simp [hs, Nat.mul_comm]
    · apply Finsupp.support_mapRange.trans
      intro i hi
      rw [← (hdata ha).2.2, mem_nonzeroSupport]
      exact Finsupp.mem_support_iff.mp hi
  have hfill_support (b : Fin m →₀ ℕ) : nonzeroSupport (fun i => fill b i) = s := by
    ext i
    by_cases hi : i ∈ s <;> simp [fill, Finsupp.indicator_apply, hi]
  have hfill {b : Fin m →₀ ℕ} (hb : b ∈ s.finsuppAntidiag (2 * k - 2 * s.card)) :
      fill b ∈ T := by
    apply Finset.mem_filter.mpr
    refine ⟨mem_multiplicityVectors.mpr ⟨?_, ?_⟩, hfill_support b⟩
    · rw [← sum_nonzeroSupport (fun i => fill b i), hfill_support]
      have heq : (∑ i ∈ s, fill b i) = ∑ i ∈ s, (b i + 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finsupp.indicator_of_mem hi _
      rw [heq, Finset.sum_add_distrib, (Finset.mem_finsuppAntidiag.mp hb).1]
      simp only [Finset.sum_const, smul_eq_mul]
      omega
    · intro i
      by_cases hi : i ∈ s <;> simp [fill, Finsupp.indicator_apply, hi]
  have hleft {a : Fin m →₀ ℕ} (ha : a ∈ T) : fill (peel a) = a := by
    ext i
    by_cases hi : i ∈ s
    · simp only [fill, Finsupp.indicator_apply, dite_eq_left hi, peel, Finsupp.mapRange_apply]
      exact Nat.sub_add_cancel (hge ha hi)
    · simp [fill, Finsupp.indicator_apply, hi, hzero ha hi]
  have hright {b : Fin m →₀ ℕ} (hb : b ∈ s.finsuppAntidiag (2 * k - 2 * s.card)) :
      peel (fill b) = b := by
    ext i
    by_cases hi : i ∈ s
    · simp [peel, fill, Finsupp.indicator_apply, hi]
    · have hb0 : b i = 0 := by
        apply Finsupp.notMem_support_iff.mp
        exact fun h => hi ((Finset.mem_finsuppAntidiag.mp hb).2 h)
      simp [peel, fill, Finsupp.indicator_apply, hi, hb0]
  have hcard : T.card = (s.finsuppAntidiag (2 * k - 2 * s.card)).card :=
    Finset.card_nbij' peel fill (fun _ ha => hpeel ha) (fun _ hb => hfill hb)
      (fun _ ha => hleft ha) (fun _ hb => hright hb)
  exact hcard.trans (Finset.card_finsuppAntidiag_nat_eq_choose _)

theorem multiplicity_support_fiber_le (m k : ℕ) (s : Finset (Fin m)) (hsk : s.card ≤ k) :
    ((multiplicityVectors m k).filter
      (fun (a : Fin m →₀ ℕ) => nonzeroSupport (fun i => a i) = s)).card ≤
      2 ^ (2 * k - s.card - 1) := by
  rw [multiplicity_support_fiber_card m k s hsk]
  have he : s.card + (2 * k - 2 * s.card) - 1 = 2 * k - s.card - 1 := by omega
  simpa only [he] using Nat.choose_le_two_pow (s.card + (2 * k - 2 * s.card) - 1)
    (2 * k - 2 * s.card)

/-- Precisely the possible occupied supports when `k` is positive. -/
def admissibleSupports (m k : ℕ) : Finset (Finset (Fin m)) :=
  Finset.univ.filter (fun s => 1 ≤ s.card ∧ s.card ≤ k)

@[simp] theorem mem_admissibleSupports {m k : ℕ} {s : Finset (Fin m)} :
    s ∈ admissibleSupports m k ↔ 1 ≤ s.card ∧ s.card ≤ k := by
  simp [admissibleSupports]

theorem sum_admissibleSupports (m k : ℕ) (f : ℕ → ℕ) :
    ∑ s ∈ admissibleSupports m k, f s.card =
      ∑ r ∈ Finset.Icc 1 (min m k), m.choose r * f r := by
  have hmap : ∀ s ∈ admissibleSupports m k, s.card ∈ Finset.Icc 1 (min m k) := by
    intro s hs
    have hm : s.card ≤ m := by simpa using Finset.card_le_card (Finset.subset_univ s)
    exact Finset.mem_Icc.mpr ⟨(mem_admissibleSupports.mp hs).1,
      le_min hm (mem_admissibleSupports.mp hs).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to' hmap f]
  apply Finset.sum_congr rfl
  intro r hr
  have hr1 := (Finset.mem_Icc.mp hr).1
  have hrk := (Finset.mem_Icc.mp hr).2.trans (min_le_right m k)
  have he : (admissibleSupports m k).filter (fun s => s.card = r) =
      (Finset.univ : Finset (Fin m)).powersetCard r := by
    ext s
    simp only [Finset.mem_filter, mem_admissibleSupports, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨⟨h ▸ hr1, h ▸ hrk⟩, h⟩
  rw [he]
  simp [Finset.card_powersetCard, smul_eq_mul]

theorem A_eq_sum_choose (m k : ℕ) (hk : 1 ≤ k) :
    A m k = ∑ r ∈ Finset.Icc 1 (min m k),
      m.choose r * (r + (2 * k - 2 * r) - 1).choose (2 * k - 2 * r) := by
  have hmap : ∀ a ∈ multiplicityVectors m k,
      nonzeroSupport (fun i => a i) ∈ admissibleSupports m k := by
    intro a ha
    have hd := mem_multiplicityVectors.mp ha
    apply mem_admissibleSupports.mpr
    exact ⟨(support_nonempty hk hd.1).card_pos,
      (support_card_le hd.1 hd.2).trans (min_le_right m k)⟩
  calc
    A m k = ∑ s ∈ admissibleSupports m k,
        ((multiplicityVectors m k).filter
          (fun (a : Fin m →₀ ℕ) => nonzeroSupport (fun i => a i) = s)).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ = ∑ s ∈ admissibleSupports m k,
        (s.card + (2 * k - 2 * s.card) - 1).choose (2 * k - 2 * s.card) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact multiplicity_support_fiber_card m k s (mem_admissibleSupports.mp hs).2
    _ = _ := sum_admissibleSupports m k
      (fun r => (r + (2 * k - 2 * r) - 1).choose (2 * k - 2 * r))

theorem A_le_sum_choose (m k : ℕ) (hk : 1 ≤ k) :
    A m k ≤ ∑ r ∈ Finset.Icc 1 (min m k), m.choose r * 2 ^ (2 * k - r - 1) := by
  rw [A_eq_sum_choose m k hk]
  apply Finset.sum_le_sum
  intro r hr
  apply Nat.mul_le_mul_left
  have hrk := (Finset.mem_Icc.mp hr).2.trans (min_le_right m k)
  have he : r + (2 * k - 2 * r) - 1 = 2 * k - r - 1 := by omega
  simpa only [he] using Nat.choose_le_two_pow (r + (2 * k - 2 * r) - 1)
    (2 * k - 2 * r)

theorem B_le_sum_choose (m k : ℕ) (hk : 1 ≤ k) :
    B m k ≤ ∑ r ∈ Finset.Icc 1 (min m k), m.choose r * r ^ (2 * k) := by
  have hmap : ∀ w ∈ singletonFreeWords m k,
      nonzeroSupport (wordMultiplicity w) ∈ admissibleSupports m k := by
    intro w hw
    exact mem_admissibleSupports.mpr
      ⟨(support_nonempty hk (sum_wordMultiplicity w)).card_pos,
        (word_support_card_le hw).trans (min_le_right m k)⟩
  calc
    B m k = ∑ s ∈ admissibleSupports m k,
        ((singletonFreeWords m k).filter
          (fun w => nonzeroSupport (wordMultiplicity w) = s)).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ s ∈ admissibleSupports m k, s.card ^ (2 * k) :=
      Finset.sum_le_sum (fun s _ => word_support_fiber_le m k s)
    _ = _ := sum_admissibleSupports m k (fun r => r ^ (2 * k))

/-- A convenient coarser stars-and-bars bound also controls the small-alphabet case. -/
theorem A_le_all_multiplicities (m k : ℕ) :
    A m k ≤ (m + 2 * k - 1).choose (2 * k) := by
  have hc := Finset.card_le_card
    (Finset.filter_subset (s := (Finset.univ : Finset (Fin m)).finsuppAntidiag (2 * k))
      (p := fun a => ∀ i, a i ≠ 1))
  simpa [A, multiplicityVectors, Finset.card_finsuppAntidiag_nat_eq_choose] using hc

theorem A_le_eight_pow {m k : ℕ} (hmk : m ≤ k) : A m k ≤ 8 ^ k := by
  calc
    A m k ≤ (m + 2 * k - 1).choose (2 * k) := A_le_all_multiplicities m k
    _ ≤ 2 ^ (m + 2 * k - 1) := Nat.choose_le_two_pow _ _
    _ ≤ 2 ^ (3 * k) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 8 ^ k := by rw [pow_mul]; norm_num

theorem exp_one_ge_two : 2 ≤ Real.exp 1 := by
  have h := Real.add_one_le_exp (1 : ℝ)
  linarith

theorem count_product_le_of_le {m k : ℕ} (hmk : m ≤ k) :
    (A m k : ℝ) * (B m k : ℝ) ≤ (4 * Real.exp 1 ^ 2) ^ k * (m : ℝ) ^ (2 * k) := by
  have ha : (A m k : ℝ) ≤ (8 : ℝ) ^ k := by exact_mod_cast A_le_eight_pow hmk
  have hb : (B m k : ℝ) ≤ (m : ℝ) ^ (2 * k) := by exact_mod_cast B_le_all_words m k
  have he : (8 : ℝ) ≤ 4 * Real.exp 1 ^ 2 := by nlinarith [exp_one_ge_two]
  calc
    (A m k : ℝ) * (B m k : ℝ) ≤ (8 : ℝ) ^ k * (m : ℝ) ^ (2 * k) :=
      mul_le_mul ha hb (by positivity) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) he _) (by positivity)

/-- The source geometric estimate with the harmless larger prefactor two. -/
theorem sum_exp_powers_le (k : ℕ) :
    (∑ r ∈ Finset.Icc 1 k, Real.exp 1 ^ r) ≤ 2 * Real.exp 1 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), pow_succ]
    have h := mul_le_mul_of_nonneg_right exp_one_ge_two
      (pow_nonneg (Real.exp_pos 1).le k)
    nlinarith

theorem sum_descending_two_powers {n j : ℕ} (hj : j ≤ n) :
    (∑ r ∈ Finset.Icc 1 j, (2 : ℝ) ^ (n - r)) = 2 ^ n - 2 ^ (n - j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih (by omega)]
    have he : n - j = (n - (j + 1)) + 1 := by omega
    rw [he, pow_succ]
    ring

theorem pow_div_factorial_mono {m r k : ℕ} (hrk : r ≤ k) (hkm : k ≤ m) :
    (m : ℝ) ^ r / (r.factorial : ℝ) ≤ (m : ℝ) ^ k / (k.factorial : ℝ) := by
  induction k with
  | zero =>
    have hr : r = 0 := by omega
    subst r
    exact le_rfl
  | succ k ih =>
    by_cases hr : r = k + 1
    · subst r; exact le_rfl
    have hprev := ih (by omega) (by omega)
    apply hprev.trans
    have hkpos : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hkp : (0 : ℝ) < ((k + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos (k + 1)
    apply (div_le_div_iff₀ hkpos hkp).mpr
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    have hm : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hkm
    have h := mul_le_mul_of_nonneg_left hm
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg m) k) hkpos.le)
    nlinarith

theorem A_le_of_ge {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    (A m k : ℝ) ≤ ((m : ℝ) ^ k / (k.factorial : ℝ)) * 2 ^ (2 * k - 1) := by
  have ha : (A m k : ℝ) ≤ ∑ r ∈ Finset.Icc 1 k,
      (m.choose r : ℝ) * 2 ^ (2 * k - r - 1) := by
    have h := A_le_sum_choose m k hk
    rw [min_eq_right hkm] at h
    exact_mod_cast h
  calc
    (A m k : ℝ) ≤ ∑ r ∈ Finset.Icc 1 k,
        (m.choose r : ℝ) * 2 ^ (2 * k - r - 1) := ha
    _ ≤ ∑ r ∈ Finset.Icc 1 k,
        ((m : ℝ) ^ k / (k.factorial : ℝ)) * 2 ^ (2 * k - r - 1) := by
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (Nat.choose_le_pow_div r m).trans
        (pow_div_factorial_mono (Finset.mem_Icc.mp hr).2 hkm)
    _ = ((m : ℝ) ^ k / (k.factorial : ℝ)) *
        (∑ r ∈ Finset.Icc 1 k, (2 : ℝ) ^ ((2 * k - 1) - r)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      congr 2
      omega
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [sum_descending_two_powers (by omega : k ≤ 2 * k - 1)]
      exact sub_le_self _ (by positivity)

theorem power_div_factorial_le_exp_power (r : ℕ) :
    (r : ℝ) ^ r / (r.factorial : ℝ) ≤ Real.exp 1 ^ r := by
  rw [← Real.exp_nat_mul, mul_one]
  exact Real.pow_div_factorial_le_exp (r : ℝ) (Nat.cast_nonneg r) r

theorem choose_mul_power_le {m k r : ℕ} (hrk : r ≤ k) (hkm : k ≤ m) :
    (m.choose r : ℝ) * (r : ℝ) ^ (2 * k) ≤
      Real.exp 1 ^ r * (m : ℝ) ^ k * (k : ℝ) ^ k := by
  have hmon : (m : ℝ) ^ r * (k : ℝ) ^ (2 * k - r) ≤
      (m : ℝ) ^ k * (k : ℝ) ^ k := by
    calc
      (m : ℝ) ^ r * (k : ℝ) ^ (2 * k - r) =
          ((m : ℝ) ^ r * (k : ℝ) ^ (k - r)) * (k : ℝ) ^ k := by
        rw [show 2 * k - r = (k - r) + k by omega, pow_add]
        ring
      _ ≤ ((m : ℝ) ^ r * (m : ℝ) ^ (k - r)) * (k : ℝ) ^ k := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hkm) _
      _ = _ := by rw [← pow_add, show r + (k - r) = k by omega]
  calc
    (m.choose r : ℝ) * (r : ℝ) ^ (2 * k) ≤
        ((m : ℝ) ^ r / (r.factorial : ℝ)) * (r : ℝ) ^ (2 * k) :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div r m) (by positivity)
    _ = ((r : ℝ) ^ r / (r.factorial : ℝ)) *
        ((m : ℝ) ^ r * (r : ℝ) ^ (2 * k - r)) := by
      conv_lhs => rw [show 2 * k = r + (2 * k - r) by omega, pow_add]
      ring
    _ ≤ Real.exp 1 ^ r * ((m : ℝ) ^ r * (k : ℝ) ^ (2 * k - r)) := by
      apply mul_le_mul (power_div_factorial_le_exp_power r)
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hrk) _
      · positivity
      · positivity
    _ ≤ Real.exp 1 ^ r * ((m : ℝ) ^ k * (k : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_left hmon (by positivity)
    _ = _ := by ring

theorem B_le_of_ge {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    (B m k : ℝ) ≤ 2 * Real.exp 1 ^ k * (m : ℝ) ^ k * (k : ℝ) ^ k := by
  have hb : (B m k : ℝ) ≤ ∑ r ∈ Finset.Icc 1 k,
      (m.choose r : ℝ) * (r : ℝ) ^ (2 * k) := by
    have h := B_le_sum_choose m k hk
    rw [min_eq_right hkm] at h
    exact_mod_cast h
  calc
    (B m k : ℝ) ≤ ∑ r ∈ Finset.Icc 1 k,
        (m.choose r : ℝ) * (r : ℝ) ^ (2 * k) := hb
    _ ≤ ∑ r ∈ Finset.Icc 1 k,
        Real.exp 1 ^ r * ((m : ℝ) ^ k * (k : ℝ) ^ k) := by
      apply Finset.sum_le_sum
      intro r hr
      simpa only [mul_assoc] using choose_mul_power_le (Finset.mem_Icc.mp hr).2 hkm
    _ = (∑ r ∈ Finset.Icc 1 k, Real.exp 1 ^ r) * ((m : ℝ) ^ k * (k : ℝ) ^ k) := by
      rw [Finset.sum_mul]
    _ ≤ (2 * Real.exp 1 ^ k) * ((m : ℝ) ^ k * (k : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_right (sum_exp_powers_le k) (by positivity)
    _ = _ := by ring

theorem count_product_le_of_ge {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    (A m k : ℝ) * (B m k : ℝ) ≤ (4 * Real.exp 1 ^ 2) ^ k * (m : ℝ) ^ (2 * k) := by
  have ht : (2 : ℝ) ^ (2 * k - 1) * 2 = 4 ^ k := by
    rw [← pow_succ, show 2 * k - 1 + 1 = 2 * k by omega, pow_mul]
    norm_num
  have hm : (m : ℝ) ^ (2 * k) = (m : ℝ) ^ k * (m : ℝ) ^ k := by
    rw [two_mul, pow_add]
  have he : (4 * Real.exp 1 ^ 2) ^ k =
      (4 : ℝ) ^ k * Real.exp 1 ^ k * Real.exp 1 ^ k := by
    rw [mul_pow, ← pow_mul, two_mul, pow_add]
    ring
  calc
    (A m k : ℝ) * (B m k : ℝ) ≤
        (((m : ℝ) ^ k / (k.factorial : ℝ)) * 2 ^ (2 * k - 1)) *
          (2 * Real.exp 1 ^ k * (m : ℝ) ^ k * (k : ℝ) ^ k) :=
      mul_le_mul (A_le_of_ge hk hkm) (B_le_of_ge hk hkm) (by positivity) (by positivity)
    _ = ((2 ^ (2 * k - 1) * 2) * ((m : ℝ) ^ k * (m : ℝ) ^ k)) *
        Real.exp 1 ^ k * ((k : ℝ) ^ k / (k.factorial : ℝ)) := by ring
    _ = ((4 : ℝ) ^ k * (m : ℝ) ^ (2 * k)) *
        Real.exp 1 ^ k * ((k : ℝ) ^ k / (k.factorial : ℝ)) := by rw [ht, ← hm]
    _ ≤ ((4 : ℝ) ^ k * (m : ℝ) ^ (2 * k)) * Real.exp 1 ^ k * Real.exp 1 ^ k :=
      mul_le_mul_of_nonneg_left (power_div_factorial_le_exp_power k) (by positivity)
    _ = _ := by rw [he]; ring

/-- The counting estimate in `thm:canonical-pairs`, for the actual finite
counts defined above. No cardinality estimate is a hypothesis. -/
theorem count_product_le (m k : ℕ) (hk : 1 ≤ k) :
    (A m k : ℝ) * (B m k : ℝ) ≤ (4 * Real.exp 1 ^ 2) ^ k * (m : ℝ) ^ (2 * k) := by
  rcases le_total m k with hmk | hkm
  · exact count_product_le_of_le hmk
  · exact count_product_le_of_ge hk hkm

/-- The exact composition formula in the manuscript's complementary-binomial form. -/
theorem A_eq_source_sum (m k : ℕ) (hk : 1 ≤ k) :
    A m k = ∑ r ∈ Finset.Icc 1 (min m k),
      m.choose r * (2 * k - r - 1).choose (r - 1) := by
  rw [A_eq_sum_choose m k hk]
  apply Finset.sum_congr rfl
  intro r hr
  have hr1 := (Finset.mem_Icc.mp hr).1
  have hrk := (Finset.mem_Icc.mp hr).2.trans (min_le_right m k)
  have hn : r + (2 * k - 2 * r) - 1 = 2 * k - r - 1 := by omega
  rw [hn]
  congr 1
  exact Nat.choose_symm_of_eq_add (by omega)

end PeriodicAttractiveLogGas.CanonicalPairCounts
