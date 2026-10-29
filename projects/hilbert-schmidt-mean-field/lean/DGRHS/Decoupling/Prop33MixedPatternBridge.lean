import DGRHS.Decoupling.Prop33TailInductionAux

/-!
Mixed-pattern bridge for the Proposition 3.3 tail induction: the label-`j`
copy-pattern statistic of two independent arrays is the `sourceMixedStatistic` for
the slot split induced by `j`, and a mixed pattern is decoupled with cost `H²`
from lower-order uniform tail bounds.
-/

noncomputable section
open MeasureTheory DGRHS.Decoupling.FiniteCube DGRHS.Decoupling.Heterogeneous
open scoped BigOperators ENNReal

namespace DGRHS.Decoupling.Prop33

open DGRHS.Decoupling.Prop33.CopySwap

/-- The slot split induced by a Boolean label pattern. -/
def patSplit {k : ℕ} (j : Fin k → Bool) :
    Fin k ≃ Fin (Fintype.card {s // j s = true}) ⊕
      Fin (Fintype.card {s // ¬ j s = true}) :=
  (Equiv.sumCompl (fun s => j s = true)).symm.trans
    (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _))

lemma patSplit_of_true {k : ℕ} (j : Fin k → Bool) (s : Fin k) (h : j s = true) :
    patSplit j s = Sum.inl (Fintype.equivFin _ ⟨s, h⟩) := by
  unfold patSplit
  rw [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos (p := fun s => j s = true) h]
  rfl

lemma patSplit_of_false {k : ℕ} (j : Fin k → Bool) (s : Fin k) (h : ¬ j s = true) :
    patSplit j s = Sum.inr (Fintype.equivFin _ ⟨s, h⟩) := by
  unfold patSplit
  rw [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg (p := fun s => j s = true) h]
  rfl

section Statistics
variable {S E : Type*} [NormedAddCommGroup E] {n k : ℕ}

/-- The label-`j` statistic of two independent arrays is the source mixed statistic. -/
theorem sourceMixedStatistic_patSplit (K : OrderedTuple n k → (Fin k → S) → E)
    (x y : Fin n → S) (j : Fin k → Bool) :
    sourceMixedStatistic (patSplit j) K x y =
      sourceCopyPatternStatistic K (pairArrays (x, y)) j := by
  unfold sourceMixedStatistic sourceCopyPatternStatistic
  apply Finset.sum_congr rfl
  intro t _
  apply congrArg (K t)
  funext s
  by_cases hjs : j s = true
  · have hs := patSplit_of_true j s hjs
    have hinv : (patSplit j).symm (Sum.inl (Fintype.equivFin _ ⟨s, hjs⟩)) = s := by
      rw [← hs]; exact Equiv.symm_apply_apply _ _
    simp only [sourcePatternValues, hs, Sum.elim_inl, sourceLeftTuple, hinv,
      sourcePatternArgument, pairArrays, hjs]
    simp
  · have hs := patSplit_of_false j s hjs
    have hinv : (patSplit j).symm (Sum.inr (Fintype.equivFin _ ⟨s, hjs⟩)) = s := by
      rw [← hs]; exact Equiv.symm_apply_apply _ _
    simp only [sourcePatternValues, hs, Sum.elim_inr, sourceRightTuple, hinv,
      sourcePatternArgument, pairArrays, hjs]
    simp

theorem copyPattern_allTrue [Fintype (OrderedTuple n k)]
    (K : OrderedTuple n k → (Fin k → S) → E) (x y : Fin n → S) :
    sourceCopyPatternStatistic K (pairArrays (x, y)) (fun _ => true) =
      sourceOrderStatistic K x := by
  unfold sourceCopyPatternStatistic sourceOrderStatistic
  rfl

theorem copyPattern_allFalse [Fintype (OrderedTuple n k)]
    (K : OrderedTuple n k → (Fin k → S) → E) (x y : Fin n → S) :
    sourceCopyPatternStatistic K (pairArrays (x, y)) (fun _ => false) =
      sourceOrderStatistic K y := by
  unfold sourceCopyPatternStatistic sourceOrderStatistic
  rfl

end Statistics

/-- The mixed patterns: all patterns except the two constant ones. -/
def mixedPatterns (k : ℕ) : Finset (Fin k → Bool) :=
  ((Finset.univ : Finset (Fin k → Bool)).erase (fun _ => true)).erase (fun _ => false)

lemma mem_mixedPatterns {k : ℕ} {j : Fin k → Bool} :
    j ∈ mixedPatterns k ↔ j ≠ (fun _ => false) ∧ j ≠ (fun _ => true) := by
  simp [mixedPatterns]

lemma card_mixedPatterns {k : ℕ} (hk : 0 < k) : (mixedPatterns k).card + 2 = 2 ^ k := by
  have hne : (fun _ : Fin k => true) ≠ (fun _ : Fin k => false) := by
    intro h
    have := congrFun h ⟨0, hk⟩
    simp at this
  unfold mixedPatterns
  rw [Finset.card_erase_of_mem (by simp [hne.symm]), Finset.card_erase_of_mem (by simp)]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have : 2 ^ k ≥ 2 := by
    calc 2 ^ k ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk
      _ = 2 := by norm_num
  omega

lemma mixedPatterns_nonempty {k : ℕ} (hk : 2 ≤ k) : (mixedPatterns k).Nonempty := by
  refine ⟨fun q => decide (q = ⟨0, by omega⟩), ?_⟩
  rw [mem_mixedPatterns]
  constructor
  · intro h
    have := congrFun h ⟨0, by omega⟩
    simp at this
  · intro h
    have := congrFun h ⟨1, by omega⟩
    simp [Fin.ext_iff] at this

section AllPattern
variable {S E : Type*} [NormedAddCommGroup E] {n k : ℕ} [Fintype (OrderedTuple n k)]

/-- Decomposition of the all-pattern aggregate into the two constant patterns and the
mixed ones. -/
theorem allPattern_decomp (hk : 0 < k) (K : OrderedTuple n k → (Fin k → S) → E)
    (z : Fin n → S × S) :
    sourceAllPatternStatistic K z =
      sourceCopyPatternStatistic K z (fun _ => true) +
        sourceCopyPatternStatistic K z (fun _ => false) +
        ∑ j ∈ mixedPatterns k, sourceCopyPatternStatistic K z j := by
  have hne : (fun _ : Fin k => true) ≠ (fun _ : Fin k => false) := by
    intro h
    have := congrFun h ⟨0, hk⟩
    simp at this
  unfold sourceAllPatternStatistic mixedPatterns
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (fun _ : Fin k => true)),
    ← Finset.add_sum_erase _ _ (show (fun _ : Fin k => false) ∈
      (Finset.univ : Finset (Fin k → Bool)).erase (fun _ => true) by simp [hne.symm]),
    add_assoc]

/-- Norm bound for the sum of the two constant-pattern statistics. -/
theorem norm_constPatterns_le (hk : 0 < k) (K : OrderedTuple n k → (Fin k → S) → E)
    (z : Fin n → S × S) :
    ‖sourceCopyPatternStatistic K z (fun _ => true) +
        sourceCopyPatternStatistic K z (fun _ => false)‖ ≤
      ‖sourceAllPatternStatistic K z‖ +
        ∑ j ∈ mixedPatterns k, ‖sourceCopyPatternStatistic K z j‖ := by
  have h := allPattern_decomp hk K z
  have h2 : sourceCopyPatternStatistic K z (fun _ => true) +
        sourceCopyPatternStatistic K z (fun _ => false) =
      sourceAllPatternStatistic K z -
        ∑ j ∈ mixedPatterns k, sourceCopyPatternStatistic K z j := by
    rw [h]; abel
  rw [h2]
  calc _ ≤ ‖sourceAllPatternStatistic K z‖ +
        ‖∑ j ∈ mixedPatterns k, sourceCopyPatternStatistic K z j‖ := norm_sub_le _ _
    _ ≤ _ := by gcongr; exact norm_sum_le _ _

end AllPattern


section MixedBound
variable {S E : Type*} [MeasurableSpace S] [MeasurableSpace E] [NormedAddCommGroup E]
  [OpensMeasurableSpace E] [MeasurableAdd₂ E] {n k : ℕ}

lemma patSplit_card (j : Fin k → Bool) :
    Fintype.card {s // j s = true} + Fintype.card {s // ¬ j s = true} = k := by
  have h := Fintype.card_congr (patSplit j)
  simpa [Fintype.card_sum] using h.symm

lemma card_true_pos {j : Fin k → Bool} (hj : j ≠ fun _ => false) :
    0 < Fintype.card {s // j s = true} := by
  have : ∃ s, j s = true := by
    by_contra hcon
    push_neg at hcon
    exact hj (funext fun s => by simpa using hcon s)
  obtain ⟨s, hs⟩ := this
  exact Fintype.card_pos_iff.mpr ⟨⟨s, hs⟩⟩

lemma card_false_pos {j : Fin k → Bool} (hj : j ≠ fun _ => true) :
    0 < Fintype.card {s // ¬ j s = true} := by
  have : ∃ s, ¬ j s = true := by
    by_contra hcon
    push_neg at hcon
    exact hj (funext fun s => hcon s)
  obtain ⟨s, hs⟩ := this
  exact Fintype.card_pos_iff.mpr ⟨⟨s, hs⟩⟩

/-- A mixed copy pattern is decoupled with cost `H²` from lower-order uniform tail bounds
with the common constant `H ≥ 1`, in terms of the full `k`-copy law. -/
theorem mixedPattern_tail_bound (hk : 2 ≤ k) (hn : k ≤ n)
    (marginal : Fin n → Measure S) [∀ i, IsProbabilityMeasure (marginal i)]
    (K : OrderedTuple n k → (Fin k → S) → E) (hK : ∀ t, Measurable (K t))
    (H : ℝ) (hH : 1 ≤ H)
    (hLow : ∀ r, 0 < r → r < k → sourceUniformTailAtOrder (S := S) (E := E) r H)
    (j : Fin k → Bool) (hj : j ∈ mixedPatterns k) (a : ℝ) (ha : 0 < a) :
    ((sourceArrayLaw marginal).prod (sourceArrayLaw marginal))
        {xy | a ≤ ‖sourceCopyPatternStatistic K (pairArrays xy) j‖} ≤
      ENNReal.ofReal (H * H) *
        sourceCopiesLaw (r := k) marginal
          {z | a ≤ H * H * ‖sourceOrderDecoupledStatistic K z‖} := by
  classical
  rw [mem_mixedPatterns] at hj
  have hp := card_true_pos hj.1
  have hq := card_false_pos hj.2
  have hslots := patSplit_card j
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have key := source_mixed_pattern_induction_from_uniform (S := S) (E := E)
    marginal (patSplit j) hslots hp hq hk hn K hK a H H ha hH hH
    (fun h => hLow _ hp h) (fun h => hLow _ hq h)
  have hset1 : {xy : (Fin n → S) × (Fin n → S) |
        a ≤ ‖sourceMixedStatistic (patSplit j) K xy.1 xy.2‖} =
      {xy | a ≤ ‖sourceCopyPatternStatistic K (pairArrays xy) j‖} := by
    ext xy
    simp only [Set.mem_ofPred_eq]
    rw [sourceMixedStatistic_patSplit K xy.1 xy.2 j]
  rw [hset1] at key
  have hVmeas := measurable_sourceOrderDecoupledStatistic K hK
  have hflat := sourceCopyBlockFlattening_measurePreserving marginal (patSplit j)
  have hVset : MeasurableSet {z : Fin k → Fin n → S |
      a / H ≤ H * ‖sourceOrderDecoupledStatistic K z‖} :=
    measurableSet_le measurable_const (hVmeas.norm.const_mul _)
  have hpre := hflat.measure_preimage hVset.nullMeasurableSet
  rw [sourceFullyDecoupled_event_preimage (patSplit j) K (a / H) H] at hpre
  rw [hpre] at key
  have hset2 : {z : Fin k → Fin n → S | a / H ≤ H * ‖sourceOrderDecoupledStatistic K z‖} =
      {z | a ≤ H * H * ‖sourceOrderDecoupledStatistic K z‖} := by
    ext z
    simp only [Set.mem_ofPred_eq]
    rw [div_le_iff₀ hH0]
    constructor <;> intro h <;> linarith
  rw [hset2] at key
  rw [← ENNReal.ofReal_mul hH0.le] at key
  exact key

end MixedBound

end DGRHS.Decoupling.Prop33
