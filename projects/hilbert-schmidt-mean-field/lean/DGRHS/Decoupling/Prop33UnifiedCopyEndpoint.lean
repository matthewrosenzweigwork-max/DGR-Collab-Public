import DGRHS.Decoupling.Prop33MixedPatternConditionalPrefix

/-! Conditional source ordered-kernel p/q induction and independent copy-law endpoint.
Assembly of the preserved 132290 predecessor after the checked generic prefix.
P10 repair: the former line-566 `simpa` failure is fixed by an explicit set equality
(`sourceFully_eq_rightSections`); the module now builds with allowed axioms only.
The explicit MeasurableAdd₂ qualification is retained. The general-k statement is
`DGRHS.Decoupling.Prop33.prop33_banach_tail` in `Prop33GeneralK`. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace DGRHS.Decoupling.Prop33

/-- The ordered tuple in the first block of source slots. The equivalence
`slotSplit` records the source slot order and identifies which original
coordinate belongs to each first-block position. -/
def sourceLeftTuple {n k p q : ℕ} (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (t : OrderedTuple n k) : OrderedTuple n p := by
  refine ⟨fun j => t.1 (slotSplit.symm (.inl j)), ?_⟩
  intro i j hij
  have hs : slotSplit.symm (.inl i) = slotSplit.symm (.inl j) := t.2 hij
  have he : (Sum.inl i : Fin p ⊕ Fin q) = Sum.inl j := by
    calc
      Sum.inl i = slotSplit (slotSplit.symm (.inl i)) := by simp
      _ = slotSplit (slotSplit.symm (.inl j)) := congrArg slotSplit hs
      _ = Sum.inl j := by simp
  exact Sum.inl.inj he

/-- The ordered tuple in the second block of source slots. -/
def sourceRightTuple {n k p q : ℕ} (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (t : OrderedTuple n k) : OrderedTuple n q := by
  refine ⟨fun j => t.1 (slotSplit.symm (.inr j)), ?_⟩
  intro i j hij
  have hs : slotSplit.symm (.inr i) = slotSplit.symm (.inr j) := t.2 hij
  have he : (Sum.inr i : Fin p ⊕ Fin q) = Sum.inr j := by
    calc
      Sum.inr i = slotSplit (slotSplit.symm (.inr i)) := by simp
      _ = slotSplit (slotSplit.symm (.inr j)) := congrArg slotSplit hs
      _ = Sum.inr j := by simp
  exact Sum.inr.inj he

/-- Put the two ordered slot-value blocks back in the original source order. -/
def sourcePatternValues {S : Type*} {k p q : ℕ}
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (u : Fin p → S) (v : Fin q → S) : Fin k → S :=
  fun s => Sum.elim u v (slotSplit s)

/-- Original two-copy mixed-pattern statistic with source tuple order retained. -/
def sourceMixedStatistic {S E : Type*} {n k p q : ℕ}
    [NormedAddCommGroup E] [Fintype (OrderedTuple n k)]
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (f : OrderedTuple n k → (Fin k → S) → E)
    (x y : Fin n → S) : E :=
  ∑ t : OrderedTuple n k,
    f t (sourcePatternValues slotSplit
      (fun j => x ((sourceLeftTuple slotSplit t).1 j))
      (fun j => y ((sourceRightTuple slotSplit t).1 j)))

/-- First-block section kernel. For a fixed retained second array y and fixed
ordered first-block tuple a, sum over exactly those original ordered k-tuples
whose first-block restriction is a. All cross-block distinctness remains
encoded by the original tuple subtype. -/
def sourceLeftSectionKernel {S E : Type*} {n k p q : ℕ}
    [NormedAddCommGroup E] [Fintype (OrderedTuple n k)] [Fintype (OrderedTuple n p)]
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (f : OrderedTuple n k → (Fin k → S) → E)
    (y : Fin n → S) (a : OrderedTuple n p) (u : Fin p → S) : E :=
  ∑ t : OrderedTuple n k,
    if sourceLeftTuple slotSplit t = a then
      f t (sourcePatternValues slotSplit u
        (fun j => y ((sourceRightTuple slotSplit t).1 j)))
    else 0

/-- Second-block section kernel after the first block has already been copied
independently. -/
def sourceRightSectionKernel {S E : Type*} {n k p q : ℕ}
    [NormedAddCommGroup E] [Fintype (OrderedTuple n k)] [Fintype (OrderedTuple n q)]
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (f : OrderedTuple n k → (Fin k → S) → E)
    (z : Fin p → Fin n → S) (b : OrderedTuple n q) (v : Fin q → S) : E :=
  ∑ t : OrderedTuple n k,
    if sourceRightTuple slotSplit t = b then
      f t (sourcePatternValues slotSplit
        (fun j => z j ((sourceLeftTuple slotSplit t).1 j)) v)
    else 0

/-- Statistic after decoupling the first repeated-copy block. It is the
order-p decoupled statistic of `sourceLeftSectionKernel`. -/
def sourceAfterLeftDecoupling {S E : Type*} {n k p q : ℕ}
    [NormedAddCommGroup E] [Fintype (OrderedTuple n p)] [Fintype (OrderedTuple n k)]
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (f : OrderedTuple n k → (Fin k → S) → E)
    (z : Fin p → Fin n → S) (y : Fin n → S) : E :=
  ∑ a : OrderedTuple n p,
    sourceLeftSectionKernel slotSplit f y a (fun j => z j (a.1 j))

/-- Fully decoupled ordered statistic: one independent array per source slot
block position. -/
def sourceFullyDecoupledStatistic {S E : Type*} {n k p q : ℕ}
    [NormedAddCommGroup E] [Fintype (OrderedTuple n k)]
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (f : OrderedTuple n k → (Fin k → S) → E)
    (z : Fin p → Fin n → S) (w : Fin q → Fin n → S) : E :=
  ∑ t : OrderedTuple n k,
    f t (sourcePatternValues slotSplit
      (fun j => z j ((sourceLeftTuple slotSplit t).1 j))
      (fun j => w j ((sourceRightTuple slotSplit t).1 j)))

/-- The original mixed statistic written as the diagonal statistic of the
first-block section-kernel family. This is the exact form to which the
order-p induction hypothesis applies. -/
def sourceLeftCoupledStatistic {S E : Type*} {n k p q : ℕ}
    [NormedAddCommGroup E] [Fintype (OrderedTuple n p)] [Fintype (OrderedTuple n k)]
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (f : OrderedTuple n k → (Fin k → S) → E)
    (x y : Fin n → S) : E :=
  ∑ a : OrderedTuple n p,
    sourceLeftSectionKernel slotSplit f y a (fun j => x (a.1 j))

/-- The partially decoupled statistic written as the diagonal statistic of the
second-block section-kernel family. This is the exact order-q induction input. -/
def sourceRightCoupledStatistic {S E : Type*} {n k p q : ℕ}
    [NormedAddCommGroup E] [Fintype (OrderedTuple n q)] [Fintype (OrderedTuple n k)]
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (f : OrderedTuple n k → (Fin k → S) → E)
    (z : Fin p → Fin n → S) (y : Fin n → S) : E :=
  ∑ b : OrderedTuple n q,
    sourceRightSectionKernel slotSplit f z b (fun j => y (b.1 j))

/-- Restrict a source family to its A-slot tuple indices. -/
def sourceLeftRestrictedFamily {S E : Type*} {n k p q : ℕ}
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (f : OrderedTuple n k → (Fin k → S) → E) :
    OrderedTuple n k → (Fin n → S) → (Fin n → S) → E :=
  fun t x y => f t (sourcePatternValues slotSplit
    (fun j => x ((sourceLeftTuple slotSplit t).1 j))
    (fun j => y ((sourceRightTuple slotSplit t).1 j)))

/-- Exact finite-fiber reindexing from the original ordered statistic to the
first section family. This is the only regrouping step; it neither symmetrizes
nor identifies tuple permutations. -/
theorem sourceMixed_eq_leftSections {S E : Type*} {n k p q : ℕ}
    [NormedAddCommGroup E] [Fintype (OrderedTuple n p)] [Fintype (OrderedTuple n k)]
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (f : OrderedTuple n k → (Fin k → S) → E)
    (x y : Fin n → S) :
    sourceMixedStatistic slotSplit f x y =
      sourceLeftCoupledStatistic slotSplit f x y := by
  classical
  let G := sourceLeftRestrictedFamily slotSplit f
  have hsec : ∀ a : OrderedTuple n p,
      sourceLeftSectionKernel slotSplit f y a (fun j => x (a.1 j)) =
        leftSectionKernel (fun t => sourceLeftTuple slotSplit t) G y a x := by
    intro a
    unfold sourceLeftSectionKernel leftSectionKernel G sourceLeftRestrictedFamily
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases h : sourceLeftTuple slotSplit t = a
    · have hval : a.1 = (sourceLeftTuple slotSplit t).1 :=
        congrArg Subtype.val h.symm
      simp [h, hval, sourcePatternValues]
    · simp [h]
  have hgroup := sum_leftSectionKernel
    (left := fun t => sourceLeftTuple slotSplit t) (F := G) x y
  calc
    sourceMixedStatistic slotSplit f x y =
        ∑ t : OrderedTuple n k, G t x y := by
          rfl
    _ = ∑ a : OrderedTuple n p,
          leftSectionKernel (fun t => sourceLeftTuple slotSplit t) G y a x :=
          hgroup.symm
    _ = sourceLeftCoupledStatistic slotSplit f x y := by
          unfold sourceLeftCoupledStatistic
          apply Finset.sum_congr rfl
          intro a ha
          exact (hsec a).symm

/-- After the first slot block has been copied, the same source statistic is
exactly the order-q diagonal statistic of the second section family. -/
theorem sourceAfterLeft_eq_rightSections {S E : Type*} {n k p q : ℕ}
    [NormedAddCommGroup E] [Fintype (OrderedTuple n p)]
    [Fintype (OrderedTuple n q)] [Fintype (OrderedTuple n k)]
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (f : OrderedTuple n k → (Fin k → S) → E)
    (z : Fin p → Fin n → S) (y : Fin n → S) :
    sourceAfterLeftDecoupling slotSplit f z y =
      sourceRightCoupledStatistic slotSplit f z y := by
  classical
  let G : OrderedTuple n k → (Fin p → Fin n → S) → (Fin n → S) → E :=
    fun t z' y' => f t (sourcePatternValues slotSplit
      (fun j => z' j ((sourceLeftTuple slotSplit t).1 j))
      (fun j => y' ((sourceRightTuple slotSplit t).1 j)))
  have hleftSection : ∀ a : OrderedTuple n p,
      sourceLeftSectionKernel slotSplit f y a (fun j => z j (a.1 j)) =
        leftSectionKernel (fun t => sourceLeftTuple slotSplit t) G y a z := by
    intro a
    unfold sourceLeftSectionKernel leftSectionKernel
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases h : sourceLeftTuple slotSplit t = a
    · have hval : a.1 = (sourceLeftTuple slotSplit t).1 :=
        congrArg Subtype.val h.symm
      simp [h, hval, G, sourcePatternValues]
    · simp [h]
  have hrightSection : ∀ b : OrderedTuple n q,
      sourceRightSectionKernel slotSplit f z b (fun j => y (b.1 j)) =
        rightSectionKernel (fun t => sourceRightTuple slotSplit t) G z b y := by
    intro b
    unfold sourceRightSectionKernel rightSectionKernel
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases h : sourceRightTuple slotSplit t = b
    · have hval : b.1 = (sourceRightTuple slotSplit t).1 :=
        congrArg Subtype.val h.symm
      simp [h, hval, G, sourcePatternValues]
    · simp [h]
  have hleftGroup := sum_leftSectionKernel
    (left := fun t => sourceLeftTuple slotSplit t) (F := G) z y
  have hrightGroup := sum_rightSectionKernel
    (right := fun t => sourceRightTuple slotSplit t) (F := G) z y
  calc
    sourceAfterLeftDecoupling slotSplit f z y =
        ∑ a : OrderedTuple n p,
          leftSectionKernel (fun t => sourceLeftTuple slotSplit t) G y a z := by
      unfold sourceAfterLeftDecoupling
      apply Finset.sum_congr rfl
      intro a ha
      exact hleftSection a
    _ = ∑ t : OrderedTuple n k, G t z y := hleftGroup
    _ = ∑ b : OrderedTuple n q,
          rightSectionKernel (fun t => sourceRightTuple slotSplit t) G z b y :=
      hrightGroup.symm
    _ = sourceRightCoupledStatistic slotSplit f z y := by
      unfold sourceRightCoupledStatistic
      apply Finset.sum_congr rfl
      intro b hb
      exact (hrightSection b).symm


def sourceArrayLaw {S : Type*} {n : ℕ} [MeasurableSpace S]
    (marginal : Fin n → Measure S) : Measure (Fin n → S) :=
  Measure.pi marginal

def sourceCopiesLaw {S : Type*} {n r : ℕ} [MeasurableSpace S]
    (marginal : Fin n → Measure S) : Measure (Fin r → Fin n → S) :=
  Measure.pi (fun _ : Fin r => sourceArrayLaw marginal)

def sourceOrderStatistic {S E : Type*} {n r : ℕ}
    [NormedAddCommGroup E] [Fintype (OrderedTuple n r)] (K : OrderedTuple n r → (Fin r → S) → E)
    (x : Fin n → S) : E :=
  ∑ a : OrderedTuple n r, K a (fun j => x (a.1 j))

def sourceOrderDecoupledStatistic {S E : Type*} {n r : ℕ}
    [NormedAddCommGroup E] [Fintype (OrderedTuple n r)] (K : OrderedTuple n r → (Fin r → S) → E)
    (z : Fin r → Fin n → S) : E :=
  ∑ a : OrderedTuple n r, K a (fun j => z j (a.1 j))

def sourceUniformTailAtOrder {S E : Type*}
    [MeasurableSpace S] [MeasurableSpace E] [NormedAddCommGroup E]
    [OpensMeasurableSpace E] [MeasurableAdd₂ E]
    (r : ℕ) (C : ℝ) : Prop :=
  ∀ {n : ℕ} (marginal : Fin n → Measure S)
    [∀ i, IsProbabilityMeasure (marginal i)]
    (hrn : r ≤ n) [Fintype (OrderedTuple n r)],
    ∀ (K : OrderedTuple n r → (Fin r → S) → E),
      (∀ a, Measurable (K a)) → ∀ t, 0 < t →
        (sourceArrayLaw marginal) {x | t ≤ ‖sourceOrderStatistic K x‖} ≤
          ENNReal.ofReal C *
            (sourceCopiesLaw marginal) {z | t ≤ C * ‖sourceOrderDecoupledStatistic K z‖}

lemma measurable_sourceMixedArgument {S : Type*} {n k p q : ℕ}
    [MeasurableSpace S] (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (t : OrderedTuple n k) :
    Measurable (fun xy : (Fin n → S) × (Fin n → S) =>
      sourcePatternValues slotSplit
        (fun j => xy.1 ((sourceLeftTuple slotSplit t).1 j))
        (fun j => xy.2 ((sourceRightTuple slotSplit t).1 j))) := by
  refine measurable_pi_iff.mpr ?_
  intro s
  rcases hs : slotSplit s with j | j
  · simpa [Function.comp_def, sourcePatternValues, hs] using
      (measurable_pi_apply ((sourceLeftTuple slotSplit t).1 j)).comp measurable_fst
  · simpa [Function.comp_def, sourcePatternValues, hs] using
      (measurable_pi_apply ((sourceRightTuple slotSplit t).1 j)).comp measurable_snd

lemma measurable_sourceAfterLeftArgument {S : Type*} {n k p q : ℕ}
    [MeasurableSpace S] (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (t : OrderedTuple n k) :
    Measurable (fun zy : (Fin p → Fin n → S) × (Fin n → S) =>
      sourcePatternValues slotSplit
        (fun j => zy.1 j ((sourceLeftTuple slotSplit t).1 j))
        (fun j => zy.2 ((sourceRightTuple slotSplit t).1 j))) := by
  refine measurable_pi_iff.mpr ?_
  intro s
  rcases hs : slotSplit s with j | j
  · simpa [Function.comp_def, sourcePatternValues, hs] using
      (measurable_pi_apply ((sourceLeftTuple slotSplit t).1 j)).comp
        ((measurable_pi_apply j).comp measurable_fst)
  · simpa [Function.comp_def, sourcePatternValues, hs] using
      (measurable_pi_apply ((sourceRightTuple slotSplit t).1 j)).comp measurable_snd

lemma measurable_sourceFullyArgument {S : Type*} {n k p q : ℕ}
    [MeasurableSpace S] (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (t : OrderedTuple n k) :
    Measurable (fun zw : (Fin p → Fin n → S) × (Fin q → Fin n → S) =>
      sourcePatternValues slotSplit
        (fun j => zw.1 j ((sourceLeftTuple slotSplit t).1 j))
        (fun j => zw.2 j ((sourceRightTuple slotSplit t).1 j))) := by
  refine measurable_pi_iff.mpr ?_
  intro s
  rcases hs : slotSplit s with j | j
  · simpa [Function.comp_def, sourcePatternValues, hs] using
      (measurable_pi_apply ((sourceLeftTuple slotSplit t).1 j)).comp
        ((measurable_pi_apply j).comp measurable_fst)
  · simpa [Function.comp_def, sourcePatternValues, hs] using
      (measurable_pi_apply ((sourceRightTuple slotSplit t).1 j)).comp
        ((measurable_pi_apply j).comp measurable_snd)

lemma measurable_sourceMixedStatistic {S E : Type*} {n k p q : ℕ}
    [MeasurableSpace S] [MeasurableSpace E] [NormedAddCommGroup E]
    [MeasurableAdd₂ E] [Fintype (OrderedTuple n k)]
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (f : OrderedTuple n k → (Fin k → S) → E)
    (hf : ∀ t, Measurable (f t)) :
    Measurable (fun xy : (Fin n → S) × (Fin n → S) =>
      sourceMixedStatistic slotSplit f xy.1 xy.2) := by
  classical
  unfold sourceMixedStatistic
  apply Finset.measurable_sum
  intro t ht
  exact (hf t).comp (measurable_sourceMixedArgument slotSplit t)

lemma measurable_sourceFullyDecoupledStatistic {S E : Type*} {n k p q : ℕ}
    [MeasurableSpace S] [MeasurableSpace E] [NormedAddCommGroup E]
    [MeasurableAdd₂ E] [Fintype (OrderedTuple n k)]
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (f : OrderedTuple n k → (Fin k → S) → E)
    (hf : ∀ t, Measurable (f t)) :
    Measurable (fun zw : (Fin p → Fin n → S) × (Fin q → Fin n → S) =>
      sourceFullyDecoupledStatistic slotSplit f zw.1 zw.2) := by
  classical
  unfold sourceFullyDecoupledStatistic
  apply Finset.measurable_sum
  intro t ht
  exact (hf t).comp (measurable_sourceFullyArgument slotSplit t)

lemma measurable_sourceLeftSectionKernel {S E : Type*} {n k p q : ℕ}
    [MeasurableSpace S] [MeasurableSpace E] [NormedAddCommGroup E]
    [MeasurableAdd₂ E] [Fintype (OrderedTuple n k)]
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (f : OrderedTuple n k → (Fin k → S) → E)
    (hf : ∀ t, Measurable (f t)) (y : Fin n → S) (a : OrderedTuple n p) :
    Measurable (fun u : Fin p → S => sourceLeftSectionKernel slotSplit f y a u) := by
  classical
  unfold sourceLeftSectionKernel
  apply Finset.measurable_sum
  intro t ht
  by_cases h : sourceLeftTuple slotSplit t = a
  · simp [h]
    apply (hf t).comp
    refine measurable_pi_iff.mpr ?_
    intro s
    rcases hs : slotSplit s with j | j
    · simpa [sourcePatternValues, hs] using (measurable_pi_apply j)
    · simpa [sourcePatternValues, hs] using
        (measurable_const : Measurable (fun _ : Fin p → S => y ((sourceRightTuple slotSplit t).1 j)))
  · simp [h]

lemma measurable_sourceRightSectionKernel {S E : Type*} {n k p q : ℕ}
    [MeasurableSpace S] [MeasurableSpace E] [NormedAddCommGroup E]
    [MeasurableAdd₂ E] [Fintype (OrderedTuple n k)]
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (f : OrderedTuple n k → (Fin k → S) → E)
    (hf : ∀ t, Measurable (f t)) (z : Fin p → Fin n → S)
    (b : OrderedTuple n q) :
    Measurable (fun v : Fin q → S => sourceRightSectionKernel slotSplit f z b v) := by
  classical
  unfold sourceRightSectionKernel
  apply Finset.measurable_sum
  intro t ht
  by_cases h : sourceRightTuple slotSplit t = b
  · simp [h]
    apply (hf t).comp
    refine measurable_pi_iff.mpr ?_
    intro s
    rcases hs : slotSplit s with j | j
    · simpa [sourcePatternValues, hs] using
        (measurable_const : Measurable (fun _ : Fin q → S => z j ((sourceLeftTuple slotSplit t).1 j)))
    · simpa [sourcePatternValues, hs] using (measurable_pi_apply j)
  · simp [h]

lemma measurable_sourceAfterLeftDecoupling {S E : Type*} {n k p q : ℕ}
    [MeasurableSpace S] [MeasurableSpace E] [NormedAddCommGroup E]
    [MeasurableAdd₂ E] [Fintype (OrderedTuple n p)]
    [Fintype (OrderedTuple n q)] [Fintype (OrderedTuple n k)]
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (f : OrderedTuple n k → (Fin k → S) → E)
    (hf : ∀ t, Measurable (f t)) :
    Measurable (fun zy : (Fin p → Fin n → S) × (Fin n → S) =>
      sourceAfterLeftDecoupling slotSplit f zy.1 zy.2) := by
  classical
  have hright : Measurable (fun zy : (Fin p → Fin n → S) × (Fin n → S) =>
      sourceRightCoupledStatistic slotSplit f zy.1 zy.2) := by
    unfold sourceRightCoupledStatistic sourceRightSectionKernel
    apply Finset.measurable_sum
    intro b hb
    apply Finset.measurable_sum
    intro t ht
    by_cases h : sourceRightTuple slotSplit t = b
    · have hval : b.1 = (sourceRightTuple slotSplit t).1 :=
        congrArg Subtype.val h.symm
      simp [h, hval]
      exact (hf t).comp (measurable_sourceAfterLeftArgument slotSplit t)
    · simp [h]
  have hEq : (fun zy : (Fin p → Fin n → S) × (Fin n → S) =>
      sourceAfterLeftDecoupling slotSplit f zy.1 zy.2) =
      (fun zy => sourceRightCoupledStatistic slotSplit f zy.1 zy.2) := by
    funext zy
    exact sourceAfterLeft_eq_rightSections slotSplit f zy.1 zy.2
  rw [hEq]
  exact hright

/-- Exact second-block fiber decomposition of the fully copied statistic. -/
theorem sourceFully_eq_rightSections {S E : Type*} {n k p q : ℕ}
    [NormedAddCommGroup E] [Fintype (OrderedTuple n q)] [Fintype (OrderedTuple n k)]
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (f : OrderedTuple n k → (Fin k → S) → E)
    (z : Fin p → Fin n → S) (w : Fin q → Fin n → S) :
    sourceFullyDecoupledStatistic slotSplit f z w =
      ∑ b : OrderedTuple n q,
        sourceRightSectionKernel slotSplit f z b (fun j => w j (b.1 j)) := by
  classical
  let G : OrderedTuple n k → (Fin p → Fin n → S) → (Fin q → Fin n → S) → E :=
    fun t z' w' => f t (sourcePatternValues slotSplit
      (fun j => z' j ((sourceLeftTuple slotSplit t).1 j))
      (fun j => w' j ((sourceRightTuple slotSplit t).1 j)))
  have hsec : ∀ b : OrderedTuple n q,
      sourceRightSectionKernel slotSplit f z b (fun j => w j (b.1 j)) =
        rightSectionKernel (fun t => sourceRightTuple slotSplit t) G z b w := by
    intro b
    unfold sourceRightSectionKernel rightSectionKernel
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases h : sourceRightTuple slotSplit t = b
    · have hval : b.1 = (sourceRightTuple slotSplit t).1 :=
        congrArg Subtype.val h.symm
      simp [h, hval, G, sourcePatternValues]
    · simp [h]
  have hgroup := sum_rightSectionKernel
    (right := fun t => sourceRightTuple slotSplit t) (F := G) z w
  calc
    sourceFullyDecoupledStatistic slotSplit f z w =
        ∑ t : OrderedTuple n k, G t z w := by rfl
    _ = ∑ b : OrderedTuple n q,
          rightSectionKernel (fun t => sourceRightTuple slotSplit t) G z b w :=
      hgroup.symm
    _ = ∑ b : OrderedTuple n q,
          sourceRightSectionKernel slotSplit f z b (fun j => w j (b.1 j)) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact (hsec b).symm

/-- The mixed-pattern conditional step, with product-copy measure types and
lower-order tails instantiated from uniform order-p and order-q hypotheses. -/
theorem source_mixed_pattern_induction_from_uniform
    {S E : Type*} {n k p q : ℕ}
    [MeasurableSpace S] [MeasurableSpace E] [NormedAddCommGroup E]
    [OpensMeasurableSpace E] [MeasurableAdd₂ E]
    [Fintype (OrderedTuple n k)] [Fintype (OrderedTuple n p)]
    [Fintype (OrderedTuple n q)]
    (marginal : Fin n → Measure S) [∀ i, IsProbabilityMeasure (marginal i)]
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (hslots : p + q = k) (hp : 0 < p) (hq : 0 < q)
    (hk : 2 ≤ k) (hn : k ≤ n)
    (f : OrderedTuple n k → (Fin k → S) → E)
    (hf : ∀ t, Measurable (f t))
    (t Cp Cq : ℝ) (ht : 0 < t)
    (hCp : 1 ≤ Cp) (hCq : 1 ≤ Cq)
    (hLowerp : p < k → sourceUniformTailAtOrder (S := S) (E := E) p Cp)
    (hLowerq : q < k → sourceUniformTailAtOrder (S := S) (E := E) q Cq) :
    (sourceArrayLaw marginal).prod (sourceArrayLaw marginal)
      {xy | t ≤ ‖sourceMixedStatistic slotSplit f xy.1 xy.2‖} ≤
      (ENNReal.ofReal Cp * ENNReal.ofReal Cq) *
        (sourceCopiesLaw (r := p) marginal).prod
          (sourceCopiesLaw (r := q) marginal)
          {zw | t / Cp ≤ Cq *
            ‖sourceFullyDecoupledStatistic slotSplit f zw.1 zw.2‖} := by
  classical
  let μ := sourceArrayLaw marginal
  let ρ := sourceCopiesLaw (r := p) marginal
  let σ := sourceCopiesLaw (r := q) marginal
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, sourceArrayLaw]
    infer_instance
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ, sourceCopiesLaw, sourceArrayLaw]
    infer_instance
  letI : IsProbabilityMeasure σ := by
    dsimp [σ, sourceCopiesLaw, sourceArrayLaw]
    infer_instance
  have hCpPos : 0 < Cp := lt_of_lt_of_le zero_lt_one hCp
  have hCqPos : 0 < Cq := lt_of_lt_of_le zero_lt_one hCq
  have hpk : p < k := by omega
  have hqk : q < k := by omega
  have hTailp : sourceUniformTailAtOrder (S := S) (E := E) p Cp :=
    hLowerp hpk
  have hTailq : sourceUniformTailAtOrder (S := S) (E := E) q Cq :=
    hLowerq hqk
  have hOriginal := measurable_sourceMixedStatistic slotSplit f hf
  have hAfterLeft := measurable_sourceAfterLeftDecoupling slotSplit f hf
  have hFully := measurable_sourceFullyDecoupledStatistic slotSplit f hf
  have hIHp : ∀ y,
      μ {x | t ≤ ‖sourceLeftCoupledStatistic slotSplit f x y‖} ≤
        ENNReal.ofReal Cp * ρ {z | t ≤ Cp *
          ‖sourceRightCoupledStatistic slotSplit f z y‖} := by
    intro y
    have hK : ∀ a, Measurable (sourceLeftSectionKernel slotSplit f y a) :=
      fun a => measurable_sourceLeftSectionKernel slotSplit f hf y a
    have hTailAtN := hTailp (n := n) marginal (by omega : p ≤ n)
    have h := hTailAtN
      (fun a u => sourceLeftSectionKernel slotSplit f y a u) hK t ht
    have hbase : μ {x | t ≤ ‖sourceLeftCoupledStatistic slotSplit f x y‖} ≤
        ENNReal.ofReal Cp * ρ {z | t ≤ Cp *
          ‖sourceAfterLeftDecoupling slotSplit f z y‖} := by
      simpa only [μ, ρ, sourceArrayLaw, sourceCopiesLaw,
        sourceOrderStatistic, sourceOrderDecoupledStatistic,
        sourceLeftCoupledStatistic, sourceAfterLeftDecoupling] using h
    have hset : {z | t ≤ Cp * ‖sourceAfterLeftDecoupling slotSplit f z y‖} =
        {z | t ≤ Cp * ‖sourceRightCoupledStatistic slotSplit f z y‖} := by
      ext z
      change (t ≤ Cp * ‖sourceAfterLeftDecoupling slotSplit f z y‖) ↔
        (t ≤ Cp * ‖sourceRightCoupledStatistic slotSplit f z y‖)
      rw [sourceAfterLeft_eq_rightSections slotSplit f z y]
    calc
      μ {x | t ≤ ‖sourceLeftCoupledStatistic slotSplit f x y‖} ≤
          ENNReal.ofReal Cp * ρ
            {z | t ≤ Cp * ‖sourceAfterLeftDecoupling slotSplit f z y‖} := hbase
      _ = ENNReal.ofReal Cp * ρ
            {z | t ≤ Cp * ‖sourceRightCoupledStatistic slotSplit f z y‖} := by
        rw [hset]
  have hIHq : ∀ z,
      μ {y | t ≤ Cp * ‖sourceRightCoupledStatistic slotSplit f z y‖} ≤
        ENNReal.ofReal Cq * σ {w | t / Cp ≤ Cq *
          ‖sourceFullyDecoupledStatistic slotSplit f z w‖} := by
    intro z
    have hK : ∀ b, Measurable (sourceRightSectionKernel slotSplit f z b) :=
      fun b => measurable_sourceRightSectionKernel slotSplit f hf z b
    have hTailAtN := hTailq (n := n) marginal (by omega : q ≤ n)
    have h := hTailAtN
      (fun b v => sourceRightSectionKernel slotSplit f z b v) hK
      (t / Cp) (div_pos ht hCpPos)
    have hdec : sourceOrderDecoupledStatistic
        (fun b v => sourceRightSectionKernel slotSplit f z b v)
        = fun w => sourceFullyDecoupledStatistic slotSplit f z w := by
      funext w
      change (∑ b : OrderedTuple n q,
        sourceRightSectionKernel slotSplit f z b (fun j => w j (b.1 j))) =
          sourceFullyDecoupledStatistic slotSplit f z w
      exact (sourceFully_eq_rightSections slotSplit f z w).symm
    have hbase : μ {y | t / Cp ≤ ‖sourceRightCoupledStatistic slotSplit f z y‖} ≤
        ENNReal.ofReal Cq * σ {w | t / Cp ≤ Cq *
          ‖sourceFullyDecoupledStatistic slotSplit f z w‖} := by
      have hset : {w | t / Cp ≤ Cq *
            ‖sourceFullyDecoupledStatistic slotSplit f z w‖} =
          {w | t / Cp ≤ Cq * ‖sourceOrderDecoupledStatistic
            (fun b v => sourceRightSectionKernel slotSplit f z b v) w‖} := by
        ext w
        simp only [Set.mem_setOf_eq]
        rw [congrFun hdec w]
      rw [hset]
      exact h
    have hthreshold (y : Fin n → S) :
        (t / Cp ≤ ‖sourceRightCoupledStatistic slotSplit f z y‖) ↔
          (t ≤ Cp * ‖sourceRightCoupledStatistic slotSplit f z y‖) := by
      rw [div_le_iff₀ hCpPos]
      rw [mul_comm]
    have hset : {y | t / Cp ≤ ‖sourceRightCoupledStatistic slotSplit f z y‖} =
        {y | t ≤ Cp * ‖sourceRightCoupledStatistic slotSplit f z y‖} := by
      ext y
      exact hthreshold y
    rw [← hset]
    exact hbase
  have hU : Measurable (fun xy : (Fin n → S) × (Fin n → S) =>
      sourceLeftCoupledStatistic slotSplit f xy.1 xy.2) := by
    have hEq : (fun xy : (Fin n → S) × (Fin n → S) =>
        sourceMixedStatistic slotSplit f xy.1 xy.2) =
        (fun xy => sourceLeftCoupledStatistic slotSplit f xy.1 xy.2) := by
      funext xy
      exact sourceMixed_eq_leftSections slotSplit f xy.1 xy.2
    rw [← hEq]
    exact hOriginal
  have hH : Measurable (fun zy :
      (Fin p → Fin n → S) × (Fin n → S) =>
        sourceRightCoupledStatistic slotSplit f zy.1 zy.2) := by
    have hEq : (fun zy : (Fin p → Fin n → S) × (Fin n → S) =>
        sourceAfterLeftDecoupling slotSplit f zy.1 zy.2) =
        (fun zy => sourceRightCoupledStatistic slotSplit f zy.1 zy.2) := by
      funext zy
      exact sourceAfterLeft_eq_rightSections slotSplit f zy.1 zy.2
    rw [← hEq]
    exact hAfterLeft
  have hbound := mixedPattern_conditional_induction
    (U := fun xy => sourceLeftCoupledStatistic slotSplit f xy.1 xy.2)
    (H := fun zy => sourceRightCoupledStatistic slotSplit f zy.1 zy.2)
    (V := fun zw => sourceFullyDecoupledStatistic slotSplit f zw.1 zw.2)
    (μ := μ) (ν := μ) (ρ := ρ) (σ := σ)
    hU hH hFully t Cp Cq hCpPos hCqPos hIHp hIHq
  have hsourceSet :
      {xy : (Fin n → S) × (Fin n → S) |
        t ≤ ‖sourceMixedStatistic slotSplit f xy.1 xy.2‖} =
      {xy | t ≤ ‖sourceLeftCoupledStatistic slotSplit f xy.1 xy.2‖} := by
    ext xy
    change (t ≤ ‖sourceMixedStatistic slotSplit f xy.1 xy.2‖) ↔
      (t ≤ ‖sourceLeftCoupledStatistic slotSplit f xy.1 xy.2‖)
    rw [sourceMixed_eq_leftSections slotSplit f xy.1 xy.2]
  rw [hsourceSet]
  simpa only [μ, ρ, σ, sourceArrayLaw, sourceCopiesLaw] using hbound

/-- Canonical order-preserving split of the first p+q natural-number slots. -/
def finSumEquiv (p q : ℕ) : Fin (p+q) ≃ Fin p ⊕ Fin q where
  toFun i := if h : i.val < p then
    Sum.inl ⟨i.val,h⟩
  else
    Sum.inr ⟨i.val-p, by have hi := i.isLt; omega⟩
  invFun
    | Sum.inl j => ⟨j.val, by omega⟩
    | Sum.inr j => ⟨p+j.val, by omega⟩
  left_inv i := by
    apply Fin.ext
    by_cases h : i.val < p
    · simp [h]
    · simp [h]
      omega
  right_inv s := by
    cases s with
    | inl j =>
        simp [j.isLt]
    | inr j =>
        have hnot : ¬ p + j.val < p := by omega
        simp [hnot]

/-- Reindex the p- and q-block arrays into the full source copy family. The
slotSplit is the same bijection that assigns each source slot to its copy label.
-/
def sourceCopyBlockFlatteningEquiv {S : Type*} {n k p q : ℕ}
    [MeasurableSpace S] (slotSplit : Fin k ≃ Fin p ⊕ Fin q) :
    ((Fin p → Fin n → S) × (Fin q → Fin n → S)) ≃ (Fin k → Fin n → S) :=
  (Equiv.sumPiEquivProdPi
    (fun _ : Fin p ⊕ Fin q => Fin n → S)).symm.trans
    ((Equiv.piCongrLeft
      (fun _ : Fin p ⊕ Fin q => Fin n → S) slotSplit).symm)

/-- Flattening the product of p- and q-copy laws preserves the full k-copy law.
The marginal may be heterogeneous across the n sample coordinates. -/
theorem sourceCopyBlockFlattening_measurePreserving
    {S : Type*} {n k p q : ℕ} [MeasurableSpace S]
    (marginal : Fin n → Measure S)
    [∀ i, IsProbabilityMeasure (marginal i)]
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q) :
    MeasurePreserving (sourceCopyBlockFlatteningEquiv slotSplit)
      ((sourceCopiesLaw (r := p) marginal).prod
        (sourceCopiesLaw (r := q) marginal))
      (sourceCopiesLaw (r := k) marginal) := by
  let ν : Measure (Fin n → S) := sourceArrayLaw marginal
  letI : IsProbabilityMeasure ν := by
    dsimp [ν, sourceArrayLaw]
    infer_instance
  have hsum : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Fin p ⊕ Fin q => Fin n → S)).symm
      ((Measure.pi fun _ : Fin p => ν).prod
        (Measure.pi fun _ : Fin q => ν))
      (Measure.pi fun _ : Fin p ⊕ Fin q => ν) :=
    measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin p ⊕ Fin q => ν)
  have hindex : MeasurePreserving
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin p ⊕ Fin q => Fin n → S) slotSplit).symm
      (Measure.pi fun _ : Fin p ⊕ Fin q => ν)
      (Measure.pi fun _ : Fin k => ν) :=
    (measurePreserving_piCongrLeft
      (α := fun _ : Fin p ⊕ Fin q => Fin n → S)
      (μ := fun _ : Fin p ⊕ Fin q => ν) slotSplit).symm
  change MeasurePreserving
    ((MeasurableEquiv.piCongrLeft
        (fun _ : Fin p ⊕ Fin q => Fin n → S) slotSplit).symm ∘
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Fin p ⊕ Fin q => Fin n → S)).symm)
    ((Measure.pi fun _ : Fin p => ν).prod
      (Measure.pi fun _ : Fin q => ν))
    (Measure.pi fun _ : Fin k => ν)
  exact hindex.comp hsum

/-- The canonical slot bijection used when the source slots are numbered
consecutively as Fin (p+q). -/
def sourceCanonicalSlotSplit (p q : ℕ) : Fin (p+q) ≃ Fin p ⊕ Fin q :=
  finSumEquiv p q

/-- Canonical p+q-copy law flattening, stated with the exact source slot type. -/
theorem sourceCanonicalCopyBlockFlattening_measurePreserving
    {S : Type*} {n p q : ℕ} [MeasurableSpace S]
    (marginal : Fin n → Measure S)
    [∀ i, IsProbabilityMeasure (marginal i)] :
    MeasurePreserving
      (sourceCopyBlockFlatteningEquiv (sourceCanonicalSlotSplit p q))
      ((sourceCopiesLaw (r := p) marginal).prod
        (sourceCopiesLaw (r := q) marginal))
      (sourceCopiesLaw (r := p+q) marginal) :=
  sourceCopyBlockFlattening_measurePreserving marginal (sourceCanonicalSlotSplit p q)


/-- Pointwise action of the already reviewed block-to-full-array equivalence.
The copy at source slot `s` is selected by the same `slotSplit s` used by the
mixed-pattern statistic. -/
lemma sourceCopyBlockFlatteningEquiv_apply
    {S : Type*} {n k p q : ℕ} [MeasurableSpace S]
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (zw : (Fin p → Fin n → S) × (Fin q → Fin n → S)) (s : Fin k) :
    sourceCopyBlockFlatteningEquiv slotSplit zw s =
      Sum.elim zw.1 zw.2 (slotSplit s) := by
  rfl

/-- The d279 fully decoupled block statistic is exactly its standard ordered
`Fin k` statistic after flattening the two copy blocks. This is an equality of
the whole ordered statistic; it does not permute or symmetrize the `OrderedTuple`
sum, and it imposes no symmetry condition on `f`. -/
theorem sourceFullyDecoupled_eq_sourceOrderStatistic_flattened
    {S E : Type*} {n k p q : ℕ} [NormedAddCommGroup E]
    [Fintype (OrderedTuple n k)] [MeasurableSpace S]
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (f : OrderedTuple n k → (Fin k → S) → E)
    (zw : (Fin p → Fin n → S) × (Fin q → Fin n → S)) :
    sourceFullyDecoupledStatistic slotSplit f zw.1 zw.2 =
      sourceOrderDecoupledStatistic f
        (sourceCopyBlockFlatteningEquiv slotSplit zw) := by
  classical
  unfold sourceFullyDecoupledStatistic sourceOrderDecoupledStatistic
  apply Finset.sum_congr rfl
  intro t ht
  apply congrArg (f t)
  funext s
  rcases hs : slotSplit s with j | j
  · have hinv : slotSplit.symm (Sum.inl j) = s := by
      calc
        slotSplit.symm (Sum.inl j) = slotSplit.symm (slotSplit s) := by rw [hs]
        _ = s := Equiv.symm_apply_apply slotSplit s
    simp only [sourcePatternValues, sourceLeftTuple, hs, Sum.elim_inl]
    rw [sourceCopyBlockFlatteningEquiv_apply, hs]
    simp only [Sum.elim_inl]
    rw [hinv]
  · have hinv : slotSplit.symm (Sum.inr j) = s := by
      calc
        slotSplit.symm (Sum.inr j) = slotSplit.symm (slotSplit s) := by rw [hs]
        _ = s := Equiv.symm_apply_apply slotSplit s
    simp only [sourcePatternValues, sourceRightTuple, hs, Sum.elim_inr]
    rw [sourceCopyBlockFlatteningEquiv_apply, hs]
    simp only [Sum.elim_inr]
    rw [hinv]

/-- The d279 endpoint event is the exact preimage of the full-k-copy endpoint
event. This is the set-level step needed to transfer its probability through
the measure-preserving equivalence. -/
theorem sourceFullyDecoupled_event_preimage
    {S E : Type*} {n k p q : ℕ} [NormedAddCommGroup E]
    [Fintype (OrderedTuple n k)] [MeasurableSpace S]
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (f : OrderedTuple n k → (Fin k → S) → E)
    (r c : ℝ) :
    (sourceCopyBlockFlatteningEquiv slotSplit) ⁻¹'
        {z | r ≤ c * ‖sourceOrderDecoupledStatistic f z‖} =
      {zw | r ≤ c * ‖sourceFullyDecoupledStatistic slotSplit f zw.1 zw.2‖} := by
  ext zw
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [sourceFullyDecoupled_eq_sourceOrderStatistic_flattened slotSplit f zw]

/-- Composition of the copy-law transport and statistic identity: the
independent p/q block product has the exact full-k-copy law consumed by d279,
and under that equivalence its event statistic is the ordinary full-k ordered
statistic. The separate original one-array-to-product-law step is not included.
-/
theorem sourceFullyDecoupled_block_law_and_endpoint
    {S E : Type*} {n k p q : ℕ} [NormedAddCommGroup E]
    [MeasurableSpace S] [Fintype (OrderedTuple n k)]
    (marginal : Fin n → Measure S)
    [∀ i, IsProbabilityMeasure (marginal i)]
    (slotSplit : Fin k ≃ Fin p ⊕ Fin q)
    (f : OrderedTuple n k → (Fin k → S) → E)
    (zw : (Fin p → Fin n → S) × (Fin q → Fin n → S)) :
    MeasurePreserving (sourceCopyBlockFlatteningEquiv slotSplit)
      ((sourceCopiesLaw (r := p) marginal).prod
        (sourceCopiesLaw (r := q) marginal))
      (sourceCopiesLaw (r := k) marginal)
      ∧ sourceFullyDecoupledStatistic slotSplit f zw.1 zw.2 =
        sourceOrderDecoupledStatistic f
          (sourceCopyBlockFlatteningEquiv slotSplit zw) := by
  exact ⟨sourceCopyBlockFlattening_measurePreserving marginal slotSplit,
    sourceFullyDecoupled_eq_sourceOrderStatistic_flattened slotSplit f zw⟩


end DGRHS.Decoupling.Prop33

#check @DGRHS.Decoupling.Prop33.sourceCopyBlockFlattening_measurePreserving
#check @DGRHS.Decoupling.Prop33.sourceCanonicalCopyBlockFlattening_measurePreserving
#check @DGRHS.Decoupling.Prop33.sourceFullyDecoupled_eq_sourceOrderStatistic_flattened
#check @DGRHS.Decoupling.Prop33.sourceFullyDecoupled_event_preimage
#check @DGRHS.Decoupling.Prop33.sourceFullyDecoupled_block_law_and_endpoint
#print axioms DGRHS.Decoupling.Prop33.source_mixed_pattern_induction_from_uniform
#print axioms DGRHS.Decoupling.Prop33.sourceFullyDecoupled_block_law_and_endpoint
