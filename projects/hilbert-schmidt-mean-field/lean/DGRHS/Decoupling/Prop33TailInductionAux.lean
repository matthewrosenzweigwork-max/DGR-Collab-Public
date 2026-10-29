import DGRHS.Decoupling.Prop33UnifiedCopyEndpoint
import DGRHS.Decoupling.Prop33SelectorTonelliBridge

/-!
Auxiliary pieces of the all-order tail induction of Proposition 3.3
(de la Peña–Montgomery-Smith, Theorem 1): measurability of the ordered statistics,
monotonicity of the uniform tail predicate in the constant, the order-one base
case, and the three-copy symmetrization lemma on source arrays.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace DGRHS.Decoupling.Prop33

section Measurability
variable {S E : Type*} [MeasurableSpace S] [MeasurableSpace E] [NormedAddCommGroup E]
  [MeasurableAdd₂ E] {n r : ℕ}

lemma measurable_sourceOrderStatistic [Fintype (OrderedTuple n r)]
    (K : OrderedTuple n r → (Fin r → S) → E) (hK : ∀ a, Measurable (K a)) :
    Measurable (fun x : Fin n → S => sourceOrderStatistic K x) := by
  unfold sourceOrderStatistic
  apply Finset.measurable_sum
  intro a _
  refine (hK a).comp ?_
  refine measurable_pi_iff.mpr ?_
  intro j
  exact measurable_pi_apply (a.1 j)

lemma measurable_sourceOrderDecoupledStatistic [Fintype (OrderedTuple n r)]
    (K : OrderedTuple n r → (Fin r → S) → E) (hK : ∀ a, Measurable (K a)) :
    Measurable (fun z : Fin r → Fin n → S => sourceOrderDecoupledStatistic K z) := by
  unfold sourceOrderDecoupledStatistic
  apply Finset.measurable_sum
  intro a _
  refine (hK a).comp ?_
  refine measurable_pi_iff.mpr ?_
  intro j
  exact (measurable_pi_apply (a.1 j)).comp (measurable_pi_apply j)

end Measurability

section Mono
variable {S E : Type*} [MeasurableSpace S] [MeasurableSpace E] [NormedAddCommGroup E]
  [OpensMeasurableSpace E] [MeasurableAdd₂ E]

/-- The uniform tail predicate is monotone in the constant (for nonnegative constants). -/
lemma sourceUniformTailAtOrder.mono {r : ℕ} {C C' : ℝ} (hC : 0 ≤ C) (hCC' : C ≤ C')
    (h : sourceUniformTailAtOrder (S := S) (E := E) r C) :
    sourceUniformTailAtOrder (S := S) (E := E) r C' := by
  intro n marginal hm hrn hF K hK t ht
  refine (h marginal hrn K hK t ht).trans ?_
  gcongr

end Mono


section Base
variable {S E : Type*} [MeasurableSpace S] [MeasurableSpace E]
  [NormedAddCommGroup E] [OpensMeasurableSpace E] [MeasurableAdd₂ E]

/-- At order one, the one-fold copy law pushes forward exactly to the original
heterogeneous array law, and the source statistic is unchanged. -/
theorem sourceUniformTailAtOrder_one :
    sourceUniformTailAtOrder (S := S) (E := E) 1 1 := by
  intro n marginal hmarginal hn htuple K hK t ht
  classical
  let ev : (Fin 1 → Fin n → S) → (Fin n → S) := fun z => z 0
  have hev : MeasurePreserving ev
      (sourceCopiesLaw (r := 1) marginal) (sourceArrayLaw marginal) := by
    dsimp [ev, sourceCopiesLaw, sourceArrayLaw]
    exact measurePreserving_eval
      (fun _ : Fin 1 => Measure.pi marginal) (0 : Fin 1)
  have hOrigStat := measurable_sourceOrderStatistic K hK
  have hCopyStat := measurable_sourceOrderDecoupledStatistic K hK
  let A : Set (Fin n → S) :=
    {x | t ≤ ‖sourceOrderStatistic K x‖}
  let B : Set (Fin 1 → Fin n → S) :=
    {z | t ≤ ‖sourceOrderDecoupledStatistic K z‖}
  have hA : MeasurableSet A := by
    exact measurableSet_le measurable_const (Measurable.norm hOrigStat)
  have hstat (z : Fin 1 → Fin n → S) :
      sourceOrderDecoupledStatistic K z = sourceOrderStatistic K (ev z) := by
    unfold sourceOrderDecoupledStatistic sourceOrderStatistic
    apply Finset.sum_congr rfl
    intro a ha
    apply congrArg (K a)
    funext j
    change z j (a.1 j) = z 0 (a.1 j)
    have hj : j = (0 : Fin 1) := by
      apply Fin.ext
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt)
    rw [hj]
  have hBpre : B = ev ⁻¹' A := by
    ext z
    simp only [A, B, Set.mem_ofPred_eq, Set.mem_preimage]
    rw [hstat z]
  have hmeasure :
      sourceArrayLaw marginal A = sourceCopiesLaw (r := 1) marginal B := by
    calc
      sourceArrayLaw marginal A =
          (Measure.map ev (sourceCopiesLaw (r := 1) marginal)) A := by
        rw [hev.map_eq]
      _ = sourceCopiesLaw (r := 1) marginal (ev ⁻¹' A) :=
        Measure.map_apply hev.measurable hA
      _ = sourceCopiesLaw (r := 1) marginal B := by rw [← hBpre]
  simpa [sourceUniformTailAtOrder, A, B] using hmeasure.le

end Base

section ThreeCopy
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableAdd₂ E]

/-- Pointwise three-copy inclusion: `2u = (u+v)+(u+w)-(v+w)`. -/
lemma threeCopy_event_cases (u v w : E) (t : ℝ) (h : t ≤ ‖u‖) :
    2 * t / 3 ≤ ‖u + v‖ ∨ 2 * t / 3 ≤ ‖u + w‖ ∨ 2 * t / 3 ≤ ‖v + w‖ := by
  by_contra hnot
  simp only [not_or, not_le] at hnot
  obtain ⟨h01, h02, h12⟩ := hnot
  have hid : (u + v) + (u + w) - (v + w) = (2 : ℝ) • u := by module
  have hlow : 2 * t ≤ ‖(u + v) + (u + w) - (v + w)‖ := by
    calc 2 * t ≤ 2 * ‖u‖ := by linarith
      _ = ‖(2 : ℝ) • u‖ := by rw [norm_smul]; norm_num
      _ = _ := by rw [hid]
  have hupp : ‖(u + v) + (u + w) - (v + w)‖ ≤ ‖u + v‖ + ‖u + w‖ + ‖v + w‖ := by
    calc _ ≤ ‖(u + v) + (u + w)‖ + ‖v + w‖ := norm_sub_le _ _
      _ ≤ _ := by linarith [norm_add_le (u + v) (u + w)]
  linarith

/-- Three-copy symmetrization (dPmS Lemma 1) for a measurable `E`-valued statistic on
a probability space: `P(‖U‖ ≥ t) ≤ 3 P(‖U(x) + U(y)‖ ≥ 2t/3)` with `x, y` independent. -/
theorem threeCopy_tail (μ : Measure X) [IsProbabilityMeasure μ] (U : X → E)
    (hU : Measurable U) (t : ℝ) :
    μ {x | t ≤ ‖U x‖} ≤ 3 * (μ.prod μ) {xy | 2 * t / 3 ≤ ‖U xy.1 + U xy.2‖} := by
  let μ3 := μ.prod (μ.prod μ)
  have hA : MeasurableSet {x | t ≤ ‖U x‖} := measurableSet_le measurable_const hU.norm
  have hP : MeasurableSet {xy : X × X | 2 * t / 3 ≤ ‖U xy.1 + U xy.2‖} :=
    measurableSet_le measurable_const
      ((hU.comp measurable_fst).add (hU.comp measurable_snd)).norm
  have hm1 : MeasurePreserving (fun w : X × (X × X) => (w.1, w.2.1)) μ3 (μ.prod μ) :=
    (MeasurePreserving.id μ).prod measurePreserving_fst
  have hm2 : MeasurePreserving (fun w : X × (X × X) => (w.1, w.2.2)) μ3 (μ.prod μ) :=
    (MeasurePreserving.id μ).prod measurePreserving_snd
  have hm3 : MeasurePreserving (fun w : X × (X × X) => (w.2.1, w.2.2)) μ3 (μ.prod μ) :=
    measurePreserving_snd
  have hmf : MeasurePreserving (fun w : X × (X × X) => w.1) μ3 μ := measurePreserving_fst
  have e1 : μ3 ((fun w : X × (X × X) => (w.1, w.2.1)) ⁻¹'
      {xy : X × X | 2 * t / 3 ≤ ‖U xy.1 + U xy.2‖}) =
      (μ.prod μ) {xy | 2 * t / 3 ≤ ‖U xy.1 + U xy.2‖} :=
    hm1.measure_preimage hP.nullMeasurableSet
  have e2 : μ3 ((fun w : X × (X × X) => (w.1, w.2.2)) ⁻¹'
      {xy : X × X | 2 * t / 3 ≤ ‖U xy.1 + U xy.2‖}) =
      (μ.prod μ) {xy | 2 * t / 3 ≤ ‖U xy.1 + U xy.2‖} :=
    hm2.measure_preimage hP.nullMeasurableSet
  have e3 : μ3 ((fun w : X × (X × X) => (w.2.1, w.2.2)) ⁻¹'
      {xy : X × X | 2 * t / 3 ≤ ‖U xy.1 + U xy.2‖}) =
      (μ.prod μ) {xy | 2 * t / 3 ≤ ‖U xy.1 + U xy.2‖} :=
    hm3.measure_preimage hP.nullMeasurableSet
  have e0 : μ3 ((fun w : X × (X × X) => w.1) ⁻¹' {x | t ≤ ‖U x‖}) = μ {x | t ≤ ‖U x‖} :=
    hmf.measure_preimage hA.nullMeasurableSet
  calc μ {x | t ≤ ‖U x‖} = μ3 ((fun w : X × (X × X) => w.1) ⁻¹' {x | t ≤ ‖U x‖}) := e0.symm
    _ ≤ μ3 ((fun w : X × (X × X) => (w.1, w.2.1)) ⁻¹'
          {xy : X × X | 2 * t / 3 ≤ ‖U xy.1 + U xy.2‖} ∪
        ((fun w : X × (X × X) => (w.1, w.2.2)) ⁻¹'
          {xy : X × X | 2 * t / 3 ≤ ‖U xy.1 + U xy.2‖} ∪
        (fun w : X × (X × X) => (w.2.1, w.2.2)) ⁻¹'
          {xy : X × X | 2 * t / 3 ≤ ‖U xy.1 + U xy.2‖})) := by
        apply measure_mono
        intro w hw
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_union] at hw ⊢
        exact threeCopy_event_cases (U w.1) (U w.2.1) (U w.2.2) t hw
    _ ≤ μ3 ((fun w : X × (X × X) => (w.1, w.2.1)) ⁻¹'
          {xy : X × X | 2 * t / 3 ≤ ‖U xy.1 + U xy.2‖}) +
        (μ3 ((fun w : X × (X × X) => (w.1, w.2.2)) ⁻¹'
          {xy : X × X | 2 * t / 3 ≤ ‖U xy.1 + U xy.2‖}) +
        μ3 ((fun w : X × (X × X) => (w.2.1, w.2.2)) ⁻¹'
          {xy : X × X | 2 * t / 3 ≤ ‖U xy.1 + U xy.2‖})) :=
        (measure_union_le _ _).trans (add_le_add_right (measure_union_le _ _) _)
    _ = 3 * (μ.prod μ) {xy | 2 * t / 3 ≤ ‖U xy.1 + U xy.2‖} := by
        rw [e1, e2, e3]; ring

end ThreeCopy

end DGRHS.Decoupling.Prop33
