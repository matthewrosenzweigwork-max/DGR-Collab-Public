import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.MeasureTheory.Constructions.Pi

/-! Product-reference relative entropy, for source
`eq:product-conditional-entropy` at lines 2665--2670.  The extended nonnegative
values below preserve infinite cases; no subtraction of infinities is used.
The finite-coordinate induction below is complete. Identification of its
joint-law conditional costs with the supplied source conditional log integrals
is a separate remaining bridge.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace PeriodicAttractiveLogGas.ProductRelativeEntropy

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Relative entropy is unchanged by an actual measurable equivalence. -/
theorem klDiv_map_equiv (Q P : Measure α) [IsFiniteMeasure Q] [IsFiniteMeasure P]
    (e : α ≃ᵐ β) : klDiv (Q.map e) (P.map e) = klDiv Q P := by
  apply le_antisymm (klDiv_map_le Q P e.measurable)
  have h := klDiv_map_le (Q.map e) (P.map e) e.symm.measurable
  simpa only [e.map_symm_map] using h

/-- The exact product-reference chain rule uses the genuine conditional
kernel supplied by Mathlib's standard-Borel disintegration theorem. -/
theorem klDiv_prod_chain [StandardBorelSpace β] [Nonempty β]
    (Q : Measure (α × β)) [IsProbabilityMeasure Q]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv Q (μ.prod ν) = klDiv Q.fst μ + klDiv Q (Q.fst.prod ν) := by
  have h := klDiv_compProd_eq_add (μ := Q.fst) (ν := μ)
    (κ := Q.condKernel) (η := Kernel.const α ν)
  simpa only [Q.disintegrate Q.condKernel, Measure.compProd_const] using h

/-- The two-block tensorization inequality. Projection of the first
conditional-reference pair proves the conditioning direction by data
processing; the remaining term is the exact chain-rule term. -/
theorem two_block_tensorization [StandardBorelSpace β] [Nonempty β]
    (Q : Measure (α × β)) [IsProbabilityMeasure Q]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv Q (μ.prod ν) ≤ klDiv Q (μ.prod Q.snd) + klDiv Q (Q.fst.prod ν) := by
  rw [klDiv_prod_chain Q μ ν]
  apply add_le_add _ le_rfl
  have h := klDiv_map_le Q (μ.prod Q.snd) measurable_fst
  simpa only [Measure.fst, Measure.map_fst_prod, measure_univ, one_smul] using h

/-- Forgetting part of the outside information can only decrease the
conditional relative entropy with respect to the same coordinate reference.
The reference law is pushed forward along the same projection as the joint law. -/
theorem forget_conditioning (Q : Measure (α × β)) [IsProbabilityMeasure Q]
    (ν : Measure β) [IsProbabilityMeasure ν] (h : α → γ) (hh : Measurable h) :
    klDiv (Q.map (Prod.map h id)) ((Q.fst.map h).prod ν) ≤
      klDiv Q (Q.fst.prod ν) := by
  have hm : Measurable (Prod.map h (id : β → β)) := hh.prodMap measurable_id
  have he : (Q.fst.prod ν).map (Prod.map h id) = (Q.fst.map h).prod ν := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map Q.fst ν hh measurable_id).symm
  simpa only [he] using klDiv_map_le Q (Q.fst.prod ν) hm

/-- Replace one actual coordinate by an independent sample of its reference law. -/
def resample {n : ℕ} (Q : Measure (Fin n → α)) (ν : Measure α) (i : Fin n) :
    Measure (Fin n → α) :=
  (Q.prod ν).map (fun p => Function.update p.1 i p.2)

instance resample_probability {n : ℕ} (Q : Measure (Fin n → α)) (ν : Measure α)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure ν] (i : Fin n) :
    IsProbabilityMeasure (resample Q ν i) :=
  (Measure.isProbabilityMeasure_map_iff measurable_update'.aemeasurable).mpr inferInstance

def tail {n : ℕ} (X : Fin (n + 1) → α) : Fin n → α := fun j => X j.succ

theorem measurable_tail {n : ℕ} : Measurable (@tail α n) :=
  measurable_pi_iff.mpr fun j => measurable_pi_apply j.succ

/-- Independent resampling commutes with discarding a different coordinate. -/
theorem map_tail_resample {n : ℕ} (Q : Measure (Fin (n + 1) → α))
    (ν : Measure α) [IsProbabilityMeasure Q] [IsProbabilityMeasure ν] (j : Fin n) :
    (resample Q ν j.succ).map tail = resample (Q.map tail) ν j := by
  have hm : Measurable (Prod.map (@tail α n) (id : α → α)) :=
    measurable_tail.prodMap measurable_id
  have hp : (Q.map tail).prod ν = (Q.prod ν).map (Prod.map tail id) := by
    simpa only [Measure.map_id] using
      Measure.map_prod_map Q ν measurable_tail measurable_id
  rw [resample, Measure.map_map measurable_tail measurable_update', resample, hp,
    Measure.map_map measurable_update' hm]
  congr 1
  funext p k
  simp only [Function.comp_apply, tail, Prod.map_fst, Prod.map_snd, id_eq]
  by_cases h : k = j
  · subst k
    simp
  · have hh : k.succ ≠ j.succ := by
      intro hk
      have hv : k.val + 1 = j.val + 1 := congrArg Fin.val hk
      exact h (Fin.ext (by omega))
    simp [Function.update_of_ne h, Function.update_of_ne hh, tail]

/-- Actual data processing gives the further-conditioning direction at each
remaining coordinate, with extended values allowed. -/
theorem tail_conditional_cost_le {n : ℕ} (Q : Measure (Fin (n + 1) → α))
    (ν : Measure α) [IsProbabilityMeasure Q] [IsProbabilityMeasure ν] (j : Fin n) :
    klDiv (Q.map tail) (resample (Q.map tail) ν j) ≤ klDiv Q (resample Q ν j.succ) := by
  simpa only [map_tail_resample] using
    klDiv_map_le Q (resample Q ν j.succ) measurable_tail

def outside {n : ℕ} (i : Fin (n + 1)) (X : Fin (n + 1) → α) : Fin n → α :=
  fun j => X (i.succAbove j)

theorem measurable_outside {n : ℕ} (i : Fin (n + 1)) : Measurable (@outside α n i) :=
  measurable_pi_iff.mpr fun j => measurable_pi_apply (i.succAbove j)

/-- The outside coordinates followed by the chosen coordinate. -/
def coordinateSplit {n : ℕ} (i : Fin (n + 1)) :
    (Fin (n + 1) → α) ≃ᵐ ((Fin n → α) × α) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => α) i).trans
    MeasurableEquiv.prodComm

theorem coordinateSplit_apply {n : ℕ} (i : Fin (n + 1)) (X : Fin (n + 1) → α) :
    coordinateSplit i X = (outside i X, X i) := rfl

theorem coordinateSplit_fst {n : ℕ} (i : Fin (n + 1)) (Q : Measure (Fin (n + 1) → α)) :
    (Q.map (coordinateSplit i)).fst = Q.map (outside i) := by
  rw [Measure.fst, Measure.map_map measurable_fst (coordinateSplit i).measurable]
  rfl

/-- Under the actual coordinate equivalence the resampled law is precisely
the outside marginal times the chosen coordinate reference. -/
theorem map_resample_coordinateSplit {n : ℕ} (i : Fin (n + 1))
    (Q : Measure (Fin (n + 1) → α)) (ν : Measure α)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure ν] :
    (resample Q ν i).map (coordinateSplit i) = (Q.map (outside i)).prod ν := by
  have hp : (Q.map (outside i)).prod ν = (Q.prod ν).map (Prod.map (outside i) id) := by
    simpa only [Measure.map_id] using
      Measure.map_prod_map Q ν (measurable_outside i) measurable_id
  rw [resample, Measure.map_map (coordinateSplit i).measurable measurable_update', hp]
  congr 1
  funext p
  apply Prod.ext
  · funext j
    change Function.update p.1 i p.2 (i.succAbove j) = p.1 (i.succAbove j)
    exact Function.update_of_ne (i.succAbove_ne j) _ _
  · change Function.update p.1 i p.2 i = p.2
    simp

theorem map_pi_coordinateSplit {n : ℕ} (i : Fin (n + 1))
    (μ : Fin (n + 1) → Measure α) [∀ j, IsProbabilityMeasure (μ j)] :
    (Measure.pi μ).map (coordinateSplit i) = (Measure.pi (fun j => μ (i.succAbove j))).prod (μ i) := by
  change (Measure.pi μ).map (Prod.swap ∘ (MeasurableEquiv.piFinSuccAbove (fun _ => α) i)) = _
  rw [← Measure.map_map measurable_swap (MeasurableEquiv.piFinSuccAbove (fun _ => α) i).measurable,
    (measurePreserving_piFinSuccAbove μ i).map_eq, Measure.prod_swap]

/-- Splitting the first coordinate of the genuine finite product gives an
exact entropy chain rule with the actual independently resampled law. -/
theorem klDiv_pi_chain [StandardBorelSpace α] [Nonempty α] {n : ℕ}
    (Q : Measure (Fin (n + 1) → α)) [IsProbabilityMeasure Q]
    (μ : Fin (n + 1) → Measure α) [∀ j, IsProbabilityMeasure (μ j)] :
    klDiv Q (Measure.pi μ) = klDiv (Q.map tail) (Measure.pi (fun j => μ j.succ)) +
      klDiv Q (resample Q (μ 0) 0) := by
  have h := klDiv_prod_chain (Q.map (coordinateSplit (0 : Fin (n + 1))))
    (Measure.pi (fun j => μ ((0 : Fin (n + 1)).succAbove j))) (μ 0)
  rw [← map_pi_coordinateSplit 0 μ, klDiv_map_equiv, coordinateSplit_fst,
    ← map_resample_coordinateSplit, klDiv_map_equiv] at h
  exact h

theorem probability_eq_of_subsingleton [Subsingleton α]
    (Q P : Measure α) [IsProbabilityMeasure Q] [IsProbabilityMeasure P] : Q = P := by
  apply Measure.ext
  intro s _
  by_cases hs : s.Nonempty
  · obtain ⟨y, hy⟩ := hs
    have he : s = Set.univ := Set.eq_univ_of_forall fun x => by
      rw [Subsingleton.elim x y]
      exact hy
    simp only [he, measure_univ]
  · rw [Set.not_nonempty_iff_eq_empty.mp hs]
    simp

/-- The product-reference tensorization inequality, with the conditional
cost expressed by the genuine independently resampled law. It includes all
finite particle numbers and infinite entropy values. The proof follows the
product chain rule and data processing under further conditioning. -/
theorem product_tensorization [StandardBorelSpace α] [Nonempty α] (n : ℕ) :
    ∀ (Q : Measure (Fin n → α)) [IsProbabilityMeasure Q]
      (μ : Fin n → Measure α) [∀ i, IsProbabilityMeasure (μ i)],
      klDiv Q (Measure.pi μ) ≤ ∑ i, klDiv Q (resample Q (μ i) i) := by
  induction n with
  | zero =>
    intro Q hQ μ hμ
    rw [probability_eq_of_subsingleton Q (Measure.pi μ), klDiv_self]
    exact bot_le
  | succ n ih =>
    intro Q hQ μ hμ
    rw [klDiv_pi_chain Q μ, Fin.sum_univ_succ]
    calc
      klDiv (Q.map tail) (Measure.pi fun j => μ j.succ) + klDiv Q (resample Q (μ 0) 0)
        ≤ (∑ j, klDiv (Q.map tail) (resample (Q.map tail) (μ j.succ) j)) +
            klDiv Q (resample Q (μ 0) 0) :=
          add_le_add (ih (Q.map tail) (fun j => μ j.succ)) le_rfl
      _ ≤ (∑ j, klDiv Q (resample Q (μ j.succ) j.succ)) + klDiv Q (resample Q (μ 0) 0) :=
          add_le_add (Finset.sum_le_sum fun j _ => tail_conditional_cost_le Q (μ j.succ) j) le_rfl
      _ = _ := add_comm _ _

/-- The resampling cost is exactly the joint relative entropy with respect
to the outside marginal times the coordinate reference. -/
theorem conditional_cost_eq {n : ℕ} (Q : Measure (Fin (n + 1) → α))
    [IsProbabilityMeasure Q] (ν : Measure α) [IsProbabilityMeasure ν] (i : Fin (n + 1)) :
    klDiv Q (resample Q ν i) =
      klDiv (Q.map (coordinateSplit i)) ((Q.map (outside i)).prod ν) := by
  rw [← map_resample_coordinateSplit, klDiv_map_equiv]

theorem product_tensorization_joint [StandardBorelSpace α] [Nonempty α] {n : ℕ}
    (Q : Measure (Fin (n + 1) → α)) [IsProbabilityMeasure Q]
    (μ : Fin (n + 1) → Measure α) [∀ i, IsProbabilityMeasure (μ i)] :
    klDiv Q (Measure.pi μ) ≤
      ∑ i, klDiv (Q.map (coordinateSplit i)) ((Q.map (outside i)).prod (μ i)) := by
  simpa only [conditional_cost_eq] using product_tensorization (n + 1) Q μ

end PeriodicAttractiveLogGas.ProductRelativeEntropy
