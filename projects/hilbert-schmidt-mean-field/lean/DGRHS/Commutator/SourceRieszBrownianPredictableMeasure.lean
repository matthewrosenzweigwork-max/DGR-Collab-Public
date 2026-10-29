/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the preserved MathFin LICENSE.
Authors: Raphael Coelho
DGR adaptation by Codex: explicit supplied filtration and direct predictable
rectangle generators, without upstream SimpleProcess or natural-filtration data.
-/
import DGRHS.Commutator.SourceRieszBrownianTime
import Mathlib.MeasureTheory.Function.L2Space

/-! Selected adaptation of MathFin/Foundations/ItoIntegralCLM.lean at
f085fd572075c934827f1eb92c4a085941cd21e5. Finite-horizon predictable measure
and a direct generating pi-system; source and license are preserved in records. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def sourceRieszBrownianTimeOn (T : ℝ≥0) : Measure ℝ≥0 :=
  sourceRieszBrownianTime.restrict (Ioc 0 T)

instance sourceRieszBrownianTimeOn_finite (T : ℝ≥0) :
    IsFiniteMeasure (sourceRieszBrownianTimeOn T) := by
  refine ⟨?_⟩
  rw [sourceRieszBrownianTimeOn,Measure.restrict_apply MeasurableSet.univ,univ_inter,
    sourceRieszBrownianTime_Ioc]
  exact ENNReal.ofReal_lt_top

def sourceRieszBrownianPredictableMeasure (P : Measure Ω)
    (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0) :=
  ((sourceRieszBrownianTimeOn T).prod P).trim (sourceRiesz_predictable_le_product F)

instance sourceRieszBrownianPredictableMeasure_finite (P : Measure Ω)
    [IsFiniteMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0) :
    IsFiniteMeasure (sourceRieszBrownianPredictableMeasure P F T) := by
  unfold sourceRieszBrownianPredictableMeasure
  infer_instance

def sourceRieszBrownianPredictableRect (F : Filtration ℝ≥0 mΩ) : Set (Set (ℝ≥0×Ω)) :=
  {S | (∃ A,MeasurableSet[F 0] A ∧ S={0}×ˢ A) ∨
    ∃ a b A,MeasurableSet[F a] A ∧ S=Ioc a b ×ˢ A}

lemma sourceRieszBrownianPredictableRect_measurable (F : Filtration ℝ≥0 mΩ)
    {S : Set (ℝ≥0×Ω)} (hS : S∈sourceRieszBrownianPredictableRect F) :
    MeasurableSet[F.predictable] S := by
  rcases hS with ⟨A,hA,rfl⟩ | ⟨a,b,A,hA,rfl⟩
  · exact measurableSet_predictable_singleton_bot_prod hA
  · exact measurableSet_predictable_Ioc_prod a b hA

lemma sourceRieszBrownianPredictableRect_pi (F : Filtration ℝ≥0 mΩ) :
    IsPiSystem (sourceRieszBrownianPredictableRect F) := by
  intro S hS R hR _
  rcases hS with ⟨A,hA,rfl⟩ | ⟨a,b,A,hA,rfl⟩ <;>
    rcases hR with ⟨C,hC,rfl⟩ | ⟨c,d,C,hC,rfl⟩
  · exact Or.inl ⟨A∩C,hA.inter hC,by rw [prod_inter_prod,inter_self]⟩
  · have he : ({0} : Set ℝ≥0)∩Ioc c d=∅ := by ext x;simp
    exact Or.inl ⟨∅,(@MeasurableSet.empty Ω (F 0)),by rw [prod_inter_prod,he,empty_prod,prod_empty]⟩
  · have he : Ioc a b∩({0} : Set ℝ≥0)=∅ := by ext x;simp
    exact Or.inl ⟨∅,(@MeasurableSet.empty Ω (F 0)),by rw [prod_inter_prod,he,empty_prod,prod_empty]⟩
  · exact Or.inr ⟨max a c,min b d,A∩C,
      (F.mono (le_max_left a c) _ hA).inter (F.mono (le_max_right a c) _ hC),
      by rw [prod_inter_prod,Ioc_inter_Ioc]⟩

lemma sourceRieszBrownianPredictableRect_generate (F : Filtration ℝ≥0 mΩ) :
    MeasurableSpace.generateFrom (sourceRieszBrownianPredictableRect F)=F.predictable := by
  apply le_antisymm
  · exact MeasurableSpace.generateFrom_le fun _ h=>sourceRieszBrownianPredictableRect_measurable F h
  · apply measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      exact MeasurableSpace.measurableSet_generateFrom (Or.inl ⟨A,hA,rfl⟩)
    · intro a A hA
      obtain ⟨seq,_,ht⟩ := Filter.exists_seq_monotone_tendsto_atTop_atTop ℝ≥0
      have he : Ioi a=⋃ n : ℕ,Ioc a (seq n) := by
        ext t
        simp only [mem_Ioi,mem_iUnion,mem_Ioc]
        constructor
        · intro hat
          rw [Filter.tendsto_atTop_atTop] at ht
          obtain ⟨n,hn⟩ := ht t
          exact ⟨n,hat,hn n le_rfl⟩
        · rintro ⟨_,h,_⟩
          exact h
      rw [he,iUnion_prod_const]
      exact MeasurableSet.iUnion fun n=>MeasurableSpace.measurableSet_generateFrom
        (Or.inr ⟨a,seq n,A,hA,rfl⟩)

lemma sourceRieszBrownianPredictableMeasure_restrict (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0) :
    sourceRieszBrownianPredictableMeasure P F T=
      ((sourceRieszBrownianTime.prod P).trim (sourceRiesz_predictable_le_product F)).restrict
        (Ioc 0 T ×ˢ univ) := by
  unfold sourceRieszBrownianPredictableMeasure sourceRieszBrownianTimeOn
  rw [Measure.restrict_prod_eq_prod_univ,←restrict_trim (sourceRiesz_predictable_le_product F) _
    (measurableSet_predictable_Ioc_prod 0 T MeasurableSet.univ)]

lemma sourceRieszBrownianPredictableMeasure_ae (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0) :
    ∀ᵐ p ∂sourceRieszBrownianPredictableMeasure P F T,p.1∈Ioc 0 T := by
  rw [sourceRieszBrownianPredictableMeasure_restrict]
  exact (ae_restrict_mem (measurableSet_predictable_Ioc_prod 0 T
    (MeasurableSet.univ : MeasurableSet[F 0] (univ : Set Ω)))).mono fun _ h=>h.1

lemma sourceRieszBrownianPredictableMeasure_inter (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (g : ℝ≥0×Ω→ℝ) (R : Set (ℝ≥0×Ω)) (hR : MeasurableSet[F.predictable] R) :
    (∫ p in R,g p ∂sourceRieszBrownianPredictableMeasure P F T)=
      ∫ p in R∩(Ioc 0 T ×ˢ univ),g p ∂sourceRieszBrownianPredictableMeasure P F T := by
  letI : MeasurableSpace (ℝ≥0×Ω) := F.predictable
  have hS : MeasurableSet (Ioc 0 T ×ˢ (univ : Set Ω)) :=
    measurableSet_predictable_Ioc_prod 0 T MeasurableSet.univ
  have he : (sourceRieszBrownianPredictableMeasure P F T).restrict R=
      (sourceRieszBrownianPredictableMeasure P F T).restrict (R∩(Ioc 0 T ×ˢ univ)) := by
    rw [sourceRieszBrownianPredictableMeasure_restrict,Measure.restrict_restrict hR,
      Measure.restrict_restrict (hR.inter hS),inter_assoc,inter_self]
  exact congrArg (fun μ=>∫ p,g p ∂μ) he

end DGRHS.Commutator

#check @DGRHS.Commutator.sourceRieszBrownianTimeOn
#print axioms DGRHS.Commutator.sourceRieszBrownianTimeOn

#check @DGRHS.Commutator.sourceRieszBrownianTimeOn_finite
#print axioms DGRHS.Commutator.sourceRieszBrownianTimeOn_finite

#check @DGRHS.Commutator.sourceRieszBrownianPredictableMeasure
#print axioms DGRHS.Commutator.sourceRieszBrownianPredictableMeasure

#check @DGRHS.Commutator.sourceRieszBrownianPredictableMeasure_finite
#print axioms DGRHS.Commutator.sourceRieszBrownianPredictableMeasure_finite

#check @DGRHS.Commutator.sourceRieszBrownianPredictableRect
#print axioms DGRHS.Commutator.sourceRieszBrownianPredictableRect

#check @DGRHS.Commutator.sourceRieszBrownianPredictableRect_measurable
#print axioms DGRHS.Commutator.sourceRieszBrownianPredictableRect_measurable

#check @DGRHS.Commutator.sourceRieszBrownianPredictableRect_pi
#print axioms DGRHS.Commutator.sourceRieszBrownianPredictableRect_pi

#check @DGRHS.Commutator.sourceRieszBrownianPredictableRect_generate
#print axioms DGRHS.Commutator.sourceRieszBrownianPredictableRect_generate

#check @DGRHS.Commutator.sourceRieszBrownianPredictableMeasure_restrict
#print axioms DGRHS.Commutator.sourceRieszBrownianPredictableMeasure_restrict

#check @DGRHS.Commutator.sourceRieszBrownianPredictableMeasure_ae
#print axioms DGRHS.Commutator.sourceRieszBrownianPredictableMeasure_ae

#check @DGRHS.Commutator.sourceRieszBrownianPredictableMeasure_inter
#print axioms DGRHS.Commutator.sourceRieszBrownianPredictableMeasure_inter
