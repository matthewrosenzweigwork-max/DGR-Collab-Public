/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the preserved MathFin LICENSE.
Authors: Raphael Coelho
DGR adaptation by Codex: supplied full filtration, direct rectangle Finsupp
assembly, and an explicit finite predictable measure.
-/
import DGRHS.Commutator.SourceRieszBrownianAtoms
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! Selected density proof adapted from MathFin/Foundations/ItoIntegralCLM.lean
at f085fd572075c934827f1eb92c4a085941cd21e5, preserved with Apache-2.0 license.
No density premise is introduced: orthogonality is converted into zero rectangle
integrals and then zero integrals on the generated predictable sigma-algebra. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)

lemma sourceRieszBrownian_zeroIntegral_predictable {g : ℝ≥0×Ω→ℝ}
    (hg : Integrable g (sourceRieszBrownianPredictableMeasure P F T))
    (hR : ∀ R∈sourceRieszBrownianPredictableRect F,
      (∫ p in R,g p ∂sourceRieszBrownianPredictableMeasure P F T)=0)
    (S : Set (ℝ≥0×Ω)) (hS : MeasurableSet[F.predictable] S) :
    (∫ p in S,g p ∂sourceRieszBrownianPredictableMeasure P F T)=0 := by
  letI : MeasurableSpace (ℝ≥0×Ω) := F.predictable
  have hsupport : MeasurableSet (Ioc 0 T ×ˢ (univ : Set Ω)) :=
    measurableSet_predictable_Ioc_prod 0 T MeasurableSet.univ
  have htotal : (∫ p,g p ∂sourceRieszBrownianPredictableMeasure P F T)=0 := by
    calc (∫ p,g p ∂sourceRieszBrownianPredictableMeasure P F T)
        = ∫ p,(Ioc 0 T ×ˢ (univ : Set Ω)).indicator g p
            ∂sourceRieszBrownianPredictableMeasure P F T := by
          apply integral_congr_ae
          filter_upwards [sourceRieszBrownianPredictableMeasure_ae P F T] with p hp
          exact (indicator_of_mem (show p∈Ioc 0 T ×ˢ (univ : Set Ω) from ⟨hp,mem_univ _⟩) g).symm
      _ = ∫ p in Ioc 0 T ×ˢ (univ : Set Ω),g p
          ∂sourceRieszBrownianPredictableMeasure P F T := integral_indicator hsupport
      _ = 0 := hR _ (Or.inr ⟨0,T,univ,MeasurableSet.univ,rfl⟩)
  refine MeasurableSpace.induction_on_inter
    (C:=fun S _=>(∫ p in S,g p ∂sourceRieszBrownianPredictableMeasure P F T)=0)
    (h_eq:=(sourceRieszBrownianPredictableRect_generate F).symm)
    (h_inter:=sourceRieszBrownianPredictableRect_pi F)
    (empty:=setIntegral_empty) (basic:=fun R h=>hR R h) (compl:=?_) (iUnion:=?_) S hS
  · intro R hRm hz
    have he:=integral_add_compl (μ:=sourceRieszBrownianPredictableMeasure P F T) (f:=g) hRm hg
    linarith
  · intro f hf hfm hz
    rw [integral_iUnion hfm hf hg.integrableOn]
    simp [hz]

lemma sourceRieszBrownianAtomAssembly_inner (A : SourceRieszBrownianAtom F T)
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    ⟪sourceRieszBrownianAtomAssembly P F T (Finsupp.single A 1),g⟫_ℝ=
      ∫ p in Ioc A.a A.b ×ˢ A.event,g p ∂sourceRieszBrownianPredictableMeasure P F T := by
  letI : MeasurableSpace (ℝ≥0×Ω) := F.predictable
  rw [L2.inner_def]
  have he : (fun p=>⟪sourceRieszBrownianAtomAssembly P F T (Finsupp.single A 1) p,g p⟫_ℝ)
      =ᵐ[sourceRieszBrownianPredictableMeasure P F T]
        (Ioc A.a A.b ×ˢ A.event).indicator (fun p=>g p) := by
    filter_upwards [sourceRieszBrownianAtomAssembly_single P F T A] with p hp
    rw [hp,A.rectangle]
    change g p*(Ioc A.a A.b ×ˢ A.event).indicator (fun _=>1) p=_
    by_cases h : p∈Ioc A.a A.b ×ˢ A.event <;> simp [h]
  rw [integral_congr_ae he]
  exact integral_indicator (measurableSet_predictable_Ioc_prod A.a A.b A.event_measurable)

theorem sourceRieszBrownianAtomAssembly_dense : DenseRange (sourceRieszBrownianAtomAssembly P F T) := by
  suffices ho : (LinearMap.range (sourceRieszBrownianAtomAssembly P F T))ᗮ=⊥ by
    rw [denseRange_iff_closure_range,←LinearMap.coe_range (sourceRieszBrownianAtomAssembly P F T),
      ←Submodule.topologicalClosure_coe,Submodule.topologicalClosure_eq_top_iff.mpr ho,Submodule.top_coe]
  rw [Submodule.eq_bot_iff]
  intro g hg
  rw [Submodule.mem_orthogonal] at hg
  have hR : ∀ R∈sourceRieszBrownianPredictableRect F,
      (∫ p in R,g p ∂sourceRieszBrownianPredictableMeasure P F T)=0 := by
    intro R hR
    rcases hR with ⟨A,hA,rfl⟩ | ⟨a,b,A,hA,rfl⟩
    · have hm : MeasurableSet[F.predictable] ({0}×ˢ A) :=
        measurableSet_predictable_singleton_bot_prod hA
      rw [sourceRieszBrownianPredictableMeasure_inter P F T g _ hm]
      have he : ({0}×ˢ A)∩(Ioc 0 T ×ˢ (univ : Set Ω))=∅ := by
        rw [prod_inter_prod,show ({0} : Set ℝ≥0)∩Ioc 0 T=∅ by ext x;simp,empty_prod]
      rw [he,setIntegral_empty]
    · have hm : MeasurableSet[F.predictable] (Ioc a b ×ˢ A) :=
        measurableSet_predictable_Ioc_prod a b hA
      rw [sourceRieszBrownianPredictableMeasure_inter P F T g _ hm,
        prod_inter_prod,Ioc_inter_Ioc,inter_univ,max_eq_left (show (0:ℝ≥0)≤a from bot_le)]
      by_cases hab : a≤min b T
      · let Q : SourceRieszBrownianAtom F T := ⟨a,min b T,hab,min_le_right b T,A,hA⟩
        have hi := hg _ ⟨Finsupp.single Q 1,rfl⟩
        rw [sourceRieszBrownianAtomAssembly_inner P F T Q g] at hi
        exact hi
      · rw [Ioc_eq_empty (not_lt.mpr (le_of_not_ge hab)),empty_prod,setIntegral_empty]
  letI : MeasurableSpace (ℝ≥0×Ω) := F.predictable
  refine (Lp.eq_zero_iff_ae_eq_zero (f:=g)).mpr ?_
  exact Lp.ae_eq_zero_of_forall_setIntegral_eq_zero g (by norm_num) (by norm_num)
    (fun _ _ _=>((Lp.memLp g).integrable one_le_two).integrableOn)
    (fun S hS _=>sourceRieszBrownian_zeroIntegral_predictable P F T
      ((Lp.memLp g).integrable one_le_two) hR S hS)

end DGRHS.Commutator

#check @DGRHS.Commutator.sourceRieszBrownian_zeroIntegral_predictable
#print axioms DGRHS.Commutator.sourceRieszBrownian_zeroIntegral_predictable

#check @DGRHS.Commutator.sourceRieszBrownianAtomAssembly_inner
#print axioms DGRHS.Commutator.sourceRieszBrownianAtomAssembly_inner

#check @DGRHS.Commutator.sourceRieszBrownianAtomAssembly_dense
#print axioms DGRHS.Commutator.sourceRieszBrownianAtomAssembly_dense
