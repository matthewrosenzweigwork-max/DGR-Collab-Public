/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the preserved MathFin LICENSE.
Authors: Raphael Coelho
DGR adaptation by Codex: explicit predictable rectangle atoms and a free finite
linear assembly, replacing upstream SimpleProcess with direct native Finsupp.
-/
import DGRHS.Commutator.SourceRieszBrownianPredictableMeasure
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! The finite-horizon rectangle embedding used for actual L2 completion.
The density strategy adapts MathFin/Foundations/ItoIntegralCLM.lean at
f085fd572075c934827f1eb92c4a085941cd21e5, preserved with its Apache-2.0 license. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

structure SourceRieszBrownianAtom (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0) where
  a : ℝ≥0
  b : ℝ≥0
  hab : a≤b
  hbT : b≤T
  event : Set Ω
  event_measurable : MeasurableSet[F a] event

namespace SourceRieszBrownianAtom
variable {F : Filtration ℝ≥0 mΩ} {T : ℝ≥0}

def value (A : SourceRieszBrownianAtom F T) : Ω→ℝ := A.event.indicator (fun _=>1)
def integrand (A : SourceRieszBrownianAtom F T) : ℝ≥0×Ω→ℝ :=
  sourceRieszBrownianBand A.a A.b A.value

lemma value_measurable (A : SourceRieszBrownianAtom F T) :
    StronglyMeasurable[F A.a] A.value :=
  stronglyMeasurable_const.indicator A.event_measurable

lemma value_bound (A : SourceRieszBrownianAtom F T) (ω : Ω) : ‖A.value ω‖≤1 := by
  by_cases h : ω∈A.event <;> simp [value,h]

lemma predictable (A : SourceRieszBrownianAtom F T) :
    StronglyMeasurable[F.predictable] A.integrand :=
  sourceRieszBrownianBand_predictable F A.a A.b A.value A.value_measurable

lemma rectangle (A : SourceRieszBrownianAtom F T) :
    A.integrand=(Ioc A.a A.b ×ˢ A.event).indicator (fun _=>1) := by
  funext p
  by_cases ht : p.1∈Ioc A.a A.b <;> by_cases hω : p.2∈A.event <;>
    simp [integrand,sourceRieszBrownianBand,value,ht,hω]

lemma bound (A : SourceRieszBrownianAtom F T) (p : ℝ≥0×Ω) : ‖A.integrand p‖≤1 := by
  rw [A.rectangle]
  by_cases h : p∈Ioc A.a A.b ×ˢ A.event <;> simp [h]

lemma support_horizon (A : SourceRieszBrownianAtom F T) (p : ℝ≥0×Ω)
    (hp : p.1∉Ioc 0 T) : A.integrand p=0 := by
  rw [A.rectangle]
  apply indicator_of_notMem
  rintro ⟨⟨ha,hb⟩,_⟩
  exact hp ⟨lt_of_le_of_lt bot_le ha,hb.trans A.hbT⟩

lemma memLp (P : Measure Ω) [IsFiniteMeasure P] (A : SourceRieszBrownianAtom F T) :
    MemLp A.integrand 2 (sourceRieszBrownianPredictableMeasure P F T) :=
  MemLp.of_bound A.predictable.aestronglyMeasurable 1 (ae_of_all _ A.bound)

end SourceRieszBrownianAtom

variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)

def sourceRieszBrownianAtomRawAssembly :
    (SourceRieszBrownianAtom F T →₀ ℝ) →ₗ[ℝ] (ℝ≥0×Ω→ℝ) :=
  Finsupp.linearCombination ℝ SourceRieszBrownianAtom.integrand

lemma sourceRieszBrownianAtomRawAssembly_apply (c : SourceRieszBrownianAtom F T →₀ ℝ)
    (p : ℝ≥0×Ω) : sourceRieszBrownianAtomRawAssembly F T c p=
      ∑ A∈c.support,c A*A.integrand p := by
  simp [sourceRieszBrownianAtomRawAssembly,Finsupp.linearCombination_apply,Finsupp.sum]

lemma sourceRieszBrownianAtomRawAssembly_memLp (c : SourceRieszBrownianAtom F T →₀ ℝ) :
    MemLp (sourceRieszBrownianAtomRawAssembly F T c) 2
      (sourceRieszBrownianPredictableMeasure P F T) := by
  have he : sourceRieszBrownianAtomRawAssembly F T c=
      fun p=>∑ A∈c.support,c A*A.integrand p := funext (sourceRieszBrownianAtomRawAssembly_apply F T c)
  rw [he]
  exact memLp_finsetSum _ fun A _=>(A.memLp P).const_mul (c A)

def sourceRieszBrownianAtomAssembly : (SourceRieszBrownianAtom F T →₀ ℝ) →ₗ[ℝ]
    Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T) where
  toFun c := (sourceRieszBrownianAtomRawAssembly_memLp P F T c).toLp _
  map_add' c d := by
    rw [←MemLp.toLp_add (sourceRieszBrownianAtomRawAssembly_memLp P F T c)
      (sourceRieszBrownianAtomRawAssembly_memLp P F T d)]
    congr 1
    exact map_add (sourceRieszBrownianAtomRawAssembly F T) c d
  map_smul' r c := by
    simp only [RingHom.id_apply]
    rw [←MemLp.toLp_const_smul r (sourceRieszBrownianAtomRawAssembly_memLp P F T c)]
    congr 1
    exact map_smul (sourceRieszBrownianAtomRawAssembly F T) r c

lemma sourceRieszBrownianAtomAssembly_coe (c : SourceRieszBrownianAtom F T →₀ ℝ) :
    (sourceRieszBrownianAtomAssembly P F T c : ℝ≥0×Ω→ℝ)
      =ᵐ[sourceRieszBrownianPredictableMeasure P F T] sourceRieszBrownianAtomRawAssembly F T c :=
  (sourceRieszBrownianAtomRawAssembly_memLp P F T c).coeFn_toLp

lemma sourceRieszBrownianAtomAssembly_single (A : SourceRieszBrownianAtom F T) :
    (sourceRieszBrownianAtomAssembly P F T (Finsupp.single A 1) : ℝ≥0×Ω→ℝ)
      =ᵐ[sourceRieszBrownianPredictableMeasure P F T] A.integrand := by
  convert sourceRieszBrownianAtomAssembly_coe P F T (Finsupp.single A 1) using 1
  simp [sourceRieszBrownianAtomRawAssembly]

end DGRHS.Commutator

#check @DGRHS.Commutator.SourceRieszBrownianAtom
#print axioms DGRHS.Commutator.SourceRieszBrownianAtom

#check @DGRHS.Commutator.SourceRieszBrownianAtom.mk
#print axioms DGRHS.Commutator.SourceRieszBrownianAtom.mk

#check @DGRHS.Commutator.SourceRieszBrownianAtom.value
#print axioms DGRHS.Commutator.SourceRieszBrownianAtom.value

#check @DGRHS.Commutator.SourceRieszBrownianAtom.integrand
#print axioms DGRHS.Commutator.SourceRieszBrownianAtom.integrand

#check @DGRHS.Commutator.SourceRieszBrownianAtom.value_measurable
#print axioms DGRHS.Commutator.SourceRieszBrownianAtom.value_measurable

#check @DGRHS.Commutator.SourceRieszBrownianAtom.value_bound
#print axioms DGRHS.Commutator.SourceRieszBrownianAtom.value_bound

#check @DGRHS.Commutator.SourceRieszBrownianAtom.predictable
#print axioms DGRHS.Commutator.SourceRieszBrownianAtom.predictable

#check @DGRHS.Commutator.SourceRieszBrownianAtom.rectangle
#print axioms DGRHS.Commutator.SourceRieszBrownianAtom.rectangle

#check @DGRHS.Commutator.SourceRieszBrownianAtom.bound
#print axioms DGRHS.Commutator.SourceRieszBrownianAtom.bound

#check @DGRHS.Commutator.SourceRieszBrownianAtom.support_horizon
#print axioms DGRHS.Commutator.SourceRieszBrownianAtom.support_horizon

#check @DGRHS.Commutator.SourceRieszBrownianAtom.memLp
#print axioms DGRHS.Commutator.SourceRieszBrownianAtom.memLp

#check @DGRHS.Commutator.sourceRieszBrownianAtomRawAssembly
#print axioms DGRHS.Commutator.sourceRieszBrownianAtomRawAssembly

#check @DGRHS.Commutator.sourceRieszBrownianAtomRawAssembly_apply
#print axioms DGRHS.Commutator.sourceRieszBrownianAtomRawAssembly_apply

#check @DGRHS.Commutator.sourceRieszBrownianAtomRawAssembly_memLp
#print axioms DGRHS.Commutator.sourceRieszBrownianAtomRawAssembly_memLp

#check @DGRHS.Commutator.sourceRieszBrownianAtomAssembly
#print axioms DGRHS.Commutator.sourceRieszBrownianAtomAssembly

#check @DGRHS.Commutator.sourceRieszBrownianAtomAssembly_coe
#print axioms DGRHS.Commutator.sourceRieszBrownianAtomAssembly_coe

#check @DGRHS.Commutator.sourceRieszBrownianAtomAssembly_single
#print axioms DGRHS.Commutator.sourceRieszBrownianAtomAssembly_single
