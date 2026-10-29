/- Literal bounded measurable tests with oscillation sSup(range q)-sInf(range q).
The factory constant is selected before every test and all particle numbers;
no uniform bound on the amplitude or a preselected bounding interval is needed. -/
import DGRHS.Dynamics.SourceLogDynamicEmpirical
import Mathlib.Order.ConditionallyCompleteLattice.Basic
noncomputable section
open MeasureTheory InformationTheory
open scoped BigOperators NNReal ENNReal
namespace DGRHS.Dynamics
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy DGRHS.Commutator
variable {ι : Type*} [Fintype ι]
theorem exists_sourceLog_dynamic_oscillation_absolute_bound
    (β : ℝ≥0) (hβ : 0<(β:ℝ)) (hd : 0<(Fintype.card ι:ℝ))
    (J H L C₂ : ℝ) (hL : 0≤L) :
    ∃ D : ℝ,0≤D ∧ ∀ (ρ : EuclideanSpace ℝ ι→ℝ) (M : ℝ),0≤M →
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume,ρ x≤M) →
      Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) →
      -J≤DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun x y=>logPhysicalPair (x,y)) →
      ∀ (N : ℕ),1≤N →
      (sourceLogSingularPartition (⟨2*(β:ℝ),by positivity⟩:ℝ≥0) ρ N).toReal≤C₂ →
      ∀ (q : EuclideanSpace ℝ ι→ℝ),Measurable q →
      BddBelow (Set.range q) → BddAbove (Set.range q) →
      sSup (Set.range q)-sInf (Set.range q)≤L →
      ∀ (ν : Measure (Fin N→EuclideanSpace ℝ ι)),∀ [IsProbabilityMeasure ν],
      klDiv ν (sourceLogSingularGibbs β ρ N)≠∞ →
      (klDiv ν (sourceLogSingularGibbs β ρ N)).toReal≤H →
      let μ := gaussianRieszDensityMeasure ρ
      let E := fun x : Fin N→EuclideanSpace ℝ ι=>(∫ y,q y ∂transportEmpiricalLaw N x)-(∫ y,q y ∂μ)
      Integrable q μ ∧ (∀ x,Integrable q (transportEmpiricalLaw N x)) ∧
      Integrable E ν ∧ (∫ x,|E x| ∂ν)≤D/Real.sqrt N := by
  obtain ⟨D,hD,hbound⟩ := exists_sourceLog_dynamic_empirical_absolute_bound β hβ hd J H L C₂ hL
  refine ⟨D,hD,?_⟩
  intro ρ M hM hμ hρ hpair hI N hN hC₂ q hq hlo hup hosc ν hν hKL hH
  have hqbound : ∀ x,q x∈Set.Icc (sInf (Set.range q)) (sSup (Set.range q)) :=
    fun x=>subset_Icc_csInf_csSup hlo hup (Set.mem_range_self x)
  have hwidth : ‖sSup (Set.range q)-sInf (Set.range q)‖≤L := by
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr
      (csInf_le_csSup (Set.range_nonempty q) hlo hup))]
    exact hosc
  exact hbound ρ M hM hρ hpair hI N hN hC₂ q hq _ _ hqbound hwidth ν hKL hH
end DGRHS.Dynamics
#check @DGRHS.Dynamics.exists_sourceLog_dynamic_oscillation_absolute_bound
#print axioms DGRHS.Dynamics.exists_sourceLog_dynamic_oscillation_absolute_bound
