import DGRHS.Commutator.SourceRieszDynamicLinearEmpirical
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! Actual bounded raw test range supplies its interval; only oscillation enters
common constants. Every reference and finite empirical q integral is proper. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem sourceRieszDynamic_common_oscillation (s β M H L : ℝ) (hs : 0<s)
    (hβ : 0<β) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (hL : 0≤L) :
    ∃ D : ℝ,0≤D ∧ ∀ (ρ : E→ℝ),
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume,ρ x≤M) → ∀ N : ℕ,1≤N →
      ∀ (q : E→ℝ),Measurable q → BddBelow (Set.range q) → BddAbove (Set.range q) →
      sSup (Set.range q)-sInf (Set.range q)≤L →
      ∀ (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν],
      klDiv ν (sourceRieszSingularGibbs s β ρ N)≠∞ →
      (klDiv ν (sourceRieszSingularGibbs s β ρ N)).toReal≤H →
      Integrable q (gaussianRieszDensityMeasure ρ) ∧
      (∀ ω,Integrable q (sourceRieszLocalEmpiricalLaw N ω)) ∧
      Integrable (sourceRieszDynamicRawFluctuation ρ q N) ν ∧
      Integrable (sourceRieszDynamicEmpiricalDifference ρ q N) ν ∧
      (∫ ω,|sourceRieszDynamicEmpiricalDifference ρ q N ω| ∂ν)≤D/Real.sqrt N := by
  obtain ⟨D,hD,hbound⟩ := sourceRieszDynamicLinear_common_empirical (ι:=ι) s β M H L hs hβ hd hM hL
  refine ⟨D,hD,?_⟩
  intro ρ hμ hρ N hN q hq hlo hup hosc ν hν hKL hH
  have hqb : ∀ x,q x∈Set.Icc (sInf (Set.range q)) (sSup (Set.range q)) :=
    fun x=>subset_Icc_csInf_csSup hlo hup (Set.mem_range_self x)
  have hwidth : ‖sSup (Set.range q)-sInf (Set.range q)‖≤L := by
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr
      (csInf_le_csSup (Set.range_nonempty q) hlo hup))]
    exact hosc
  have hab : ∀ x,|q x|≤max |sInf (Set.range q)| |sSup (Set.range q)| := by
    intro x
    rw [abs_le]
    constructor
    · have := (hqb x).1
      have := le_max_left |sInf (Set.range q)| |sSup (Set.range q)|
      have := neg_abs_le (sInf (Set.range q))
      linarith
    · exact ((hqb x).2.trans (le_abs_self _)).trans (le_max_right _ _)
  have hiq : Integrable q (gaussianRieszDensityMeasure ρ) :=
    (integrable_const (max |sInf (Set.range q)| |sSup (Set.range q)|)).mono' hq.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x=>by simpa only [Real.norm_eq_abs] using hab x)
  exact ⟨hiq,fun ω=>integrable_sourceRieszLocalEmpiricalLaw N ω q,
    hbound ρ hρ N hN q hq _ _ hqb hwidth ν hKL hH⟩

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszDynamic_common_oscillation
#print axioms DGRHS.Commutator.sourceRieszDynamic_common_oscillation
