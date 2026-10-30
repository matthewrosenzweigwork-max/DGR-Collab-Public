import DGPS.Structural.FrozenGibbsIdentities

/-! Sharp density-ratio witnesses for frozen Gibbs probabilities.
The endpoints are the actual infimum and supremum, so the ratio loss is exp(M),
not the exp(2M) obtained by dividing the coarse two-sided bounds. -/

open MeasureTheory Set

namespace DGPS.Structural

/-- Every frozen Gibbs law admits positive lower/upper density bounds whose
ratio is at most exp(totalOscillation). All Borel input probabilities are allowed. -/
theorem frozenGibbs_sharp_density_bounds {d : ℕ} (A : InteractionData d)
    (hLip : LipschitzData A) (ν : ProbabilityMeasure (Torus d)) :
    ∃ c C : ℝ, 0 < c ∧
      (∀ x, c ≤ (frozenGibbs A ν).density x) ∧
      (∀ x, (frozenGibbs A ν).density x ≤ C) ∧
      C ≤ Real.exp (totalOscillation A) * c := by
  obtain ⟨hbd, hratio, -⟩ := frozenGibbs_uniform_bounds A hLip
  have hne : (Set.range (frozenGibbs A ν).density).Nonempty := Set.range_nonempty _
  have hlo : BddBelow (Set.range (frozenGibbs A ν).density) := by
    refine ⟨Real.exp (-totalOscillation A), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (hbd ν x).1
  have hup : BddAbove (Set.range (frozenGibbs A ν).density) := by
    refine ⟨Real.exp (totalOscillation A), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (hbd ν x).2
  refine ⟨sInf (Set.range (frozenGibbs A ν).density),
    sSup (Set.range (frozenGibbs A ν).density), ?_, ?_, ?_, hratio ν⟩
  · refine (Real.exp_pos (-totalOscillation A)).trans_le (le_csInf hne ?_)
    rintro _ ⟨x, rfl⟩
    exact (hbd ν x).1
  · intro x
    exact csInf_le hlo (Set.mem_range_self x)
  · intro x
    exact le_csSup hup (Set.mem_range_self x)

end DGPS.Structural
