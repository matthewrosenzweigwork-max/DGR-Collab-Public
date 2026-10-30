import DGPS.Examples.ThreeSpeciesCircle.NearestRootMomentError
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryReferenceLocalStability

/-! Genuine zero-distance assignments identify every ORIGINAL species law.
Positive weights suffice individually; no uniform lower bound is used. -/

noncomputable section
open MeasureTheory Filter
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Zero Haar square-root distance identifies the actual probability law. -/
theorem rootDistanceSq_zero_measure (ρ σ : AbsoluteDensity 1) (hz : rootDistanceSq ρ σ = 0) :
    (densityMeasure ρ : Measure (Torus 1)) = densityMeasure σ := by
  have hi : Integrable (fun x => (ρ.sqrt x - σ.sqrt x) ^ 2) (haar 1) :=
    (ρ.memLp_sqrt.sub σ.memLp_sqrt).integrable_sq
  have he : (fun x => (ρ.sqrt x - σ.sqrt x) ^ 2) =ᵐ[haar 1] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hi).mp hz
  apply (densityMeasure_eq_iff_STR02901 ρ σ).2
  filter_upwards [he] with x hx
  change (ρ.sqrt x - σ.sqrt x) ^ 2 = 0 at hx
  have hs : ρ.sqrt x = σ.sqrt x := sub_eq_zero.mp (sq_eq_zero_iff.mp hx)
  change ρ.sqrt x ^ 2 = σ.sqrt x ^ 2
  rw [hs]

/-- An assignment of zero nonreference mass has every label equal to zero. -/
theorem nonreferenceRootWeight_zero_labels (F : SpeciesFamily 1)
    (label : Fin F.count → Fin 4) (hu : nonreferenceRootWeight F label = 0) :
    ∀ s, label s = 0 := by
  classical
  intro s
  by_contra hn
  have hm : (if label s = 0 then 0 else F.weight s) ≤ nonreferenceRootWeight F label := by
    apply Finset.single_le_sum _ (Finset.mem_univ s)
    intro i hi
    split_ifs
    · exact le_rfl
    · exact F.weight_nonneg i
  rw [if_neg hn, hu] at hm
  exact (not_le_of_gt (F.weight_pos s)) hm

/-- A zero weighted budget identifies each original law with its assigned law. -/
theorem rootDistanceBudget_zero_measures (F : SpeciesFamily 1) (R : Fin 4 → AbsoluteDensity 1)
    (label : Fin F.count → Fin 4) (hbudget : rootDistanceBudget F R label = 0) :
    ∀ s, (densityMeasure (F.density s) : Measure (Torus 1)) = densityMeasure (R (label s)) := by
  intro s
  apply rootDistanceSq_zero_measure
  have hm : F.weight s * rootDistanceSq (F.density s) (R (label s)) ≤ rootDistanceBudget F R label :=
    Finset.single_le_sum
      (f := fun i => F.weight i * rootDistanceSq (F.density i) (R (label i)))
      (fun i _ => mul_nonneg (F.weight_nonneg i)
        (rootDistanceSq_nonneg (F.density i) (R (label i))))
      (Finset.mem_univ s)
  rw [hbudget] at hm
  apply le_antisymm _ (rootDistanceSq_nonneg _ _)
  by_contra hn
  have hp := mul_pos (F.weight_pos s) (lt_of_not_ge hn)
  linarith

/-- At the actual interacting minimizer, a family whose every original law
is the reference has exactly zero actual gap. -/
theorem elementaryModel_gap_zero_of_species_reference {h ε : ℝ} (hh : 0 < h)
    (hε : 0 < ε) (hεmax : ε < epsMax h) (F : SpeciesFamily 1)
    (hμ : ∀ s, (densityMeasure (F.density s) : Measure (Torus 1)) = threefoldReference h) :
    speciesGap (modelData h ε) F = 0 := by
  letI : IsProbabilityMeasure (threefoldReference h) :=
    (threefoldReference_integral_properties hh).2.2.2.2.1
  have hE (s : Fin F.count) : ordinaryEntropy h (F.density s) = 0 := by
    unfold ordinaryEntropy
    rw [hμ s]
    exact relativeEntropy_self _
  have hm (i : Fin 6) : (∫ x, elementarySixObservable h i x
      ∂(densityMeasure (barycenter F) : Measure (Torus 1))) = 0 := by
    rw [Structural.budget_integral_barycenter F (continuous_elementarySixObservable h i)]
    apply Finset.sum_eq_zero
    intro s hs
    rw [hμ s, elementarySixObservable_reference_zero hh i, mul_zero]
  have hC : momC h (densityMeasure (barycenter F)) = 0 := hm 0
  have hS : momS h (densityMeasure (barycenter F)) = 0 := hm 1
  have hB : momB h (densityMeasure (barycenter F)) = 0 := hm 2
  have hQ : elementaryQ h (densityMeasure (barycenter F)) = 0 := by
    rw [elementaryQ_moments, hC, hS, hB]
    ring
  have hgap := elementaryModel_speciesGap_expansion hh hε hεmax F
  simp only [hE, ENNReal.toReal_zero, mul_zero, Finset.sum_const_zero, hQ, add_zero] at hgap
  exact_mod_cast hgap

/-- The actual zero-deficit/zero-nonreference endpoint is excluded by positive
family gap, through true law identification rather than representative equality. -/
theorem ordinaryAssignment_zero_gap {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (F : SpeciesFamily 1) (R : Fin 4 → AbsoluteDensity 1)
    (label : Fin F.count → Fin 4)
    (hR : (densityMeasure (R 0) : Measure (Torus 1)) = threefoldReference h)
    (hbudget : rootDistanceBudget F R label = 0) (hu : nonreferenceRootWeight F label = 0) :
    speciesGap (modelData h ε) F = 0 := by
  apply elementaryModel_gap_zero_of_species_reference hh hε hεmax F
  intro s
  have he := rootDistanceBudget_zero_measures F R label hbudget s
  rw [nonreferenceRootWeight_zero_labels F label hu s] at he
  exact he.trans hR

end DGPS.Examples.ThreeSpeciesCircle
