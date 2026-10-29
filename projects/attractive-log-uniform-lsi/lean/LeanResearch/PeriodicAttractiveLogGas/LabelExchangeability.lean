import LeanResearch.PeriodicAttractiveLogGas.CellRestrictions
import LeanResearch.PeriodicAttractiveLogGas.LabelOccupations
import LeanResearch.PeriodicAttractiveLogGas.TorusPatchDensity
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Nat.Choose.Multinomial

/-! Particle relabeling of the actual Green ensemble, and the distinction
between the mass of one labeling and its occupation event. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace PeriodicAttractiveLogGas.LabelExchangeability

open MeshCells CellRestrictions LabelOccupations

def permute {N : ℕ} (σ : Equiv.Perm (Fin N)) (X : Configuration N) : Configuration N := X ∘ σ

theorem two_pairEnergy {g : Torus → ℝ} (hg : ∀ z, g (-z) = g z)
    (N : ℕ) (X : Configuration N) :
    2 * pairEnergy g N X = ∑ i : Fin N, ∑ j : Fin N, if i ≠ j then g (X i - X j) else 0 := by
  classical
  have hp : pairEnergy g N X =
      ∑ i : Fin N, ∑ j : Fin N, if i < j then g (X i - X j) else 0 := by
    unfold pairEnergy
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  have hs (i j : Fin N) :
      (if i ≠ j then g (X i - X j) else 0) =
        (if i < j then g (X i - X j) else 0) +
          (if j < i then g (X i - X j) else 0) := by
    rcases lt_trichotomy i j with h | h | h <;> simp [h, ne_of_lt, ne_of_gt, not_lt_of_ge, le_of_lt]
  have hsym (i j : Fin N) : g (X j - X i) = g (X i - X j) := by
    rw [← neg_sub, hg]
  simp_rw [hs, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin N ↦ if j < i then g (X i - X j) else 0)]
  simp_rw [hsym]
  rw [← hp]
  ring

theorem pairEnergy_permute {g : Torus → ℝ} (hg : ∀ z, g (-z) = g z)
    {N : ℕ} (σ : Equiv.Perm (Fin N)) (X : Configuration N) :
    pairEnergy g N (permute σ X) = pairEnergy g N X := by
  have h : 2 * pairEnergy g N (permute σ X) = 2 * pairEnergy g N X := by
    rw [two_pairEnergy hg, two_pairEnergy hg]
    calc
      _ = ∑ i : Fin N, ∑ j : Fin N,
          if σ i ≠ σ j then g (X (σ i) - X (σ j)) else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            by_cases hij : i = j
            · subst j
              simp
            · have hσ : σ i ≠ σ j := fun h ↦ hij (σ.injective h)
              simp [permute, hij, hσ]
      _ = _ := by
        rw [← Equiv.sum_comp σ (fun i ↦ ∑ j : Fin N, if i ≠ j then g (X i - X j) else 0)]
        apply Finset.sum_congr rfl
        intro i _
        exact Equiv.sum_comp σ (fun j ↦ if σ i ≠ j then g (X (σ i) - X j) else 0)
  linarith

theorem gibbsWeight_permute {g : Torus → ℝ} (hg : ∀ z, g (-z) = g z)
    {N : ℕ} (σ : Equiv.Perm (Fin N)) (β : ℝ) (X : Configuration N) :
    gibbsWeight g N β (permute σ X) = gibbsWeight g N β X := by
  simp only [gibbsWeight, pairEnergy_permute hg]

theorem measurePreserving_permute {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (permute σ) (referenceMeasure N) (referenceMeasure N) := by
  simpa [permute, referenceMeasure, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    Equiv.piCongrLeft', Function.comp_def] using!
    (measurePreserving_piCongrLeft (fun _ : Fin N ↦ torusMeasure) σ.symm)

theorem measurePreserving_gibbs_permute {g : Torus → ℝ} (hgm : Measurable g)
    (hge : ∀ z, g (-z) = g z) {N : ℕ} (σ : Equiv.Perm (Fin N)) (β : ℝ) :
    MeasurePreserving (permute σ) (gibbsMeasure g N β) (gibbsMeasure g N β) := by
  have h := TorusPatchDensity.measurePreserving_withDensity (measurePreserving_permute σ)
    (measurable_gibbsWeight hgm N β).aemeasurable
  simp only [gibbsWeight_permute hge] at h
  refine ⟨h.measurable, ?_⟩
  rw [gibbsMeasure, Measure.map_smul, h.map_eq]
  exact h.aemeasurable

theorem measurePreserving_greenGibbs_permute {N : ℕ} (σ : Equiv.Perm (Fin N)) (β : ℝ) :
    MeasurePreserving (permute σ) (gibbsMeasure greenRealRepresentative N β)
      (gibbsMeasure greenRealRepresentative N β) := by
  rw [← regularGreen_gibbsMeasure_eq]
  exact measurePreserving_gibbs_permute regularGreenRepresentative_measurable
    regularGreenRepresentative_even σ β

theorem labelFiber_permute_preimage {N J : ℕ} (hJ : 0 < J)
    (σ : Equiv.Perm (Fin N)) (η : LabelVector J N) :
    permute σ ⁻¹' labelFiber hJ (η ∘ σ) = labelFiber hJ η := by
  ext X
  simp only [Set.mem_preimage, mem_labelFiber, permute, Function.comp_apply]
  constructor
  · intro h i
    obtain ⟨j, rfl⟩ := σ.surjective i
    exact h j
  · intro h i
    exact h (σ i)

theorem labelProbability_permute {N J : ℕ} (hJ : 0 < J)
    (σ : Equiv.Perm (Fin N)) (η : LabelVector J N) (β : ℝ) :
    labelProbability hJ (η ∘ σ) β = labelProbability hJ η β := by
  have h := (measurePreserving_greenGibbs_permute σ β).measure_preimage
    (measurableSet_labelFiber hJ (η ∘ σ)).nullMeasurableSet
  rw [labelFiber_permute_preimage] at h
  exact h.symm

theorem occupation_permute {N J : ℕ} (σ : Equiv.Perm (Fin N)) (η : LabelVector J N) :
    occupation (η ∘ σ) = occupation η := by
  classical
  funext a
  have h := Equiv.sum_comp σ (fun i ↦ if η i = a then (1 : ℕ) else 0)
  simpa only [occupation, Finset.card_eq_sum_ones, Finset.sum_filter, Function.comp_apply] using h

theorem exists_permutation_of_occupation_eq {N J : ℕ} {η ζ : LabelVector J N}
    (h : occupation η = occupation ζ) : ∃ σ : Equiv.Perm (Fin N), η ∘ σ = ζ := by
  classical
  have hc (a : MeshIndex J) : Fintype.card {i : Fin N // ζ i = a} =
      Fintype.card {i : Fin N // η i = a} := by
    simpa [Fintype.card_subtype, occupation] using (congrFun h a).symm
  let e (a : MeshIndex J) := Fintype.equivOfCardEq (hc a)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext i
  exact Equiv.ofFiberEquiv_map e i

theorem labelProbability_eq_of_occupation_eq {N J : ℕ} (hJ : 0 < J)
    {η ζ : LabelVector J N} (h : occupation η = occupation ζ) (β : ℝ) :
    labelProbability hJ η β = labelProbability hJ ζ β := by
  obtain ⟨σ, rfl⟩ := exists_permutation_of_occupation_eq h
  exact (labelProbability_permute hJ σ η β).symm

end PeriodicAttractiveLogGas.LabelExchangeability
