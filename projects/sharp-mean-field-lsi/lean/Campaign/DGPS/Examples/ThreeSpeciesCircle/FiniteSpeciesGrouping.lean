import DGPS.Structural.SmallRateCircle

/-! Grouping an original finite family into three positive label classes.
Every grouped density is an original representative. There is no weight floor
and no optimizer or classification hypothesis. -/

noncomputable section
open MeasureTheory

namespace DGPS.Examples.ThreeSpeciesCircle

def finiteSpeciesGroupWeight (F : SpeciesFamily 1) (label : Fin F.count → Fin 3)
    (j : Fin 3) : ℝ := ∑ s, if label s = j then F.weight s else 0

theorem finiteSpeciesGroupWeight_sum (F : SpeciesFamily 1) (label : Fin F.count → Fin 3) :
    ∑ j, finiteSpeciesGroupWeight F label j = 1 := by
  classical
  calc
    (∑ j, finiteSpeciesGroupWeight F label j) =
        ∑ s, ∑ j : Fin 3, if label s = j then F.weight s else 0 := by
      exact Finset.sum_comm
    _ = ∑ s, F.weight s := by
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = 1 := F.weight_sum

theorem finiteSpeciesGroup_nonempty (F : SpeciesFamily 1) (label : Fin F.count → Fin 3)
    (hp : ∀ j, 0 < finiteSpeciesGroupWeight F label j) (j : Fin 3) :
    ∃ s : Fin F.count, label s = j := by
  classical
  by_contra hn
  have he : ∀ s, label s ≠ j := fun s hs => hn ⟨s, hs⟩
  have hz : finiteSpeciesGroupWeight F label j = 0 := by
    simp only [finiteSpeciesGroupWeight, if_neg (he _), Finset.sum_const_zero]
  have := hp j
  linarith

def finiteSpeciesGroupRepresentative (F : SpeciesFamily 1) (label : Fin F.count → Fin 3)
    (hp : ∀ j, 0 < finiteSpeciesGroupWeight F label j) (j : Fin 3) : Fin F.count :=
  Classical.choose (finiteSpeciesGroup_nonempty F label hp j)

theorem finiteSpeciesGroupRepresentative_label (F : SpeciesFamily 1)
    (label : Fin F.count → Fin 3) (hp : ∀ j, 0 < finiteSpeciesGroupWeight F label j)
    (j : Fin 3) : label (finiteSpeciesGroupRepresentative F label hp j) = j :=
  Classical.choose_spec (finiteSpeciesGroup_nonempty F label hp j)

/-- A genuine three-species family with the original group masses and one
original density from each positive-mass label class. -/
def finiteSpeciesGroup3 (F : SpeciesFamily 1) (label : Fin F.count → Fin 3)
    (hp : ∀ j, 0 < finiteSpeciesGroupWeight F label j) : SpeciesFamily 1 where
  count := 3
  weight := finiteSpeciesGroupWeight F label
  weight_pos := hp
  weight_sum := finiteSpeciesGroupWeight_sum F label
  density := fun j => F.density (finiteSpeciesGroupRepresentative F label hp j)

@[simp] theorem finiteSpeciesGroup3_count (F : SpeciesFamily 1)
    (label : Fin F.count → Fin 3) (hp : ∀ j, 0 < finiteSpeciesGroupWeight F label j) :
    (finiteSpeciesGroup3 F label hp).count = 3 := rfl

theorem finiteSpeciesGroup3_weight (F : SpeciesFamily 1)
    (label : Fin F.count → Fin 3) (hp : ∀ j, 0 < finiteSpeciesGroupWeight F label j)
    (j : Fin 3) : (finiteSpeciesGroup3 F label hp).weight j =
      finiteSpeciesGroupWeight F label j := rfl

theorem finiteSpeciesGroup3_density (F : SpeciesFamily 1)
    (label : Fin F.count → Fin 3) (hp : ∀ j, 0 < finiteSpeciesGroupWeight F label j)
    (j : Fin 3) : (finiteSpeciesGroup3 F label hp).density j =
      F.density (finiteSpeciesGroupRepresentative F label hp j) := rfl

/-- Arbitrary real statistics depending only on the original probability law
are preserved by grouping. No integrability or variational premise is needed. -/
theorem finiteSpeciesGroup3_statistic (F : SpeciesFamily 1)
    (label : Fin F.count → Fin 3) (hp : ∀ j, 0 < finiteSpeciesGroupWeight F label j)
    (hsame : ∀ s t, label s = label t → densityMeasure (F.density s) = densityMeasure (F.density t))
    (L : AbsoluteDensity 1 → ℝ)
    (hL : ∀ ρ σ, densityMeasure ρ = densityMeasure σ → L ρ = L σ) :
    (∑ j : Fin 3, (finiteSpeciesGroup3 F label hp).weight j *
      L ((finiteSpeciesGroup3 F label hp).density j)) =
        ∑ s, F.weight s * L (F.density s) := by
  classical
  change (∑ j : Fin 3, finiteSpeciesGroupWeight F label j *
    L (F.density (finiteSpeciesGroupRepresentative F label hp j))) = _
  simp only [finiteSpeciesGroupWeight, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hL _ _ (hsame _ _ (finiteSpeciesGroupRepresentative_label F label hp (label s)))]

/-- Every continuous moment of the actual barycenter probability law is
preserved. The representative choice changes neither weights nor laws. -/
theorem finiteSpeciesGroup3_barycenter_moment (F : SpeciesFamily 1)
    (label : Fin F.count → Fin 3) (hp : ∀ j, 0 < finiteSpeciesGroupWeight F label j)
    (hsame : ∀ s t, label s = label t → densityMeasure (F.density s) = densityMeasure (F.density t))
    (g : Torus 1 → ℝ) (hg : Continuous g) :
    (∫ x, g x ∂(densityMeasure (barycenter (finiteSpeciesGroup3 F label hp)) :
      Measure (Torus 1))) = ∫ x, g x ∂(densityMeasure (barycenter F) : Measure (Torus 1)) := by
  rw [Structural.budget_integral_barycenter (finiteSpeciesGroup3 F label hp) hg,
    Structural.budget_integral_barycenter F hg]
  exact finiteSpeciesGroup3_statistic F label hp hsame
    (fun ρ => ∫ x, g x ∂(densityMeasure ρ : Measure (Torus 1)))
    (fun ρ σ hρσ => by rw [hρσ])

end DGPS.Examples.ThreeSpeciesCircle
