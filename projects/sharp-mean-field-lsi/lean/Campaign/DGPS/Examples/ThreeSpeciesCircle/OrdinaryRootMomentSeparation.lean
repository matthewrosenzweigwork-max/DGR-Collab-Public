import DGPS.Examples.ThreeSpeciesCircle.OrdinarySignedRootMomentBound

/-! Separation of the actual SAME-graph ordinary root moment vectors.
The vectors contain all six original native observables, including the genuine
generator observables. No profile, minimizer or classification premise enters. -/

noncomputable section
open MeasureTheory
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The six original native moments, with the usual finite Pi supremum norm. -/
def ordinaryRootSixMomentVector (h : ℝ) (ρ : AbsoluteDensity 1) : Fin 6 → ℝ :=
  fun i => ∫ x, elementarySixObservable h i x ∂(densityMeasure ρ : Measure (Torus 1))

private def pairCharge (j k : Fin 3) (l : Fin 3) : ℝ :=
  (if l = j then 1 else 0) - if l = k then 1 else 0

private theorem pairCharge_eval (j k : Fin 3) (f : Fin 3 → ℝ) :
    (∑ l, pairCharge j k l * f l) = f j - f k := by
  classical
  simp [pairCharge, sub_mul, Finset.sum_sub_distrib, ite_mul]

private theorem pairCharge_sum (j k : Fin 3) : ∑ l, pairCharge j k l = 0 := by
  simpa only [mul_one, sub_self] using pairCharge_eval j k (fun _ => 1)

private theorem pairCharge_abs (j k : Fin 3) (hjk : j ≠ k) :
    ∑ l, |pairCharge j k l| = 2 := by
  classical
  have he (l : Fin 3) : |pairCharge j k l| =
      (if l = j then 1 else 0) + if l = k then 1 else 0 := by
    by_cases hlj : l = j
    · subst l
      simp [pairCharge, hjk]
    · by_cases hlk : l = k
      · subst l
        simp [pairCharge, hlj]
      · simp [pairCharge, hlj, hlk]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp
  norm_num

/-- A single field interval precedes all SAME-chart triples. Equality of two
six-moment vectors would contradict the actual signed-root lower bound. -/
theorem ordinaryRoot_six_moment_injective (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ σ : Fin 3 → AbsoluteDensity 1,
        (∀ j θ, (σ j).density (angEquiv.symm θ) =
          rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) →
        Function.Injective (fun j => ordinaryRootSixMomentVector h (σ j)) := by
  obtain ⟨δ, hδ, hδD, hlow⟩ := ordinarySignedRootMoment_lower D
  refine ⟨δ, hδ, hδD, fun h hh hhd σ hσ => ?_⟩
  intro j k he
  by_contra hjk
  let p := pairCharge j k
  have hp : ∑ l, p l = 0 := pairCharge_sum j k
  have habs : ∑ l, |p l| = 2 := pairCharge_abs j k hjk
  have hm (i : Fin 6) : ordinarySignedRootMoment h σ p i = 0 := by
    change (∑ l, pairCharge j k l * ordinaryRootSixMomentVector h (σ l) i) = 0
    rw [pairCharge_eval]
    exact sub_eq_zero.mpr (congrFun he i)
  have hQ : ordinarySignedRootQuadratic h 0 σ p = 0 := by
    unfold ordinarySignedRootQuadratic
    dsimp only
    rw [hm 0, hm 1, hm 2, hm 3, hm 4, hm 5] <;> ring
  have hl := hlow h hh hhd σ hσ 0 le_rfl ENNReal.toReal_nonneg p hp
  rw [habs, hQ] at hl
  norm_num at hl

/-- For every fixed positive small field and SAME-chart root triple, one
positive moment separation is chosen before all labels or competing profiles.
This theorem supplies no profile-to-root error or minimizer premise. -/
theorem ordinaryRoot_six_moment_separation (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ σ : Fin 3 → AbsoluteDensity 1,
        (∀ j θ, (σ j).density (angEquiv.symm θ) =
          rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) →
        ∃ η : ℝ, 0 < η ∧ ∀ j k : Fin 3, j ≠ k →
          η ≤ ‖ordinaryRootSixMomentVector h (σ j) -
            ordinaryRootSixMomentVector h (σ k)‖ := by
  obtain ⟨δ, hδ, hδD, hinj⟩ := ordinaryRoot_six_moment_injective D
  refine ⟨δ, hδ, hδD, fun h hh hhd σ hσ => ?_⟩
  let V := fun j => ordinaryRootSixMomentVector h (σ j)
  have hi : Function.Injective V := hinj h hh hhd σ hσ
  have hpos (j k : Fin 3) (hne : j ≠ k) : 0 < ‖V j - V k‖ := by
    apply norm_pos_iff.mpr
    intro hz
    exact hne (hi (sub_eq_zero.mp hz))
  let η := min ‖V 0 - V 1‖ (min ‖V 0 - V 2‖ ‖V 1 - V 2‖)
  have hη : 0 < η := lt_min (hpos 0 1 (by decide))
    (lt_min (hpos 0 2 (by decide)) (hpos 1 2 (by decide)))
  have h01 : η ≤ ‖V 0 - V 1‖ := min_le_left _ _
  have h02 : η ≤ ‖V 0 - V 2‖ := (min_le_right _ _).trans (min_le_left _ _)
  have h12 : η ≤ ‖V 1 - V 2‖ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η, hη, fun j k hjk => ?_⟩
  change η ≤ ‖V j - V k‖
  fin_cases j <;> fin_cases k
  · exact (hjk rfl).elim
  · exact h01
  · exact h02
  · exact h01.trans_eq (norm_sub_rev (V 0) (V 1))
  · exact (hjk rfl).elim
  · exact h12
  · exact h02.trans_eq (norm_sub_rev (V 0) (V 2))
  · exact h12.trans_eq (norm_sub_rev (V 1) (V 2))
  · exact (hjk rfl).elim

end DGPS.Examples.ThreeSpeciesCircle
