import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootBinaryMargin

/-! An absolute correction bound at the actual assigned roots. The constant
is selected from the fixed root moments before the family and its assignment;
no asymptotic coefficient bound is a premise. -/

noncomputable section
open MeasureTheory
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Nonnegative orbit weights have resultant length at most their total mass. -/
theorem threefoldResultant_normSq_le_mass (p : Fin 3 → ℝ) (hp : ∀ j, 0 ≤ p j) :
    Complex.normSq (threefoldResultant p) ≤ threefoldMass p ^ 2 := by
  rw [threefoldResultant_normSq]
  unfold threefoldMass
  rw [Fin.sum_univ_three]
  nlinarith [mul_nonneg (hp 0) (hp 1), mul_nonneg (hp 0) (hp 2),
    mul_nonneg (hp 1) (hp 2)]

/-- The absolute polynomial bound uses the actual two finite coefficients. -/
theorem threefoldQuadratic_abs_le (α β : ℝ) (p : Fin 3 → ℝ) (hp : ∀ j, 0 ≤ p j) :
    |threefoldQuadratic α β p| ≤ (|α| + |β| + 1) * threefoldMass p ^ 2 := by
  have hz := threefoldResultant_normSq_le_mass p hp
  have hn : 0 ≤ Complex.normSq (threefoldResultant p) := Complex.normSq_nonneg _
  have hm : 0 ≤ threefoldMass p ^ 2 := sq_nonneg _
  calc
    |threefoldQuadratic α β p| ≤
        |β| * Complex.normSq (threefoldResultant p) + |α| * threefoldMass p ^ 2 := by
      have ht := abs_sub (β * Complex.normSq (threefoldResultant p)) (α * threefoldMass p ^ 2)
      rw [abs_mul, abs_mul, abs_of_nonneg hn, abs_of_nonneg hm] at ht
      exact ht
    _ ≤ |β| * threefoldMass p ^ 2 + |α| * threefoldMass p ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hz (abs_nonneg β)) le_rfl
    _ ≤ (|α| + |β| + 1) * threefoldMass p ^ 2 := by nlinarith

/-- For the SAME actual chart roots, a positive finite constant works for every
finite family and every assignment, without a root-moment-sign premise. -/
theorem ordinaryAssignedRoot_C_abs_bound (D : OrdinaryRootGraphData) {h : ℝ} (hh : 0 < h)
    (hhr : h ∈ Set.Ioo (-D.radius) D.radius) (σ : Fin 3 → AbsoluteDensity 1)
    (hσ : ∀ j θ, (σ j).density (angEquiv.symm θ) =
      rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ))
    (a : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (F : SpeciesFamily 1) (label : Fin F.count → Fin 4),
      |elementaryC h a (barycenter
        (assignedRootFamily F (Fin.cases (ordinaryReferenceAbsolute h) σ) label))| ≤
          K * nonreferenceRootWeight F label ^ 2 := by
  refine ⟨|ordinaryRootCorrectionAlpha h a σ| + |ordinaryRootCorrectionBeta h a σ| + 1,
    by positivity, ?_⟩
  intro F label
  have he := elementaryC_assigned_ordinary_roots D hh hhr σ hσ a F label
  change elementaryC h a (barycenter
    (assignedRootFamily F (Fin.cases (ordinaryReferenceAbsolute h) σ) label)) =
    threefoldQuadratic (ordinaryRootCorrectionAlpha h a σ)
      (ordinaryRootCorrectionBeta h a σ) (assignedOrbitWeights F label) at he
  rw [he]
  have hb := threefoldQuadratic_abs_le (ordinaryRootCorrectionAlpha h a σ)
    (ordinaryRootCorrectionBeta h a σ) (assignedOrbitWeights F label)
    (assignedOrbitWeights_nonneg F label)
  rw [assignedOrbitWeights_mass] at hb
  exact hb

end DGPS.Examples.ThreeSpeciesCircle
