import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootMixtureCorrection

/-! Exact finite-family binary geometry and the scalar absorption calculation.
The coefficient bounds below concern the actual six root moments; their
analytic discharge is intentionally left to the owning moment-limit producer. -/

noncomputable section
open MeasureTheory
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The actual root-zero invariant coefficient, with physical normalization. -/
def ordinaryRootCorrectionAlpha (h a : ℝ) (σ : Fin 3 → AbsoluteDensity 1) : ℝ :=
  threefoldAlpha a (momB h (densityMeasure (σ 0)))
    (∫ x, elementaryFeatureGenerator h (featureB h) x ∂(densityMeasure (σ 0) : Measure (Torus 1)))

/-- The two genuine native vectors enter independently. -/
def ordinaryRootCorrectionBeta (h a : ℝ) (σ : Fin 3 → AbsoluteDensity 1) : ℝ :=
  threefoldBeta a ⟨momC h (densityMeasure (σ 0)), momS h (densityMeasure (σ 0))⟩
    ⟨∫ x, elementaryFeatureGenerator h (featureC h) x ∂(densityMeasure (σ 0) : Measure (Torus 1)),
      ∫ x, elementaryFeatureGenerator h (featureS h) x ∂(densityMeasure (σ 0) : Measure (Torus 1))⟩

/-- Grouping an arbitrary assignment cannot increase its original species count. -/
theorem assignedOrbitWeights_support_card_le (F : SpeciesFamily 1)
    (label : Fin F.count → Fin 4) :
    (Finset.univ.filter fun j => assignedOrbitWeights F label j ≠ 0).card ≤ (F.count : ℕ) := by
  classical
  let S := Finset.univ.filter fun j => assignedOrbitWeights F label j ≠ 0
  have hsub : S.image Fin.succ ⊆ Finset.univ.image label := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have hnon : assignedOrbitWeights F label j ≠ 0 := (Finset.mem_filter.mp hj).2
    by_contra hn
    apply hnon
    unfold assignedOrbitWeights
    apply Finset.sum_eq_zero
    intro s hs
    have he : label s ≠ j.succ := by
      intro he
      exact hn (Finset.mem_image.mpr ⟨s, Finset.mem_univ s, he⟩)
    rw [if_neg he]
  calc S.card = (S.image Fin.succ).card :=
      (Finset.card_image_of_injective S (Fin.succ_injective 3)).symm
    _ ≤ (Finset.univ.image label).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin F.count)).card := Finset.card_image_le
    _ = (F.count : ℕ) := by simp

/-- The actual assigned-root correction has a binary margin once its actual
moment coefficients satisfy the stated factual bounds. No rate bound is a premise. -/
theorem elementaryC_assigned_binary_margin (D : OrdinaryRootGraphData) {h : ℝ} (hh : 0 < h)
    (hhr : h ∈ Set.Ioo (-D.radius) D.radius) (σ : Fin 3 → AbsoluteDensity 1)
    (hσ : ∀ j θ, (σ j).density (angEquiv.symm θ) =
      rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ))
    (a : ℝ) (hβ : 7 ≤ ordinaryRootCorrectionBeta h a σ)
    (hα : ordinaryRootCorrectionAlpha h a σ ≤ 5 / 4)
    (F : SpeciesFamily 1) (hcount : (F.count : ℕ) ≤ 2) (label : Fin F.count → Fin 4) :
    nonreferenceRootWeight F label ^ 2 / 2 ≤
      elementaryC h a (barycenter
        (assignedRootFamily F (Fin.cases (ordinaryReferenceAbsolute h) σ) label)) := by
  have he := elementaryC_assigned_ordinary_roots D hh hhr σ hσ a F label
  change elementaryC h a (barycenter
    (assignedRootFamily F (Fin.cases (ordinaryReferenceAbsolute h) σ) label)) =
    threefoldQuadratic (ordinaryRootCorrectionAlpha h a σ)
      (ordinaryRootCorrectionBeta h a σ) (assignedOrbitWeights F label) at he
  rw [he]
  have hgeom := threefoldQuadratic_binary_card_lower hβ hα (assignedOrbitWeights F label)
    ((assignedOrbitWeights_support_card_le F label).trans hcount)
  rw [assignedOrbitWeights_mass] at hgeom
  exact hgeom

/-- Young absorption with exact constants: the mixed nearest-root error does
not consume the binary quadratic margin at sufficiently small coupling. -/
theorem binary_deficit_absorption {D0 u K ε C J : ℝ}
    (hD : 0 ≤ D0) (hu : 0 ≤ u) (hK : 0 ≤ K) (hε : 0 ≤ ε) (hJ : 0 ≤ J)
    (hεK : ε * K ≤ 1 / 4) (hεK2 : ε * K ^ 2 ≤ 1 / 4)
    (hC : u ^ 2 / 2 - K * (u * Real.sqrt D0 + D0) ≤ C) :
    D0 / 2 + ε * u ^ 2 / 4 ≤ D0 + ε * C + ε ^ 2 * J := by
  have hs : Real.sqrt D0 ^ 2 = D0 := Real.sq_sqrt hD
  have hYoung : ε * K * u * Real.sqrt D0 ≤ D0 / 4 + ε ^ 2 * K ^ 2 * u ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt D0 / 2 - ε * K * u)]
  have hCε := mul_le_mul_of_nonneg_left hC hε
  have hKD := mul_le_mul_of_nonneg_right hεK hD
  have hKu := mul_le_mul_of_nonneg_right hεK2 (sq_nonneg u)
  have hKuε := mul_le_mul_of_nonneg_left hKu hε
  have hJε := mul_nonneg (sq_nonneg ε) hJ
  nlinarith

end DGPS.Examples.ThreeSpeciesCircle
