import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootNormComparison
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootPoincareGap

/-! Actual SAME-D local ordinary-deficit stability at all three ordinary roots. -/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Actual SAME-D three-root local stability. For each fixed h, both neighborhood and
coercivity constants are chosen before the root index and every original H1 competitor. -/
theorem ordinaryRoot_family_localStability (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ (σ : Fin 3 → AbsoluteDensity 1) (u : Fin 3 → Torus 1 → ℝ),
        (∀ j θ, (σ j).density (DGPS.Circle.AngularNormalization.angEquiv.symm θ) =
          rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h))
            (DGPS.Circle.AngularNormalization.angSec θ)) ∧
        (∀ j, 0 < ordinaryEntropy h (σ j)) ∧
        (∀ j, str025_quot h (σ j) = ordinaryLSRate (ordinaryReference h)) ∧
        (∀ j, Continuous (u j) ∧ (∀ x, 0 < u j x) ∧ (σ j).sqrt =ᵐ[haar 1] u j) ∧
        ∃ η c : ℝ, 0 < η ∧ 0 < c ∧ ∀ j : Fin 3, ∀ ρ : AbsoluteDensity 1,
          ordinaryRootH1Deviation (σ j) ρ (u j) ≤ η →
          let w := fun x => ρ.sqrt x / u j x
          ∃ hw : MemH1 w,
          c * ((∫ x, (σ j).density x * (weakGradient w hw x 0) ^ 2 ∂haar 1) +
            ∫ x, (σ j).density x * (w x - 1) ^ 2 ∂haar 1) ≤
              (ordinaryFisher h ρ).toReal - 2 * (ordinaryLSRate (ordinaryReference h)).toReal *
                (ordinaryEntropy h ρ).toReal := by
  obtain ⟨k, δ, hk, hδ, hδr, hPC⟩ := ordinaryRoot_native_poincare_lower D
  refine ⟨δ, hδ, hδr, fun h hh hhd => ?_⟩
  obtain ⟨σ, hσ, hpos, hquot, hmin, _, _, _, hrate⟩ := D.roots h hh (hhd.trans_le hδr)
  choose u hu hup hrep using fun j => ordinaryChart_positiveContinuousRoot h
    (chartU_isC2_STR02924 D.ψ h (D.Z j h)) (σ j) (hσ j)
  have hU : ∀ j, Continuous (u j) ∧ (∀ x, 0 < u j x) ∧ (σ j).sqrt =ᵐ[haar 1] u j :=
    fun j => ⟨hu j, hup j, hrep j⟩
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  let p := a + DGPS.Circle.AngularNormalization.a0 * (4 * k / 5) * h ^ 2
  have ha0 : 0 < DGPS.Circle.AngularNormalization.a0 := by
    unfold DGPS.Circle.AngularNormalization.a0
    positivity
  have hap : a < p := by
    dsimp only [p]
    nlinarith [mul_pos ha0 (mul_pos (by positivity : 0 < 4 * k / 5) (sq_pos_of_pos hh))]
  have hP : ∀ j, ENNReal.ofReal p ≤ poincareRate (densityMeasure (σ j)) := by
    intro j
    have hl := hPC h hh hhd j (σ j) (hσ j)
    convert hl using 1
    congr 1
    dsimp only [p, a]
    rw [hrate j]
    ring
  have hs := fun j => ordinaryRoot_local_deficit_stability h (σ j) (hpos j) (hmin j)
    (u j) (hu j) (hup j) (hrep j) p hap (hP j)
  choose ηs cs hηs hcs hstab using hs
  let η := min (ηs 0) (min (ηs 1) (ηs 2))
  let c := min (cs 0) (min (cs 1) (cs 2))
  have hη : 0 < η := lt_min (hηs 0) (lt_min (hηs 1) (hηs 2))
  have hc : 0 < c := lt_min (hcs 0) (lt_min (hcs 1) (hcs 2))
  have hηle : ∀ j : Fin 3, η ≤ ηs j := by
    intro j
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hcle : ∀ j : Fin 3, c ≤ cs j := by
    intro j
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨σ, u, hσ, hpos, hquot, hU, η, c, hη, hc, fun j ρ hnear => ?_⟩
  refine ⟨ordinaryEquality_relativeRoot_memH1 (σ j) ρ (u j) (hu j) (hup j) (hrep j), ?_⟩
  have hsρ := hstab j ρ (hnear.trans (hηle j))
  apply le_trans _ hsρ
  apply mul_le_mul_of_nonneg_right (hcle j)
  exact add_nonneg (integral_nonneg fun x =>
    mul_nonneg ((σ j).density_nonneg x) (sq_nonneg _))
    (integral_nonneg fun x => mul_nonneg ((σ j).density_nonneg x) (sq_nonneg _))

/-- Original-Haar local coercivity for ANY supplied SAME-D triple. The root laws are
not reselected: the auxiliary use of `D.roots` below extracts only the canonical rate
identity. Neighborhood and coercivity constants are chosen before the root index. -/
theorem ordinaryRoot_same_graph_localHaar (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ σ : Fin 3 → AbsoluteDensity 1,
        (∀ j θ, (σ j).density (DGPS.Circle.AngularNormalization.angEquiv.symm θ) =
          rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h))
            (DGPS.Circle.AngularNormalization.angSec θ)) →
        (∀ j, 0 < ordinaryEntropy h (σ j)) →
        (∀ j, ∀ τ : AbsoluteDensity 1, 0 < ordinaryEntropy h τ →
          str025_quot h (σ j) ≤ str025_quot h τ) →
        ∃ (u : Fin 3 → Torus 1 → ℝ) (η c : ℝ),
          (∀ j, Continuous (u j) ∧ (∀ x, 0 < u j x) ∧ (σ j).sqrt =ᵐ[haar 1] u j) ∧
          0 < η ∧ 0 < c ∧ ∀ j : Fin 3, ∀ ρ : AbsoluteDensity 1,
            ordinaryRootH1Deviation (σ j) ρ (u j) ≤ η →
            c * ordinaryRootH1Deviation (σ j) ρ (u j) ^ 2 ≤
              (ordinaryFisher h ρ).toReal - 2 * (ordinaryLSRate (ordinaryReference h)).toReal *
                (ordinaryEntropy h ρ).toReal := by
  obtain ⟨k, δ, hk, hδ, hδr, hPC⟩ := ordinaryRoot_native_poincare_lower D
  refine ⟨δ, hδ, hδr, fun h hh hhd σ hσ hpos hmin => ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, hrate⟩ := D.roots h hh (hhd.trans_le hδr)
  choose u hu hup hrep using fun j => ordinaryChart_positiveContinuousRoot h
    (chartU_isC2_STR02924 D.ψ h (D.Z j h)) (σ j) (hσ j)
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  let p := a + DGPS.Circle.AngularNormalization.a0 * (4 * k / 5) * h ^ 2
  have ha0 : 0 < DGPS.Circle.AngularNormalization.a0 := by
    unfold DGPS.Circle.AngularNormalization.a0
    positivity
  have hap : a < p := by
    dsimp only [p]
    nlinarith [mul_pos ha0 (mul_pos (by positivity : 0 < 4 * k / 5) (sq_pos_of_pos hh))]
  have hP : ∀ j, ENNReal.ofReal p ≤ poincareRate (densityMeasure (σ j)) := by
    intro j
    have hl := hPC h hh hhd j (σ j) (hσ j)
    convert hl using 1
    congr 1
    dsimp only [p, a]
    rw [hrate j]
    ring
  choose ηs cs hηs hcs hstab using fun j => ordinaryRoot_localHaar_deficit_stability
    h (σ j) (hpos j) (hmin j) (u j) (hu j) (hup j) (hrep j) p hap (hP j)
  let η := min (ηs 0) (min (ηs 1) (ηs 2))
  let c := min (cs 0) (min (cs 1) (cs 2))
  have hη : 0 < η := lt_min (hηs 0) (lt_min (hηs 1) (hηs 2))
  have hc : 0 < c := lt_min (hcs 0) (lt_min (hcs 1) (hcs 2))
  have hηle : ∀ j : Fin 3, η ≤ ηs j := by
    intro j
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hcle : ∀ j : Fin 3, c ≤ cs j := by
    intro j
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨u, η, c, fun j => ⟨hu j, hup j, hrep j⟩, hη, hc, fun j ρ hnear => ?_⟩
  exact (mul_le_mul_of_nonneg_right (hcle j) (sq_nonneg _)).trans
    (hstab j ρ (hnear.trans (hηle j)))

end DGPS.Examples.ThreeSpeciesCircle
