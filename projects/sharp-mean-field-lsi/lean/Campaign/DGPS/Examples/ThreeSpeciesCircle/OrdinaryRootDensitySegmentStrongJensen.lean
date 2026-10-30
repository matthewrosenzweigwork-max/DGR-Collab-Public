import DGPS.Examples.ThreeSpeciesCircle.H1DensitySegmentStrongJensen
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootPoincareGap
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryGroundStateRoots

/-! Actual same-graph common density neighborhoods for quantitative H1 merging.
The supplied root family is preserved. The ordinary rate is a fixed upper
subrate before coupling, drift, family, active labels and mixing weights. -/

noncomputable section
open MeasureTheory Filter Topology Set
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Every actual ordinary root on the SAME graph has one common density
neighborhood with quantitative strong merging for every real rate between zero and the
ordinary optimum. No species is assumed to be an individual scalar minimizer. -/
theorem ordinaryGraph_densitySegment_common_strongJensen (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ S : Fin 3 → AbsoluteDensity 1,
      (∀ j θ, (S j).density (angEquiv.symm θ) =
        rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) →
      ∃ w : Fin 3 → Torus 1 → ℝ, ∃ q c : ℝ,
        (∀ j, Continuous (w j)) ∧ (∀ j x, 0 < w j x) ∧
        (∀ j, (S j).sqrt =ᵐ[haar 1] w j) ∧ 0 < q ∧ q ≤ 1 / 4 ∧ 0 < c ∧
        ∀ r : ℝ, 0 ≤ r → r ≤ (ordinaryLSRate (ordinaryReference h)).toReal →
          ∀ j : Fin 3, ∀ (ρ ν : AbsoluteDensity 1) (u v : Torus 1 → ℝ),
            ∀ (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x),
            ∀ (hρ : ρ.sqrt =ᵐ[haar 1] u) (hν : ν.sqrt =ᵐ[haar 1] v),
            (∀ x, (1 - q) ^ 2 * w j x ^ 2 ≤ u x ^ 2) →
            (∀ x, u x ^ 2 ≤ (1 + q) ^ 2 * w j x ^ 2) →
            (∀ x, (1 - q) ^ 2 * w j x ^ 2 ≤ v x ^ 2) →
            (∀ x, v x ^ 2 ≤ (1 + q) ^ 2 * w j x ^ 2) →
            ∀ θ : ℝ, ∀ hθ : θ ∈ Icc (0 : ℝ) 1,
              let τ := h1DensitySegment ρ ν u v hu hv hup hvp hρ hν θ hθ
              (ordinaryFisher h τ).toReal - 2 * r * (ordinaryEntropy h τ).toReal ≤
                (1 - θ) * ((ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal) +
                  θ * ((ordinaryFisher h ν).toReal - 2 * r * (ordinaryEntropy h ν).toReal) -
                    c * θ * (1 - θ) * ∫ x, (ν.density x - ρ.density x) ^ 2 ∂haar 1 := by
  classical
  obtain ⟨k, δ, hk, hδ, hδr, hPC⟩ := ordinaryRoot_native_poincare_lower D
  refine ⟨δ, hδ, hδr, fun h hh hhd S hS => ?_⟩
  have hhD : h < D.radius := hhd.trans_le hδr
  obtain ⟨_, _, _, _, _, _, _, _, hrate⟩ := D.roots h hh hhD
  choose w hw hwp hrep using fun j => ordinaryChart_positiveContinuousRoot h
    (chartU_isC2_STR02924 D.ψ h (D.Z j h)) (S j) (hS j)
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  let gap := DGPS.Circle.AngularNormalization.a0 * (4 * k / 5) * h ^ 2
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hgap : 0 < gap := by
    have ha0 : 0 < DGPS.Circle.AngularNormalization.a0 := by
      unfold DGPS.Circle.AngularNormalization.a0
      positivity
    dsimp only [gap]
    positivity
  have hPj (j : Fin 3) : ENNReal.ofReal (a + gap) ≤ poincareRate (densityMeasure (S j)) := by
    have ht := hPC h hh hhd j (S j) (hS j)
    convert ht using 1
    congr 1
    dsimp only [a, gap]
    rw [hrate j]
    ring
  choose qj cj hqj hqj4 hcj hstrong using fun j =>
    h1DensitySegment_cost_uniformStrongJensen_of_reference h a (a + gap) ha (by linarith)
      (S j) (w j) (hw j) (hwp j) (hrep j) (hPj j)
  let q := min (qj 0) (min (qj 1) (qj 2))
  have hq : 0 < q := lt_min (hqj 0) (lt_min (hqj 1) (hqj 2))
  have hqle (j : Fin 3) : q ≤ qj j := by
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hq4 : q ≤ 1 / 4 := (hqle 0).trans (hqj4 0)
  let c := min (cj 0) (min (cj 1) (cj 2))
  have hc : 0 < c := lt_min (hcj 0) (lt_min (hcj 1) (hcj 2))
  have hcle (j : Fin 3) : c ≤ cj j := by
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨w, q, c, hw, hwp, hrep, hq, hq4, hc,
    fun r hr hra j ρ ν u v hu hv hup hvp hρ hν hulo huhi hvlo hvhi θ hθ => ?_⟩
  have hloMon (x : Torus 1) : (1 - qj j) ^ 2 * w j x ^ 2 ≤ (1 - q) ^ 2 * w j x ^ 2 :=
    mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (by linarith [hqj4 j] : 0 ≤ 1 - qj j)
        (by linarith : 0 ≤ 1 - q)).2 (sub_le_sub_left (hqle j) 1)) (sq_nonneg _)
  have hhiMon (x : Torus 1) : (1 + q) ^ 2 * w j x ^ 2 ≤ (1 + qj j) ^ 2 * w j x ^ 2 :=
    mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (by positivity : 0 ≤ 1 + q)
        (by linarith [hqj j] : 0 ≤ 1 + qj j)).2 (show 1 + q ≤ 1 + qj j by linarith [hqle j])) (sq_nonneg _)
  have hh := hstrong j r hr hra ρ ν u v hu hv hup hvp hρ hν
    (fun x => (hloMon x).trans (hulo x)) (fun x => (huhi x).trans (hhiMon x))
    (fun x => (hloMon x).trans (hvlo x)) (fun x => (hvhi x).trans (hhiMon x)) θ hθ
  have hGain : c * θ * (1 - θ) * (∫ x, (ν.density x - ρ.density x) ^ 2 ∂haar 1) ≤
      cj j * θ * (1 - θ) * (∫ x, (ν.density x - ρ.density x) ^ 2 ∂haar 1) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hcle j) hθ.1)
        (sub_nonneg.mpr hθ.2)) (integral_nonneg fun _ => sq_nonneg _)
  exact hh.trans (sub_le_sub_left hGain _)

end DGPS.Examples.ThreeSpeciesCircle
