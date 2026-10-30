import DGPS.Examples.ThreeSpeciesCircle.H1DensitySegmentJensen
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootPoincareGap
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryGroundStateRoots

/-! Actual same-graph common density neighborhoods for strict H1 merging.
The supplied root family is preserved. The ordinary rate is a fixed upper
subrate before coupling, drift, family, active labels and mixing weights. -/

noncomputable section
open MeasureTheory Filter Topology Set
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Every actual ordinary root on the SAME graph has one common density
neighborhood with strict merging for every real rate between zero and the
ordinary optimum. No species is assumed to be an individual scalar minimizer. -/
theorem ordinaryGraph_densitySegment_common_strictJensen (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ S : Fin 3 → AbsoluteDensity 1,
      (∀ j θ, (S j).density (angEquiv.symm θ) =
        rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) →
      ∃ w : Fin 3 → Torus 1 → ℝ, ∃ q : ℝ,
        (∀ j, Continuous (w j)) ∧ (∀ j x, 0 < w j x) ∧
        (∀ j, (S j).sqrt =ᵐ[haar 1] w j) ∧ 0 < q ∧ q ≤ 1 / 4 ∧
        ∀ r : ℝ, 0 ≤ r → r ≤ (ordinaryLSRate (ordinaryReference h)).toReal →
          ∀ j : Fin 3, ∀ (ρ ν : AbsoluteDensity 1) (u v : Torus 1 → ℝ),
            ∀ (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x),
            ∀ (hρ : ρ.sqrt =ᵐ[haar 1] u) (hν : ν.sqrt =ᵐ[haar 1] v),
            densityMeasure ρ ≠ densityMeasure ν →
            (∀ x, (1 - q) ^ 2 * w j x ^ 2 ≤ u x ^ 2) →
            (∀ x, u x ^ 2 ≤ (1 + q) ^ 2 * w j x ^ 2) →
            (∀ x, (1 - q) ^ 2 * w j x ^ 2 ≤ v x ^ 2) →
            (∀ x, v x ^ 2 ≤ (1 + q) ^ 2 * w j x ^ 2) →
            ∀ θ : ℝ, ∀ hθ0 : 0 < θ, ∀ hθ1 : θ < 1,
              let τ := h1DensitySegment ρ ν u v hu hv hup hvp hρ hν θ ⟨hθ0.le, hθ1.le⟩
              (ordinaryFisher h τ).toReal - 2 * r * (ordinaryEntropy h τ).toReal <
                (1 - θ) * ((ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal) +
                  θ * ((ordinaryFisher h ν).toReal - 2 * r * (ordinaryEntropy h ν).toReal) := by
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
  choose qj κj hqj hqj4 hκj hmargin using fun j =>
    h1DensitySegment_poincare_margin_of_reference (S j) (w j) (hw j) (hwp j) (hrep j)
      a (a + gap) ha (by linarith) (hPj j)
  let q := min (qj 0) (min (qj 1) (qj 2))
  have hq : 0 < q := lt_min (hqj 0) (lt_min (hqj 1) (hqj 2))
  have hqle (j : Fin 3) : q ≤ qj j := by
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hq4 : q ≤ 1 / 4 := (hqle 0).trans (hqj4 0)
  refine ⟨w, q, hw, hwp, hrep, hq, hq4,
    fun r hr hra j ρ ν u v hu hv hup hvp hρ hν hne hulo huhi hvlo hvhi θ hθ0 hθ1 => ?_⟩
  have hloMon (x : Torus 1) : (1 - qj j) ^ 2 * w j x ^ 2 ≤ (1 - q) ^ 2 * w j x ^ 2 :=
    mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (by linarith [hqj4 j] : 0 ≤ 1 - qj j)
        (by linarith : 0 ≤ 1 - q)).2 (sub_le_sub_left (hqle j) 1)) (sq_nonneg _)
  have hhiMon (x : Torus 1) : (1 + q) ^ 2 * w j x ^ 2 ≤ (1 + qj j) ^ 2 * w j x ^ 2 :=
    mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (by positivity : 0 ≤ 1 + q)
        (by linarith [hqj j] : 0 ≤ 1 + qj j)).2 (add_le_add_right (hqle j) 1)) (sq_nonneg _)
  let κ := a + κj j - r
  have hκ : 0 < κ := by dsimp only [κ]; linarith [hκj j]
  have hmarg : ∀ t : ℝ, ∀ ht : t ∈ Icc (0 : ℝ) 1,
      ENNReal.ofReal (r + κ) ≤
        poincareRate (densityMeasure (h1DensitySegment ρ ν u v hu hv hup hvp hρ hν t ht)) := by
    intro t ht
    rw [show r + κ = a + κj j by dsimp only [κ]; ring]
    exact hmargin j ρ ν u v hu hv hup hvp hρ hν
      (fun x => (hloMon x).trans (hulo x)) (fun x => (huhi x).trans (hhiMon x))
      (fun x => (hloMon x).trans (hvlo x)) (fun x => (hvhi x).trans (hhiMon x)) t ht
  have hSC := h1DensitySegmentPhi_strictConvexOn h r κ hr hκ ρ ν u v hu hv hup hvp hρ hν hne hmarg
  have hj := hSC.2 (by constructor <;> norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by constructor <;> norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) (by norm_num : (0 : ℝ) ≠ 1)
    (sub_pos.mpr hθ1) hθ0 (by ring : (1 - θ) + θ = 1)
  have hj' : h1DensitySegmentPhi h r ρ ν u v θ <
      (1 - θ) * h1DensitySegmentPhi h r ρ ν u v 0 + θ * h1DensitySegmentPhi h r ρ ν u v 1 := by
    simpa only [smul_eq_mul, mul_zero, mul_one, zero_add] using hj
  have hep := h1DensitySegmentPhi_endpoints h r ρ ν u v hu hv hup hvp hρ hν
  rw [h1DensitySegmentPhi_eq ρ ν u v hu hv hup hvp hρ hν θ ⟨hθ0.le, hθ1.le⟩ h r,
    hep.1, hep.2] at hj'
  exact hj'

end DGPS.Examples.ThreeSpeciesCircle
