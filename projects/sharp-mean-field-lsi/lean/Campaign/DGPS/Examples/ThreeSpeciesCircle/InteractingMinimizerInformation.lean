import DGPS.Examples.ThreeSpeciesCircle.InteractingUniformInformationBound
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarTrial

/-! Common-in-coupling information bounds for EVERY actual scalar minimizer.
The common quotient bound is supplied by the actual ordinary-root trial; it is not
an assumption on the minimizer or an epsilon-dependent information constant. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The actual trial at comparison value a+1 supplies a common quotient bound. The
information and entropy constant is fixed before epsilon, drift and every original-H1
minimizer. No information/localization/regularity premise is supplied. -/
theorem elementaryModel_minimizer_uniform_information (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 C : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ 0 ≤ C ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
          ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (modelData h ε) ρ →
            scalarQuotient (modelData h ε) b ρ = scalarRate (modelData h ε) b →
            (ordinaryFisher h ρ).toReal + (ordinaryEntropy h ρ).toReal ≤ C := by
  refine ⟨D.radius, D.radius_pos, le_rfl, fun h hh hhd => ?_⟩
  obtain ⟨σ, _, hpos, hquot, _⟩ := D.roots h hh hhd
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  let M := a + 1
  have hM : 0 ≤ M := by dsimp only [M]; linarith
  have har : a < M := by dsimp only [M]; linarith
  obtain ⟨εT, hεT, hεTmax, htrial⟩ := ordinaryRoot_interacting_scalar_trial
    hh (σ 0) (hpos 0) (hquot 0) har
  obtain ⟨εI, hεI, _, hinfo⟩ := elementaryModel_uniform_scalar_information hh
  obtain ⟨CI, hCI, hbound⟩ := hinfo M hM
  obtain ⟨B, hB, hbudget⟩ := ordinaryEntropy_information_bound h 1 one_pos
  refine ⟨min εT εI, 2 * CI + B, lt_min hεT hεI,
    (min_le_left _ _).trans hεTmax, by positivity,
    fun ε hε hεsmall b ρ hG hmin => ?_⟩
  obtain ⟨hσG, hσQ⟩ := htrial ε hε (hεsmall.trans_le (min_le_left _ _)) b
  have hQ : scalarQuotient (modelData h ε) b ρ ≤ ENNReal.ofReal M := by
    rw [hmin]
    exact (scalarRate_le_quotient (modelData h ε) b (σ 0) hσG).trans hσQ.le
  have hI := hbound ε hε (hεsmall.trans_le (min_le_right _ _)) b ρ hG hQ
  have hH := hbudget ρ
  nlinarith

end DGPS.Examples.ThreeSpeciesCircle
