import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarStationarity
import DGPS.Examples.ThreeSpeciesCircle.InteractingReferenceBarrier

/-! Actual value and normalized-H1 first variation of the scalar deficit at
EVERY actual minimizer. These identities supply the mass terms in the explicit
weak equation, without assuming that equation or an analytic provider. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

theorem elementaryModel_scalarMinimizer_deficit_zero {h ε : ℝ} (hh : 0 < h)
    (hε : 0 < ε) (hεmax : ε < epsMax h) (b : AbsoluteDrift (modelData h ε))
    (ρ : AbsoluteDensity 1) (hGP : 0 < scalarGap (modelData h ε) ρ)
    (hmin : scalarQuotient (modelData h ε) b ρ = scalarRate (modelData h ε) b) :
    let r := (scalarRate (modelData h ε) b).toReal
    (ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal +
      ε * elementaryC h r ρ + ε ^ 2 * elementaryJ h ρ = 0 := by
  let r := (scalarRate (modelData h ε) b).toReal
  have hratefin : scalarRate (modelData h ε) b ≠ ⊤ := by
    rw [← hmin]
    unfold scalarQuotient
    exact ENNReal.div_ne_top (elementaryModel_scalarDissipation_real h ε b ρ).1
      (mul_ne_zero (by norm_num) (by exact_mod_cast hGP.ne'))
  have hq := congrArg ENNReal.toReal hmin
  unfold scalarQuotient at hq
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.coe_toReal] at hq
  have hg : (0 : ℝ) < scalarGap (modelData h ε) ρ := hGP
  have hD : (scalarDissipation (modelData h ε) b ρ).toReal =
      2 * r * (scalarGap (modelData h ε) ρ : ℝ) := by
    have hm := (div_eq_iff (by positivity : 2 * (scalarGap (modelData h ε) ρ : ℝ) ≠ 0)).mp hq
    change _ = r * _ at hm
    nlinarith
  have he := elementaryModel_scalar_deficit_real hh hε hεmax b ρ r
  rw [hD] at he
  change (ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal +
    ε * elementaryC h r ρ + ε ^ 2 * elementaryJ h ρ = 0
  linarith

/-- Genuine full-H1 deficit stationarity with all actual nonlinear force
variations present. The rate and initial function values come from the actual
minimizer, not an external Euler or normalization premise. -/
theorem elementaryModel_scalarMinimizer_deficit_hasDerivAt_zero {h : ℝ} (hh : 0 < h) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧
      ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
        ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (modelData h ε) ρ →
          scalarQuotient (modelData h ε) b ρ = scalarRate (modelData h ε) b →
          ∀ (φ : Torus 1 → ℝ) (G : Torus 1 → Tangent 1) (hφ : IsWeakGradient φ G),
            let r := (scalarRate (modelData h ε) b).toReal
            HasDerivAt (fun t : ℝ =>
              (ordinaryFisher h (absoluteRootVariation ρ hφ t)).toReal -
                2 * r * (ordinaryEntropy h (absoluteRootVariation ρ hφ t)).toReal +
                ε * elementaryC h r (absoluteRootVariation ρ hφ t) +
                ε ^ 2 * elementaryJ h (absoluteRootVariation ρ hφ t)) 0 0 := by
  obtain ⟨εS, hεS, hεSmax, hstation⟩ := elementaryModel_scalarMinimizer_H1_stationarity hh
  obtain ⟨εG, hεG, _, hgap⟩ := elementaryModel_speciesGap_entropy_comparable hh
  refine ⟨min εS εG, lt_min hεS hεG, (min_le_left _ _).trans hεSmax,
    fun ε hε hεsmall b ρ hGP hmin φ G hφ => ?_⟩
  have heS : ε < εS := hεsmall.trans_le (min_le_left _ _)
  have heG : ε < εG := hεsmall.trans_le (min_le_right _ _)
  have heMax : ε < epsMax h := heS.trans_le hεSmax
  have hH : 0 < ordinaryEntropy h ρ := by
    by_contra hn
    have hHz : ordinaryEntropy h ρ = 0 := le_antisymm (not_lt.mp hn) zero_le
    have hg := (hgap ε hε heG (SpeciesFamily.single ρ)).2
    have hu : (scalarGap (modelData h ε) ρ : ℝ) ≤ 0 := by
      simpa only [speciesGap_single, sum_single_count, SpeciesFamily.single_weight,
        SpeciesFamily.single_density, one_mul, hHz, ENNReal.toReal_zero, mul_zero] using hg
    have hp : (0 : ℝ) < scalarGap (modelData h ε) ρ := hGP
    linarith
  let r := (scalarRate (modelData h ε) b).toReal
  have hD := (absoluteRootVariation_scalarDissipation_hasDerivAt h ε b ρ hφ).differentiableAt.hasDerivAt
  have hG := (absoluteRootVariation_scalarGap_hasDerivAt hh hε heMax ρ hH hφ).differentiableAt.hasDerivAt
  have hzero := hstation ε hε heS b ρ hGP hmin φ G hφ
  have hd := hD.sub (hG.const_mul (2 * r))
  have hd0 : HasDerivAt (fun t : ℝ =>
      (scalarDissipation (modelData h ε) b (absoluteRootVariation ρ hφ t)).toReal -
        2 * r * (scalarGap (modelData h ε) (absoluteRootVariation ρ hφ t) : ℝ)) 0 0 := by
    convert hd using 1
    rw [hzero]
    dsimp only [r]
    ring
  apply hd0.congr_of_eventuallyEq
  exact Eventually.of_forall fun t =>
    (elementaryModel_scalar_deficit_real hh hε heMax b (absoluteRootVariation ρ hφ t) r).symm

end DGPS.Examples.ThreeSpeciesCircle
