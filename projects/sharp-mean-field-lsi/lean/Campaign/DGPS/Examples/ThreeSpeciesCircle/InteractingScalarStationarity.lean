import DGPS.Examples.ThreeSpeciesCircle.InteractingDissipationVariation
import DGPS.Examples.ThreeSpeciesCircle.InteractingVariationInitial

/-! Actual scalar minimizers are stationary on every genuine normalized
original-H1 root path. Differentiability and initial-law identification are
derived from the concrete model leaves, not imposed as analytical hypotheses. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Actual full-H1 first-variation stationarity for EVERY positive-gap scalar
minimizer. No smoothness, positive stored root, Euler equation, path derivative
or limiting rate is a premise. The remaining conversion to a displayed weak
elliptic equation uses the explicit component formulas in the variation leaves. -/
theorem elementaryModel_scalarMinimizer_H1_stationarity {h : ℝ} (hh : 0 < h) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧
      ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
        ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (modelData h ε) ρ →
          scalarQuotient (modelData h ε) b ρ = scalarRate (modelData h ε) b →
          ∀ (φ : Torus 1 → ℝ) (G : Torus 1 → Tangent 1) (hφ : IsWeakGradient φ G),
            deriv (fun t : ℝ =>
                (scalarDissipation (modelData h ε) b (absoluteRootVariation ρ hφ t)).toReal) 0 =
              2 * (scalarRate (modelData h ε) b).toReal *
                deriv (fun t : ℝ =>
                  (scalarGap (modelData h ε) (absoluteRootVariation ρ hφ t) : ℝ)) 0 := by
  obtain ⟨ε0, hε0, hεmax, hgap⟩ := elementaryModel_speciesGap_entropy_comparable hh
  refine ⟨ε0, hε0, hεmax, fun ε hε hεsmall b ρ hGP hmin φ G hφ => ?_⟩
  have hεbound : ε < epsMax h := hεsmall.trans_le hεmax
  -- Finiteness is derived from the actual positive-gap minimizer before the
  -- canonical rate is passed to `toReal`.
  have hratefin : scalarRate (modelData h ε) b ≠ ⊤ := by
    rw [← hmin]
    unfold scalarQuotient
    exact ENNReal.div_ne_top (elementaryModel_scalarDissipation_real h ε b ρ).1
      (mul_ne_zero (by norm_num) (by exact_mod_cast hGP.ne'))
  have hH : 0 < ordinaryEntropy h ρ := by
    by_contra hn
    have hHz : ordinaryEntropy h ρ = 0 := le_antisymm (not_lt.mp hn) zero_le
    have hg := (hgap ε hε hεsmall (SpeciesFamily.single ρ)).2
    have ht : (scalarGap (modelData h ε) ρ : ℝ) ≤ 0 := by
      simpa only [speciesGap_single, sum_single_count, SpeciesFamily.single_weight,
        SpeciesFamily.single_density, one_mul, hHz, ENNReal.toReal_zero, mul_zero] using hg
    have hp : (0 : ℝ) < scalarGap (modelData h ε) ρ := hGP
    linarith
  let N := fun t : ℝ =>
    (scalarDissipation (modelData h ε) b (absoluteRootVariation ρ hφ t)).toReal
  let g := fun t : ℝ => (scalarGap (modelData h ε) (absoluteRootVariation ρ hφ t) : ℝ)
  let r := (scalarRate (modelData h ε) b).toReal
  have hN := (absoluteRootVariation_scalarDissipation_hasDerivAt h ε b ρ hφ).differentiableAt.hasDerivAt
  have hg := (absoluteRootVariation_scalarGap_hasDerivAt hh hε hεbound ρ hH hφ).differentiableAt.hasDerivAt
  change HasDerivAt N (deriv N 0) 0 at hN
  change HasDerivAt g (deriv g 0) 0 at hg
  have hN0 : N 0 = (scalarDissipation (modelData h ε) b ρ).toReal := by
    dsimp only [N]
    rw [absoluteRootVariation_dissipation_zero]
  have hg0 : g 0 = (scalarGap (modelData h ε) ρ : ℝ) := by
    dsimp only [g]
    rw [absoluteRootVariation_gap_zero]
  have hgpos : 0 < g 0 := by rw [hg0]; exact hGP
  have hgp : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < g t :=
    hg.continuousAt.eventually (lt_mem_nhds hgpos)
  have hQ := hN.div (hg.const_mul 2) (by positivity : 2 * g 0 ≠ 0)
  have hloc : IsLocalMin (fun t : ℝ => N t / (2 * g t)) 0 := by
    filter_upwards [hgp] with t ht
    have hGt : 0 < scalarGap (modelData h ε) (absoluteRootVariation ρ hφ t) := ht
    have hle : scalarQuotient (modelData h ε) b ρ ≤
        scalarQuotient (modelData h ε) b (absoluteRootVariation ρ hφ t) := by
      rw [hmin]
      exact scalarRate_le_quotient (modelData h ε) b _ hGt
    have hqfin : scalarQuotient (modelData h ε) b (absoluteRootVariation ρ hφ t) ≠ ⊤ := by
      unfold scalarQuotient
      exact ENNReal.div_ne_top (elementaryModel_scalarDissipation_real h ε b _).1
        (mul_ne_zero (by norm_num) (by exact_mod_cast hGt.ne'))
    have hr := ENNReal.toReal_mono hqfin hle
    unfold scalarQuotient at hr
    rw [ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.coe_toReal,
      ENNReal.coe_toReal] at hr
    change (scalarDissipation (modelData h ε) b ρ).toReal /
      (2 * (scalarGap (modelData h ε) ρ : ℝ)) ≤ N t / (2 * g t) at hr
    rw [← hN0, ← hg0] at hr
    exact hr
  have hzero := hloc.hasDerivAt_eq_zero hQ
  have hnum := (div_eq_iff (by positivity : (2 * g 0) ^ 2 ≠ 0)).mp hzero
  simp only [zero_mul] at hnum
  have hr : N 0 = 2 * r * g 0 := by
    have ht := congrArg ENNReal.toReal hmin
    unfold scalarQuotient at ht
    rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.coe_toReal] at ht
    rw [← hN0, ← hg0] at ht
    change N 0 / (2 * g 0) = r at ht
    have he := (div_eq_iff (by positivity : 2 * g 0 ≠ 0)).mp ht
    nlinarith
  have he : deriv N 0 * (2 * g 0) - N 0 * (2 * deriv g 0) =
      (2 * g 0) * (deriv N 0 - 2 * r * deriv g 0) := by
    rw [hr]
    ring
  rw [he] at hnum
  have hc : deriv N 0 - 2 * r * deriv g 0 = 0 :=
    (mul_eq_zero.mp hnum).resolve_left (by positivity)
  change deriv N 0 = 2 * r * deriv g 0
  linarith

end DGPS.Examples.ThreeSpeciesCircle
