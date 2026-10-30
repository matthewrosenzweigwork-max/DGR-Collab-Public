import DGPS.Examples.PolynomialSpeciesFullLimitCapture
import DGPS.Examples.PolynomialSpeciesOptimizerAssembly

noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ContDiff ENNReal
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium
open DGPS.Circle.AngularNormalization
namespace DGPS.Examples.PolynomialSpecies

/-- An exact original-domain minimizer represented on the supplied graph, in
scaled coordinates. This packages data, not a new hypothesis on optimizers. -/
def PolynomialScaledOptimizerData (U : Set PolynomialRangeParameters)
    (ψ : PolynomialRangeParameters → E_STR02969) (h : ℝ)
    (c : PolynomialScaledCoefficients) : Prop :=
  ∃ (b : AbsoluteDrift (canonical_elementary_polynomial_model h))
    (ρ : AbsoluteDensity 1),
    h ^ 4 * c.2.2.2 = root_EX054 h ∧
    a0 * (1 + h ^ 2 * c.2.2.1) = (scalarRate (canonical_elementary_polynomial_model h) b).toReal ∧
    0 < scalarGap (canonical_elementary_polynomial_model h) ρ ∧
    scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
      scalarRate (canonical_elementary_polynomial_model h) b ∧
    polynomialScaledParameters (h, c) ∈ U ∧
    ρ.density =ᵐ[haar 1] (polynomialChartAbsolute h
      ((h * c.1) • cosC2_STR02915 + (h * c.2.1) • sinC2_STR02915 +
        (ψ (polynomialScaledParameters (h, c)) : PeriodicC2_STR02969))).density

/-- Uniform two-base capture of ALL represented original optimizers in any
compact coefficient box. No annular separation or limiting classification is
assumed: those are discharged by the actual original-domain producers. -/
theorem polynomial_scalarMinimizer_compact_uniform_capture
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0) (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (K : Set PolynomialScaledCoefficients) (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ c ∈ K, PolynomialScaledOptimizerData U ψ h c →
      ∃ j : Fin 2, dist ((c.1, c.2.1), c.2.2.1) (polynomialQuarticCriticalBase j) < ε := by
  let V : Set PolynomialScaledCoefficients :=
    {c | ∃ j : Fin 2, dist ((c.1, c.2.1), c.2.2.1) (polynomialQuarticCriticalBase j) < ε}
  have hV : IsOpen V := by
    apply isOpen_iff_mem_nhds.2
    intro c hc
    obtain ⟨j, hj⟩ := hc
    have ho : IsOpen {c : PolynomialScaledCoefficients |
        dist ((c.1, c.2.1), c.2.2.1) (polynomialQuarticCriticalBase j) < ε} :=
      isOpen_lt (by fun_prop) continuous_const
    exact Filter.mem_of_superset (ho.mem_nhds hj) (fun d hd => ⟨j, hd⟩)
  apply compact_uniform_capture_of_limit hK hV (PolynomialScaledOptimizerData U ψ)
  intro h c c₀ hpos hh _hKmem hdata hc
  choose b ρ hs hr hG hmin hp hρ using hdata
  have hA := hc.fst_nhds
  have hB := hc.snd_nhds.fst_nhds
  have hα := hc.snd_nhds.snd_nhds.fst_nhds
  have hσ := hc.snd_nhds.snd_nhds.snd_nhds
  obtain ⟨hα₀, hA₀, hB₀⟩ := polynomial_scalarMinimizer_full_limit_capture
    hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst
    h (fun n => (c n).1) (fun n => (c n).2.1)
    (fun n => (c n).2.2.1) (fun n => (c n).2.2.2)
    c₀.1 c₀.2.1 c₀.2.2.1 c₀.2.2.2 hh hA hB hα hσ
    b ρ (fun n => (hpos n).ne') hs hr hG hmin hρ hpos hp
  have hsqrt : (Real.sqrt ((1 + Real.sqrt 2) / 4)) ^ 2 = (1 + Real.sqrt 2) / 4 :=
    Real.sq_sqrt (by positivity)
  have hsign : c₀.2.1 = Real.sqrt ((1 + Real.sqrt 2) / 4) ∨
      c₀.2.1 = -Real.sqrt ((1 + Real.sqrt 2) / 4) :=
    sq_eq_sq_iff_eq_or_eq_neg.1 (hB₀.trans hsqrt.symm)
  rcases hsign with hplus | hminus
  · refine ⟨0, ?_⟩
    have he : ((c₀.1, c₀.2.1), c₀.2.2.1) = polynomialQuarticCriticalBase 0 := by
      simp [polynomialQuarticCriticalBase, hA₀, hplus, hα₀]
    rw [he, dist_self]
    exact hε
  · refine ⟨1, ?_⟩
    have he : ((c₀.1, c₀.2.1), c₀.2.2.1) = polynomialQuarticCriticalBase 1 := by
      simp [polynomialQuarticCriticalBase, hA₀, hminus, hα₀]
    rw [he, dist_self]
    exact hε

end DGPS.Examples.PolynomialSpecies
