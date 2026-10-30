import DGPS.Examples.PolynomialSpeciesUniformOptimizerCapture
import DGPS.Examples.PolynomialSpeciesCompactTube

noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ContDiff ENNReal
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium
open DGPS.Circle.AngularNormalization
namespace DGPS.Examples.PolynomialSpecies

/-- Actual original optimizer representations near one coefficient base have identical amplitude/rate unknowns. No stationarity or uniqueness premise is assumed. -/
theorem polynomial_scalarMinimizer_uniform_branch_unique
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0) (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)

    (K : Set PolynomialScaledCoefficients) (hK : IsCompact K)
    (M : ℝ) (hσK : ∀ c ∈ K, |c.2.2.2| ≤ M) (j : Fin 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ c ∈ K, ∀ d ∈ K,
      PolynomialScaledOptimizerData U ψ h c →
      PolynomialScaledOptimizerData U ψ h d →
      dist ((c.1, c.2.1), c.2.2.1) (polynomialQuarticCriticalBase j) < δ →
      dist ((d.1, d.2.1), d.2.2.1) (polynomialQuarticCriticalBase j) < δ →
      ((c.1, c.2.1), c.2.2.1) = ((d.1, d.2.1), d.2.2.1) := by
  obtain ⟨O, hO, h0O, _hOU, hcritical⟩ :=
    polynomial_scalarMinimizer_scaled_critical hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst
  obtain ⟨δO, hδO, htube⟩ := compact_zero_slice_tube hK hO (fun c _hc => h0O c)
  obtain ⟨δI, hδI, huniq⟩ := polynomial_actual_factor_uniform_local_unique
    hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst
    (Set.Icc (-M) M) isCompact_Icc j
  refine ⟨min δO δI, lt_min hδO hδI, ?_⟩
  intro h hh hsmall c hc d hd hdc hdd hnearC hnearD
  obtain ⟨bc, ρc, hsc, hrc, hGc, hmc, _hpc, hρc⟩ := hdc
  obtain ⟨bd, ρd, hsd, hrd, hGd, hmd, _hpd, hρd⟩ := hdd
  have hfield : |h| < δO := by
    rw [abs_of_pos hh]
    exact hsmall.trans_le (min_le_left _ _)
  have hcc := hcritical h c.2.2.2 ((c.1, c.2.1), c.2.2.1) bc ρc
    hh.ne' (htube h hfield c hc) hsc hrc hGc hmc hρc
  have hcd := hcritical h d.2.2.2 ((d.1, d.2.1), d.2.2.1) bd ρd
    hh.ne' (htube h hfield d hd) hsd hrd hGd hmd hρd
  have hσeq : d.2.2.2 = c.2.2.2 :=
    mul_left_cancel₀ (pow_ne_zero 4 hh.ne') (hsd.trans hsc.symm)
  rw [hσeq] at hcd
  exact huniq h c.2.2.2 ((c.1, c.2.1), c.2.2.1) ((d.1, d.2.1), d.2.2.1)
    (by rw [abs_of_pos hh]; exact hsmall.trans_le (min_le_right _ _))
    (abs_le.mp (hσK c hc))
    (hnearC.trans_le (min_le_right _ _)) (hnearD.trans_le (min_le_right _ _)) hcc hcd

end DGPS.Examples.PolynomialSpecies
