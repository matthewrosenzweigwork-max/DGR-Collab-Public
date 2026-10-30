import DGPS.Examples.ThreeSpeciesCircle.InteractingChartLogProfile
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarLogEuler

/-! Physical-to-angular Euler transport on the actual retained chart. The final
factory applies to EVERY original-H1 minimizer with any actual AE chart
representation; it assumes no Euler or gradient-zero condition. -/

noncomputable section
open MeasureTheory Filter
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem angular_point (t : ℝ) :
    angEquiv.symm (t : AngCircle) = pt (t / (2 * Real.pi)) := by
  rw [MeasurableEquiv.symm_apply_eq, angEquiv_apply]
  change (t : AngCircle) = angRescale ((t / (2 * Real.pi) : ℝ) : UnitAddCircle)
  rw [angRescale_mk]
  congr 1
  field_simp

/-- Deterministic physical-to-angular transport. The full actual normalization
constant and both nonlinear feedbacks are retained. -/
theorem interactingChart_logResidual_zero_of_physicalEuler (h γ ε : ℝ)
    (u : PeriodicC2_STR02969) (ρ : AbsoluteDensity 1)
    {v : Torus 1 → ℝ} (hv : Continuous v) (hvrep : ρ.sqrt =ᵐ[haar 1] v)
    (hρ : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u.val (angSec θ))
    (hphysical : let L := fun s : ℝ => Real.log (v (pt s) ^ 2) - ellT h (pt s);
      ∀ s : ℝ, -2 * deriv (deriv L) s - (deriv L s) ^ 2 -
        2 * sigT h (pt s) * deriv L s - 2 * (a0 * (1 + γ)) * L s +
          elementaryEulerCorrection h ε (a0 * (1 + γ)) ρ (pt s) -
            elementaryEulerMultiplier h ε (a0 * (1 + γ)) ρ = 0) :
    ∀ t : ℝ, elementaryAngularLogResidual h γ ε u ρ t = 0 := by
  let p := 2 * Real.pi
  have hp : p ≠ 0 := by dsimp only [p]; positivity
  let L := fun s : ℝ => Real.log (v (pt s) ^ 2) - ellT h (pt s)
  have hprofile : (fun t : ℝ => L (p⁻¹ * t)) =
      fun t => u.val t + elementaryChartLogConstant h u := by
    simpa only [L, p, div_eq_inv_mul] using interactingChart_continuous_logProfile h u ρ hv hvrep hρ
  have hd1 : ∀ t : ℝ, p⁻¹ * deriv L (p⁻¹ * t) = deriv u.val t := by
    intro t
    have ht := congrArg (fun f : ℝ → ℝ => deriv f t) hprofile
    rw [deriv_dil_STR02901, deriv_add_const] at ht
    exact ht
  have hd2 : ∀ t : ℝ, p⁻¹ * (p⁻¹ * deriv (deriv L) (p⁻¹ * t)) =
      deriv (deriv u.val) t := by
    intro t
    have ht := congrArg (fun f : ℝ → ℝ => deriv (deriv f) t) hprofile
    rw [deriv2_dil_STR02901, deriv_add_const'] at ht
    exact ht
  intro t
  have h1 : deriv L (p⁻¹ * t) = p * deriv u.val t := by
    calc
      _ = p * (p⁻¹ * deriv L (p⁻¹ * t)) := by field_simp [hp]
      _ = _ := by rw [hd1]
  have h2 : deriv (deriv L) (p⁻¹ * t) = p * (p * deriv (deriv u.val) t) := by
    calc
      _ = p * (p * (p⁻¹ * (p⁻¹ * deriv (deriv L) (p⁻¹ * t)))) := by field_simp [hp]
      _ = _ := by rw [hd2]
  have ht := hphysical (p⁻¹ * t)
  change -2 * deriv (deriv L) (p⁻¹ * t) - (deriv L (p⁻¹ * t)) ^ 2 -
    2 * sigT h (pt (p⁻¹ * t)) * deriv L (p⁻¹ * t) -
      2 * (a0 * (1 + γ)) * L (p⁻¹ * t) +
        elementaryEulerCorrection h ε (a0 * (1 + γ)) ρ (pt (p⁻¹ * t)) -
          elementaryEulerMultiplier h ε (a0 * (1 + γ)) ρ = 0 at ht
  have hs : sigT h (pt (p⁻¹ * t)) = -(6 * Real.pi) * h * Real.sin (3 * t) := by
    rw [sigT_lift]
    unfold sg0
    have hangle : 6 * Real.pi * (p⁻¹ * t) = 3 * t := by
      dsimp only [p]
      field_simp
      <;> ring
    rw [hangle]
  have hpoint : pt (p⁻¹ * t) = angEquiv.symm (t : AngCircle) := by
    simpa only [p, div_eq_inv_mul] using (angular_point t).symm
  rw [h1, h2, hs, congrFun hprofile t, hpoint] at ht
  unfold elementaryAngularLogResidual
  dsimp only [p] at ht
  unfold a0 at *
  nlinarith [ht]

/-- Actual full-original-H1 minimizers satisfy the written chart gradient
equation in EVERY AE C2 representation. Neither stationarity nor the physical
deficit identity is an input to this actual-model factory. -/
theorem elementaryModel_scalarMinimizer_chartGradient_zero (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
          ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (modelData h ε) ρ →
            scalarQuotient (modelData h ε) b ρ = scalarRate (modelData h ε) b →
            ∀ u : PeriodicC2_STR02969,
              (∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u.val (angSec θ)) →
              interactingChartGradient h (ε, (scalarRate (modelData h ε) b).toReal / a0 - 1, u) = 0 := by
  obtain ⟨δ, hδ, hδr, hEuler⟩ := elementaryModel_scalarMinimizer_logEuler D
  refine ⟨δ, hδ, hδr, fun h hh hsmall => ?_⟩
  obtain ⟨ε0, m, hε0, hεmax, _, hm⟩ := hEuler h hh hsmall
  refine ⟨ε0, hε0, hεmax, fun ε hε he b ρ hG hmin u hρ => ?_⟩
  obtain ⟨v, hv, hvrep, _, _, hphysical⟩ := hm ε hε he b ρ hG hmin
  let r := (scalarRate (modelData h ε) b).toReal
  let γ := r / a0 - 1
  have ha : a0 ≠ 0 := by unfold a0; positivity
  have hr : a0 * (1 + γ) = r := by dsimp only [γ]; field_simp [ha]; ring
  have hR : ∀ t : ℝ, elementaryAngularLogResidual h γ ε u ρ t = 0 := by
    apply interactingChart_logResidual_zero_of_physicalEuler h γ ε u ρ hv.continuous_torus hvrep hρ
    simpa only [hr] using hphysical
  have hF : (ordinaryFisher h ρ).toReal -
      2 * (a0 * (1 + γ)) * (ordinaryEntropy h ρ).toReal +
        ε * elementaryC h (a0 * (1 + γ)) ρ + ε ^ 2 * elementaryJ h ρ = 0 := by
    rw [hr]
    exact elementaryModel_scalarMinimizer_deficit_zero hh hε (he.trans_le hεmax) b ρ hG hmin
  apply ext_STR02954
  funext t
  have ht := interactingChartGradient_logResidual hh u ρ hρ γ ε t
  rw [hR t, hF] at ht
  have hz : a0 * (interactingChartGradient h (ε, γ, u)).val t = 0 := by simpa using ht
  exact (mul_eq_zero.mp hz).resolve_left ha

end DGPS.Examples.ThreeSpeciesCircle
