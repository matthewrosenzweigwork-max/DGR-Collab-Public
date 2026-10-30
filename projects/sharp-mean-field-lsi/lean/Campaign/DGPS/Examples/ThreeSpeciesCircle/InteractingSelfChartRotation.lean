import DGPS.Examples.ThreeSpeciesCircle.InteractingHolderRotation
import DGPS.Examples.ThreeSpeciesCircle.InteractingChartTurn

/-! Actual self-feedback chart covariance from the native ALL-Abs feedback
identities. No optimizer, selected graph symmetry or invariant IFT domain is
an input. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization DGPS.Circle.VonMisesParity

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The canonical density of the turned chart is the physical law turn. -/
theorem interactingChartAbsolute_thirdTurn_density (h : ℝ) (j : Fin 3)
    (u : PeriodicC2_STR02969) (x : Torus 1) :
    (interactingChartAbsolute h (interactingC2Translate (2 * Real.pi * ((j : ℕ) / 3)) u)).density x =
      (interactingDensityTranslate (pt ((j : ℕ) / 3)) (interactingChartAbsolute h u)).density x := by
  have hc (v : PeriodicC2_STR02969) (y : Torus 1) :
      (interactingChartAbsolute h v).density y =
        (rho_STR02954 (h, e0_STR02955 v)).val (angSec (angEquiv y)) := by
    simpa only [angEquiv.symm_apply_apply, rho_val_STR02954, e0_val_STR02955] using
      interactingChartAbsolute_density h v (angEquiv y)
  rw [hc, interactingDensityTranslate_density, hc, interactingC2Translate_rho]
  exact interactingHolderTranslate_native ((j : ℕ) / 3) (rho_STR02954 (h, e0_STR02955 u)) x

/-- Compact form of the already identified physical gradient, retaining both
changing-law feedback means. -/
theorem interactingChartGradient_native_holder {h : ℝ} (hh : 0 < h)
    (u : PeriodicC2_STR02969) (ρ : AbsoluteDensity 1)
    (hρ : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u.val (angSec θ))
    (γ ε : ℝ) :
    interactingChartGradient h (ε, γ, u) = Gfun_STR02955 h γ u + a0⁻¹ •
      (rho_STR02954 (h, e0_STR02955 u) *
        (elementaryEulerHolder h ε (a0 * (1 + γ)) ρ -
          (2 * ε * elementaryC h (a0 * (1 + γ)) ρ + 3 * ε ^ 2 * elementaryJ h ρ) •
            (1 : PeriodicHolder_STR02968))) := by
  apply ext_STR02954
  funext t
  rw [interactingChartGradient_native hh u ρ hρ γ ε t]
  simp only [PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_smul,
    PeriodicHolder_STR02968.val_sub, val_mul_STR02954, val_one_STR02954,
    Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul,
    Gfun_val_STR02955, rho_val_STR02954, e0_val_STR02955]
  rw [elementaryEulerHolder_native hh]
  unfold elementaryEulerCorrection
  ring

/-- Covariance of the actual self-feedback gradient, at the same rate. -/
theorem interactingChartGradient_interactingThirdTurn {h : ℝ} (hh : 0 < h)
    (γ ε : ℝ) (j : Fin 3) (u : PeriodicC2_STR02969) :
    interactingChartGradient h
        (ε, γ, interactingC2Translate (2 * Real.pi * ((j : ℕ) / 3)) u) =
      interactingHolderTranslate (2 * Real.pi * ((j : ℕ) / 3))
        (interactingChartGradient h (ε, γ, u)) := by
  let ρ := interactingChartAbsolute h u
  let τ := interactingDensityTranslate (pt ((j : ℕ) / 3)) ρ
  let v := interactingC2Translate (2 * Real.pi * ((j : ℕ) / 3)) u
  have hρ : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u.val (angSec θ) :=
    Eventually.of_forall (interactingChartAbsolute_density h u)
  have hτ : ∀ᵐ θ ∂angHaar, τ.density (angEquiv.symm θ) = rhoT_STR02901 h v.val (angSec θ) := by
    exact Eventually.of_forall fun θ =>
      (interactingChartAbsolute_thirdTurn_density h j u (angEquiv.symm θ)).symm.trans
        (interactingChartAbsolute_density h v θ)
  rw [interactingChartGradient_native_holder hh v τ hτ,
    interactingChartGradient_native_holder hh u ρ hρ,
    interactingC2Translate_Gfun, interactingC2Translate_rho,
    elementaryEulerHolder_interactingThirdTurn hh,
    elementaryC_interactingThirdTurn, elementaryJ_interactingThirdTurn]
  apply ext_STR02954
  funext t
  rfl

/-- Actual deficit invariance retains all native nonlinear terms. -/
theorem interactingChartDeficit_interactingThirdTurn {h : ℝ} (hh : 0 < h)
    (γ ε : ℝ) (j : Fin 3) (u : PeriodicC2_STR02969) :
    interactingChartDeficit h (ε, γ, interactingC2Translate (2 * Real.pi * ((j : ℕ) / 3)) u) =
      interactingChartDeficit h (ε, γ, u) := by
  let ρ := interactingChartAbsolute h u
  let τ := interactingDensityTranslate (pt ((j : ℕ) / 3)) ρ
  let v := interactingC2Translate (2 * Real.pi * ((j : ℕ) / 3)) u
  have hτ : ∀ᵐ θ ∂angHaar, τ.density (angEquiv.symm θ) = rhoT_STR02901 h v.val (angSec θ) := by
    exact Eventually.of_forall fun θ =>
      (interactingChartAbsolute_thirdTurn_density h j u (angEquiv.symm θ)).symm.trans
        (interactingChartAbsolute_density h v θ)
  have hv := interactingChartDeficit_native hh γ ε v τ hτ
  have hu := interactingChartAbsolute_deficit hh γ ε u
  rw [ordinaryFisher_interactingThirdTurn, ordinaryEntropy_interactingThirdTurn,
    elementaryC_interactingThirdTurn, elementaryJ_interactingThirdTurn] at hv
  have ha0 : a0 ≠ 0 := by unfold a0; positivity
  exact mul_left_cancel₀ ha0 (hv.trans hu.symm)

end DGPS.Examples.ThreeSpeciesCircle
