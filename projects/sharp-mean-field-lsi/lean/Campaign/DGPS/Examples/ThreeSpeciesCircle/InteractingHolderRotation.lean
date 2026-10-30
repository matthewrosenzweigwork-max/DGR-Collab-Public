import DGPS.Examples.ThreeSpeciesCircle.InteractingHolderFeedback
import DGPS.Examples.ThreeSpeciesCircle.InteractingExternalRotation

/-! The actual nonlinear common feedback transforms in the SAME Holder
parameter space as the external IFT. This is factual covariance on ALL absolute
densities, before identifying any family common field by stationarity. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization DGPS.Circle.VonMisesParity

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Literal Holder-space covariance of the existing actual common Euler field.
There is no chart, minimizer, family-stationarity or optimizer premise. -/
theorem elementaryEulerHolder_interactingThirdTurn {h : ℝ} (hh : 0 < h) (ε r : ℝ)
    (j : Fin 3) (ρ : AbsoluteDensity 1) :
    elementaryEulerHolder h ε r (interactingDensityTranslate (pt ((j : ℕ) / 3)) ρ) =
      interactingHolderTranslate (2 * Real.pi * ((j : ℕ) / 3)) (elementaryEulerHolder h ε r ρ) := by
  let a := pt ((j : ℕ) / 3)
  let τ := interactingDensityTranslate a ρ
  have hv (σ : AbsoluteDensity 1) (x : Torus 1) :
      (elementaryEulerHolder h ε r σ).val (angSec (angEquiv x)) = elementaryEulerCorrection h ε r σ x := by
    have he := elementaryEulerHolder_native hh ε r σ (angSec (angEquiv x))
    simpa only [coe_angSec_STR02962, angEquiv.symm_apply_apply] using he
  have hc (x : Torus 1) : (elementaryEulerHolder h ε r τ).val (angSec (angEquiv x)) =
      (interactingHolderTranslate (2 * Real.pi * ((j : ℕ) / 3))
        (elementaryEulerHolder h ε r ρ)).val (angSec (angEquiv x)) := by
    calc
      _ = elementaryEulerCorrection h ε r τ x := hv τ x
      _ = elementaryEulerCorrection h ε r ρ (x - a) := by
        simpa only [a, sub_add_cancel] using
          elementaryEulerCorrection_interactingThirdTurn h ε r j ρ (x - a)
      _ = (elementaryEulerHolder h ε r ρ).val (angSec (angEquiv (x - a))) := (hv ρ (x - a)).symm
      _ = _ := (interactingHolderTranslate_native ((j : ℕ) / 3) (elementaryEulerHolder h ε r ρ) x).symm
  apply ext_STR02954
  funext t
  have hread (F : PeriodicHolder_STR02968) : F.val (angSec (t : AngCircle)) = F.val t := by
    apply eq_of_circDist_eq_zero_STR02968 F.isPerHolder.1
    unfold circDist_STR02968
    rw [coe_angSec_STR02962]
    exact dist_self _
  have he := hc (angEquiv.symm (t : AngCircle))
  simpa only [angEquiv.apply_symm_apply, hread] using he

end DGPS.Examples.ThreeSpeciesCircle
