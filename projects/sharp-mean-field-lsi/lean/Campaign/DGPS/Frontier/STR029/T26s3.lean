import DGPS.Frontier.STR029.T62

/-!
# STR029.26-s3: chart densities in the absolute variational domain

## Provides

* `s3a_exists_abs_of_chart_STR02926`: an absolute density representing any concrete
  `C^{2,1/2}` chart, pointwise on the angular circle.
* `s3b_chart_invariants_STR02926`: entropy and Fisher information of any absolute
  density with the chart representation almost everywhere.
* `s3c_chart_density_not_ae_STR02926`: distinct chart density functions yield
  absolute densities that differ on a set of positive Haar measure.

## R5 notes

The three signatures are those of the saved STR029.26 split plan. The construction
uses the existing angular square-root lift and absolute-domain correspondence.
Entropy and Fisher identification use the existing invariance under almost-everywhere
changes from STR029.62. Fisher information retains the physical factor
`DGPS.Circle.AngularNormalization.a0`. No normalization of the chart mean is assumed.
For distinctness, continuity is established after descending each periodic density
to the angular circle, and Haar positivity upgrades almost-everywhere equality to
pointwise equality. Periodic lifts then recover equality on the whole real line.
-/

open Filter Topology
open MeasureTheory Set
open DGPS.Circle.AngularNormalization
open scoped ENNReal
open DGPS DGPS.Examples.ThreeSpeciesCircle

namespace DGPS.Frontier.STR029

theorem s3a_exists_abs_of_chart_STR02926 (h : ℝ) {u : ℝ → ℝ}
    (hu : IsC2Alpha_STR02901 (1 / 2) u) :
    ∃ ρ : AbsoluteDensity 1,
      ∀ θ : AngCircle, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u (angSec θ) := by
  obtain ⟨ρ, hρ⟩ := exists_abs_of_angDomain_STR02901 h (angDomain_gLift_STR02962 h hu)
  refine ⟨ρ, fun θ => ?_⟩
  rw [density_eq_gAng_sq_STR02901 h ρ, angEquiv.apply_symm_apply, hρ]
  change gLift_STR02962 h u θ ^ 2 * qAng_STR02901 h θ = _
  exact gLift_sq_STR02962 h hu.2.1.continuous θ

theorem s3b_chart_invariants_STR02926 (h : ℝ) {u : ℝ → ℝ}
    (hu : IsC2Alpha_STR02901 (1 / 2) u) (ρ : AbsoluteDensity 1)
    (hρ : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u (angSec θ)) :
    ordinaryEntropy h ρ = ENNReal.ofReal (entropyChart_STR02949 h u) ∧
      ordinaryFisher h ρ = ENNReal.ofReal DGPS.Circle.AngularNormalization.a0 *
        ENNReal.ofReal (fisherChart_STR02949 h u) := by
  have hae := gAng_ae_eq_gLift_STR02962 h ρ hu.2.1.continuous hρ
  constructor
  · rw [ordinaryEntropy_eq_angEntropy_STR02901, angEntropy_congr_STR02962 h hae,
      angEntropy_gLift_STR02962 h hu.2.1.continuous]
  · rw [ordinaryFisher_eq_angFisher_STR02901, angFisher_congr_STR02962 h hae,
      angFisher_gLift_STR02962 h hu]

theorem s3c_chart_density_not_ae_STR02926 (h : ℝ) {u u' : ℝ → ℝ}
    (hu : IsC2Alpha_STR02901 (1 / 2) u) (hu' : IsC2Alpha_STR02901 (1 / 2) u')
    (hne : rhoT_STR02901 h u ≠ rhoT_STR02901 h u') (ρ ρ' : AbsoluteDensity 1)
    (hρ : ∀ θ : AngCircle, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u (angSec θ))
    (hρ' : ∀ θ : AngCircle, ρ'.density (angEquiv.symm θ) = rhoT_STR02901 h u' (angSec θ)) :
    ¬ ρ.density =ᵐ[haar 1] ρ'.density := by
  intro hae
  have hd : (fun θ => ρ.density (angEquiv.symm θ)) =ᵐ[angHaar]
      (fun θ => ρ'.density (angEquiv.symm θ)) :=
    (ae_comp_angEquiv_iff).1 (by
      filter_upwards [hae] with x hx
      simpa only [angEquiv.symm_apply_apply] using hx)
  have hchart : (fun θ => rhoT_STR02901 h u (angSec θ)) =ᵐ[angHaar]
      (fun θ => rhoT_STR02901 h u' (angSec θ)) := by
    filter_upwards [hd] with θ hθ
    rw [← hρ θ, ← hρ' θ]
    exact hθ
  have hp := periodic_rho_STR02950 h hu.1
  have hp' := periodic_rho_STR02950 h hu'.1
  have hc : Continuous (fun θ => rhoT_STR02901 h u (angSec θ)) := by
    change Continuous (AddCircle.liftIoc (2 * Real.pi) 0 (rhoT_STR02901 h u))
    exact AddCircle.liftIoc_zero_continuous (by simpa using (hp 0).symm)
      (continuous_rho_STR02950 h hu.2.1.continuous).continuousOn
  have hc' : Continuous (fun θ => rhoT_STR02901 h u' (angSec θ)) := by
    change Continuous (AddCircle.liftIoc (2 * Real.pi) 0 (rhoT_STR02901 h u'))
    exact AddCircle.liftIoc_zero_continuous (by simpa using (hp' 0).symm)
      (continuous_rho_STR02950 h hu'.2.1.continuous).continuousOn
  have heq := MeasureTheory.Measure.eq_of_ae_eq hchart hc hc'
  have hl : ∀ θ : AngCircle, hp.lift θ = rhoT_STR02901 h u (angSec θ) := by
    intro θ
    rw [← hp.lift_coe (angSec θ), coe_angSec_STR02962]
  have hl' : ∀ θ : AngCircle, hp'.lift θ = rhoT_STR02901 h u' (angSec θ) := by
    intro θ
    rw [← hp'.lift_coe (angSec θ), coe_angSec_STR02962]
  have hL : hp.lift = hp'.lift := funext fun θ =>
    (hl θ).trans ((congrFun heq θ).trans (hl' θ).symm)
  apply hne
  funext t
  simpa only [Function.Periodic.lift_coe] using congrFun hL (t : AngCircle)

end DGPS.Frontier.STR029
