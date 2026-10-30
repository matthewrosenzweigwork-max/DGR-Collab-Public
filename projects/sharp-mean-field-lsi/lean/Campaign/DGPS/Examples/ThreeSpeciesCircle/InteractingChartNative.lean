import DGPS.Examples.ThreeSpeciesCircle.InteractingChartCalculus
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootNativeMoments

/-! Actual physical entropy/information identification in the retained angular
chart, for every represented absolute H1 density. These identities supply the
ordinary part of the nonlinear native chart bridge, without optimizer assumptions. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Both native ordinary terms have their exact angular chart values on the
full represented absolute-density domain, with the physical Fisher factor a0. -/
theorem interactingChart_native_ordinary_terms (h : ℝ) (u : PeriodicC2_STR02969)
    (ρ : AbsoluteDensity 1)
    (hρ : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u.val (angSec θ)) :
    (ordinaryEntropy h ρ).toReal = entropyChart_STR02949 h u.val ∧
      (ordinaryFisher h ρ).toReal = a0 * fisherChart_STR02949 h u.val := by
  have hc : Continuous u.val := u.isC2.2.1.continuous
  have hae := gAng_ae_eq_gLift_STR02962 h ρ hc hρ
  have hH : angEntropy_STR02901 h (gAng_STR02901 h ρ) = entropyChart_STR02949 h u.val :=
    (angEntropy_congr_STR02962 h hae).trans (angEntropy_gLift_STR02962 h hc)
  have hI : angFisher_STR02901 h (gAng_STR02901 h ρ) =
      ENNReal.ofReal (fisherChart_STR02949 h u.val) :=
    (angFisher_congr_STR02962 h hae).trans (angFisher_gLift_STR02962 h u.isC2)
  constructor
  · rw [ordinaryEntropy_eq_angEntropy_STR02901, hH,
      ENNReal.toReal_ofReal (by rw [← hH]; exact angEntropy_gAng_nonneg_STR02901 h ρ)]
  · calc
      _ = DGPS.Circle.AngularNormalization.a0 * fisherChart_STR02949 h u.val := by
        rw [ordinaryFisher_eq_angFisher_STR02901, hI, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal DGPS.Circle.AngularNormalization.a0_pos.le,
          ENNReal.toReal_ofReal (fisherChart_nonneg_STR02962 h hc)]
      _ = _ := by rfl

/-- The zero-coupling chart deficit is the actual physical native deficit,
including the exact rate conversion r=a0*(1+gamma). -/
theorem interactingChartDeficit_zero_native (h γ : ℝ) (u : PeriodicC2_STR02969)
    (ρ : AbsoluteDensity 1)
    (hρ : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u.val (angSec θ)) :
    a0 * interactingChartDeficit h (0, γ, u) =
      (ordinaryFisher h ρ).toReal - 2 * (a0 * (1 + γ)) * (ordinaryEntropy h ρ).toReal := by
  obtain ⟨hH, hI⟩ := interactingChart_native_ordinary_terms h u ρ hρ
  rw [interactingChartDeficit_zero, JC2_eq_STR02956, hH, hI]
  unfold Jchart_STR02950
  ring

/-- The full written angular chart deficit equals the actual physical scalar
native deficit, retaining all nonlinear force terms and the full AE H1 domain. -/
theorem interactingChartDeficit_native {h : ℝ} (hh : 0 < h) (γ ε : ℝ)
    (u : PeriodicC2_STR02969) (ρ : AbsoluteDensity 1)
    (hρ : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u.val (angSec θ)) :
    a0 * interactingChartDeficit h (ε, γ, u) =
      (ordinaryFisher h ρ).toReal - 2 * (a0 * (1 + γ)) * (ordinaryEntropy h ρ).toReal +
        ε * elementaryC h (a0 * (1 + γ)) ρ + ε ^ 2 * elementaryJ h ρ := by
  have hbase := interactingChartDeficit_zero_native h γ u ρ hρ
  rw [interactingChartDeficit_zero] at hbase
  have hcor := interactingChartDeficit_native_corrections hh u ρ hρ γ ε
  nlinarith only [hbase, hcor]

/-- A genuine absolute H1 density attached to every retained C2-Holder chart.
Its admissibility is supplied by the existing angular construction. -/
def interactingChartAbsolute (h : ℝ) (u : PeriodicC2_STR02969) : AbsoluteDensity 1 :=
  absOfAng_STR02901 h (gLift_STR02962 h u.val) (angDomain_gLift_STR02962 h u.isC2)

theorem interactingChartAbsolute_density (h : ℝ) (u : PeriodicC2_STR02969) (θ : AngCircle) :
    (interactingChartAbsolute h u).density (angEquiv.symm θ) =
      rhoT_STR02901 h u.val (angSec θ) := by
  change (gLift_STR02962 h u.val (angEquiv (angEquiv.symm θ)) *
    Real.sqrt (referenceDensity h (angEquiv.symm θ))) ^ 2 = _
  rw [angEquiv.apply_symm_apply, mul_pow,
    Real.sq_sqrt (referenceDensity_pos (h := h) (angEquiv.symm θ)).le]
  exact gLift_sq_STR02962 h u.isC2.2.1.continuous θ

/-- The actual canonical density factory realizes the full physical deficit,
so native admissibility and chart representation are not external premises. -/
theorem interactingChartAbsolute_deficit {h : ℝ} (hh : 0 < h) (γ ε : ℝ)
    (u : PeriodicC2_STR02969) :
    a0 * interactingChartDeficit h (ε, γ, u) =
      (ordinaryFisher h (interactingChartAbsolute h u)).toReal -
        2 * (a0 * (1 + γ)) * (ordinaryEntropy h (interactingChartAbsolute h u)).toReal +
        ε * elementaryC h (a0 * (1 + γ)) (interactingChartAbsolute h u) +
        ε ^ 2 * elementaryJ h (interactingChartAbsolute h u) :=
  interactingChartDeficit_native hh γ ε u (interactingChartAbsolute h u)
    (Eventually.of_forall (interactingChartAbsolute_density h u))

end DGPS.Examples.ThreeSpeciesCircle
