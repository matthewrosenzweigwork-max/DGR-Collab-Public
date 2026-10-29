import LeanResearch.PeriodicAttractiveLogGas.OccupationCoercivity

/-! Source prop:occupation-PI (2093--2121). This interface retains the actual
central conditional mean and original outer graph. The only unresolved
analytic input is the literal far-imbalance hypothesis. No entropy estimate
is used in the proof. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.OccupationPoincare
open MeshCells LabelOccupations DiscreteOccupationIdentities ConditionalLawEstimates
open OccupationCoordinates OccupationCentralLogGradient OccupationAbsoluteMass

variable {J N : ℕ} {t β β₀ cFar : ℝ}

/-- The source center is the actual mean under the conditional original
occupation weights on the fixed central box. -/
def center (hJ : 0 < J) (β β₀ : ℝ) (F : OccupationState J N t → ℝ) : ℝ :=
  FiniteBoxPoincare.mean (FiniteEntropyLocalization.conditionalWeight (occupationWeight hJ β)
    (OccupationCentralPoincare.centralBall J N t (OccupationCoercivity.chosenRadius J β₀))) F

/-- The existing uniform threshold also supplies the literal path buffer
N ≥ 2/t required later in the label variance decomposition. -/
theorem threshold_gates (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ht : 0 < t)
    (hlarge : OccupationCoercivity.particleThreshold J β₀ t cFar ≤ N) :
    8*J^2 ≤ N ∧ 2 ≤ N ∧ 2/t ≤ (N : ℝ) ∧ 1 ≤ (t-t/2)*N := by
  have hbox := (le_max_left _ _).trans hlarge
  have hcentral := (le_max_left _ _).trans hbox
  have hnear : OccupationNearImbalance.particleThreshold J β₀ t ≤ N :=
    (le_max_left _ _).trans hcentral
  have hb := OccupationNearImbalance.particleThreshold_bounds hβ₀ hsub ht hnear
  have hbuffer : OccupationBufferPoincare.bufferThreshold t ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hh := (OccupationBufferPoincare.bufferThreshold_gates ht hbuffer).1
  refine ⟨hb.2.2.1, hb.2.2.2.1, ?_, ?_⟩
  · exact (div_le_iff₀ ht).mpr (by nlinarith only [hh])
  · nlinarith only [hh]

theorem central_mass_pos (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (hJ : 0 < J) (hsmall : 1/(J^2:ℕ) < t/8)
    (hlarge : OccupationCoercivity.particleThreshold J β₀ t cFar ≤ N) :
    0 < FiniteEntropyLocalization.setMass (occupationWeight hJ β)
      (OccupationCentralPoincare.centralBall J N t (OccupationCoercivity.chosenRadius J β₀)) := by
  classical
  have hb := threshold_gates (hβ.trans hβ₀) hsub ht hlarge
  let m : OccupationState J N t := roundedState hJ hb.1 hsmall
  apply FiniteEntropyLocalization.setMass_pos _ _
    (LabelGroundState.occupationWeight_pos hJ hb.2.1 hβ (hβ₀.trans_lt hsub))
  refine ⟨m, ?_⟩
  simp only [OccupationCentralPoincare.centralBall, OccupationAbsoluteMass.coordinateBall,
    Finset.mem_filter, Finset.mem_univ, true_and]
  intro i
  have he : stateCoordinates m i = interior (cumulative (rounded J N)) i := rfl
  rw [he, sub_self, Int.cast_zero, abs_zero]
  exact mul_nonneg (OccupationCoercivity.chosenRadius_nonneg J β₀) (Real.sqrt_nonneg _)

local instance : DecidablePred (fun m : OccupationState J N t =>
    m.val ∈ cappedOccupations J N (t/2)) := fun _ => Classical.propDecidable _

/-- Actual source occupation PI, with its unchanged exterior error and
specified central-box mean. All cutoff, ground-state and local PI inputs
are discharged by the already proved variance route. -/
theorem occupation_poincare_of_far
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t ≤ occupationBound β₀)
    (hmesh : 8*(radius β₀+4) ≤ J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀ ≤ J)
    (hsmall : 1/(J^2:ℕ) < t/8) (hcFar : 0 < cFar)
    (hlarge : OccupationCoercivity.particleThreshold J β₀ t cFar ≤ N)
    (hfar : OccupationCoercivity.FarImbalance (N := N) (t := t) (mesh_pos hmesh) β β₀ cFar)
    (F : OccupationState J N t → ℝ) :
    let c := center (mesh_pos hmesh) β β₀ F
    (∑ m, occupationWeight (mesh_pos hmesh) β m * (F m-c)^2) ≤
      OccupationCoercivity.bufferConstant J β₀ * occupationEnergy (mesh_pos hmesh) β F +
      2*(∑ m, if m.val ∈ cappedOccupations J N (t/2) then 0
        else occupationWeight (mesh_pos hmesh) β m * (F m-c)^2) := by
  exact OccupationCoercivity.source_buffer_poincare_of_far hβ hβ₀ hsub ht htC hmesh
    hnearJ hsmall hcFar hlarge hfar F

end PeriodicAttractiveLogGas.OccupationPoincare
