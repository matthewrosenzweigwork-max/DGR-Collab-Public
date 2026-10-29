import LeanResearch.PeriodicAttractiveLogGas.FibreProjection

/-! The actual occupation ground state and its lift to the original outer
label graph. Source eq:occupation-test-function, eq:occupation-ground-state,
eq:occupation-W-exact and eq:label-ground-state (lines 2011–2035, 3086–3091).
No occupation drift or functional inequality is assumed in these identities. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace PeriodicAttractiveLogGas.LabelGroundState

open MeshCells CellRestrictions LabelOccupations DiscreteOccupationIdentities FibreProjection

variable {J N : ℕ} {t β : ℝ}

theorem occupationWeight_pos (hJ : 0 < J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) (m : OccupationState J N t) :
    0 < occupationWeight hJ β m := by
  have hc : 0 < multiplicity m := by
    rw [← card_profile_fiber]
    exact fibre_card_pos m
  rw [occupationWeight_eq]
  exact mul_pos (Nat.cast_pos.mpr hc) (qWeight_pos hJ hN hβ hsub m)

/-- The source V is defined on the entire original occupation graph. -/
def occupationV (hJ : 0 < J) (β : ℝ) (m : OccupationState J N t) : ℝ :=
  (Real.sqrt (occupationWeight hJ β m))⁻¹

def occupationW (hJ : 0 < J) (β : ℝ) (m : OccupationState J N t) : ℝ :=
  FiniteGraph.groundStatePotential (occupationRate hJ β) (occupationV hJ β) m

theorem occupationV_pos (hJ : 0 < J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) (m : OccupationState J N t) :
    0 < occupationV hJ β m :=
  inv_pos.mpr (Real.sqrt_pos.mpr (occupationWeight_pos hJ hN hβ hsub m))

/-- Literal generator intertwining, including suppressed outer-cap moves. -/
theorem generator_profile (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (β : ℝ) (F : OccupationState J N t → ℝ) (η : LabelState J N t) :
    FiniteGraph.generator (labelRate hJ β) (F ∘ profile) η =
      FiniteGraph.generator (occupationRate hJ β) F (profile η) := by
  classical
  unfold FiniteGraph.generator
  simp only [Function.comp_apply]
  rw [sum_weighted_fibers profile (labelRate hJ β η)
    (fun m' => F m' - F (profile η))]
  simp_rw [sum_labelRate_profile hJ hJ2 β η]

theorem groundStatePotential_profile (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (β : ℝ) (V : OccupationState J N t → ℝ) (η : LabelState J N t) :
    FiniteGraph.groundStatePotential (labelRate hJ β) (V ∘ profile) η =
      FiniteGraph.groundStatePotential (occupationRate hJ β) V (profile η) := by
  unfold FiniteGraph.groundStatePotential
  rw [generator_profile hJ hJ2]
  rfl

/-- Exact occupation identity with its actual unnormalized Gibbs weights. -/
theorem occupation_ground_state_identity (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) (F : OccupationState J N t → ℝ) :
    occupationEnergy hJ β F -
        ∑ m, occupationWeight hJ β m * F m ^ 2 * occupationW hJ β m =
      (1 / 2 : ℝ) * ∑ m, ∑ m',
        occupationWeight hJ β m * occupationRate hJ β m m' *
          occupationV hJ β m * occupationV hJ β m' *
            (F m / occupationV hJ β m - F m' / occupationV hJ β m') ^ 2 := by
  exact FiniteGraph.groundState_identity _ _ (occupation_detailed_balance hJ hJ2 β) _
    (occupationV_pos hJ hN hβ hsub) F

theorem occupation_ground_state_coercivity (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) (F : OccupationState J N t → ℝ) :
    (∑ m, occupationWeight hJ β m * F m ^ 2 * occupationW hJ β m) ≤
      occupationEnergy hJ β F := by
  exact FiniteGraph.groundState_coercivity _ _
    (fun m => (occupationWeight_pos hJ hN hβ hsub m).le)
    (occupationRate_nonneg hJ β) (occupation_detailed_balance hJ hJ2 β) _
    (occupationV_pos hJ hN hβ hsub) F

/-- Detailed balance converts the true ground-state ratio into a square root
of the product of the actual forward and reverse rates, including zero rates. -/
theorem rate_sqrt_balance {wx wy a b : ℝ} (hx : 0 < wx) (hy : 0 < wy)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hbal : wx * a = wy * b) :
    a * (Real.sqrt wy)⁻¹ / (Real.sqrt wx)⁻¹ = Real.sqrt (a * b) := by
  have hsy : Real.sqrt wy ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have hsx : Real.sqrt wx ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have he : a * (Real.sqrt wy)⁻¹ / (Real.sqrt wx)⁻¹ =
      a * Real.sqrt wx / Real.sqrt wy := by field_simp
  rw [he]
  have hq : 0 ≤ a * Real.sqrt wx / Real.sqrt wy := by positivity
  have hs : (a * Real.sqrt wx / Real.sqrt wy) ^ 2 = a * b := by
    rw [div_pow, mul_pow, Real.sq_sqrt hx.le, Real.sq_sqrt hy.le]
    apply (div_eq_iff hy.ne').mpr
    nlinarith only [congrArg (fun z : ℝ => a * z) hbal]
  exact (sq_eq_sq₀ hq (Real.sqrt_nonneg (a * b))).mp
    (hs.trans (Real.sq_sqrt (mul_nonneg ha hb)).symm)

theorem occupationW_eq_rates (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) (m : OccupationState J N t) :
    occupationW hJ β m =
      ∑ m', (occupationRate hJ β m m' -
        Real.sqrt (occupationRate hJ β m m' * occupationRate hJ β m' m)) := by
  unfold occupationW
  rw [FiniteGraph.groundStatePotential_eq_sum _ _
    (occupationV_pos hJ hN hβ hsub)]
  apply Finset.sum_congr rfl
  intro m' _
  rw [mul_sub, mul_one, ← mul_div_assoc]
  unfold occupationV
  rw [rate_sqrt_balance (occupationWeight_pos hJ hN hβ hsub m)
    (occupationWeight_pos hJ hN hβ hsub m')
    (occupationRate_nonneg hJ β m m') (occupationRate_nonneg hJ β m' m)
    (occupation_detailed_balance hJ hJ2 β m m')]

/-- Exact identity for arbitrary label observables. There is no symmetry or
support premise; the occupation ground state is lifted through the true generator. -/
theorem label_ground_state_identity (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) (F : LabelState J N t → ℝ) :
    labelEnergy hJ β F -
        ∑ η, labelWeight hJ β η * F η ^ 2 * occupationW hJ β (profile η) =
      (1 / 2 : ℝ) * ∑ η, ∑ ζ,
        labelWeight hJ β η * labelRate hJ β η ζ *
          occupationV hJ β (profile η) * occupationV hJ β (profile ζ) *
            (F η / occupationV hJ β (profile η) -
              F ζ / occupationV hJ β (profile ζ)) ^ 2 := by
  rw [labelEnergy_eq_directed]
  have hh := FiniteGraph.groundState_identity (labelWeight hJ β) (labelRate hJ β)
    (label_detailed_balance hJ β) (occupationV hJ β ∘ profile)
    (fun η => occupationV_pos hJ hN hβ hsub (profile η)) F
  simp_rw [groundStatePotential_profile hJ hJ2 β] at hh
  exact hh

theorem label_ground_state_coercivity (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) (F : LabelState J N t → ℝ) :
    (∑ η, labelWeight hJ β η * F η ^ 2 * occupationW hJ β (profile η)) ≤
      labelEnergy hJ β F := by
  rw [labelEnergy_eq_directed]
  have hh := FiniteGraph.groundState_coercivity (labelWeight hJ β) (labelRate hJ β)
    (fun η => (labelWeight_pos hJ hN hβ hsub η).le)
    (labelRate_nonneg hJ β) (label_detailed_balance hJ β)
    (occupationV hJ β ∘ profile)
    (fun η => occupationV_pos hJ hN hβ hsub (profile η)) F
  simp_rw [groundStatePotential_profile hJ hJ2 β] at hh
  exact hh

/-- Source eq:label-ground-state for every nonnegative label function, on the
entire original outer graph and with every edge retained. -/
theorem label_ground_state_nonnegative (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) (Φ : LabelState J N t → ℝ)
    (hΦ : ∀ η, 0 ≤ Φ η) :
    (∑ η, labelWeight hJ β η * Φ η * occupationW hJ β (profile η)) ≤
      labelEnergy hJ β (fun η => Real.sqrt (Φ η)) := by
  simpa only [Real.sq_sqrt (hΦ _)] using
    label_ground_state_coercivity hJ hJ2 hN hβ hsub (fun η => Real.sqrt (Φ η))

end PeriodicAttractiveLogGas.LabelGroundState
