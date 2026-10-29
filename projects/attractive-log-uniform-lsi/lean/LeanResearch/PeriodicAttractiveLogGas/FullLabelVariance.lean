import LeanResearch.PeriodicAttractiveLogGas.OccupationPoincare
import LeanResearch.PeriodicAttractiveLogGas.MultislicePoincare
import LeanResearch.PeriodicAttractiveLogGas.PermutationPathComparison

/-! Source prop:label-variance-decomposition, 2786--2832. The proof uses
multislice Poincare, actual permutation paths and occupation Poincare only.
No entropy inequality or logarithmic Sobolev inequality is used. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.FullLabelVariance
open MeshCells LabelOccupations CellRestrictions DiscreteOccupationIdentities FibreProjection
open MultislicePoincare ConditionalLawEstimates
variable {J N : ℕ} {t β β₀ cFar : ℝ}

local instance : DecidablePred (fun η : LabelState J N t =>
    OccupationCap (t/2) η.val) := fun _ => Classical.propDecidable _

/-- Actual labels in a chosen collection of occupation classes. -/
def labelsIn (S : Finset (OccupationState J N t)) : Finset (LabelState J N t) :=
  Finset.univ.filter (fun η => profile η ∈ S)

theorem weighted_selected_fibres (hJ : 0 < J) (β : ℝ)
    (S : Finset (OccupationState J N t)) (G : LabelState J N t → ℝ) :
    (∑ η ∈ labelsIn S, labelWeight hJ β η*G η) =
      ∑ m ∈ S, occupationWeight hJ β m*fibreAverage G m := by
  classical
  have hh := FibreEntropy.weighted_sum_by_fibres hJ β (fun η => if profile η ∈ S then G η else 0)
  have he (m : OccupationState J N t) :
      fibreAverage (fun η => if profile η ∈ S then G η else 0) m =
        if m ∈ S then fibreAverage G m else 0 := by
    unfold fibreAverage
    simp only [profile_fibre]
    by_cases hm : m ∈ S <;> simp [hm]
  simp_rw [he] at hh
  simp only [mul_ite, mul_zero] at hh
  rw [← Finset.sum_filter, ← Finset.sum_filter] at hh
  have hs : Finset.univ.filter (fun m : OccupationState J N t => m ∈ S) = S := by
    ext m
    simp
  rw [hs] at hh
  exact hh

theorem transpositionEnergy_average (H : LabelState J N t → ℝ)
    (m : OccupationState J N t) :
    transpositionEnergy H m = (1/(2*(N : ℝ)))*fibreAverage
      (fun η => ∑ i : Fin N, ∑ j : Fin N,
        if i < j then (H (permutedLabel (Equiv.swap i j) η)-H η)^2 else 0) m := by
  classical
  change transpositionEnergy H m = (1/(2*(N : ℝ)))*uniformAverage
    (fun η : Fibre m => ∑ i : Fin N, ∑ j : Fin N,
      if i < j then (H (permutedLabel (Equiv.swap i j) η.val)-H η.val)^2 else 0)
  simp_rw [uniformAverage_sum]
  unfold transpositionEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j <;> simp [hij, uniformAverage, fibreAverage]

/-- Exact weighted original transposition form on any union of fibres. -/
theorem weighted_transposition_identity (hJ : 0 < J) (β : ℝ)
    (S : Finset (OccupationState J N t)) (H : LabelState J N t → ℝ) :
    (∑ m ∈ S, occupationWeight hJ β m*transpositionEnergy H m) =
      (1/(2*(N : ℝ)))*(∑ η ∈ labelsIn S, labelWeight hJ β η*
        ∑ i : Fin N, ∑ j : Fin N,
          if i < j then (H (permutedLabel (Equiv.swap i j) η)-H η)^2 else 0) := by
  rw [weighted_selected_fibres]
  simp_rw [transpositionEnergy_average]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring


/-- Exactly the source path coefficient, independent of N and actual beta. -/
def fibreConstant (J : ℕ) (β₀ : ℝ) : ℝ :=
  4*(J : ℝ)^3/CellNormalizerBounds.kappaConstant β₀ MovingPoleCalculus.greenLowerConstant
    kernelConstant J (radius β₀)

def poincareConstant (J : ℕ) (β₀ : ℝ) : ℝ :=
  max (fibreConstant J β₀) (OccupationCoercivity.bufferConstant J β₀)

theorem fibreAverage_remainder (F : LabelState J N t → ℝ) (m : OccupationState J N t) :
    fibreAverage (remainder F) m = 0 := by
  simp only [fibreAverage, sum_fibre_remainder, zero_div]

/-- The actual zero-mean fibre remainder is controlled by the sharp
multislice PI, including zero counts and singleton fibres. -/
theorem remainder_fibre_bound (F : LabelState J N t → ℝ) (m : OccupationState J N t) :
    fibreAverage (fun η => remainder F η ^ 2) m ≤ transpositionEnergy (remainder F) m := by
  have hh := multislice_poincare (remainder F) m
  simpa only [fibreVariance, fibreAverage_remainder, sub_zero] using hh

/-- Inner-fibre remainder norm bounded using genuine transposition paths
in the outer t graph; the only path margin is the literal 1 ≤ (t/2)N. -/
theorem inner_remainder_bound (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t < occupationBound β₀)
    (hmesh : 8*(radius β₀+4) ≤ J) (hbuffer : 1 ≤ (t-t/2)*N)
    (S : Finset (OccupationState J N t))
    (hS : ∀ m ∈ S, m.val ∈ cappedOccupations J N (t/2))
    (F : LabelState J N t → ℝ) :
    (∑ η ∈ labelsIn S, labelWeight (mesh_pos hmesh) β η * remainder F η ^ 2) ≤
      fibreConstant J β₀ * labelEnergy (mesh_pos hmesh) β (remainder F) := by
  have hp := PermutationPathComparison.permutation_paths hN hβ hβ₀ hsub
    (show 0 < t/2 by linarith) (show t/2 < t by linarith) htC le_rfl
    MovingPoleCalculus.greenLowerConstant_pos.le MovingPoleCalculus.green_lower_bound
    hmesh hbuffer (labelsIn S) (fun η hη => by
      have hm : profile η ∈ S := (Finset.mem_filter.mp hη).2
      exact (occupation_mem_cappedOccupations_iff η.val).mp (hS (profile η) hm)) (remainder F)
  rw [← weighted_transposition_identity (mesh_pos hmesh) β S (remainder F)] at hp
  rw [weighted_selected_fibres]
  exact (Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left
    (remainder_fibre_bound F m) ENNReal.toReal_nonneg).trans hp

/-- Exact mass transport for observables constant on each occupation fibre. -/
theorem weighted_profile_sum (hJ : 0 < J) (β : ℝ)
    (A : OccupationState J N t → ℝ) :
    (∑ η, labelWeight hJ β η * A (profile η)) =
      ∑ m, occupationWeight hJ β m * A m := by
  rw [FibreEntropy.weighted_sum_by_fibres]
  simp only [fibreAverage_profile]

/-- The exterior is a union of complete fibres, so the same exact
orthogonality holds there, with no normalization of the restricted weights. -/
theorem exterior_decomposition (hJ : 0 < J) (β : ℝ)
    (F : LabelState J N t → ℝ) (c : ℝ) :
    (∑ η, if OccupationCap (t/2) η.val then 0 else labelWeight hJ β η*(F η-c)^2) =
    (∑ η, if OccupationCap (t/2) η.val then 0 else labelWeight hJ β η*(projection F η-c)^2) +
    (∑ η, if OccupationCap (t/2) η.val then 0 else labelWeight hJ β η*remainder F η^2) := by
  classical
  have hh := weighted_l2_decomposition hJ β F c
    (Finset.univ.filter (fun m : OccupationState J N t =>
      m.val ∉ cappedOccupations J N (t/2)))
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, profile,
    occupation_mem_cappedOccupations_iff, ite_not] using hh

theorem remainder_bound (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t < occupationBound β₀)
    (hmesh : 8*(radius β₀+4) ≤ J) (hbuffer : 1 ≤ (t-t/2)*N)
    (F : LabelState J N t → ℝ) :
    (∑ η, labelWeight (mesh_pos hmesh) β η*remainder F η^2) ≤
    fibreConstant J β₀ * labelEnergy (mesh_pos hmesh) β (remainder F) +
    (∑ η, if OccupationCap (t/2) η.val then 0
      else labelWeight (mesh_pos hmesh) β η*remainder F η^2) := by
  classical
  let S := Finset.univ.filter (fun m : OccupationState J N t =>
    m.val ∈ cappedOccupations J N (t/2))
  have hh := inner_remainder_bound hN hβ hβ₀ hsub ht htC hmesh hbuffer S
    (fun m hm => (Finset.mem_filter.mp hm).2) F
  have he : (∑ η, labelWeight (mesh_pos hmesh) β η*remainder F η^2) =
      (∑ η ∈ labelsIn S, labelWeight (mesh_pos hmesh) β η*remainder F η^2) +
      (∑ η, if OccupationCap (t/2) η.val then 0
        else labelWeight (mesh_pos hmesh) β η*remainder F η^2) := by
    simp only [labelsIn, S, Finset.sum_filter, Finset.mem_filter, Finset.mem_univ,
      true_and, profile, occupation_mem_cappedOccupations_iff]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro η _
    split_ifs <;> simp
  rw [he]
  linarith only [hh]

/-- Actual occupation PI transported to the fibre projection. -/
theorem projection_bound
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t ≤ occupationBound β₀)
    (hmesh : 8*(radius β₀+4) ≤ J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀ ≤ J)
    (hsmall : 1/(J^2:ℕ) < t/8) (hcFar : 0 < cFar)
    (hlarge : OccupationCoercivity.particleThreshold J β₀ t cFar ≤ N)
    (hfar : OccupationCoercivity.FarImbalance (N := N) (t := t) (mesh_pos hmesh) β β₀ cFar)
    (F : LabelState J N t → ℝ) :
    let c := OccupationPoincare.center (mesh_pos hmesh) β β₀ (fibreAverage F)
    (∑ η, labelWeight (mesh_pos hmesh) β η*(projection F η-c)^2) ≤
      OccupationCoercivity.bufferConstant J β₀ * labelEnergy (mesh_pos hmesh) β (projection F) +
      2*(∑ η, if OccupationCap (t/2) η.val then 0
        else labelWeight (mesh_pos hmesh) β η*(projection F η-c)^2) := by
  classical
  dsimp only
  let c := OccupationPoincare.center (mesh_pos hmesh) β β₀ (fibreAverage F)
  have hh := OccupationPoincare.occupation_poincare_of_far hβ hβ₀ hsub ht htC
    hmesh hnearJ hsmall hcFar hlarge hfar (fibreAverage F)
  change (∑ m, occupationWeight (mesh_pos hmesh) β m*(fibreAverage F m-c)^2) ≤ _ at hh
  have hwhole := weighted_profile_sum (mesh_pos hmesh) β
    (fun m => (fibreAverage F m-c)^2)
  have hout := weighted_profile_sum (mesh_pos hmesh) β
    (fun m => if m.val ∈ cappedOccupations J N (t/2) then 0 else (fibreAverage F m-c)^2)
  simp only [mul_ite, mul_zero, profile, occupation_mem_cappedOccupations_iff] at hout
  have he := energy_occupation_restriction (mesh_pos hmesh)
    (show 2 ≤ J by omega) β (fibreAverage F)
  change labelEnergy (mesh_pos hmesh) β (projection F) = _ at he
  dsimp only [c] at hh hwhole hout
  simpa only [← hwhole, ← hout, ← he, projection, profile] using! hh

/-- Source label variance decomposition, with the exact maximum coefficient
and error 2 on the complement of the inner half-cap. The sole unresolved
analytic input is the explicitly named literal far-imbalance hypothesis. -/
theorem full_label_poincare_of_far
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t < occupationBound β₀)
    (hmesh : 8*(radius β₀+4) ≤ J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀ ≤ J)
    (hsmall : 1/(J^2:ℕ) < t/8) (hcFar : 0 < cFar)
    (hlarge : OccupationCoercivity.particleThreshold J β₀ t cFar ≤ N)
    (hfar : OccupationCoercivity.FarImbalance (N := N) (t := t) (mesh_pos hmesh) β β₀ cFar)
    (F : LabelState J N t → ℝ) :
    let c := OccupationPoincare.center (mesh_pos hmesh) β β₀ (fibreAverage F)
    (∑ η, labelWeight (mesh_pos hmesh) β η*(F η-c)^2) ≤
      poincareConstant J β₀ * labelEnergy (mesh_pos hmesh) β F +
      2*(∑ η, if OccupationCap (t/2) η.val then 0
        else labelWeight (mesh_pos hmesh) β η*(F η-c)^2) := by
  classical
  dsimp only
  let c := OccupationPoincare.center (mesh_pos hmesh) β β₀ (fibreAverage F)
  have hg := OccupationPoincare.threshold_gates (hβ.trans hβ₀) hsub ht hlarge
  have hp := projection_bound hβ hβ₀ hsub ht htC.le hmesh hnearJ hsmall hcFar hlarge hfar F
  have hr := remainder_bound hg.2.1 hβ hβ₀ hsub ht htC hmesh hg.2.2.2 F
  have hwhole := weighted_l2_decomposition_univ (mesh_pos hmesh) β F c
  have hout := exterior_decomposition (mesh_pos hmesh) β F c
  have he := labelEnergy_decomposition (mesh_pos hmesh) β F
  have hep := PermutationPathComparison.labelEnergy_nonneg (mesh_pos hmesh) β (projection F)
  have her := PermutationPathComparison.labelEnergy_nonneg (mesh_pos hmesh) β (remainder F)
  have hp' := mul_le_mul_of_nonneg_right (le_max_right (fibreConstant J β₀)
    (OccupationCoercivity.bufferConstant J β₀)) hep
  have hr' := mul_le_mul_of_nonneg_right (le_max_left (fibreConstant J β₀)
    (OccupationCoercivity.bufferConstant J β₀)) her
  have hrem : 0 ≤ ∑ η : LabelState J N t, if OccupationCap (t/2) η.val then 0
      else labelWeight (mesh_pos hmesh) β η*remainder F η^2 := by
    apply Finset.sum_nonneg
    intro η _
    split_ifs
    · exact le_rfl
    · exact mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  change (∑ η, labelWeight (mesh_pos hmesh) β η*(projection F η-c)^2) ≤ _ at hp
  dsimp only [c] at hp hwhole hout
  unfold poincareConstant
  rw [hwhole, he, hout, mul_add]
  linarith only [hp, hr, hp', hr', hrem]

end PeriodicAttractiveLogGas.FullLabelVariance
