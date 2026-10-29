import LeanResearch.PeriodicAttractiveLogGas.MultisliceColourRecursion
import LeanResearch.PeriodicAttractiveLogGas.OccupationCriterion
import LeanResearch.PeriodicAttractiveLogGas.PermutationPathComparison
import LeanResearch.PeriodicAttractiveLogGas.FiniteFibreEntropyBound

/-! Source 3045–3104: the original unnormalized outer label entropy.
Development proceeds through actual fibre and occupation laws; the unresolved
far-imbalance assumption will remain explicit in the final assembly. -/
noncomputable section
open scoped BigOperators ENNReal
namespace PeriodicAttractiveLogGas.FullLabelEntropy
open MeshCells LabelOccupations CellRestrictions DiscreteOccupationIdentities
  FibreProjection FibreEntropy MultislicePoincare MultisliceColourRecursion
  ConditionalLawEstimates
variable {J N : ℕ} {t : ℝ}

/-- Actual labels in a chosen collection of occupation classes. -/
def labelsIn (S : Finset (OccupationState J N t)) : Finset (LabelState J N t) :=
  Finset.univ.filter (fun η => profile η ∈ S)

theorem weighted_selected_fibres (hJ : 0 < J) (β : ℝ)
    (S : Finset (OccupationState J N t)) (G : LabelState J N t → ℝ) :
    (∑ η ∈ labelsIn S, labelWeight hJ β η*G η) =
      ∑ m ∈ S, occupationWeight hJ β m*fibreAverage G m := by
  classical
  have hh := weighted_sum_by_fibres hJ β (fun η => if profile η ∈ S then G η else 0)
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

def tau (J : ℕ) : ℝ := 4/Real.log 2*Real.log (4*(J : ℝ)^2)

theorem tau_nonneg (hJ : 0 < J) : 0 ≤ tau J := by
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  unfold tau
  apply mul_nonneg (div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le)
  exact Real.log_nonneg (by nlinarith)

/-- Every original count is bounded below only in this balanced-fibre step. -/
theorem balanced_fibre_entropy (hJ : 0 < J) (hN : 0 < N)
    (m : OccupationState J N t) (hm : ∀ a, (N : ℝ)/(4*(J : ℝ)^2) ≤ m.val a)
    (Φ : LabelState J N t → ℝ) (hΦ : ∀ η, 0 ≤ Φ η) :
    uniformFibreEntropy Φ m ≤ tau J*transpositionEnergy (fun η => Real.sqrt (Φ η)) m := by
  have hk := minimumPositiveCount_pos m hN
  have hmin : (N : ℝ)/(4*(J : ℝ)^2) ≤ minimumPositiveCount m hN := by
    have hh : minimumPositiveCount m hN ∈ (occupiedColours m).image m.val := by
      unfold minimumPositiveCount
      exact Finset.min'_mem _ _
    obtain ⟨a, _ha, he⟩ := Finset.mem_image.mp hh
    rw [← he]
    exact hm a
  have hJr : (0 : ℝ) < J := Nat.cast_pos.mpr hJ
  have hkr : (0 : ℝ) < minimumPositiveCount m hN := Nat.cast_pos.mpr hk
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hratio : (N : ℝ)/minimumPositiveCount m hN ≤ 4*(J : ℝ)^2 := by
    apply (div_le_iff₀ hkr).mpr
    have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < 4*(J : ℝ)^2)).mp hmin
    nlinarith only [hh]
  have hc := mul_le_mul_of_nonneg_left
    (Real.log_le_log (div_pos hn hkr) hratio)
    (show (0 : ℝ) ≤ 4/Real.log 2 from div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le)
  exact (multislice_logSobolev Φ m hN (fun η => hΦ η.val)).trans
    (mul_le_mul_of_nonneg_right hc (transpositionEnergy_nonneg _ m))

/-- The supplied permutation paths are applied to the literal union of the
selected balanced fibres, retaining the original outer conductances. -/
theorem balanced_fibre_sum {β β₀ δ Cg u : ℝ} (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hu : 0 < u) (hut : u < t) (htδ : t < δ) (hδ : δ ≤ occupationBound β₀)
    (hCg : 0 ≤ Cg) (hg : ∀ z : Torus, -Cg ≤ regularGreenRepresentative z)
    (hmesh : 8*(radius β₀+4) ≤ J) (hbuffer : 1 ≤ (t-u)*N)
    (S : Finset (OccupationState J N t))
    (hS : ∀ m ∈ S, m.val ∈ cappedOccupations J N u)
    (hbalanced : ∀ m ∈ S, ∀ a, (N : ℝ)/(4*(J : ℝ)^2) ≤ m.val a)
    (Φ : LabelState J N t → ℝ) (hΦ : ∀ η, 0 ≤ Φ η) :
    (∑ m ∈ S, occupationWeight (mesh_pos hmesh) β m*uniformFibreEntropy Φ m) ≤
      tau J*(4*(J : ℝ)^3/
        CellNormalizerBounds.kappaConstant β₀ Cg kernelConstant J (radius β₀))*
      labelEnergy (mesh_pos hmesh) β (fun η => Real.sqrt (Φ η)) := by
  classical
  have hp := PermutationPathComparison.permutation_paths hN hβ hβ₀ hsub hu hut htδ hδ
    hCg hg hmesh hbuffer (labelsIn S) (fun η hη => by
      have hm : profile η ∈ S := (Finset.mem_filter.mp hη).2
      exact (occupation_mem_cappedOccupations_iff η.val).mp (hS (profile η) hm)) (fun η => Real.sqrt (Φ η))
  rw [← weighted_transposition_identity (mesh_pos hmesh) β S (fun η => Real.sqrt (Φ η))] at hp
  calc
    _ ≤ ∑ m ∈ S, occupationWeight (mesh_pos hmesh) β m*
        (tau J*transpositionEnergy (fun η => Real.sqrt (Φ η)) m) := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_left
        (balanced_fibre_entropy (mesh_pos hmesh) (by omega) m (hbalanced m hm) Φ hΦ)
        ENNReal.toReal_nonneg
    _ = tau J*∑ m ∈ S, occupationWeight (mesh_pos hmesh) β m*
        transpositionEnergy (fun η => Real.sqrt (Φ η)) m := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hp (tau_nonneg (mesh_pos hmesh))
      simpa only [mul_assoc] using hh

/-- Vanishing on the inner complement passes to the actual fibre mean. -/
theorem fibreAverage_support {u : ℝ} (Φ : LabelState J N t → ℝ)
    (hsupport : ∀ η, ¬OccupationCap u η.val → Φ η = 0)
    (m : OccupationState J N t) (hm : m.val ∉ cappedOccupations J N u) :
    fibreAverage Φ m = 0 := by
  unfold fibreAverage
  have hz : (∑ η : Fibre m, Φ η.val) = 0 := by
    apply Finset.sum_eq_zero
    intro η _
    apply hsupport
    intro hcap
    apply hm
    have he : occupation η.val.val = m.val := congrArg Subtype.val η.property
    rw [← he]
    exact (occupation_mem_cappedOccupations_iff η.val.val).mpr hcap
  rw [hz, zero_div]

/-- The actual occupation entropy term, with no extra projection-energy or
occupation-LSI premise. Only the literal far-imbalance input remains. -/
theorem occupation_entropy_term {β β₀ u cFar : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t ≤ occupationBound β₀)
    (hu : 0 < u) (hu1 : u < 1) (hut : u < 3*t/4)
    (hmesh : 8*(radius β₀+4) ≤ J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀ ≤ J)
    (hresolution : HeavyScales.sourceResolution β₀ (u/2) ≤ J)
    (hsmall : 1/(J^2:ℕ) < t/8) (hinner : 1/(J^2:ℕ) < u)
    (hcFar : 0 < cFar) (hlarge : OccupationCriterion.particleThreshold J β₀ t u cFar ≤ N)
    (hfar : OccupationCoercivity.FarImbalance (N:=N) (t:=t) (mesh_pos hmesh) β β₀ cFar)
    (Φ : LabelState J N t → ℝ) (hΦ : ∀ η, 0 ≤ Φ η)
    (hsupport : ∀ η, ¬OccupationCap u η.val → Φ η = 0) :
    FibreEntropy.finiteEntropy (occupationWeight (mesh_pos hmesh) β) (fibreAverage Φ) ≤
      OccupationCriterion.entropyConstant J β₀ u cFar*
        labelEnergy (mesh_pos hmesh) β (fun η => Real.sqrt (Φ η))+
      OccupationCriterion.defectConstant J β₀ u cFar*
        ∑ η, labelWeight (mesh_pos hmesh) β η*Φ η := by
  have hh := OccupationCriterion.source_occupation_entropy_of_far hβ hβ₀ hsub ht htC
    hu hu1 hut hmesh hnearJ hresolution hsmall hinner hcFar hlarge hfar
    (fun m => Real.sqrt (fibreAverage Φ m)) (fun m hm => by
      rw [fibreAverage_support Φ hsupport m hm, Real.sqrt_zero])
  simp only [Real.sq_sqrt (fibreAverage_nonneg hΦ _)] at hh
  have hc := (OccupationCriterion.constants_nonneg (mesh_pos hmesh) (u:=u)
    (hβ.trans hβ₀) hsub hcFar).1
  have hp := mul_le_mul_of_nonneg_left
    (occupationEnergy_sqrt_fibreAverage_le (mesh_pos hmesh) (mesh_two_le hmesh) β Φ hΦ) hc
  rw [weighted_sum_by_fibres]
  exact hh.trans (add_le_add hp le_rfl)

/-- A valid fixed choice of the source quadratic-imbalance constants. The
truncation radius is one; the actual near/far split below proves this choice. -/
def quadraticCoefficient (J : ℕ) (β₀ cFar : ℝ) : ℝ :=
  min (OccupationNearImbalance.coercivityConstant J β₀/2) cFar

def quadraticLoss (J : ℕ) (β₀ : ℝ) : ℝ :=
  max (OccupationNearImbalance.translatedConstant J β₀)
    (OccupationNearImbalance.roundedConstant J β₀)

def sparseCoefficient (J : ℕ) (β₀ cFar : ℝ) : ℝ :=
  quadraticCoefficient J β₀ cFar/2*min (1/(4*(J : ℝ)^4)) 1

def sparseLoss (J : ℕ) (β₀ : ℝ) : ℝ :=
  quadraticLoss J β₀/2+OccupationCoercivity.lowerLoss J β₀

theorem quadraticCoefficient_pos (hJ : 0 < J) {β₀ cFar : ℝ}
    (hsub : β₀ < 4) (hcFar : 0 < cFar) : 0 < quadraticCoefficient J β₀ cFar :=
  lt_min (div_pos (OccupationNearImbalance.coercivityConstant_pos hJ hsub) (by norm_num)) hcFar

theorem quadraticLoss_nonneg (hJ : 0 < J) {β₀ : ℝ} (hsub : β₀ < 4) :
    0 ≤ quadraticLoss J β₀ :=
  (OccupationNearImbalance.translatedConstant_nonneg hJ hsub).trans (le_max_left _ _)

theorem sparseCoefficient_pos (hJ : 0 < J) {β₀ cFar : ℝ}
    (hsub : β₀ < 4) (hcFar : 0 < cFar) : 0 < sparseCoefficient J β₀ cFar := by
  have hJr : (0 : ℝ) < J := Nat.cast_pos.mpr hJ
  have hc := quadraticCoefficient_pos hJ hsub hcFar
  unfold sparseCoefficient
  positivity

/-- Actual global profile-quadratic imbalance from the proved near theorem
and the sole unresolved literal far-subset input. -/
theorem profile_quadratic_imbalance {β β₀ cFar : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t ≤ occupationBound β₀)
    (hmesh : 8*(radius β₀+4) ≤ J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀ ≤ J)
    (hlarge : OccupationNearImbalance.particleThreshold J β₀ t ≤ N)
    (hcFar : 0 < cFar)
    (hfar : OccupationCoercivity.FarImbalance (N:=N) (t:=t) (mesh_pos hmesh) β β₀ cFar)
    (m : OccupationState J N t) (hm : m.val ∈ cappedOccupations J N (3*t/4)) :
    let hmargin := (OccupationNearImbalance.particleThreshold_bounds
      (hβ.trans hβ₀) hsub ht hlarge).2.2.2.2.1
    quadraticCoefficient J β₀ cFar*N*
        min (∑ a, (OccupationNearImbalance.stateProfile m a-
          (OccupationCoordinates.rounded J N a : ℝ)/N)^2) 1-quadraticLoss J β₀ ≤
      OccupationDrift.imbalance (mesh_pos hmesh) β m hm hmargin := by
  dsimp only
  let S := ∑ a, (OccupationNearImbalance.stateProfile m a-
    (OccupationCoordinates.rounded J N a : ℝ)/N)^2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc := (quadraticCoefficient_pos (mesh_pos hmesh) hsub hcFar).le
  have hnearC := (OccupationNearImbalance.coercivityConstant_pos (mesh_pos hmesh) hsub).le
  have hCD := le_max_left (OccupationNearImbalance.translatedConstant J β₀)
    (OccupationNearImbalance.roundedConstant J β₀)
  by_cases hnear : OccupationNearContraction.profileDeviation
      (OccupationNearImbalance.stateProfile m) ≤ OccupationNearImbalance.nearNeighborhood β₀
  · have hi := OccupationNearImbalance.near_rounded_imbalance hβ hβ₀ hsub ht htC hmesh
      hnearJ hlarge m hnear hm
    dsimp only at hi
    have hp := mul_le_mul (min_le_left (OccupationNearImbalance.coercivityConstant J β₀/2) cFar)
      (min_le_left S 1) (le_min hS (by norm_num))
      (div_nonneg hnearC (by norm_num))
    have hpN := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg N)
    change quadraticCoefficient J β₀ cFar*N*min S 1-quadraticLoss J β₀ ≤ _
    dsimp only [quadraticCoefficient, quadraticLoss, S] at *
    nlinarith only [hi, hpN, hCD]
  · have hi := hfar m hm (OccupationNearImbalance.particleThreshold_bounds
      (hβ.trans hβ₀) hsub ht hlarge).2.2.2.2.1 (lt_of_not_ge hnear)
    have hp := mul_le_mul (min_le_right (OccupationNearImbalance.coercivityConstant J β₀/2) cFar)
      (min_le_right S 1) (le_min hS (by norm_num)) hcFar.le
    have hpN := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg N)
    have hloss := quadraticLoss_nonneg (mesh_pos hmesh) hsub
    change quadraticCoefficient J β₀ cFar*N*min S 1-quadraticLoss J β₀ ≤ _
    dsimp only [quadraticCoefficient] at *
    nlinarith only [hi, hpN, hloss]

/-- The same CD also covers the actual rounded center, as required in the
source choice of quadratic constants. -/
theorem rounded_imbalance_le_loss {β β₀ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4) (ht : 0 < t)
    (htC : t ≤ occupationBound β₀) (hmesh : 8*(radius β₀+4) ≤ J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀ ≤ J)
    (hlarge : OccupationNearImbalance.particleThreshold J β₀ t ≤ N)
    (hsmall : 1/(J^2:ℕ) < t/8) (m : OccupationState J N t)
    (hround : m.val = OccupationCoordinates.rounded J N) :
    let hb := OccupationNearImbalance.particleThreshold_bounds (hβ.trans hβ₀) hsub ht hlarge
    OccupationDrift.imbalance (mesh_pos hmesh) β m
      (OccupationNearImbalance.rounded_inner (mesh_pos hmesh) hb.2.2.1 hsmall m hround)
      hb.2.2.2.2.1 ≤ quadraticLoss J β₀ := by
  exact (OccupationNearImbalance.rounded_imbalance_upper hβ hβ₀ hsub ht htC hmesh
    hnearJ hlarge hsmall m hround).trans (le_max_right _ _)

/-- A small or zero original count gives a definite normalized distance
from the actual rounded profile; no positivity of that count is needed. -/
theorem sparse_profile_distance (hJ : 0 < J) (hN : 0 < N) (hcounts : 4*J^2 ≤ N)
    (m : OccupationState J N t) (a : MeshIndex J)
    (ha : (m.val a : ℝ) < (N : ℝ)/(4*(J : ℝ)^2)) :
    1/(4*(J : ℝ)^4) ≤ ∑ b, (OccupationNearImbalance.stateProfile m b-
      (OccupationCoordinates.rounded J N b : ℝ)/N)^2 := by
  have hJr : (0 : ℝ) < J := Nat.cast_pos.mpr hJ
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hnr : 4*(J : ℝ)^2 ≤ N := by exact_mod_cast hcounts
  have hr := (abs_le.mp (OccupationCoordinates.rounded_close hJ N a)).1
  simp only [Nat.cast_pow] at hr
  have hscale : 1 ≤ (N : ℝ)/(4*(J : ℝ)^2) := (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  have hsplit : (N : ℝ)/(J : ℝ)^2 = 4*((N : ℝ)/(4*(J : ℝ)^2)) := by ring
  have hgap : (N : ℝ)/(2*(J : ℝ)^2) ≤
      (OccupationCoordinates.rounded J N a : ℝ)-m.val a := by
    have he : (N : ℝ)/(2*(J : ℝ)^2) = 2*((N : ℝ)/(4*(J : ℝ)^2)) := by ring
    rw [he]
    linarith only [hr, ha, hscale, hsplit]
  have hd : 1/(2*(J : ℝ)^2) ≤ (OccupationCoordinates.rounded J N a : ℝ)/N-
      (m.val a : ℝ)/N := by
    rw [← sub_div]
    apply (le_div_iff₀ hn).mpr
    convert hgap using 1; ring
  have hs : 1/(4*(J : ℝ)^4) ≤ (OccupationNearImbalance.stateProfile m a-
      (OccupationCoordinates.rounded J N a : ℝ)/N)^2 := by
    rw [OccupationNearImbalance.stateProfile_apply]
    have hsq := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 1/(2*(J : ℝ)^2))
      ((by positivity : (0 : ℝ) ≤ 1/(2*(J : ℝ)^2)).trans hd)).mpr hd
    have he : (1/(2*(J : ℝ)^2))^2 = 1/(4*(J : ℝ)^4) := by ring
    rw [he] at hsq
    nlinarith only [hsq]
  exact hs.trans (Finset.single_le_sum
    (fun b (_ : b ∈ (Finset.univ : Finset (MeshIndex J))) => sq_nonneg
      (OccupationNearImbalance.stateProfile m b-(OccupationCoordinates.rounded J N b : ℝ)/N))
    (Finset.mem_univ a))

/-- The exact source sparse drift, derived for small and zero counts. -/
theorem sparse_ground_state {β β₀ cFar : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t ≤ occupationBound β₀)
    (hmesh : 8*(radius β₀+4) ≤ J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀ ≤ J)
    (hlarge : OccupationNearImbalance.particleThreshold J β₀ t ≤ N)
    (hcFar : 0 < cFar)
    (hfar : OccupationCoercivity.FarImbalance (N:=N) (t:=t) (mesh_pos hmesh) β β₀ cFar)
    (m : OccupationState J N t) (hm : m.val ∈ cappedOccupations J N (3*t/4))
    (hsparse : ∃ a, (m.val a : ℝ) < (N : ℝ)/(4*(J : ℝ)^2)) :
    sparseCoefficient J β₀ cFar*N-sparseLoss J β₀ ≤
      LabelGroundState.occupationW (mesh_pos hmesh) β m := by
  have hb := OccupationNearImbalance.particleThreshold_bounds (hβ.trans hβ₀) hsub ht hlarge
  have hN : 0 < N := by omega
  have hcounts : 4*J^2 ≤ N := by have hh := hb.2.2.1; omega
  obtain ⟨a, ha⟩ := hsparse
  have hd := sparse_profile_distance (mesh_pos hmesh) hN hcounts m a ha
  have hi := profile_quadratic_imbalance hβ hβ₀ hsub ht htC hmesh hnearJ hlarge hcFar hfar m hm
  dsimp only at hi
  have hw := OccupationDrift.occupation_W_bound hβ hβ₀ hsub ht htC hmesh hb.2.1
    hb.2.2.2.2.1 m hm
  have hmin := min_le_min_right (1 : ℝ) hd
  have hp := mul_le_mul_of_nonneg_left hmin
    (mul_nonneg (quadraticCoefficient_pos (mesh_pos hmesh) hsub hcFar).le (Nat.cast_nonneg N))
  unfold sparseCoefficient sparseLoss OccupationCoercivity.lowerLoss
  nlinarith only [hi, hw, hp]

/-- The common source loss also gives the genuine lower W bound everywhere
on the supported inner occupations. -/
theorem ground_state_lower_loss {β β₀ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t ≤ occupationBound β₀)
    (hmesh : 8*(radius β₀+4) ≤ J)
    (hlarge : OccupationNearImbalance.particleThreshold J β₀ t ≤ N)
    (m : OccupationState J N t) (hm : m.val ∈ cappedOccupations J N (3*t/4)) :
    -sparseLoss J β₀ ≤ LabelGroundState.occupationW (mesh_pos hmesh) β m := by
  have hb := OccupationNearImbalance.particleThreshold_bounds (hβ.trans hβ₀) hsub ht hlarge
  have hh := OccupationCoercivity.ground_state_lower hβ hβ₀ hsub ht htC hmesh hb.2.1
    hb.2.2.2.2.1 m hm
  have hc := quadraticLoss_nonneg (mesh_pos hmesh) hsub
  unfold sparseLoss
  linarith only [hh, hc]

/-- Literal inner occupation classes, with no renormalization. -/
def innerClasses (u : ℝ) : Finset (OccupationState J N t) := by
  classical
  exact Finset.univ.filter (fun m => m.val ∈ cappedOccupations J N u)

def balancedClasses (u : ℝ) : Finset (OccupationState J N t) := by
  classical
  exact (innerClasses u).filter (fun m => ∀ a, (N : ℝ)/(4*(J : ℝ)^2) ≤ m.val a)

def sparseClasses (u : ℝ) : Finset (OccupationState J N t) :=
  innerClasses u \ balancedClasses u

theorem inner_cap_mono {u : ℝ} (hut : u ≤ 3*t/4)
    (m : OccupationState J N t) (hm : m ∈ innerClasses u) :
    m.val ∈ cappedOccupations J N (3*t/4) := by
  classical
  have hc := (Finset.mem_filter.mp hm).2
  exact ⟨hc.1, fun a => (hc.2 a).trans (mul_le_mul_of_nonneg_right hut (Nat.cast_nonneg N))⟩

theorem sparse_class_small {u : ℝ} (m : OccupationState J N t) (hm : m ∈ sparseClasses u) :
    ∃ a, (m.val a : ℝ) < (N : ℝ)/(4*(J : ℝ)^2) := by
  classical
  have hmem := Finset.mem_sdiff.mp hm
  have hn : ¬∀ a, (N : ℝ)/(4*(J : ℝ)^2) ≤ m.val a := by
    intro hh
    exact hmem.2 (Finset.mem_filter.mpr ⟨hmem.1, hh⟩)
  push Not at hn
  exact hn

/-- Actual ground-state lifting bounds the mass in the sparse classes.
The cutoff support is checked pointwise before summation. -/
theorem sparse_mass {β β₀ u cFar : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t ≤ occupationBound β₀) (hut : u < 3*t/4)
    (hmesh : 8*(radius β₀+4) ≤ J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀ ≤ J)
    (hlarge : OccupationNearImbalance.particleThreshold J β₀ t ≤ N)
    (hcFar : 0 < cFar)
    (hfar : OccupationCoercivity.FarImbalance (N:=N) (t:=t) (mesh_pos hmesh) β β₀ cFar)
    (Φ : LabelState J N t → ℝ) (hΦ : ∀ η, 0 ≤ Φ η)
    (hsupport : ∀ η, ¬OccupationCap u η.val → Φ η = 0) :
    sparseCoefficient J β₀ cFar*N*
        (∑ m ∈ sparseClasses u, occupationWeight (mesh_pos hmesh) β m*fibreAverage Φ m) ≤
      labelEnergy (mesh_pos hmesh) β (fun η => Real.sqrt (Φ η))+
        sparseLoss J β₀*∑ η, labelWeight (mesh_pos hmesh) β η*Φ η := by
  classical
  have hb := OccupationNearImbalance.particleThreshold_bounds (hβ.trans hβ₀) hsub ht hlarge
  have hp (η : LabelState J N t) :
      sparseCoefficient J β₀ cFar*N*(if profile η ∈ sparseClasses u then Φ η else 0)-
        sparseLoss J β₀*Φ η ≤ Φ η*LabelGroundState.occupationW (mesh_pos hmesh) β (profile η) := by
    by_cases hcap : OccupationCap u η.val
    · have hm : profile η ∈ innerClasses u := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ (profile η), (occupation_mem_cappedOccupations_iff η.val).mpr hcap⟩
      have hinner := inner_cap_mono hut.le (profile η) hm
      by_cases hs : profile η ∈ sparseClasses u
      · rw [ite_eq_left hs]
        have hw := sparse_ground_state hβ hβ₀ hsub ht htC hmesh hnearJ hlarge hcFar hfar
          (profile η) hinner (sparse_class_small (profile η) hs)
        nlinarith only [mul_le_mul_of_nonneg_right hw (hΦ η)]
      · rw [ite_eq_right hs, mul_zero]
        have hw := ground_state_lower_loss hβ hβ₀ hsub ht htC hmesh hlarge (profile η) hinner
        nlinarith only [mul_le_mul_of_nonneg_right hw (hΦ η)]
    · rw [hsupport η hcap]
      simp only [ite_self, mul_zero, zero_mul, sub_self, le_refl]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun η _ =>
    mul_le_mul_of_nonneg_left (hp η) (show 0 ≤ labelWeight (mesh_pos hmesh) β η from ENNReal.toReal_nonneg))
  have he : (∑ η : LabelState J N t, labelWeight (mesh_pos hmesh) β η*
      (sparseCoefficient J β₀ cFar*N*(if profile η ∈ sparseClasses u then Φ η else 0)-
        sparseLoss J β₀*Φ η)) =
      sparseCoefficient J β₀ cFar*N*(∑ η ∈ labelsIn (sparseClasses u),
        labelWeight (mesh_pos hmesh) β η*Φ η)-
      sparseLoss J β₀*(∑ η, labelWeight (mesh_pos hmesh) β η*Φ η) := by
    simp only [labelsIn, Finset.sum_filter, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro η _
    by_cases hh : profile η ∈ sparseClasses u <;> simp [hh] <;> ring
  rw [he, weighted_selected_fibres] at hs
  have hg := LabelGroundState.label_ground_state_nonnegative (mesh_pos hmesh) (mesh_two_le hmesh)
    hb.2.2.2.1 hβ (hβ₀.trans_lt hsub) Φ hΦ
  have hg' : (∑ η, labelWeight (mesh_pos hmesh) β η*
      (Φ η*LabelGroundState.occupationW (mesh_pos hmesh) β (profile η))) ≤
      labelEnergy (mesh_pos hmesh) β (fun η => Real.sqrt (Φ η)) := by
    simpa only [mul_assoc] using hg
  linarith only [hs, hg']

/-- The factor N in the crude finite-fibre bound is canceled by the
actual order-N drift, for every sparse class including empty cells. -/
theorem sparse_fibre_sum {β β₀ u cFar : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t ≤ occupationBound β₀) (hut : u < 3*t/4)
    (hmesh : 8*(radius β₀+4) ≤ J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀ ≤ J)
    (hlarge : OccupationNearImbalance.particleThreshold J β₀ t ≤ N)
    (hcFar : 0 < cFar)
    (hfar : OccupationCoercivity.FarImbalance (N:=N) (t:=t) (mesh_pos hmesh) β β₀ cFar)
    (Φ : LabelState J N t → ℝ) (hΦ : ∀ η, 0 ≤ Φ η)
    (hsupport : ∀ η, ¬OccupationCap u η.val → Φ η = 0) :
    (∑ m ∈ sparseClasses u, occupationWeight (mesh_pos hmesh) β m*uniformFibreEntropy Φ m) ≤
      (2*Real.log J/sparseCoefficient J β₀ cFar)*
        (labelEnergy (mesh_pos hmesh) β (fun η => Real.sqrt (Φ η))+
          sparseLoss J β₀*∑ η, labelWeight (mesh_pos hmesh) β η*Φ η) := by
  have hmass := sparse_mass hβ hβ₀ hsub ht htC hut hmesh hnearJ hlarge hcFar hfar Φ hΦ hsupport
  have hf := FiniteFibreEntropyBound.weighted_fibre_entropy_le (mesh_pos hmesh) β Φ hΦ (sparseClasses u)
  have hc := sparseCoefficient_pos (mesh_pos hmesh) hsub hcFar
  have hlog : 0 ≤ Real.log (J : ℝ) := Real.log_nonneg (by exact_mod_cast mesh_pos hmesh)
  have hh := mul_le_mul_of_nonneg_left hmass
    (show 0 ≤ 2*Real.log J/sparseCoefficient J β₀ cFar from
      div_nonneg (mul_nonneg (by norm_num) hlog) hc.le)
  have he : (2*Real.log J/sparseCoefficient J β₀ cFar)*(sparseCoefficient J β₀ cFar*N) =
      2*(N : ℝ)*Real.log J := by field_simp [hc.ne']
  rw [← mul_assoc, he] at hh
  exact hf.trans hh

/-- Zero extension of the original test gives zero fibre entropy on every
unsupported class, including its zero-mean case. -/
theorem fibre_entropy_support {u : ℝ} (Φ : LabelState J N t → ℝ)
    (hsupport : ∀ η, ¬OccupationCap u η.val → Φ η = 0)
    (m : OccupationState J N t) (hm : m.val ∉ cappedOccupations J N u) :
    uniformFibreEntropy Φ m = 0 := by
  have hz (η : Fibre m) : Φ η.val = 0 := by
    apply hsupport
    intro hc
    apply hm
    have he : occupation η.val.val = m.val := congrArg Subtype.val η.property
    rw [← he]
    exact (occupation_mem_cappedOccupations_iff η.val.val).mpr hc
  simp only [uniformFibreEntropy, fibreAverage, hz, zero_mul,
    Finset.sum_const_zero, zero_div, sub_self]

theorem sum_indicator {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (g : α → ℝ) :
    (∑ x, if x ∈ S then g x else 0) = ∑ x ∈ S, g x := by
  rw [← Finset.sum_filter]
  have hh : Finset.univ.filter (fun x : α => x ∈ S) = S := by ext x; simp
  rw [hh]

/-- The exact split over all balanced and sparse inner classes. -/
theorem fibre_entropy_split (hJ : 0 < J) (β : ℝ) {u : ℝ}
    (Φ : LabelState J N t → ℝ)
    (hsupport : ∀ η, ¬OccupationCap u η.val → Φ η = 0) :
    (∑ m, occupationWeight hJ β m*uniformFibreEntropy Φ m) =
      (∑ m ∈ balancedClasses u, occupationWeight hJ β m*uniformFibreEntropy Φ m)+
      (∑ m ∈ sparseClasses u, occupationWeight hJ β m*uniformFibreEntropy Φ m) := by
  classical
  rw [← sum_indicator (balancedClasses u) (fun m => occupationWeight hJ β m*uniformFibreEntropy Φ m),
    ← sum_indicator (sparseClasses u) (fun m => occupationWeight hJ β m*uniformFibreEntropy Φ m),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hi : m ∈ innerClasses u
  · by_cases hb : m ∈ balancedClasses u
    · have hs : m ∉ sparseClasses u := by simp only [sparseClasses, Finset.mem_sdiff]; tauto
      rw [ite_eq_left hb, ite_eq_right hs, add_zero]
    · have hs : m ∈ sparseClasses u := Finset.mem_sdiff.mpr ⟨hi, hb⟩
      rw [ite_eq_right hb, ite_eq_left hs, zero_add]
  · have hb : m ∉ balancedClasses u := fun h => hi (Finset.mem_filter.mp h).1
    have hs : m ∉ sparseClasses u := fun h => hi (Finset.mem_sdiff.mp h).1
    rw [ite_eq_right hb, ite_eq_right hs, zero_add]
    have hm : m.val ∉ cappedOccupations J N u := by
      intro h
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ m, h⟩)
    rw [fibre_entropy_support Φ hsupport m hm, mul_zero]

/-- The actual path constant uses the already proved Green lower bound. -/
def fibreConstant (J : ℕ) (β₀ : ℝ) : ℝ :=
  4*(J : ℝ)^3/CellNormalizerBounds.kappaConstant β₀ MovingPoleCalculus.greenLowerConstant
    kernelConstant J (radius β₀)

def entropyConstant (J : ℕ) (β₀ u cFar : ℝ) : ℝ :=
  OccupationCriterion.entropyConstant J β₀ u cFar+tau J*fibreConstant J β₀+
    2*Real.log J/sparseCoefficient J β₀ cFar

def defectConstant (J : ℕ) (β₀ u cFar : ℝ) : ℝ :=
  OccupationCriterion.defectConstant J β₀ u cFar+
    2*sparseLoss J β₀*Real.log J/sparseCoefficient J β₀ cFar

/-- All particle thresholds depend only on the fixed source parameters.
The final term is the literal one-particle cap buffer required by the paths. -/
def particleThreshold (J : ℕ) (β₀ t u cFar : ℝ) : ℕ :=
  max (OccupationCriterion.particleThreshold J β₀ t u cFar)
    (max (OccupationNearImbalance.particleThreshold J β₀ t) ⌈1/(t-u)⌉₊)

/-- Source full-label entropy, retaining only the literal far-imbalance
premise. Original subprobability weights, outer edges and zero extensions are
unchanged; no sparse-mass, multislice, projection or occupation-LSI input is assumed. -/
theorem full_label_entropy_of_far {β β₀ u cFar : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t < occupationBound β₀)
    (hu : 0 < u) (hu1 : u < 1) (hut : u < 3*t/4)
    (hmesh : 8*(radius β₀+4) ≤ J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀ ≤ J)
    (hresolution : HeavyScales.sourceResolution β₀ (u/2) ≤ J)
    (hsmall : 1/(J^2:ℕ) < t/8) (hinner : 1/(J^2:ℕ) < u)
    (hcFar : 0 < cFar) (hlarge : particleThreshold J β₀ t u cFar ≤ N)
    (hfar : OccupationCoercivity.FarImbalance (N:=N) (t:=t) (mesh_pos hmesh) β β₀ cFar)
    (Φ : LabelState J N t → ℝ) (hΦ : ∀ η, 0 ≤ Φ η)
    (hsupport : ∀ η, ¬OccupationCap u η.val → Φ η = 0) :
    FibreEntropy.finiteEntropy (labelWeight (mesh_pos hmesh) β) Φ ≤
      entropyConstant J β₀ u cFar*labelEnergy (mesh_pos hmesh) β (fun η => Real.sqrt (Φ η))+
        defectConstant J β₀ u cFar*∑ η, labelWeight (mesh_pos hmesh) β η*Φ η := by
  classical
  have hocc : OccupationCriterion.particleThreshold J β₀ t u cFar ≤ N :=
    (le_max_left _ _).trans hlarge
  have hnear : OccupationNearImbalance.particleThreshold J β₀ t ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hceil : ⌈1/(t-u)⌉₊ ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hb := OccupationNearImbalance.particleThreshold_bounds (hβ.trans hβ₀) hsub ht hnear
  have hut' : u < t := by linarith only [hut, ht]
  have hbuffer : 1 ≤ (t-u)*N := by
    have hh : 1/(t-u) ≤ (N : ℝ) := (Nat.ceil_le).mp hceil
    have hp := (div_le_iff₀ (sub_pos.mpr hut')).mp hh
    nlinarith only [hp]
  have ho := occupation_entropy_term hβ hβ₀ hsub ht htC.le hu hu1 hut hmesh hnearJ hresolution
    hsmall hinner hcFar hocc hfar Φ hΦ hsupport
  have hbal := balanced_fibre_sum hb.2.2.2.1 hβ hβ₀ hsub hu hut' htC le_rfl
    MovingPoleCalculus.greenLowerConstant_pos.le MovingPoleCalculus.green_lower_bound
    hmesh hbuffer (balancedClasses u)
    (fun m hm => (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2)
    (fun m hm => (Finset.mem_filter.mp hm).2) Φ hΦ
  have hsp := sparse_fibre_sum hβ hβ₀ hsub ht htC.le hut hmesh hnearJ hnear hcFar hfar Φ hΦ hsupport
  rw [fibre_entropy_chain, fibre_entropy_split (mesh_pos hmesh) β Φ hsupport]
  unfold entropyConstant defectConstant fibreConstant
  exact (add_le_add (add_le_add hbal hsp) ho).trans_eq (by ring)

/-- The same result in the existing genuine extended-entropy convention. -/
theorem actual_full_label_entropy_of_far {β β₀ u cFar : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t < occupationBound β₀)
    (hu : 0 < u) (hu1 : u < 1) (hut : u < 3*t/4)
    (hmesh : 8*(radius β₀+4) ≤ J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀ ≤ J)
    (hresolution : HeavyScales.sourceResolution β₀ (u/2) ≤ J)
    (hsmall : 1/(J^2:ℕ) < t/8) (hinner : 1/(J^2:ℕ) < u)
    (hcFar : 0 < cFar) (hlarge : particleThreshold J β₀ t u cFar ≤ N)
    (hfar : OccupationCoercivity.FarImbalance (N:=N) (t:=t) (mesh_pos hmesh) β β₀ cFar)
    (Φ : LabelState J N t → ℝ) (hΦ : ∀ η, 0 ≤ Φ η)
    (hsupport : ∀ η, ¬OccupationCap u η.val → Φ η = 0) :
    entropy (finiteMeasure (labelWeight (mesh_pos hmesh) β)) Φ ≤
      ((entropyConstant J β₀ u cFar*labelEnergy (mesh_pos hmesh) β (fun η => Real.sqrt (Φ η))+
        defectConstant J β₀ u cFar*∑ η, labelWeight (mesh_pos hmesh) β η*Φ η : ℝ) : EReal) := by
  have hw : ∀ η : LabelState J N t, 0 ≤ labelWeight (mesh_pos hmesh) β η :=
    fun _ => ENNReal.toReal_nonneg
  rw [entropy_finiteMeasure (labelWeight (mesh_pos hmesh) β) Φ hw hΦ]
  exact_mod_cast full_label_entropy_of_far hβ hβ₀ hsub ht htC hu hu1 hut hmesh hnearJ hresolution
    hsmall hinner hcFar hlarge hfar Φ hΦ hsupport

end PeriodicAttractiveLogGas.FullLabelEntropy
