import LeanResearch.PeriodicAttractiveLogGas.OccupationCentralPoincare
import LeanResearch.PeriodicAttractiveLogGas.OccupationBufferPoincare

/-! Actual global lower and near quadratic ground-state bounds. The final
buffer assembly isolates only the genuine far-imbalance input. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.OccupationCoercivity
open MeshCells LabelOccupations DiscreteOccupationIdentities LabelGroundState
open ConditionalLawEstimates OccupationCoordinates OccupationAbsoluteMass
open OccupationDrift OccupationSecondDifferences OccupationNearImbalance
open DyadicShellPartition

/-- Exact additive loss in the proved original unordered-edge drift bound. -/
def lowerLoss (J : ℕ) (β₀ : ℝ) : ℝ :=
  10*(J^2:ℕ)*(1+secondDifferenceConstant J β₀/4)

theorem lowerLoss_nonneg (J : ℕ) {β₀ : ℝ} (hβ₀ : 0≤β₀) : 0≤lowerLoss J β₀ := by
  have := secondDifferenceConstant_nonneg J hβ₀
  unfold lowerLoss
  positivity

theorem imbalance_nonneg {J N : ℕ} {t : ℝ} (hJ : 0<J) (β : ℝ)
    (m : OccupationState J N t) (hm : m.val∈cappedOccupations J N (3*t/4))
    (hmargin : 4≤t*N) : 0 ≤ imbalance hJ β m hm hmargin := by
  classical
  unfold imbalance unorderedSum
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  split <;> positivity

/-- No far-region assumption is needed for this global lower bound. -/
theorem ground_state_lower {J N : ℕ} {t β β₀ : ℝ}
    (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤occupationBound β₀)
    (hmesh : 8*(ConditionalLawEstimates.radius β₀+4)≤J)
    (hlarge : secondDifferenceThreshold J β₀≤N) (hmargin : 4≤t*N)
    (m : OccupationState J N t) (hm : m.val∈cappedOccupations J N (3*t/4)) :
    -lowerLoss J β₀ ≤ occupationW (mesh_pos hmesh) β m := by
  have hh := occupation_W_bound hβ hβ₀ hsub ht htC hmesh hlarge hmargin m hm
  have hn := imbalance_nonneg (mesh_pos hmesh) β m hm hmargin
  unfold lowerLoss
  linarith

/-- Full normalization from actual occupation profile squares to actual
cumulative-coordinate sup distance, including the fixed-dimensional factor. -/
theorem coordinate_distance_square {J N : ℕ} {t : ℝ} (hN : 0<N)
    (m : OccupationState J N t) :
    ‖fun i => ((stateCoordinates m i-interior (cumulative (rounded J N)) i:ℤ):ℝ)‖^2 ≤
      (J^2:ℕ)^2*(N:ℝ)^2*(∑ a, (stateProfile m a-(rounded J N a:ℝ)/N)^2) := by
  classical
  let S := ∑ a, (stateProfile m a-(rounded J N a:ℝ)/N)^2
  have hS : 0≤S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hs := Real.sq_sqrt hS
  have hdiff (a : MeshIndex J) : |(m.val a:ℝ)-rounded J N a|≤N*Real.sqrt S := by
    have ha : (stateProfile m a-(rounded J N a:ℝ)/N)^2≤S :=
      Finset.single_le_sum (fun b _ => sq_nonneg (stateProfile m b-(rounded J N b:ℝ)/N)) (Finset.mem_univ a)
    have hb : |stateProfile m a-(rounded J N a:ℝ)/N|≤Real.sqrt S := by
      nlinarith [sq_abs (stateProfile m a-(rounded J N a:ℝ)/N),
        abs_nonneg (stateProfile m a-(rounded J N a:ℝ)/N), Real.sqrt_nonneg S]
    have he : (m.val a:ℝ)-rounded J N a = N*(stateProfile m a-(rounded J N a:ℝ)/N) := by
      rw [stateProfile_apply]
      field_simp
    rw [he, abs_mul, abs_of_pos hn]
    exact mul_le_mul_of_nonneg_left hb hn.le
  have hc : ‖fun a => (m.val a:ℝ)-rounded J N a‖≤N*Real.sqrt S := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hn.le (Real.sqrt_nonneg S))).mpr
    intro a
    simpa only [Real.norm_eq_abs] using hdiff a
  have hh := (interior_norm_le m.val (rounded J N)).trans
    (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (J^2)))
  have hp := pow_le_pow_left₀ (norm_nonneg _) hh 2
  change ‖fun i => ((interior (cumulative m.val) i-interior (cumulative (rounded J N)) i:ℤ):ℝ)‖^2 ≤ _
  simpa only [mul_pow, hs, S, mul_assoc] using hp

def nearCoefficient (J : ℕ) (β₀ : ℝ) : ℝ :=
  coercivityConstant J β₀/(4*(J^2:ℕ)^2)

def nearLoss (J : ℕ) (β₀ : ℝ) : ℝ :=
  lowerLoss J β₀+translatedConstant J β₀/2

theorem nearCoefficient_pos {J : ℕ} (hJ : 0<J) {β₀ : ℝ} (hsub : β₀<4) :
    0<nearCoefficient J β₀ := by
  have := coercivityConstant_pos hJ hsub
  have : (0:ℝ)<(J^2:ℕ) := Nat.cast_pos.mpr (pow_pos hJ _)
  unfold nearCoefficient
  positivity

theorem nearLoss_nonneg {J : ℕ} (hJ : 0<J) {β₀ : ℝ} (hβ₀ : 0≤β₀) (hsub : β₀<4) :
    0≤nearLoss J β₀ :=
  add_nonneg (lowerLoss_nonneg J hβ₀) (div_nonneg (translatedConstant_nonneg hJ hsub) (by norm_num))

/-- Genuine near-region quadratic drift in the source's literal sup radius. -/
theorem near_ground_state {J N : ℕ} {t β β₀ : ℝ}
    (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤occupationBound β₀)
    (hmesh : 8*(ConditionalLawEstimates.radius β₀+4)≤J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀≤J)
    (hlarge : OccupationNearImbalance.particleThreshold J β₀ t≤N)
    (m : OccupationState J N t)
    (hnear : OccupationNearContraction.profileDeviation (stateProfile m)≤nearNeighborhood β₀)
    (hm : m.val∈cappedOccupations J N (3*t/4)) :
    nearCoefficient J β₀ *
      (DyadicShellPartition.radius N (interior (cumulative (rounded J N))) (stateCoordinates m))^2 -
      nearLoss J β₀ ≤ occupationW (mesh_pos hmesh) β m := by
  have hb := OccupationNearImbalance.particleThreshold_bounds (hβ.trans hβ₀) hsub ht hlarge
  have hN : 0<N := by omega
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hJ : (0:ℝ)<(J^2:ℕ) := Nat.cast_pos.mpr (pow_pos (mesh_pos hmesh) _)
  have hc := (coercivityConstant_pos (mesh_pos hmesh) hsub).le
  have hi := near_rounded_imbalance hβ hβ₀ hsub ht htC hmesh hnearJ hlarge m hnear hm
  dsimp only at hi
  have hw := occupation_W_bound hβ hβ₀ hsub ht htC hmesh hb.2.1 hb.2.2.2.2.1 m hm
  have hd := coordinate_distance_square hN m
  let d := ‖fun i => ((stateCoordinates m i-interior (cumulative (rounded J N)) i:ℤ):ℝ)‖
  let S := ∑ a, (stateProfile m a-(rounded J N a:ℝ)/N)^2
  change d^2≤(J^2:ℕ)^2*(N:ℝ)^2*S at hd
  have hdiv : d^2/((J^2:ℕ)^2*N)≤N*S := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hd]
  have hp := mul_le_mul_of_nonneg_left hdiv (div_nonneg hc (by norm_num : (0:ℝ)≤4))
  have he : nearCoefficient J β₀ *
      (DyadicShellPartition.radius N (interior (cumulative (rounded J N))) (stateCoordinates m))^2 =
      (coercivityConstant J β₀/4)*(d^2/((J^2:ℕ)^2*N)) := by
    unfold nearCoefficient DyadicShellPartition.radius
    change coercivityConstant J β₀/(4*(J^2:ℕ)^2)*(d/Real.sqrt N)^2 = _
    rw [div_pow, Real.sq_sqrt hn.le]
    ring
  rw [he]
  unfold nearLoss lowerLoss
  dsimp only [S] at hp
  nlinarith only [hi, hw, hp]


/-- This is the only unresolved analytic input in the assembly: a literal
far-subset lower bound on the original unordered occupation imbalance. -/
def FarImbalance {J N : ℕ} {t : ℝ} (hJ : 0<J) (β β₀ cFar : ℝ) : Prop :=
  ∀ (m : OccupationState J N t) (hm : m.val∈cappedOccupations J N (3*t/4))
    (hmargin : 4≤t*N),
    nearNeighborhood β₀ < OccupationNearContraction.profileDeviation (stateProfile m) →
      cFar*N ≤ imbalance hJ β m hm hmargin

/-- Exact conditional capped drift, useful for the absolute-mass and entropy
criterion. The far-imbalance input is fully exposed in the statement. -/
theorem capped_ground_state_of_far {J N : ℕ} {t β β₀ cFar : ℝ}
    (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤occupationBound β₀)
    (hmesh : 8*(ConditionalLawEstimates.radius β₀+4)≤J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀≤J)
    (hlarge : OccupationNearImbalance.particleThreshold J β₀ t≤N)
    (hcFar : 0<cFar) (hfar : FarImbalance (N:=N) (t:=t) (mesh_pos hmesh) β β₀ cFar)
    (m : OccupationState J N t) (hm : m.val∈cappedOccupations J N (3*t/4)) :
    min (nearCoefficient J β₀) (cFar/2) *
      min ((DyadicShellPartition.radius N (interior (cumulative (rounded J N))) (stateCoordinates m))^2)
        (N:ℝ) - nearLoss J β₀ ≤ occupationW (mesh_pos hmesh) β m := by
  have hb := OccupationNearImbalance.particleThreshold_bounds (hβ.trans hβ₀) hsub ht hlarge
  have ha := (nearCoefficient_pos (mesh_pos hmesh) hsub).le
  by_cases hnear : OccupationNearContraction.profileDeviation (stateProfile m)≤nearNeighborhood β₀
  · have hh := near_ground_state hβ hβ₀ hsub ht htC hmesh hnearJ hlarge m hnear hm
    have hp := mul_le_mul (min_le_left (nearCoefficient J β₀) (cFar/2))
      (min_le_left ((DyadicShellPartition.radius N (interior (cumulative (rounded J N))) (stateCoordinates m))^2) (N:ℝ))
      (le_min (sq_nonneg _) (Nat.cast_nonneg N)) ha
    linarith only [hh,hp]
  · have hi := hfar m hm hb.2.2.2.2.1 (lt_of_not_ge hnear)
    have hw := occupation_W_bound hβ hβ₀ hsub ht htC hmesh hb.2.1 hb.2.2.2.2.1 m hm
    have hp := mul_le_mul (min_le_right (nearCoefficient J β₀) (cFar/2))
      (min_le_right ((DyadicShellPartition.radius N (interior (cumulative (rounded J N))) (stateCoordinates m))^2) (N:ℝ))
      (le_min (sq_nonneg _) (Nat.cast_nonneg N)) (by positivity : 0≤cFar/2)
    have hl := translatedConstant_nonneg (mesh_pos hmesh) hsub
    unfold nearLoss lowerLoss
    nlinarith only [hi,hw,hp,hl]

/-- A fixed radius; its value depends only on the fixed mesh and beta bound. -/
def chosenRadius (J : ℕ) (β₀ : ℝ) : ℝ :=
  Real.sqrt ((nearLoss J β₀+1)/nearCoefficient J β₀)

theorem chosenRadius_nonneg (J : ℕ) (β₀ : ℝ) : 0≤chosenRadius J β₀ := Real.sqrt_nonneg _

theorem chosenRadius_identity {J : ℕ} (hJ : 0<J) {β₀ : ℝ}
    (hβ₀ : 0≤β₀) (hsub : β₀<4) :
    nearCoefficient J β₀*(chosenRadius J β₀)^2=nearLoss J β₀+1 := by
  have ha := nearCoefficient_pos hJ hsub
  have hb := nearLoss_nonneg hJ hβ₀ hsub
  unfold chosenRadius
  rw [Real.sq_sqrt (by positivity)]
  field_simp

theorem centralBall_of_radius_le {J N : ℕ} {t M : ℝ} (hN : 0<N)
    (m : OccupationState J N t)
    (hρ : DyadicShellPartition.radius N (interior (cumulative (rounded J N))) (stateCoordinates m)≤M) :
    m∈OccupationCentralPoincare.centralBall J N t M := by
  classical
  have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hh := (div_le_iff₀ hs).mp hρ
  simp only [OccupationCentralPoincare.centralBall, coordinateBall, Finset.mem_filter,
    Finset.mem_univ, true_and]
  intro i
  have hi := norm_le_pi_norm
    (fun i => ((stateCoordinates m i-interior (cumulative (rounded J N)) i:ℤ):ℝ)) i
  have hi' : |((stateCoordinates m i-interior (cumulative (rounded J N)) i:ℤ):ℝ)| ≤
      ‖fun j => ((stateCoordinates m j-interior (cumulative (rounded J N)) j:ℤ):ℝ)‖ := by
    simpa only [Real.norm_eq_abs] using hi
  exact hi'.trans hh

def particleThreshold (J : ℕ) (β₀ t cFar : ℝ) : ℕ :=
  max (OccupationCentralPoincare.boxThreshold J β₀ t (chosenRadius J β₀))
    (max (OccupationBufferPoincare.bufferThreshold t) ⌈2*(lowerLoss J β₀+1)/cFar⌉₊)

theorem positive_off_center {J N : ℕ} {t β β₀ cFar : ℝ}
    (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤occupationBound β₀)
    (hmesh : 8*(ConditionalLawEstimates.radius β₀+4)≤J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀≤J)
    (hlarge : particleThreshold J β₀ t cFar≤N)
    (hcFar : 0<cFar) (hfar : FarImbalance (N:=N) (t:=t) (mesh_pos hmesh) β β₀ cFar)
    (m : OccupationState J N t) (hm : m.val∈cappedOccupations J N (3*t/4))
    (hout : m∉OccupationCentralPoincare.centralBall J N t (chosenRadius J β₀)) :
    1≤occupationW (mesh_pos hmesh) β m := by
  have hbox := (le_max_left _ _).trans hlarge
  have hcentral := (le_max_left _ _).trans hbox
  have hnearN : OccupationNearImbalance.particleThreshold J β₀ t≤N :=
    (le_max_left _ _).trans hcentral
  have hb := OccupationNearImbalance.particleThreshold_bounds (hβ.trans hβ₀) hsub ht hnearN
  by_cases hnear : OccupationNearContraction.profileDeviation (stateProfile m)≤nearNeighborhood β₀
  · have hh := near_ground_state hβ hβ₀ hsub ht htC hmesh hnearJ hnearN m hnear hm
    have hR : chosenRadius J β₀ < DyadicShellPartition.radius N
        (interior (cumulative (rounded J N))) (stateCoordinates m) :=
      lt_of_not_ge (fun h => hout (centralBall_of_radius_le (by omega) m h))
    have hM := chosenRadius_nonneg J β₀
    have ha := nearCoefficient_pos (mesh_pos hmesh) hsub
    have he := chosenRadius_identity (mesh_pos hmesh) (hβ.trans hβ₀) hsub
    have hp := mul_le_mul_of_nonneg_left (show (chosenRadius J β₀)^2 ≤
      (DyadicShellPartition.radius N (interior (cumulative (rounded J N))) (stateCoordinates m))^2 by nlinarith) ha.le
    nlinarith only [hh,he,hp]
  · have hi := hfar m hm hb.2.2.2.2.1 (lt_of_not_ge hnear)
    have hw := occupation_W_bound hβ hβ₀ hsub ht htC hmesh hb.2.1 hb.2.2.2.2.1 m hm
    have hn : ⌈2*(lowerLoss J β₀+1)/cFar⌉₊≤N :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
    have hn' := (Nat.le_ceil (2*(lowerLoss J β₀+1)/cFar)).trans (Nat.cast_le.mpr hn)
    have hm' := (div_le_iff₀ hcFar).mp hn'
    unfold lowerLoss at hm'
    nlinarith only [hi,hw,hm']


/-- Uniform buffered PI coefficient; N and beta do not enter this expression. -/
def bufferConstant (J : ℕ) (β₀ : ℝ) : ℝ :=
  2+(lowerLoss J β₀+1)*OccupationCentralPoincare.poincareConstant J β₀ (chosenRadius J β₀)

theorem bufferConstant_nonneg (J : ℕ) {β₀ : ℝ} (hβ₀ : 0≤β₀) :
    0≤bufferConstant J β₀ := by
  have := lowerLoss_nonneg J hβ₀
  have := OccupationCentralPoincare.poincareConstant_nonneg J β₀ (chosenRadius J β₀)
  unfold bufferConstant
  positivity

local instance {J N : ℕ} {t u : ℝ} :
    DecidablePred (fun m : OccupationState J N t => m.val∈cappedOccupations J N u) :=
  fun _ => Classical.propDecidable _

/-- Actual source buffer Poincare assembly. The ONLY unresolved analytic
premise is literal far imbalance; no W bound, PI, center imbalance, logarithmic
increment, cutoff or product-energy conclusion is assumed. -/
theorem source_buffer_poincare_of_far {J N : ℕ} {t β β₀ cFar : ℝ}
    (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤occupationBound β₀)
    (hmesh : 8*(ConditionalLawEstimates.radius β₀+4)≤J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀≤J)
    (hsmall : 1/(J^2:ℕ)<t/8)
    (hcFar : 0<cFar) (hlarge : particleThreshold J β₀ t cFar≤N)
    (hfar : FarImbalance (N:=N) (t:=t) (mesh_pos hmesh) β β₀ cFar)
    (F : OccupationState J N t → ℝ) :
    let B := OccupationCentralPoincare.centralBall J N t (chosenRadius J β₀)
    let w := occupationWeight (mesh_pos hmesh) β
    let c := FiniteBoxPoincare.mean (FiniteEntropyLocalization.conditionalWeight w B) F
    (∑ m, w m*(F m-c)^2) ≤ bufferConstant J β₀ * occupationEnergy (mesh_pos hmesh) β F +
      2*(∑ m, if m.val∈cappedOccupations J N (t/2) then 0 else w m*(F m-c)^2) := by
  have hbox : OccupationCentralPoincare.boxThreshold J β₀ t (chosenRadius J β₀)≤N :=
    (le_max_left _ _).trans hlarge
  have hcentral : OccupationCentralPoincare.particleThreshold J β₀ t≤N :=
    (le_max_left _ _).trans hbox
  have hnearN : OccupationNearImbalance.particleThreshold J β₀ t≤N :=
    (le_max_left _ _).trans hcentral
  have hb := OccupationNearImbalance.particleThreshold_bounds (hβ.trans hβ₀) hsub ht hnearN
  have hbuffer : OccupationBufferPoincare.bufferThreshold t≤N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hPI := OccupationCentralPoincare.source_central_poincare hβ hβ₀ hsub ht htC
    hmesh hnearJ hsmall (chosenRadius_nonneg J β₀) hbox F
  have hh := OccupationBufferPoincare.occupation_buffer_poincare
    (mesh_pos hmesh) (mesh_three_le hmesh) hb.2.2.2.1 hβ (hβ₀.trans_lt hsub) ht hbuffer
    (OccupationCentralPoincare.centralBall J N t (chosenRadius J β₀)) F
    (lowerLoss_nonneg J (hβ.trans hβ₀))
    (OccupationCentralPoincare.poincareConstant_nonneg J β₀ (chosenRadius J β₀))
    (fun m hm => ground_state_lower hβ hβ₀ hsub ht htC hmesh hb.2.1 hb.2.2.2.2.1 m hm)
    (fun m hm hout => positive_off_center hβ hβ₀ hsub ht htC hmesh hnearJ hlarge hcFar hfar m hm hout)
    hPI
  simpa only [bufferConstant] using! hh

end PeriodicAttractiveLogGas.OccupationCoercivity
