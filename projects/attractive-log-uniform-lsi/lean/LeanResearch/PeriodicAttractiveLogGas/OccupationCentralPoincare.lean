import LeanResearch.PeriodicAttractiveLogGas.OccupationNearImbalance
import LeanResearch.PeriodicAttractiveLogGas.OccupationCentralLogGradient
import LeanResearch.PeriodicAttractiveLogGas.FiniteBoxPoincare
import LeanResearch.PeriodicAttractiveLogGas.FiniteGraphTransport

/-! Source2063–2092: composition of the genuine rounded-center bound,
actual coordinate increments and conditional PI on the occupation graph. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.OccupationCentralPoincare
open MeshCells LabelOccupations LabelRatioTransport DiscreteOccupationIdentities
  OccupationCoordinates OccupationAbsoluteMass OccupationCentralRates
  OccupationCentralLogGradient ConditionalLawEstimates OccupationProbability FiniteGraph FiniteEntropyLocalization

/-- The finite image of the actual occupation-coordinate bijection. -/
def coordinateDomain (J N : ℕ) (t : ℝ) : Finset (Interior J) := by
  classical
  exact Finset.univ.image (stateCoordinates (J:=J) (N:=N) (t:=t))

/-- No alternate state space: this is precisely the image of the original states. -/
def coordinateEquiv (J N : ℕ) (t : ℝ) :
    OccupationState J N t ≃ ↥(coordinateDomain J N t) := by
  classical
  refine Equiv.ofBijective
    (fun m => ⟨stateCoordinates m, Finset.mem_image.mpr ⟨m, Finset.mem_univ _, rfl⟩⟩) ?_
  constructor
  · intro m n h
    apply stateCoordinates_injective
    exact congrArg (fun z : ↥(coordinateDomain J N t) => z.val) h
  · intro y
    obtain ⟨m, _, hm⟩ := Finset.mem_image.mp y.property
    exact ⟨m, Subtype.ext hm⟩

theorem coordinateEquiv_val {J N : ℕ} {t : ℝ} (m : OccupationState J N t) :
    (coordinateEquiv J N t m).val = stateCoordinates m := rfl

theorem coordinates_inverse {J N : ℕ} {t : ℝ} (y : ↥(coordinateDomain J N t)) :
    stateCoordinates ((coordinateEquiv J N t).symm y) = y.val := by
  exact congrArg Subtype.val ((coordinateEquiv J N t).apply_symm_apply y)

theorem coordinateWeight_inverse {J N : ℕ} {t : ℝ} (hJ : 0<J) (β : ℝ)
    (y : ↥(coordinateDomain J N t)) :
    coordinateWeight (N:=N) (t:=t) hJ β y.val =
      occupationWeight hJ β ((coordinateEquiv J N t).symm y) := by
  simpa only [coordinates_inverse] using
    coordinateWeight_state hJ β ((coordinateEquiv J N t).symm y)

def coordinateRate {J N : ℕ} {t : ℝ} (hJ : 0<J) (β : ℝ)
    (x y : ↥(coordinateDomain J N t)) : ℝ :=
  occupationRate hJ β ((coordinateEquiv J N t).symm x) ((coordinateEquiv J N t).symm y)

theorem coordinateRate_state {J N : ℕ} {t : ℝ} (hJ : 0<J) (β : ℝ)
    (m n : OccupationState J N t) :
    coordinateRate hJ β (coordinateEquiv J N t m) (coordinateEquiv J N t n) =
      occupationRate hJ β m n := by
  simp only [coordinateRate, Equiv.symm_apply_apply]

/-- The smaller source cube has radius centralEpsilon*N; epsilon_c is half
centralEpsilon, leaving the larger cube available for mixed differences. -/
theorem coordinateDomain_contains {J N : ℕ} {t : ℝ}
    (hJ : 0<J) (hcounts : 8*J^2≤N) (hsmall : 1/(J^2:ℕ)<t/8)
    (y : Interior J)
    (hy : ∀ i, |((y i-interior (cumulative (rounded J N)) i:ℤ):ℝ)|≤centralEpsilon J*N) :
    y ∈ coordinateDomain J N t := by
  classical
  have hε := centralEpsilon_pos hJ
  have hz : 0≤centralEpsilon J*(N:ℝ) := mul_nonneg hε.le (Nat.cast_nonneg _)
  have hy' : ∀ i, |((y i-interior (cumulative (rounded J N)) i:ℤ):ℝ)|≤2*centralEpsilon J*N :=
    fun i => (hy i).trans (by nlinarith only [hz])
  exact Finset.mem_image.mpr
    ⟨centralState hJ hcounts hsmall y hy', Finset.mem_univ _,
      centralState_coordinates hJ hcounts hsmall y hy'⟩

/-- Fixed particle threshold for the actual center and rectangle margins. -/
def particleThreshold (J : ℕ) (β₀ t : ℝ) : ℕ :=
  max (OccupationNearImbalance.particleThreshold J β₀ t) (64*J^2)

def incrementConstant (J : ℕ) (β₀ : ℝ) : ℝ :=
  gradientCoefficient J β₀ (OccupationNearImbalance.roundedConstant J β₀)

theorem incrementConstant_nonneg (J : ℕ) {β₀ : ℝ} (hβ₀ : 0≤β₀) :
    0 ≤ incrementConstant J β₀ :=
  gradientCoefficient_nonneg J β₀ _ hβ₀

/-- The actual occupation log-increment bound, with its rounded-center
imbalance input now proved rather than assumed. -/
theorem actual_log_increment {J N : ℕ} {t β β₀ : ℝ}
    (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤occupationBound β₀)
    (hmesh : 8*(radius β₀+4)≤J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀≤J)
    (hlarge : particleThreshold J β₀ t≤N) (hsmall : 1/(J^2:ℕ)<t/8) :
    IntegerBoxMassGeometry.LogIncrementBound (interior (cumulative (rounded J N)))
      (centralEpsilon J*N) N (incrementConstant J β₀)
      (coordinateWeight (N:=N) (t:=t) (mesh_pos hmesh) β) := by
  have hn : OccupationNearImbalance.particleThreshold J β₀ t≤N :=
    (le_max_left _ _).trans hlarge
  have hc : 64*J^2≤N := (le_max_right _ _).trans hlarge
  have hb := OccupationNearImbalance.particleThreshold_bounds (hβ.trans hβ₀) hsub ht hn
  apply source_log_increment hβ hβ₀ hsub ht htC hmesh hb.2.1 hc hsmall
  exact OccupationNearImbalance.rounded_imbalance_upper hβ hβ₀ hsub ht htC hmesh
    hnearJ hn hsmall (roundedState (mesh_pos hmesh) (by omega) hsmall) rfl

/-- The source positive coordinate rates in the literal finite image. -/
theorem coordinate_rate_lower {J N : ℕ} {t β β₀ : ℝ}
    (hN : 2≤N) (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤occupationBound β₀)
    (hmesh : 8*(radius β₀+4)≤J) (hcounts : 8*J^2≤N)
    (hsmall : 1/(J^2:ℕ)<t/8)
    (x z : ↥(coordinateDomain J N t))
    (hx : ∀ i, |((x.val i-interior (cumulative (rounded J N)) i:ℤ):ℝ)|≤centralEpsilon J*N)
    (i : Fin (J^2-1)) (he : z.val=Function.update x.val i (x.val i+1)) :
    (lowerBound β₀/(4*(J^2:ℕ)))*N ≤ coordinateRate (mesh_pos hmesh) β x z := by
  let m := (coordinateEquiv J N t).symm x
  let n := (coordinateEquiv J N t).symm z
  have hm : stateCoordinates m=x.val := coordinates_inverse x
  have hn : stateCoordinates n=z.val := coordinates_inverse z
  have hp := forward_permitted (mesh_pos hmesh) (mesh_two_le hmesh) m n i
    (by rw [hm,hn]; exact he)
  have hε := centralEpsilon_pos (mesh_pos hmesh)
  have hz : 0≤centralEpsilon J*(N:ℝ) := mul_nonneg hε.le (Nat.cast_nonneg _)
  have hcentral : ∀ k, |((interior (cumulative m.val) k-interior (cumulative (rounded J N)) k:ℤ):ℝ)|
      ≤2*centralEpsilon J*N := by
    change ∀ k, |((stateCoordinates m k-interior (cumulative (rounded J N)) k:ℤ):ℝ)|≤_
    rw [hm]
    exact fun k => (hx k).trans (by nlinarith only [hz])
  exact central_rate_lower hN hβ hβ₀ hsub ht htC hmesh hp
    (central_counts (mesh_pos hmesh) hcounts hsmall m hcentral _)

def poincareConstant (J : ℕ) (β₀ M : ℝ) : ℝ :=
  Real.exp (8*(J^2-1:ℕ)*incrementConstant J β₀*(M+M^2))*(2*M+1)^2/
    (lowerBound β₀/(4*(J^2:ℕ)))

theorem poincareConstant_nonneg (J : ℕ) (β₀ M : ℝ) :
    0≤poincareConstant J β₀ M := by
  have := (lowerBound_pos β₀).le
  unfold poincareConstant
  positivity

/-- The actual coordinate law satisfies the central PI, with uniform
constants and only primitive numerical/source gates. -/
theorem coordinate_central_poincare {J N : ℕ} {t β β₀ M : ℝ}
    (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤occupationBound β₀)
    (hmesh : 8*(radius β₀+4)≤J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀≤J)
    (hlarge : particleThreshold J β₀ t≤N) (hsmall : 1/(J^2:ℕ)<t/8)
    (hM : 0≤M) (hMT : M*Real.sqrt N≤centralEpsilon J*N)
    (F : ↥(coordinateDomain J N t) → ℝ) :
    let B := FiniteBoxPoincare.centralBox (coordinateDomain J N t)
      (interior (cumulative (rounded J N))) (M*Real.sqrt N)
    let W := fun z : ↥(coordinateDomain J N t) =>
      coordinateWeight (N:=N) (t:=t) (mesh_pos hmesh) β z.val
    (∑ z ∈ B, W z*(F z-FiniteBoxPoincare.mean (conditionalWeight W B) F)^2) ≤
      poincareConstant J β₀ M *
        energy (restrictedWeight W B) (restrictedRates (coordinateRate (mesh_pos hmesh) β) B) F := by
  have hn : OccupationNearImbalance.particleThreshold J β₀ t≤N :=
    (le_max_left _ _).trans hlarge
  have hb := OccupationNearImbalance.particleThreshold_bounds (hβ.trans hβ₀) hsub ht hn
  have hN : 2≤N := hb.2.2.2.1
  have hcounts : 8*J^2≤N := hb.2.2.1
  have hc : 0<lowerBound β₀/(4*(J^2:ℕ)) :=
    div_pos (lowerBound_pos β₀) (by have := mesh_pos hmesh; positivity)
  apply FiniteBoxPoincare.source_central_box_poincare (by omega)
    (coordinateDomain J N t) (interior (cumulative (rounded J N)))
    (coordinateWeight (N:=N) (t:=t) (mesh_pos hmesh) β) F
    (coordinateRate (mesh_pos hmesh) β) hM (incrementConstant_nonneg J (hβ.trans hβ₀)) hc hMT
  · exact coordinateDomain_contains (mesh_pos hmesh) hcounts hsmall
  · intro y hy
    rw [coordinateWeight_inverse (mesh_pos hmesh) β ⟨y,hy⟩]
    exact LabelGroundState.occupationWeight_pos (mesh_pos hmesh) hN hβ (hβ₀.trans_lt hsub) _
  · intro x z
    exact occupationRate_nonneg (mesh_pos hmesh) β _ _
  · intro x z
    rw [coordinateWeight_inverse (mesh_pos hmesh) β x,
      coordinateWeight_inverse (mesh_pos hmesh) β z]
    exact occupation_detailed_balance (mesh_pos hmesh) (mesh_two_le hmesh) β _ _
  · exact actual_log_increment hβ hβ₀ hsub ht htC hmesh hnearJ hlarge hsmall
  · intro x z hx _hz i he
    exact coordinate_rate_lower hN hβ hβ₀ hsub ht htC hmesh hcounts hsmall x z hx i he


/-- The source central ball in the original occupation states. -/
def centralBall (J N : ℕ) (t M : ℝ) : Finset (OccupationState J N t) :=
  coordinateBall stateCoordinates (interior (cumulative (rounded J N))) (M*Real.sqrt N)

theorem centralBall_corresponds {J N : ℕ} {t M : ℝ} (hM : 0≤M)
    (m : OccupationState J N t) :
    m ∈ centralBall J N t M ↔ coordinateEquiv J N t m ∈
      FiniteBoxPoincare.centralBox (coordinateDomain J N t)
        (interior (cumulative (rounded J N))) (M*Real.sqrt N) := by
  classical
  rw [FiniteBoxPoincare.mem_centralBox_iff _ _ (mul_nonneg hM (Real.sqrt_nonneg _))]
  simp only [centralBall, coordinateBall, Finset.mem_filter, Finset.mem_univ,
    true_and, coordinateEquiv_val]

/-- Source central cube and count assertions on actual occupation states. -/
theorem central_state_properties {J N : ℕ} {t : ℝ}
    (hJ : 0<J) (hcounts : 8*J^2≤N) (hsmall : 1/(J^2:ℕ)<t/8)
    (m : OccupationState J N t)
    (hm : ∀ i, |((stateCoordinates m i-interior (cumulative (rounded J N)) i:ℤ):ℝ)|
      ≤centralEpsilon J*N) :
    m.val∈cappedOccupations J N (t/2) ∧
      ∀ a, (N:ℝ)/(2*(J^2:ℕ))≤(m.val a:ℝ) := by
  have hε := centralEpsilon_pos hJ
  have hz : 0≤centralEpsilon J*(N:ℝ) := mul_nonneg hε.le (Nat.cast_nonneg _)
  have hm' : ∀ i, |((stateCoordinates m i-interior (cumulative (rounded J N)) i:ℤ):ℝ)|
      ≤2*centralEpsilon J*N := fun i => (hm i).trans (by nlinarith only [hz])
  have he : centralState hJ hcounts hsmall (stateCoordinates m) hm'=m :=
    stateCoordinates_injective (centralState_coordinates hJ hcounts hsmall _ hm')
  constructor
  · rw [← he]
    exact centralState_half_cap hJ hcounts hsmall _ hm'
  · exact central_counts hJ hcounts hsmall m hm'

/-- The supplied conditional central PI, now on the genuine original
occupation graph, with the exact original conditional mean and internal energy. -/
theorem occupation_central_poincare {J N : ℕ} {t β β₀ M : ℝ}
    (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤occupationBound β₀)
    (hmesh : 8*(radius β₀+4)≤J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀≤J)
    (hlarge : particleThreshold J β₀ t≤N) (hsmall : 1/(J^2:ℕ)<t/8)
    (hM : 0≤M) (hMT : M*Real.sqrt N≤centralEpsilon J*N)
    (F : OccupationState J N t → ℝ) :
    let B := centralBall J N t M
    let w := occupationWeight (mesh_pos hmesh) β
    let c := FiniteBoxPoincare.mean (conditionalWeight w B) F
    (∑ m ∈ B, w m*(F m-c)^2) ≤ poincareConstant J β₀ M *
      energy (restrictedWeight w B) (restrictedRates (occupationRate (mesh_pos hmesh) β) B) F := by
  let e := coordinateEquiv J N t
  let B := FiniteBoxPoincare.centralBox (coordinateDomain J N t)
    (interior (cumulative (rounded J N))) (M*Real.sqrt N)
  let w := fun z : ↥(coordinateDomain J N t) =>
    coordinateWeight (N:=N) (t:=t) (mesh_pos hmesh) β z.val
  let G := fun z => F (e.symm z)
  have hh := coordinate_central_poincare hβ hβ₀ hsub ht htC hmesh hnearJ
    hlarge hsmall hM hMT G
  exact FiniteGraphTransport.internal_poincare_transport e
    (centralBall J N t M) B (centralBall_corresponds hM)
    (occupationWeight (mesh_pos hmesh) β) w
    (occupationRate (mesh_pos hmesh) β) (coordinateRate (mesh_pos hmesh) β) F G
    (fun m => coordinateWeight_state (mesh_pos hmesh) β m)
    (coordinateRate_state (mesh_pos hmesh) β)
    (fun m => by dsimp only [G]; rw [Equiv.symm_apply_apply])
    (poincareConstant J β₀ M) hh

/-- Fixed M is absorbed into a numerical particle threshold, uniformly in beta. -/
def boxThreshold (J : ℕ) (β₀ t M : ℝ) : ℕ :=
  max (particleThreshold J β₀ t) ⌈(M/centralEpsilon J)^2⌉₊

theorem boxThreshold_radius {J N : ℕ} {β₀ t M : ℝ} (hJ : 0<J) (hM : 0≤M)
    (hlarge : boxThreshold J β₀ t M≤N) :
    M*Real.sqrt N≤centralEpsilon J*N := by
  have hε := centralEpsilon_pos hJ
  have hn : ⌈(M/centralEpsilon J)^2⌉₊≤N := (le_max_right _ _).trans hlarge
  have hh : (M/centralEpsilon J)^2≤(N:ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
  have hd : 0≤M/centralEpsilon J := div_nonneg hM hε.le
  have hs := Real.sq_sqrt (Nat.cast_nonneg N)
  have hsr := Real.sqrt_nonneg (N:ℝ)
  have hroot : M/centralEpsilon J≤Real.sqrt N := by nlinarith only [hh,hd,hs,hsr]
  have hMε : M≤Real.sqrt N*centralEpsilon J := (div_le_iff₀ hε).mp hroot
  have hp := mul_le_mul_of_nonneg_right hMε hsr
  calc
    _ ≤ Real.sqrt N*centralEpsilon J*Real.sqrt N := hp
    _ = centralEpsilon J*(Real.sqrt N)^2 := by ring
    _ = _ := by rw [hs]

/-- All analytic conclusions in source central comparison are discharged.
Only the fixed source parameter gates and an explicit particle threshold remain. -/
theorem source_central_poincare {J N : ℕ} {t β β₀ M : ℝ}
    (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤occupationBound β₀)
    (hmesh : 8*(radius β₀+4)≤J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀≤J)
    (hsmall : 1/(J^2:ℕ)<t/8) (hM : 0≤M)
    (hlarge : boxThreshold J β₀ t M≤N) (F : OccupationState J N t → ℝ) :
    let B := centralBall J N t M
    let w := occupationWeight (mesh_pos hmesh) β
    let c := FiniteBoxPoincare.mean (conditionalWeight w B) F
    (∑ m ∈ B, w m*(F m-c)^2) ≤ poincareConstant J β₀ M *
      energy (restrictedWeight w B) (restrictedRates (occupationRate (mesh_pos hmesh) β) B) F :=
  occupation_central_poincare hβ hβ₀ hsub ht htC hmesh hnearJ
    ((le_max_left _ _).trans hlarge) hsmall hM
    (boxThreshold_radius (mesh_pos hmesh) hM hlarge) F

end PeriodicAttractiveLogGas.OccupationCentralPoincare
