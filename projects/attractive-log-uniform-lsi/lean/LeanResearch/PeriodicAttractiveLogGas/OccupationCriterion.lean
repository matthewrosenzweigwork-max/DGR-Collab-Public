import LeanResearch.PeriodicAttractiveLogGas.OccupationMassInstantiation
import LeanResearch.PeriodicAttractiveLogGas.FiniteBoxLocalization

/-! The original unnormalized occupation entropy criterion, conditional only
on the explicitly named far-subset imbalance input. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.OccupationCriterion
open MeshCells LabelOccupations DiscreteOccupationIdentities LabelGroundState
open ConditionalLawEstimates OccupationCoordinates OccupationAbsoluteMass
open OccupationCentralPoincare FiniteEntropyLocalization FiniteGraph

/-- One lower constant for actual coordinate rates, point masses and drift. -/
def lowerConstant (J : ℕ) (β₀ u cFar : ℝ) : ℝ :=
  min (lowerBound β₀/(4*(J^2:ℕ)))
    (min (OccupationMassInstantiation.centerCoefficient J β₀ u cFar)
      (OccupationMassInstantiation.driftCoefficient J β₀ cFar))

/-- One upper constant for outgoing rates, increments, global masses and drift. -/
def upperConstant (J : ℕ) (β₀ _u _cFar : ℝ) : ℝ :=
  4+incrementConstant J β₀+OccupationMassInstantiation.globalExponent J β₀+
    OccupationCoercivity.nearLoss J β₀

def cubeEpsilon (J : ℕ) (u : ℝ) : ℝ := OccupationMassInstantiation.innerEpsilon J u/2

def particleThreshold (J : ℕ) (β₀ t u cFar : ℝ) : ℕ :=
  max (OccupationMassInstantiation.particleThreshold J β₀ t u cFar)
    (FiniteBoxLocalization.particleThreshold (cubeEpsilon J u))

theorem lowerConstant_pos {J : ℕ} (hJ : 0<J) {β₀ u cFar : ℝ}
    (hsub : β₀<4) (hcFar : 0<cFar) : 0<lowerConstant J β₀ u cFar := by
  have hJr : (0:ℝ)<(J^2:ℕ) := Nat.cast_pos.mpr (pow_pos hJ _)
  exact lt_min (div_pos (lowerBound_pos β₀) (by positivity))
    (lt_min (OccupationMassInstantiation.centerCoefficient_pos J β₀ u cFar)
      (OccupationMassInstantiation.driftCoefficient_pos hJ hsub hcFar))

theorem upperConstant_bounds {J : ℕ} (hJ : 0<J) {β₀ u cFar : ℝ}
    (hβ₀ : 0≤β₀) (hsub : β₀<4) :
    4≤upperConstant J β₀ u cFar ∧ incrementConstant J β₀≤upperConstant J β₀ u cFar ∧
    OccupationMassInstantiation.globalExponent J β₀≤upperConstant J β₀ u cFar ∧
    OccupationCoercivity.nearLoss J β₀≤upperConstant J β₀ u cFar := by
  have hi := incrementConstant_nonneg J hβ₀
  have hg := OccupationMassInstantiation.globalExponent_nonneg J β₀
  have hb := OccupationCoercivity.nearLoss_nonneg hJ hβ₀ hsub
  unfold upperConstant
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem cubeEpsilon_pos {J : ℕ} (hJ : 0<J) {u : ℝ} (hu : 1/(J^2:ℕ)<u) :
    0<cubeEpsilon J u := div_pos (OccupationMassInstantiation.innerEpsilon_pos hJ hu) (by norm_num)

/-- Both original occupation coordinates lie between zero and N. -/
theorem coordinate_distance_le {J N : ℕ} {t : ℝ}
    (m n : OccupationState J N t) (i : Fin (J^2-1)) :
    |((stateCoordinates m i-stateCoordinates n i:ℤ):ℝ)|≤(N:ℝ) := by
  let k : Fin (J^2+1) := ⟨i.val+1,by have := i.isLt; omega⟩
  have hm := cumulative_bounds m.val m.property.1 k
  have hn := cumulative_bounds n.val n.property.1 k
  have hh : |stateCoordinates m i-stateCoordinates n i|≤(N:ℤ) := by
    change |cumulative m.val k-cumulative n.val k|≤(N:ℤ)
    rw [abs_le]
    omega
  exact_mod_cast hh

/-- Nonzero actual rates imply actual particle moves, hence integer sup jumps at most one. -/
theorem coordinate_jump {J N : ℕ} {t : ℝ} (hJ : 0<J) (β : ℝ)
    (m n : OccupationState J N t) (hr : occupationRate hJ β m n≠0)
    (i : Fin (J^2-1)) : |stateCoordinates m i-stateCoordinates n i|≤1 := by
  classical
  have he : ∃ a b, PermittedMove hJ m n a b := by
    by_contra hh
    exact hr (occupationRate_eq_zero hJ β hh)
  obtain ⟨a,b,hmove⟩ := he
  let k : Fin (J^2+1) := ⟨i.val+1,by have := i.isLt; omega⟩
  have hh := cumulative_move_abs_le_one m.val a b hmove.2.1 k
  change |cumulative m.val k-cumulative n.val k|≤1
  rw [← hmove.2.2]
  simpa only [abs_sub_comm] using hh

theorem coordinate_potential {J N : ℕ} {t : ℝ} (hJ : 0<J) (β : ℝ)
    (x : ↥(coordinateDomain J N t)) :
    groundStatePotential (coordinateRate hJ β)
      (fun y => occupationV hJ β ((OccupationCentralPoincare.coordinateEquiv J N t).symm y)) x =
      occupationW hJ β ((OccupationCentralPoincare.coordinateEquiv J N t).symm x) := by
  let e := OccupationCentralPoincare.coordinateEquiv J N t
  have hh := FiniteGraphTransport.groundStatePotential_eq e (occupationRate hJ β)
    (coordinateRate hJ β) (occupationV hJ β) (fun y => occupationV hJ β (e.symm y))
    (coordinateRate_state hJ β) (fun m => by simp only [Equiv.symm_apply_apply]) (e.symm x)
  simpa only [Equiv.apply_symm_apply,occupationW] using hh.symm

def entropyConstant (J : ℕ) (β₀ u cFar : ℝ) : ℝ :=
  FiniteBoxLocalization.entropyConstant (J^2-1) (cubeEpsilon J u)
    (upperConstant J β₀ u cFar) (lowerConstant J β₀ u cFar)

def defectConstant (J : ℕ) (β₀ u cFar : ℝ) : ℝ :=
  FiniteBoxLocalization.defectConstant (J^2-1) (cubeEpsilon J u)
    (upperConstant J β₀ u cFar) (lowerConstant J β₀ u cFar)

/-- Literal source defective occupation entropy, with the unresolved far
imbalance assumption exposed. All other criterion inputs concern actual
original rates, weights, coordinates and support and are proved below. -/
theorem source_occupation_entropy_of_far {J N : ℕ} {β β₀ t u cFar : ℝ}
    (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤occupationBound β₀)
    (hu : 0<u) (hu1 : u<1) (hut : u<3*t/4)
    (hmesh : 8*(ConditionalLawEstimates.radius β₀+4)≤J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀≤J)
    (hresolution : HeavyScales.sourceResolution β₀ (u/2)≤J)
    (hsmall : 1/(J^2:ℕ)<t/8) (hinner : 1/(J^2:ℕ)<u)
    (hcFar : 0<cFar) (hlarge : particleThreshold J β₀ t u cFar≤N)
    (hfar : OccupationCoercivity.FarImbalance (N:=N) (t:=t) (mesh_pos hmesh) β β₀ cFar)
    (F : OccupationState J N t → ℝ)
    (hF : ∀ m, m.val∉cappedOccupations J N u → F m=0) :
    FibreEntropy.finiteEntropy (occupationWeight (mesh_pos hmesh) β) (fun m => F m^2) ≤
      entropyConstant J β₀ u cFar*occupationEnergy (mesh_pos hmesh) β F +
        defectConstant J β₀ u cFar*∑ m, occupationWeight (mesh_pos hmesh) β m*F m^2 := by
  classical
  let hJ := mesh_pos hmesh
  have hmassN : OccupationMassInstantiation.particleThreshold J β₀ t u cFar≤N :=
    (le_max_left _ _).trans hlarge
  have hlocalN : FiniteBoxLocalization.particleThreshold (cubeEpsilon J u)≤N :=
    (le_max_right _ _).trans hlarge
  have hb := OccupationMassInstantiation.particleThreshold_bounds hmassN
  have hnearN : OccupationNearImbalance.particleThreshold J β₀ t≤N := (le_max_left _ _).trans hb.1
  have hn := OccupationNearImbalance.particleThreshold_bounds (hβ.trans hβ₀) hsub ht hnearN
  have hN : 2≤N := hn.2.2.2.1
  have hcounts : 8*J^2≤N := hn.2.2.1
  have hε := cubeEpsilon_pos hJ hinner
  have hci := OccupationMassInstantiation.innerEpsilon_pos hJ hinner
  have hcb := upperConstant_bounds (u:=u) (cFar:=cFar) hJ (hβ.trans hβ₀) hsub
  have hC : 0<upperConstant J β₀ u cFar := by linarith only [hcb.1]
  have hc := lowerConstant_pos (u:=u) hJ hsub hcFar
  have hcrate : lowerConstant J β₀ u cFar≤lowerBound β₀/(4*(J^2:ℕ)) := min_le_left _ _
  have hcmass : lowerConstant J β₀ u cFar≤OccupationMassInstantiation.centerCoefficient J β₀ u cFar :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hcdrift : lowerConstant J β₀ u cFar≤OccupationMassInstantiation.driftCoefficient J β₀ cFar :=
    (min_le_right _ _).trans (min_le_right _ _)
  let e := OccupationCentralPoincare.coordinateEquiv J N t
  let m₀ := OccupationMassInstantiation.centerState hJ hsmall hmassN
  let x₀ : ↥(coordinateDomain J N t) := e m₀
  let K : Finset ↥(coordinateDomain J N t) :=
    Finset.univ.filter (fun x => (e.symm x).val∈cappedOccupations J N u)
  let w := coordinateWeight (N:=N) (t:=t) hJ β
  let r := coordinateRate (N:=N) (t:=t) hJ β
  let G := fun x : ↥(coordinateDomain J N t) => F (e.symm x)
  let V := fun x : ↥(coordinateDomain J N t) => occupationV hJ β (e.symm x)
  have hx₀ : x₀.val=interior (cumulative (rounded J N)) := rfl
  have hw (x : ↥(coordinateDomain J N t)) : w x.val=occupationWeight hJ β (e.symm x) :=
    coordinateWeight_inverse hJ β x
  have hwstate (m : OccupationState J N t) : w (e m).val=occupationWeight hJ β m :=
    coordinateWeight_state hJ β m
  have heps : 2*cubeEpsilon J u*(N:ℝ)=OccupationMassInstantiation.innerEpsilon J u*N := by
    unfold cubeEpsilon
    ring
  have hT : 2*cubeEpsilon J u*(N:ℝ)≤centralEpsilon J*N := by
    rw [heps]
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg N)
  have habs := OccupationMassInstantiation.source_absolute_masses hβ hβ₀ hsub ht htC hu hu1 hut
    hmesh hnearJ hresolution hsmall hinner hcFar hmassN hfar
  dsimp only at habs
  have hxK : x₀∈K := by
    simp only [K,Finset.mem_filter,Finset.mem_univ,true_and,x₀,Equiv.symm_apply_apply]
    exact habs.2.1
  have hwp : ∀ z∈coordinateDomain J N t, 0<w z := by
    intro z hz
    rw [hw ⟨z,hz⟩]
    exact occupationWeight_pos hJ hN hβ (hβ₀.trans_lt hsub) _
  have hmass : (∑ x : ↥(coordinateDomain J N t), w x.val)≤1 := by
    rw [← FiniteGraphTransport.sum_eq e (occupationWeight hJ β) (fun x => w x.val) hwstate]
    exact occupation_mass_le_one hJ hN hβ (hβ₀.trans_lt hsub)
  have hbal : ∀ x z : ↥(coordinateDomain J N t), w x.val*r x z=w z.val*r z x := by
    intro x z
    rw [hw x,hw z]
    exact occupation_detailed_balance hJ (mesh_two_le hmesh) β _ _
  have hbound (x : ↥(coordinateDomain J N t)) (k) :
      |((x.val k-x₀.val k:ℤ):ℝ)|≤upperConstant J β₀ u cFar*N := by
    have hh := coordinate_distance_le (e.symm x) m₀ k
    rw [coordinates_inverse] at hh
    exact hh.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (show (1:ℝ)≤upperConstant J β₀ u cFar by linarith only [hcb.1]) (Nat.cast_nonneg N))
  have hjump (x z : ↥(coordinateDomain J N t)) (hr : r x z≠0) (k) : |x.val k-z.val k|≤1 := by
    have hh := coordinate_jump hJ β (e.symm x) (e.symm z) hr k
    dsimp only [e] at hh
    simpa only [coordinates_inverse] using hh
  have hout (x : ↥(coordinateDomain J N t)) : (∑ z,r x z)≤upperConstant J β₀ u cFar*N := by
    have hh := occupation_outgoing_le hJ (mesh_three_le hmesh) β (e.symm x)
    have he := FiniteGraphTransport.outgoing_sum_eq e (occupationRate hJ β) r
      (coordinateRate_state hJ β) (e.symm x)
    rw [Equiv.apply_symm_apply] at he
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hcb.1 (Nat.cast_nonneg N))
  have hΩ : ∀ z, (∀ k, |((z k-x₀.val k:ℤ):ℝ)|≤2*cubeEpsilon J u*N) → z∈coordinateDomain J N t := by
    intro z hz
    apply coordinateDomain_contains hJ hcounts hsmall z
    exact fun k => (hz k).trans hT
  have hK : ∀ x : ↥(coordinateDomain J N t),
      (∀ k, |((x.val k-x₀.val k:ℤ):ℝ)|≤2*cubeEpsilon J u*N) → x∈K := by
    intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    apply OccupationMassInstantiation.reduced_cube_capped hJ hinner hmassN (e.symm x)
    intro k
    rw [coordinates_inverse]
    have hh := hx k
    rw [hx₀,heps] at hh
    exact hh.trans (by nlinarith only [mul_nonneg hci.le (Nat.cast_nonneg N)])
  have hcoord : ∀ x z : ↥(coordinateDomain J N t),
      (∀ k, |((x.val k-x₀.val k:ℤ):ℝ)|≤2*cubeEpsilon J u*N) →
      (∀ k, |((z.val k-x₀.val k:ℤ):ℝ)|≤2*cubeEpsilon J u*N) →
      ∀ k, z.val=Function.update x.val k (x.val k+1) → lowerConstant J β₀ u cFar*N≤r x z := by
    intro x z hx _ k he
    exact (mul_le_mul_of_nonneg_right hcrate (Nat.cast_nonneg N)).trans
      (coordinate_rate_lower hN hβ hβ₀ hsub ht htC hmesh hcounts hsmall x z
        (fun i => (hx i).trans hT) k he)
  have hinc : IntegerBoxMassGeometry.LogIncrementBound x₀.val (2*cubeEpsilon J u*N) N
      (upperConstant J β₀ u cFar) w := by
    have hh := OccupationMassInstantiation.actual_inner_log_increment hβ hβ₀ hsub ht htC hmesh
      hnearJ hmassN hsmall
    rw [heps,hx₀]
    intro x hx i hi
    exact (hh x hx i hi).trans (mul_le_mul_of_nonneg_right hcb.2.1 (by positivity))
  have hcenter : lowerConstant J β₀ u cFar*(N:ℝ)^(-((J^2-1:ℕ):ℝ)/2)≤w x₀.val := by
    rw [hwstate m₀]
    exact (mul_le_mul_of_nonneg_right hcmass (Real.rpow_nonneg (Nat.cast_nonneg N) _)).trans habs.2.2.2.1
  have hglobal : ∀ x∈K, lowerConstant J β₀ u cFar*(N:ℝ)^(-((J^2-1:ℕ):ℝ)/2)*
      Real.exp (-upperConstant J β₀ u cFar*N)≤w x.val := by
    intro x hx
    have hh := habs.2.2.2.2 (e.symm x) (Finset.mem_filter.mp hx).2
    rw [hw x]
    apply le_trans _ hh
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hcmass (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hcb.2.2.1) (Nat.cast_nonneg N))
    · exact (Real.exp_pos _).le
    · exact mul_nonneg (OccupationMassInstantiation.centerCoefficient_pos J β₀ u cFar).le
        (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hdrift : ∀ x∈K, lowerConstant J β₀ u cFar*
      min ((DyadicShellPartition.radius N x₀.val x.val)^2) (N:ℝ)-upperConstant J β₀ u cFar≤
        groundStatePotential r V x := by
    intro x hx
    have hcap := (Finset.mem_filter.mp hx).2
    have hcap' : (e.symm x).val∈cappedOccupations J N (3*t/4) :=
      ⟨hcap.1,fun a => (hcap.2 a).trans (mul_le_mul_of_nonneg_right hut.le (Nat.cast_nonneg N))⟩
    have hh := OccupationCoercivity.capped_ground_state_of_far hβ hβ₀ hsub ht htC hmesh
      hnearJ hnearN hcFar hfar (e.symm x) hcap'
    rw [coordinates_inverse,← hx₀] at hh
    have hp := mul_le_mul_of_nonneg_right hcdrift
      (le_min (sq_nonneg (DyadicShellPartition.radius N x₀.val x.val)) (Nat.cast_nonneg N))
    rw [coordinate_potential]
    change OccupationMassInstantiation.driftCoefficient J β₀ cFar*_
      -OccupationCoercivity.nearLoss J β₀≤_ at hh
    linarith only [hh,hp,hcb.2.2.2]
  have hG : ∀ x, x∉K → G x=0 := by
    intro x hx
    apply hF
    intro hm
    exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩)
  have hD : 1≤J^2-1 := by
    have hj := mesh_two_le hmesh
    have hs : 2≤J^2 := by nlinarith
    omega
  have hh := FiniteBoxLocalization.local_box_criterion hD hε hC hc hlocalN
    (coordinateDomain J N t) x₀ K w G V r hxK hwp hmass
    (fun x z => occupationRate_nonneg hJ β (e.symm x) (e.symm z)) hbal hbound hjump hout hΩ hK
    hcoord hinc hcenter hglobal
    (fun x => occupationV_pos hJ hN hβ (hβ₀.trans_lt hsub) (e.symm x)) hdrift hG
  have htransport := FiniteGraphTransport.entropy_energy_transport e (occupationWeight hJ β)
    (fun x => w x.val) (occupationRate hJ β) r F G hwstate (coordinateRate_state hJ β)
    (fun m => by simp only [G,Equiv.symm_apply_apply])
    (FiniteBoxLocalization.entropyConstant (J^2-1) (cubeEpsilon J u)
      (upperConstant J β₀ u cFar) (lowerConstant J β₀ u cFar))
    (FiniteBoxLocalization.defectConstant (J^2-1) (cubeEpsilon J u)
      (upperConstant J β₀ u cFar) (lowerConstant J β₀ u cFar)) hh
  simpa only [entropyConstant,defectConstant,occupationEnergy,FiniteBoxPoincare.mean] using! htransport

/-- Both source coefficients are fixed nonnegative real numbers. -/
theorem constants_nonneg {J : ℕ} (hJ : 0<J) {β₀ u cFar : ℝ}
    (hβ₀ : 0≤β₀) (hsub : β₀<4) (hcFar : 0<cFar) :
    0≤entropyConstant J β₀ u cFar ∧ 0≤defectConstant J β₀ u cFar := by
  have hC := (upperConstant_bounds (u:=u) (cFar:=cFar) hJ hβ₀ hsub).1
  exact FiniteBoxLocalization.constants_nonneg (J^2-1) (cubeEpsilon J u)
    (show 0≤upperConstant J β₀ u cFar by linarith only [hC])
    (lowerConstant_pos hJ hsub hcFar)

end PeriodicAttractiveLogGas.OccupationCriterion
