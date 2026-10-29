import LeanResearch.PeriodicAttractiveLogGas.OccupationCoercivity

/-! Absolute occupation masses from the actual near and central estimates,
with only the literal far-imbalance input left unresolved. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.OccupationMassInstantiation
open MeshCells LabelOccupations DiscreteOccupationIdentities LabelGroundState
open ConditionalLawEstimates OccupationCoordinates OccupationAbsoluteMass
open OccupationCentralLogGradient

/-- The actual coefficient of the capped quadratic ground-state bound. -/
def driftCoefficient (J : ℕ) (β₀ cFar : ℝ) : ℝ :=
  min (OccupationCoercivity.nearCoefficient J β₀) (cFar/2)

def massRadius (J : ℕ) (β₀ u cFar : ℝ) : ℝ :=
  Real.sqrt (4*((288*HeavyCoercivityConstants.coercivityConstant β₀ (u/2)/(u/2)^2+
    OccupationCoercivity.nearLoss J β₀)/driftCoefficient J β₀ cFar)+1)

/-- Reduction of the central cube to the source inner occupation cap. -/
def innerEpsilon (J : ℕ) (u : ℝ) : ℝ :=
  min (centralEpsilon J) ((u-1/(J^2:ℕ))/8)

def particleThreshold (J : ℕ) (β₀ t u cFar : ℝ) : ℕ :=
  max (OccupationCentralPoincare.particleThreshold J β₀ t)
    (max (HeavyCoercivityConstants.particleThreshold β₀ (u/2))
      (max ⌈(massRadius J β₀ u cFar)^2⌉₊
        (max ⌈(massRadius J β₀ u cFar/innerEpsilon J u)^2⌉₊
          (max ⌈1+288*HeavyCoercivityConstants.coercivityConstant β₀ (u/2)/(u/2)^2⌉₊
            ⌈2/(u-1/(J^2:ℕ))⌉₊))))

theorem driftCoefficient_pos {J : ℕ} (hJ : 0<J) {β₀ cFar : ℝ}
    (hsub : β₀<4) (hcFar : 0<cFar) : 0<driftCoefficient J β₀ cFar :=
  lt_min (OccupationCoercivity.nearCoefficient_pos hJ hsub) (by positivity)

theorem innerEpsilon_pos {J : ℕ} (hJ : 0<J) {u : ℝ}
    (hu : 1/(J^2:ℕ)<u) : 0 < innerEpsilon J u :=
  lt_min (centralEpsilon_pos hJ) (div_pos (sub_pos.mpr hu) (by norm_num))

theorem massRadius_spec {J : ℕ} (hJ : 0<J) {β₀ u cFar : ℝ}
    (hβ₀ : 0≤β₀) (hsub : β₀<4) (hu : 0<u) (hcFar : 0<cFar) :
    0<massRadius J β₀ u cFar ∧
      4*((288*HeavyCoercivityConstants.coercivityConstant β₀ (u/2)/(u/2)^2+
        OccupationCoercivity.nearLoss J β₀)/driftCoefficient J β₀ cFar) ≤
          (massRadius J β₀ u cFar)^2 := by
  have ha := driftCoefficient_pos hJ hsub hcFar
  have hb := OccupationCoercivity.nearLoss_nonneg hJ hβ₀ hsub
  have hK := (HeavyCoercivityConstants.coercivityConstant_pos hsub (show 0<u/2 by linarith)).le
  have hnon : 0≤4*((288*HeavyCoercivityConstants.coercivityConstant β₀ (u/2)/(u/2)^2+
      OccupationCoercivity.nearLoss J β₀)/driftCoefficient J β₀ cFar) := by positivity
  unfold massRadius
  constructor
  · exact Real.sqrt_pos.mpr (by linarith)
  · rw [Real.sq_sqrt (by linarith)]
    linarith

theorem particleThreshold_bounds {J N : ℕ} {β₀ t u cFar : ℝ}
    (hlarge : particleThreshold J β₀ t u cFar≤N) :
    OccupationCentralPoincare.particleThreshold J β₀ t≤N ∧
    HeavyCoercivityConstants.particleThreshold β₀ (u/2)≤N ∧
    (massRadius J β₀ u cFar)^2≤(N:ℝ) ∧
    (massRadius J β₀ u cFar/innerEpsilon J u)^2≤(N:ℝ) ∧
    1+288*HeavyCoercivityConstants.coercivityConstant β₀ (u/2)/(u/2)^2≤(N:ℝ) ∧
    2/(u-1/(J^2:ℕ))≤(N:ℝ) := by
  rcases max_le_iff.mp hlarge with ⟨h1,hrest⟩
  rcases max_le_iff.mp hrest with ⟨h2,hrest⟩
  rcases max_le_iff.mp hrest with ⟨h3,hrest⟩
  rcases max_le_iff.mp hrest with ⟨h4,hrest⟩
  rcases max_le_iff.mp hrest with ⟨h5,h6⟩
  exact ⟨h1,h2,(Nat.le_ceil _).trans (Nat.cast_le.mpr h3),
    (Nat.le_ceil _).trans (Nat.cast_le.mpr h4),
    (Nat.le_ceil _).trans (Nat.cast_le.mpr h5),
    (Nat.le_ceil _).trans (Nat.cast_le.mpr h6)⟩

theorem radius_fits {J N : ℕ} {β₀ t u cFar : ℝ} (hJ : 0<J)
    (hu : 1/(J^2:ℕ)<u) (hlarge : particleThreshold J β₀ t u cFar≤N) :
    massRadius J β₀ u cFar*Real.sqrt N ≤ innerEpsilon J u*N := by
  have hε := innerEpsilon_pos hJ hu
  have hh := (particleThreshold_bounds hlarge).2.2.2.1
  have hM : 0≤massRadius J β₀ u cFar := Real.sqrt_nonneg _
  have hd : 0≤massRadius J β₀ u cFar/innerEpsilon J u := div_nonneg hM hε.le
  have hs := Real.sq_sqrt (Nat.cast_nonneg N)
  have hr := Real.sqrt_nonneg (N:ℝ)
  have hh' : massRadius J β₀ u cFar/innerEpsilon J u≤Real.sqrt N := by
    nlinarith only [hh,hd,hs,hr]
  have hp := mul_le_mul_of_nonneg_right ((div_le_iff₀ hε).mp hh') hr
  calc
    _ ≤ Real.sqrt N*innerEpsilon J u*Real.sqrt N := hp
    _ = innerEpsilon J u*(Real.sqrt N)^2 := by ring
    _ = _ := by rw [hs]

theorem cutoff_error_le_quarter {J N : ℕ} {β₀ t u cFar : ℝ}
    (hsub : β₀<4) (hu : 0<u) (hlarge : particleThreshold J β₀ t u cFar≤N) :
    72*HeavyCoercivityConstants.coercivityConstant β₀ (u/2)/
      ((N:ℝ)^2*(u-u/2)^2)≤1/4 := by
  have hK := (HeavyCoercivityConstants.coercivityConstant_pos hsub (show 0<u/2 by linarith)).le
  have hh := (particleThreshold_bounds hlarge).2.2.2.2.1
  have hq : 0≤288*HeavyCoercivityConstants.coercivityConstant β₀ (u/2)/(u/2)^2 := by positivity
  have hN : (0:ℝ)<N := by linarith
  have hqN : 288*HeavyCoercivityConstants.coercivityConstant β₀ (u/2)/(u/2)^2≤(N:ℝ)^2 := by
    nlinarith only [hh,hq]
  have hp := (div_le_iff₀ (sq_pos_of_pos (show 0<u/2 by linarith))).mp hqN
  have hg : 0<u-u/2 := by linarith
  apply (div_le_iff₀ (by positivity : 0<(N:ℝ)^2*(u-u/2)^2)).mpr
  have he : u-u/2=u/2 := by ring
  rw [he]
  nlinarith only [hp]

/-- The entire doubled reduced cube lies in the actual inner cap. -/
theorem reduced_cube_capped {J N : ℕ} {β₀ t u cFar : ℝ}
    (hJ : 0<J) (hu : 1/(J^2:ℕ)<u)
    (hlarge : particleThreshold J β₀ t u cFar≤N)
    (m : OccupationState J N t)
    (hclose : ∀ i, |((stateCoordinates m i-interior (cumulative (rounded J N)) i:ℤ):ℝ)| ≤
      2*innerEpsilon J u*N) : m.val∈cappedOccupations J N u := by
  have hε := (innerEpsilon_pos hJ hu).le
  have hbound := (particleThreshold_bounds hlarge).2.2.2.2.2
  have hgap := sub_pos.mpr hu
  have hmargin : 2≤(N:ℝ)*(u-1/(J^2:ℕ)) := (div_le_iff₀ hgap).mp hbound
  have heps : innerEpsilon J u≤(u-1/(J^2:ℕ))/8 := min_le_right _ _
  have hprod := mul_le_mul_of_nonneg_right heps (Nat.cast_nonneg N)
  have hnorm : ‖fun i => ((interior (cumulative m.val) i-interior (cumulative (rounded J N)) i:ℤ):ℝ)‖ ≤
      2*innerEpsilon J u*N := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    simpa only [stateCoordinates, Real.norm_eq_abs] using! hclose i
  have hcount := (count_norm_le_interior m.val (rounded J N) m.property.1 (rounded_sum hJ N)).trans
    (mul_le_mul_of_nonneg_left hnorm (by norm_num : (0:ℝ)≤2))
  refine ⟨m.property.1,fun a => ?_⟩
  have hi : |(m.val a:ℝ)-rounded J N a|≤4*innerEpsilon J u*N := by
    have hh := (norm_le_pi_norm (fun a => (m.val a:ℝ)-rounded J N a) a).trans hcount
    calc
      _ ≤ 2*(2*innerEpsilon J u*N) := by simpa only [Real.norm_eq_abs] using hh
      _ = _ := by ring
  have hr := (abs_le.mp (rounded_close hJ N a)).2
  have he : (N:ℝ)/(J^2:ℕ)=N*(1/(J^2:ℕ)) := by ring
  rw [he] at hr
  have hh := (abs_le.mp hi).2
  nlinarith only [hh,hr,hmargin,hprod]

/-- The actual rounded center belongs to the inner cap, not just the outer graph. -/
theorem roundedState_capped {J N : ℕ} {β₀ t u cFar : ℝ}
    (hJ : 0<J) (hcounts : 8*J^2≤N) (hsmall : 1/(J^2:ℕ)<t/8)
    (hu : 1/(J^2:ℕ)<u) (hlarge : particleThreshold J β₀ t u cFar≤N) :
    (roundedState hJ hcounts hsmall).val∈cappedOccupations J N u := by
  apply reduced_cube_capped hJ hu hlarge
  intro i
  change |((interior (cumulative (rounded J N)) i-interior (cumulative (rounded J N)) i:ℤ):ℝ)|≤_
  simp only [sub_self,Int.cast_zero,abs_zero]
  have := (innerEpsilon_pos hJ hu).le
  positivity

/-- Restriction of the genuine occupation increment theorem to the reduced cube. -/
theorem actual_inner_log_increment {J N : ℕ} {t β β₀ u cFar : ℝ}
    (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤occupationBound β₀)
    (hmesh : 8*(ConditionalLawEstimates.radius β₀+4)≤J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀≤J)
    (hlarge : particleThreshold J β₀ t u cFar≤N) (hsmall : 1/(J^2:ℕ)<t/8) :
    IntegerBoxMassGeometry.LogIncrementBound (interior (cumulative (rounded J N)))
      (innerEpsilon J u*N) N (OccupationCentralPoincare.incrementConstant J β₀)
      (coordinateWeight (N:=N) (t:=t) (mesh_pos hmesh) β) := by
  have hh := OccupationCentralPoincare.actual_log_increment hβ hβ₀ hsub ht htC hmesh hnearJ
    (particleThreshold_bounds hlarge).1 hsmall
  have hT : innerEpsilon J u*N≤centralEpsilon J*N :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg N)
  exact fun x hx i hi => hh x (fun j => (hx j).trans hT) i (fun j => (hi j).trans hT)

/-- Concrete rounded state, using only the explicit particle threshold. -/
def centerState {J N : ℕ} {β₀ t u cFar : ℝ} (hJ : 0<J)
    (hsmall : 1/(J^2:ℕ)<t/8) (hlarge : particleThreshold J β₀ t u cFar≤N) :
    OccupationState J N t :=
  roundedState hJ (by
    have hc : 64*J^2≤N := (le_max_right _ _).trans (particleThreshold_bounds hlarge).1
    omega) hsmall

def centerCoefficient (J : ℕ) (β₀ u cFar : ℝ) : ℝ :=
  (2*(2*massRadius J β₀ u cFar+1)^(J^2-1)*
    Real.exp (4*(J^2-1:ℕ)*OccupationCentralPoincare.incrementConstant J β₀*
      (1+(massRadius J β₀ u cFar)^2)))⁻¹

theorem centerCoefficient_pos (J : ℕ) (β₀ u cFar : ℝ) :
    0<centerCoefficient J β₀ u cFar := by
  have hM : 0≤massRadius J β₀ u cFar := Real.sqrt_nonneg _
  unfold centerCoefficient
  positivity

/-- All drift, increment, normalization and central-mass inputs are discharged.
Only the literal far-subset imbalance remains as an analytic hypothesis. -/
theorem source_center_mass {J N : ℕ} {β β₀ t u cFar : ℝ}
    (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤occupationBound β₀)
    (hu : 0<u) (hu1 : u<1) (hut : u<3*t/4)
    (hmesh : 8*(ConditionalLawEstimates.radius β₀+4)≤J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀≤J)
    (hresolution : HeavyScales.sourceResolution β₀ (u/2)≤J)
    (hsmall : 1/(J^2:ℕ)<t/8) (hinner : 1/(J^2:ℕ)<u)
    (hcFar : 0<cFar) (hlarge : particleThreshold J β₀ t u cFar≤N)
    (hfar : OccupationCoercivity.FarImbalance (N:=N) (t:=t) (mesh_pos hmesh) β β₀ cFar) :
    centerCoefficient J β₀ u cFar*(N:ℝ)^(-((J^2-1:ℕ):ℝ)/2) ≤
      occupationWeight (mesh_pos hmesh) β (centerState (mesh_pos hmesh) hsmall hlarge) := by
  classical
  let m₀ := centerState (mesh_pos hmesh) hsmall hlarge
  have hb := particleThreshold_bounds hlarge
  have hnearN : OccupationNearImbalance.particleThreshold J β₀ t≤N := (le_max_left _ _).trans hb.1
  have hrad := massRadius_spec (mesh_pos hmesh) (hβ.trans hβ₀) hsub hu hcFar
  have hhalf : u-u/2=u/2 := by ring
  have hdrift : ∀ m∈innerProfiles (J:=J) (N:=N) t u,
      driftCoefficient J β₀ cFar*truncatedRadius m₀ m-OccupationCoercivity.nearLoss J β₀ ≤
        occupationW (SeparatedRadius.source_mesh_pos hresolution) β m := by
    intro m hm
    have hcap := (Finset.mem_filter.mp hm).2
    have hcap' : m.val∈cappedOccupations J N (3*t/4) :=
      ⟨hcap.1,fun a => (hcap.2 a).trans (mul_le_mul_of_nonneg_right hut.le (Nat.cast_nonneg N))⟩
    have hh := OccupationCoercivity.capped_ground_state_of_far hβ hβ₀ hsub ht htC hmesh
      hnearJ hnearN hcFar hfar m hcap'
    simpa only [driftCoefficient,truncatedRadius,m₀,centerState,roundedState,stateCoordinates] using! hh
  have hinc := actual_inner_log_increment hβ hβ₀ hsub ht htC hmesh hnearJ hlarge hsmall
  have hh := occupation_center_lower (hβ.trans hβ₀) hsub (show 0<u/2 by linarith)
    (show u/2<u by linarith) hu1 (show u≤t by linarith) hresolution hb.2.1 hβ hβ₀ m₀
    (driftCoefficient_pos (mesh_pos hmesh) hsub hcFar)
    (OccupationCoercivity.nearLoss_nonneg (mesh_pos hmesh) (hβ.trans hβ₀) hsub)
    hrad.1 hb.2.2.1 (OccupationCentralPoincare.incrementConstant_nonneg J (hβ.trans hβ₀))
    (radius_fits (mesh_pos hmesh) hinner hlarge) (cutoff_error_le_quarter hsub hu hlarge)
    (by simpa only [hhalf] using hrad.2) hdrift
    (by simpa only [m₀,centerState,roundedState,stateCoordinates] using! hinc)
  simpa only [centerCoefficient,m₀] using! hh

/-- A fixed nonnegative global exponent, using the proved actual Green lower bound. -/
def globalExponent (J : ℕ) (β₀ : ℝ) : ℝ :=
  max 0 (-Real.log (CellNormalizerBounds.kappaConstant β₀ MovingPoleCalculus.greenLowerConstant
    kernelConstant J (ConditionalLawEstimates.radius β₀)/(J:ℝ)^2))

theorem globalExponent_nonneg (J : ℕ) (β₀ : ℝ) : 0≤globalExponent J β₀ := le_max_left _ _

/-- The comparison path is taken on the smaller cap itself. Both resulting
weights are literally the original unnormalized occupation-event masses. -/
theorem inner_global_comparison {J N : ℕ} {β β₀ t u : ℝ}
    (hN : 2≤N) (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (hu : 0<u) (huC : u≤occupationBound β₀)
    (hmesh : 8*(ConditionalLawEstimates.radius β₀+4)≤J)
    (m n : OccupationState J N t)
    (hm : m.val∈cappedOccupations J N u) (hn : n.val∈cappedOccupations J N u) :
    occupationWeight (mesh_pos hmesh) β m*Real.exp (-globalExponent J β₀*N) ≤
      occupationWeight (mesh_pos hmesh) β n := by
  let m' : OccupationState J N u := ⟨m.val,hm⟩
  let n' : OccupationState J N u := ⟨n.val,hn⟩
  have hh := occupation_global_exponential hN hβ hβ₀ hsub hu huC
    MovingPoleCalculus.greenLowerConstant_pos.le MovingPoleCalculus.green_lower_bound hmesh m' n'
  dsimp only at hh
  let raw := -Real.log (CellNormalizerBounds.kappaConstant β₀ MovingPoleCalculus.greenLowerConstant
    kernelConstant J (ConditionalLawEstimates.radius β₀)/(J:ℝ)^2)
  change occupationWeight (mesh_pos hmesh) β m*Real.exp (-raw*N)≤
    occupationWeight (mesh_pos hmesh) β n at hh
  have he : -globalExponent J β₀*(N:ℝ)≤-raw*N :=
    mul_le_mul_of_nonneg_right (neg_le_neg (le_max_right _ _)) (Nat.cast_nonneg N)
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
    (show 0≤occupationWeight (mesh_pos hmesh) β m from ENNReal.toReal_nonneg)).trans hh

/-- Source absolute point masses: explicit positive polynomial coefficient and
fixed exponential coefficient, with only genuine far imbalance unresolved. -/
theorem source_absolute_masses {J N : ℕ} {β β₀ t u cFar : ℝ}
    (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤occupationBound β₀)
    (hu : 0<u) (hu1 : u<1) (hut : u<3*t/4)
    (hmesh : 8*(ConditionalLawEstimates.radius β₀+4)≤J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀≤J)
    (hresolution : HeavyScales.sourceResolution β₀ (u/2)≤J)
    (hsmall : 1/(J^2:ℕ)<t/8) (hinner : 1/(J^2:ℕ)<u)
    (hcFar : 0<cFar) (hlarge : particleThreshold J β₀ t u cFar≤N)
    (hfar : OccupationCoercivity.FarImbalance (N:=N) (t:=t) (mesh_pos hmesh) β β₀ cFar) :
    let m₀ := centerState (mesh_pos hmesh) hsmall hlarge
    m₀.val=rounded J N ∧ m₀.val∈cappedOccupations J N u ∧
    0<centerCoefficient J β₀ u cFar ∧
    centerCoefficient J β₀ u cFar*(N:ℝ)^(-((J^2-1:ℕ):ℝ)/2) ≤
      occupationWeight (mesh_pos hmesh) β m₀ ∧
    ∀ m : OccupationState J N t, m.val∈cappedOccupations J N u →
      centerCoefficient J β₀ u cFar*(N:ℝ)^(-((J^2-1:ℕ):ℝ)/2)*
        Real.exp (-globalExponent J β₀*N) ≤ occupationWeight (mesh_pos hmesh) β m := by
  let m₀ := centerState (mesh_pos hmesh) hsmall hlarge
  have hb := particleThreshold_bounds hlarge
  have hc : 64*J^2≤N := (le_max_right _ _).trans hb.1
  have hnearN : OccupationNearImbalance.particleThreshold J β₀ t≤N := (le_max_left _ _).trans hb.1
  have hN := (OccupationNearImbalance.particleThreshold_bounds (hβ.trans hβ₀) hsub ht hnearN).2.2.2.1
  have hm₀ : m₀.val∈cappedOccupations J N u :=
    roundedState_capped (mesh_pos hmesh) (by omega) hsmall hinner hlarge
  have hcenter := source_center_mass hβ hβ₀ hsub ht htC hu hu1 hut hmesh hnearJ hresolution
    hsmall hinner hcFar hlarge hfar
  refine ⟨rfl,hm₀,centerCoefficient_pos J β₀ u cFar,hcenter,?_⟩
  intro m hm
  have hg := inner_global_comparison hN hβ hβ₀ hsub hu
    ((show u≤t by linarith).trans htC) hmesh m₀ m hm₀ hm
  exact (mul_le_mul_of_nonneg_right hcenter (Real.exp_pos _).le).trans hg

/-- Literal whole integer cube, including validity of every reconstructed count.
No pre-existing occupation or surrogate domain is assumed for y. -/
theorem reduced_integer_cube_valid {J N : ℕ} {β₀ t u cFar : ℝ}
    (hJ : 0<J) (hsmall : 1/(J^2:ℕ)<t/8) (hu : 1/(J^2:ℕ)<u)
    (hlarge : particleThreshold J β₀ t u cFar≤N) (y : Interior J)
    (hy : ∀ i, |((y i-interior (cumulative (rounded J N)) i:ℤ):ℝ)|≤2*innerEpsilon J u*N) :
    ValidCoordinates J N u (extend J N y) := by
  have hε := (innerEpsilon_pos hJ hu).le
  have hc : 64*J^2≤N := (le_max_right _ _).trans (particleThreshold_bounds hlarge).1
  have heps : innerEpsilon J u≤centralEpsilon J := min_le_left _ _
  have hprod := mul_le_mul_of_nonneg_right heps (Nat.cast_nonneg N)
  apply box_valid_of_margins hJ (rounded J N) (rounded_sum hJ N) y (by positivity) hy
  · intro a
    have hm := (rounded_central_margins hJ (show 8*J^2≤N by omega) hsmall a).1
    have hz : 0≤(N:ℝ)/(2*(J^2:ℕ)) := by positivity
    nlinarith only [hm,hz,hprod]
  · intro a
    have hr := (abs_le.mp (rounded_close hJ N a)).2
    have hmargin := (div_le_iff₀ (sub_pos.mpr hu)).mp
      (particleThreshold_bounds hlarge).2.2.2.2.2
    have heps' : innerEpsilon J u≤(u-1/(J^2:ℕ))/8 := min_le_right _ _
    have hp := mul_le_mul_of_nonneg_right heps' (Nat.cast_nonneg N)
    have he : (N:ℝ)/(J^2:ℕ)=N*(1/(J^2:ℕ)) := by ring
    rw [he] at hr
    nlinarith only [hr,hmargin,hp]

end PeriodicAttractiveLogGas.OccupationMassInstantiation
