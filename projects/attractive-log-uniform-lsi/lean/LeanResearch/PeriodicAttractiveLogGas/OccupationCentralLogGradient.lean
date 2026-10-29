import LeanResearch.PeriodicAttractiveLogGas.OccupationAbsoluteMass

/-! Source2060–2095: actual central mixed differences, center rate comparison,
and propagation of first differences along integer coordinate paths. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.OccupationCentralLogGradient
open MeshCells MeshAdjacentCells LabelOccupations LabelRatioTransport
  DiscreteOccupationIdentities OccupationCoordinates ConditionalLawEstimates
  OccupationCentralRates OccupationSecondDifferences OccupationReverseRates

/-- A rectangle of actual permitted moves has the source O(1/N) mixed
log-weight bound, including coincident coordinate directions. -/
theorem occupation_mixed_difference {J N : ℕ} {t β β₀ : ℝ}
    (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤occupationBound β₀)
    (hmesh : 8*(radius β₀+4)≤J) (hlarge : secondDifferenceThreshold J β₀≤N)
    (hcounts : 8*J^2≤N) (hsmall : 1/(J^2:ℕ)<t/8)
    {m ma mc mac : OccupationState J N t} {a b c d : MeshIndex J}
    (hab : PermittedMove (mesh_pos hmesh) m ma a b)
    (hcd : PermittedMove (mesh_pos hmesh) m mc c d)
    (hab' : PermittedMove (mesh_pos hmesh) mc mac a b)
    (hcd' : PermittedMove (mesh_pos hmesh) ma mac c d)
    (hm : ∀ i, |((interior (cumulative m.val) i-interior (cumulative (rounded J N)) i:ℤ):ℝ)|≤
      2*centralEpsilon J*N)
    (hmc : ∀ i, |((interior (cumulative mc.val) i-interior (cumulative (rounded J N)) i:ℤ):ℝ)|≤
      2*centralEpsilon J*N) :
    |Real.log (occupationWeight (mesh_pos hmesh) β mac)-Real.log (occupationWeight (mesh_pos hmesh) β mc)-
      Real.log (occupationWeight (mesh_pos hmesh) β ma)+Real.log (occupationWeight (mesh_pos hmesh) β m)|≤
      (secondDifferenceConstant J β₀+4*(J^2:ℕ))/N := by
  have hN := (secondDifferenceThreshold_bounds hlarge).1
  have hfac := central_factorial_mixed_difference (mesh_pos hmesh) (mesh_two_le hmesh)
    hN hcounts hsmall hab hcd hab' hm hmc
  have hq := occupation_second_differences hβ hβ₀ hsub ht htC hmesh hlarge m.val a b c d
    hab.1 hcd.1 m.property (by rw [hab.2.2]; exact ma.property)
    (by rw [hcd.2.2]; exact mc.property)
    (by rw [hab.2.2,hcd'.2.2]; exact mac.property)
  rw [hab.2.2,hcd.2.2,hcd'.2.2] at hq
  change |Real.log (qWeight (mesh_pos hmesh) β mac)-Real.log (qWeight (mesh_pos hmesh) β ma)-
    Real.log (qWeight (mesh_pos hmesh) β mc)+Real.log (qWeight (mesh_pos hmesh) β m)|≤_ at hq
  have he (z : OccupationState J N t) : Real.log (occupationWeight (mesh_pos hmesh) β z)=
      Real.log (multiplicity z:ℝ)+Real.log (qWeight (mesh_pos hmesh) β z) := by
    rw [occupationWeight_eq,Real.log_mul]
    · exact_mod_cast (multiplicity_pos z).ne'
    · exact (qWeight_pos (mesh_pos hmesh) hN hβ (hβ₀.trans_lt hsub) z).ne'
  rw [he mac,he mc,he ma,he m]
  have hid :
      (Real.log (multiplicity mac:ℝ)+Real.log (qWeight (mesh_pos hmesh) β mac))-
      (Real.log (multiplicity mc:ℝ)+Real.log (qWeight (mesh_pos hmesh) β mc))-
      (Real.log (multiplicity ma:ℝ)+Real.log (qWeight (mesh_pos hmesh) β ma))+
      (Real.log (multiplicity m:ℝ)+Real.log (qWeight (mesh_pos hmesh) β m)) =
      (Real.log (multiplicity mac:ℝ)-Real.log (multiplicity mc:ℝ)-Real.log (multiplicity ma:ℝ)+Real.log (multiplicity m:ℝ))+
      (Real.log (qWeight (mesh_pos hmesh) β mac)-Real.log (qWeight (mesh_pos hmesh) β ma)-
      Real.log (qWeight (mesh_pos hmesh) β mc)+Real.log (qWeight (mesh_pos hmesh) β m)) := by ring
  rw [hid]
  calc
    _ ≤ _ := abs_add_le _ _
    _ ≤ 4*(J^2:ℕ)/N+secondDifferenceConstant J β₀/N := add_le_add hfac hq
    _ = _ := by ring

/-- Logarithms are Lipschitz above a positive lower scale. -/
theorem abs_log_sub_le {x y c : ℝ} (hc : 0<c) (hx : c≤x) (hy : c≤y) :
    |Real.log x-Real.log y|≤|x-y|/c := by
  have bound {u v : ℝ} (hu : c≤u) (hv : c≤v) : Real.log u-Real.log v≤|u-v|/c := by
    have hup := hc.trans_le hu
    have hvp := hc.trans_le hv
    have hh := Real.log_le_sub_one_of_pos (div_pos hup hvp)
    rw [Real.log_div hup.ne' hvp.ne'] at hh
    have he : u/v-1=(u-v)/v := by field_simp
    rw [he] at hh
    exact hh.trans ((div_le_div_of_nonneg_right (le_abs_self _) hvp.le).trans
      (div_le_div_of_nonneg_left (abs_nonneg _) hc hv))
  have h1 := bound hx hy
  have h2 := bound hy hx
  rw [abs_sub_comm y x] at h2
  exact abs_le.mpr ⟨by linarith only [h2],h1⟩

/-- Square-root rate imbalance and the bounded reverse-rate error give the
source N^(-1/2) center log ratio; no log-gradient bound is assumed. -/
theorem log_rate_ratio_from_imbalance {N r s v c B E : ℝ}
    (hN : 1≤N) (hc : 0<c) (hB : 0≤B) (hE : 0≤E)
    (hr : c*N≤r) (hv : c*N≤v) (hs : 0≤s) (hrN : r≤N) (hsN : s≤N)
    (himb : |Real.sqrt r-Real.sqrt s|≤B) (hrev : |v-s|≤E) :
    |Real.log r-Real.log v|≤((2*B+E)/c)/Real.sqrt N := by
  have hNp : 0<N := by linarith
  have hr0 := (mul_pos hc hNp).le.trans hr
  have hR := Real.sq_sqrt hr0
  have hS := Real.sq_sqrt hs
  have hn := Real.sq_sqrt hNp.le
  have hsqrt : 1≤Real.sqrt N := by
    have := Real.sqrt_le_sqrt hN
    simpa only [Real.sqrt_one] using this
  have hsum : Real.sqrt r+Real.sqrt s≤2*Real.sqrt N := by
    linarith [Real.sqrt_le_sqrt hrN,Real.sqrt_le_sqrt hsN]
  have hrs : |r-s|≤2*B*Real.sqrt N := by
    have he : r-s=(Real.sqrt r-Real.sqrt s)*(Real.sqrt r+Real.sqrt s) := by nlinarith only [hR,hS]
    rw [he,abs_mul,abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    calc
      _ ≤ B*(2*Real.sqrt N) := mul_le_mul himb hsum
        (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hB
      _ = _ := by ring
  have hrv : |r-v|≤2*B*Real.sqrt N+E := by
    have hh := abs_sub_le r s v
    rw [abs_sub_comm s v] at hh
    linarith only [hh,hrs,hrev]
  have hh := (abs_log_sub_le (mul_pos hc hNp) hr hv).trans
    (div_le_div_of_nonneg_right hrv (mul_nonneg hc.le hNp.le))
  have he : (2*B*Real.sqrt N+E)/(c*N)≤((2*B+E)/c)/Real.sqrt N := by
    have hE' := mul_le_mul_of_nonneg_left hsqrt hE
    have hcancel : Real.sqrt N/N=1/Real.sqrt N := by
      apply (div_eq_div_iff hNp.ne' (Real.sqrt_pos.mpr hNp).ne').mpr
      nlinarith only [hn]
    calc
      _ ≤ (2*B*Real.sqrt N+E*Real.sqrt N)/(c*N) := by
        apply div_le_div_of_nonneg_right _ (mul_nonneg hc.le hNp.le)
        linarith only [hE']
      _ = (2*B+E)*(Real.sqrt N/N)/c := by ring
      _ = _ := by rw [hcancel]; ring
  exact hh.trans he

/-- Detailed balance converts the rate ratio into the original weight increment. -/
theorem log_weight_increment_of_balance {w w' r r' : ℝ}
    (hw : 0<w) (hw' : 0<w') (hr : 0<r) (hr' : 0<r')
    (hb : w*r=w'*r') : Real.log w'-Real.log w=Real.log r-Real.log r' := by
  have hh := congrArg Real.log hb
  rw [Real.log_mul hw.ne' hr.ne',Real.log_mul hw'.ne' hr'.ne'] at hh
  linarith only [hh]


/-- A literal positive unit step in free integer coordinates. -/
def step {D : ℕ} (y : Fin D → ℤ) (i : Fin D) : Fin D → ℤ := Function.update y i (y i+1)

theorem step_apply {D : ℕ} (y : Fin D → ℤ) (i j : Fin D) :
    step y i j=y j+if j=i then 1 else 0 := by
  classical
  by_cases h : j=i <;> simp [step,h]

theorem step_comm {D : ℕ} (y : Fin D → ℤ) (i j : Fin D) : step (step y i) j=step (step y j) i := by
  funext k
  simp only [step_apply]
  ring

theorem step_distance {D : ℕ} (y z : Fin D → ℤ) {R : ℝ}
    (hy : ∀ k, |((y k-z k:ℤ):ℝ)|≤R) (i : Fin D) :
    ∀ k, |((step y i k-z k:ℤ):ℝ)|≤R+1 := by
  intro k
  rw [step_apply]
  by_cases hk : k=i
  · simp only [hk,ite_true,Int.cast_sub,Int.cast_add,Int.cast_one]
    have hh := abs_add_le ((y i:ℝ)-z i) 1
    have he : (y i:ℝ)+1-z i=((y i:ℝ)-z i)+1 := by ring
    rw [he]
    have hi := hy i
    simp only [Int.cast_sub,abs_one] at hi hh
    linarith only [hi,hh]
  · simp only [hk,ite_false,add_zero]
    exact (hy k).trans (by linarith)

/-- The actual enlarged central cube reconstructs an original capped state. -/
def centralState {J N : ℕ} {t : ℝ} (hJ : 0<J) (hN : 8*J^2≤N)
    (ht : 1/(J^2:ℕ)<t/8) (y : Interior J)
    (hy : ∀ i, |((y i-interior (cumulative (rounded J N)) i:ℤ):ℝ)|≤2*centralEpsilon J*N) :
    OccupationState J N t :=
  ⟨recover (extend J N y), (central_box_occupation hJ hN ht y hy).1.1, fun a => by
    have hh := (central_box_occupation hJ hN ht y hy).1.2 a
    have hz : (0:ℝ)≤recover (extend J N y) a := Nat.cast_nonneg _
    nlinarith only [hh,hz]⟩

theorem centralState_coordinates {J N : ℕ} {t : ℝ} (hJ : 0<J) (hN : 8*J^2≤N)
    (ht : 1/(J^2:ℕ)<t/8) (y : Interior J)
    (hy : ∀ i, |((y i-interior (cumulative (rounded J N)) i:ℤ):ℝ)|≤2*centralEpsilon J*N) :
    OccupationAbsoluteMass.stateCoordinates (centralState hJ hN ht y hy)=y :=
  (central_box_occupation hJ hN ht y hy).2.1

theorem centralState_half_cap {J N : ℕ} {t : ℝ} (hJ : 0<J) (hN : 8*J^2≤N)
    (ht : 1/(J^2:ℕ)<t/8) (y : Interior J)
    (hy : ∀ i, |((y i-interior (cumulative (rounded J N)) i:ℤ):ℝ)|≤2*centralEpsilon J*N) :
    (centralState hJ hN ht y hy).val∈cappedOccupations J N (t/2) :=
  (central_box_occupation hJ hN ht y hy).1

theorem centralState_weight {J N : ℕ} {t : ℝ} (hJ : 0<J) (hN : 8*J^2≤N)
    (ht : 1/(J^2:ℕ)<t/8) (y : Interior J)
    (hy : ∀ i, |((y i-interior (cumulative (rounded J N)) i:ℤ):ℝ)|≤2*centralEpsilon J*N) (β : ℝ) :
    OccupationAbsoluteMass.coordinateWeight (N:=N) (t:=t) hJ β y=
      occupationWeight hJ β (centralState hJ hN ht y hy) := by
  simpa only [centralState_coordinates] using
    OccupationAbsoluteMass.coordinateWeight_state hJ β (centralState hJ hN ht y hy)

/-- Positive coordinate steps are reverse moves along the actual snake path. -/
theorem forward_permitted {J N : ℕ} {t : ℝ} (hJ : 0<J) (hJ2 : 2≤J)
    (m n : OccupationState J N t) (i : Fin (J^2-1))
    (he : OccupationAbsoluteMass.stateCoordinates n=step (OccupationAbsoluteMass.stateCoordinates m) i) :
    PermittedMove hJ m n (snakeOrder J ⟨i.val+1,by have := i.isLt; omega⟩)
      (snakeOrder J ⟨i.val,by have := i.isLt; omega⟩) := by
  have hh : interior (cumulative m.val)=fun k => interior (cumulative n.val) k-if k=i then 1 else 0 := by
    change OccupationAbsoluteMass.stateCoordinates m=fun k => OccupationAbsoluteMass.stateCoordinates n k-if k=i then 1 else 0
    rw [he]
    funext k
    rw [step_apply]
    ring
  exact (interior_neighbor_is_permitted hJ n m i hh).reverse hJ2

/-- Every four-point coordinate rectangle in the smaller cube lies in the
actual enlarged cube. Thus cap and count hypotheses are discharged, even
when the two coordinate directions coincide. -/
theorem coordinate_mixed_difference {J N : ℕ} {t β β₀ : ℝ}
    (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤occupationBound β₀)
    (hmesh : 8*(radius β₀+4)≤J) (hlarge : secondDifferenceThreshold J β₀≤N)
    (hcounts : 8*J^2≤N) (hsmall : 1/(J^2:ℕ)<t/8)
    (hroom : 2≤centralEpsilon J*N) (y : Interior J)
    (hy : ∀ k, |((y k-interior (cumulative (rounded J N)) k:ℤ):ℝ)|≤centralEpsilon J*N)
    (i j : Fin (J^2-1)) :
    let w := OccupationAbsoluteMass.coordinateWeight (N:=N) (t:=t) (mesh_pos hmesh) β
    |Real.log (w (step (step y i) j))-Real.log (w (step y j))-
      Real.log (w (step y i))+Real.log (w y)|≤(secondDifferenceConstant J β₀+4*(J^2:ℕ))/N := by
  let y₀ := interior (cumulative (rounded J N))
  have hy0 : ∀ k, |((y k-y₀ k:ℤ):ℝ)|≤2*centralEpsilon J*N := fun k => (hy k).trans (by linarith)
  have hyi : ∀ k, |((step y i k-y₀ k:ℤ):ℝ)|≤2*centralEpsilon J*N :=
    fun k => (step_distance y y₀ hy i k).trans (by linarith)
  have hyj : ∀ k, |((step y j k-y₀ k:ℤ):ℝ)|≤2*centralEpsilon J*N :=
    fun k => (step_distance y y₀ hy j k).trans (by linarith)
  have hyij : ∀ k, |((step (step y i) j k-y₀ k:ℤ):ℝ)|≤2*centralEpsilon J*N :=
    fun k => (step_distance (step y i) y₀ (step_distance y y₀ hy i) j k).trans (by linarith)
  let m := centralState (mesh_pos hmesh) hcounts hsmall y hy0
  let ma := centralState (mesh_pos hmesh) hcounts hsmall (step y i) hyi
  let mc := centralState (mesh_pos hmesh) hcounts hsmall (step y j) hyj
  let mac := centralState (mesh_pos hmesh) hcounts hsmall (step (step y i) j) hyij
  have hm := centralState_coordinates (mesh_pos hmesh) hcounts hsmall y hy0
  have ha := centralState_coordinates (mesh_pos hmesh) hcounts hsmall (step y i) hyi
  have hc := centralState_coordinates (mesh_pos hmesh) hcounts hsmall (step y j) hyj
  have hac := centralState_coordinates (mesh_pos hmesh) hcounts hsmall (step (step y i) j) hyij
  have h1 := forward_permitted (mesh_pos hmesh) (mesh_two_le hmesh) m ma i (by rw [ha,hm])
  have h2 := forward_permitted (mesh_pos hmesh) (mesh_two_le hmesh) m mc j (by rw [hc,hm])
  have h3 := forward_permitted (mesh_pos hmesh) (mesh_two_le hmesh) mc mac i (by rw [hac,hc,step_comm])
  have h4 := forward_permitted (mesh_pos hmesh) (mesh_two_le hmesh) ma mac j (by rw [hac,ha])
  have hcm : ∀ k, |((interior (cumulative m.val) k-y₀ k:ℤ):ℝ)|≤2*centralEpsilon J*N := by
    change ∀ k, |((OccupationAbsoluteMass.stateCoordinates m k-y₀ k:ℤ):ℝ)|≤_
    rw [hm]
    exact hy0
  have hcc : ∀ k, |((interior (cumulative mc.val) k-y₀ k:ℤ):ℝ)|≤2*centralEpsilon J*N := by
    change ∀ k, |((OccupationAbsoluteMass.stateCoordinates mc k-y₀ k:ℤ):ℝ)|≤_
    rw [hc]
    exact hyj
  have hh := occupation_mixed_difference hβ hβ₀ hsub ht htC hmesh hlarge hcounts hsmall h1 h2 h3 h4 hcm hcc
  dsimp only
  rw [centralState_weight (mesh_pos hmesh) hcounts hsmall _ hyij,
    centralState_weight (mesh_pos hmesh) hcounts hsmall _ hyj,
    centralState_weight (mesh_pos hmesh) hcounts hsmall _ hyi,
    centralState_weight (mesh_pos hmesh) hcounts hsmall _ hy0]
  exact hh


/-- A genuine individual direction is controlled by the actual unordered
imbalance, using the proved factor two in the directed enumeration. -/
theorem direction_sqrt_bound {J N : ℕ} {t β I : ℝ} (hJ : 0<J) (hJ2 : 2≤J)
    (m : OccupationState J N t) (hm : m.val∈cappedOccupations J N (3*t/4))
    (hmargin : 4≤t*N) (hI : OccupationDrift.imbalance hJ β m hm hmargin≤I)
    (a b : MeshIndex J) (hab : EdgeAdjacent J hJ a b) :
    |Real.sqrt (OccupationDrift.directionRate hJ β m hm hmargin a b)-
      Real.sqrt (OccupationDrift.directionRate hJ β m hm hmargin b a)|≤Real.sqrt (2*I) := by
  classical
  let F : MeshIndex J → MeshIndex J → ℝ := fun a b =>
    (Real.sqrt (OccupationDrift.directionRate hJ β m hm hmargin a b)-
      Real.sqrt (OccupationDrift.directionRate hJ β m hm hmargin b a))^2
  have hn (a b : MeshIndex J) : 0≤(if EdgeAdjacent J hJ a b then F a b else 0) := by
    split
    · exact sq_nonneg _
    · norm_num
  have h1 := Finset.single_le_sum (fun b _ => hn a b) (Finset.mem_univ b)
  have h2 := Finset.single_le_sum (fun a _ => Finset.sum_nonneg (s:=Finset.univ) (fun b _ => hn a b))
    (Finset.mem_univ a)
  rw [ite_eq_left hab] at h1
  have hdir := OccupationDrift.directed_eq_twice_unordered hJ hJ2 F (fun a b => by dsimp only [F]; ring)
  have hh : F a b≤2*I := by
    have hs : F a b≤OccupationDrift.directedSum hJ F := h1.trans h2
    rw [hdir] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left hI (by norm_num))
  simpa only [F,Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hh

/-- Actual rates and detailed balance at any inner state, with only its
literal imbalance as the upstream analytic input. -/
theorem actual_center_rate_increment {J N : ℕ} {t β β₀ I c : ℝ}
    (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤occupationBound β₀)
    (hmesh : 8*(radius β₀+4)≤J) (hlarge : secondDifferenceThreshold J β₀≤N)
    (hmargin : 4≤t*N) (hc : 0<c)
    (m : OccupationState J N t) (hm : m.val∈cappedOccupations J N (3*t/4))
    (hI : OccupationDrift.imbalance (mesh_pos hmesh) β m hm hmargin≤I)
    (a b : MeshIndex J) (hab : EdgeAdjacent J (mesh_pos hmesh) a b)
    (ha : 1≤m.val a) (hb : 1≤m.val b)
    (hr : c*N≤occupationRate (mesh_pos hmesh) β m (movedState m hm hmargin a b ha))
    (hv : c*N≤occupationRate (mesh_pos hmesh) β (movedState m hm hmargin a b ha) m) :
    |Real.log (occupationWeight (mesh_pos hmesh) β (movedState m hm hmargin a b ha))-
      Real.log (occupationWeight (mesh_pos hmesh) β m)|≤
      ((2*Real.sqrt (2*I)+(1+secondDifferenceConstant J β₀/4))/c)/Real.sqrt N := by
  let mp := movedState m hm hmargin a b ha
  let mm := movedState m hm hmargin b a hb
  have hp : PermittedMove (mesh_pos hmesh) m mp a b := ⟨hab,ha,rfl⟩
  have hq : PermittedMove (mesh_pos hmesh) m mm b a := ⟨hab.symm,hb,rfl⟩
  have hN := (secondDifferenceThreshold_bounds hlarge).1
  have hNr : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hNp : (0:ℝ)<N := by linarith
  have himb := direction_sqrt_bound (mesh_pos hmesh) (mesh_two_le hmesh) m hm hmargin hI a b hab
  simp only [OccupationDrift.directionRate,dite_eq_left ha,dite_eq_left hb] at himb
  have hrev := reverse_rate_comparison hβ hβ₀ hsub ht htC hmesh hlarge hmargin m hm a b hab ha hb
  have hrN : occupationRate (mesh_pos hmesh) β m mp≤N :=
    (OccupationAbsoluteMass.occupationRate_le_source (mesh_pos hmesh) (mesh_two_le hmesh) β hp).trans
      (by exact_mod_cast count_le_total m a)
  have hsN : occupationRate (mesh_pos hmesh) β m mm≤N :=
    (OccupationAbsoluteMass.occupationRate_le_source (mesh_pos hmesh) (mesh_two_le hmesh) β hq).trans
      (by exact_mod_cast count_le_total m b)
  have hE : 0≤1+secondDifferenceConstant J β₀/4 := by
    have := secondDifferenceConstant_nonneg J (hβ.trans hβ₀)
    positivity
  have hh := log_rate_ratio_from_imbalance hNr hc (Real.sqrt_nonneg (2*I)) hE hr hv
    (occupationRate_nonneg (mesh_pos hmesh) β m mm) hrN hsN himb hrev
  have hlog := log_weight_increment_of_balance
    (LabelGroundState.occupationWeight_pos (mesh_pos hmesh) hN hβ (hβ₀.trans_lt hsub) m)
    (LabelGroundState.occupationWeight_pos (mesh_pos hmesh) hN hβ (hβ₀.trans_lt hsub) mp)
    ((mul_pos hc hNp).trans_le hr) ((mul_pos hc hNp).trans_le hv)
    (occupation_detailed_balance (mesh_pos hmesh) (mesh_two_le hmesh) β m mp)
  rw [hlog]
  exact hh

/-- The fixed large-N choice supplies all integer rectangle room. -/
theorem central_room {J N : ℕ} (hJ : 0<J) (hN : 64*J^2≤N) : 2≤centralEpsilon J*N := by
  have hJr : (0:ℝ)<(J^2:ℕ) := by exact_mod_cast pow_pos hJ 2
  have hh : (64:ℝ)*(J^2:ℕ)≤N := by exact_mod_cast hN
  unfold centralEpsilon
  have he : (1/(32*(J^2:ℕ):ℝ))*N=(N:ℝ)/(32*(J^2:ℕ)) := by ring
  rw [he]
  apply (le_div_iff₀ (show (0:ℝ)<32*(J^2:ℕ) by positivity)).mpr
  nlinarith only [hh]


/-- The existing rounded near-uniform profile, as an original outer state. -/
def roundedState {J N : ℕ} {t : ℝ} (hJ : 0<J) (hN : 8*J^2≤N)
    (ht : 1/(J^2:ℕ)<t/8) : OccupationState J N t :=
  ⟨rounded J N,rounded_sum hJ N,fun a => by
    have hh := (rounded_capped hJ hN ht).2 a
    have hz : (0:ℝ)≤rounded J N a := Nat.cast_nonneg _
    nlinarith only [hh,hz]⟩

theorem roundedState_inner {J N : ℕ} {t : ℝ} (hJ : 0<J) (hN : 8*J^2≤N)
    (ht : 1/(J^2:ℕ)<t/8) : (roundedState hJ hN ht).val∈cappedOccupations J N (3*t/4) := by
  refine ⟨rounded_sum hJ N,fun a => ?_⟩
  have hh := (rounded_capped hJ hN ht).2 a
  have hz : (0:ℝ)≤rounded J N a := Nat.cast_nonneg _
  change (rounded J N a:ℝ)≤3*t/4*N
  nlinarith only [hh,hz]

theorem central_move_margin {J N : ℕ} {t : ℝ} (hJ : 0<J) (hN : 8*J^2≤N)
    (ht : 1/(J^2:ℕ)<t/8) (ht0 : 0<t) : 4≤t*N := by
  have hJr : (0:ℝ)<(J^2:ℕ) := by exact_mod_cast pow_pos hJ 2
  have hn : (8:ℝ)*(J^2:ℕ)≤N := by exact_mod_cast hN
  have hh := mul_le_mul_of_nonneg_left hn ht0.le
  have ht' := (div_lt_iff₀ hJr).mp ht
  nlinarith only [hh,ht']

/-- The center coefficient depends only on the fixed mesh, beta0 and the
upstream uniform bound for the actual rounded-center imbalance. -/
def centerCoefficient (J : ℕ) (β₀ I : ℝ) : ℝ :=
  (2*Real.sqrt (2*I)+(1+secondDifferenceConstant J β₀/4))/(lowerBound β₀/(4*(J^2:ℕ)))

theorem centerCoefficient_nonneg {J : ℕ} (β₀ I : ℝ) (hβ₀ : 0≤β₀) :
    0≤centerCoefficient J β₀ I := by
  have hq := secondDifferenceConstant_nonneg J hβ₀
  have hl := lowerBound_pos β₀
  unfold centerCoefficient
  positivity

/-- The source center first difference follows from actual lower rates,
reverse-rate error and detailed balance. Only the literal center imbalance
bound is retained as an upstream input. -/
theorem rounded_center_increment {J N : ℕ} {t β β₀ I : ℝ}
    (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤occupationBound β₀)
    (hmesh : 8*(radius β₀+4)≤J) (hlarge : secondDifferenceThreshold J β₀≤N)
    (hcounts : 8*J^2≤N) (hsmall : 1/(J^2:ℕ)<t/8)
    (hroom : 2≤centralEpsilon J*N)
    (hI : OccupationDrift.imbalance (mesh_pos hmesh) β (roundedState (mesh_pos hmesh) hcounts hsmall)
      (roundedState_inner (mesh_pos hmesh) hcounts hsmall)
      (central_move_margin (mesh_pos hmesh) hcounts hsmall ht)≤I)
    (i : Fin (J^2-1)) :
    let y₀ := interior (cumulative (rounded J N))
    let w := OccupationAbsoluteMass.coordinateWeight (N:=N) (t:=t) (mesh_pos hmesh) β
    |Real.log (w (step y₀ i))-Real.log (w y₀)|≤centerCoefficient J β₀ I/Real.sqrt N := by
  let y₀ := interior (cumulative (rounded J N))
  let m := roundedState (mesh_pos hmesh) hcounts hsmall
  have hm : OccupationAbsoluteMass.stateCoordinates m=y₀ := rfl
  have hm0 : ∀ k, |((y₀ k-y₀ k:ℤ):ℝ)|≤centralEpsilon J*N := by
    intro k; simp only [sub_self,Int.cast_zero,abs_zero]; linarith only [hroom]
  have hyi : ∀ k, |((step y₀ i k-y₀ k:ℤ):ℝ)|≤2*centralEpsilon J*N :=
    fun k => (step_distance y₀ y₀ hm0 i k).trans (by linarith)
  let mp := centralState (mesh_pos hmesh) hcounts hsmall (step y₀ i) hyi
  have hp := centralState_coordinates (mesh_pos hmesh) hcounts hsmall (step y₀ i) hyi
  have he : OccupationAbsoluteMass.stateCoordinates mp=step (OccupationAbsoluteMass.stateCoordinates m) i := by rw [hp,hm]
  have hmove := forward_permitted (mesh_pos hmesh) (mesh_two_le hmesh) m mp i he
  have hmi : m.val∈cappedOccupations J N (3*t/4) := roundedState_inner (mesh_pos hmesh) hcounts hsmall
  have hmargin := central_move_margin (mesh_pos hmesh) hcounts hsmall ht
  have hcentral : ∀ k, |((interior (cumulative m.val) k-y₀ k:ℤ):ℝ)|≤2*centralEpsilon J*N := by
    intro k; change |((y₀ k-y₀ k:ℤ):ℝ)|≤_; simp only [sub_self,Int.cast_zero,abs_zero]; linarith only [hroom]
  have hcentralp : ∀ k, |((interior (cumulative mp.val) k-y₀ k:ℤ):ℝ)|≤2*centralEpsilon J*N := by
    change ∀ k, |((OccupationAbsoluteMass.stateCoordinates mp k-y₀ k:ℤ):ℝ)|≤_
    rw [hp]
    exact hyi
  let a := snakeOrder J ⟨i.val+1,by have := i.isLt; omega⟩
  let b := snakeOrder J ⟨i.val,by have := i.isLt; omega⟩
  have ha : 1≤m.val a := hmove.2.1
  have hJr : (0:ℝ)<(J^2:ℕ) := by exact_mod_cast pow_pos (mesh_pos hmesh) 2
  have hb : 1≤m.val b := by
    have hc := central_counts (mesh_pos hmesh) hcounts hsmall m hcentral b
    have hn : (8:ℝ)*(J^2:ℕ)≤N := by exact_mod_cast hcounts
    have hfour : (4:ℝ)≤(N:ℝ)/(2*(J^2:ℕ)) := (le_div_iff₀ (by positivity)).mpr (by nlinarith only [hn])
    have hh : (1:ℝ)≤m.val b := by linarith only [hc,hfour]
    exact_mod_cast hh
  have hmoved : movedState m hmi hmargin a b ha=mp := Subtype.ext hmove.2.2
  have hN := (secondDifferenceThreshold_bounds hlarge).1
  let c := lowerBound β₀/(4*(J^2:ℕ))
  have hc : 0<c := div_pos (lowerBound_pos β₀) (by positivity)
  have hlo := central_rate_lower hN hβ hβ₀ hsub ht htC hmesh hmove
    (central_counts (mesh_pos hmesh) hcounts hsmall m hcentral a)
  have hrevlo := central_rate_lower hN hβ hβ₀ hsub ht htC hmesh (hmove.reverse (mesh_two_le hmesh))
    (central_counts (mesh_pos hmesh) hcounts hsmall mp hcentralp b)
  have hh := actual_center_rate_increment hβ hβ₀ hsub ht htC hmesh hlarge hmargin hc m hmi hI a b hmove.1 ha hb
    (by rw [hmoved]; exact hlo) (by rw [hmoved]; exact hrevlo)
  rw [hmoved] at hh
  dsimp only
  rw [centralState_weight (mesh_pos hmesh) hcounts hsmall _ hyi]
  have hw : OccupationAbsoluteMass.coordinateWeight (N:=N) (t:=t) (mesh_pos hmesh) β y₀=
      occupationWeight (mesh_pos hmesh) β m := OccupationAbsoluteMass.coordinateWeight_state _ β m
  rw [hw]
  exact hh


open IntegerBoxLogWeights FiniteBoxLogSobolev

/-- Uniform coordinate increments propagate along the already constructed
finite integer paths; flooring never enlarges the central cube. -/
theorem function_difference_on_cube {D : ℕ} (H : (Fin D → ℤ) → ℝ)
    (y₀ y : Fin D → ℤ) {T R L : ℝ} (hR : 0≤R) (hRT : R≤T) (hL : 0≤L)
    (hy : ∀ i, |((y i-y₀ i:ℤ):ℝ)|≤R)
    (hf : ∀ z, (∀ i, |((z i-y₀ i:ℤ):ℝ)|≤T) → ∀ i, |H (step z i)-H z|≤L) :
    |H y-H y₀|≤(D:ℝ)*(2*R)*L := by
  classical
  let r := ⌊R⌋₊
  let l : Fin D → ℤ := fun i => y₀ i-(r:ℤ)
  have hr : (r:ℝ)≤R := Nat.floor_le hR
  have hyr (i : Fin D) : |y i-y₀ i|≤(r:ℤ) := by
    have habs := congrArg (fun a : ℤ => (a:ℝ)) (Int.natCast_natAbs (y i-y₀ i))
    simp only [Int.cast_natCast,Int.cast_abs] at habs
    have hh : ((y i-y₀ i).natAbs:ℝ)≤R := by rw [habs]; exact hy i
    have hn : (y i-y₀ i).natAbs≤r := (Nat.le_floor_iff hR).mpr hh
    rw [← Int.natCast_natAbs]
    exact_mod_cast hn
  have hmem (z : Fin D → ℤ) (hz : ∀ i, |z i-y₀ i|≤(r:ℤ)) : z∈integerBox l (2*r) := by
    intro i
    have hh := abs_le.mp (hz i)
    change y₀ i-(r:ℤ)≤z i ∧ z i≤y₀ i-(r:ℤ)+(2*r:ℕ)
    constructor <;> omega
  let a := (chartEquiv l).symm ⟨y₀,hmem y₀ (by intro i; simp)⟩
  let b := (chartEquiv l).symm ⟨y,hmem y hyr⟩
  have ha : chart l a=y₀ := congrArg Subtype.val ((chartEquiv l).apply_symm_apply _)
  have hb : chart l b=y := congrArg Subtype.val ((chartEquiv l).apply_symm_apply _)
  have hc (x : Box D (2*r)) : ∀ i, |((chart l x i-y₀ i:ℤ):ℝ)|≤T := by
    intro i
    have hi := (x i).isLt
    have hh : |chart l x i-y₀ i|≤(r:ℤ) := by
      change |y₀ i-(r:ℤ)+(x i).val-y₀ i|≤(r:ℤ)
      rw [abs_le]
      constructor <;> omega
    have hh' : |((chart l x i-y₀ i:ℤ):ℝ)|≤(r:ℝ) := by exact_mod_cast hh
    exact hh'.trans (hr.trans hRT)
  have hforward (x : Box D (2*r)) (i : Fin D) (hi : (x i).val<2*r) :
      |H (chart l (Function.update x i ⟨(x i).val+1,Nat.succ_lt_succ hi⟩))-H (chart l x)|≤L := by
    have he : chart l (Function.update x i ⟨(x i).val+1,Nat.succ_lt_succ hi⟩)=step (chart l x) i := by
      funext j
      by_cases hj : j=i
      · subst j
        simp only [chart,step,Function.update_self,Nat.cast_add,Nat.cast_one]
        ring
      · simp only [chart,step,Function.update_of_ne hj]
    rw [he]
    exact hf (chart l x) (hc x) i
  have hh := oscillation_of_forward_bound (fun x : Box D (2*r) => H (chart l x)) hL hforward a b
  simp only [ha,hb,Nat.cast_mul,Nat.cast_ofNat] at hh
  apply hh.trans
  gcongr

/-- Explicit propagation coefficient, uniform in particle number and beta. -/
def gradientCoefficient (J : ℕ) (β₀ I : ℝ) : ℝ :=
  centerCoefficient J β₀ I+2*(J^2-1:ℕ)*(secondDifferenceConstant J β₀+4*(J^2:ℕ))

theorem gradientCoefficient_nonneg (J : ℕ) (β₀ I : ℝ) (hβ₀ : 0≤β₀) :
    0≤gradientCoefficient J β₀ I := by
  have h0 := centerCoefficient_nonneg (J:=J) β₀ I hβ₀
  have h1 := secondDifferenceConstant_nonneg J hβ₀
  unfold gradientCoefficient
  positivity

/-- Source central log-gradient mechanism for the actual coordinateWeight.
Only the actual rounded-center imbalance bound remains upstream. The local
log-gradient conclusion is derived from rates, mixed differences and paths. -/
theorem central_log_increment {J N : ℕ} {t β β₀ I : ℝ}
    (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤occupationBound β₀)
    (hmesh : 8*(radius β₀+4)≤J) (hlarge : secondDifferenceThreshold J β₀≤N)
    (hcounts : 8*J^2≤N) (hsmall : 1/(J^2:ℕ)<t/8)
    (hroom : 2≤centralEpsilon J*N)
    (hI : OccupationDrift.imbalance (mesh_pos hmesh) β (roundedState (mesh_pos hmesh) hcounts hsmall)
      (roundedState_inner (mesh_pos hmesh) hcounts hsmall)
      (central_move_margin (mesh_pos hmesh) hcounts hsmall ht)≤I) :
    IntegerBoxMassGeometry.LogIncrementBound (interior (cumulative (rounded J N)))
      (centralEpsilon J*N) N (gradientCoefficient J β₀ I)
      (OccupationAbsoluteMass.coordinateWeight (N:=N) (t:=t) (mesh_pos hmesh) β) := by
  intro y hy i _hyi
  let y₀ := interior (cumulative (rounded J N))
  let w := OccupationAbsoluteMass.coordinateWeight (N:=N) (t:=t) (mesh_pos hmesh) β
  let G : Interior J → ℝ := fun z => Real.log (w (step z i))-Real.log (w z)
  let R : ℝ := ‖fun j => ((y j-y₀ j:ℤ):ℝ)‖
  let K : ℝ := secondDifferenceConstant J β₀+4*(J^2:ℕ)
  have hK : 0≤K := add_nonneg (secondDifferenceConstant_nonneg J (hβ.trans hβ₀)) (by positivity)
  have hR : 0≤R := norm_nonneg _
  have hRT : R≤centralEpsilon J*N := by
    apply (pi_norm_le_iff_of_nonneg (by linarith only [hroom])).mpr
    intro j
    simpa only [Real.norm_eq_abs] using hy j
  have hyR : ∀ j, |((y j-y₀ j:ℤ):ℝ)|≤R := by
    intro j
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun k => ((y k-y₀ k:ℤ):ℝ)) j
  have hf : ∀ z, (∀ j, |((z j-y₀ j:ℤ):ℝ)|≤centralEpsilon J*N) →
      ∀ j, |G (step z j)-G z|≤K/N := by
    intro z hz j
    have hh := coordinate_mixed_difference hβ hβ₀ hsub ht htC hmesh hlarge hcounts hsmall hroom z hz i j
    change |Real.log (w (step (step z i) j))-Real.log (w (step z j))-
      Real.log (w (step z i))+Real.log (w z)|≤K/N at hh
    have he : G (step z j)-G z=Real.log (w (step (step z i) j))-Real.log (w (step z j))-
        Real.log (w (step z i))+Real.log (w z) := by
      dsimp only [G]
      rw [step_comm z j i]
      ring
    rw [he]
    exact hh
  have hh := function_difference_on_cube G y₀ y hR hRT
    (div_nonneg hK (Nat.cast_nonneg N)) hyR hf
  have hc := rounded_center_increment hβ hβ₀ hsub ht htC hmesh hlarge hcounts hsmall hroom hI i
  change |G y₀|≤centerCoefficient J β₀ I/Real.sqrt N at hc
  have h0 := centerCoefficient_nonneg (J:=J) β₀ I (hβ.trans hβ₀)
  have hdk : 0≤2*(J^2-1:ℕ)*K := by positivity
  have hC0 : centerCoefficient J β₀ I≤gradientCoefficient J β₀ I := by
    change centerCoefficient J β₀ I≤centerCoefficient J β₀ I+2*(J^2-1:ℕ)*K
    linarith only [hdk]
  have hCK : 2*(J^2-1:ℕ)*K≤gradientCoefficient J β₀ I := by
    change 2*(J^2-1:ℕ)*K≤centerCoefficient J β₀ I+2*(J^2-1:ℕ)*K
    linarith only [h0]
  change |G y|≤gradientCoefficient J β₀ I*(1/Real.sqrt N+R/N)
  calc
    _ ≤ |G y-G y₀|+|G y₀| := by
      have hh := abs_add_le (G y-G y₀) (G y₀)
      simpa only [sub_add_cancel] using hh
    _ ≤ (J^2-1:ℕ)*(2*R)*(K/N)+centerCoefficient J β₀ I/Real.sqrt N := add_le_add hh hc
    _ = centerCoefficient J β₀ I*(1/Real.sqrt N)+(2*(J^2-1:ℕ)*K)*(R/N) := by ring
    _ ≤ gradientCoefficient J β₀ I*(1/Real.sqrt N)+gradientCoefficient J β₀ I*(R/N) :=
      add_le_add (mul_le_mul_of_nonneg_right hC0 (by positivity))
        (mul_le_mul_of_nonneg_right hCK (div_nonneg hR (Nat.cast_nonneg N)))
    _ = _ := by ring

/-- Fixed epsilon and a fixed N threshold discharge every rectangle margin.
The source epsilon_c is centralEpsilon/2, so its cube radius is the literal
centralEpsilon*N used here. No first-gradient or mixed-gradient hypothesis remains. -/
theorem source_log_increment {J N : ℕ} {t β β₀ I : ℝ}
    (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤occupationBound β₀)
    (hmesh : 8*(radius β₀+4)≤J) (hlarge : secondDifferenceThreshold J β₀≤N)
    (hcounts : 64*J^2≤N) (hsmall : 1/(J^2:ℕ)<t/8)
    (hI : OccupationDrift.imbalance (mesh_pos hmesh) β
      (roundedState (mesh_pos hmesh) (show 8*J^2≤N by omega) hsmall)
      (roundedState_inner (mesh_pos hmesh) (show 8*J^2≤N by omega) hsmall)
      (central_move_margin (mesh_pos hmesh) (show 8*J^2≤N by omega) hsmall ht)≤I) :
    IntegerBoxMassGeometry.LogIncrementBound (interior (cumulative (rounded J N)))
      (centralEpsilon J*N) N (gradientCoefficient J β₀ I)
      (OccupationAbsoluteMass.coordinateWeight (N:=N) (t:=t) (mesh_pos hmesh) β) :=
  central_log_increment hβ hβ₀ hsub ht htC hmesh hlarge (by omega) hsmall
    (central_room (mesh_pos hmesh) hcounts) hI

end PeriodicAttractiveLogGas.OccupationCentralLogGradient
