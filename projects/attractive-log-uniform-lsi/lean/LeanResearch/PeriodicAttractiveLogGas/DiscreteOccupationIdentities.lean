import LeanResearch.PeriodicAttractiveLogGas.LabelRatioTransport
import LeanResearch.PeriodicAttractiveLogGas.FiniteGraph
import Mathlib.Combinatorics.SimpleGraph.Basic

/-! Source Lemma 3.10: the actual label and occupation graphs at the
stated outer cap, unconditioned weights, reversibility, and restriction of
the label energy to occupation observables. SOURCE_ONLY candidate.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace PeriodicAttractiveLogGas.DiscreteOccupationIdentities

open MeshCells MeshAdjacentCells CellRestrictions LabelOccupations
  LabelExchangeability OccupationProbability LabelRatioTransport

abbrev LabelState (J N : ℕ) (t : ℝ) := ↥(goodLabels J N t)
abbrev OccupationState (J N : ℕ) (t : ℝ) := ↥(cappedOccupations J N t)

instance labelStateFintype (J N : ℕ) (t : ℝ) : Fintype (LabelState J N t) :=
  Fintype.ofFinite _

def labelOfState {J N : ℕ} {t : ℝ} (m : OccupationState J N t) : LabelState J N t :=
  ⟨labelOfProfile m.val m.property.1, by
    change OccupationCap t (labelOfProfile m.val m.property.1)
    intro a
    simpa only [occupation_labelOfProfile] using m.property.2 a⟩

def profile {J N : ℕ} {t : ℝ} (η : LabelState J N t) : OccupationState J N t :=
  ⟨occupation η.val, sum_occupation η.val, η.property⟩

@[simp] theorem profile_labelOfState {J N : ℕ} {t : ℝ} (m : OccupationState J N t) :
    profile (labelOfState m) = m := by
  apply Subtype.ext
  exact occupation_labelOfProfile _ _

instance occupationStateFintype (J N : ℕ) (t : ℝ) : Fintype (OccupationState J N t) :=
  Fintype.ofInjective labelOfState fun m m' h ↦ by
    have := congrArg profile h
    simpa only [profile_labelOfState] using this

def labelWeight {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ) (η : LabelState J N t) : ℝ :=
  (labelProbability hJ η.val β).toReal

def qWeight {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ) (m : OccupationState J N t) : ℝ :=
  (profileWeight (N := N) hJ m.val β).toReal

/-- The actual unconditioned occupation-event mass, not Q. -/
def occupationWeight {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ)
    (m : OccupationState J N t) : ℝ :=
  (gibbsMeasure greenRealRepresentative N β (occupationEvent hJ m.val)).toReal

def multiplicity {J N : ℕ} {t : ℝ} (m : OccupationState J N t) : ℕ :=
  N.factorial / ∏ a : MeshIndex J, (m.val a).factorial

theorem labelWeight_eq_qWeight {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ)
    (η : LabelState J N t) : labelWeight hJ β η = qWeight hJ β (profile η) := by
  exact congrArg ENNReal.toReal (labelProbability_eq_profileWeight hJ η.val β)

theorem occupationWeight_eq {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ)
    (m : OccupationState J N t) :
    occupationWeight hJ β m = (multiplicity m : ℝ) * qWeight hJ β m := by
  simp only [occupationWeight, occupationProbability_profile hJ m.val m.property.1 β,
    ENNReal.toReal_mul, ENNReal.toReal_natCast, multiplicity, qWeight]

theorem multiplicity_mul_factorials {J N : ℕ} {t : ℝ} (m : OccupationState J N t) :
    multiplicity m * (∏ a : MeshIndex J, (m.val a).factorial) = N.factorial := by
  have h := card_sameOccupation_mul_factorials (labelOfProfile m.val m.property.1)
  rw [card_sameOccupation, occupation_labelOfProfile] at h
  exact h

def profileFiberEquiv {J N : ℕ} {t : ℝ} (m : OccupationState J N t) :
    {η : LabelState J N t // profile η = m} ≃
      ↥(sameOccupation (labelOfProfile m.val m.property.1)) where
  toFun η := ⟨η.val.val, by
    rw [mem_sameOccupation, occupation_labelOfProfile]
    exact congrArg Subtype.val η.property⟩
  invFun η := by
    have he : occupation η.val = m.val := by
      simpa only [mem_sameOccupation, occupation_labelOfProfile] using η.property
    refine ⟨⟨η.val, ?_⟩, ?_⟩
    · intro a
      simpa only [he] using m.property.2 a
    · exact Subtype.ext he
  left_inv η := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv η := by apply Subtype.ext; rfl

theorem card_profile_fiber {J N : ℕ} {t : ℝ} (m : OccupationState J N t) :
    Fintype.card {η : LabelState J N t // profile η = m} = multiplicity m := by
  classical
  simpa only [Fintype.card_coe, card_sameOccupation, occupation_labelOfProfile, multiplicity] using
    Fintype.card_congr (profileFiberEquiv m)

theorem sum_by_profile {J N : ℕ} {t : ℝ} (F : OccupationState J N t → ℝ) :
    (∑ η : LabelState J N t, F (profile η)) =
      ∑ m : OccupationState J N t, (multiplicity m : ℝ) * F m := by
  classical
  have h := Fintype.sum_fiberwise' (profile : LabelState J N t → OccupationState J N t) F
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_profile_fiber] using h.symm

theorem labelWeight_pos {J N : ℕ} {t β : ℝ} (hJ : 0 < J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) (η : LabelState J N t) : 0 < labelWeight hJ β η :=
  ENNReal.toReal_pos (labelProbability_ne_zero hJ hN η.val hβ hsub)
    (labelProbability_ne_top hJ hN η.val hβ hsub)

theorem qWeight_pos {J N : ℕ} {t β : ℝ} (hJ : 0 < J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) (m : OccupationState J N t) : 0 < qWeight hJ β m := by
  have h := labelWeight_pos hJ hN hβ hsub (labelOfState m)
  rwa [labelWeight_eq_qWeight, profile_labelOfState] at h

theorem moveOccupation_source {J : ℕ} (m : MeshIndex J → ℕ) {a b : MeshIndex J}
    (hab : a ≠ b) : moveOccupation m a b a = m a - 1 := by
  simp only [moveOccupation, ite_true, ite_eq_right hab.symm, add_zero]

theorem moveOccupation_target {J : ℕ} (m : MeshIndex J → ℕ) {a b : MeshIndex J}
    (hab : a ≠ b) : moveOccupation m a b b = m b + 1 := by
  simp only [moveOccupation, ite_eq_right hab, ite_true, Nat.sub_zero]

theorem moveOccupation_other {J : ℕ} (m : MeshIndex J → ℕ) {a b c : MeshIndex J}
    (hac : a ≠ c) (hbc : b ≠ c) : moveOccupation m a b c = m c := by
  simp only [moveOccupation, ite_eq_right hac, ite_eq_right hbc, Nat.sub_zero, add_zero]

theorem moveOccupation_inverse {J : ℕ} (m : MeshIndex J → ℕ) {a b : MeshIndex J}
    (hab : a ≠ b) (ha : 1 ≤ m a) : moveOccupation (moveOccupation m a b) b a = m := by
  funext c
  by_cases hac : a = c
  · subst c
    rw [moveOccupation_target _ hab.symm, moveOccupation_source _ hab]
    omega
  · by_cases hbc : b = c
    · subst c
      rw [moveOccupation_source _ hab.symm, moveOccupation_target _ hab]
      omega
    · rw [moveOccupation_other _ hbc hac, moveOccupation_other _ hac hbc]

theorem moveOccupation_ne {J : ℕ} (m : MeshIndex J → ℕ) {a b : MeshIndex J}
    (hab : a ≠ b) (ha : 1 ≤ m a) : moveOccupation m a b ≠ m := by
  intro h
  have hh := congrFun h a
  rw [moveOccupation_source m hab] at hh
  omega

theorem moveOccupation_unique {J : ℕ} (m : MeshIndex J → ℕ)
    {a b c d : MeshIndex J} (hab : a ≠ b) (_hcd : c ≠ d)
    (ha : 1 ≤ m a) (_hc : 1 ≤ m c)
    (h : moveOccupation m a b = moveOccupation m c d) : a = c ∧ b = d := by
  have hac : a = c := by
    by_contra hac
    have hh := congrFun h a
    by_cases hda : d = a <;>
      simp only [moveOccupation, ite_true, ite_eq_right hab.symm, ite_eq_right (Ne.symm hac),
        hda, ite_false, Nat.sub_zero, add_zero] at hh <;> omega
  subst c
  refine ⟨rfl, ?_⟩
  by_contra hbd
  have hh := congrFun h b
  simp only [moveOccupation, ite_eq_right hab, ite_true, ite_eq_right (Ne.symm hbd),
    Nat.sub_zero] at hh
  omega

def PermittedMove {J N : ℕ} {t : ℝ} (hJ : 0 < J)
    (m m' : OccupationState J N t) (a b : MeshIndex J) : Prop :=
  EdgeAdjacent J hJ a b ∧ 1 ≤ m.val a ∧ moveOccupation m.val a b = m'.val

theorem PermittedMove.reverse {J N : ℕ} {t : ℝ} {hJ : 0 < J} (hJ2 : 2 ≤ J)
    {m m' : OccupationState J N t} {a b : MeshIndex J} (h : PermittedMove hJ m m' a b) :
    PermittedMove hJ m' m b a := by
  refine ⟨h.1.symm, ?_, ?_⟩
  · rw [← h.2.2, moveOccupation_target _ (h.1.ne hJ2)]
    omega
  · rw [← h.2.2, moveOccupation_inverse _ (h.1.ne hJ2) h.2.1]

theorem PermittedMove.target_count {J N : ℕ} {t : ℝ} {hJ : 0 < J} (hJ2 : 2 ≤ J)
    {m m' : OccupationState J N t} {a b : MeshIndex J} (h : PermittedMove hJ m m' a b) :
    m'.val b = m.val b + 1 := by
  rw [← h.2.2, moveOccupation_target _ (h.1.ne hJ2)]

theorem PermittedMove.unique {J N : ℕ} {t : ℝ} {hJ : 0 < J} (hJ2 : 2 ≤ J)
    {m m' : OccupationState J N t} {a b c d : MeshIndex J}
    (h : PermittedMove hJ m m' a b) (h' : PermittedMove hJ m m' c d) : a = c ∧ b = d :=
  moveOccupation_unique m.val (h.1.ne hJ2) (h'.1.ne hJ2) h.2.1 h'.2.1
    (h.2.2.trans h'.2.2.symm)

def occupationGraph {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hJ2 : 2 ≤ J) :
    SimpleGraph (OccupationState J N t) where
  Adj m m' := ∃ a b, PermittedMove hJ m m' a b
  symm := ⟨fun _ _ ⟨a, b, h⟩ ↦ ⟨b, a, h.reverse hJ2⟩⟩
  loopless := ⟨fun m ⟨_, _, h⟩ ↦ moveOccupation_ne m.val (h.1.ne hJ2) h.2.1 h.2.2⟩

/-- The zero branch suppresses every nonpermitted move. In the other
branch the source cell is uniquely determined, as proved below. -/
def occupationRate {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ)
    (m m' : OccupationState J N t) : ℝ := by
  classical
  exact if h : ∃ a b, PermittedMove hJ m m' a b then
    (m.val h.choose : ℝ) * qWeight hJ β m' / (qWeight hJ β m + qWeight hJ β m') else 0

theorem occupationRate_of_move {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (β : ℝ) {m m' : OccupationState J N t} {a b : MeshIndex J}
    (h : PermittedMove hJ m m' a b) :
    occupationRate hJ β m m' =
      (m.val a : ℝ) * qWeight hJ β m' / (qWeight hJ β m + qWeight hJ β m') := by
  classical
  have he : ∃ c d, PermittedMove hJ m m' c d := ⟨a, b, h⟩
  have hc := (h.unique hJ2 he.choose_spec.choose_spec).1
  simp only [occupationRate, dite_eq_left he, ← hc]

theorem occupationRate_eq_zero {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ)
    {m m' : OccupationState J N t} (h : ¬ ∃ a b, PermittedMove hJ m m' a b) :
    occupationRate hJ β m m' = 0 := by simp only [occupationRate, dite_eq_right h]

theorem occupationRate_reverse {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (β : ℝ) {m m' : OccupationState J N t} {a b : MeshIndex J}
    (h : PermittedMove hJ m m' a b) :
    occupationRate hJ β m' m = (m.val b + 1 : ℕ) *
      qWeight hJ β m / (qWeight hJ β m + qWeight hJ β m') := by
  rw [occupationRate_of_move hJ hJ2 β (h.reverse hJ2), h.target_count hJ2,
    add_comm (qWeight hJ β m') (qWeight hJ β m)]

theorem product_eq_two_mul {J : ℕ} (f : MeshIndex J → ℕ) {a b : MeshIndex J} (hab : a ≠ b) :
    (∏ c, f c) = f a * f b * ∏ c ∈ (Finset.univ.erase a).erase b, f c := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ a),
    ← Finset.mul_prod_erase (Finset.univ.erase a) f (by simp [hab.symm] : b ∈ Finset.univ.erase a)]
  ring

theorem factorial_product_move {J : ℕ} (m : MeshIndex J → ℕ) {a b : MeshIndex J}
    (hab : a ≠ b) (ha : 1 ≤ m a) :
    (∏ c, (moveOccupation m a b c).factorial) * m a =
      (∏ c, (m c).factorial) * (m b + 1) := by
  classical
  have hs : (∏ c ∈ (Finset.univ.erase a).erase b, (moveOccupation m a b c).factorial) =
      ∏ c ∈ (Finset.univ.erase a).erase b, (m c).factorial := by
    apply Finset.prod_congr rfl
    intro c hc
    have hca := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
    have hcb := (Finset.mem_erase.mp hc).1
    rw [moveOccupation_other _ hca.symm hcb.symm]
  rw [product_eq_two_mul (fun c ↦ (moveOccupation m a b c).factorial) hab,
    product_eq_two_mul (fun c ↦ (m c).factorial) hab,
    moveOccupation_source _ hab, moveOccupation_target _ hab, Nat.factorial_succ, hs]
  have hf := Nat.mul_factorial_pred (by omega : m a ≠ 0)
  calc
    _ = (m a * (m a - 1).factorial) * (m b).factorial *
        (∏ c ∈ (Finset.univ.erase a).erase b, (m c).factorial) * (m b + 1) := by ring
    _ = _ := by rw [hf]

/-- The literal factorial identity from the source proof. -/
theorem multiplicity_move {J N : ℕ} {t : ℝ} {hJ : 0 < J} (hJ2 : 2 ≤ J)
    {m m' : OccupationState J N t} {a b : MeshIndex J} (h : PermittedMove hJ m m' a b) :
    multiplicity m * m.val a = multiplicity m' * (m.val b + 1) := by
  have hf : (∏ c, (m'.val c).factorial) * m.val a =
      (∏ c, (m.val c).factorial) * (m.val b + 1) := by
    rw [← h.2.2]
    exact factorial_product_move m.val (h.1.ne hJ2) h.2.1
  have hp : 0 < ∏ c, (m'.val c).factorial := Finset.prod_pos fun _ _ ↦ Nat.factorial_pos _
  apply mul_right_cancel₀ hp.ne'
  calc
    _ = multiplicity m * ((∏ c, (m'.val c).factorial) * m.val a) := by ring
    _ = multiplicity m * ((∏ c, (m.val c).factorial) * (m.val b + 1)) := by rw [hf]
    _ = (multiplicity m * ∏ c, (m.val c).factorial) * (m.val b + 1) := by ring
    _ = N.factorial * (m.val b + 1) := by rw [multiplicity_mul_factorials]
    _ = (multiplicity m' * ∏ c, (m'.val c).factorial) * (m.val b + 1) := by
      rw [multiplicity_mul_factorials]
    _ = _ := by ring

theorem occupation_detailed_balance_of_move {J N : ℕ} {t : ℝ}
    (hJ : 0 < J) (hJ2 : 2 ≤ J) (β : ℝ)
    {m m' : OccupationState J N t} {a b : MeshIndex J} (h : PermittedMove hJ m m' a b) :
    occupationWeight hJ β m * occupationRate hJ β m m' =
      occupationWeight hJ β m' * occupationRate hJ β m' m := by
  have hc : (multiplicity m : ℝ) * m.val a = (multiplicity m' : ℝ) * (m.val b + 1 : ℕ) := by
    exact_mod_cast multiplicity_move hJ2 h
  rw [occupationWeight_eq, occupationWeight_eq, occupationRate_of_move hJ hJ2 β h,
    occupationRate_reverse hJ hJ2 β h]
  calc
    _ = ((multiplicity m : ℝ) * m.val a) *
        (qWeight hJ β m * qWeight hJ β m' / (qWeight hJ β m + qWeight hJ β m')) := by ring
    _ = _ := by rw [hc]; ring

theorem occupation_detailed_balance {J N : ℕ} {t : ℝ}
    (hJ : 0 < J) (hJ2 : 2 ≤ J) (β : ℝ) (m m' : OccupationState J N t) :
    occupationWeight hJ β m * occupationRate hJ β m m' =
      occupationWeight hJ β m' * occupationRate hJ β m' m := by
  classical
  by_cases h : ∃ a b, PermittedMove hJ m m' a b
  · obtain ⟨a, b, h⟩ := h
    exact occupation_detailed_balance_of_move hJ hJ2 β h
  · have hr : ¬ ∃ a b, PermittedMove hJ m' m a b := by
      rintro ⟨a, b, hr⟩
      exact h ⟨b, a, hr.reverse hJ2⟩
    rw [occupationRate_eq_zero hJ β h, occupationRate_eq_zero hJ β hr, mul_zero, mul_zero]

/-- Both endpoints are vertices at the same outer cap. -/
def LabelAdjacent {J N : ℕ} {t : ℝ} (hJ : 0 < J) (η ζ : LabelState J N t) : Prop :=
  ∃ i : Fin N, EdgeAdjacent J hJ (η.val i) (ζ.val i) ∧
    Function.update η.val i (ζ.val i) = ζ.val

theorem LabelAdjacent.symm {J N : ℕ} {t : ℝ} {hJ : 0 < J}
    {η ζ : LabelState J N t} (h : LabelAdjacent hJ η ζ) : LabelAdjacent hJ ζ η := by
  classical
  obtain ⟨i, he, hu⟩ := h
  refine ⟨i, he.symm, ?_⟩
  funext j
  by_cases hj : j = i
  · subst j
    exact Function.update_self _ _ _
  · rw [Function.update_of_ne hj]
    have hh := congrFun hu j
    simpa only [Function.update_of_ne hj] using hh.symm

theorem LabelAdjacent.ne {J N : ℕ} {t : ℝ} {hJ : 0 < J} (hJ2 : 2 ≤ J)
    {η ζ : LabelState J N t} (h : LabelAdjacent hJ η ζ) : η ≠ ζ := by
  rintro rfl
  obtain ⟨i, he, _⟩ := h
  exact he.ne hJ2 rfl

def labelGraph {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hJ2 : 2 ≤ J) :
    SimpleGraph (LabelState J N t) where
  Adj := LabelAdjacent hJ
  symm := ⟨fun _ _ h ↦ h.symm⟩
  loopless := ⟨fun _ h ↦ h.ne hJ2 rfl⟩

theorem update_site_unique {J N : ℕ} (η : LabelVector J N)
    {i j : Fin N} {b c : MeshIndex J} (hib : η i ≠ b)
    (h : Function.update η i b = Function.update η j c) : i = j ∧ b = c := by
  classical
  have hij : i = j := by
    by_contra hij
    have hh := congrFun h i
    rw [Function.update_self, Function.update_of_ne hij] at hh
    exact hib hh.symm
  subst j
  exact ⟨rfl, by simpa only [Function.update_self] using congrFun h i⟩

theorem permittedMove_of_label_step {J N : ℕ} {t : ℝ} {hJ : 0 < J}
    {η ζ : LabelState J N t} {i : Fin N}
    (he : EdgeAdjacent J hJ (η.val i) (ζ.val i))
    (hu : Function.update η.val i (ζ.val i) = ζ.val) :
    PermittedMove hJ (profile η) (profile ζ) (η.val i) (ζ.val i) := by
  refine ⟨he, occupation_at_label_pos η.val i, ?_⟩
  have h := occupation_update η.val i (η.val i) (ζ.val i) rfl
  rw [hu] at h
  exact h.symm

def movedLabel {J N : ℕ} {t : ℝ} {hJ : 0 < J}
    (η : LabelState J N t) (m' : OccupationState J N t) {a b : MeshIndex J}
    (h : PermittedMove hJ (profile η) m' a b) (i : {i : Fin N // η.val i = a}) :
    LabelState J N t :=
  ⟨Function.update η.val i.val b, by
    change OccupationCap t (Function.update η.val i.val b)
    intro c
    have hc := occupation_update η.val i.val a b i.property
    rw [hc]
    change (moveOccupation (profile η).val a b c : ℝ) ≤ t * N
    rw [h.2.2]
    exact m'.property.2 c⟩

theorem profile_movedLabel {J N : ℕ} {t : ℝ} {hJ : 0 < J}
    (η : LabelState J N t) (m' : OccupationState J N t) {a b : MeshIndex J}
    (h : PermittedMove hJ (profile η) m' a b) (i : {i : Fin N // η.val i = a}) :
    profile (movedLabel η m' h i) = m' := by
  apply Subtype.ext
  exact (occupation_update η.val i.val a b i.property).trans h.2.2

theorem adjacent_movedLabel {J N : ℕ} {t : ℝ} {hJ : 0 < J}
    (η : LabelState J N t) (m' : OccupationState J N t) {a b : MeshIndex J}
    (h : PermittedMove hJ (profile η) m' a b) (i : {i : Fin N // η.val i = a}) :
    LabelAdjacent hJ η (movedLabel η m' h i) := by
  refine ⟨i.val, ?_, ?_⟩
  · simpa only [movedLabel, Function.update_self, i.property] using h.1
  · simp only [movedLabel, Function.update_self]

/-- Exact edge count: the neighboring labelings with the stated target
profile are in bijection with the coordinates carrying its source label. -/
def labelMoveFiberEquiv {J N : ℕ} {t : ℝ} {hJ : 0 < J} (hJ2 : 2 ≤ J)
    (η : LabelState J N t) (m' : OccupationState J N t) {a b : MeshIndex J}
    (h : PermittedMove hJ (profile η) m' a b) :
    {i : Fin N // η.val i = a} ≃
      {ζ : LabelState J N t // LabelAdjacent hJ η ζ ∧ profile ζ = m'} := by
  classical
  let f : {i : Fin N // η.val i = a} →
      {ζ : LabelState J N t // LabelAdjacent hJ η ζ ∧ profile ζ = m'} :=
    fun i ↦ ⟨movedLabel η m' h i, adjacent_movedLabel η m' h i, profile_movedLabel η m' h i⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    have hh : Function.update η.val i.val b = Function.update η.val j.val b :=
      congrArg (fun ζ ↦ ζ.val.val) hij
    apply Subtype.ext
    exact (update_site_unique η.val (by simpa only [i.property] using h.1.ne hJ2) hh).1
  · intro ζ
    obtain ⟨i, he, hu⟩ := ζ.property.1
    have hs := permittedMove_of_label_step he hu
    rw [ζ.property.2] at hs
    have hab := hs.unique hJ2 h
    refine ⟨⟨i, hab.1⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change Function.update η.val i b = ζ.val.val
    rw [← hab.2]
    exact hu

open Classical in
theorem card_labelMove_fiber {J N : ℕ} {t : ℝ} {hJ : 0 < J} (hJ2 : 2 ≤ J)
    (η : LabelState J N t) (m' : OccupationState J N t) {a b : MeshIndex J}
    (h : PermittedMove hJ (profile η) m' a b) :
    Fintype.card {ζ : LabelState J N t // LabelAdjacent hJ η ζ ∧ profile ζ = m'} =
      (profile η).val a := by
  classical
  simpa only [Fintype.card_subtype, profile, occupation] using
    (Fintype.card_congr (labelMoveFiberEquiv hJ2 η m' h)).symm

open Classical in
theorem directed_label_edges_of_move {J N : ℕ} {t : ℝ} {hJ : 0 < J} (hJ2 : 2 ≤ J)
    {m m' : OccupationState J N t} {a b : MeshIndex J} (h : PermittedMove hJ m m' a b) :
    Fintype.card (Σ η : {η : LabelState J N t // profile η = m},
      {ζ : LabelState J N t // LabelAdjacent hJ η.val ζ ∧ profile ζ = m'}) =
      multiplicity m * m.val a := by
  classical
  rw [Fintype.card_sigma]
  have hf (η : {η : LabelState J N t // profile η = m}) :
      Fintype.card {ζ : LabelState J N t // LabelAdjacent hJ η.val ζ ∧ profile ζ = m'} = m.val a := by
    have hm : PermittedMove hJ (profile η.val) m' a b := η.property.symm ▸ h
    rw [card_labelMove_fiber hJ2 η.val m' hm, η.property]
  simp only [hf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_profile_fiber, Nat.cast_id]

def labelRate {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ)
    (η ζ : LabelState J N t) : ℝ := by
  classical
  exact if LabelAdjacent hJ η ζ then labelWeight hJ β ζ /
    (labelWeight hJ β η + labelWeight hJ β ζ) else 0

def labelConductance {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ)
    (η ζ : LabelState J N t) : ℝ := by
  classical
  exact if LabelAdjacent hJ η ζ then labelWeight hJ β η * labelWeight hJ β ζ /
    (labelWeight hJ β η + labelWeight hJ β ζ) else 0

theorem labelRate_nonneg {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ)
    (η ζ : LabelState J N t) : 0 ≤ labelRate hJ β η ζ := by
  classical
  unfold labelRate
  split_ifs
  · exact div_nonneg ENNReal.toReal_nonneg (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  · exact le_rfl

theorem occupationRate_nonneg {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ)
    (m m' : OccupationState J N t) : 0 ≤ occupationRate hJ β m m' := by
  classical
  unfold occupationRate
  split_ifs
  · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg)
      (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  · exact le_rfl

theorem labelWeight_mul_rate {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ)
    (η ζ : LabelState J N t) :
    labelWeight hJ β η * labelRate hJ β η ζ = labelConductance hJ β η ζ := by
  classical
  by_cases h : LabelAdjacent hJ η ζ <;> simp only [labelRate, labelConductance, h, ite_true,
    ite_false, mul_zero]
  ring

theorem labelConductance_symm {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ)
    (η ζ : LabelState J N t) : labelConductance hJ β η ζ = labelConductance hJ β ζ η := by
  classical
  have he : LabelAdjacent hJ η ζ ↔ LabelAdjacent hJ ζ η := ⟨LabelAdjacent.symm, LabelAdjacent.symm⟩
  simp only [labelConductance, he, mul_comm, add_comm]

theorem labelConductance_self {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (β : ℝ) (η : LabelState J N t) : labelConductance hJ β η η = 0 := by
  classical
  exact ite_eq_right fun h ↦ h.ne hJ2 rfl

theorem label_detailed_balance {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ)
    (η ζ : LabelState J N t) :
    labelWeight hJ β η * labelRate hJ β η ζ = labelWeight hJ β ζ * labelRate hJ β ζ η := by
  rw [labelWeight_mul_rate, labelWeight_mul_rate, labelConductance_symm]

theorem sum_labelRate_profile {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (β : ℝ) (η : LabelState J N t) (m' : OccupationState J N t) :
    (∑ ζ : LabelState J N t, if profile ζ = m' then labelRate hJ β η ζ else 0) =
      occupationRate hJ β (profile η) m' := by
  classical
  let C := qWeight hJ β m' / (qWeight hJ β (profile η) + qWeight hJ β m')
  have heq : (∑ ζ : LabelState J N t, if profile ζ = m' then labelRate hJ β η ζ else 0) =
      ∑ ζ : LabelState J N t, if LabelAdjacent hJ η ζ ∧ profile ζ = m' then C else 0 := by
    apply Finset.sum_congr rfl
    intro ζ _
    by_cases hp : profile ζ = m' <;> by_cases he : LabelAdjacent hJ η ζ <;>
      simp only [hp, he, labelRate, labelWeight_eq_qWeight, C, and_true, and_false,
        ite_true, ite_false]
  rw [heq]
  by_cases h : ∃ a b, PermittedMove hJ (profile η) m' a b
  · obtain ⟨a, b, h⟩ := h
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      ← Fintype.card_subtype, card_labelMove_fiber hJ2 η m' h,
      occupationRate_of_move hJ hJ2 β h]
    dsimp only [C]
    ring
  · rw [occupationRate_eq_zero hJ β h]
    apply Finset.sum_eq_zero
    intro ζ _
    apply ite_eq_right
    rintro ⟨⟨i, he, hu⟩, hp⟩
    have hs := permittedMove_of_label_step he hu
    rw [hp] at hs
    exact h ⟨η.val i, ζ.val i, hs⟩

def labelTerm {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ) (Φ : LabelState J N t → ℝ)
    (η ζ : LabelState J N t) : ℝ := labelConductance hJ β η ζ * (Φ ζ - Φ η) ^ 2

theorem labelTerm_symm {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ)
    (Φ : LabelState J N t → ℝ) (η ζ : LabelState J N t) :
    labelTerm hJ β Φ η ζ = labelTerm hJ β Φ ζ η := by
  rw [labelTerm, labelTerm, labelConductance_symm]
  ring

/-- A fixed enumeration chooses exactly one orientation of each
unordered label edge. The enumeration has no probabilistic role. -/
def labelRank {J N : ℕ} {t : ℝ} (η : LabelState J N t) : Fin (Fintype.card (LabelState J N t)) :=
  Fintype.equivFin (LabelState J N t) η

def labelEnergy {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ) (Φ : LabelState J N t → ℝ) : ℝ :=
  ∑ η : LabelState J N t, ∑ ζ : LabelState J N t,
    if labelRank η < labelRank ζ then labelTerm hJ β Φ η ζ else 0

theorem labelTerm_orientation_split {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ)
    (Φ : LabelState J N t → ℝ) (η ζ : LabelState J N t) :
    labelTerm hJ β Φ η ζ =
      (if labelRank η < labelRank ζ then labelTerm hJ β Φ η ζ else 0) +
      (if labelRank ζ < labelRank η then labelTerm hJ β Φ ζ η else 0) := by
  rcases lt_trichotomy (labelRank η) (labelRank ζ) with h | h | h
  · simp only [ite_eq_left h, ite_eq_right (not_lt.mpr h.le), add_zero]
  · have he : η = ζ := (Fintype.equivFin (LabelState J N t)).injective h
    subst ζ
    simp only [lt_self_iff_false, ite_false, labelTerm, sub_self, zero_pow (by omega : 2 ≠ 0), mul_zero,
      add_zero]
  · simp only [ite_eq_right (not_lt.mpr h.le), ite_eq_left h, zero_add]
    exact labelTerm_symm hJ β Φ η ζ

/-- Every unordered edge is counted twice by the directed sum. -/
theorem directed_label_sum_eq_twice {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ)
    (Φ : LabelState J N t → ℝ) :
    (∑ η : LabelState J N t, ∑ ζ : LabelState J N t, labelTerm hJ β Φ η ζ) =
      2 * labelEnergy hJ β Φ := by
  calc
    _ = ∑ η : LabelState J N t, ∑ ζ : LabelState J N t,
        ((if labelRank η < labelRank ζ then labelTerm hJ β Φ η ζ else 0) +
          (if labelRank ζ < labelRank η then labelTerm hJ β Φ ζ η else 0)) := by
      apply Finset.sum_congr rfl
      intro η _
      apply Finset.sum_congr rfl
      intro ζ _
      exact labelTerm_orientation_split hJ β Φ η ζ
    _ = labelEnergy hJ β Φ + labelEnergy hJ β Φ := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun η ζ : LabelState J N t ↦
        if labelRank ζ < labelRank η then labelTerm hJ β Φ ζ η else 0)]
      rfl
    _ = _ := by ring

theorem labelEnergy_eq_directed {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ)
    (Φ : LabelState J N t → ℝ) :
    labelEnergy hJ β Φ = FiniteGraph.energy (labelWeight hJ β) (labelRate hJ β) Φ := by
  unfold FiniteGraph.energy
  simp_rw [labelWeight_mul_rate]
  change labelEnergy hJ β Φ = (1 / 2 : ℝ) *
    ∑ η : LabelState J N t, ∑ ζ : LabelState J N t, labelTerm hJ β Φ η ζ
  rw [directed_label_sum_eq_twice]
  ring

/-- Literal source occupation form, with one half of the directed sum. -/
def occupationEnergy {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ)
    (F : OccupationState J N t → ℝ) : ℝ :=
  FiniteGraph.energy (occupationWeight hJ β) (occupationRate hJ β) F

theorem sum_weighted_fibers {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (p : A → B) (w : A → ℝ) (F : B → ℝ) :
    (∑ a, w a * F (p a)) = ∑ b, (∑ a, if p a = b then w a else 0) * F b := by
  classical
  symm
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul]
  simp

theorem label_row_energy_on_profiles {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (β : ℝ) (F : OccupationState J N t → ℝ) (η : LabelState J N t) :
    (∑ ζ : LabelState J N t,
      labelWeight hJ β η * labelRate hJ β η ζ * (F (profile ζ) - F (profile η)) ^ 2) =
      qWeight hJ β (profile η) * ∑ m' : OccupationState J N t,
        occupationRate hJ β (profile η) m' * (F m' - F (profile η)) ^ 2 := by
  rw [labelWeight_eq_qWeight]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  rw [sum_weighted_fibers profile (labelRate hJ β η) (fun m' ↦ (F m' - F (profile η)) ^ 2)]
  simp_rw [sum_labelRate_profile hJ hJ2 β η]

/-- Source Lemma 3.10: exact restriction to every real occupation
observable. The graph is always the one at the stated outer cap t. -/
theorem energy_occupation_restriction {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (β : ℝ) (F : OccupationState J N t → ℝ) :
    labelEnergy hJ β (F ∘ profile) = occupationEnergy hJ β F := by
  rw [labelEnergy_eq_directed]
  unfold occupationEnergy FiniteGraph.energy
  simp only [Function.comp_apply]
  simp_rw [label_row_energy_on_profiles hJ hJ2 β F]
  rw [sum_by_profile (fun m : OccupationState J N t ↦ qWeight hJ β m *
    ∑ m', occupationRate hJ β m m' * (F m' - F m) ^ 2)]
  change (1 / 2 : ℝ) *
      (∑ m : OccupationState J N t, (multiplicity m : ℝ) *
        (qWeight hJ β m * ∑ m', occupationRate hJ β m m' * (F m' - F m) ^ 2)) =
    (1 / 2 : ℝ) * ∑ m : OccupationState J N t, ∑ m',
      occupationWeight hJ β m * occupationRate hJ β m m' * (F m' - F m) ^ 2
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [occupationWeight_eq]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m' _
  ring

def labelCapMass {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ) : ℝ :=
  ∑ η : LabelState J N t, labelWeight hJ β η

def occupationCapMass {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ) : ℝ :=
  ∑ m : OccupationState J N t, occupationWeight hJ β m

theorem capMass_eq {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ) :
    labelCapMass (N := N) (t := t) hJ β = occupationCapMass (N := N) (t := t) hJ β := by
  unfold labelCapMass occupationCapMass
  simp_rw [labelWeight_eq_qWeight, occupationWeight_eq]
  exact sum_by_profile (qWeight hJ β)

theorem capEvent_eq_union {J N : ℕ} {t : ℝ} (hJ : 0 < J) :
    {X : Configuration N | OccupationCap t (configurationMeshLabel N J hJ X)} =
      ⋃ η : LabelState J N t, labelFiber hJ η.val := by
  ext X
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro hX
    refine ⟨⟨configurationMeshLabel N J hJ X, hX⟩, ?_⟩
    rw [labelFiber_eq_label_preimage]
    rfl
  · rintro ⟨η, hX⟩
    rw [labelFiber_eq_label_preimage] at hX
    change configurationMeshLabel N J hJ X = η.val at hX
    rw [hX]
    exact η.property

/-- The normalization factor is the actual mass of the cap event under
the original Green ensemble, not an unspecified positive constant. -/
theorem labelCapMass_eq_actual {J N : ℕ} {t β : ℝ} (hJ : 0 < J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) :
    labelCapMass (N := N) (t := t) hJ β =
      (gibbsMeasure greenRealRepresentative N β
        {X : Configuration N | OccupationCap t (configurationMeshLabel N J hJ X)}).toReal := by
  rw [capEvent_eq_union hJ, measure_iUnion, tsum_fintype]
  · rw [ENNReal.toReal_sum (fun η _ ↦ labelProbability_ne_top hJ hN η.val hβ hsub)]
    rfl
  · intro η ζ hne
    exact disjoint_labelFiber hJ fun he ↦ hne (Subtype.ext he)
  · intro η
    exact measurableSet_labelFiber hJ η.val

theorem labelCapMass_pos {J N : ℕ} {t β : ℝ} (hJ : 0 < J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) (hne : (goodLabels J N t).Nonempty) :
    0 < labelCapMass (N := N) (t := t) hJ β := by
  obtain ⟨η, hη⟩ := hne
  have hp := labelWeight_pos hJ hN hβ hsub (⟨η, hη⟩ : LabelState J N t)
  have hs : labelWeight hJ β (⟨η, hη⟩ : LabelState J N t) ≤
      ∑ ζ : LabelState J N t, labelWeight hJ β ζ :=
    Finset.single_le_sum (fun ζ _ ↦ (show 0 ≤ labelWeight hJ β ζ from ENNReal.toReal_nonneg))
      (Finset.mem_univ _)
  exact hp.trans_le hs

/-- Conditioning multiplies both restriction energies by the same
positive factor; it never changes the outer transition graph. -/
theorem normalized_energy_restriction {J N : ℕ} {t β : ℝ}
    (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ N) (hβ : 0 ≤ β) (hsub : β < 4)
    (hne : (goodLabels J N t).Nonempty) (F : OccupationState J N t → ℝ) :
    0 < (labelCapMass (N := N) (t := t) hJ β)⁻¹ ∧
      (labelCapMass (N := N) (t := t) hJ β)⁻¹ * labelEnergy hJ β (F ∘ profile) =
        (occupationCapMass (N := N) (t := t) hJ β)⁻¹ * occupationEnergy hJ β F := by
  refine ⟨inv_pos.mpr (labelCapMass_pos hJ hN hβ hsub hne), ?_⟩
  rw [capMass_eq, energy_occupation_restriction hJ hJ2 β F]

theorem energy_scale_weights {A : Type*} [Fintype A] (c : ℝ)
    (w : A → ℝ) (r : A → A → ℝ) (F : A → ℝ) :
    FiniteGraph.energy (fun a ↦ c * w a) r F = c * FiniteGraph.energy w r F := by
  unfold FiniteGraph.energy
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

/-- The normalized weighted forms use the same rates and the same outer
graphs. The only alteration is division of the actual weights by cap mass. -/
theorem conditioned_forms_restriction {J N : ℕ} {t β : ℝ}
    (hJ : 0 < J) (hJ2 : 2 ≤ J) (F : OccupationState J N t → ℝ) :
    FiniteGraph.energy
        (fun η : LabelState J N t ↦ (labelCapMass (N := N) (t := t) hJ β)⁻¹ * labelWeight hJ β η)
        (labelRate hJ β) (F ∘ profile) =
      FiniteGraph.energy
        (fun m : OccupationState J N t ↦
          (occupationCapMass (N := N) (t := t) hJ β)⁻¹ * occupationWeight hJ β m)
        (occupationRate hJ β) F := by
  rw [energy_scale_weights, energy_scale_weights, ← labelEnergy_eq_directed,
    energy_occupation_restriction hJ hJ2 β F, capMass_eq]
  rfl

/-- Source Lemma 3.10 in the genuine probabilistic parameter range.
The identities themselves above are algebraic; here the cap normalization
is strictly positive and the weights are those of the actual Green law. -/
theorem discreteIdentities {J N : ℕ} {t β : ℝ}
    (hJ : 0 < J) (hJ3 : 3 ≤ J) (hN : 2 ≤ N) (hβ : 0 ≤ β) (hsub : β < 4)
    (_ht : 0 < t) (hne : (goodLabels J N t).Nonempty) :
    (∀ (m m' : OccupationState J N t) (a b : MeshIndex J), PermittedMove hJ m m' a b →
      occupationWeight hJ β m * occupationRate hJ β m m' =
        occupationWeight hJ β m' * occupationRate hJ β m' m ∧
      occupationRate hJ β m' m = (m.val b + 1 : ℕ) *
        qWeight hJ β m / (qWeight hJ β m + qWeight hJ β m')) ∧
    (∀ F : OccupationState J N t → ℝ,
      labelEnergy hJ β (F ∘ profile) = occupationEnergy hJ β F) ∧
    (0 < labelCapMass (N := N) (t := t) hJ β ∧
      labelCapMass (N := N) (t := t) hJ β = occupationCapMass (N := N) (t := t) hJ β) := by
  have hJ2 : 2 ≤ J := by omega
  exact ⟨fun _ _ _ _ h ↦ ⟨occupation_detailed_balance_of_move hJ hJ2 β h,
      occupationRate_reverse hJ hJ2 β h⟩,
    fun F ↦ energy_occupation_restriction hJ hJ2 β F,
    labelCapMass_pos hJ hN hβ hsub hne, capMass_eq hJ β⟩

end PeriodicAttractiveLogGas.DiscreteOccupationIdentities
