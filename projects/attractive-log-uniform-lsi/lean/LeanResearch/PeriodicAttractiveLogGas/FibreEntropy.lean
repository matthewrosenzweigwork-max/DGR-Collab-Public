import LeanResearch.PeriodicAttractiveLogGas.FibreProjection
import LeanResearch.PeriodicAttractiveLogGas.CenteredL2

/-! Source 3045–3062: entropy on the original, unnormalized outer restriction
and the actual uniform directed-move coupling between occupation fibres. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace PeriodicAttractiveLogGas.FibreEntropy
open MeshCells LabelOccupations CellRestrictions DiscreteOccupationIdentities FibreProjection
variable {J N : ℕ} {t : ℝ}

/-- The finite expression for entropy, without normalizing the total weight. -/
def finiteEntropy {α : Type*} [Fintype α] (w F : α → ℝ) : ℝ :=
  (∑ x, w x * (F x * Real.log (F x))) -
    (∑ x, w x * F x) * Real.log (∑ x, w x * F x)

def uniformFibreEntropy (F : LabelState J N t → ℝ) (m : OccupationState J N t) : ℝ :=
  fibreAverage (fun η => F η * Real.log (F η)) m -
    fibreAverage F m * Real.log (fibreAverage F m)

theorem weighted_sum_by_fibres (hJ : 0 < J) (β : ℝ) (F : LabelState J N t → ℝ) :
    (∑ η, labelWeight hJ β η * F η) =
      ∑ m, occupationWeight hJ β m * fibreAverage F m := by
  rw [sum_by_fibres]
  apply Finset.sum_congr rfl
  intro m _
  have hc : (Fintype.card (Fibre m) : ℝ) ≠ 0 := by exact_mod_cast (fibre_card_pos m).ne'
  simp only [labelWeight_eq_qWeight, profile_fibre, ← Finset.mul_sum,
    occupationWeight_eq, ← card_profile_fiber, fibreAverage]
  field_simp

/-- No total-mass normalization occurs: this identity applies directly to
outer subprobability restrictions and to functions zero outside inner classes. -/
theorem fibre_entropy_chain (hJ : 0 < J) (β : ℝ) (F : LabelState J N t → ℝ) :
    finiteEntropy (labelWeight hJ β) F =
      (∑ m, occupationWeight hJ β m * uniformFibreEntropy F m) +
        finiteEntropy (occupationWeight hJ β) (fibreAverage F) := by
  unfold finiteEntropy uniformFibreEntropy
  rw [weighted_sum_by_fibres, weighted_sum_by_fibres]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

theorem fibreAverage_nonneg {F : LabelState J N t → ℝ} (hF : ∀ η, 0 ≤ F η)
    (m : OccupationState J N t) : 0 ≤ fibreAverage F m :=
  div_nonneg (Finset.sum_nonneg fun η _ => hF η.val) (Nat.cast_nonneg _)

/-- Literal finite weighted measure; its total mass is not renormalized. -/
def finiteMeasure {α : Type*} [Fintype α] [MeasurableSpace α] (w : α → ℝ) : Measure α :=
  ∑ x, ENNReal.ofReal (w x) • Measure.dirac x

instance finiteMeasure_isFinite {α : Type*} [Fintype α] [MeasurableSpace α]
    (w : α → ℝ) : IsFiniteMeasure (finiteMeasure w) := by
  constructor
  simp [finiteMeasure, Measure.finsetSum_apply]

theorem integral_finiteMeasure {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (w F : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∫ x, F x ∂finiteMeasure w) = ∑ x, w x * F x := by
  unfold finiteMeasure
  rw [integral_finsetSum_measure (fun _ _ =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw _), smul_eq_mul]

/-- The real finite expression is the existing extended entropy on its
actual finite measure, also when that measure has mass strictly below one. -/
theorem entropy_finiteMeasure {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (w F : α → ℝ) (hw : ∀ x, 0 ≤ w x) (hF : ∀ x, 0 ≤ F x) :
    entropy (finiteMeasure w) F = (finiteEntropy w F : EReal) := by
  rw [entropy_eq_integral (Filter.Eventually.of_forall hF) Integrable.of_finite,
    integral_finiteMeasure _ _ hw, integral_finiteMeasure _ _ hw]
  rfl

/-- Uniform probability on a nonempty finite type, proved by actual mass. -/
theorem uniform_finiteMeasure_probability {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hc : 0 < Fintype.card α) :
    IsProbabilityMeasure (finiteMeasure (fun _ : α => (Fintype.card α : ℝ)⁻¹)) := by
  let μ := finiteMeasure (fun _ : α => (Fintype.card α : ℝ)⁻¹)
  have hc' : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have hi := integral_finiteMeasure (fun _ : α => (Fintype.card α : ℝ)⁻¹)
    (fun _ => (1 : ℝ)) (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  have hm : μ.real univ = 1 := by
    simpa only [integral_const, smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_inv_cancel₀ hc'] using hi
  constructor
  change μ univ = 1
  calc
    μ univ = ENNReal.ofReal (μ.real univ) := (ENNReal.ofReal_toReal (measure_ne_top μ univ)).symm
    _ = 1 := by rw [hm]; norm_num

theorem entropy_uniform_fibre (F : LabelState J N t → ℝ) (hF : ∀ η, 0 ≤ F η)
    (m : OccupationState J N t) :
    entropy (finiteMeasure (fun _ : Fibre m => (Fintype.card (Fibre m) : ℝ)⁻¹))
      (fun η => F η.val) = (uniformFibreEntropy F m : EReal) := by
  rw [entropy_finiteMeasure (fun _ : Fibre m => (Fintype.card (Fibre m) : ℝ)⁻¹)
    (fun η : Fibre m => F η.val)
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)) (fun η => hF η.val)]
  congr 1
  simp only [finiteEntropy, uniformFibreEntropy, fibreAverage, div_eq_mul_inv, ← Finset.mul_sum]
  simp only [mul_comm]

/-- Entropy chain in the existing extended entropy convention, using the
original unconditioned label and occupation weights on the outer cap. -/
theorem actual_entropy_chain (hJ : 0 < J) (β : ℝ) (F : LabelState J N t → ℝ)
    (hF : ∀ η, 0 ≤ F η) :
    entropy (finiteMeasure (labelWeight hJ β)) F =
      (((∑ m, occupationWeight hJ β m * uniformFibreEntropy F m) : ℝ) : EReal) +
        entropy (finiteMeasure (occupationWeight hJ β)) (fibreAverage F) := by
  rw [entropy_finiteMeasure (labelWeight hJ β) F (fun _ => ENNReal.toReal_nonneg) hF,
    entropy_finiteMeasure (occupationWeight hJ β) (fibreAverage F)
      (fun _ => ENNReal.toReal_nonneg) (fibreAverage_nonneg hF),
    ← EReal.coe_add, fibre_entropy_chain]

/-- Taking an inner union of classes uses literal zero extension, without
conditioning or renormalizing the outer label law. -/
theorem fibreAverage_zeroExtension (F : LabelState J N t → ℝ)
    (S : Finset (OccupationState J N t)) (m : OccupationState J N t) :
    fibreAverage (fun η => if profile η ∈ S then F η else 0) m =
      if m ∈ S then fibreAverage F m else 0 := by
  classical
  unfold fibreAverage
  simp only [profile_fibre]
  split_ifs <;> simp

theorem uniformFibreEntropy_zeroExtension (F : LabelState J N t → ℝ)
    (S : Finset (OccupationState J N t)) (m : OccupationState J N t) :
    uniformFibreEntropy (fun η => if profile η ∈ S then F η else 0) m =
      if m ∈ S then uniformFibreEntropy F m else 0 := by
  classical
  by_cases hm : m ∈ S <;>
    simp [uniformFibreEntropy, fibreAverage, profile_fibre, hm]

/-- Exact source chain for an arbitrary inner union of occupation classes.
Both outer measures remain unnormalized, and zero class means are retained. -/
theorem actual_entropy_chain_zeroExtension (hJ : 0 < J) (β : ℝ)
    (F : LabelState J N t → ℝ) (hF : ∀ η, 0 ≤ F η)
    (S : Finset (OccupationState J N t)) :
    entropy (finiteMeasure (labelWeight hJ β))
      (fun η => if profile η ∈ S then F η else 0) =
      (((∑ m ∈ S, occupationWeight hJ β m * uniformFibreEntropy F m) : ℝ) : EReal) +
        entropy (finiteMeasure (occupationWeight hJ β))
          (fun m => if m ∈ S then fibreAverage F m else 0) := by
  classical
  have hn (η : LabelState J N t) : 0 ≤ if profile η ∈ S then F η else 0 := by
    split_ifs
    · exact hF η
    · exact le_rfl
  have hh := actual_entropy_chain hJ β (fun η => if profile η ∈ S then F η else 0) hn
  have he : fibreAverage (fun η => if profile η ∈ S then F η else 0) =
      fun m => if m ∈ S then fibreAverage F m else 0 :=
    funext (fibreAverage_zeroExtension F S)
  rw [he] at hh
  simpa [uniformFibreEntropy_zeroExtension, mul_ite, ← Finset.sum_filter] using hh

/-- Literal directed moves: uniformly choose a source word and one of its
coordinates with the prescribed source cell. Target words are recorded exactly. -/
abbrev MoveCoupling (hJ : 0 < J) (m m' : OccupationState J N t) :=
  Σ η : Fibre m, {ζ : LabelState J N t // LabelAdjacent hJ η.val ζ ∧ profile ζ = m'}

instance moveCouplingFintype (hJ : 0 < J) (m m' : OccupationState J N t) :
    Fintype (MoveCoupling hJ m m') := by
  classical
  unfold MoveCoupling
  infer_instance

instance moveCouplingMeasurableSingletonClass (hJ : 0 < J) (m m' : OccupationState J N t) :
    MeasurableSingletonClass (MoveCoupling hJ m m') := by
  classical
  constructor
  intro e
  rcases e with ⟨η, ζ⟩
  change MeasurableSet[⨅ ξ : Fibre m,
    (inferInstance : MeasurableSpace {z : LabelState J N t //
      LabelAdjacent hJ ξ.val z ∧ profile z = m'}).map (Sigma.mk ξ)]
    ({⟨η, ζ⟩} : Set (MoveCoupling hJ m m'))
  rw [MeasurableSpace.measurableSet_iInf]
  change ∀ ξ : Fibre m, MeasurableSet ((Sigma.mk ξ) ⁻¹'
    ({⟨η, ζ⟩} : Set (MoveCoupling hJ m m')))
  intro ξ
  by_cases he : ξ = η
  · subst ξ
    have hs : (Sigma.mk η) ⁻¹' ({⟨η, ζ⟩} : Set (MoveCoupling hJ m m')) = {ζ} := by
      ext z
      simp
    rw [hs]
    exact measurableSet_singleton ζ
  · have hs : (Sigma.mk ξ) ⁻¹' ({⟨η, ζ⟩} : Set (MoveCoupling hJ m m')) = ∅ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hz
      exact he (congrArg Sigma.fst hz)
    rw [hs]
    exact MeasurableSet.empty

def moveReverse (hJ : 0 < J) (m m' : OccupationState J N t) :
    MoveCoupling hJ m m' ≃ MoveCoupling hJ m' m where
  toFun e := ⟨⟨e.2.val, e.2.property.2⟩, ⟨e.1.val, e.2.property.1.symm, e.1.property⟩⟩
  invFun e := ⟨⟨e.2.val, e.2.property.2⟩, ⟨e.1.val, e.2.property.1.symm, e.1.property⟩⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

def moveAverage (hJ : 0 < J) (m m' : OccupationState J N t)
    (F : MoveCoupling hJ m m' → ℝ) : ℝ :=
  (∑ e, F e) / Fintype.card (MoveCoupling hJ m m')

theorem move_card (hJ : 0 < J) (hJ2 : 2 ≤ J) {m m' : OccupationState J N t}
    {a b : MeshIndex J} (h : PermittedMove hJ m m' a b) :
    Fintype.card (MoveCoupling hJ m m') = Fintype.card (Fibre m) * m.val a := by
  rw [directed_label_edges_of_move hJ2 h, card_profile_fiber]

theorem move_card_pos (hJ : 0 < J) (hJ2 : 2 ≤ J) {m m' : OccupationState J N t}
    {a b : MeshIndex J} (h : PermittedMove hJ m m' a b) :
    0 < Fintype.card (MoveCoupling hJ m m') := by
  rw [move_card hJ hJ2 h]
  exact Nat.mul_pos (fibre_card_pos m) h.2.1

/-- The actual source marginal is uniform, proved from its exact degree. -/
theorem moveAverage_left (hJ : 0 < J) (hJ2 : 2 ≤ J) {m m' : OccupationState J N t}
    {a b : MeshIndex J} (h : PermittedMove hJ m m' a b) (F : LabelState J N t → ℝ) :
    moveAverage hJ m m' (fun e => F e.1.val) = fibreAverage F m := by
  classical
  have ha : (m.val a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h.2.1)
  have hf : (Fintype.card (Fibre m) : ℝ) ≠ 0 := by exact_mod_cast (fibre_card_pos m).ne'
  have hd (η : Fibre m) :
      Fintype.card {ζ : LabelState J N t // LabelAdjacent hJ η.val ζ ∧ profile ζ = m'} = m.val a := by
    have hh : PermittedMove hJ (profile η.val) m' a b := η.property.symm ▸ h
    rw [card_labelMove_fiber hJ2 η.val m' hh, η.property]
  unfold moveAverage fibreAverage
  rw [Fintype.sum_sigma, move_card hJ hJ2 h]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hd, Nat.cast_mul,
    ← Finset.mul_sum]
  field_simp

/-- Reversing the literal edge set proves the uniform target marginal; its
degree is the target count, including the newly added particle. -/
theorem moveAverage_right (hJ : 0 < J) (hJ2 : 2 ≤ J) {m m' : OccupationState J N t}
    {a b : MeshIndex J} (h : PermittedMove hJ m m' a b) (F : LabelState J N t → ℝ) :
    moveAverage hJ m m' (fun e => F e.2.val) = fibreAverage F m' := by
  have hh := Equiv.sum_comp (moveReverse hJ m m') (fun e => F e.1.val)
  have hc := Fintype.card_congr (moveReverse hJ m m')
  calc
    moveAverage hJ m m' (fun e => F e.2.val) =
        moveAverage hJ m' m (fun e => F e.1.val) := by
      unfold moveAverage
      rw [hc]
      exact congrArg (fun x : ℝ => x / Fintype.card (MoveCoupling hJ m' m)) hh
    _ = _ := moveAverage_left hJ hJ2 (h.reverse hJ2) F

theorem move_uniform_probability (hJ : 0 < J) (hJ2 : 2 ≤ J)
    {m m' : OccupationState J N t} {a b : MeshIndex J} (h : PermittedMove hJ m m' a b) :
    IsProbabilityMeasure (finiteMeasure
      (fun _ : MoveCoupling hJ m m' => (Fintype.card (MoveCoupling hJ m m') : ℝ)⁻¹)) :=
  uniform_finiteMeasure_probability (move_card_pos hJ hJ2 h)

theorem integral_uniform_finiteMeasure {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (F : α → ℝ) :
    (∫ x, F x ∂finiteMeasure (fun _ : α => (Fintype.card α : ℝ)⁻¹)) =
      (∑ x, F x) / Fintype.card α := by
  rw [integral_finiteMeasure (fun _ : α => (Fintype.card α : ℝ)⁻¹) F
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)), ← Finset.mul_sum, div_eq_mul_inv, mul_comm]

/-- Both literal uniform probability marginals, tested against every real
function; finiteness supplies all needed integrability automatically. -/
theorem move_uniform_marginals (hJ : 0 < J) (hJ2 : 2 ≤ J)
    {m m' : OccupationState J N t} {a b : MeshIndex J} (h : PermittedMove hJ m m' a b)
    (F : LabelState J N t → ℝ) :
    let μ := finiteMeasure
      (fun _ : MoveCoupling hJ m m' => (Fintype.card (MoveCoupling hJ m m') : ℝ)⁻¹)
    (∫ e, F e.1.val ∂μ) =
      (∫ η : Fibre m, F η.val ∂finiteMeasure (fun _ => (Fintype.card (Fibre m) : ℝ)⁻¹)) ∧
    (∫ e, F e.2.val ∂μ) =
      (∫ η : Fibre m', F η.val ∂finiteMeasure (fun _ => (Fintype.card (Fibre m') : ℝ)⁻¹)) := by
  dsimp only
  simp only [integral_uniform_finiteMeasure]
  exact ⟨moveAverage_left hJ hJ2 h F, moveAverage_right hJ hJ2 h F⟩

/-- Reverse Euclidean L2 triangle with literal finite second moments. -/
theorem reverse_sqrt_sum_sq {α : Type*} [Fintype α] (f g : α → ℝ) :
    (Real.sqrt (∑ x, f x ^ 2) - Real.sqrt (∑ x, g x ^ 2)) ^ 2 ≤
      ∑ x, (f x - g x) ^ 2 := by
  let u : EuclideanSpace ℝ α := WithLp.toLp 2 f
  let v : EuclideanSpace ℝ α := WithLp.toLp 2 g
  have hu : ‖u‖ ^ 2 = ∑ x, f x ^ 2 := EuclideanSpace.real_norm_sq_eq u
  have hv : ‖v‖ ^ 2 = ∑ x, g x ^ 2 := EuclideanSpace.real_norm_sq_eq v
  have hd : ‖u - v‖ ^ 2 = ∑ x, (f x - g x) ^ 2 := by
    simpa only [PiLp.sub_apply] using EuclideanSpace.real_norm_sq_eq (u - v)
  rw [← hu, ← hv, ← hd, Real.sqrt_sq (norm_nonneg u), Real.sqrt_sq (norm_nonneg v)]
  have hh := mul_self_le_mul_self (abs_nonneg _) (abs_norm_sub_norm_le u v)
  simpa only [← sq, sq_abs] using hh

theorem reverse_sqrt_average {α : Type*} [Fintype α] (f g : α → ℝ) :
    (Real.sqrt ((∑ x, f x ^ 2) / Fintype.card α) -
      Real.sqrt ((∑ x, g x ^ 2) / Fintype.card α)) ^ 2 ≤
        (∑ x, (f x - g x) ^ 2) / Fintype.card α := by
  rw [Real.sqrt_div (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sqrt_div (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    ← sub_div, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (reverse_sqrt_sum_sq f g) (Nat.cast_nonneg _)

/-- Actual coupling inequality for the two uniform occupation fibres. -/
theorem move_sqrt_projection (hJ : 0 < J) (hJ2 : 2 ≤ J) {m m' : OccupationState J N t}
    {a b : MeshIndex J} (h : PermittedMove hJ m m' a b)
    (F : LabelState J N t → ℝ) (hF : ∀ η, 0 ≤ F η) :
    (Real.sqrt (fibreAverage F m') - Real.sqrt (fibreAverage F m)) ^ 2 ≤
      moveAverage hJ m m' (fun e => (Real.sqrt (F e.2.val) - Real.sqrt (F e.1.val)) ^ 2) := by
  have hl := moveAverage_left hJ hJ2 h F
  have hr := moveAverage_right hJ hJ2 h F
  have hh := reverse_sqrt_average (fun e : MoveCoupling hJ m m' => Real.sqrt (F e.2.val))
    (fun e => Real.sqrt (F e.1.val))
  simp only [Real.sq_sqrt (hF _)] at hh
  change (Real.sqrt (moveAverage hJ m m' (fun e => F e.2.val)) -
    Real.sqrt (moveAverage hJ m m' (fun e => F e.1.val))) ^ 2 ≤ _ at hh
  rwa [hl, hr] at hh

open Classical in
/-- The literal coupling sum, with each directed edge counted once. -/
theorem move_sum_eq (hJ : 0 < J) (m m' : OccupationState J N t)
    (G : LabelState J N t → LabelState J N t → ℝ) :
    (∑ e : MoveCoupling hJ m m', G e.1.val e.2.val) =
      ∑ η : Fibre m, ∑ ζ : LabelState J N t,
        if LabelAdjacent hJ η.val ζ ∧ profile ζ = m' then G η.val ζ else 0 := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro η _
  rw [← Finset.sum_subtype
    (p := fun ζ : LabelState J N t => LabelAdjacent hJ η.val ζ ∧ profile ζ = m')
    (Finset.univ.filter fun ζ => LabelAdjacent hJ η.val ζ ∧ profile ζ = m')
    (by simp) (fun ζ => G η.val ζ)]
  simp only [Finset.sum_filter]

theorem move_conductance_sum (hJ : 0 < J) (β : ℝ) (m m' : OccupationState J N t)
    (G : LabelState J N t → LabelState J N t → ℝ) :
    (qWeight hJ β m * qWeight hJ β m' / (qWeight hJ β m + qWeight hJ β m')) *
      (∑ e : MoveCoupling hJ m m', G e.1.val e.2.val) =
        ∑ η : Fibre m, ∑ ζ : LabelState J N t,
          if profile ζ = m' then labelConductance hJ β η.val ζ * G η.val ζ else 0 := by
  classical
  rw [move_sum_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ζ _
  by_cases hp : profile ζ = m' <;> by_cases he : LabelAdjacent hJ η.val ζ <;>
    simp only [hp, he, and_self, and_false, false_and, ite_true, ite_false,
      labelConductance, labelWeight_eq_qWeight, profile_fibre, mul_zero, zero_mul]

/-- Exact occupation conductance times uniform coupling expectation equals
original directed label conductance, with no occupation-dependent loss. -/
theorem occupation_conductance_average (hJ : 0 < J) (hJ2 : 2 ≤ J) (β : ℝ)
    {m m' : OccupationState J N t} {a b : MeshIndex J}
    (h : PermittedMove hJ m m' a b) (G : LabelState J N t → LabelState J N t → ℝ) :
    occupationWeight hJ β m * occupationRate hJ β m m' *
      moveAverage hJ m m' (fun e => G e.1.val e.2.val) =
        ∑ η : Fibre m, ∑ ζ : LabelState J N t,
          if profile ζ = m' then labelConductance hJ β η.val ζ * G η.val ζ else 0 := by
  rw [← move_conductance_sum]
  have hc : (Fintype.card (Fibre m) : ℝ) ≠ 0 := by exact_mod_cast (fibre_card_pos m).ne'
  have ha : (m.val a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h.2.1)
  rw [occupationWeight_eq, ← card_profile_fiber, occupationRate_of_move hJ hJ2 β h,
    moveAverage, move_card hJ hJ2 h, Nat.cast_mul]
  by_cases hd : qWeight hJ β m + qWeight hJ β m' = 0
  · simp only [hd, div_zero, mul_zero, zero_mul]
  · field_simp

theorem occupation_block_energy_le (hJ : 0 < J) (hJ2 : 2 ≤ J) (β : ℝ)
    (F : LabelState J N t → ℝ) (hF : ∀ η, 0 ≤ F η) (m m' : OccupationState J N t) :
    occupationWeight hJ β m * occupationRate hJ β m m' *
      (Real.sqrt (fibreAverage F m') - Real.sqrt (fibreAverage F m)) ^ 2 ≤
        ∑ η : Fibre m, ∑ ζ : LabelState J N t,
          if profile ζ = m' then labelConductance hJ β η.val ζ *
            (Real.sqrt (F ζ) - Real.sqrt (F η.val)) ^ 2 else 0 := by
  classical
  by_cases hm : ∃ a b, PermittedMove hJ m m' a b
  · obtain ⟨a, b, h⟩ := hm
    calc
      _ ≤ occupationWeight hJ β m * occupationRate hJ β m m' *
          moveAverage hJ m m' (fun e => (Real.sqrt (F e.2.val) -
            Real.sqrt (F e.1.val)) ^ 2) :=
        mul_le_mul_of_nonneg_left (move_sqrt_projection hJ hJ2 h F hF)
          (mul_nonneg ENNReal.toReal_nonneg (occupationRate_nonneg hJ β m m'))
      _ = _ := occupation_conductance_average hJ hJ2 β h
        (fun η ζ : LabelState J N t => (Real.sqrt (F ζ) - Real.sqrt (F η)) ^ 2)
  · rw [occupationRate_eq_zero hJ β hm, mul_zero, zero_mul]
    apply Finset.sum_nonneg
    intro η _
    apply Finset.sum_nonneg
    intro ζ _
    split_ifs
    · rw [← labelWeight_mul_rate]
      exact mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (labelRate_nonneg hJ β η.val ζ))
        (sq_nonneg _)
    · exact le_rfl

/-- Source exact square-root projection estimate, for the original outer
label and occupation forms. Every directed edge retains its original conductance. -/
theorem occupationEnergy_sqrt_fibreAverage_le (hJ : 0 < J) (hJ2 : 2 ≤ J) (β : ℝ)
    (F : LabelState J N t → ℝ) (hF : ∀ η, 0 ≤ F η) :
    occupationEnergy hJ β (fun m => Real.sqrt (fibreAverage F m)) ≤
      labelEnergy hJ β (fun η => Real.sqrt (F η)) := by
  classical
  rw [labelEnergy_eq_directed]
  unfold occupationEnergy FiniteGraph.energy
  simp only [labelWeight_mul_rate]
  rw [sum_by_fibres (fun η : LabelState J N t => ∑ ζ : LabelState J N t,
    labelConductance hJ β η ζ * (Real.sqrt (F ζ) - Real.sqrt (F η)) ^ 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro m _
  calc
    _ ≤ ∑ m' : OccupationState J N t, ∑ η : Fibre m, ∑ ζ : LabelState J N t,
        if profile ζ = m' then labelConductance hJ β η.val ζ *
          (Real.sqrt (F ζ) - Real.sqrt (F η.val)) ^ 2 else 0 :=
      Finset.sum_le_sum fun m' _ => occupation_block_energy_le hJ hJ2 β F hF m m'
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro η _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ζ _
      simp

end PeriodicAttractiveLogGas.FibreEntropy


