import LeanResearch.PeriodicAttractiveLogGas.MultisliceLogSobolev

/-! Actual finite couplings and ordinary entropy recurrences for the source
multislice LSI. The scalar input is frozen in MultisliceLogSobolev. The complete two-color theorem is proved by deletion induction below. The
full occupied-color multislice induction is a separate remaining obligation. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.MultisliceEntropyRecursion
open MeshCells LabelOccupations DiscreteOccupationIdentities FibreProjection
open MultislicePoincare MultisliceLogSobolev FibreEntropy
variable {J N : ℕ} {t : ℝ}

abbrev PivotFibre (m : OccupationState J N t) (i : Fin N) (a : MeshIndex J) :=
  CoordinateFibre (fun η : Fibre m => η.val.val i) a

/-- Arbitrary-color pivot/transposition pairs. There is no spatial adjacency
restriction on the colors or on the selected particle index. -/
abbrev PivotCoupling (m : OccupationState J N t) (i : Fin N) (a b : MeshIndex J) :=
  {e : Fibre m × Fin N // e.1.val.val i = a ∧ e.1.val.val e.2 = b}

def pivotSigmaEquiv (m : OccupationState J N t) (i : Fin N) (a b : MeshIndex J) :
    PivotCoupling m i a b ≃
      (Σ η : PivotFibre m i a, {j : Fin N // η.val.val.val j = b}) where
  toFun e := ⟨⟨e.val.1, e.property.1⟩, ⟨e.val.2, e.property.2⟩⟩
  invFun e := ⟨(e.1.val, e.2.val), e.1.property, e.2.property⟩
  left_inv e := by cases e; rfl
  right_inv e := by rcases e with ⟨⟨η, ha⟩, ⟨j, hb⟩⟩; rfl

@[simp] theorem fibrePermutation_swap_twice (m : OccupationState J N t)
    (i j : Fin N) (η : Fibre m) :
    fibrePermutation (Equiv.swap i j) m (fibrePermutation (Equiv.swap i j) m η) = η := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  simp only [fibrePermutation_apply_coordinate, Equiv.swap_apply_self]

/-- Reversal is a literal bijection of the two finite pivot couplings. -/
def pivotReverse (m : OccupationState J N t) (i : Fin N) (a b : MeshIndex J) :
    PivotCoupling m i a b ≃ PivotCoupling m i b a where
  toFun e := ⟨(fibrePermutation (Equiv.swap i e.val.2) m e.val.1, e.val.2), by
    constructor
    · simpa only [fibrePermutation_apply_coordinate, Equiv.swap_apply_left] using e.property.2
    · simpa only [fibrePermutation_apply_coordinate, Equiv.swap_apply_right] using e.property.1⟩
  invFun e := ⟨(fibrePermutation (Equiv.swap i e.val.2) m e.val.1, e.val.2), by
    constructor
    · simpa only [fibrePermutation_apply_coordinate, Equiv.swap_apply_left] using e.property.2
    · simpa only [fibrePermutation_apply_coordinate, Equiv.swap_apply_right] using e.property.1⟩
  left_inv e := by
    apply Subtype.ext
    apply Prod.ext
    · exact fibrePermutation_swap_twice m i e.val.2 e.val.1
    · rfl
  right_inv e := by
    apply Subtype.ext
    apply Prod.ext
    · exact fibrePermutation_swap_twice m i e.val.2 e.val.1
    · rfl

/-- The number of available partners is the original literal occupation. -/
theorem partner_card (m : OccupationState J N t) (η : Fibre m) (b : MeshIndex J) :
    Fintype.card {j : Fin N // η.val.val j = b} = m.val b := by
  classical
  have hh := congrFun (congrArg Subtype.val η.property) b
  simpa only [profile, occupation, Fintype.card_subtype] using hh

theorem pivot_card_pos (m : OccupationState J N t) (i : Fin N) (a : MeshIndex J)
    (ha : 0 < m.val a) : 0 < Fintype.card (PivotFibre m i a) := by
  classical
  let ξ : Fibre m := ⟨labelOfState m, profile_labelOfState m⟩
  have hc : 0 < occupation ξ.val.val a := by
    have he := congrFun (congrArg Subtype.val ξ.property) a
    change occupation ξ.val.val a = m.val a at he
    rw [he]
    exact ha
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hc
  have hj' : ξ.val.val j = a := (Finset.mem_filter.mp hj).2
  let : Nonempty (PivotFibre m i a) := ⟨⟨fibrePermutation (Equiv.swap i j) m ξ, by
    simpa only [fibrePermutation_apply_coordinate, Equiv.swap_apply_left] using hj'⟩⟩
  exact Fintype.card_pos

theorem pivotCoupling_card (m : OccupationState J N t) (i : Fin N) (a b : MeshIndex J) :
    Fintype.card (PivotCoupling m i a b) = Fintype.card (PivotFibre m i a)*m.val b := by
  classical
  rw [Fintype.card_congr (pivotSigmaEquiv m i a b), Fintype.card_sigma]
  simp only [partner_card, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- First uniform marginal, obtained from the exact constant partner count. -/
theorem pivotAverage_left (m : OccupationState J N t) (i : Fin N) (a b : MeshIndex J)
    (ha : 0 < m.val a) (hb : 0 < m.val b) (f : Fibre m → ℝ) :
    uniformAverage (fun e : PivotCoupling m i a b => f e.val.1) =
      coordinateProjection m f i a := by
  classical
  have hk : (m.val b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hc : (Fintype.card (PivotFibre m i a) : ℝ) ≠ 0 :=
    by exact_mod_cast (pivot_card_pos m i a ha).ne'
  have hs := Equiv.sum_comp (pivotSigmaEquiv m i a b)
    (fun e => f e.1.val)
  change (∑ e : PivotCoupling m i a b, f e.val.1) = _ at hs
  rw [Fintype.sum_sigma] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, partner_card,
    ← Finset.mul_sum] at hs
  unfold coordinateProjection conditionalAverage uniformAverage
  rw [hs, pivotCoupling_card, Nat.cast_mul]
  field_simp

/-- The second uniform marginal is derived by reversing the actual coupling. -/
theorem pivotAverage_right (m : OccupationState J N t) (i : Fin N) (a b : MeshIndex J)
    (ha : 0 < m.val a) (hb : 0 < m.val b) (f : Fibre m → ℝ) :
    uniformAverage (fun e : PivotCoupling m i a b =>
      f (fibrePermutation (Equiv.swap i e.val.2) m e.val.1)) =
      coordinateProjection m f i b := by
  have hh := uniformAverage_equiv (pivotReverse m i a b)
    (fun e : PivotCoupling m i b a => f e.val.1)
  change uniformAverage (fun e : PivotCoupling m i a b =>
    f (fibrePermutation (Equiv.swap i e.val.2) m e.val.1)) = _ at hh
  rw [hh]
  exact pivotAverage_left m i b a hb ha f

/-- Actual reverse-L2 comparison for the two conditional means, including
zero means and repeated colors. Both marginal identities are proved above. -/
theorem pivot_reverse_sqrt (m : OccupationState J N t) (i : Fin N) (a b : MeshIndex J)
    (ha : 0 < m.val a) (hb : 0 < m.val b) (f : Fibre m → ℝ) (hf : ∀ η, 0 ≤ f η) :
    (Real.sqrt (coordinateProjection m f i a)-Real.sqrt (coordinateProjection m f i b))^2 ≤
      uniformAverage (fun e : PivotCoupling m i a b =>
        (Real.sqrt (f e.val.1)-Real.sqrt (f (fibrePermutation (Equiv.swap i e.val.2) m e.val.1)))^2) := by
  have hh := reverse_sqrt_uniform (fun e : PivotCoupling m i a b => f e.val.1)
    (fun e => f (fibrePermutation (Equiv.swap i e.val.2) m e.val.1))
    (fun e => hf e.val.1) (fun e => hf _)
  rw [pivotAverage_left m i a b ha hb, pivotAverage_right m i a b ha hb] at hh
  exact hh


/-- Uniform entropy is transported by a genuine finite equivalence. -/
theorem uniformEntropy_equiv {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (e : Ω ≃ Λ) (f : Λ → ℝ) : uniformEntropy (fun x => f (e x)) = uniformEntropy f := by
  unfold uniformEntropy
  rw [uniformAverage_equiv e (fun x => f x*Real.log (f x)), uniformAverage_equiv e f]

/-- The coupling normalization is converted into the actual conditional sum
of partner contributions, with no degree conclusion as a premise. -/
theorem pivotAverage_sum (m : OccupationState J N t) (i : Fin N) (a b : MeshIndex J)
    (ha : 0 < m.val a) (hb : 0 < m.val b) (g : Fin N → Fibre m → ℝ) :
    (m.val b : ℝ)*uniformAverage (fun e : PivotCoupling m i a b => g e.val.2 e.val.1) =
      coordinateProjection m (fun η => ∑ j, if η.val.val j = b then g j η else 0) i a := by
  classical
  have hk : (m.val b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hc : (Fintype.card (PivotFibre m i a) : ℝ) ≠ 0 :=
    by exact_mod_cast (pivot_card_pos m i a ha).ne'
  have hs := Equiv.sum_comp (pivotSigmaEquiv m i a b)
    (fun e => g e.2.val e.1.val)
  change (∑ e : PivotCoupling m i a b, g e.val.2 e.val.1) = _ at hs
  rw [Fintype.sum_sigma] at hs
  have hsub (η : PivotFibre m i a) :
      (∑ j : {j : Fin N // η.val.val.val j = b}, g j.val η.val) =
        ∑ j : Fin N, if η.val.val.val j = b then g j η.val else 0 := by
    have hh := Finset.sum_subtype (p := fun j : Fin N => η.val.val.val j = b) (F := inferInstance)
      (Finset.univ.filter (fun j : Fin N => η.val.val.val j = b))
      (by intro j; simp) (fun j : Fin N => g j η.val)
    simpa only [Finset.sum_filter] using hh.symm
  simp_rw [hsub] at hs
  unfold coordinateProjection conditionalAverage uniformAverage
  rw [hs, pivotCoupling_card, Nat.cast_mul]
  field_simp

/-- A literal coordinate indicator selects the actual conditional law. -/
theorem average_pivot_indicator (m : OccupationState J N t) (i : Fin N)
    (a : MeshIndex J) (g : Fibre m → ℝ) :
    uniformAverage (fun η => if η.val.val i = a then g η else 0) =
      ((m.val a : ℝ)/N)*coordinateProjection m g i a := by
  classical
  have hh := average_mul_coordinate (fun η : Fibre m => η.val.val i) g
    (fun c : MeshIndex J => if c = a then (1 : ℝ) else 0)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq'] at hh
  rw [coordinate_marginal] at hh
  simpa only [Finset.mem_univ, ite_true, coordinateProjection] using hh

/-- Exact weighted coupling identity before any entropy inequality is used. -/
theorem pivot_mass_sum (m : OccupationState J N t) (i : Fin N) (a b : MeshIndex J)
    (ha : 0 < m.val a) (hb : 0 < m.val b) (g : Fin N → Fibre m → ℝ) :
    ((m.val a : ℝ)/N)*(m.val b : ℝ)*
        uniformAverage (fun e : PivotCoupling m i a b => g e.val.2 e.val.1) =
      uniformAverage (fun η => if η.val.val i = a then
        ∑ j, if η.val.val j = b then g j η else 0 else 0) := by
  rw [average_pivot_indicator, ← pivotAverage_sum m i a b ha hb g]
  ring

/-- Colors outside the two specified occupied labels contribute exactly zero. -/
theorem two_colour_sum (m : OccupationState J N t) (a b : MeshIndex J) (hab : a ≠ b)
    (honly : ∀ c, 0 < m.val c → c = a ∨ c = b) (g : MeshIndex J → ℝ) :
    (∑ c, (m.val c : ℝ)*g c) = (m.val a : ℝ)*g a+(m.val b : ℝ)*g b := by
  classical
  have he (c : MeshIndex J) : (m.val c : ℝ)*g c =
      (if c = a then (m.val a : ℝ)*g a else 0)+
        (if c = b then (m.val b : ℝ)*g b else 0) := by
    by_cases hca : c = a
    · subst c; simp only [ite_eq_left, ite_eq_right hab, add_zero]
    by_cases hcb : c = b
    · subst c; simp only [ite_eq_right (Ne.symm hab), ite_eq_left, zero_add]
    have hz : m.val c = 0 := by
      by_contra hn
      exact (honly c (Nat.pos_of_ne_zero hn)).elim hca hcb
    simp only [hz, Nat.cast_zero, zero_mul, ite_eq_right hca, ite_eq_right hcb, add_zero]
  calc
    _ = ∑ c, ((if c = a then (m.val a : ℝ)*g a else 0)+
        (if c = b then (m.val b : ℝ)*g b else 0)) :=
      Finset.sum_congr rfl fun c _ => he c
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem two_colour_total (m : OccupationState J N t) (a b : MeshIndex J) (hab : a ≠ b)
    (honly : ∀ c, 0 < m.val c → c = a ∨ c = b) : m.val a+m.val b = N := by
  have hh := two_colour_sum m a b hab honly (fun _ => 1)
  have hs : (∑ c, (m.val c : ℝ)) = N := by exact_mod_cast m.property.1
  simp only [mul_one] at hh
  exact_mod_cast hh.symm.trans hs

/-- The finite marginal entropy is precisely the two-point ordinary entropy. -/
theorem two_colour_projection_entropy (m : OccupationState J N t) (i : Fin N)
    (a b : MeshIndex J) (hab : a ≠ b)
    (honly : ∀ c, 0 < m.val c → c = a ∨ c = b) (f : Fibre m → ℝ) :
    finiteEntropy (marginalWeight (fun η : Fibre m => η.val.val i))
      (coordinateProjection m f i) =
      let p : ℝ := m.val a/N
      let A := coordinateProjection m f i a
      let B := coordinateProjection m f i b
      p*A*Real.log A+(1-p)*B*Real.log B-
        (p*A+(1-p)*B)*Real.log (p*A+(1-p)*B) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt).ne'
  have hs : (m.val a : ℝ)+(m.val b : ℝ) = N :=
    by exact_mod_cast two_colour_total m a b hab honly
  have hb : (m.val b : ℝ)/N = 1-(m.val a : ℝ)/N := by field_simp; linarith only [hs]
  have hsum (g : MeshIndex J → ℝ) :
      (∑ c, ((m.val c : ℝ)/N)*g c) =
        ((m.val a : ℝ)/N)*g a+((m.val b : ℝ)/N)*g b := by
    simp only [div_mul_eq_mul_div, ← Finset.sum_div]
    rw [two_colour_sum m a b hab honly g, add_div]
  unfold finiteEntropy
  simp_rw [coordinate_marginal]
  rw [hsum, hsum, hb]
  ring


/-- The scalar two-point theorem is applied to actual conditional means,
and its square-root difference is bounded by the actual pivot coupling. -/
theorem two_colour_projection_bound (m : OccupationState J N t) (i : Fin N)
    (a b : MeshIndex J) (hab : a ≠ b) (ha : 0 < m.val a) (hb : 0 < m.val b)
    (honly : ∀ c, 0 < m.val c → c = a ∨ c = b) (f : Fibre m → ℝ) (hf : ∀ η, 0 ≤ f η) :
    finiteEntropy (marginalWeight (fun η : Fibre m => η.val.val i))
      (coordinateProjection m f i) ≤
      -(((m.val a : ℝ)/N)*(1-(m.val a : ℝ)/N))*
        Real.log (((m.val a : ℝ)/N)*(1-(m.val a : ℝ)/N))/Real.log 2*
        uniformAverage (fun e : PivotCoupling m i a b =>
          (Real.sqrt (f e.val.1)-Real.sqrt (f (fibrePermutation (Equiv.swap i e.val.2) m e.val.1)))^2) := by
  let p : ℝ := m.val a/N
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have ha' : (0 : ℝ) < m.val a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < m.val b := by exact_mod_cast hb
  have hs : (m.val a : ℝ)+(m.val b : ℝ) = N :=
    by exact_mod_cast two_colour_total m a b hab honly
  have hp : 0 < p := div_pos ha' hn
  have hp1 : p < 1 := (div_lt_one hn).mpr (by linarith only [hs, hb'])
  have hA : 0 ≤ coordinateProjection m f i a := uniformAverage_nonneg fun η => hf η.val
  have hB : 0 ≤ coordinateProjection m f i b := uniformAverage_nonneg fun η => hf η.val
  have hh := twoPoint_entropy_le hp.le hp1.le hA hB
  rw [two_colour_projection_entropy m i a b hab honly]
  dsimp only
  apply hh.trans
  have hpq : 0 < p*(1-p) := mul_pos hp (by linarith)
  have hlog : Real.log (p*(1-p)) ≤ 0 := by
    have hl := Real.log_le_sub_one_of_pos hpq
    nlinarith only [hl, sq_nonneg (p-1/2)]
  have hC : 0 ≤ -(p*(1-p))*Real.log (p*(1-p))/Real.log 2 :=
    div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith) hlog)
      (Real.log_pos (by norm_num)).le
  exact mul_le_mul_of_nonneg_left (pivot_reverse_sqrt m i a b ha hb f hf) hC

theorem fibre_two_colours (m : OccupationState J N t) (a b : MeshIndex J)
    (honly : ∀ c, 0 < m.val c → c = a ∨ c = b) (η : Fibre m) (i : Fin N) :
    η.val.val i = a ∨ η.val.val i = b := by
  have hh := occupation_pos_at η.val.val i
  have he := congrArg Subtype.val η.property
  change occupation η.val.val = m.val at he
  rw [he] at hh
  exact honly _ hh

theorem fibrePermutation_swap_of_equal (m : OccupationState J N t)
    (i j : Fin N) (η : Fibre m) (he : η.val.val i = η.val.val j) :
    fibrePermutation (Equiv.swap i j) m η = η := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  exact Equiv.apply_swap_eq_self he k

/-- An actual two-color edge is counted once in each orientation. Same-color
swaps vanish as functions, including the diagonal. -/
theorem two_colour_directional_sum (m : OccupationState J N t) (a b : MeshIndex J)
    (hab : a ≠ b) (honly : ∀ c, 0 < m.val c → c = a ∨ c = b) (g : Fibre m → ℝ) :
    2*(∑ i : Fin N, uniformAverage (fun η : Fibre m =>
      if η.val.val i = a then ∑ j : Fin N, if η.val.val j = b then
        (g (fibrePermutation (Equiv.swap i j) m η)-g η)^2 else 0 else 0)) =
      orderedSwapSum m g := by
  classical
  let E : Fin N → Fin N → Fibre m → ℝ := fun i j η =>
    (g (fibrePermutation (Equiv.swap i j) m η)-g η)^2
  let C : Fin N → Fin N → Fibre m → ℝ := fun i j η =>
    if η.val.val i = a then if η.val.val j = b then E i j η else 0 else 0
  have hEs (i j : Fin N) (η : Fibre m) : E i j η = E j i η := by
    dsimp only [E]
    rw [Equiv.swap_comm i j]
  have he (i j : Fin N) (η : Fibre m) : E i j η = C i j η+C j i η := by
    rcases fibre_two_colours m a b honly η i with hi | hi <;>
      rcases fibre_two_colours m a b honly η j with hj | hj
    · have hz := fibrePermutation_swap_of_equal m i j η (hi.trans hj.symm)
      simp only [C, E, hz, sub_self, zero_pow (by decide : 2 ≠ 0),
        hi, hj, ite_eq_left, ite_eq_right hab, add_zero]
    · simp only [C, hi, hj, ite_eq_left, ite_eq_right (Ne.symm hab), add_zero]
    · simp only [C, hi, hj, ite_eq_left, ite_eq_right (Ne.symm hab), zero_add]
      exact hEs i j η
    · have hz := fibrePermutation_swap_of_equal m i j η (hi.trans hj.symm)
      simp only [C, E, hz, sub_self, zero_pow (by decide : 2 ≠ 0),
        hi, hj, ite_eq_right (Ne.symm hab), add_zero]
  have hc (i : Fin N) (η : Fibre m) :
      (if η.val.val i = a then ∑ j : Fin N, if η.val.val j = b then E i j η else 0 else 0) =
        ∑ j : Fin N, C i j η := by
    by_cases hi : η.val.val i = a <;> simp only [C, hi, ite_true, ite_false, Finset.sum_const_zero]
  change 2*(∑ i, uniformAverage (fun η =>
    if η.val.val i = a then ∑ j, if η.val.val j = b then E i j η else 0 else 0)) =
      ∑ i, ∑ j, uniformAverage (E i j)
  simp_rw [hc, uniformAverage_sum]
  have hav (i j : Fin N) : uniformAverage (E i j) =
      uniformAverage (C i j)+uniformAverage (C j i) := by
    rw [← uniformAverage_add]
    exact congrArg uniformAverage (funext fun η => he i j η)
  simp_rw [hav, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => uniformAverage (C j i))]
  ring


/-- Exact sum of the pivot coupling energies, in the original ordered
transposition normalization. All degrees and orientations are accounted for. -/
theorem sum_pivot_energy (m : OccupationState J N t) (a b : MeshIndex J)
    (hab : a ≠ b) (ha : 0 < m.val a) (hb : 0 < m.val b)
    (honly : ∀ c, 0 < m.val c → c = a ∨ c = b) (g : Fibre m → ℝ) :
    2*(((m.val a : ℝ)/N)*(m.val b : ℝ))*(∑ i : Fin N,
      uniformAverage (fun e : PivotCoupling m i a b =>
        (g e.val.1-g (fibrePermutation (Equiv.swap i e.val.2) m e.val.1))^2)) =
      orderedSwapSum m g := by
  classical
  have hi (i : Fin N) : ((m.val a : ℝ)/N)*(m.val b : ℝ)*
      uniformAverage (fun e : PivotCoupling m i a b =>
        (g e.val.1-g (fibrePermutation (Equiv.swap i e.val.2) m e.val.1))^2) =
      uniformAverage (fun η : Fibre m => if η.val.val i = a then
        ∑ j : Fin N, if η.val.val j = b then
          (g (fibrePermutation (Equiv.swap i j) m η)-g η)^2 else 0 else 0) := by
    rw [pivot_mass_sum m i a b ha hb
      (fun j η => (g η-g (fibrePermutation (Equiv.swap i j) m η))^2)]
    apply congrArg uniformAverage
    funext η
    split_ifs with hi
    · apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    · rfl
  have hh := Finset.sum_congr rfl fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => hi i
  rw [← Finset.mul_sum] at hh
  have hd := two_colour_directional_sum m a b hab honly g
  rw [← hh] at hd
  simpa only [mul_assoc] using hd

/-- The total projected-entropy contribution with the exact Lee--Yau
coefficient and the actual original-fibre transposition energy. -/
theorem sum_projection_entropy_le (m : OccupationState J N t) (a b : MeshIndex J)
    (hab : a ≠ b) (ha : 0 < m.val a) (hb : 0 < m.val b)
    (honly : ∀ c, 0 < m.val c → c = a ∨ c = b) (f : Fibre m → ℝ) (hf : ∀ η, 0 ≤ f η) :
    (∑ i : Fin N, finiteEntropy (marginalWeight (fun η : Fibre m => η.val.val i))
      (coordinateProjection m f i)) ≤
      -Real.log (((m.val a : ℝ)/N)*((m.val b : ℝ)/N))/(2*(N : ℝ)*Real.log 2)*
        orderedSwapSum m (fun η => Real.sqrt (f η)) := by
  have hs : (m.val a : ℝ)+(m.val b : ℝ) = N :=
    by exact_mod_cast two_colour_total m a b hab honly
  have ha' : (0 : ℝ) < m.val a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < m.val b := by exact_mod_cast hb
  have hn : (0 : ℝ) < N := by linarith only [hs, ha', hb']
  have hq : (m.val b : ℝ)/N = 1-(m.val a : ℝ)/N := by field_simp; linarith only [hs]
  have hh := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
    two_colour_projection_bound m i a b hab ha hb honly f hf
  rw [← Finset.mul_sum] at hh
  rw [← hq] at hh
  have he := sum_pivot_energy m a b hab ha hb honly (fun η => Real.sqrt (f η))
  apply hh.trans_eq
  rw [← he]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp [hn.ne', hlog]

/-- Entropy, not merely expectation, is transported to the true deleted
occupation fibre by the already proved insertion/deletion equivalence. -/
theorem conditionalEntropy_deletion {n : ℕ} {m : OccupationState J (n+1) t}
    (ξ : Fibre m) (i : Fin (n+1)) (f : Fibre m → ℝ) :
    uniformEntropy (fun η : PivotFibre m i (ξ.val.val i) => f η.val) =
      uniformEntropy (fun ζ : Fibre (deletedProfile ξ i) => f (insertedFibre ξ i ζ)) := by
  have hh := uniformEntropy_equiv (deletionEquiv ξ i).symm
    (fun η : PivotFibre m i (ξ.val.val i) => f η.val)
  exact hh.symm

/-- Exact entropy chain with the actual smaller occupation law at every
observed conditioning color. Empty unobserved colors do not create premises. -/
theorem deletion_entropy_chain {n : ℕ} (m : OccupationState J (n+1) t) (f : Fibre m → ℝ)
    (i : Fin (n+1)) :
    uniformEntropy f =
      uniformAverage (fun ξ : Fibre m => uniformEntropy
        (fun ζ : Fibre (deletedProfile ξ i) => f (insertedFibre ξ i ζ))) +
      finiteEntropy (marginalWeight (fun η : Fibre m => η.val.val i)) (coordinateProjection m f i) := by
  let H : MeshIndex J → ℝ := fun a => uniformEntropy (fun η : PivotFibre m i a => f η.val)
  have hh := coordinate_entropy_chain (fun η : Fibre m => η.val.val i) f
  have hm := coordinate_average m H i
  unfold colourAverage at hm
  rw [Finset.sum_div] at hm
  have hc : (∑ a, marginalWeight (fun η : Fibre m => η.val.val i) a*H a) =
      uniformAverage (fun ξ : Fibre m => H (ξ.val.val i)) := by
    rw [hm]
    apply Finset.sum_congr rfl
    intro a _
    rw [coordinate_marginal]
    ring
  change uniformEntropy f = (∑ a, marginalWeight (fun η : Fibre m => η.val.val i) a*H a)+_ at hh
  rw [hc] at hh
  have hd : (fun ξ : Fibre m => H (ξ.val.val i)) =
      (fun ξ : Fibre m => uniformEntropy
        (fun ζ : Fibre (deletedProfile ξ i) => f (insertedFibre ξ i ζ))) :=
    funext fun ξ => conditionalEntropy_deletion ξ i f
  rw [hd] at hh
  exact hh

/-- Weighted deletion count. Each retained ordered pair excludes exactly
its two endpoint pivots; the diagonal is zero, including the one-site case. -/
theorem weighted_sum_deleted_pairs {n : ℕ} (w : Fin (n+1) → ℝ)
    (E : Fin (n+1) → Fin (n+1) → ℝ) (hdiag : ∀ i, E i i = 0) :
    (∑ i : Fin (n+1), w i * ∑ j : Fin n, ∑ k : Fin n,
      E (i.succAbove j) (i.succAbove k)) =
      ∑ j : Fin (n+1), ∑ k : Fin (n+1),
        ((∑ i : Fin (n+1), w i)-w j-w k)*E j k := by
  have hp (i : Fin (n+1)) :
      (∑ j : Fin n, ∑ k : Fin n, E (i.succAbove j) (i.succAbove k)) =
      (∑ j : Fin (n+1), ∑ k : Fin (n+1), E j k) -
        (∑ k : Fin (n+1), E i k) - (∑ j : Fin (n+1), E j i) := by
    have ho := Fin.sum_univ_succAbove (fun j => ∑ k : Fin (n+1), E j k) i
    have hc := Fin.sum_univ_succAbove (fun j => E j i) i
    have hi (j : Fin n) := Fin.sum_univ_succAbove (fun k => E (i.succAbove j) k) i
    simp_rw [hi] at ho
    rw [Finset.sum_add_distrib] at ho
    rw [hdiag i, zero_add] at hc
    linarith only [ho, hc]
  simp_rw [hp, mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i j => ∑ k : Fin (n+1), w i*E j k)]
  simp_rw [Finset.sum_comm (f := fun i k => w i*E _ k), ← Finset.sum_mul]
  rw [Finset.sum_comm (f := fun i j => w i*E j i)]

/-- Actual two-color weighted retained-edge count. The coefficient is the
number of possible deleted pivots of each color after excluding both endpoints. -/
theorem two_colour_weighted_deleted_pairs {n : ℕ}
    (m : OccupationState J (n+1) t) (a b : MeshIndex J) (hab : a ≠ b)
    (honly : ∀ c, 0 < m.val c → c = a ∨ c = b)
    (A B : ℝ) (g : Fibre m → ℝ) (η : Fibre m) :
    (∑ i : Fin (n+1), (if η.val.val i = a then A else B) *
      ∑ j : Fin n, ∑ k : Fin n,
        (g (fibrePermutation (Equiv.swap (i.succAbove j) (i.succAbove k)) m η)-g η)^2) =
      (((m.val a : ℝ)-1)*A+((m.val b : ℝ)-1)*B) *
        ∑ j : Fin (n+1), ∑ k : Fin (n+1),
          (g (fibrePermutation (Equiv.swap j k) m η)-g η)^2 := by
  classical
  have hw : (∑ i : Fin (n+1), if η.val.val i = a then A else B) =
      (m.val a : ℝ)*A+(m.val b : ℝ)*B := by
    have hh := occupation_sum η.val.val (fun c => if c = a then A else B)
    have hm : occupation η.val.val = m.val := congrArg Subtype.val η.property
    rw [hm] at hh
    rw [two_colour_sum m a b hab honly] at hh
    simpa only [ite_true, ite_eq_left, Ne.symm hab, ite_false] using hh
  have hd (i : Fin (n+1)) :
      (g (fibrePermutation (Equiv.swap i i) m η)-g η)^2 = 0 := by
    simp only [Equiv.swap_self, fibrePermutation_refl, sub_self,
      zero_pow (by decide : 2 ≠ 0)]
  rw [weighted_sum_deleted_pairs (fun i => if η.val.val i = a then A else B)
    (fun j k => (g (fibrePermutation (Equiv.swap j k) m η)-g η)^2) hd,
    hw, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rcases fibre_two_colours m a b honly η j with hj | hj <;>
    rcases fibre_two_colours m a b honly η k with hk | hk
  · rw [fibrePermutation_swap_of_equal m j k η (hj.trans hk.symm)]
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero]
  · simp only [hj, hk, ite_eq_left, Ne.symm hab, ite_false]
    ring
  · simp only [hj, hk, ite_eq_left, Ne.symm hab, ite_false]
    ring
  · rw [fibrePermutation_swap_of_equal m j k η (hj.trans hk.symm)]
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero]

/-- A color-dependent coefficient is constant on the actual conditioning
fibre. Insertion, not an assumed conditional-law identity, transports the energy. -/
theorem weighted_deleted_energy_pivot {n : ℕ}
    (m : OccupationState J (n+1) t) (W : MeshIndex J → ℝ)
    (g : Fibre m → ℝ) (i : Fin (n+1)) :
    uniformAverage (fun ξ : Fibre m => W (ξ.val.val i) *
      orderedSwapSum (deletedProfile ξ i) (fun ζ => g (insertedFibre ξ i ζ))) =
      uniformAverage (fun η : Fibre m => W (η.val.val i) *
        ∑ j : Fin n, ∑ k : Fin n,
          (g (fibrePermutation (Equiv.swap (i.succAbove j) (i.succAbove k)) m η)-g η)^2) := by
  let H : Fibre m → ℝ := fun η => W (η.val.val i) *
    ∑ j : Fin n, ∑ k : Fin n,
      (g (fibrePermutation (Equiv.swap (i.succAbove j) (i.succAbove k)) m η)-g η)^2
  have hp (ξ : Fibre m) : W (ξ.val.val i) *
      orderedSwapSum (deletedProfile ξ i) (fun ζ => g (insertedFibre ξ i ζ)) =
      coordinateProjection m H i (ξ.val.val i) := by
    unfold coordinateProjection
    rw [conditionalAverage_deletion ξ i H]
    unfold orderedSwapSum
    simp_rw [← uniformAverage_sum]
    rw [← uniformAverage_mul]
    apply congrArg uniformAverage
    funext ζ
    have hi : (insertedFibre ξ i ζ).val.val i = ξ.val.val i :=
      Fin.insertNth_apply_same (α := fun _ => MeshIndex J) i _ _
    dsimp only [H]
    rw [hi]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [insertedFibre_swap]
  simp_rw [hp]
  exact coordinateProjection_tower m H i

/-- Averaging the actual weighted deletion count gives the exact two-color
coefficient in the Lee--Yau entropy recurrence. -/
theorem two_colour_deleted_energy {n : ℕ}
    (m : OccupationState J (n+1) t) (a b : MeshIndex J) (hab : a ≠ b)
    (honly : ∀ c, 0 < m.val c → c = a ∨ c = b)
    (A B : ℝ) (g : Fibre m → ℝ) :
    (∑ i : Fin (n+1), uniformAverage (fun ξ : Fibre m =>
      (if ξ.val.val i = a then A else B) *
        orderedSwapSum (deletedProfile ξ i) (fun ζ => g (insertedFibre ξ i ζ)))) =
      (((m.val a : ℝ)-1)*A+((m.val b : ℝ)-1)*B)*orderedSwapSum m g := by
  classical
  simp_rw [weighted_deleted_energy_pivot m (fun c => if c = a then A else B) g]
  rw [← uniformAverage_sum]
  simp_rw [two_colour_weighted_deleted_pairs m a b hab honly A B g]
  rw [uniformAverage_mul]
  simp_rw [uniformAverage_sum]
  rfl

/-- Genuine two-color entropy recurrence. Its only inductive input is the
ordinary entropy bound on the literal smaller occupation fibres; the coupling,
uniform conditional laws, retained-edge counts and projected entropy are proved. -/
theorem two_colour_entropy_step {n : ℕ} (hn : 1 ≤ n)
    (m : OccupationState J (n+1) t) (a b : MeshIndex J)
    (hab : a ≠ b) (ha : 0 < m.val a) (hb : 0 < m.val b)
    (honly : ∀ c, 0 < m.val c → c = a ∨ c = b)
    (A B : ℝ) (f : Fibre m → ℝ) (hf : ∀ η, 0 ≤ f η)
    (ih : ∀ (i : Fin (n+1)) (ξ : Fibre m),
      4*(n : ℝ)*uniformEntropy (fun ζ : Fibre (deletedProfile ξ i) => f (insertedFibre ξ i ζ)) ≤
        (if ξ.val.val i = a then A else B)*orderedSwapSum (deletedProfile ξ i)
          (fun ζ => Real.sqrt (f (insertedFibre ξ i ζ)))) :
    4*((n+1 : ℕ) : ℝ)*uniformEntropy f ≤
      ((((m.val a : ℝ)-1)*A+((m.val b : ℝ)-1)*B)/(n : ℝ) -
        2*Real.log (((m.val a : ℝ)/(n+1))*((m.val b : ℝ)/(n+1)))/
          (((n+1 : ℕ) : ℝ)*Real.log 2))*orderedSwapSum m (fun η => Real.sqrt (f η)) := by
  classical
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnN : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hi := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin (n+1)))) =>
    uniformAverage_mono (ih i)
  simp_rw [uniformAverage_mul] at hi
  rw [← Finset.mul_sum, two_colour_deleted_energy m a b hab honly A B (fun η => Real.sqrt (f η))] at hi
  have hc := Finset.sum_congr rfl fun i (_ : i ∈ (Finset.univ : Finset (Fin (n+1)))) =>
    deletion_entropy_chain m f i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_add_distrib] at hc
  have hp := sum_projection_entropy_le m a b hab ha hb honly f hf
  simp only [Nat.cast_add, Nat.cast_one] at hp
  have hh := add_le_add hi (mul_le_mul_of_nonneg_left hp (show 0 ≤ 4*(n : ℝ) by positivity))
  have heq : (n : ℝ)*
      (((((m.val a : ℝ)-1)*A+((m.val b : ℝ)-1)*B)/(n : ℝ) -
        2*Real.log (((m.val a : ℝ)/(n+1))*((m.val b : ℝ)/(n+1)))/
          (((n+1 : ℕ) : ℝ)*Real.log 2))*orderedSwapSum m (fun η => Real.sqrt (f η))) =
      (((m.val a : ℝ)-1)*A+((m.val b : ℝ)-1)*B)*orderedSwapSum m (fun η => Real.sqrt (f η)) +
        (4*(n : ℝ))*(-Real.log (((m.val a : ℝ)/(n+1))*((m.val b : ℝ)/(n+1)))/
          (2*((n+1 : ℕ) : ℝ)*Real.log 2)*orderedSwapSum m (fun η => Real.sqrt (f η))) := by
    field_simp [hnr.ne', hnN.ne', hlog]
    ring
  have hmul : (n : ℝ)*(4*((n+1 : ℕ) : ℝ)*uniformEntropy f) ≤
      (n : ℝ)*
        (((((m.val a : ℝ)-1)*A+((m.val b : ℝ)-1)*B)/(n : ℝ) -
          2*Real.log (((m.val a : ℝ)/(n+1))*((m.val b : ℝ)/(n+1)))/
            (((n+1 : ℕ) : ℝ)*Real.log 2))*orderedSwapSum m (fun η => Real.sqrt (f η))) := by
    rw [heq]
    have hcc := congrArg (fun x : ℝ => 4*(n : ℝ)*x) hc
    simp only [Nat.cast_add, Nat.cast_one] at hh hcc ⊢
    nlinarith only [hh, hcc]
  nlinarith only [hmul, hnr]

/-- The logarithm tangent inequality at an arbitrary positive point. -/
theorem log_tangent_relative {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log x ≤ Real.log y+x/y-1 := by
  have hh := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div hx.ne' hy.ne'] at hh
  linarith only [hh]

/-- The binary logarithmic factor is at least one, with no numerical
approximation to log 2. -/
theorem one_le_log_binary_ratio {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    1 ≤ Real.log ((r+s)^2/(r*s)) := by
  have hratio : (4 : ℝ) ≤ (r+s)^2/(r*s) := by
    apply (le_div_iff₀ (mul_pos hr hs)).mpr
    nlinarith only [sq_nonneg (r-s)]
  have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1/2)
  have he : Real.log ((1 : ℝ)/2) = -Real.log 2 := by rw [one_div, Real.log_inv]
  rw [he] at hh
  have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hratio
  have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  rw [h4] at hm
  linarith only [hh, hm]

/-- Exact interior recurrence comparison. Applying the logarithm tangent
bound to the two smaller-fibre arguments leaves a weighted error exactly 1/N.
This is an elementary form of the Lee--Yau Jensen calculation. -/
theorem binary_log_recurrence_interior {r s : ℝ} (hr : 1 < r) (hs : 1 < s) :
    ((r-1)*Real.log ((r+s-1)^2/((r-1)*s))+
      (s-1)*Real.log ((r+s-1)^2/(r*(s-1))))/(r+s-1) +
      Real.log ((r+s)^2/(r*s))/(r+s) ≤ Real.log ((r+s)^2/(r*s)) := by
  have hr0 : 0 < r := by linarith
  have hs0 : 0 < s := by linarith
  have hr1 : 0 < r-1 := by linarith
  have hs1 : 0 < s-1 := by linarith
  have hN : 0 < r+s := by linarith
  have hn : 0 < r+s-1 := by linarith
  let T := (r+s)^2/(r*s)
  let X := (r+s-1)^2/((r-1)*s)
  let Y := (r+s-1)^2/(r*(s-1))
  have hT : 0 < T := div_pos (sq_pos_of_pos hN) (mul_pos hr0 hs0)
  have hX : 0 < X := div_pos (sq_pos_of_pos hn) (mul_pos hr1 hs0)
  have hY : 0 < Y := div_pos (sq_pos_of_pos hn) (mul_pos hr0 hs1)
  have hL : 1 ≤ Real.log T := one_le_log_binary_ratio hr0 hs0
  have hlogs := add_le_add
    (mul_le_mul_of_nonneg_left (log_tangent_relative hX hT) hr1.le)
    (mul_le_mul_of_nonneg_left (log_tangent_relative hY hT) hs1.le)
  have he : (r-1)*(X/T-1)+(s-1)*(Y/T-1) = 1/(r+s) := by
    dsimp only [T, X, Y]
    field_simp [hr0.ne', hs0.ne', hr1.ne', hs1.ne', hN.ne']
    ring
  have hsum : (r-1)*Real.log X+(s-1)*Real.log Y ≤
      (r+s-2)*Real.log T+1/(r+s) := by
    nlinarith only [hlogs, he]
  have halg : ((r+s-2)*Real.log T+1/(r+s))/(r+s-1)+Real.log T/(r+s) =
      Real.log T+(1-Real.log T)/((r+s)*(r+s-1)) := by
    field_simp [hN.ne', hn.ne']
    ring
  calc
    ((r-1)*Real.log X+(s-1)*Real.log Y)/(r+s-1)+Real.log T/(r+s) ≤
        ((r+s-2)*Real.log T+1/(r+s))/(r+s-1)+Real.log T/(r+s) :=
      add_le_add (div_le_div_of_nonneg_right hsum hn.le) le_rfl
    _ = Real.log T+(1-Real.log T)/((r+s)*(r+s-1)) := halg
    _ ≤ Real.log T := by
      have hneg := div_nonpos_of_nonpos_of_nonneg (show 1-Real.log T ≤ 0 by linarith)
        (mul_nonneg hN.le hn.le)
      linarith only [hneg]

/-- A singleton deletion contributes zero. The other endpoint coefficient
is controlled directly, without importing Lee--Yau's separately cited (3.1). -/
theorem binary_log_recurrence_endpoint {s : ℝ} (hs : 2 ≤ s) :
    (s-1)*Real.log (s^2/(s-1))/s +
      Real.log ((1+s)^2/s)/(1+s) ≤ Real.log ((1+s)^2/s) := by
  have hs0 : 0 < s := by linarith
  have hs1 : 0 < s-1 := by linarith
  have hN : 0 < 1+s := by linarith
  have hr : s^2/(s-1) ≤ (1+s)^2/s := by
    apply (div_le_div_iff₀ hs1 hs0).mpr
    nlinarith only [sq_nonneg (s-2), hs]
  have hl := Real.log_le_log (div_pos (sq_pos_of_pos hs0) hs1) hr
  have hL : 0 ≤ Real.log ((1+s)^2/s) := by
    have hh := one_le_log_binary_ratio (r := (1 : ℝ)) zero_lt_one hs0
    simp only [one_mul] at hh
    linarith only [hh]
  have hc : (s-1)/s+1/(1+s) ≤ 1 := by
    have he : (s-1)/s+1/(1+s) = 1-1/(s*(1+s)) := by
      field_simp [hs0.ne', hN.ne']
      ring
    rw [he]
    have hh : 0 ≤ 1/(s*(1+s)) := by positivity
    linarith only [hh]
  calc
    (s-1)*Real.log (s^2/(s-1))/s+Real.log ((1+s)^2/s)/(1+s) ≤
        (s-1)*Real.log ((1+s)^2/s)/s+Real.log ((1+s)^2/s)/(1+s) :=
      add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl hs1.le) hs0.le) le_rfl
    _ = ((s-1)/s+1/(1+s))*Real.log ((1+s)^2/s) := by ring
    _ ≤ Real.log ((1+s)^2/s) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hL

/-- The logarithmic part of the binary coefficient. At a zero count this
is algebraically zero; the corresponding entropy bound is proved separately by
singleton-fibre identification, never by applying a positive-count estimate. -/
def binaryLog (r s : ℝ) : ℝ := Real.log ((r+s)^2/(r*s))

theorem binaryLog_comm (r s : ℝ) : binaryLog r s = binaryLog s r := by
  simp only [binaryLog, add_comm, mul_comm]

@[simp] theorem binaryLog_zero_left (s : ℝ) : binaryLog 0 s = 0 := by
  simp only [binaryLog, zero_mul, div_zero, Real.log_zero]

@[simp] theorem binaryLog_zero_right (r : ℝ) : binaryLog r 0 = 0 := by
  rw [binaryLog_comm, binaryLog_zero_left]

theorem binaryLog_recurrence_one {s : ℝ} (hs : 2 ≤ s) :
    ((1-1)*binaryLog (1-1) s+(s-1)*binaryLog 1 (s-1))/(1+s-1)+
      binaryLog 1 s/(1+s) ≤ binaryLog 1 s := by
  have he : (1 : ℝ)+(s-1) = s := by ring
  simpa only [binaryLog, sub_self, zero_mul, zero_add, add_sub_cancel_left, one_mul, he]
    using binary_log_recurrence_endpoint hs

/-- The coefficient comparison at every actual positive integer pair,
including (1,1) and each singleton deletion endpoint. -/
theorem binaryLog_recurrence (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    (((r : ℝ)-1)*binaryLog ((r : ℝ)-1) s+
      ((s : ℝ)-1)*binaryLog r ((s : ℝ)-1))/((r : ℝ)+s-1)+
      binaryLog r s/((r : ℝ)+s) ≤ binaryLog r s := by
  by_cases hr1 : r = 1
  · subst r
    by_cases hs1 : s = 1
    · subst s
      have hh := one_le_log_binary_ratio (r := (1 : ℝ)) (s := (1 : ℝ)) zero_lt_one zero_lt_one
      norm_num [binaryLog] at hh ⊢
      linarith only [hh]
    · have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast (show 2 ≤ s by omega)
      simpa only [Nat.cast_one] using binaryLog_recurrence_one hs2
  · have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast (show 2 ≤ r by omega)
    by_cases hs1 : s = 1
    · subst s
      have hh := binaryLog_recurrence_one hr2
      simpa only [Nat.cast_one, binaryLog, add_comm, mul_comm] using hh
    · have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast (show 2 ≤ s by omega)
      have hleft : (r : ℝ)-1+s = (r : ℝ)+s-1 := by ring
      have hright : (r : ℝ)+((s : ℝ)-1) = (r : ℝ)+s-1 := by ring
      simpa only [binaryLog, hleft, hright] using
        binary_log_recurrence_interior (r := (r : ℝ)) (s := (s : ℝ)) (by linarith) (by linarith)

/-- The actual count equation for deletion, valid also when a color is absent. -/
theorem deletedProfile_count {n : ℕ} {m : OccupationState J (n+1) t}
    (ξ : Fibre m) (i : Fin (n+1)) (a : MeshIndex J) :
    m.val a = (if ξ.val.val i = a then 1 else 0)+(deletedProfile ξ i).val a := by
  have hh := occupation_removeNth ξ.val.val i a
  have hm : occupation ξ.val.val = m.val := congrArg Subtype.val ξ.property
  rw [hm] at hh
  exact hh

theorem deletedProfile_count_le {n : ℕ} {m : OccupationState J (n+1) t}
    (ξ : Fibre m) (i : Fin (n+1)) (a : MeshIndex J) :
    (deletedProfile ξ i).val a ≤ m.val a := by
  rw [deletedProfile_count ξ i a]
  omega

/-- Removing one particle cannot introduce an occupied color. -/
theorem deletedProfile_two_colours {n : ℕ} {m : OccupationState J (n+1) t}
    (ξ : Fibre m) (i : Fin (n+1)) (a b : MeshIndex J)
    (honly : ∀ c, 0 < m.val c → c = a ∨ c = b) :
    ∀ c, 0 < (deletedProfile ξ i).val c → c = a ∨ c = b := by
  intro c hc
  exact honly c (lt_of_lt_of_le hc (deletedProfile_count_le ξ i c))

/-- Singleton-fibre entropy for functions defined on the actual fibre itself. -/
theorem uniformEntropy_one_colour (m : OccupationState J N t) (a : MeshIndex J)
    (honly : ∀ c, 0 < m.val c → c = a) (f : Fibre m → ℝ) : uniformEntropy f = 0 := by
  let : Subsingleton (Fibre m) := fibre_subsingleton_of_one_colour m a honly
  let ξ : Fibre m := ⟨labelOfState m, profile_labelOfState m⟩
  let : Nonempty (Fibre m) := ⟨ξ⟩
  have he : f = fun _ => f ξ := funext fun η => congrArg f (Subsingleton.elim η ξ)
  rw [he, uniformEntropy_const]

/-- The full Lee--Yau two-color ordinary logarithmic Sobolev bound on
actual occupation fibres. The smaller-fibre recurrence is discharged by strong
induction; absent colors and singleton fibres are proved directly. -/
theorem two_colour_lsi (m : OccupationState J N t) (a b : MeshIndex J)
    (hab : a ≠ b) (honly : ∀ c, 0 < m.val c → c = a ∨ c = b)
    (f : Fibre m → ℝ) (hf : ∀ η, 0 ≤ f η) :
    4*(N : ℝ)*uniformEntropy f ≤
      (2/Real.log 2*binaryLog (m.val a) (m.val b))*
        orderedSwapSum m (fun η => Real.sqrt (f η)) := by
  classical
  induction N using Nat.strong_induction_on generalizing t with
  | h N ih =>
    by_cases ha0 : m.val a = 0
    · have hz := uniformEntropy_one_colour m b (fun c hc => by
        rcases honly c hc with he | he
        · subst c
          omega
        · exact he) f
      simp only [hz, ha0, Nat.cast_zero, binaryLog_zero_left, mul_zero, zero_mul, le_refl]
    by_cases hb0 : m.val b = 0
    · have hz := uniformEntropy_one_colour m a (fun c hc => by
        rcases honly c hc with he | he
        · exact he
        · subst c
          omega) f
      simp only [hz, hb0, Nat.cast_zero, binaryLog_zero_right, mul_zero, zero_mul, le_refl]
    have ha : 0 < m.val a := Nat.pos_of_ne_zero ha0
    have hb : 0 < m.val b := Nat.pos_of_ne_zero hb0
    have ht := two_colour_total m a b hab honly
    rcases N with _ | n
    · omega
    have hn : 1 ≤ n := by omega
    let A := 2/Real.log 2*binaryLog ((m.val a : ℝ)-1) (m.val b)
    let B := 2/Real.log 2*binaryLog (m.val a) ((m.val b : ℝ)-1)
    have hsmall (i : Fin (n+1)) (ξ : Fibre m) :
        4*(n : ℝ)*uniformEntropy (fun ζ : Fibre (deletedProfile ξ i) => f (insertedFibre ξ i ζ)) ≤
          (if ξ.val.val i = a then A else B)*orderedSwapSum (deletedProfile ξ i)
            (fun ζ => Real.sqrt (f (insertedFibre ξ i ζ))) := by
      have hh := ih n (by omega) (deletedProfile ξ i)
        (deletedProfile_two_colours ξ i a b honly)
        (fun ζ => f (insertedFibre ξ i ζ)) (fun ζ => hf (insertedFibre ξ i ζ))
      have hca := deletedProfile_count ξ i a
      have hcb := deletedProfile_count ξ i b
      rcases fibre_two_colours m a b honly ξ i with hi | hi
      · simp only [hi, ite_true, hab, ite_false, zero_add] at hca hcb
        have har : ((deletedProfile ξ i).val a : ℝ) = (m.val a : ℝ)-1 := by
          have hh : ((deletedProfile ξ i).val a : ℝ)+1 = m.val a :=
            by exact_mod_cast (show (deletedProfile ξ i).val a+1 = m.val a by omega)
          linarith only [hh]
        simpa only [A, hi, ite_true, har, ← hcb] using hh
      · simp only [hi, Ne.symm hab, ite_false, ite_true, zero_add] at hca hcb
        have hbr : ((deletedProfile ξ i).val b : ℝ) = (m.val b : ℝ)-1 := by
          have hh : ((deletedProfile ξ i).val b : ℝ)+1 = m.val b :=
            by exact_mod_cast (show (deletedProfile ξ i).val b+1 = m.val b by omega)
          linarith only [hh]
        simpa only [B, hi, Ne.symm hab, ite_false, hbr, ← hca] using hh
    have hh := two_colour_entropy_step hn m a b hab ha hb honly A B f hf hsmall
    have hnr : (0 : ℝ) < n+1 := by positivity
    have har : (0 : ℝ) < m.val a := by exact_mod_cast ha
    have hbr : (0 : ℝ) < m.val b := by exact_mod_cast hb
    have hsum : (m.val a : ℝ)+(m.val b : ℝ) = (n : ℝ)+1 := by exact_mod_cast ht
    have hlog : Real.log (((m.val a : ℝ)/(n+1))*((m.val b : ℝ)/(n+1))) =
        -binaryLog (m.val a) (m.val b) := by
      have he : (((m.val a : ℝ)/(n+1))*((m.val b : ℝ)/(n+1)))⁻¹ =
          ((m.val a : ℝ)+(m.val b : ℝ))^2/((m.val a : ℝ)*(m.val b : ℝ)) := by
        rw [hsum]
        field_simp [har.ne', hbr.ne', hnr.ne']
      unfold binaryLog
      rw [← he, Real.log_inv, neg_neg]
    have hc := mul_le_mul_of_nonneg_left (binaryLog_recurrence (m.val a) (m.val b) ha hb)
      (show 0 ≤ 2/Real.log 2 from div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le)
    rw [hsum, add_sub_cancel_right] at hc
    have hcoef :
        ((((m.val a : ℝ)-1)*A+((m.val b : ℝ)-1)*B)/(n : ℝ) -
          2*Real.log (((m.val a : ℝ)/(n+1))*((m.val b : ℝ)/(n+1)))/
            (((n+1 : ℕ) : ℝ)*Real.log 2)) ≤
          2/Real.log 2*binaryLog (m.val a) (m.val b) := by
      rw [hlog]
      simp only [Nat.cast_add, Nat.cast_one]
      convert hc using 1
      dsimp only [A, B]
      rw [div_mul_eq_div_div]
      ring
    exact hh.trans (mul_le_mul_of_nonneg_right hcoef
      (orderedSwapSum_nonneg m (fun η => Real.sqrt (f η))))

/-- Lee--Yau's actual two-color ordinary LSI in the manuscript's exact
once-counted particle-pair energy. The two occupied colors are explicit; all
other colors have count zero by `honly`. -/
theorem two_colour_logSobolev (F : LabelState J N t → ℝ)
    (m : OccupationState J N t) (a b : MeshIndex J) (hab : a ≠ b)
    (ha : 0 < m.val a) (hb : 0 < m.val b)
    (honly : ∀ c, 0 < m.val c → c = a ∨ c = b)
    (hF : ∀ η : Fibre m, 0 ≤ F η.val) :
    uniformFibreEntropy F m ≤
      (2/Real.log 2*Real.log ((N : ℝ)^2/((m.val a : ℝ)*(m.val b : ℝ))))*
        transpositionEnergy (fun η => Real.sqrt (F η)) m := by
  have ht := two_colour_total m a b hab honly
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsum : (m.val a : ℝ)+(m.val b : ℝ) = N := by exact_mod_cast ht
  have hh := two_colour_lsi m a b hab honly (fun η => F η.val) hF
  rw [orderedSwapSum_eq_source_sum (fun η => Real.sqrt (F η)) m] at hh
  change 4*(N : ℝ)*uniformFibreEntropy F m ≤ _ at hh
  unfold binaryLog at hh
  rw [hsum] at hh
  unfold transpositionEnergy
  rw [one_div_mul_eq_div, ← mul_div_assoc]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*(N : ℝ))).mpr
  nlinarith only [hh]

end PeriodicAttractiveLogGas.MultisliceEntropyRecursion
