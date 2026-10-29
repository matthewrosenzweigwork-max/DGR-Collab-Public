import LeanResearch.PeriodicAttractiveLogGas.FibreEntropy

/-! The exact complete-graph transposition form in source 2723–2735.
The elementary finite-conditioning development below is intended to prove
its sharp Poincare bound without importing an Aldous spectral-gap premise.
The final multislice inequality is not yet established in this candidate. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.MultislicePoincare
open MeshCells LabelOccupations DiscreteOccupationIdentities FibreProjection FibreEntropy

/-- Uniform average, with the empty finite sum convention retained. -/
def uniformAverage {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card Ω

theorem card_mul_uniformAverage {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    (Fintype.card Ω : ℝ) * uniformAverage f = ∑ x, f x := by
  by_cases h : Fintype.card Ω = 0
  · have hx (x : Ω) : False := by
      let : Nonempty Ω := ⟨x⟩
      have hp : 0 < Fintype.card Ω := Fintype.card_pos
      omega
    have hs : (∑ x, f x) = 0 := Finset.sum_eq_zero fun x _ => (hx x).elim
    simp only [h, Nat.cast_zero, zero_mul, hs]
  · unfold uniformAverage
    field_simp

theorem uniformAverage_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    uniformAverage (fun _ : Ω => c) = c := by
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  simp only [uniformAverage, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem uniformAverage_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    uniformAverage (fun x => f x + g x) = uniformAverage f + uniformAverage g := by
  simp only [uniformAverage, Finset.sum_add_distrib, add_div]

theorem uniformAverage_sub {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    uniformAverage (fun x => f x - g x) = uniformAverage f - uniformAverage g := by
  simp only [uniformAverage, Finset.sum_sub_distrib, sub_div]

theorem uniformAverage_mul {Ω : Type*} [Fintype Ω] (c : ℝ) (f : Ω → ℝ) :
    uniformAverage (fun x => c * f x) = c * uniformAverage f := by
  simp only [uniformAverage, ← Finset.mul_sum]
  ring

theorem uniformAverage_nonneg {Ω : Type*} [Fintype Ω] {f : Ω → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ uniformAverage f :=
  div_nonneg (Finset.sum_nonneg fun x _ => hf x) (Nat.cast_nonneg _)

theorem uniformAverage_equiv {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (e : Ω ≃ Λ) (f : Λ → ℝ) : uniformAverage (fun x => f (e x)) = uniformAverage f := by
  unfold uniformAverage
  rw [Equiv.sum_comp e, Fintype.card_congr e]

section Conditioning
variable {Ω A : Type*} [Fintype Ω] [Fintype A] [DecidableEq A]

/-- Literal coordinate fibre, including values absent from the support. -/
abbrev CoordinateFibre (X : Ω → A) (a : A) := {x : Ω // X x = a}

def marginalWeight (X : Ω → A) (a : A) : ℝ :=
  Fintype.card (CoordinateFibre X a) / (Fintype.card Ω : ℝ)

def conditionalAverage (X : Ω → A) (f : Ω → ℝ) (a : A) : ℝ :=
  uniformAverage (fun x : CoordinateFibre X a => f x.val)

theorem sum_coordinate_fibres (X : Ω → A) (f : Ω → ℝ) :
    (∑ x, f x) = ∑ a, ∑ x : CoordinateFibre X a, f x.val := by
  have h := Equiv.sum_comp (Equiv.sigmaFiberEquiv X) f
  rw [Fintype.sum_sigma] at h
  exact h.symm

theorem average_conditioning (X : Ω → A) (f : Ω → ℝ) :
    uniformAverage f = ∑ a, marginalWeight X a * conditionalAverage X f a := by
  unfold uniformAverage
  rw [sum_coordinate_fibres X f, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  dsimp only [marginalWeight, conditionalAverage]
  rw [div_mul_eq_mul_div, card_mul_uniformAverage]

theorem average_mul_coordinate (X : Ω → A) (f : Ω → ℝ) (g : A → ℝ) :
    uniformAverage (fun x => f x * g (X x)) =
      ∑ a, marginalWeight X a * conditionalAverage X f a * g a := by
  unfold uniformAverage
  rw [sum_coordinate_fibres X (fun x => f x * g (X x)), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  have he : (∑ x : CoordinateFibre X a, f x.val * g (X x.val)) =
      (∑ x : CoordinateFibre X a, f x.val) * g a := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by rw [x.property]
  rw [he, ← card_mul_uniformAverage (fun x : CoordinateFibre X a => f x.val)]
  dsimp only [marginalWeight, conditionalAverage]
  ring

omit [Fintype A] in
theorem marginalWeight_nonneg (X : Ω → A) (a : A) : 0 ≤ marginalWeight X a :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem marginalWeight_sum [Nonempty Ω] (X : Ω → A) :
    (∑ a, marginalWeight X a) = 1 := by
  have h := sum_coordinate_fibres X (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  simp only [marginalWeight, ← Finset.sum_div, ← h, div_self hc]

/-- The conditional mean is its genuine orthogonal finite projection;
no nonempty-fibre hypothesis is imposed on unused coordinate values. -/
theorem conditional_centering (X : Ω → A) (f : Ω → ℝ) :
    uniformAverage (fun x => f x * conditionalAverage X f (X x)) =
      ∑ a, marginalWeight X a * (conditionalAverage X f a)^2 := by
  rw [average_mul_coordinate]
  apply Finset.sum_congr rfl
  intro a _
  ring

end Conditioning

variable {J N : ℕ} {t : ℝ}

/-- The literal manuscript form: each unordered particle pair appears once. -/
def transpositionEnergy (F : LabelState J N t → ℝ) (m : OccupationState J N t) : ℝ :=
  (1 / (2 * (N : ℝ))) * ∑ i : Fin N, ∑ j : Fin N,
    if i < j then fibreAverage
      (fun η => (F (permutedLabel (Equiv.swap i j) η) - F η)^2) m else 0

def fibreVariance (F : LabelState J N t → ℝ) (m : OccupationState J N t) : ℝ :=
  fibreAverage (fun η => (F η - fibreAverage F m)^2) m

theorem transpositionEnergy_nonneg (F : LabelState J N t → ℝ)
    (m : OccupationState J N t) : 0 ≤ transpositionEnergy F m := by
  unfold transpositionEnergy
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    by split_ifs; exact fibreAverage_nonneg (fun _ => sq_nonneg _) m; exact le_rfl

theorem fibreVariance_nonneg (F : LabelState J N t → ℝ) (m : OccupationState J N t) :
    0 ≤ fibreVariance F m := fibreAverage_nonneg (fun _ => sq_nonneg _) m

/-- Exact uniform orbit averaging, using the previously proved factorial
multiplicity of every actual permutation fibre. -/
theorem fibreAverage_eq_permutation_average (F : LabelState J N t → ℝ)
    (m : OccupationState J N t) :
    fibreAverage F m = uniformAverage
      (fun σ : Equiv.Perm (Fin N) => F (permutedLabel σ (labelOfState m))) := by
  have h := projection_eq_permutation_average F (labelOfState m)
  simpa only [projection, profile_labelOfState, uniformAverage] using h

/-- Finite sums commute with the literal uniform expectation. -/
theorem uniformAverage_sum {Ω I : Type*} [Fintype Ω] [Fintype I] (f : I → Ω → ℝ) :
    uniformAverage (fun x => ∑ i, f i x) = ∑ i, uniformAverage (f i) := by
  unfold uniformAverage
  rw [Finset.sum_comm, Finset.sum_div]

/-- Particle relabeling acts bijectively on the same actual occupation fibre. -/
def fibrePermutation (σ : Equiv.Perm (Fin N)) (m : OccupationState J N t) :
    Fibre m ≃ Fibre m where
  toFun η := ⟨permutedLabel σ η.val, by rw [profile_permutedLabel, η.property]⟩
  invFun η := ⟨permutedLabel σ.symm η.val, by rw [profile_permutedLabel, η.property]⟩
  left_inv η := by apply Subtype.ext; exact permutedLabel_symm σ η.val
  right_inv η := by apply Subtype.ext; exact permutedLabel_apply_symm σ η.val

@[simp] theorem fibrePermutation_apply_coordinate (σ : Equiv.Perm (Fin N))
    (m : OccupationState J N t) (η : Fibre m) (i : Fin N) :
    (fibrePermutation σ m η).val.val i = η.val.val (σ i) := rfl

/-- Equal one-coordinate marginal expectations follow from an actual swap. -/
theorem coordinate_average_eq (m : OccupationState J N t) (g : MeshIndex J → ℝ)
    (i j : Fin N) :
    uniformAverage (fun η : Fibre m => g (η.val.val i)) =
      uniformAverage (fun η : Fibre m => g (η.val.val j)) := by
  have h := uniformAverage_equiv (fibrePermutation (Equiv.swap i j) m)
    (fun η : Fibre m => g (η.val.val i))
  simpa only [fibrePermutation_apply_coordinate, Equiv.swap_apply_left] using h.symm

/-- The deterministic occupation identity is proved by partitioning the
actual particle indices into the fibres of their labels. -/
theorem occupation_sum (η : LabelVector J N) (g : MeshIndex J → ℝ) :
    (∑ i, g (η i)) = ∑ a, (occupation η a : ℝ) * g a := by
  classical
  rw [sum_coordinate_fibres η (fun i => g (η i))]
  apply Finset.sum_congr rfl
  intro a _
  have he : (∑ i : CoordinateFibre η a, g (η i.val)) =
      ∑ _ : CoordinateFibre η a, g a :=
    Finset.sum_congr rfl fun i _ => by rw [i.property]
  rw [he]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  simp only [CoordinateFibre, Fintype.card_subtype, occupation]

/-- Actual fixed counts, including absent colors. -/
def colourAverage (m : OccupationState J N t) (g : MeshIndex J → ℝ) : ℝ :=
  (∑ a, (m.val a : ℝ) * g a) / N

theorem coordinate_average (m : OccupationState J N t) (g : MeshIndex J → ℝ)
    (i : Fin N) :
    uniformAverage (fun η : Fibre m => g (η.val.val i)) = colourAverage m g := by
  let : Nonempty (Fibre m) := ⟨⟨labelOfState m, profile_labelOfState m⟩⟩
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt).ne'
  have hs : uniformAverage (fun η : Fibre m => ∑ j, g (η.val.val j)) =
      (N : ℝ) * uniformAverage (fun η : Fibre m => g (η.val.val i)) := by
    rw [uniformAverage_sum]
    simp_rw [← coordinate_average_eq m g i]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have he (η : Fibre m) : (∑ j, g (η.val.val j)) = ∑ a, (m.val a : ℝ) * g a := by
    rw [occupation_sum]
    have hp : occupation η.val.val = m.val := congrArg Subtype.val η.property
    rw [hp]
  simp_rw [he] at hs
  rw [uniformAverage_const] at hs
  unfold colourAverage
  rw [hs]
  field_simp

/-- Joint-coordinate exchangeability fixing the first coordinate, proved by
an actual swap of the other two coordinates. -/
theorem coordinate_pair_average_eq (m : OccupationState J N t)
    (f g : MeshIndex J → ℝ) (i j k : Fin N) (hij : i ≠ j) (hik : i ≠ k) :
    uniformAverage (fun η : Fibre m => f (η.val.val i) * g (η.val.val j)) =
      uniformAverage (fun η : Fibre m => f (η.val.val i) * g (η.val.val k)) := by
  have h := uniformAverage_equiv (fibrePermutation (Equiv.swap j k) m)
    (fun η : Fibre m => f (η.val.val i) * g (η.val.val j))
  simpa only [fibrePermutation_apply_coordinate,
    Equiv.swap_apply_of_ne_of_ne hij hik, Equiv.swap_apply_left] using h.symm

/-- The actual without-replacement covariance identity. The denominator is
kept multiplication-free here, so no spurious assumption excludes N=1. -/
theorem pair_average_relation (m : OccupationState J N t) (f g : MeshIndex J → ℝ)
    (i j : Fin N) (hij : i ≠ j) :
    ((N : ℝ) - 1) * uniformAverage
      (fun η : Fibre m => f (η.val.val i) * g (η.val.val j)) =
      (N : ℝ) * colourAverage m f * colourAverage m g -
        colourAverage m (fun a => f a * g a) := by
  let A (k : Fin N) := uniformAverage
    (fun η : Fibre m => f (η.val.val i) * g (η.val.val k))
  have hd : A i = colourAverage m (fun a => f a * g a) := coordinate_average m (fun a => f a * g a) i
  have he (k : Fin N) : A k = (if k = i then A i - A j else 0) + A j := by
    by_cases hk : k = i
    · subst k
      simp
    · simp only [ite_eq_right hk, zero_add]
      exact coordinate_pair_average_eq m f g i k j (Ne.symm hk) hij
  have hs : (∑ k, A k) = A i + ((N : ℝ) - 1) * A j := by
    rw [show (∑ k, A k) = ∑ k, ((if k = i then A i - A j else 0) + A j) from
      Finset.sum_congr rfl (fun k _ => he k), Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hp (η : Fibre m) :
      (∑ k, f (η.val.val i) * g (η.val.val k)) =
        (∑ a, (m.val a : ℝ) * g a) * f (η.val.val i) := by
    rw [← Finset.mul_sum, occupation_sum]
    have hm : occupation η.val.val = m.val := congrArg Subtype.val η.property
    rw [hm]
    ring
  have ha : (∑ k, A k) = (∑ a, (m.val a : ℝ) * g a) * colourAverage m f := by
    change (∑ k, uniformAverage (fun η : Fibre m => f (η.val.val i) * g (η.val.val k))) = _
    rw [← uniformAverage_sum]
    simp_rw [hp]
    rw [uniformAverage_mul, coordinate_average]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt).ne'
  have hg : (∑ a, (m.val a : ℝ) * g a) = (N : ℝ) * colourAverage m g := by
    unfold colourAverage
    field_simp
  rw [hg, hs, hd] at ha
  change ((N : ℝ) - 1) * A j = _
  nlinarith only [ha]

/-- The literal one-coordinate marginal is count/N, not an assumed law. -/
theorem coordinate_marginal (m : OccupationState J N t) (i : Fin N) (a : MeshIndex J) :
    marginalWeight (fun η : Fibre m => η.val.val i) a = (m.val a : ℝ) / N := by
  classical
  have h := coordinate_average m (fun b => if b = a then (1 : ℝ) else 0) i
  have hl : uniformAverage (fun η : Fibre m => if η.val.val i = a then (1 : ℝ) else 0) =
      marginalWeight (fun η : Fibre m => η.val.val i) a := by
    simp only [uniformAverage, marginalWeight, CoordinateFibre, Fintype.card_subtype,
      ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hl] at h
  simpa only [colourAverage, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using h

/-- The conditional coordinate projections have the actual color law. -/
theorem coordinate_projection_pairing (m : OccupationState J N t) (f : Fibre m → ℝ)
    (i : Fin N) (g : MeshIndex J → ℝ) :
    uniformAverage (fun η => f η * g (η.val.val i)) =
      colourAverage m (fun a => conditionalAverage (fun η : Fibre m => η.val.val i) f a * g a) := by
  rw [average_mul_coordinate]
  simp_rw [coordinate_marginal]
  unfold colourAverage
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem colourAverage_nonneg (m : OccupationState J N t) {g : MeshIndex J → ℝ}
    (hg : ∀ a, 0 ≤ g a) : 0 ≤ colourAverage m g :=
  div_nonneg (Finset.sum_nonneg fun a _ => mul_nonneg (Nat.cast_nonneg _) (hg a))
    (Nat.cast_nonneg _)

theorem colourAverage_sum {I : Type*} [Fintype I] (m : OccupationState J N t)
    (g : I → MeshIndex J → ℝ) :
    colourAverage m (fun a => ∑ i, g i a) = ∑ i, colourAverage m (g i) := by
  unfold colourAverage
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_div]

/-- The actual conditional coordinate projection of an observable. -/
def coordinateProjection (m : OccupationState J N t) (f : Fibre m → ℝ)
    (i : Fin N) : MeshIndex J → ℝ :=
  conditionalAverage (fun η : Fibre m => η.val.val i) f

theorem coordinateProjection_mean (m : OccupationState J N t) (f : Fibre m → ℝ)
    (i : Fin N) : colourAverage m (coordinateProjection m f i) = uniformAverage f := by
  have h := average_conditioning (fun η : Fibre m => η.val.val i) f
  simp_rw [coordinate_marginal] at h
  unfold colourAverage coordinateProjection
  rw [Finset.sum_div]
  convert h.symm using 1
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem coordinateProjection_pairing (m : OccupationState J N t) (f : Fibre m → ℝ)
    (i : Fin N) :
    uniformAverage (fun η => f η * coordinateProjection m f i (η.val.val i)) =
      colourAverage m (fun a => (coordinateProjection m f i a)^2) := by
  have h := coordinate_projection_pairing m f i (coordinateProjection m f i)
  simpa only [coordinateProjection, pow_two] using h

/-- Summed conditional projections on the literal finite fibre. -/
def projectionSum (m : OccupationState J N t) (f : Fibre m → ℝ) (η : Fibre m) : ℝ :=
  ∑ i : Fin N, coordinateProjection m f i (η.val.val i)

def projectionSquareSum (m : OccupationState J N t) (f : Fibre m → ℝ) : ℝ :=
  ∑ i : Fin N, colourAverage m (fun a => (coordinateProjection m f i a)^2)

theorem projectionSum_pairing (m : OccupationState J N t) (f : Fibre m → ℝ) :
    uniformAverage (fun η => f η * projectionSum m f η) = projectionSquareSum m f := by
  unfold projectionSum projectionSquareSum
  simp only [Finset.mul_sum]
  rw [uniformAverage_sum]
  exact Finset.sum_congr rfl fun i _ => coordinateProjection_pairing m f i

/-- Exact negative-covariance identity, including the nonnegative correction
term which is discarded only when deriving the sharp projection estimate. -/
theorem projectionSum_square (m : OccupationState J N t) (f : Fibre m → ℝ)
    (hf : uniformAverage f = 0) :
    ((N : ℝ) - 1) * uniformAverage (fun η => (projectionSum m f η)^2) =
      (N : ℝ) * projectionSquareSum m f -
        colourAverage m (fun a => (∑ i : Fin N, coordinateProjection m f i a)^2) := by
  let g := coordinateProjection m f
  have hmean (i : Fin N) : colourAverage m (g i) = 0 := by
    rw [show colourAverage m (g i) = uniformAverage f from coordinateProjection_mean m f i, hf]
  have hp (i j : Fin N) :
      ((N : ℝ)-1) * uniformAverage (fun η : Fibre m => g i (η.val.val i)*g j (η.val.val j)) =
        (if i = j then (N : ℝ)*colourAverage m (fun a => (g i a)^2) else 0) -
          colourAverage m (fun a => g i a*g j a) := by
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      rw [show uniformAverage (fun η : Fibre m => g i (η.val.val i)*g i (η.val.val i)) =
        colourAverage m (fun a => g i a*g i a) from coordinate_average m (fun a => g i a*g i a) i]
      have he : (fun a => g i a*g i a) = fun a => (g i a)^2 := funext fun _ => by ring
      rw [he]
      ring
    · have h := pair_average_relation m (g i) (g j) i j hij
      rw [hmean i, hmean j] at h
      simpa only [ite_eq_right hij, mul_zero, zero_sub] using h
  have hs (η : Fibre m) : (projectionSum m f η)^2 =
      ∑ i : Fin N, ∑ j : Fin N, g i (η.val.val i)*g j (η.val.val j) := by
    simp only [projectionSum, g, pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have ht : colourAverage m (fun a => (∑ i : Fin N, g i a)^2) =
      ∑ i : Fin N, ∑ j : Fin N, colourAverage m (fun a => g i a*g j a) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum, colourAverage_sum]
    rw [Finset.sum_comm]
  calc
    _ = ∑ i : Fin N, ∑ j : Fin N, ((N : ℝ)-1)*
        uniformAverage (fun η : Fibre m => g i (η.val.val i)*g j (η.val.val j)) := by
          simp_rw [hs, uniformAverage_sum]
          simp only [Finset.mul_sum]
    _ = ∑ i : Fin N, ∑ j : Fin N,
        ((if i = j then (N : ℝ)*colourAverage m (fun a => (g i a)^2) else 0) -
          colourAverage m (fun a => g i a*g j a)) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hp i j
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [← Finset.mul_sum, ← ht]
      rfl

/-- Finite quadratic expansion used to prove the sharp projection estimate
without a separate Hilbert-space or spectral-gap premise. -/
theorem uniformAverage_linear_square {Ω : Type*} [Fintype Ω]
    (f g : Ω → ℝ) (a b : ℝ) :
    uniformAverage (fun x => (a*f x-b*g x)^2) =
      a^2*uniformAverage (fun x => (f x)^2) -
        (2*a*b)*uniformAverage (fun x => f x*g x) +
          b^2*uniformAverage (fun x => (g x)^2) := by
  have he : (fun x => (a*f x-b*g x)^2) =
      fun x => a^2*(f x)^2-(2*a*b)*(f x*g x)+b^2*(g x)^2 :=
    funext fun _ => by ring
  rw [he, uniformAverage_add, uniformAverage_sub]
  simp only [uniformAverage_mul]

/-- The sharp coordinate-projection frame bound on the actual multislice.
Its negative covariance and all coordinate laws have been proved above. -/
theorem coordinate_projection_bound (m : OccupationState J N t) (hN : 2 ≤ N)
    (f : Fibre m → ℝ) (hf : uniformAverage f = 0) :
    ((N : ℝ)-1)*projectionSquareSum m f ≤
      (N : ℝ)*uniformAverage (fun η => (f η)^2) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (0 : ℝ) ≤ (N : ℝ)-1 := by
    have h : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    linarith only [h]
  have hs := projectionSum_square m f hf
  have hc := colourAverage_nonneg m
    (fun a => sq_nonneg (∑ i : Fin N, coordinateProjection m f i a))
  have hm := congrArg (fun z : ℝ => ((N : ℝ)-1)*z) hs
  have ht := mul_nonneg hn1 hc
  have hq := uniformAverage_nonneg
    (fun η : Fibre m => sq_nonneg (((N : ℝ)-1)*projectionSum m f η-(N : ℝ)*f η))
  rw [uniformAverage_linear_square] at hq
  have hp : uniformAverage (fun η => projectionSum m f η*f η) = projectionSquareSum m f := by
    simpa only [mul_comm] using projectionSum_pairing m f
  rw [hp] at hq
  by_contra h
  have hh : 0 < (N : ℝ)*(((N : ℝ)-1)*projectionSquareSum m f-
      (N : ℝ)*uniformAverage (fun η => (f η)^2)) :=
    mul_pos hn (sub_pos.mpr (lt_of_not_ge h))
  nlinarith only [hq, hm, ht, hh]

section Deletion
variable {n : ℕ}

/-- Cap one contains every actual word, also at zero particle count. -/
def unitCapLabel (η : LabelVector J n) : LabelState J n 1 :=
  ⟨η, by
    intro a
    have hc : occupation η a ≤ n := by
      simpa only [occupation, Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.filter_subset (fun i => η i = a) (Finset.univ : Finset (Fin n)))
    simpa only [one_mul] using (show (occupation η a : ℝ) ≤ (n : ℝ) by exact_mod_cast hc)⟩

theorem occupation_eq_sum (η : LabelVector J n) (a : MeshIndex J) :
    occupation η a = ∑ i, if η i = a then (1 : ℕ) else 0 := by
  classical
  simp only [occupation, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Literal count decomposition at the deleted coordinate. -/
theorem occupation_removeNth (η : LabelVector J (n+1)) (i : Fin (n+1)) (a : MeshIndex J) :
    occupation η a = (if η i = a then 1 else 0) + occupation (i.removeNth η) a := by
  classical
  have h := Fin.sum_univ_succAbove (fun j : Fin (n+1) => if η j = a then (1 : ℕ) else 0) i
  rw [occupation_eq_sum, occupation_eq_sum]
  simpa only [Fin.removeNth] using! h

def deletedProfile {m : OccupationState J (n+1) t} (ξ : Fibre m) (i : Fin (n+1)) :
    OccupationState J n 1 := profile (unitCapLabel (i.removeNth ξ.val.val))

theorem removed_occupation_eq {m : OccupationState J (n+1) t}
    (ξ η : Fibre m) (i : Fin (n+1)) (hi : η.val.val i = ξ.val.val i) :
    occupation (i.removeNth η.val.val) = occupation (i.removeNth ξ.val.val) := by
  funext a
  have hη := occupation_removeNth η.val.val i a
  have hξ := occupation_removeNth ξ.val.val i a
  have hpη : occupation η.val.val = m.val := congrArg Subtype.val η.property
  have hpξ : occupation ξ.val.val = m.val := congrArg Subtype.val ξ.property
  rw [hpη, hi] at hη
  rw [hpξ] at hξ
  omega

/-- Inserting the conditioned color reconstructs exactly the original counts. -/
theorem inserted_occupation {m : OccupationState J (n+1) t} (ξ : Fibre m)
    (i : Fin (n+1)) (ζ : Fibre (deletedProfile ξ i)) :
    occupation (Fin.insertNth (α := fun _ : Fin (n+1) => MeshIndex J) i (ξ.val.val i) ζ.val.val) = occupation ξ.val.val := by
  funext a
  have hz : occupation ζ.val.val = occupation (i.removeNth ξ.val.val) :=
    congrArg Subtype.val ζ.property
  have h := occupation_removeNth (Fin.insertNth (α := fun _ : Fin (n+1) => MeshIndex J) i (ξ.val.val i) ζ.val.val) i a
  rw [Fin.insertNth_apply_same, Fin.removeNth_insertNth, hz] at h
  exact h.trans (occupation_removeNth ξ.val.val i a).symm

def insertedFibre {m : OccupationState J (n+1) t} (ξ : Fibre m)
    (i : Fin (n+1)) (ζ : Fibre (deletedProfile ξ i)) : Fibre m :=
  ⟨⟨i.insertNth (ξ.val.val i) ζ.val.val, by
    intro a
    rw [inserted_occupation ξ i ζ]
    exact ξ.val.property a⟩, by
    apply Subtype.ext
    change occupation (Fin.insertNth (α := fun _ : Fin (n+1) => MeshIndex J) i (ξ.val.val i) ζ.val.val) = m.val
    rw [inserted_occupation ξ i ζ]
    exact congrArg Subtype.val ξ.property⟩

/-- Actual bijection of the conditioned fibre with the (N-1)-particle
occupation fibre. No conditional uniform-law or count assertion is assumed. -/
def deletionEquiv {m : OccupationState J (n+1) t} (ξ : Fibre m) (i : Fin (n+1)) :
    CoordinateFibre (fun η : Fibre m => η.val.val i) (ξ.val.val i) ≃
      Fibre (deletedProfile ξ i) where
  toFun η := ⟨unitCapLabel (i.removeNth η.val.val.val), by
    apply Subtype.ext
    exact removed_occupation_eq ξ η.val i η.property⟩
  invFun ζ := ⟨insertedFibre ξ i ζ, by
    change Fin.insertNth (α := fun _ : Fin (n+1) => MeshIndex J) i
      (ξ.val.val i) ζ.val.val i = ξ.val.val i
    exact Fin.insertNth_apply_same (α := fun _ => MeshIndex J) i _ _⟩
  left_inv η := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change i.insertNth (ξ.val.val i) (i.removeNth η.val.val.val) = η.val.val.val
    exact (congrArg (fun a : MeshIndex J => i.insertNth a (i.removeNth η.val.val.val))
      η.property.symm).trans (Fin.insertNth_self_removeNth i η.val.val.val)
  right_inv ζ := by
    apply Subtype.ext
    apply Subtype.ext
    exact Fin.removeNth_insertNth (α := fun _ => MeshIndex J) i (ξ.val.val i) ζ.val.val

/-- Deleting a coordinate commutes with every transposition on the remaining
actual indices, via the injective succAbove embedding. -/
theorem removeNth_swap (η : LabelVector J (n+1)) (i : Fin (n+1)) (j k : Fin n) :
    i.removeNth (η ∘ Equiv.swap (i.succAbove j) (i.succAbove k)) =
      i.removeNth η ∘ Equiv.swap j k := by
  funext l
  change η (Equiv.swap (i.succAbove j) (i.succAbove k) (i.succAbove l)) =
    η (i.succAbove (Equiv.swap j k l))
  by_cases hj : l = j
  · subst l
    rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  · by_cases hk : l = k
    · subst l
      rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
    · have hij : i.succAbove l ≠ i.succAbove j := fun h => hj (Fin.succAbove_right_inj.mp h)
      have hik : i.succAbove l ≠ i.succAbove k := fun h => hk (Fin.succAbove_right_inj.mp h)
      rw [Equiv.swap_apply_of_ne_of_ne hij hik, Equiv.swap_apply_of_ne_of_ne hj hk]

/-- Uniform conditional expectations are transported by the proved bijection. -/
theorem conditionalAverage_deletion {m : OccupationState J (n+1) t} (ξ : Fibre m)
    (i : Fin (n+1)) (f : Fibre m → ℝ) :
    conditionalAverage (fun η : Fibre m => η.val.val i) f (ξ.val.val i) =
      uniformAverage (fun ζ : Fibre (deletedProfile ξ i) => f (insertedFibre ξ i ζ)) := by
  have h := uniformAverage_equiv (deletionEquiv ξ i).symm
    (fun η : CoordinateFibre (fun η : Fibre m => η.val.val i) (ξ.val.val i) => f η.val)
  exact h.symm

end Deletion


/-- A local fibre observable has a literal extension to the original label space. -/
def extendFibre (m : OccupationState J N t) (f : Fibre m → ℝ)
    (η : LabelState J N t) : ℝ :=
  if h : profile η = m then f ⟨η, h⟩ else 0

@[simp] theorem extendFibre_val (m : OccupationState J N t) (f : Fibre m → ℝ)
    (η : Fibre m) : extendFibre m f η.val = f η := by
  simp only [extendFibre, dite_eq_left η.property]

/-- Orbit averaging at any actual fibre point, for a genuinely local observable. -/
theorem uniformAverage_permutations (m : OccupationState J N t) (f : Fibre m → ℝ)
    (ξ : Fibre m) :
    uniformAverage f = uniformAverage (fun σ : Equiv.Perm (Fin N) =>
      f (fibrePermutation σ m ξ)) := by
  have h := projection_eq_permutation_average (extendFibre m f) ξ.val
  unfold projection at h
  rw [ξ.property] at h
  change uniformAverage (fun η : Fibre m => extendFibre m f η.val) =
    uniformAverage (fun σ => extendFibre m f (permutedLabel σ ξ.val)) at h
  simp only [extendFibre_val] at h
  convert h using 1
  apply congrArg uniformAverage
  funext σ
  exact (extendFibre_val m f (fibrePermutation σ m ξ)).symm

def localVariance (m : OccupationState J N t) (f : Fibre m → ℝ) : ℝ :=
  uniformAverage (fun η => (f η - uniformAverage f)^2)

/-- Ordered unnormalized transposition sum; its factor 1/(4N) agrees with
1/(2N) times the source's unordered-pair sum. -/
def orderedSwapSum (m : OccupationState J N t) (f : Fibre m → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, uniformAverage
    (fun η => (f (fibrePermutation (Equiv.swap i j) m η) - f η)^2)

@[simp] theorem fibrePermutation_refl (m : OccupationState J N t) (η : Fibre m) :
    fibrePermutation (Equiv.refl (Fin N)) m η = η := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

theorem orderedSwapSum_center (m : OccupationState J N t) (f : Fibre m → ℝ) :
    orderedSwapSum m (fun η => f η - uniformAverage f) = orderedSwapSum m f := by
  unfold orderedSwapSum
  congr 1
  funext i
  congr 1
  funext j
  congr 1
  funext η
  ring

theorem uniformAverage_center (m : OccupationState J N t) (f : Fibre m → ℝ) :
    uniformAverage (fun η => f η - uniformAverage f) = 0 := by
  let : Nonempty (Fibre m) := ⟨⟨labelOfState m, profile_labelOfState m⟩⟩
  rw [uniformAverage_sub, uniformAverage_const, sub_self]

/-- The exact conditional variance subtraction on the actual occupation fibre. -/
theorem coordinate_residual_square (m : OccupationState J N t) (f : Fibre m → ℝ)
    (i : Fin N) :
    uniformAverage (fun η => (f η-coordinateProjection m f i (η.val.val i))^2) =
      uniformAverage (fun η => (f η)^2)-colourAverage m (fun a => (coordinateProjection m f i a)^2) := by
  rw [show (fun η => (f η-coordinateProjection m f i (η.val.val i))^2) =
    (fun η => (1*f η-1*coordinateProjection m f i (η.val.val i))^2) by
      funext η; ring]
  rw [uniformAverage_linear_square, coordinateProjection_pairing]
  rw [coordinate_average m (fun a => (coordinateProjection m f i a)^2) i]
  ring

theorem sum_coordinate_residual_square (m : OccupationState J N t) (f : Fibre m → ℝ) :
    (∑ i : Fin N, uniformAverage
      (fun η => (f η-coordinateProjection m f i (η.val.val i))^2)) =
      (N : ℝ)*uniformAverage (fun η => (f η)^2)-projectionSquareSum m f := by
  simp only [coordinate_residual_square, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, projectionSquareSum]

/-- Deletion and insertion preserve the actual transpositions on unconditioned sites. -/
theorem insertedFibre_swap {n : ℕ} {m : OccupationState J (n+1) t}
    (ξ : Fibre m) (i : Fin (n+1)) (ζ : Fibre (deletedProfile ξ i)) (j k : Fin n) :
    insertedFibre ξ i (fibrePermutation (Equiv.swap j k) (deletedProfile ξ i) ζ) =
      fibrePermutation (Equiv.swap (i.succAbove j) (i.succAbove k)) m (insertedFibre ξ i ζ) := by
  apply Subtype.ext
  apply Subtype.ext
  funext l
  by_cases hl : l = i
  · subst l
    change (Fin.insertNth (α := fun _ : Fin (n+1) => MeshIndex J) i (ξ.val.val i) _ ) i =
      (Fin.insertNth (α := fun _ : Fin (n+1) => MeshIndex J) i (ξ.val.val i) ζ.val.val) (Equiv.swap (i.succAbove j) (i.succAbove k) i)
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.ne_succAbove i j) (Fin.ne_succAbove i k)]
    simp only [Fin.insertNth_apply_same]
  · obtain ⟨l', rfl⟩ := Fin.exists_succAbove_eq hl
    change (Fin.insertNth (α := fun _ : Fin (n+1) => MeshIndex J) i (ξ.val.val i) (ζ.val.val ∘ Equiv.swap j k)) (i.succAbove l') =
      (Fin.insertNth (α := fun _ : Fin (n+1) => MeshIndex J) i (ξ.val.val i) ζ.val.val)
        (Equiv.swap (i.succAbove j) (i.succAbove k) (i.succAbove l'))
    have h := congrFun (removeNth_swap (Fin.insertNth (α := fun _ : Fin (n+1) => MeshIndex J) i (ξ.val.val i) ζ.val.val) i j k) l'
    simpa only [Fin.removeNth, Function.comp_apply, Fin.insertNth_apply_succAbove] using h.symm


/-- The zero- and one-particle cases are genuine singleton permutation orbits. -/
theorem localVariance_of_subsingleton_index [Subsingleton (Fin N)]
    (m : OccupationState J N t) (f : Fibre m → ℝ) : localVariance m f = 0 := by
  let : Nonempty (Fibre m) := ⟨⟨labelOfState m, profile_labelOfState m⟩⟩
  have hm (ξ : Fibre m) : uniformAverage f = f ξ := by
    rw [uniformAverage_permutations m f ξ]
    have he : (fun σ : Equiv.Perm (Fin N) => f (fibrePermutation σ m ξ)) =
        fun _ => f ξ := by
      funext σ
      have hσ : σ = Equiv.refl (Fin N) := Equiv.ext fun i => Subsingleton.elim _ _
      rw [hσ, fibrePermutation_refl]
    rw [he, uniformAverage_const]
  unfold localVariance
  have he : (fun η => (f η-uniformAverage f)^2) = fun _ => (0 : ℝ) := by
    funext η
    rw [hm η]
    ring
  rw [he, uniformAverage_const]

/-- There are exactly the identity and the unique nontrivial transposition
on two actual particle positions. -/
theorem finTwo_permutations (σ : Equiv.Perm (Fin 2)) :
    σ = Equiv.refl (Fin 2) ∨ σ = Equiv.swap (0 : Fin 2) 1 := by
  have hval (i : Fin 2) : i = 0 ∨ i = 1 := by
    have hi := i.isLt
    by_cases h : i.val = 0
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext (by omega))
  rcases hval (σ 0) with h | h
  · left
    apply Equiv.ext
    intro i
    rcases hval i with rfl | rfl
    · exact h
    · rcases hval (σ 1) with h1 | h1
      · have he := σ.injective (h1.trans h.symm)
        norm_num at he
      · exact h1
  · right
    apply Equiv.ext
    intro i
    rcases hval i with rfl | rfl
    · simpa only [Equiv.swap_apply_left] using h
    · rcases hval (σ 1) with h1 | h1
      · simpa only [Equiv.swap_apply_right] using h1
      · have he := σ.injective (h1.trans h.symm)
        norm_num at he

theorem uniformAverage_two (m : OccupationState J 2 t) (f : Fibre m → ℝ)
    (ξ : Fibre m) :
    uniformAverage f = (f ξ + f (fibrePermutation (Equiv.swap 0 1) m ξ))/2 := by
  classical
  have hne : Equiv.refl (Fin 2) ≠ Equiv.swap (0 : Fin 2) 1 := by
    intro h
    have hh := congrArg (fun σ : Equiv.Perm (Fin 2) => σ 0) h
    norm_num at hh
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {Equiv.refl (Fin 2), Equiv.swap (0 : Fin 2) 1} := by
    ext σ
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact finTwo_permutations σ
  rw [uniformAverage_permutations m f ξ]
  unfold uniformAverage
  rw [hu, Finset.sum_pair hne]
  simp only [fibrePermutation_refl, Fintype.card_perm, Fintype.card_fin]
  norm_num

/-- The sharp two-particle base, proved by the literal two-element orbit. -/
theorem localVariance_two (m : OccupationState J 2 t) (f : Fibre m → ℝ) :
    4*(2 : ℝ)*localVariance m f = orderedSwapSum m f := by
  have he (ξ : Fibre m) : (f ξ-uniformAverage f)^2 =
      (1/4 : ℝ)*(f (fibrePermutation (Equiv.swap 0 1) m ξ)-f ξ)^2 := by
    rw [uniformAverage_two m f ξ]
    ring
  have hv : localVariance m f = (1/4 : ℝ)*uniformAverage
      (fun ξ => (f (fibrePermutation (Equiv.swap 0 1) m ξ)-f ξ)^2) := by
    unfold localVariance
    simp_rw [he]
    rw [uniformAverage_mul]
  have hz : uniformAverage (fun _ : Fibre m => (0 : ℝ)) = 0 := by
    simp only [uniformAverage, Finset.sum_const_zero, zero_div]
  rw [hv]
  unfold orderedSwapSum
  simp only [Fin.sum_univ_two, Equiv.swap_self, fibrePermutation_refl, sub_self,
    zero_pow (by decide : 2 ≠ 0), hz, zero_add, add_zero, Equiv.swap_comm (1 : Fin 2) 0]
  ring


theorem uniformAverage_mono {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ}
    (h : ∀ x, f x ≤ g x) : uniformAverage f ≤ uniformAverage g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) (Nat.cast_nonneg _)

/-- Tower identity for the genuine coordinate conditional average. -/
theorem coordinateProjection_tower (m : OccupationState J N t) (f : Fibre m → ℝ)
    (i : Fin N) :
    uniformAverage (fun η : Fibre m => coordinateProjection m f i (η.val.val i)) = uniformAverage f := by
  rw [coordinate_average, coordinateProjection_mean]

/-- The smaller-particle Poincare inequality is transported to the actual
conditional law through the proved deletion bijection and swap commutation. -/
theorem conditional_poincare_of_smaller {n : ℕ}
    (ih : ∀ (m' : OccupationState J n 1) (g : Fibre m' → ℝ),
      4*(n : ℝ)*localVariance m' g ≤ orderedSwapSum m' g)
    (m : OccupationState J (n+1) t) (f : Fibre m → ℝ) (i : Fin (n+1)) :
    4*(n : ℝ)*uniformAverage
      (fun η => (f η-coordinateProjection m f i (η.val.val i))^2) ≤
      ∑ j : Fin n, ∑ k : Fin n, uniformAverage
        (fun η => (f (fibrePermutation (Equiv.swap (i.succAbove j) (i.succAbove k)) m η)-f η)^2) := by
  let h : Fibre m → ℝ := fun η => (f η-coordinateProjection m f i (η.val.val i))^2
  let g : Fin n → Fin n → Fibre m → ℝ := fun j k η =>
    (f (fibrePermutation (Equiv.swap (i.succAbove j) (i.succAbove k)) m η)-f η)^2
  have hp (ξ : Fibre m) :
      4*(n : ℝ)*coordinateProjection m h i (ξ.val.val i) ≤
        ∑ j : Fin n, ∑ k : Fin n, coordinateProjection m (g j k) i (ξ.val.val i) := by
    have hsmall := ih (deletedProfile ξ i) (fun ζ => f (insertedFibre ξ i ζ))
    have hm := conditionalAverage_deletion ξ i f
    have hv : coordinateProjection m h i (ξ.val.val i) =
        localVariance (deletedProfile ξ i) (fun ζ => f (insertedFibre ξ i ζ)) := by
      unfold coordinateProjection
      rw [conditionalAverage_deletion ξ i h]
      unfold localVariance
      apply congrArg uniformAverage
      funext ζ
      have hi : (insertedFibre ξ i ζ).val.val i = ξ.val.val i :=
        Fin.insertNth_apply_same (α := fun _ => MeshIndex J) i _ _
      dsimp only [h]
      rw [hi]
      change (f (insertedFibre ξ i ζ)-conditionalAverage
        (fun η : Fibre m => η.val.val i) f (ξ.val.val i))^2 = _
      rw [hm]
    have hg (j k : Fin n) : coordinateProjection m (g j k) i (ξ.val.val i) =
        uniformAverage (fun ζ : Fibre (deletedProfile ξ i) =>
          (f (insertedFibre ξ i (fibrePermutation (Equiv.swap j k) (deletedProfile ξ i) ζ))-
            f (insertedFibre ξ i ζ))^2) := by
      unfold coordinateProjection
      rw [conditionalAverage_deletion ξ i (g j k)]
      apply congrArg uniformAverage
      funext ζ
      simp only [g, insertedFibre_swap]
    rw [hv]
    simp_rw [hg]
    exact hsmall
  have hh := uniformAverage_mono hp
  rw [uniformAverage_mul, coordinateProjection_tower] at hh
  simp_rw [uniformAverage_sum, coordinateProjection_tower] at hh
  exact hh

/-- A genuine finite count: every off-diagonal ordered transposition is
retained at exactly N-2 choices of the deleted particle. -/
theorem sum_deleted_pairs {n : ℕ} (a : Fin (n+1) → Fin (n+1) → ℝ)
    (ha : ∀ i, a i i = 0) :
    (∑ i : Fin (n+1), ∑ j : Fin n, ∑ k : Fin n,
      a (i.succAbove j) (i.succAbove k)) =
      ((n : ℝ)-1)*(∑ j : Fin (n+1), ∑ k : Fin (n+1), a j k) := by
  have hp (i : Fin (n+1)) :
      (∑ j : Fin n, ∑ k : Fin n, a (i.succAbove j) (i.succAbove k)) =
      (∑ j : Fin (n+1), ∑ k : Fin (n+1), a j k) -
        (∑ k : Fin (n+1), a i k) - (∑ j : Fin (n+1), a j i) := by
    have houter := Fin.sum_univ_succAbove (fun j => ∑ k : Fin (n+1), a j k) i
    have hcol := Fin.sum_univ_succAbove (fun j => a j i) i
    have hinner (j : Fin n) := Fin.sum_univ_succAbove (fun k => a (i.succAbove j) k) i
    simp_rw [hinner] at houter
    rw [Finset.sum_add_distrib] at houter
    rw [ha i, zero_add] at hcol
    linarith only [houter, hcol]
  simp_rw [hp]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_comm (f := fun i j => a j i)]
  push_cast
  ring

/-- The exact deletion induction step, with the projection correction and
all finite edge multiplicities proved rather than assumed. -/
theorem local_poincare_step {n : ℕ} (hn : 2 ≤ n)
    (ih : ∀ (m' : OccupationState J n 1) (g : Fibre m' → ℝ),
      4*(n : ℝ)*localVariance m' g ≤ orderedSwapSum m' g)
    (m : OccupationState J (n+1) t) (f : Fibre m → ℝ) :
    4*((n+1 : ℕ) : ℝ)*localVariance m f ≤ orderedSwapSum m f := by
  let g : Fibre m → ℝ := fun η => f η-uniformAverage f
  have hmean : uniformAverage g = 0 := uniformAverage_center m f
  have hf := coordinate_projection_bound m (by omega) g hmean
  have hp := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n+1)))) =>
    conditional_poincare_of_smaller ih m g i)
  rw [← Finset.mul_sum, sum_coordinate_residual_square] at hp
  have ha (i : Fin (n+1)) : uniformAverage
      (fun η => (g (fibrePermutation (Equiv.swap i i) m η)-g η)^2) = 0 := by
    simp only [Equiv.swap_self, fibrePermutation_refl, sub_self,
      zero_pow (by decide : 2 ≠ 0), uniformAverage, Finset.sum_const_zero, zero_div]
  rw [sum_deleted_pairs (fun j k : Fin (n+1) => uniformAverage
    (fun η : Fibre m => (g (fibrePermutation (Equiv.swap j k) m η)-g η)^2)) ha] at hp
  have henergy : (∑ j : Fin (n+1), ∑ k : Fin (n+1), uniformAverage
      (fun η => (g (fibrePermutation (Equiv.swap j k) m η)-g η)^2)) = orderedSwapSum m f :=
    orderedSwapSum_center m f
  rw [henergy] at hp
  have hv : uniformAverage (fun η => (g η)^2) = localVariance m f := rfl
  rw [hv] at hp hf
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hmult : ((n : ℝ)-1)*(4*((n+1 : ℕ) : ℝ)*localVariance m f) ≤
      ((n : ℝ)-1)*orderedSwapSum m f := by
    push_cast at hp hf ⊢
    nlinarith only [hp, hf]
  by_contra hh
  have hpos := mul_pos (sub_pos.mpr hn') (sub_pos.mpr (lt_of_not_ge hh))
  nlinarith only [hmult, hpos]


theorem orderedSwapSum_nonneg (m : OccupationState J N t) (f : Fibre m → ℝ) :
    0 ≤ orderedSwapSum m f :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    uniformAverage_nonneg fun _ => sq_nonneg _

/-- Sharp Poincare inequality on every actual occupation fibre. The induction
uses the genuine deletion law, explicit small-size orbits, and the proved
negative covariance; no spectral-gap input is used. -/
theorem local_poincare (m : OccupationState J N t) (f : Fibre m → ℝ) :
    4*(N : ℝ)*localVariance m f ≤ orderedSwapSum m f := by
  induction N using Nat.strong_induction_on generalizing t with
  | h N ih =>
    rcases N with _ | N
    · simpa only [Nat.cast_zero, mul_zero, zero_mul] using orderedSwapSum_nonneg m f
    rcases N with _ | N
    · let : Subsingleton (Fin (0+1)) := ⟨fun x y => Fin.ext (by
        have hx := x.isLt
        have hy := y.isLt
        omega)⟩
      rw [localVariance_of_subsingleton_index, mul_zero]
      exact orderedSwapSum_nonneg m f
    rcases N with _ | n
    · exact (localVariance_two m f).le
    · apply local_poincare_step (by omega)
      intro m' g
      exact ih (n+2) (by omega) m' g

/-- Explicit conversion from the ordered form to the source's once-counted
unordered transpositions, including the vanishing diagonal. -/
theorem sum_ordered_eq_twice_upper (a : Fin N → Fin N → ℝ)
    (hs : ∀ i j, a i j = a j i) (hd : ∀ i, a i i = 0) :
    (∑ i, ∑ j, a i j) = 2*(∑ i, ∑ j, if i < j then a i j else 0) := by
  let b : Fin N → Fin N → ℝ := fun i j => if i < j then a i j else 0
  have he (i j : Fin N) : a i j = b i j + b j i := by
    rcases lt_trichotomy i j with hij | hij | hij
    · simp only [b, ite_eq_left hij, ite_eq_right (not_lt.mpr hij.le), add_zero]
    · subst j
      simp only [b, lt_self_iff_false, ite_false, hd, add_zero]
    · simp only [b, ite_eq_right (not_lt.mpr hij.le), ite_eq_left hij, zero_add]
      exact hs i j
  have hc : (∑ i, ∑ j, b j i) = ∑ i, ∑ j, b i j := Finset.sum_comm
  calc
    _ = ∑ i, ∑ j, (b i j+b j i) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => he i j
    _ = 2*(∑ i, ∑ j, b i j) := by
      simp only [Finset.sum_add_distrib]
      rw [hc]
      ring
    _ = _ := rfl

theorem orderedSwapSum_eq_source_sum (F : LabelState J N t → ℝ)
    (m : OccupationState J N t) :
    orderedSwapSum m (fun η => F η.val) =
      2*(∑ i : Fin N, ∑ j : Fin N, if i < j then fibreAverage
        (fun η => (F (permutedLabel (Equiv.swap i j) η)-F η)^2) m else 0) := by
  unfold orderedSwapSum
  have hs (i j : Fin N) : uniformAverage (fun η : Fibre m =>
      (F (fibrePermutation (Equiv.swap i j) m η).val-F η.val)^2) =
      uniformAverage (fun η : Fibre m =>
        (F (fibrePermutation (Equiv.swap j i) m η).val-F η.val)^2) := by
    rw [Equiv.swap_comm i j]
  have hd (i : Fin N) : uniformAverage (fun η : Fibre m =>
      (F (fibrePermutation (Equiv.swap i i) m η).val-F η.val)^2) = 0 := by
    simp only [Equiv.swap_self, fibrePermutation_refl, sub_self,
      zero_pow (by decide : 2 ≠ 0), uniformAverage, Finset.sum_const_zero, zero_div]
  exact sum_ordered_eq_twice_upper _ hs hd

/-- Source proposition `multislice-PI`, with its exact 1/(2N) unordered form.
It remains valid at N=0 by the actual singleton-fibre convention. -/
theorem multislice_poincare (F : LabelState J N t → ℝ) (m : OccupationState J N t) :
    fibreVariance F m ≤ transpositionEnergy F m := by
  by_cases hN : N = 0
  · subst N
    have hv := localVariance_of_subsingleton_index m (fun η => F η.val)
    change fibreVariance F m = 0 at hv
    rw [hv]
    exact transpositionEnergy_nonneg F m
  · have hn : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
    have hp := local_poincare m (fun η => F η.val)
    rw [orderedSwapSum_eq_source_sum] at hp
    change 4*(N : ℝ)*fibreVariance F m ≤ _ at hp
    unfold transpositionEnergy
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*(N : ℝ))).mpr
    nlinarith only [hp]

end PeriodicAttractiveLogGas.MultislicePoincare
