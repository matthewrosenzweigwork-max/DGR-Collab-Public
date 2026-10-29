import LeanResearch.PeriodicAttractiveLogGas.MultisliceEntropyRecursion
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Actual occupied-color/region recursion for Salez's ordinary multislice LSI.
The two-color theorem is proved in MultisliceEntropyRecursion. Literal region
bijections, the two energy counts, and strong induction discharge all recursive
inputs. The final theorem uses the actual minimum positive multiplicity and the
source once-counted transposition form. Root verification statuses are separate. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.MultisliceColourRecursion
open MeshCells LabelOccupations DiscreteOccupationIdentities FibreProjection
open FibreEntropy MultislicePoincare MultisliceLogSobolev MultisliceEntropyRecursion
open LabelExchangeability
variable {J N : ℕ} {t : ℝ}

/-- Literal recoloring: retain color a and merge every other color into b. -/
def coarsen (a b : MeshIndex J) (η : LabelVector J N) : LabelVector J N :=
  fun i => if η i = a then a else b

theorem coarsen_permute (a b : MeshIndex J) (η : LabelVector J N)
    (σ : Equiv.Perm (Fin N)) : coarsen a b (η ∘ σ) = coarsen a b η ∘ σ := rfl

theorem coarsen_occupation_eq (a b : MeshIndex J) {η ζ : LabelVector J N}
    (h : occupation η = occupation ζ) : occupation (coarsen a b η) = occupation (coarsen a b ζ) := by
  obtain ⟨σ, hσ⟩ := exists_permutation_of_occupation_eq h
  rw [← hσ, coarsen_permute, occupation_permute]

/-- Actual coarsened profile, at cap one which contains every particle word. -/
def coarsenedProfile (m : OccupationState J N t) (a b : MeshIndex J) : OccupationState J N 1 :=
  profile (unitCapLabel (coarsen a b (labelOfState m).val))

def coarsenedFibre (m : OccupationState J N t) (a b : MeshIndex J) (η : Fibre m) :
    Fibre (coarsenedProfile m a b) :=
  ⟨unitCapLabel (coarsen a b η.val.val), by
    apply Subtype.ext
    change occupation (coarsen a b η.val.val) = occupation (coarsen a b (labelOfState m).val)
    apply coarsen_occupation_eq
    exact (congrArg Subtype.val η.property).trans
      (congrArg Subtype.val (profile_labelOfState m)).symm⟩

@[simp] theorem coarsenedFibre_apply (m : OccupationState J N t) (a b : MeshIndex J)
    (η : Fibre m) (i : Fin N) :
    (coarsenedFibre m a b η).val.val i = if η.val.val i = a then a else b := rfl

theorem coarsenedFibre_permutation (m : OccupationState J N t) (a b : MeshIndex J)
    (σ : Equiv.Perm (Fin N)) (η : Fibre m) :
    coarsenedFibre m a b (fibrePermutation σ m η) =
      fibrePermutation σ (coarsenedProfile m a b) (coarsenedFibre m a b η) := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- The binary pushforward is genuinely uniform. Both sides are derived
from the actual particle-permutation orbit averages; no uniform-law premise is used. -/
theorem coarsened_average (m : OccupationState J N t) (a b : MeshIndex J)
    (H : Fibre (coarsenedProfile m a b) → ℝ) :
    uniformAverage (fun η : Fibre m => H (coarsenedFibre m a b η)) = uniformAverage H := by
  let ξ : Fibre m := ⟨labelOfState m, profile_labelOfState m⟩
  calc
    _ = uniformAverage (fun σ : Equiv.Perm (Fin N) =>
        H (coarsenedFibre m a b (fibrePermutation σ m ξ))) :=
      uniformAverage_permutations m (fun η => H (coarsenedFibre m a b η)) ξ
    _ = uniformAverage (fun σ : Equiv.Perm (Fin N) =>
        H (fibrePermutation σ (coarsenedProfile m a b) (coarsenedFibre m a b ξ))) := by
      apply congrArg uniformAverage
      funext σ
      rw [coarsenedFibre_permutation]
    _ = uniformAverage H :=
      (uniformAverage_permutations (coarsenedProfile m a b) H (coarsenedFibre m a b ξ)).symm

theorem coarsened_count_left (m : OccupationState J N t) (a b : MeshIndex J) (hab : a ≠ b) :
    (coarsenedProfile m a b).val a = m.val a := by
  classical
  change occupation (coarsen a b (labelOfState m).val) a = m.val a
  calc
    _ = occupation (labelOfState m).val a := by
      rw [occupation_eq_sum, occupation_eq_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : (labelOfState m).val i = a
      · simp only [coarsen, hi, ite_eq_left]
      · simp only [coarsen, hi, ite_false, Ne.symm hab]
    _ = m.val a := congrFun (congrArg Subtype.val (profile_labelOfState m)) a

theorem coarsened_two_colours (m : OccupationState J N t) (a b : MeshIndex J) :
    ∀ c, 0 < (coarsenedProfile m a b).val c → c = a ∨ c = b := by
  intro c hc
  change 0 < occupation (coarsen a b (labelOfState m).val) c at hc
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hc
  have he : coarsen a b (labelOfState m).val i = c := (Finset.mem_filter.mp hi).2
  unfold coarsen at he
  split_ifs at he
  · exact Or.inl he.symm
  · exact Or.inr he.symm

theorem coarsened_count_right (m : OccupationState J N t) (a b : MeshIndex J) (hab : a ≠ b) :
    (coarsenedProfile m a b).val b = N-m.val a := by
  have hh := two_colour_total (coarsenedProfile m a b) a b hab (coarsened_two_colours m a b)
  rw [coarsened_count_left m a b hab] at hh
  omega

/-- The actual region fibre is the set of original words with one specified
coarsened word. Thus all conditioning coordinates are retained literally. -/
abbrev RegionFibre (m : OccupationState J N t) (a b : MeshIndex J)
    (z : Fibre (coarsenedProfile m a b)) := CoordinateFibre (coarsenedFibre m a b) z

def regionAverage (m : OccupationState J N t) (a b : MeshIndex J)
    (f : Fibre m → ℝ) : Fibre (coarsenedProfile m a b) → ℝ :=
  conditionalAverage (coarsenedFibre m a b) f

/-- Exact finite pushforward sum, including empty unused coordinate fibres. -/
theorem uniformAverage_comp {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] [DecidableEq Λ]
    (X : Ω → Λ) (H : Λ → ℝ) :
    uniformAverage (fun x => H (X x)) = ∑ a, marginalWeight X a*H a := by
  unfold uniformAverage
  rw [sum_coordinate_fibres X (fun x => H (X x)), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  have he : (∑ x : CoordinateFibre X a, H (X x.val)) = ∑ _ : CoordinateFibre X a, H a :=
    Finset.sum_congr rfl fun x _ => by rw [x.property]
  rw [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold marginalWeight
  ring

/-- Uniformity of every actual region marginal is proved from the pushforward. -/
theorem region_marginal (m : OccupationState J N t) (a b : MeshIndex J)
    (z : Fibre (coarsenedProfile m a b)) :
    marginalWeight (coarsenedFibre m a b) z = 1/(Fintype.card (Fibre (coarsenedProfile m a b)) : ℝ) := by
  classical
  have hh := coarsened_average m a b (fun z' => if z' = z then (1 : ℝ) else 0)
  rw [uniformAverage_comp (coarsenedFibre m a b)
    (fun z' : Fibre (coarsenedProfile m a b) => if z' = z then (1 : ℝ) else 0)] at hh
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hh
  unfold uniformAverage at hh
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hh

/-- Exact region entropy chain for the actual original word law and the
actual uniform coarsened law. No conditional entropy or normalization is assumed. -/
theorem region_entropy_chain (m : OccupationState J N t) (a b : MeshIndex J) (f : Fibre m → ℝ) :
    uniformEntropy f =
      uniformAverage (fun z : Fibre (coarsenedProfile m a b) =>
        uniformEntropy (fun η : RegionFibre m a b z => f η.val)) +
      uniformEntropy (regionAverage m a b f) := by
  have hh := coordinate_entropy_chain (coarsenedFibre m a b) f
  unfold finiteEntropy at hh
  simp_rw [region_marginal] at hh
  simp only [one_div_mul_eq_div, ← Finset.sum_div] at hh
  exact hh

/-- The literal transposition acts involutively on each original fibre. -/
theorem fibreSwap_involutive (m : OccupationState J N t) (i j : Fin N) (η : Fibre m) :
    fibrePermutation (Equiv.swap i j) m (fibrePermutation (Equiv.swap i j) m η) = η := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  simp only [fibrePermutation_apply_coordinate, Equiv.swap_apply_self]

/-- Swapping particle sites transports one actual color-region fibre
bijectively onto the swapped region. -/
def regionSwap (m : OccupationState J N t) (a b : MeshIndex J)
    (i j : Fin N) (z : Fibre (coarsenedProfile m a b)) :
    RegionFibre m a b z ≃
      RegionFibre m a b (fibrePermutation (Equiv.swap i j) (coarsenedProfile m a b) z) where
  toFun η := ⟨fibrePermutation (Equiv.swap i j) m η.val, by
    rw [coarsenedFibre_permutation, η.property]⟩
  invFun η := ⟨fibrePermutation (Equiv.swap i j) m η.val, by
    rw [coarsenedFibre_permutation, η.property, fibreSwap_involutive]⟩
  left_inv η := Subtype.ext (fibreSwap_involutive m i j η.val)
  right_inv η := Subtype.ext (fibreSwap_involutive m i j η.val)

/-- The square-root conditional means contract under the actual uniform
region coupling. This uses neither a conditional-law nor an energy premise. -/
theorem region_swap_contraction (m : OccupationState J N t) (a b : MeshIndex J)
    (f : Fibre m → ℝ) (hf : ∀ η, 0 ≤ f η) (i j : Fin N)
    (z : Fibre (coarsenedProfile m a b)) :
    (Real.sqrt (regionAverage m a b f
      (fibrePermutation (Equiv.swap i j) (coarsenedProfile m a b) z))-
      Real.sqrt (regionAverage m a b f z))^2 ≤
    conditionalAverage (coarsenedFibre m a b)
      (fun η => (Real.sqrt (f (fibrePermutation (Equiv.swap i j) m η))-
        Real.sqrt (f η))^2) z := by
  have hh := reverse_sqrt_uniform_equiv (regionSwap m a b i j z)
    (fun η => f η.val) (fun η => f η.val) (fun η => hf η.val) (fun η => hf η.val)
  change (Real.sqrt (regionAverage m a b f z)-
    Real.sqrt (regionAverage m a b f
      (fibrePermutation (Equiv.swap i j) (coarsenedProfile m a b) z)))^2 ≤
    conditionalAverage (coarsenedFibre m a b)
      (fun η => (Real.sqrt (f η)-
        Real.sqrt (f (fibrePermutation (Equiv.swap i j) m η)))^2) z at hh
  calc
    _ = (Real.sqrt (regionAverage m a b f z)-
      Real.sqrt (regionAverage m a b f
        (fibrePermutation (Equiv.swap i j) (coarsenedProfile m a b) z)))^2 := by ring
    _ ≤ _ := hh
    _ = _ := by
      apply congrArg uniformAverage
      funext η
      dsimp only
      ring

/-- When the binary word changes, exactly one endpoint carries the retained
color in every original word in that region. -/
theorem region_crossing_count (m : OccupationState J N t) (a b : MeshIndex J)
    (i j : Fin N) (z : Fibre (coarsenedProfile m a b))
    (hz : z.val.val i ≠ z.val.val j) (η : RegionFibre m a b z) :
    (if η.val.val.val i = a then (1 : ℝ) else 0)+
      (if η.val.val.val j = a then (1 : ℝ) else 0) = 1 := by
  classical
  have hi := congrArg (fun w : Fibre (coarsenedProfile m a b) => w.val.val i) η.property
  have hj := congrArg (fun w : Fibre (coarsenedProfile m a b) => w.val.val j) η.property
  change (if η.val.val.val i = a then a else b) = z.val.val i at hi
  change (if η.val.val.val j = a then a else b) = z.val.val j at hj
  by_cases hia : η.val.val.val i = a <;> by_cases hja : η.val.val.val j = a
  · simp only [hia, hja, ite_true] at hi hj
    exact (hz (hi.symm.trans hj)).elim
  · simp only [hia, hja, ite_true, ite_false, add_zero]
  · simp only [hia, hja, ite_true, ite_false, zero_add]
  · simp only [hia, hja, ite_false] at hi hj
    exact (hz (hi.symm.trans hj)).elim

/-- The projected gradient is charged only to original swaps touching the
retained color. Swaps invisible in the binary word have exactly zero cost. -/
theorem region_swap_contraction_supported (m : OccupationState J N t) (a b : MeshIndex J)
    (f : Fibre m → ℝ) (hf : ∀ η, 0 ≤ f η) (i j : Fin N)
    (z : Fibre (coarsenedProfile m a b)) :
    (Real.sqrt (regionAverage m a b f
      (fibrePermutation (Equiv.swap i j) (coarsenedProfile m a b) z))-
      Real.sqrt (regionAverage m a b f z))^2 ≤
    conditionalAverage (coarsenedFibre m a b)
      (fun η => ((if η.val.val i = a then (1 : ℝ) else 0)+
          (if η.val.val j = a then (1 : ℝ) else 0))*
        (Real.sqrt (f (fibrePermutation (Equiv.swap i j) m η))-Real.sqrt (f η))^2) z := by
  classical
  by_cases hz : z.val.val i = z.val.val j
  · rw [fibrePermutation_swap_of_equal (coarsenedProfile m a b) i j z hz, sub_self,
      zero_pow (by decide : 2 ≠ 0)]
    apply uniformAverage_nonneg
    intro η
    exact mul_nonneg (add_nonneg (by split_ifs <;> positivity) (by split_ifs <;> positivity))
      (sq_nonneg _)
  · have hh := region_swap_contraction m a b f hf i j z
    have he : conditionalAverage (coarsenedFibre m a b)
        (fun η => ((if η.val.val i = a then (1 : ℝ) else 0)+
            (if η.val.val j = a then (1 : ℝ) else 0))*
          (Real.sqrt (f (fibrePermutation (Equiv.swap i j) m η))-Real.sqrt (f η))^2) z =
        conditionalAverage (coarsenedFibre m a b)
        (fun η => (Real.sqrt (f (fibrePermutation (Equiv.swap i j) m η))-
          Real.sqrt (f η))^2) z := by
      apply congrArg uniformAverage
      funext η
      dsimp only
      rw [region_crossing_count m a b i j z hz η, one_mul]
    rw [he]
    exact hh

/-- The actual positions not occupied by the retained color. -/
abbrev Remaining (ξ : LabelVector J N) (a : MeshIndex J) := {i : Fin N // ξ i ≠ a}

def remainingIndex (ξ : LabelVector J N) (a : MeshIndex J)
    (j : Fin (Fintype.card (Remaining ξ a))) : Fin N :=
  ((Fintype.equivFin (Remaining ξ a)).symm j).val

def remainingWord (ξ : LabelVector J N) (a : MeshIndex J) (η : LabelVector J N) :
    LabelVector J (Fintype.card (Remaining ξ a)) := fun j => η (remainingIndex ξ a j)

theorem remainingIndex_ne (ξ : LabelVector J N) (a : MeshIndex J)
    (j : Fin (Fintype.card (Remaining ξ a))) : ξ (remainingIndex ξ a j) ≠ a :=
  ((Fintype.equivFin (Remaining ξ a)).symm j).property

/-- Restriction preserves every other color count, and removes exactly the
retained color. The formula comes from the literal occupation indicator sum. -/
theorem remaining_count (ξ η : LabelVector J N) (a c : MeshIndex J)
    (hpat : ∀ i, η i = a ↔ ξ i = a) :
    occupation (remainingWord ξ a η) c = if c = a then 0 else occupation η c := by
  classical
  rw [occupation_eq_sum]
  have he := Equiv.sum_comp (Fintype.equivFin (Remaining ξ a)).symm
    (fun i : Remaining ξ a => if η i.val = c then (1 : ℕ) else 0)
  change (∑ j : Fin (Fintype.card (Remaining ξ a)),
    if remainingWord ξ a η j = c then (1 : ℕ) else 0) =
    ∑ i : Remaining ξ a, if η i.val = c then (1 : ℕ) else 0 at he
  rw [he]
  have hs := Finset.sum_subtype (p := fun i : Fin N => ξ i ≠ a) (F := inferInstance)
    (Finset.univ.filter (fun i : Fin N => ξ i ≠ a)) (by intro i; simp)
    (fun i : Fin N => if η i = c then (1 : ℕ) else 0)
  rw [← hs, Finset.sum_filter]
  by_cases hc : c = a
  · subst c
    rw [ite_eq_left rfl]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : ξ i = a
    · simp [hi]
    · have hh : η i ≠ a := fun h => hi ((hpat i).mp h)
      simp [hi, hh]
  · rw [ite_eq_right hc, occupation_eq_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : ξ i = a
    · have hh : η i = a := (hpat i).mpr hi
      simp [hi, hh, Ne.symm hc]
    · simp [hi]

/-- The smaller profile is constructed from an actual restricted word. -/
def remainingProfile {m : OccupationState J N t} (ξ : Fibre m) (a : MeshIndex J) :
    OccupationState J (Fintype.card (Remaining ξ.val.val a)) 1 :=
  profile (unitCapLabel (remainingWord ξ.val.val a ξ.val.val))

theorem remainingProfile_count {m : OccupationState J N t} (ξ : Fibre m)
    (a c : MeshIndex J) : (remainingProfile ξ a).val c = if c = a then 0 else m.val c := by
  change occupation (remainingWord ξ.val.val a ξ.val.val) c = _
  rw [remaining_count ξ.val.val ξ.val.val a c (fun _ => Iff.rfl)]
  rw [show occupation ξ.val.val = m.val from congrArg Subtype.val ξ.property]

/-- Equality of literal binary words identifies the entire retained-color
region, not merely its cardinality. -/
theorem region_pattern {m : OccupationState J N t} (ξ : Fibre m) (a b : MeshIndex J)
    (hab : a ≠ b) (η : RegionFibre m a b (coarsenedFibre m a b ξ)) :
    ∀ i, η.val.val.val i = a ↔ ξ.val.val i = a := by
  intro i
  have hh := congrArg (fun z : Fibre (coarsenedProfile m a b) => z.val.val i) η.property
  change (if η.val.val.val i = a then a else b) = (if ξ.val.val i = a then a else b) at hh
  by_cases hi : η.val.val.val i = a <;> by_cases hj : ξ.val.val i = a
  · exact iff_of_true hi hj
  · simp only [hi, hj, ite_true, ite_false] at hh
    exact (hab hh).elim
  · simp only [hi, hj, ite_true, ite_false] at hh
    exact (hab hh.symm).elim
  · exact iff_of_false hi hj

/-- Restricting an actual region word produces precisely the smaller
occupation fibre; no profile or conditional-law assertion is an input. -/
def restrictRegion {m : OccupationState J N t} (ξ : Fibre m) (a b : MeshIndex J)
    (hab : a ≠ b) (η : RegionFibre m a b (coarsenedFibre m a b ξ)) :
    Fibre (remainingProfile ξ a) :=
  ⟨unitCapLabel (remainingWord ξ.val.val a η.val.val.val), by
    apply Subtype.ext
    funext c
    change occupation (remainingWord ξ.val.val a η.val.val.val) c = (remainingProfile ξ a).val c
    rw [remaining_count ξ.val.val η.val.val.val a c (region_pattern ξ a b hab η),
      remainingProfile_count]
    rw [show occupation η.val.val.val = m.val from congrArg Subtype.val η.val.property]⟩

/-- Insert the retained color on its original sites and the smaller word
on the actual ordered complement. -/
def insertRemaining (ξ : LabelVector J N) (a : MeshIndex J)
    (ζ : LabelVector J (Fintype.card (Remaining ξ a))) : LabelVector J N :=
  fun i => if h : ξ i = a then a else ζ (Fintype.equivFin (Remaining ξ a) ⟨i, h⟩)

theorem insertRemaining_at_remaining (ξ : LabelVector J N) (a : MeshIndex J)
    (ζ : LabelVector J (Fintype.card (Remaining ξ a)))
    (j : Fin (Fintype.card (Remaining ξ a))) :
    insertRemaining ξ a ζ (remainingIndex ξ a j) = ζ j := by
  unfold insertRemaining
  rw [dite_eq_right (remainingIndex_ne ξ a j)]
  have he : (⟨remainingIndex ξ a j, remainingIndex_ne ξ a j⟩ : Remaining ξ a) =
      (Fintype.equivFin (Remaining ξ a)).symm j := rfl
  rw [he, Equiv.apply_symm_apply]

theorem remaining_insert (ξ : LabelVector J N) (a : MeshIndex J)
    (ζ : LabelVector J (Fintype.card (Remaining ξ a))) :
    remainingWord ξ a (insertRemaining ξ a ζ) = ζ :=
  funext (insertRemaining_at_remaining ξ a ζ)

theorem insert_remaining (ξ η : LabelVector J N) (a : MeshIndex J)
    (hpat : ∀ i, η i = a ↔ ξ i = a) :
    insertRemaining ξ a (remainingWord ξ a η) = η := by
  funext i
  by_cases hi : ξ i = a
  · simp only [insertRemaining, dite_eq_left hi]
    exact ((hpat i).mpr hi).symm
  · simp only [insertRemaining, dite_eq_right hi, remainingWord, remainingIndex,
      Equiv.symm_apply_apply]

/-- A smaller actual fibre contains no occurrence of the removed color. -/
theorem remainingFibre_ne {m : OccupationState J N t} (ξ : Fibre m) (a : MeshIndex J)
    (ζ : Fibre (remainingProfile ξ a)) (j : Fin (Fintype.card (Remaining ξ.val.val a))) :
    ζ.val.val j ≠ a := by
  intro hj
  have hp := occupation_pos_at ζ.val.val j
  rw [hj] at hp
  have he := congrFun (congrArg Subtype.val ζ.property) a
  change occupation ζ.val.val a = (remainingProfile ξ a).val a at he
  rw [remainingProfile_count, ite_eq_left rfl] at he
  omega

theorem insertRemaining_pattern {m : OccupationState J N t} (ξ : Fibre m)
    (a : MeshIndex J) (ζ : Fibre (remainingProfile ξ a)) :
    ∀ i, insertRemaining ξ.val.val a ζ.val.val i = a ↔ ξ.val.val i = a := by
  intro i
  by_cases hi : ξ.val.val i = a
  · simp [insertRemaining, hi]
  · simp only [insertRemaining, dite_eq_right hi]
    exact iff_of_false (remainingFibre_ne ξ a ζ _) hi

/-- The literal insertion reconstructs every original occupation count. -/
theorem insertRemaining_occupation {m : OccupationState J N t} (ξ : Fibre m)
    (a : MeshIndex J) (ζ : Fibre (remainingProfile ξ a)) :
    occupation (insertRemaining ξ.val.val a ζ.val.val) = occupation ξ.val.val := by
  funext c
  by_cases hc : c = a
  · subst c
    rw [occupation_eq_sum, occupation_eq_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [insertRemaining_pattern ξ a ζ i]
  · have hh := remaining_count ξ.val.val (insertRemaining ξ.val.val a ζ.val.val) a c
      (insertRemaining_pattern ξ a ζ)
    rw [remaining_insert, ite_eq_right hc] at hh
    have he := congrFun (congrArg Subtype.val ζ.property) c
    change occupation ζ.val.val c = (remainingProfile ξ a).val c at he
    rw [remainingProfile_count, ite_eq_right hc] at he
    have hx := congrFun (congrArg Subtype.val ξ.property) c
    change occupation ξ.val.val c = m.val c at hx
    exact hh.symm.trans (he.trans hx.symm)

def insertedRegionFibre {m : OccupationState J N t} (ξ : Fibre m)
    (a : MeshIndex J) (ζ : Fibre (remainingProfile ξ a)) : Fibre m :=
  ⟨⟨insertRemaining ξ.val.val a ζ.val.val, by
    intro c
    rw [insertRemaining_occupation ξ a ζ]
    exact ξ.val.property c⟩, by
    apply Subtype.ext
    change occupation (insertRemaining ξ.val.val a ζ.val.val) = m.val
    rw [insertRemaining_occupation ξ a ζ]
    exact congrArg Subtype.val ξ.property⟩

/-- The conditioned original region is exactly the smaller multislice,
including the empty complement and all zero occupations. -/
def regionEquiv {m : OccupationState J N t} (ξ : Fibre m) (a b : MeshIndex J) (hab : a ≠ b) :
    RegionFibre m a b (coarsenedFibre m a b ξ) ≃ Fibre (remainingProfile ξ a) where
  toFun := restrictRegion ξ a b hab
  invFun ζ := ⟨insertedRegionFibre ξ a ζ, by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change (if insertRemaining ξ.val.val a ζ.val.val i = a then a else b) =
      (if ξ.val.val i = a then a else b)
    simp only [insertRemaining_pattern ξ a ζ i]⟩
  left_inv η := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact insert_remaining ξ.val.val η.val.val.val a (region_pattern ξ a b hab η)
  right_inv ζ := by
    apply Subtype.ext
    apply Subtype.ext
    exact remaining_insert ξ.val.val a ζ.val.val

/-- Entropy on the true region is transported through the actual insertion
bijection, with its uniform measure established by finite reindexing. -/
theorem region_entropy_remaining {m : OccupationState J N t} (ξ : Fibre m)
    (a b : MeshIndex J) (hab : a ≠ b) (f : Fibre m → ℝ) :
    uniformEntropy (fun η : RegionFibre m a b (coarsenedFibre m a b ξ) => f η.val) =
      uniformEntropy (fun ζ : Fibre (remainingProfile ξ a) => f (insertedRegionFibre ξ a ζ)) := by
  have hh := uniformEntropy_equiv (regionEquiv ξ a b hab).symm
    (fun η : RegionFibre m a b (coarsenedFibre m a b ξ) => f η.val)
  exact hh.symm

theorem remainingIndex_injective (ξ : LabelVector J N) (a : MeshIndex J) :
    Function.Injective (remainingIndex ξ a) := by
  intro j k h
  apply (Fintype.equivFin (Remaining ξ a)).symm.injective
  exact Subtype.ext h

/-- Every sum over the smaller index set is the literal original sum
restricted to the complement of the observed region. -/
theorem remaining_sum (ξ : LabelVector J N) (a : MeshIndex J) (g : Fin N → ℝ) :
    (∑ j : Fin (Fintype.card (Remaining ξ a)), g (remainingIndex ξ a j)) =
      ∑ i : Fin N, if ξ i ≠ a then g i else 0 := by
  classical
  have he := Equiv.sum_comp (Fintype.equivFin (Remaining ξ a)).symm
    (fun i : Remaining ξ a => g i.val)
  change (∑ j : Fin (Fintype.card (Remaining ξ a)), g (remainingIndex ξ a j)) =
    ∑ i : Remaining ξ a, g i.val at he
  rw [he]
  have hs := Finset.sum_subtype (p := fun i : Fin N => ξ i ≠ a) (F := inferInstance)
    (Finset.univ.filter (fun i : Fin N => ξ i ≠ a)) (by intro i; simp) g
  simpa only [Finset.sum_filter] using hs.symm

theorem remaining_double_sum (ξ : LabelVector J N) (a : MeshIndex J) (g : Fin N → Fin N → ℝ) :
    (∑ j : Fin (Fintype.card (Remaining ξ a)), ∑ k : Fin (Fintype.card (Remaining ξ a)),
      g (remainingIndex ξ a j) (remainingIndex ξ a k)) =
      ∑ i : Fin N, ∑ j : Fin N, if ξ i ≠ a ∧ ξ j ≠ a then g i j else 0 := by
  classical
  simp_rw [remaining_sum]
  rw [remaining_sum ξ a (fun i => ∑ j : Fin N, if ξ j ≠ a then g i j else 0)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : ξ i ≠ a
  · rw [ite_eq_left hi]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : ξ j ≠ a
    · rw [ite_eq_left hj, ite_eq_left (And.intro hi hj)]
    · rw [ite_eq_right hj, ite_eq_right (fun h => hj h.2)]
  · rw [ite_eq_right hi]
    symm
    apply Finset.sum_eq_zero
    intro j _
    rw [ite_eq_right (fun h => hi h.1)]

/-- Swaps of remaining sites commute with the genuine index embedding. -/
theorem remainingIndex_swap (ξ : LabelVector J N) (a : MeshIndex J)
    (j k l : Fin (Fintype.card (Remaining ξ a))) :
    Equiv.swap (remainingIndex ξ a j) (remainingIndex ξ a k) (remainingIndex ξ a l) =
      remainingIndex ξ a (Equiv.swap j k l) := by
  classical
  by_cases hj : l = j
  · subst l
    rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  · by_cases hk : l = k
    · subst l
      rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne
        (fun h => hj (remainingIndex_injective ξ a h))
        (fun h => hk (remainingIndex_injective ξ a h)), Equiv.swap_apply_of_ne_of_ne hj hk]

/-- Insertion commutes with exactly the transpositions whose endpoints are
outside the retained region. -/
theorem insertRemaining_swap (ξ : LabelVector J N) (a : MeshIndex J)
    (ζ : LabelVector J (Fintype.card (Remaining ξ a)))
    (j k : Fin (Fintype.card (Remaining ξ a))) :
    insertRemaining ξ a (ζ ∘ Equiv.swap j k) =
      insertRemaining ξ a ζ ∘ Equiv.swap (remainingIndex ξ a j) (remainingIndex ξ a k) := by
  classical
  funext i
  by_cases hi : ξ i = a
  · have hij : i ≠ remainingIndex ξ a j := fun h => remainingIndex_ne ξ a j (h ▸ hi)
    have hik : i ≠ remainingIndex ξ a k := fun h => remainingIndex_ne ξ a k (h ▸ hi)
    simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hij hik,
      insertRemaining, dite_eq_left hi]
  · let l : Fin (Fintype.card (Remaining ξ a)) := Fintype.equivFin (Remaining ξ a) ⟨i, hi⟩
    have hl : remainingIndex ξ a l = i := by
      simp only [remainingIndex, l, Equiv.symm_apply_apply]
    rw [← hl]
    simp only [Function.comp_apply, remainingIndex_swap, insertRemaining_at_remaining]

theorem insertedRegion_swap {m : OccupationState J N t} (ξ : Fibre m) (a : MeshIndex J)
    (ζ : Fibre (remainingProfile ξ a))
    (j k : Fin (Fintype.card (Remaining ξ.val.val a))) :
    insertedRegionFibre ξ a (fibrePermutation (Equiv.swap j k) (remainingProfile ξ a) ζ) =
      fibrePermutation (Equiv.swap (remainingIndex ξ.val.val a j) (remainingIndex ξ.val.val a k)) m
        (insertedRegionFibre ξ a ζ) := by
  apply Subtype.ext
  apply Subtype.ext
  exact insertRemaining_swap ξ.val.val a ζ.val.val j k

/-- Exact remaining particle number, including a full or empty retained region. -/
theorem remaining_card {m : OccupationState J N t} (ξ : Fibre m) (a : MeshIndex J) :
    Fintype.card (Remaining ξ.val.val a)+m.val a = N := by
  classical
  have hs := (remainingProfile ξ a).property.1
  simp only [remainingProfile_count] at hs
  have he : (∑ c, m.val c) = m.val a+(∑ c, if c = a then 0 else m.val c) := by
    calc
      _ = ∑ c, ((if c = a then m.val c else 0)+(if c = a then 0 else m.val c)) := by
        apply Finset.sum_congr rfl
        intro c _
        by_cases hc : c = a <;> simp [hc]
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [m.property.1, hs] at he
  omega

/-- Literal ordered transposition density retained after removing a color. -/
def retainedDensity (m : OccupationState J N t) (a : MeshIndex J) (g : Fibre m → ℝ)
    (η : Fibre m) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, if η.val.val i ≠ a ∧ η.val.val j ≠ a then
    (g (fibrePermutation (Equiv.swap i j) m η)-g η)^2 else 0

def retainedEnergy (m : OccupationState J N t) (a : MeshIndex J) (g : Fibre m → ℝ) : ℝ :=
  uniformAverage (retainedDensity m a g)

/-- Exact smaller-energy transport. Its mask, indices, and conditional
uniform measure all come from the proved restriction/insertion equivalence. -/
theorem remaining_energy {m : OccupationState J N t} (ξ : Fibre m)
    (a b : MeshIndex J) (hab : a ≠ b) (g : Fibre m → ℝ) :
    orderedSwapSum (remainingProfile ξ a) (fun ζ => g (insertedRegionFibre ξ a ζ)) =
      conditionalAverage (coarsenedFibre m a b) (retainedDensity m a g)
        (coarsenedFibre m a b ξ) := by
  have hp (ζ : Fibre (remainingProfile ξ a)) :
      (∑ j : Fin (Fintype.card (Remaining ξ.val.val a)),
        ∑ k : Fin (Fintype.card (Remaining ξ.val.val a)),
        (g (insertedRegionFibre ξ a
          (fibrePermutation (Equiv.swap j k) (remainingProfile ξ a) ζ))-
          g (insertedRegionFibre ξ a ζ))^2) =
      retainedDensity m a g (insertedRegionFibre ξ a ζ) := by
    simp_rw [insertedRegion_swap]
    rw [remaining_double_sum ξ.val.val a (fun i j =>
      (g (fibrePermutation (Equiv.swap i j) m (insertedRegionFibre ξ a ζ))-
        g (insertedRegionFibre ξ a ζ))^2)]
    unfold retainedDensity
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hi := insertRemaining_pattern ξ a ζ i
    have hj := insertRemaining_pattern ξ a ζ j
    change (if ξ.val.val i ≠ a ∧ ξ.val.val j ≠ a then _ else 0) =
      (if insertRemaining ξ.val.val a ζ.val.val i ≠ a ∧
        insertRemaining ξ.val.val a ζ.val.val j ≠ a then _ else 0)
    by_cases hx : ξ.val.val i ≠ a ∧ ξ.val.val j ≠ a
    · have hy : insertRemaining ξ.val.val a ζ.val.val i ≠ a ∧
          insertRemaining ξ.val.val a ζ.val.val j ≠ a :=
        ⟨fun h => hx.1 (hi.mp h), fun h => hx.2 (hj.mp h)⟩
      rw [ite_eq_left hx, ite_eq_left hy]
    · have hy : ¬(insertRemaining ξ.val.val a ζ.val.val i ≠ a ∧
          insertRemaining ξ.val.val a ζ.val.val j ≠ a) := by
        intro h
        exact hx ⟨fun h' => h.1 (hi.mpr h'), fun h' => h.2 (hj.mpr h')⟩
      rw [ite_eq_right hx, ite_eq_right hy]
  unfold orderedSwapSum
  simp_rw [← uniformAverage_sum]
  have he := congrArg uniformAverage (funext hp)
  refine he.trans ?_
  have hh := uniformAverage_equiv (regionEquiv ξ a b hab).symm
    (fun η : RegionFibre m a b (coarsenedFibre m a b ξ) => retainedDensity m a g η.val)
  exact hh

/-- The ordinary tower identity for the actual finite conditional average. -/
theorem conditionalAverage_tower {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] [DecidableEq Λ]
    (X : Ω → Λ) (g : Ω → ℝ) :
    uniformAverage (fun x => conditionalAverage X g (X x)) = uniformAverage g := by
  rw [uniformAverage_comp X (conditionalAverage X g), ← average_conditioning X g]

/-- The remaining-fibre entropy chain, expressed entirely on original words. -/
theorem remaining_entropy_chain (m : OccupationState J N t) (a b : MeshIndex J)
    (hab : a ≠ b) (f : Fibre m → ℝ) :
    uniformEntropy f =
      uniformAverage (fun ξ : Fibre m => uniformEntropy
        (fun ζ : Fibre (remainingProfile ξ a) => f (insertedRegionFibre ξ a ζ)))+
      uniformEntropy (regionAverage m a b f) := by
  have hh := region_entropy_chain m a b f
  rw [← coarsened_average m a b (fun z =>
    uniformEntropy (fun η : RegionFibre m a b z => f η.val))] at hh
  simp_rw [region_entropy_remaining _ a b hab f] at hh
  exact hh

/-- Averaging a genuinely proved smaller-fibre bound gives its exact
retained-edge contribution. This intermediate lemma is consumed by induction. -/
theorem averaged_remaining_bound (m : OccupationState J N t) (a b : MeshIndex J)
    (hab : a ≠ b) (f : Fibre m → ℝ) (K : ℝ)
    (hsmall : ∀ ξ : Fibre m,
      4*(Fintype.card (Remaining ξ.val.val a) : ℝ)*uniformEntropy
        (fun ζ : Fibre (remainingProfile ξ a) => f (insertedRegionFibre ξ a ζ)) ≤
      K*orderedSwapSum (remainingProfile ξ a)
        (fun ζ => Real.sqrt (f (insertedRegionFibre ξ a ζ)))) :
    4*((N : ℝ)-m.val a)*uniformAverage (fun ξ : Fibre m => uniformEntropy
      (fun ζ : Fibre (remainingProfile ξ a) => f (insertedRegionFibre ξ a ζ))) ≤
      K*retainedEnergy m a (fun η => Real.sqrt (f η)) := by
  have hc (ξ : Fibre m) : (Fintype.card (Remaining ξ.val.val a) : ℝ) = (N : ℝ)-m.val a := by
    have he : (Fintype.card (Remaining ξ.val.val a) : ℝ)+(m.val a : ℝ) = N := by
      exact_mod_cast remaining_card ξ a
    linarith
  have hh := uniformAverage_mono hsmall
  simp_rw [hc, remaining_energy _ a b hab (fun η => Real.sqrt (f η))] at hh
  rw [uniformAverage_mul, uniformAverage_mul, conditionalAverage_tower] at hh
  exact hh

/-- Elementary coefficient bound for at least three occupied colors.
This tangent-line adaptation of Salez Lemma 3.3 keeps its exact constant. -/
theorem weighted_binary_log {p K : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hK : 1 ≤ K) (hlog : -Real.log p ≤ K) :
    (1-p)*(-Real.log (p*(1-p))) ≤ K := by
  have hq : 0 < 1-p := sub_pos.mpr hp1
  have hh := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (inv_pos.mpr hq)) hq.le
  rw [Real.log_inv] at hh
  have he : (1-p)*((1-p)⁻¹-1) = p := by field_simp [hq.ne']; ring
  rw [he] at hh
  rw [Real.log_mul hp.ne' hq.ne']
  have h1 := mul_le_mul_of_nonneg_left hlog hq.le
  have h2 := mul_le_mul_of_nonneg_left hK hp.le
  nlinarith only [hh, h1, h2]

theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  have hh := Real.log_le_log (Real.exp_pos 1) Real.exp_one_lt_three.le
  simpa only [Real.log_exp] using hh

/-- The weighted binary coefficient needed in the color induction;
all denominators are positive and no endpoint quotient is evaluated. -/
theorem weighted_binary_ratio {r s k : ℝ} (hr : 0 < r) (hs : 0 < s) (hk : 0 < k)
    (hkr : k ≤ r) (hthree : 3*k ≤ r+s) :
    s/(r+s)*Real.log ((r+s)^2/(r*s)) ≤ Real.log ((r+s)/k) := by
  let p : ℝ := r/(r+s)
  have hn : 0 < r+s := add_pos hr hs
  have hp : 0 < p := div_pos hr hn
  have hp1 : p < 1 := (div_lt_one hn).mpr (by linarith)
  have hK : 1 ≤ Real.log ((r+s)/k) :=
    one_le_log_three.trans (Real.log_le_log (by norm_num)
      ((le_div_iff₀ hk).mpr hthree))
  have hlog : -Real.log p ≤ Real.log ((r+s)/k) := by
    dsimp only [p]
    rw [Real.log_div hr.ne' hn.ne', Real.log_div hn.ne' hk.ne']
    have hh := Real.log_le_log hk hkr
    linarith only [hh]
  have hh := weighted_binary_log hp hp1 hK hlog
  have hq : 1-p = s/(r+s) := by dsimp only [p]; field_simp; ring
  have he : (p*(1-p))⁻¹ = (r+s)^2/(r*s) := by
    rw [hq]
    dsimp only [p]
    field_simp
  have hl : -Real.log (p*(1-p)) = Real.log ((r+s)^2/(r*s)) := by
    rw [← he, Real.log_inv]
  rw [hl, hq] at hh
  exact hh

/-- The two-color base of the color induction uses both positive counts,
so its binary logarithm is at most twice the source logarithmic factor. -/
theorem binary_ratio_le {r s k : ℝ} (hr : 0 < r) (hs : 0 < s) (hk : 0 < k)
    (hkr : k ≤ r) (hks : k ≤ s) :
    Real.log ((r+s)^2/(r*s)) ≤ 2*Real.log ((r+s)/k) := by
  have hn : 0 < r+s := add_pos hr hs
  have hprod : k*k ≤ r*s := mul_le_mul hkr hks hk.le hr.le
  have hrat : (r+s)^2/(r*s) ≤ ((r+s)/k)^2 := by
    rw [div_pow]
    apply (div_le_div_iff₀ (mul_pos hr hs) (sq_pos_of_pos hk)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hprod (sq_nonneg (r+s))]
  have hh := Real.log_le_log (div_pos (sq_pos_of_pos hn) (mul_pos hr hs)) hrat
  rw [Real.log_pow] at hh
  norm_num at hh
  exact hh

/-- Only genuinely occupied colors participate in the recursion. -/
def occupiedColours (m : OccupationState J N t) : Finset (MeshIndex J) :=
  Finset.univ.filter (fun a => 0 < m.val a)

@[simp] theorem mem_occupiedColours (m : OccupationState J N t) (a : MeshIndex J) :
    a ∈ occupiedColours m ↔ 0 < m.val a := by simp [occupiedColours]

theorem word_colour_mem (m : OccupationState J N t) (η : Fibre m) (i : Fin N) :
    η.val.val i ∈ occupiedColours m := by
  rw [mem_occupiedColours]
  have hh := occupation_pos_at η.val.val i
  rw [show occupation η.val.val = m.val from congrArg Subtype.val η.property] at hh
  exact hh

theorem occupied_counts_sum (m : OccupationState J N t) :
    ∑ a ∈ occupiedColours m, m.val a = N := by
  classical
  calc
    _ = ∑ a, m.val a := by
      unfold occupiedColours
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : 0 < m.val a
      · rw [ite_eq_left ha]
      · rw [ite_eq_right ha]
        omega
    _ = N := m.property.1

theorem occupied_lower_total (m : OccupationState J N t) (k : ℕ)
    (hk : ∀ a, 0 < m.val a → k ≤ m.val a) :
    (occupiedColours m).card*k ≤ N := by
  have hh := Finset.sum_le_sum (fun a ha => hk a ((mem_occupiedColours m a).mp ha))
  change (∑ _a ∈ occupiedColours m, k) ≤ ∑ a ∈ occupiedColours m, m.val a at hh
  simpa only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, occupied_counts_sum] using hh

/-- Removing a color deletes exactly its occupied-color entry and creates none. -/
theorem remaining_occupiedColours {m : OccupationState J N t} (ξ : Fibre m) (a : MeshIndex J) :
    occupiedColours (remainingProfile ξ a) = (occupiedColours m).erase a := by
  classical
  ext c
  by_cases hc : c = a
  · subst c
    simp [mem_occupiedColours, remainingProfile_count]
  · simp [mem_occupiedColours, remainingProfile_count, hc]

theorem remaining_colour_card_lt {m : OccupationState J N t} (ξ : Fibre m) (a : MeshIndex J)
    (ha : 0 < m.val a) :
    (occupiedColours (remainingProfile ξ a)).card < (occupiedColours m).card := by
  rw [remaining_occupiedColours, Finset.card_erase_of_mem ((mem_occupiedColours m a).mpr ha)]
  have hh : 0 < (occupiedColours m).card :=
    Finset.card_pos.mpr ⟨a, (mem_occupiedColours m a).mpr ha⟩
  omega

/-- The zero- and one-color fibres really are singletons. -/
theorem fibre_subsingleton_of_colour_card (m : OccupationState J N t)
    (hcard : (occupiedColours m).card ≤ 1) : Subsingleton (Fibre m) := by
  constructor
  intro η ζ
  apply Subtype.ext
  apply Subtype.ext
  funext i
  exact Finset.card_le_one.mp hcard _ (word_colour_mem m η i) _ (word_colour_mem m ζ i)

theorem entropy_energy_one_colour (m : OccupationState J N t)
    (hcard : (occupiedColours m).card ≤ 1) (f : Fibre m → ℝ) :
    uniformEntropy f = 0 ∧ orderedSwapSum m (fun η => Real.sqrt (f η)) = 0 := by
  let : Subsingleton (Fibre m) := fibre_subsingleton_of_colour_card m hcard
  let ξ : Fibre m := ⟨labelOfState m, profile_labelOfState m⟩
  let : Nonempty (Fibre m) := ⟨ξ⟩
  have he : f = fun _ => f ξ := funext fun η => congrArg f (Subsingleton.elim η ξ)
  rw [he]
  constructor
  · exact uniformEntropy_const _
  · simp only [orderedSwapSum, sub_self, zero_pow (by decide : 2 ≠ 0),
      uniformAverage, Finset.sum_const_zero, zero_div]

/-- Ordered original energy charged to the two endpoint colors. -/
def touchingDensity (m : OccupationState J N t) (a : MeshIndex J) (g : Fibre m → ℝ)
    (η : Fibre m) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N,
    (((if η.val.val i = a then (1 : ℝ) else 0)+(if η.val.val j = a then (1 : ℝ) else 0))*
      (g (fibrePermutation (Equiv.swap i j) m η)-g η)^2)

def touchingEnergy (m : OccupationState J N t) (a : MeshIndex J) (g : Fibre m → ℝ) : ℝ :=
  uniformAverage (touchingDensity m a g)

theorem touchingEnergy_nonneg (m : OccupationState J N t) (a : MeshIndex J) (g : Fibre m → ℝ) :
    0 ≤ touchingEnergy m a g := by
  apply uniformAverage_nonneg
  intro η
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (add_nonneg (by split_ifs <;> positivity) (by split_ifs <;> positivity))
    (sq_nonneg _)

/-- Uniform coarsened averaging of true conditional means gives the original mean. -/
theorem region_average_tower (m : OccupationState J N t) (a b : MeshIndex J) (g : Fibre m → ℝ) :
    uniformAverage (conditionalAverage (coarsenedFibre m a b) g) = uniformAverage g := by
  rw [← coarsened_average m a b (conditionalAverage (coarsenedFibre m a b) g),
    conditionalAverage_tower]

/-- The actual binary projected energy is bounded by precisely the
original swaps touching the retained color. -/
theorem projected_energy_le (m : OccupationState J N t) (a b : MeshIndex J)
    (f : Fibre m → ℝ) (hf : ∀ η, 0 ≤ f η) :
    orderedSwapSum (coarsenedProfile m a b) (fun z => Real.sqrt (regionAverage m a b f z)) ≤
      touchingEnergy m a (fun η => Real.sqrt (f η)) := by
  let T : Fin N → Fin N → Fibre m → ℝ := fun i j η =>
    ((if η.val.val i = a then (1 : ℝ) else 0)+(if η.val.val j = a then (1 : ℝ) else 0))*
      (Real.sqrt (f (fibrePermutation (Equiv.swap i j) m η))-Real.sqrt (f η))^2
  have hh (i j : Fin N) := uniformAverage_mono (region_swap_contraction_supported m a b f hf i j)
  have ht (i j : Fin N) :
      uniformAverage (conditionalAverage (coarsenedFibre m a b) (T i j)) =
      uniformAverage (T i j) := region_average_tower m a b (T i j)
  unfold orderedSwapSum
  calc
    _ ≤ ∑ i : Fin N, ∑ j : Fin N,
        uniformAverage (conditionalAverage (coarsenedFibre m a b) (T i j)) := by
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hh i j
    _ = ∑ i : Fin N, ∑ j : Fin N, uniformAverage (T i j) := by simp_rw [ht]
    _ = touchingEnergy m a (fun η => Real.sqrt (f η)) := by
      unfold touchingEnergy touchingDensity
      simp only [uniformAverage_sum]
      rfl

theorem uniformAverage_finset_sum {Ω I : Type*} [Fintype Ω] (s : Finset I)
    (f : I → Ω → ℝ) :
    uniformAverage (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, uniformAverage (f i) := by
  unfold uniformAverage
  rw [Finset.sum_comm, Finset.sum_div]

/-- Every particle endpoint has exactly one occupied color. -/
theorem touching_colour_sum (m : OccupationState J N t) (η : Fibre m) (i j : Fin N) (E : ℝ) :
    (∑ a ∈ occupiedColours m,
      (((if η.val.val i = a then (1 : ℝ) else 0)+(if η.val.val j = a then (1 : ℝ) else 0))*E)) =
      2*E := by
  classical
  have hsingle (k : Fin N) :
      (∑ a ∈ occupiedColours m, if η.val.val k = a then (1 : ℝ) else 0) = 1 := by
    have he : (fun a : MeshIndex J => if η.val.val k = a then (1 : ℝ) else 0) =
        (fun a => if a = η.val.val k then (1 : ℝ) else 0) := by
      funext a
      by_cases ha : η.val.val k = a
      · simp [ha]
      · simp [ha, Ne.symm ha]
    rw [he]
    simp only [Finset.sum_ite_eq', word_colour_mem, ite_true]
  rw [← Finset.sum_mul, Finset.sum_add_distrib, hsingle i, hsingle j]
  ring

/-- A nonzero transposition is retained after removing exactly L-2
occupied colors. Same-color transpositions vanish before counting. -/
theorem retained_colour_sum (m : OccupationState J N t) (g : Fibre m → ℝ)
    (η : Fibre m) (i j : Fin N) :
    (∑ a ∈ occupiedColours m, if η.val.val i ≠ a ∧ η.val.val j ≠ a then
      (g (fibrePermutation (Equiv.swap i j) m η)-g η)^2 else 0) =
      ((occupiedColours m).card-2 : ℝ)*(g (fibrePermutation (Equiv.swap i j) m η)-g η)^2 := by
  classical
  by_cases hij : η.val.val i = η.val.val j
  · rw [fibrePermutation_swap_of_equal m i j η hij]
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), ite_self, Finset.sum_const_zero, mul_zero]
  · let E : ℝ := (g (fibrePermutation (Equiv.swap i j) m η)-g η)^2
    have he (a : MeshIndex J) : (if η.val.val i ≠ a ∧ η.val.val j ≠ a then E else 0) =
        E-(if a = η.val.val i then E else 0)-(if a = η.val.val j then E else 0) := by
      by_cases hi : a = η.val.val i
      · subst a
        rw [ite_eq_right (fun h => h.1 rfl), ite_eq_left rfl, ite_eq_right hij]
        ring
      · by_cases hj : a = η.val.val j
        · subst a
          rw [ite_eq_right (fun h => h.2 rfl), ite_eq_right (Ne.symm hij), ite_eq_left rfl]
          ring
        · rw [ite_eq_left (And.intro (Ne.symm hi) (Ne.symm hj)), ite_eq_right hi, ite_eq_right hj]
          ring
    change (∑ a ∈ occupiedColours m, if η.val.val i ≠ a ∧ η.val.val j ≠ a then E else 0) =
      ((occupiedColours m).card-2 : ℝ)*E
    simp_rw [he]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.sum_ite_eq', word_colour_mem, ite_true]
    ring

/-- Sum of the actual retained energies, with every orientation counted once. -/
theorem sum_retainedEnergy (m : OccupationState J N t) (g : Fibre m → ℝ) :
    (∑ a ∈ occupiedColours m, retainedEnergy m a g) =
      ((occupiedColours m).card-2 : ℝ)*orderedSwapSum m g := by
  unfold retainedEnergy
  rw [← uniformAverage_finset_sum]
  have hp (η : Fibre m) : (∑ a ∈ occupiedColours m, retainedDensity m a g η) =
      ((occupiedColours m).card-2 : ℝ)*
        (∑ i : Fin N, ∑ j : Fin N, (g (fibrePermutation (Equiv.swap i j) m η)-g η)^2) := by
    unfold retainedDensity
    rw [Finset.sum_comm (f := fun a i => ∑ j : Fin N,
      if η.val.val i ≠ a ∧ η.val.val j ≠ a then
        (g (fibrePermutation (Equiv.swap i j) m η)-g η)^2 else 0)]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact retained_colour_sum m g η i j
  rw [show (fun η => ∑ a ∈ occupiedColours m, retainedDensity m a g η) =
    (fun η => ((occupiedColours m).card-2 : ℝ)*
      (∑ i : Fin N, ∑ j : Fin N, (g (fibrePermutation (Equiv.swap i j) m η)-g η)^2)) from funext hp]
  rw [uniformAverage_mul]
  simp only [uniformAverage_sum, orderedSwapSum]

/-- Summing the supported projected-energy charges counts each endpoint
color once, hence exactly twice each original transposition. -/
theorem sum_touchingEnergy (m : OccupationState J N t) (g : Fibre m → ℝ) :
    (∑ a ∈ occupiedColours m, touchingEnergy m a g) = 2*orderedSwapSum m g := by
  unfold touchingEnergy
  rw [← uniformAverage_finset_sum]
  have hp (η : Fibre m) : (∑ a ∈ occupiedColours m, touchingDensity m a g η) =
      2*(∑ i : Fin N, ∑ j : Fin N, (g (fibrePermutation (Equiv.swap i j) m η)-g η)^2) := by
    unfold touchingDensity
    rw [Finset.sum_comm (f := fun a i => ∑ j : Fin N,
      (((if η.val.val i = a then (1 : ℝ) else 0)+(if η.val.val j = a then (1 : ℝ) else 0))*
        (g (fibrePermutation (Equiv.swap i j) m η)-g η)^2))]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact touching_colour_sum m η i j _
  rw [show (fun η => ∑ a ∈ occupiedColours m, touchingDensity m a g η) =
    (fun η => 2*(∑ i : Fin N, ∑ j : Fin N,
      (g (fibrePermutation (Equiv.swap i j) m η)-g η)^2)) from funext hp]
  rw [uniformAverage_mul]
  simp only [uniformAverage_sum, orderedSwapSum]

/-- The exact color-chain weights sum to (L-1)N. -/
theorem sum_remaining_weights (m : OccupationState J N t) :
    (∑ a ∈ occupiedColours m, ((N : ℝ)-m.val a)) = ((occupiedColours m).card-1 : ℝ)*N := by
  have hh : (∑ a ∈ occupiedColours m, (m.val a : ℝ)) = N := by
    exact_mod_cast occupied_counts_sum m
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hh]
  ring

theorem occupied_other (m : OccupationState J N t) (a : MeshIndex J)
    (ha : 0 < m.val a) (hcard : 2 ≤ (occupiedColours m).card) :
    ∃ b ∈ occupiedColours m, a ≠ b := by
  have hm : a ∈ occupiedColours m := (mem_occupiedColours m a).mpr ha
  have he : 0 < ((occupiedColours m).erase a).card := by
    rw [Finset.card_erase_of_mem hm]
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp he
  exact ⟨b, (Finset.mem_erase.mp hb).2, Ne.symm (Finset.mem_erase.mp hb).1⟩

theorem occupied_count_lt_total (m : OccupationState J N t) (a : MeshIndex J)
    (ha : 0 < m.val a) (hcard : 2 ≤ (occupiedColours m).card) : m.val a < N := by
  obtain ⟨b, hb, hab⟩ := occupied_other m a ha hcard
  have hbp := (mem_occupiedColours m b).mp hb
  let ξ : Fibre m := ⟨labelOfState m, profile_labelOfState m⟩
  have hle := Finset.single_le_sum
    (fun c (_ : c ∈ (Finset.univ : Finset (MeshIndex J))) =>
      Nat.zero_le ((remainingProfile ξ a).val c)) (Finset.mem_univ b)
  rw [(remainingProfile ξ a).property.1, remainingProfile_count, ite_eq_right (Ne.symm hab)] at hle
  have hc := remaining_card ξ a
  omega

/-- Actual binary LSI plus the proved projection contraction and coefficient
comparison, in the color-chain normalization. -/
theorem projected_entropy_bound (m : OccupationState J N t) (a b : MeshIndex J)
    (hab : a ≠ b) (ha : 0 < m.val a) (haN : m.val a < N)
    (k : ℕ) (hk : 0 < k) (hka : k ≤ m.val a) (hthree : 3*k ≤ N)
    (f : Fibre m → ℝ) (hf : ∀ η, 0 ≤ f η) :
    4*((N : ℝ)-m.val a)*uniformEntropy (regionAverage m a b f) ≤
      (4/Real.log 2*Real.log ((N : ℝ)/k))/2*
        touchingEnergy m a (fun η => Real.sqrt (f η)) := by
  have hM : 0 < N-m.val a := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr : (0 : ℝ) < m.val a := by exact_mod_cast ha
  have hs : (0 : ℝ) < (N-m.val a : ℕ) := by exact_mod_cast hM
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have ht : (m.val a : ℝ)+(N-m.val a : ℕ) = N := by exact_mod_cast (show m.val a+(N-m.val a)=N by omega)
  have hc := weighted_binary_ratio hr hs hkr (by exact_mod_cast hka)
    (show 3*(k : ℝ) ≤ (m.val a : ℝ)+(N-m.val a : ℕ) by rw [ht]; exact_mod_cast hthree)
  rw [ht] at hc
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcoef : ((N-m.val a : ℕ) : ℝ)/(N : ℝ)*
      (2/Real.log 2*binaryLog (m.val a) (N-m.val a : ℕ)) ≤
      (4/Real.log 2*Real.log ((N : ℝ)/k))/2 := by
    have hh := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 2/Real.log 2 from div_nonneg (by norm_num) hlog2.le)
    unfold binaryLog
    rw [ht]
    convert hh using 1 <;> ring
  have hB : 0 ≤ 2/Real.log 2*binaryLog (m.val a) (N-m.val a : ℕ) := by
    apply mul_nonneg (div_nonneg (by norm_num) hlog2.le)
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_log_binary_ratio hr hs)
  have hraw := two_colour_lsi (coarsenedProfile m a b) a b hab (coarsened_two_colours m a b)
    (regionAverage m a b f) (fun z => uniformAverage_nonneg (fun η => hf η.val))
  rw [coarsened_count_left m a b hab, coarsened_count_right m a b hab] at hraw
  have hscale : ((N : ℝ)-m.val a) = (N-m.val a : ℕ) := by linarith only [ht]
  calc
    _ = (((N-m.val a : ℕ) : ℝ)/(N : ℝ))*
        (4*(N : ℝ)*uniformEntropy (regionAverage m a b f)) := by
      rw [hscale]
      field_simp [hn.ne']
    _ ≤ (((N-m.val a : ℕ) : ℝ)/(N : ℝ))*
        ((2/Real.log 2*binaryLog (m.val a) (N-m.val a : ℕ))*
          orderedSwapSum (coarsenedProfile m a b) (fun z => Real.sqrt (regionAverage m a b f z))) :=
      mul_le_mul_of_nonneg_left hraw (div_nonneg hs.le hn.le)
    _ = ((((N-m.val a : ℕ) : ℝ)/(N : ℝ))*(2/Real.log 2*binaryLog (m.val a) (N-m.val a : ℕ)))*
        orderedSwapSum (coarsenedProfile m a b) (fun z => Real.sqrt (regionAverage m a b f z)) := by ring
    _ ≤ ((((N-m.val a : ℕ) : ℝ)/(N : ℝ))*(2/Real.log 2*binaryLog (m.val a) (N-m.val a : ℕ)))*
        touchingEnergy m a (fun η => Real.sqrt (f η)) :=
      mul_le_mul_of_nonneg_left (projected_energy_le m a b f hf)
        (mul_nonneg (div_nonneg hs.le hn.le) hB)
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (touchingEnergy_nonneg m a _)

/-- One occupied-color entropy chain with all geometric/coupling inputs
proved. Only the explicitly displayed smaller-fibre induction assertion remains. -/
theorem colour_entropy_step (m : OccupationState J N t) (a b : MeshIndex J)
    (hab : a ≠ b) (ha : 0 < m.val a) (haN : m.val a < N)
    (k : ℕ) (hk : 0 < k) (hka : k ≤ m.val a) (hthree : 3*k ≤ N)
    (f : Fibre m → ℝ) (hf : ∀ η, 0 ≤ f η)
    (hsmall : ∀ ξ : Fibre m,
      4*(Fintype.card (Remaining ξ.val.val a) : ℝ)*uniformEntropy
        (fun ζ : Fibre (remainingProfile ξ a) => f (insertedRegionFibre ξ a ζ)) ≤
      (4/Real.log 2*Real.log ((N : ℝ)/k))*orderedSwapSum (remainingProfile ξ a)
        (fun ζ => Real.sqrt (f (insertedRegionFibre ξ a ζ)))) :
    4*((N : ℝ)-m.val a)*uniformEntropy f ≤
      (4/Real.log 2*Real.log ((N : ℝ)/k))*retainedEnergy m a (fun η => Real.sqrt (f η))+
      (4/Real.log 2*Real.log ((N : ℝ)/k))/2*touchingEnergy m a (fun η => Real.sqrt (f η)) := by
  have h1 := averaged_remaining_bound m a b hab f _ hsmall
  have h2 := projected_entropy_bound m a b hab ha haN k hk hka hthree f hf
  rw [remaining_entropy_chain m a b hab f]
  nlinarith only [h1, h2]

/-- The exact occupied-color recurrence, with the smaller-fibre assertion
exposed only for the strong induction that follows. -/
theorem colour_entropy_recursion (m : OccupationState J N t)
    (hcard : 3 ≤ (occupiedColours m).card) (k : ℕ) (hk : 0 < k)
    (hmin : ∀ a, 0 < m.val a → k ≤ m.val a) (f : Fibre m → ℝ) (hf : ∀ η, 0 ≤ f η)
    (hsmall : ∀ a, 0 < m.val a → ∀ ξ : Fibre m,
      4*(Fintype.card (Remaining ξ.val.val a) : ℝ)*uniformEntropy
        (fun ζ : Fibre (remainingProfile ξ a) => f (insertedRegionFibre ξ a ζ)) ≤
      (4/Real.log 2*Real.log ((N : ℝ)/k))*orderedSwapSum (remainingProfile ξ a)
        (fun ζ => Real.sqrt (f (insertedRegionFibre ξ a ζ)))) :
    4*(N : ℝ)*uniformEntropy f ≤
      (4/Real.log 2*Real.log ((N : ℝ)/k))*orderedSwapSum m (fun η => Real.sqrt (f η)) := by
  have hthree : 3*k ≤ N := (Nat.mul_le_mul_right k hcard).trans (occupied_lower_total m k hmin)
  have hstep (a : MeshIndex J) (ha : a ∈ occupiedColours m) :
      4*((N : ℝ)-m.val a)*uniformEntropy f ≤
        (4/Real.log 2*Real.log ((N : ℝ)/k))*retainedEnergy m a (fun η => Real.sqrt (f η))+
        (4/Real.log 2*Real.log ((N : ℝ)/k))/2*touchingEnergy m a (fun η => Real.sqrt (f η)) := by
    have hap := (mem_occupiedColours m a).mp ha
    obtain ⟨b, _hb, hab⟩ := occupied_other m a hap (by omega)
    exact colour_entropy_step m a b hab hap (occupied_count_lt_total m a hap (by omega))
      k hk (hmin a hap) hthree f hf (hsmall a hap)
  have hh := Finset.sum_le_sum hstep
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  rw [sum_retainedEnergy, sum_touchingEnergy] at hh
  have hleft : (∑ a ∈ occupiedColours m, 4*((N : ℝ)-m.val a)*uniformEntropy f) =
      4*((occupiedColours m).card-1 : ℝ)*(N : ℝ)*uniformEntropy f := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_remaining_weights]
    ring
  rw [hleft] at hh
  have hL : (0 : ℝ) < (occupiedColours m).card-1 := by
    have hc : (3 : ℝ) ≤ (occupiedColours m).card := by exact_mod_cast hcard
    linarith only [hc]
  by_contra h
  have hp := mul_pos hL (sub_pos.mpr (lt_of_not_ge h))
  nlinarith only [hh, hp]

/-- The two-occupied-color base, with arbitrary zero-count ambient colors
removed by the actual support identity. -/
theorem colour_lsi_two (m : OccupationState J N t) (hcard : (occupiedColours m).card = 2)
    (k : ℕ) (hk : 0 < k) (hmin : ∀ a, 0 < m.val a → k ≤ m.val a)
    (f : Fibre m → ℝ) (hf : ∀ η, 0 ≤ f η) :
    4*(N : ℝ)*uniformEntropy f ≤
      (4/Real.log 2*Real.log ((N : ℝ)/k))*orderedSwapSum m (fun η => Real.sqrt (f η)) := by
  classical
  obtain ⟨a, b, hab, hsupport⟩ := Finset.card_eq_two.mp hcard
  have ha : 0 < m.val a := by rw [← mem_occupiedColours, hsupport]; simp
  have hb : 0 < m.val b := by rw [← mem_occupiedColours, hsupport]; simp
  have honly (c : MeshIndex J) (hc : 0 < m.val c) : c = a ∨ c = b := by
    have hh := (mem_occupiedColours m c).mpr hc
    simpa only [hsupport, Finset.mem_insert, Finset.mem_singleton] using hh
  have ht : (m.val a : ℝ)+(m.val b : ℝ) = N := by
    exact_mod_cast two_colour_total m a b hab honly
  have hh := two_colour_lsi m a b hab honly f hf
  have hcoef := binary_ratio_le (show (0 : ℝ) < m.val a by exact_mod_cast ha)
    (show (0 : ℝ) < m.val b by exact_mod_cast hb) (show (0 : ℝ) < k by exact_mod_cast hk)
    (show (k : ℝ) ≤ m.val a by exact_mod_cast hmin a ha)
    (show (k : ℝ) ≤ m.val b by exact_mod_cast hmin b hb)
  rw [ht] at hcoef
  unfold binaryLog at hh
  rw [ht] at hh
  have hc : 2/Real.log 2*Real.log ((N : ℝ)^2/((m.val a : ℝ)*(m.val b : ℝ))) ≤
      4/Real.log 2*Real.log ((N : ℝ)/k) := by
    have he := mul_le_mul_of_nonneg_left hcoef
      (show (0 : ℝ) ≤ 2/Real.log 2 from div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le)
    convert he using 1; ring
  exact hh.trans (mul_le_mul_of_nonneg_right hc (orderedSwapSum_nonneg m _))

/-- Full Salez occupied-color induction. Every smaller-fibre ordinary LSI
input to the recurrence is discharged here. The positive lower count is a
literal bound on original multiplicities, never an entropy or energy premise. -/
theorem multislice_lsi_of_count_lower (m : OccupationState J N t) (k : ℕ) (hk : 0 < k)
    (hmin : ∀ a, 0 < m.val a → k ≤ m.val a) (f : Fibre m → ℝ) (hf : ∀ η, 0 ≤ f η) :
    4*(N : ℝ)*uniformEntropy f ≤
      (4/Real.log 2*Real.log ((N : ℝ)/k))*orderedSwapSum m (fun η => Real.sqrt (f η)) := by
  classical
  suffices hall : ∀ l : ℕ, ∀ {n : ℕ} {u : ℝ} (m' : OccupationState J n u),
      (occupiedColours m').card = l →
      (∀ a, 0 < m'.val a → k ≤ m'.val a) → ∀ f' : Fibre m' → ℝ, (∀ η, 0 ≤ f' η) →
      4*(n : ℝ)*uniformEntropy f' ≤
        (4/Real.log 2*Real.log ((n : ℝ)/k))*orderedSwapSum m' (fun η => Real.sqrt (f' η)) by
    exact hall _ m rfl hmin f hf
  intro l
  induction l using Nat.strong_induction_on with
  | h l ih =>
    intro n u m' hl hmin' f' hf'
    by_cases hsmallcard : (occupiedColours m').card ≤ 1
    · obtain ⟨hent, henergy⟩ := entropy_energy_one_colour m' hsmallcard f'
      simp only [hent, henergy, mul_zero, le_refl]
    by_cases htwo : (occupiedColours m').card = 2
    · exact colour_lsi_two m' htwo k hk hmin' f' hf'
    have hthree : 3 ≤ (occupiedColours m').card := by omega
    apply colour_entropy_recursion m' hthree k hk hmin' f' hf'
    intro a ha ξ
    have hlt : (occupiedColours (remainingProfile ξ a)).card < l := by
      rw [← hl]
      exact remaining_colour_card_lt ξ a ha
    have hminr (c : MeshIndex J) (hc : 0 < (remainingProfile ξ a).val c) :
        k ≤ (remainingProfile ξ a).val c := by
      by_cases he : c = a
      · subst c
        rw [remainingProfile_count, ite_eq_left rfl] at hc
        omega
      · rw [remainingProfile_count, ite_eq_right he] at hc ⊢
        exact hmin' c hc
    have hh := ih _ hlt (remainingProfile ξ a) rfl hminr
      (fun ζ => f' (insertedRegionFibre ξ a ζ)) (fun ζ => hf' (insertedRegionFibre ξ a ζ))
    have hcard := remaining_card ξ a
    have haN := occupied_count_lt_total m' a ha (by omega)
    have hM : (0 : ℝ) < Fintype.card (Remaining ξ.val.val a) := by
      exact_mod_cast (show 0 < Fintype.card (Remaining ξ.val.val a) by omega)
    have hMN : (Fintype.card (Remaining ξ.val.val a) : ℝ) ≤ n := by
      exact_mod_cast (show Fintype.card (Remaining ξ.val.val a) ≤ n by omega)
    have hkr : (0 : ℝ) < k := by exact_mod_cast hk
    have hlog := Real.log_le_log (div_pos hM hkr) (div_le_div_of_nonneg_right hMN hkr.le)
    have hc := mul_le_mul_of_nonneg_left hlog
      (show (0 : ℝ) ≤ 4/Real.log 2 from div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le)
    exact hh.trans (mul_le_mul_of_nonneg_right hc (orderedSwapSum_nonneg (remainingProfile ξ a) _))

theorem occupiedColours_nonempty (m : OccupationState J N t) (hN : 0 < N) :
    (occupiedColours m).Nonempty := by
  let ξ : Fibre m := ⟨labelOfState m, profile_labelOfState m⟩
  let i : Fin N := ⟨0, hN⟩
  exact ⟨ξ.val.val i, word_colour_mem m ξ i⟩

/-- The minimum is taken over precisely the positive literal occupations;
zero-count ambient colors are removed before forming it. -/
def minimumPositiveCount (m : OccupationState J N t) (hN : 0 < N) : ℕ :=
  ((occupiedColours m).image m.val).min' (by
    obtain ⟨a, ha⟩ := occupiedColours_nonempty m hN
    exact ⟨m.val a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩)

theorem minimumPositiveCount_pos (m : OccupationState J N t) (hN : 0 < N) :
    0 < minimumPositiveCount m hN := by
  have hh : minimumPositiveCount m hN ∈ (occupiedColours m).image m.val := by
    unfold minimumPositiveCount
    exact Finset.min'_mem _ _
  obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hh
  rw [← he]
  exact (mem_occupiedColours m a).mp ha

theorem minimumPositiveCount_le (m : OccupationState J N t) (hN : 0 < N)
    (a : MeshIndex J) (ha : 0 < m.val a) : minimumPositiveCount m hN ≤ m.val a := by
  unfold minimumPositiveCount
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨a, (mem_occupiedColours m a).mpr ha, rfl⟩)

/-- Complete ordinary multislice LSI, with the actual minimum positive
multiplicity and the exact manuscript energy 1/(2N) times unordered swaps.
There is no binary, recursive, conditional-law, or entropy estimate premise. -/
theorem multislice_logSobolev (F : LabelState J N t → ℝ) (m : OccupationState J N t)
    (hN : 0 < N) (hF : ∀ η : Fibre m, 0 ≤ F η.val) :
    uniformFibreEntropy F m ≤
      (4/Real.log 2*Real.log ((N : ℝ)/minimumPositiveCount m hN))*
        transpositionEnergy (fun η => Real.sqrt (F η)) m := by
  have hh := multislice_lsi_of_count_lower m (minimumPositiveCount m hN)
    (minimumPositiveCount_pos m hN) (minimumPositiveCount_le m hN)
    (fun η => F η.val) hF
  rw [orderedSwapSum_eq_source_sum (fun η => Real.sqrt (F η)) m] at hh
  change 4*(N : ℝ)*uniformFibreEntropy F m ≤ _ at hh
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold transpositionEnergy
  rw [one_div_mul_eq_div, ← mul_div_assoc]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*(N : ℝ))).mpr
  nlinarith only [hh]

/-- The empty-particle fibre has zero entropy and energy; no undefined
minimum-positive-count expression is used at that endpoint. -/
theorem zero_particles (m : OccupationState J 0 t) (F : LabelState J 0 t → ℝ) :
    uniformFibreEntropy F m = 0 ∧ transpositionEnergy (fun η => Real.sqrt (F η)) m = 0 := by
  let : Subsingleton (Fibre m) := ⟨fun η ζ => by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact Fin.elim0 i⟩
  let ξ : Fibre m := ⟨labelOfState m, profile_labelOfState m⟩
  let : Nonempty (Fibre m) := ⟨ξ⟩
  constructor
  · change uniformEntropy (fun η : Fibre m => F η.val) = 0
    have he : (fun η : Fibre m => F η.val) = fun _ => F ξ.val :=
      funext fun η => congrArg (fun ζ : Fibre m => F ζ.val) (Subsingleton.elim η ξ)
    rw [he, uniformEntropy_const]
  · simp only [transpositionEnergy, Nat.cast_zero, mul_zero, div_zero, zero_mul]

end PeriodicAttractiveLogGas.MultisliceColourRecursion
