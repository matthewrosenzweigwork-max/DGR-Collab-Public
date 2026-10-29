import DGPS.Topology.SingularAdapter
import Mathlib.Analysis.Convex.StdSimplex

/-!
# Barycentric subdivision on affine chains (TOP004a, algebraic core)

Over the coefficient field `F2 = ZMod 2` all signs disappear, so the (augmented) complex of
affine chains of a real vector space `E` can be written without grading: a basis element is a
list `[w₀, …, wₖ]` of points of `E` (an affine simplex; the empty list is the augmentation
generator in degree `-1`), and the boundary deletes one vertex at a time.

* `LChain E = (List E →₀ F2)`, boundary `bd`, cone `cone b = (b :: ·)`.
* `bd_cone`: `∂ (b * x) = x + b * ∂ x` (uniform, thanks to the augmentation).
* `bd_bd`: `∂ ∘ ∂ = 0`.
* `sd` (the barycentric subdivision operator `S`) with `sd λ = b_λ * S ∂λ`, `bd_sd : ∂ S = S ∂`.
* `homotopy` (`T`) with `homotopy λ = b_λ * (λ - T ∂λ)` and
  `bd_homotopy_add : ∂ T + T ∂ = 1 - S` (in characteristic 2: `1 + S`).
* Naturality of `S` and `T` for barycenter preserving (e.g. affine) maps.
-/

open Finsupp

namespace DGPS.Topology.Subdivision

open DGPS.Topology (F2)

variable {E E' : Type*}

/-- Affine chains (augmented, ungraded) over `F2`: formal sums of vertex lists. -/
abbrev LChain (E : Type*) : Type _ := List E →₀ F2

lemma add_self_eq_zero' {M : Type*} [AddCommGroup M] [Module F2 M] (x : M) : x + x = 0 := by
  rw [← two_smul F2 x]
  have : (2 : F2) = 0 := by decide
  rw [this, zero_smul]

/-- Boundary of a vertex list: sum of the lists with one vertex deleted. -/
noncomputable def bdList (l : List E) : LChain E :=
  ∑ i ∈ Finset.range l.length, single (l.eraseIdx i) 1

/-- The boundary operator on affine chains. -/
noncomputable def bd : LChain E →ₗ[F2] LChain E :=
  linearCombination F2 bdList

/-- The cone operator with apex `b`. -/
noncomputable def cone (b : E) : LChain E →ₗ[F2] LChain E :=
  lmapDomain F2 F2 (List.cons b)

@[simp] lemma bd_single (l : List E) (c : F2) : bd (single l c) = c • bdList l := by
  simp [bd]

@[simp] lemma cone_single (b : E) (l : List E) (c : F2) :
    cone b (single l c) = single (b :: l) c := by
  simp [cone, mapDomain_single]

lemma bdList_cons (b : E) (l : List E) :
    bdList (b :: l) = single l 1 + cone b (bdList l) := by
  unfold bdList
  rw [List.length_cons, Finset.sum_range_succ', add_comm]
  congr 1
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

lemma bd_cone (b : E) (x : LChain E) : bd (cone b x) = x + cone b (bd x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | single l c =>
    rw [cone_single, bd_single, bd_single, bdList_cons, map_smul, smul_add]
    simp

lemma bdList_bdList (l : List E) : bd (bdList l) = 0 := by
  induction l with
  | nil => simp [bdList, bd]
  | cons b l ih =>
    rw [bdList_cons, map_add, bd_cone, ih, bd_single]
    simp [add_self_eq_zero']


lemma bdList_nil : bdList ([] : List E) = 0 := by simp [bdList]

lemma bdList_length_lt (l : List E) {i : ℕ} (hi : i < l.length) :
    (l.eraseIdx i).length < l.length := by
  rw [List.length_eraseIdx_of_lt hi]; omega

/-- A linear identity holding on all faces of `l` holds on `∂ l`. -/
lemma face_sum_congr {M : Type*} [AddCommMonoid M] [Module F2 M] (l : List E)
    (f g : LChain E →ₗ[F2] M)
    (h : ∀ i < l.length, f (single (l.eraseIdx i) 1) = g (single (l.eraseIdx i) 1)) :
    f (bdList l) = g (bdList l) := by
  unfold bdList
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun i hi => h i (Finset.mem_range.1 hi)

section core

variable {P P' : Type*} (b : List P → P)

/-- The barycentric subdivision of an affine simplex, by recursion on its size, for an arbitrary
choice of "barycenter" `b : List P → P`: `S λ = b(λ) * S ∂λ`, `S [] = []`. -/
noncomputable def sdList (l : List P) : LChain P :=
  if _ : l = [] then single [] 1
  else ∑ i : Fin l.length, cone (b l) (sdList (l.eraseIdx i))
termination_by l.length
decreasing_by exact bdList_length_lt l i.2

/-- The barycentric subdivision operator on affine chains. -/
noncomputable def sd : LChain P →ₗ[F2] LChain P :=
  linearCombination F2 (sdList b)

@[simp] lemma sd_single (l : List P) (c : F2) : sd b (single l c) = c • sdList b l := by
  simp [sd]

lemma sdList_nil : sdList b ([] : List P) = single [] 1 := by
  rw [sdList]; simp

lemma sdList_of_ne_nil {l : List P} (hl : l ≠ []) :
    sdList b l = cone (b l) (sd b (bdList l)) := by
  rw [sdList]
  simp only [hl, dite_false, bdList, map_sum, sd_single, one_smul]
  exact (Finset.sum_range fun i => cone (b l) (sdList b (l.eraseIdx i))).symm

/-- Subdivision is a chain map: `∂ S = S ∂`. -/
lemma bd_sdList (l : List P) : bd (sdList b l) = sd b (bdList l) := by
  suffices h : ∀ n, ∀ l : List P, l.length = n → bd (sdList b l) = sd b (bdList l) from h _ l rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hn
  by_cases hl : l = []
  · subst hl; simp [sdList_nil, bdList]
  · have key : bd (sd b (bdList l)) = sd b (bd (bdList l)) :=
      face_sum_congr l (bd ∘ₗ sd b) (sd b ∘ₗ bd) fun i hi => by
        simp only [LinearMap.comp_apply, sd_single, bd_single, one_smul]
        exact ih _ (hn ▸ bdList_length_lt l hi) _ rfl
    rw [sdList_of_ne_nil b hl, bd_cone, key, bdList_bdList, map_zero, map_zero]
    simp

lemma bd_sd (x : LChain P) : bd (sd b x) = sd b (bd x) := by
  have : (bd ∘ₗ sd b : LChain P →ₗ[F2] LChain P) = sd b ∘ₗ bd := by
    refine Finsupp.lhom_ext fun l c => ?_
    simp [bd_sdList]
  exact congrArg (fun f => f x) this

/-- The chain homotopy `T` from `S` to the identity, by recursion on the size:
`T λ = b(λ) * (λ - T ∂λ)`, `T [] = 0`. -/
noncomputable def homList (l : List P) : LChain P :=
  if _ : l = [] then 0
  else ∑ i : Fin l.length, cone (b l) (homList (l.eraseIdx i)) + cone (b l) (single l 1)
termination_by l.length
decreasing_by exact bdList_length_lt l i.2

/-- The chain homotopy operator `T` (raising size by one). -/
noncomputable def homotopy : LChain P →ₗ[F2] LChain P :=
  linearCombination F2 (homList b)

@[simp] lemma homotopy_single (l : List P) (c : F2) :
    homotopy b (single l c) = c • homList b l := by
  simp [homotopy]

lemma homList_of_ne_nil {l : List P} (hl : l ≠ []) :
    homList b l = cone (b l) (single l 1 + homotopy b (bdList l)) := by
  rw [homList]
  simp only [hl, dite_false, bdList, map_sum, map_add, homotopy_single, one_smul]
  rw [add_comm]
  congr 1
  exact (Finset.sum_range fun i => cone (b l) (homList b (l.eraseIdx i))).symm

/-- `∂ T + T ∂ = 1 - S` (characteristic 2: `1 + S`), on basis elements. -/
lemma bd_homList (l : List P) :
    bd (homList b l) + homotopy b (bdList l) = single l 1 + sdList b l := by
  suffices h : ∀ n, ∀ l : List P, l.length = n →
      bd (homList b l) + homotopy b (bdList l) = single l 1 + sdList b l from h _ l rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hn
  by_cases hl : l = []
  · subst hl; simp [homList, bdList_nil, sdList_nil, add_self_eq_zero']
  · have key : bd (homotopy b (bdList l)) + homotopy b (bd (bdList l)) =
        bdList l + sd b (bdList l) :=
      face_sum_congr l (bd ∘ₗ homotopy b + homotopy b ∘ₗ bd) (LinearMap.id + sd b)
        fun i hi => by
        simp only [LinearMap.add_apply, LinearMap.comp_apply, homotopy_single, bd_single,
          one_smul, LinearMap.id_apply, sd_single]
        exact ih _ (hn ▸ bdList_length_lt l hi) _ rfl
    rw [bdList_bdList, map_zero, add_zero] at key
    have h1 : bd (single l 1 + homotopy b (bdList l)) = sd b (bdList l) := by
      rw [map_add, bd_single, one_smul, add_comm, key, add_right_comm, add_self_eq_zero',
        zero_add]
    rw [homList_of_ne_nil b hl, bd_cone, h1, sdList_of_ne_nil b hl]
    calc _ = single l 1 + cone (b l) (sd b (bdList l)) +
          (homotopy b (bdList l) + homotopy b (bdList l)) := by abel
      _ = _ := by rw [add_self_eq_zero', add_zero]

/-- `∂ T + T ∂ = 1 + S` on all affine chains. -/
lemma bd_homotopy_add (x : LChain P) :
    bd (homotopy b x) + homotopy b (bd x) = x + sd b x := by
  have : (bd ∘ₗ homotopy b + homotopy b ∘ₗ bd : LChain P →ₗ[F2] LChain P) =
      LinearMap.id + sd b := by
    refine Finsupp.lhom_ext fun l c => ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, homotopy_single, bd_single,
      LinearMap.id_apply, sd_single, map_smul]
    rw [← smul_add, bd_homList, smul_add]
    simp
  exact congrArg (fun f => f x) this

/-! ### Naturality -/

/-- Push forward a chain along a map of vertices. -/
noncomputable def mapChain (f : P → P') : LChain P →ₗ[F2] LChain P' :=
  lmapDomain F2 F2 (List.map f)

@[simp] lemma mapChain_single (f : P → P') (l : List P) (c : F2) :
    mapChain f (single l c) = single (l.map f) c := by
  simp [mapChain, mapDomain_single]

lemma mapChain_cone (f : P → P') (a : P) (x : LChain P) :
    mapChain f (cone a x) = cone (f a) (mapChain f x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single l c => simp

lemma mapChain_bdList (f : P → P') (l : List P) :
    mapChain f (bdList l) = bdList (l.map f) := by
  unfold bdList
  rw [map_sum, List.length_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [List.eraseIdx_map]

lemma mapChain_bd (f : P → P') (x : LChain P) : mapChain f (bd x) = bd (mapChain f x) := by
  have : (mapChain f ∘ₗ bd : LChain P →ₗ[F2] LChain P') = bd ∘ₗ mapChain f := by
    refine Finsupp.lhom_ext fun l c => ?_
    simp [mapChain_bdList]
  exact congrArg (fun g => g x) this

variable (b' : List P' → P') (f : P → P')

lemma mapChain_sdList (hf : ∀ l : List P, l ≠ [] → b' (l.map f) = f (b l)) (l : List P) :
    mapChain f (sdList b l) = sdList b' (l.map f) := by
  suffices h : ∀ n, ∀ l : List P, l.length = n →
      mapChain f (sdList b l) = sdList b' (l.map f) from h _ l rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hn
  by_cases hl : l = []
  · subst hl; simp [sdList_nil]
  · have hl' : l.map f ≠ [] := by simpa using hl
    have key : mapChain f (sd b (bdList l)) = sd b' (bdList (l.map f)) := by
      rw [← mapChain_bdList]
      refine face_sum_congr l (mapChain f ∘ₗ sd b) (sd b' ∘ₗ mapChain f) fun i hi => ?_
      simp only [LinearMap.comp_apply, sd_single, one_smul, mapChain_single]
      rw [ih _ (hn ▸ bdList_length_lt l hi) _ rfl]
    rw [sdList_of_ne_nil b hl, sdList_of_ne_nil b' hl', mapChain_cone, hf l hl, key]

end core

end DGPS.Topology.Subdivision
