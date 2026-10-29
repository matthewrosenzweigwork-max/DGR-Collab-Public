import DGPS.Foundations.Torus

/-!
# Abstract inertia comparison for `I - B A` and `I - A B`

Let `A : X → Y` and `B : Y → X` be linear maps between real inner product spaces with
`⟪A x, y⟫ = ⟪x, B y⟫` (that is, `B` is a formal adjoint of `A`).  Then the quadratic forms
`‖x‖² - ‖A x‖²` and `‖y‖² - ‖B y‖²` (the forms of `I - B A` and `I - A B`) have the same
negative index, the kernels of `I - B A` and `I - A B` have the same dimension, and one is
coercive if and only if the other is.  No spectral theory and no completeness is used.
-/

open scoped RealInnerProductSpace

namespace DGPS.FiniteN.AttractiveLandscape

/-- There is an `n`-dimensional subspace on which the quadratic form `Q` is negative definite. -/
def HasNegativeSubspace {M : Type*} [AddCommGroup M] [Module ℝ M] (Q : M → ℝ) (n : ℕ) : Prop :=
  ∃ S : Submodule ℝ M, Module.finrank ℝ S = n ∧ ∀ v ∈ S, v ≠ 0 → Q v < 0

section Abstract

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

theorem sq_norm_sub_apply (A : X →ₗ[ℝ] Y) (B : Y →ₗ[ℝ] X)
    (hAB : ∀ x y, ⟪A x, y⟫ = ⟪x, B y⟫) (x : X) :
    ‖x - B (A x)‖ ^ 2 = ‖x‖ ^ 2 - 2 * ‖A x‖ ^ 2 + ‖B (A x)‖ ^ 2 := by
  rw [norm_sub_sq_real, ← hAB x (A x), real_inner_self_eq_norm_sq]

/-- Negative subspaces of `‖x‖² - ‖A x‖²` are mapped by `A` to negative subspaces of
`‖y‖² - ‖B y‖²` of the same dimension. -/
theorem hasNegativeSubspace_of_map (A : X →ₗ[ℝ] Y) (B : Y →ₗ[ℝ] X)
    (hAB : ∀ x y, ⟪A x, y⟫ = ⟪x, B y⟫) (n : ℕ)
    (h : HasNegativeSubspace (fun x : X => ‖x‖ ^ 2 - ‖A x‖ ^ 2) n) :
    HasNegativeSubspace (fun y : Y => ‖y‖ ^ 2 - ‖B y‖ ^ 2) n := by
  obtain ⟨S, hS, hneg⟩ := h
  have hinj : Function.Injective (A.domRestrict S) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, hx⟩ h0
    by_contra hne
    have hx0 : x ≠ 0 := fun h => hne (Subtype.ext h)
    have hAx : A x = 0 := h0
    have this : ‖x‖ ^ 2 - ‖A x‖ ^ 2 < 0 := hneg x hx hx0
    rw [hAx] at this
    simp at this
    nlinarith [sq_nonneg ‖x‖]
  refine ⟨LinearMap.range (A.domRestrict S), ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj]; exact hS
  · rintro y ⟨⟨x, hx⟩, rfl⟩ hy
    have hx0 : x ≠ 0 := by rintro rfl; apply hy; simp
    have h1 := hneg x hx hx0
    have e := sq_norm_sub_apply A B hAB x
    have key : ‖A x‖ ^ 2 - ‖B (A x)‖ ^ 2 ≤ ‖x‖ ^ 2 - ‖A x‖ ^ 2 := by
      nlinarith [sq_nonneg ‖x - B (A x)‖]
    show ‖A x‖ ^ 2 - ‖B (A x)‖ ^ 2 < 0
    linarith

theorem hasNegativeSubspace_iff (A : X →ₗ[ℝ] Y) (B : Y →ₗ[ℝ] X)
    (hAB : ∀ x y, ⟪A x, y⟫ = ⟪x, B y⟫) (n : ℕ) :
    HasNegativeSubspace (fun x : X => ‖x‖ ^ 2 - ‖A x‖ ^ 2) n ↔
      HasNegativeSubspace (fun y : Y => ‖y‖ ^ 2 - ‖B y‖ ^ 2) n :=
  ⟨hasNegativeSubspace_of_map A B hAB n,
    hasNegativeSubspace_of_map B A (fun y x => by rw [real_inner_comm x (B y), ← hAB, real_inner_comm]) n⟩

/-- The kernels of `I - B A` and `I - A B` have the same dimension. -/
theorem finrank_ker_eq (A : X →ₗ[ℝ] Y) (B : Y →ₗ[ℝ] X) :
    Module.finrank ℝ (LinearMap.ker (LinearMap.id - B ∘ₗ A)) =
      Module.finrank ℝ (LinearMap.ker (LinearMap.id - A ∘ₗ B)) := by
  have hA : ∀ x ∈ LinearMap.ker (LinearMap.id - B ∘ₗ A), A x ∈ LinearMap.ker (LinearMap.id - A ∘ₗ B) := by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    show A x = A (B (A x))
    rw [← LinearMap.comp_apply B A x, ← hx]
  have hB : ∀ y ∈ LinearMap.ker (LinearMap.id - A ∘ₗ B), B y ∈ LinearMap.ker (LinearMap.id - B ∘ₗ A) := by
    intro y hy
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hy
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    show B y = B (A (B y))
    rw [← LinearMap.comp_apply A B y, ← hy]
  refine LinearEquiv.finrank_eq (LinearEquiv.ofLinearMap (A.restrict hA) (B.restrict hB) ?_ ?_)
  · ext ⟨y, hy⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hy
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrict_apply,
      LinearMap.id_coe, id_eq]
    exact hy.symm
  · ext ⟨x, hx⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrict_apply,
      LinearMap.id_coe, id_eq]
    exact hx.symm

/-- Coercivity of `‖x‖² - ‖A x‖²` implies coercivity of `‖y‖² - ‖B y‖²`. -/
theorem coercive_of_coercive (A : X →ₗ[ℝ] Y) (B : Y →ₗ[ℝ] X)
    (hAB : ∀ x y, ⟪A x, y⟫ = ⟪x, B y⟫)
    (h : ∃ c : ℝ, 0 < c ∧ ∀ x : X, c * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 - ‖A x‖ ^ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : Y, c * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 - ‖B y‖ ^ 2 := by
  obtain ⟨c, hc, h⟩ := h
  have hc1 := min_le_left c 1
  have hc2 := min_le_right c 1
  have hc3 : 0 < min c 1 := lt_min hc one_pos
  refine ⟨min c 1, hc3, fun y => ?_⟩
  have hA : ∀ x, ‖A x‖ ^ 2 ≤ (1 - min c 1) * ‖x‖ ^ 2 := fun x => by
    have := h x
    nlinarith [sq_nonneg ‖x‖]
  have hBy : ‖B y‖ ^ 2 ≤ (1 - min c 1) * ‖y‖ ^ 2 := by
    have e1 : ‖B y‖ ^ 2 = ⟪A (B y), y⟫ := by
      rw [hAB (B y) y, real_inner_self_eq_norm_sq]
    have e2 : ⟪A (B y), y⟫ ≤ ‖A (B y)‖ * ‖y‖ := real_inner_le_norm _ _
    have e3 := hA (B y)
    by_cases ha : ‖B y‖ = 0
    · rw [ha]; nlinarith [sq_nonneg ‖y‖]
    · have hpos : 0 < ‖B y‖ ^ 2 := by positivity
      have e4 : (‖B y‖ ^ 2) ^ 2 ≤ ‖A (B y)‖ ^ 2 * ‖y‖ ^ 2 := by
        have h0 : 0 ≤ ‖B y‖ ^ 2 := hpos.le
        calc (‖B y‖ ^ 2) ^ 2 ≤ (‖A (B y)‖ * ‖y‖) ^ 2 := by
              apply pow_le_pow_left₀ h0; linarith
          _ = ‖A (B y)‖ ^ 2 * ‖y‖ ^ 2 := by ring
      have e5 : (‖B y‖ ^ 2) * ‖B y‖ ^ 2 ≤ ‖B y‖ ^ 2 * ((1 - min c 1) * ‖y‖ ^ 2) := by
        calc (‖B y‖ ^ 2) * ‖B y‖ ^ 2 = (‖B y‖ ^ 2) ^ 2 := by ring
          _ ≤ ‖A (B y)‖ ^ 2 * ‖y‖ ^ 2 := e4
          _ ≤ ((1 - min c 1) * ‖B y‖ ^ 2) * ‖y‖ ^ 2 := by gcongr
          _ = ‖B y‖ ^ 2 * ((1 - min c 1) * ‖y‖ ^ 2) := by ring
      exact le_of_mul_le_mul_left e5 hpos
  nlinarith

theorem coercive_iff (A : X →ₗ[ℝ] Y) (B : Y →ₗ[ℝ] X)
    (hAB : ∀ x y, ⟪A x, y⟫ = ⟪x, B y⟫) :
    (∃ c : ℝ, 0 < c ∧ ∀ x : X, c * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 - ‖A x‖ ^ 2) ↔
      ∃ c : ℝ, 0 < c ∧ ∀ y : Y, c * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 - ‖B y‖ ^ 2 :=
  ⟨coercive_of_coercive A B hAB,
    coercive_of_coercive B A (fun y x => by rw [real_inner_comm x (B y), ← hAB, real_inner_comm])⟩

end Abstract

end DGPS.FiniteN.AttractiveLandscape
