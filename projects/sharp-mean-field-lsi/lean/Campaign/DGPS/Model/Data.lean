import DGPS.Foundations.Torus

/-!
# Continuous potential data independent of regularity (DEF007)

INTERFACES/definitions.md §2, common_lemmas.md DEF007. `InteractionData d` consists of continuous
real functions `V : 𝕋^d → ℝ` and `W : 𝕋^d × 𝕋^d → ℝ` (stored curried as `W : 𝕋^d → 𝕋^d → ℝ`,
continuous as a function on the product), with `W x y = W y x` and `W x x = 0`.

No Sobolev or Lipschitz hypothesis is part of the data. `LipschitzData A` is a separate
`Prop` on a given `A : InteractionData d`: direct Lipschitz bounds for `V` and `W` with respect to
the Euclidean quotient distance `torusDist` (and, for `W`, the Euclidean product distance
`√(dist x x'² + dist y y'²)`). Weak gradients are not stored in the data.
-/

open Topology

namespace DGPS

/-- Continuous potential data (DEF007): a one-body potential `V`, a symmetric two-body
interaction `W` vanishing on the diagonal. No regularity beyond continuity. -/
structure InteractionData (d : ℕ) where
  V : Torus d → ℝ
  W : Torus d → Torus d → ℝ
  V_continuous : Continuous V
  W_continuous : Continuous (fun p : Torus d × Torus d => W p.1 p.2)
  W_symm : ∀ x y, W x y = W y x
  W_diag : ∀ x, W x x = 0

end DGPS

namespace DGPS.InteractionData

variable {d : ℕ}

@[ext] theorem ext {A B : InteractionData d} (hV : A.V = B.V) (hW : A.W = B.W) : A = B := by
  cases A; cases B; cases hV; cases hW; rfl

/-- The trivial interaction data `V = 0`, `W = 0`. -/
def zero (d : ℕ) : InteractionData d where
  V := fun _ => 0
  W := fun _ _ => 0
  V_continuous := continuous_const
  W_continuous := continuous_const
  W_symm := fun _ _ => rfl
  W_diag := fun _ => rfl

theorem W_continuous_left (A : InteractionData d) (y : Torus d) : Continuous fun x => A.W x y :=
  A.W_continuous.comp (continuous_id.prodMk continuous_const)

theorem W_continuous_right (A : InteractionData d) (x : Torus d) : Continuous fun y => A.W x y :=
  A.W_continuous.comp (continuous_const.prodMk continuous_id)

/-- The diagonal restriction of `W` is continuous (and identically zero). -/
theorem W_diag_continuous (A : InteractionData d) : Continuous fun x => A.W x x :=
  A.W_continuous.comp (continuous_id.prodMk continuous_id)

/-- `V` is bounded (the torus is compact). -/
theorem V_bounded (A : InteractionData d) : ∃ C, ∀ x, |A.V x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn A.V_continuous.continuousOn
  exact ⟨C, fun x => by simpa using hC x (Set.mem_univ x)⟩

/-- `W` is bounded (the torus square is compact). -/
theorem W_bounded (A : InteractionData d) : ∃ C, ∀ x y, |A.W x y| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    A.W_continuous.continuousOn
  exact ⟨C, fun x y => by simpa using hC (x, y) (Set.mem_univ _)⟩

end DGPS.InteractionData

namespace DGPS

/-- Direct Lipschitz regularity of interaction data (DEF007), a property separate from
`InteractionData`: `V` is Lipschitz for the Euclidean quotient distance and `W` is Lipschitz on the
product for the Euclidean product distance `√(dist x x'² + dist y y'²)`. -/
def LipschitzData {d : ℕ} (A : InteractionData d) : Prop :=
  (∃ L : ℝ, ∀ x y, |A.V x - A.V y| ≤ L * torusDist x y) ∧
  (∃ L : ℝ, ∀ x y x' y',
    |A.W x y - A.W x' y'| ≤ L * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2))

end DGPS

namespace DGPS.LipschitzData

variable {d : ℕ} {A : InteractionData d}

theorem V_lipschitz (h : LipschitzData A) : ∃ L : ℝ, ∀ x y, |A.V x - A.V y| ≤ L * torusDist x y :=
  h.1

theorem W_lipschitz (h : LipschitzData A) :
    ∃ L : ℝ, ∀ x y x' y',
      |A.W x y - A.W x' y'| ≤ L * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2) :=
  h.2

/-- Zero data is Lipschitz. -/
theorem zero (d : ℕ) : LipschitzData (InteractionData.zero d) :=
  ⟨⟨0, fun x y => by simp [InteractionData.zero]⟩, ⟨0, fun x y x' y' => by
    simp [InteractionData.zero]⟩⟩

/-- Lipschitz `W` has Lipschitz sections `W(x, ·)`, with the same constant. -/
theorem W_section (h : LipschitzData A) :
    ∃ L : ℝ, ∀ x y y', |A.W x y - A.W x y'| ≤ L * torusDist y y' := by
  obtain ⟨L, hL⟩ := h.2
  refine ⟨L, fun x y y' => ?_⟩
  have := hL x y x y'
  have h0 : 0 ≤ torusDist y y' := Real.sqrt_nonneg _
  simpa [torusDist_metric.1 x, Real.sqrt_sq h0] using this

/-- Lipschitz data are determined by a sum-form bound too: a sum-of-distances Lipschitz bound for
`W` is equivalent (up to the constant) to the Euclidean product form. -/
theorem W_lipschitz_sum_iff :
    (∃ L : ℝ, ∀ x y x' y',
      |A.W x y - A.W x' y'| ≤ L * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2)) ↔
    (∃ L : ℝ, ∀ x y x' y',
      |A.W x y - A.W x' y'| ≤ L * (torusDist x x' + torusDist y y')) := by
  have hnn : ∀ x y : Torus d, 0 ≤ torusDist x y := fun x y => Real.sqrt_nonneg _
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨|L|, fun x y x' y' => (hL x y x' y').trans ?_⟩
    have h1 : Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2) ≤
        torusDist x x' + torusDist y y' := by
      apply Real.sqrt_le_iff.2
      refine ⟨add_nonneg (hnn _ _) (hnn _ _), ?_⟩
      nlinarith [mul_nonneg (hnn x x') (hnn y y')]
    exact mul_le_mul (le_abs_self L) h1 (Real.sqrt_nonneg _) (abs_nonneg L)
  · rintro ⟨L, hL⟩
    refine ⟨|L| * 2, fun x y x' y' => (hL x y x' y').trans ?_⟩
    set a := torusDist x x'
    set b := torusDist y y'
    have ha : 0 ≤ a := hnn _ _
    have hb : 0 ≤ b := hnn _ _
    have h1 : a + b ≤ 2 * Real.sqrt (a ^ 2 + b ^ 2) := by
      have : (a + b) ^ 2 ≤ (2 * Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]; nlinarith [sq_nonneg (a - b)]
      exact abs_le_of_sq_le_sq' this (by positivity) |>.2
    calc L * (a + b) ≤ |L| * (a + b) := mul_le_mul_of_nonneg_right (le_abs_self L) (by positivity)
      _ ≤ |L| * (2 * Real.sqrt (a ^ 2 + b ^ 2)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg L)
      _ = |L| * 2 * Real.sqrt (a ^ 2 + b ^ 2) := by ring

end DGPS.LipschitzData

namespace DGPS

end DGPS
