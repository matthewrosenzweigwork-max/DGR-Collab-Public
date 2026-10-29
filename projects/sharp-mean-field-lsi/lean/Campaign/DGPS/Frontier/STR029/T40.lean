import DGPS.Frontier.STR029.T39
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# STR029.40: Reconstruct the weak limit from coordinate limits

Task id: STR029.40. Title: Reconstruct the weak limit from coordinate limits (node STR029, size L).

Provides:
* `DGPS.Frontier.STR029.str029_40_reconstruct_weak_limit_coordinate_limits`: let `H` be a real Hilbert
  space with a countable orthonormal basis `b` (a `HilbertBasis ℕ ℝ H`), `v : ℕ → H` with `‖v n‖ ≤ C`
  (and `0 ≤ C`), and let `σ` be strictly increasing with `⟪v (σ n), b j⟫_ℝ → a j` for every `j` (the
  output of STR029.39). Then `j ↦ a j ^ 2` is summable, `∑' j, a j ^ 2 ≤ C ^ 2`, and there is a unique
  `w : H` with `⟪w, b j⟫_ℝ = a j` for all `j` and `‖w‖ ^ 2 = ∑' j, a j ^ 2`.
* `DGPS.Frontier.STR029.str029_40_reconstruct_weak_limit_coordinate_limits_chain`: the composite of
  STR029.39 and the main statement: every bounded sequence in `H` has a strictly increasing `σ` and
  coordinate limits `a` with the conclusion of the main statement.
* `DGPS.Frontier.STR029.str029_40_reconstruct_weak_limit_coordinate_limits_unique_of_coordinates`: two
  vectors with the same coordinates against a Hilbert basis are equal (no norm condition needed).
* `DGPS.Frontier.STR029.finset_sum_sq_le_STR02940`: finite Bessel inequality
  `∑ j ∈ s, ⟪x, b j⟫^2 ≤ ‖x‖^2` for an orthonormal family indexed by `ℕ`.
* `DGPS.Frontier.STR029.sum_sq_limit_le_STR02940`: a finite coefficient-square sum of the limits `a` is at
  most `C ^ 2`.
* `DGPS.Frontier.STR029.summable_sq_tsum_le_STR02940`: summability of `a j ^ 2` and the bound
  `∑' j, a j ^ 2 ≤ C ^ 2`.
* `DGPS.Frontier.STR029.exists_coordinates_STR02940`: a square-summable real sequence is the coordinate
  sequence of some vector of `H`.
* `DGPS.Frontier.STR029.norm_sq_eq_tsum_STR02940`: Parseval, `‖w‖ ^ 2 = ∑' j, ⟪w, b j⟫^2`.
* `DGPS.Frontier.STR029.eq_of_coordinates_eq_STR02940`: vectors with equal coordinates coincide.

R5 notes:
* Carriers: `H` is a real inner product space (`[NormedAddCommGroup H] [InnerProductSpace ℝ H]`), complete
  (`[CompleteSpace H]`, as required by `HilbertBasis`). The basis `(b_j)_{j ≥ 0}` is a Mathlib
  `HilbertBasis ℕ ℝ H`; its coercion to `ℕ → H` is the family of basis vectors. The index set is `ℕ`
  as in the specification.
* "Under STR029.39" is read as taking the data and hypotheses of the conclusion of STR029.39 as given:
  `b`, `v`, `C`, `0 ≤ C`, `‖v n‖ ≤ C`, a strictly increasing `σ : ℕ → ℕ`, real numbers `a j`, and
  `Tendsto (fun n => inner ℝ (v (σ n)) (b j)) atTop (𝓝 (a j))` for every `j`. The hypotheses `0 ≤ C`
  and `StrictMono σ` are listed by STR029.39 but are not used by the proof (the first follows from the
  bound at `n = 0`, and the second is immaterial for convergence of finite sums); they are kept under the
  binder names `_hC` and `_hσ` to mark them as unused. The chain statement shows that the data can be
  supplied by STR029.39 itself.
* The weak limit is called `w` (the specification calls it `v`, which is already the name of the
  sequence). The inner product `⟨w, b_j⟩` is written `inner ℝ w (b j)`; over the real numbers the order
  of the arguments is immaterial.
* "Σ_j a_j² ≤ C²" is read as the conjunction of summability of `j ↦ a j ^ 2` and the bound on its
  `tsum`; summability is part of the conclusion, so the bound is not vacuous.
* "There is a unique `v` with `⟨v, b_j⟩ = a_j` and `‖v‖² = Σ a_j²`" is stated as
  `∃! w, (∀ j, inner ℝ w (b j) = a j) ∧ ‖w‖ ^ 2 = ∑' j, a j ^ 2`. The norm identity is a consequence of
  the coordinate identity (Parseval); the uniqueness holds already among all vectors with these
  coordinates (`..._unique_of_coordinates`), which is stronger than uniqueness under both conditions.
* Deviation from the written proof: the specification builds the limit as the Cauchy limit of the partial
  sums `∑_{j ≤ N} a_j b_j`. Here the same vector is produced by the isometric isomorphism
  `HilbertBasis.repr : H ≃ₗᵢ ℓ²(ℕ, ℝ)` applied to the sequence `a` (which lies in `ℓ²` by the first part),
  which packages the completeness argument. Square summability follows the written proof: pass to the
  limit in each finite coefficient-square sum, bound it by Bessel's inequality for `v (σ n)`, and conclude
  with `summable_of_sum_le` and `Real.tsum_le_of_sum_le`. Uniqueness uses Parseval for the difference of
  two candidates, which is the stated orthogonality argument.
-/

open Filter Topology

namespace DGPS.Frontier.STR029

/-- Finite Bessel inequality for an orthonormal family indexed by `ℕ`, with the vector in the first slot
of each coefficient. -/
theorem finset_sum_sq_le_STR02940 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {b : ℕ → H} (hb : Orthonormal ℝ b) (x : H) (s : Finset ℕ) :
    ∑ j ∈ s, inner ℝ x (b j) ^ 2 ≤ ‖x‖ ^ 2 := by
  refine le_trans (le_of_eq ?_) (hb.sum_inner_products_le (s := s) x)
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.norm_eq_abs, sq_abs, real_inner_comm x (b j)]

/-- Passing to the limit along `σ` in the finite Bessel inequality for `v (σ n)`: every finite
coefficient-square sum of the limits `a` is at most `C ^ 2`. -/
theorem sum_sq_limit_le_STR02940 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {b : ℕ → H} (hb : Orthonormal ℝ b) (v : ℕ → H) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C)
    (σ : ℕ → ℕ) (a : ℕ → ℝ)
    (ha : ∀ j, Tendsto (fun n => inner ℝ (v (σ n)) (b j)) atTop (𝓝 (a j))) (s : Finset ℕ) :
    ∑ j ∈ s, a j ^ 2 ≤ C ^ 2 := by
  have hlim : Tendsto (fun n => ∑ j ∈ s, inner ℝ (v (σ n)) (b j) ^ 2) atTop
      (𝓝 (∑ j ∈ s, a j ^ 2)) :=
    tendsto_finsetSum s fun j _ => (ha j).pow 2
  refine le_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  calc ∑ j ∈ s, inner ℝ (v (σ n)) (b j) ^ 2 ≤ ‖v (σ n)‖ ^ 2 :=
        finset_sum_sq_le_STR02940 hb (v (σ n)) s
    _ ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hv (σ n)) 2

/-- The limits `a` are square summable with total at most `C ^ 2`. -/
theorem summable_sq_tsum_le_STR02940 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {b : ℕ → H} (hb : Orthonormal ℝ b) (v : ℕ → H) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C)
    (σ : ℕ → ℕ) (a : ℕ → ℝ)
    (ha : ∀ j, Tendsto (fun n => inner ℝ (v (σ n)) (b j)) atTop (𝓝 (a j))) :
    Summable (fun j => a j ^ 2) ∧ ∑' j, a j ^ 2 ≤ C ^ 2 := by
  have h := sum_sq_limit_le_STR02940 hb v C hv σ a ha
  have h0 : (0 : ℕ → ℝ) ≤ fun j => a j ^ 2 := fun j => sq_nonneg (a j)
  exact ⟨summable_of_sum_le h0 h, Real.tsum_le_of_sum_le h0 h⟩

/-- Every square-summable real sequence is the coordinate sequence of a vector of `H`. -/
theorem exists_coordinates_STR02940 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (b : HilbertBasis ℕ ℝ H) (a : ℕ → ℝ) (ha : Summable fun j => a j ^ 2) :
    ∃ w : H, ∀ j, inner ℝ w (b j) = a j := by
  have hmem : Memℓp a 2 := memℓp_gen (by simpa [Real.norm_eq_abs] using ha)
  refine ⟨b.repr.symm ⟨a, hmem⟩, fun j => ?_⟩
  rw [real_inner_comm, ← b.repr_apply_apply, LinearIsometryEquiv.apply_symm_apply]

/-- Parseval's identity for a Hilbert basis indexed by `ℕ`. -/
theorem norm_sq_eq_tsum_STR02940 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (b : HilbertBasis ℕ ℝ H) (w : H) :
    ‖w‖ ^ 2 = ∑' j, inner ℝ w (b j) ^ 2 := by
  have h := b.tsum_inner_mul_inner w w
  rw [real_inner_self_eq_norm_sq] at h
  rw [← h]
  refine tsum_congr fun j => ?_
  rw [real_inner_comm w (b j)]
  ring

/-- Two vectors with the same coordinates against a Hilbert basis are equal. -/
theorem eq_of_coordinates_eq_STR02940 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (b : HilbertBasis ℕ ℝ H) {w₁ w₂ : H}
    (h : ∀ j, inner ℝ w₁ (b j) = inner ℝ w₂ (b j)) : w₁ = w₂ := by
  have h0 : ‖w₁ - w₂‖ ^ 2 = 0 := by
    rw [norm_sq_eq_tsum_STR02940 b]
    simp [inner_sub_left, h]
  exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0))

/-- Uniqueness of a vector with prescribed coordinates against a Hilbert basis. -/
theorem str029_40_reconstruct_weak_limit_coordinate_limits_unique_of_coordinates
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ℕ ℝ H) (a : ℕ → ℝ) {w₁ w₂ : H}
    (h₁ : ∀ j, inner ℝ w₁ (b j) = a j) (h₂ : ∀ j, inner ℝ w₂ (b j) = a j) : w₁ = w₂ :=
  eq_of_coordinates_eq_STR02940 b fun j => by rw [h₁ j, h₂ j]

/-- Reconstruct the weak limit from coordinate limits: under the conclusion of STR029.39, the limits `a j`
are square summable with `∑' j, a j ^ 2 ≤ C ^ 2`, and there is a unique `w : H` with
`⟪w, b j⟫_ℝ = a j` for every `j` and `‖w‖ ^ 2 = ∑' j, a j ^ 2`. -/
theorem str029_40_reconstruct_weak_limit_coordinate_limits
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ℕ ℝ H) (v : ℕ → H) (C : ℝ) (_hC : 0 ≤ C) (hv : ∀ n, ‖v n‖ ≤ C)
    (σ : ℕ → ℕ) (_hσ : StrictMono σ) (a : ℕ → ℝ)
    (ha : ∀ j, Tendsto (fun n => inner ℝ (v (σ n)) (b j)) atTop (𝓝 (a j))) :
    Summable (fun j => a j ^ 2) ∧ ∑' j, a j ^ 2 ≤ C ^ 2 ∧
      ∃! w : H, (∀ j, inner ℝ w (b j) = a j) ∧ ‖w‖ ^ 2 = ∑' j, a j ^ 2 := by
  obtain ⟨hs, hle⟩ := summable_sq_tsum_le_STR02940 b.orthonormal v C hv σ a ha
  obtain ⟨w, hw⟩ := exists_coordinates_STR02940 b a hs
  refine ⟨hs, hle, w, ⟨hw, ?_⟩, ?_⟩
  · rw [norm_sq_eq_tsum_STR02940 b w]
    exact tsum_congr fun j => by rw [hw j]
  · rintro w' ⟨hw', -⟩
    exact str029_40_reconstruct_weak_limit_coordinate_limits_unique_of_coordinates b a hw' hw

/-- Composite with STR029.39: every sequence in `H` bounded by `C` has a strictly increasing `σ` and
real limits `a j` of its coordinates along `σ`, and the limits satisfy the conclusion of the main
statement. -/
theorem str029_40_reconstruct_weak_limit_coordinate_limits_chain
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ℕ ℝ H) (v : ℕ → H) (C : ℝ) (hC : 0 ≤ C) (hv : ∀ n, ‖v n‖ ≤ C) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ a : ℕ → ℝ,
      (∀ j, Tendsto (fun n => inner ℝ (v (σ n)) (b j)) atTop (𝓝 (a j))) ∧
      Summable (fun j => a j ^ 2) ∧ ∑' j, a j ^ 2 ≤ C ^ 2 ∧
      ∃! w : H, (∀ j, inner ℝ w (b j) = a j) ∧ ‖w‖ ^ 2 = ∑' j, a j ^ 2 := by
  obtain ⟨σ, hσ, a, ha⟩ := str029_39_convergent_coordinates_bounded_hilbert_sequence b v C hC hv
  exact ⟨σ, hσ, a, ha, str029_40_reconstruct_weak_limit_coordinate_limits b v C hC hv σ hσ a ha⟩

end DGPS.Frontier.STR029
