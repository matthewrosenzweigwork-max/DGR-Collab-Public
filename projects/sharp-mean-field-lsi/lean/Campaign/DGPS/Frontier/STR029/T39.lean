import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Sequences

/-!
# STR029.39: Convergent coordinates of a bounded Hilbert sequence

Task id: STR029.39. Title: Convergent coordinates of a bounded Hilbert sequence (node STR029, size L).

Provides:
* `DGPS.Frontier.STR029.str029_39_convergent_coordinates_bounded_hilbert_sequence`: for a real Hilbert space `H`
  with a countable orthonormal basis `b` (a `HilbertBasis ℕ ℝ H`) and a sequence `v` in `H` with
  `‖v n‖ ≤ C` for all `n` (where `0 ≤ C`), there are a strictly increasing `σ : ℕ → ℕ` and real numbers `a j`
  such that `⟪v (σ n), b j⟫_ℝ → a j` as `n → ∞`, for every `j`.
* `DGPS.Frontier.STR029.str029_39_convergent_coordinates_bounded_hilbert_sequence_orthonormal`: the same
  conclusion for an arbitrary real inner product space `H` (completeness is not used) and an arbitrary
  orthonormal family `b : ℕ → H`, with no density of its span required and no sign hypothesis on `C`.
* `DGPS.Frontier.STR029.convergent_coordinates_of_bounded_STR02939`: the underlying statement about
  coefficient arrays `x : ℕ → ℕ → ℝ` with `|x n j| ≤ C`: some strictly increasing `σ` makes every
  coordinate sequence `n ↦ x (σ n) j` converge.
* `DGPS.Frontier.STR029.coordinate_mem_Icc_STR02939`: for an orthonormal `b` and `‖v‖ ≤ C`, every coefficient
  `⟪v, b j⟫_ℝ` lies in `[-C, C]`.

R5 notes:
* Carriers: `H` is a real inner product space (`[NormedAddCommGroup H] [InnerProductSpace ℝ H]`), complete in the
  main statement (`[CompleteSpace H]`, as required by `HilbertBasis`). The countable orthonormal basis
  `(b_j)_{j ≥ 0}` is read as a Mathlib `HilbertBasis ℕ ℝ H`, whose coercion to `ℕ → H` is the family of basis
  vectors; its orthonormality is `HilbertBasis.orthonormal`. The index set is `ℕ`, as in the specification
  (`j ≥ 0`); a finite basis is outside the specification's indexing and is not covered by the main statement.
* The inner product `⟨v_{σ(n)}, b_j⟩` is written `inner ℝ (v (σ n)) (b j)` (displayed `⟪v, w⟫_ℝ`); over the real
  numbers the order of the arguments is immaterial.
* The sequence `(v_n)` is `v : ℕ → H`. The bound is `∀ n, ‖v n‖ ≤ C` with `C : ℝ` and the listed hypothesis
  `0 ≤ C`. The sign hypothesis is not needed by the proof (it follows from the bound at `n = 0`); it is kept in
  the main statement, under the binder name `_hC` to mark it as unused, because the specification lists it,
  and dropped in the `_orthonormal` variant.
* `σ` is `StrictMono σ` with `σ : ℕ → ℕ`, and "converges" is `Filter.Tendsto … atTop (nhds (a j))` in `ℝ`.
  The limits `a j` are only real numbers: the specification asserts coordinatewise convergence, and neither
  membership of `a` in `ℓ²` nor weak convergence of the subsequence in `H` is claimed or proved.
* Generalization (strengthening, not a change of the statement): the proof uses only `|⟪v, b j⟫| ≤ ‖v‖ ‖b j‖`
  and `‖b j‖ = 1`, hence orthonormality of the family; the main statement is the instance of the
  `_orthonormal` variant at `b.orthonormal`.
* Deviation from the specification's proof: none in substance. The coefficient array of `v n` lies in the
  product `Set.pi univ (fun _ => Set.Icc (-C) C)` of compact intervals (`isCompact_univ_pi`); the ambient
  space `ℕ → ℝ` has a countable product topology and is first countable, so `IsCompact.tendsto_subseq`
  extracts a subsequence converging in the product topology, which is coordinatewise convergence
  (`tendsto_pi_nhds`). Sequential compactness is used through the Mathlib lemma for compact sets in a first
  countable space, so no separate metrizability argument is written out.
-/

open Filter Topology

namespace DGPS.Frontier.STR029

/-- A bounded array of reals has a strictly increasing subsequence along which every coordinate sequence
converges. Coordinates `x n j` with `|x n j| ≤ C` lie in the compact product `∏ⱼ [-C, C]`, which is
sequentially compact in the product topology of `ℕ → ℝ`. -/
theorem convergent_coordinates_of_bounded_STR02939 (x : ℕ → ℕ → ℝ) (C : ℝ)
    (hx : ∀ n j, |x n j| ≤ C) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ a : ℕ → ℝ,
      ∀ j, Tendsto (fun n => x (σ n) j) atTop (𝓝 (a j)) := by
  have hcpt : IsCompact (Set.pi Set.univ fun _ : ℕ => Set.Icc (-C) C) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ n, x n ∈ Set.pi Set.univ fun _ : ℕ => Set.Icc (-C) C := by
    intro n j _
    exact abs_le.mp (hx n j)
  obtain ⟨a, _, σ, hσ, hlim⟩ := hcpt.tendsto_subseq hmem
  exact ⟨σ, hσ, a, fun j => tendsto_pi_nhds.mp hlim j⟩

/-- Every coefficient of a vector of norm at most `C` against an orthonormal family lies in `[-C, C]`. -/
theorem coordinate_mem_Icc_STR02939 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {b : ℕ → H} (hb : Orthonormal ℝ b) {v : H} {C : ℝ} (hv : ‖v‖ ≤ C) (j : ℕ) :
    |inner ℝ v (b j)| ≤ C := by
  calc |inner ℝ v (b j)| ≤ ‖v‖ * ‖b j‖ := abs_real_inner_le_norm v (b j)
    _ = ‖v‖ := by rw [hb.1 j, mul_one]
    _ ≤ C := hv

/-- Bounded sequences in a real inner product space have a subsequence whose coefficients against any
orthonormal family `b : ℕ → H` all converge. -/
theorem str029_39_convergent_coordinates_bounded_hilbert_sequence_orthonormal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : ℕ → H) (hb : Orthonormal ℝ b) (v : ℕ → H) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ a : ℕ → ℝ,
      ∀ j, Tendsto (fun n => inner ℝ (v (σ n)) (b j)) atTop (𝓝 (a j)) :=
  convergent_coordinates_of_bounded_STR02939 (fun n j => inner ℝ (v n) (b j)) C
    fun n j => coordinate_mem_Icc_STR02939 hb (hv n) j

/-- Convergent coordinates of a bounded Hilbert sequence: if `H` is a real Hilbert space with a countable
orthonormal basis `(b j)_{j ≥ 0}` and `‖v n‖ ≤ C` for all `n` with `0 ≤ C`, then there are a strictly
increasing `σ : ℕ → ℕ` and real numbers `a j` such that `⟪v (σ n), b j⟫_ℝ → a j` for every `j`. -/
theorem str029_39_convergent_coordinates_bounded_hilbert_sequence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ℕ ℝ H) (v : ℕ → H) (C : ℝ) (_hC : 0 ≤ C) (hv : ∀ n, ‖v n‖ ≤ C) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ a : ℕ → ℝ,
      ∀ j, Tendsto (fun n => inner ℝ (v (σ n)) (b j)) atTop (𝓝 (a j)) :=
  str029_39_convergent_coordinates_bounded_hilbert_sequence_orthonormal b b.orthonormal v C hv

end DGPS.Frontier.STR029
