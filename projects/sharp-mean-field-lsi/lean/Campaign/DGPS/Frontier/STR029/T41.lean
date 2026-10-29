import DGPS.Frontier.STR029.T40
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-!
# STR029.41: Weak convergence and norm lower semicontinuity

Task id: STR029.41. Title: Weak convergence and norm lower semicontinuity (node STR029, size L).

Provides:
* `DGPS.Frontier.STR029.str029_41_weak_convergence_norm_lower_semicontinuity`: let `H` be a real Hilbert
  space with a countable orthonormal basis `b` (a `HilbertBasis ℕ ℝ H`), `v : ℕ → H` with `‖v n‖ ≤ C`
  (and `0 ≤ C`), let `σ` be strictly increasing with `⟪v (σ n), b j⟫_ℝ → a j` for every `j` (the output of
  STR029.39), and let `w : H` have the coordinates `⟪w, b j⟫_ℝ = a j` (the vector of STR029.40). Then
  `⟪v (σ n), x⟫_ℝ → ⟪w, x⟫_ℝ` for every `x : H` (weak convergence of `v ∘ σ` to `w`), and
  `‖w‖ ^ 2 ≤ liminf_n ‖v (σ n)‖ ^ 2`.
* `DGPS.Frontier.STR029.str029_41_weak_convergence_norm_lower_semicontinuity_chain`: the composite of
  STR029.39, STR029.40 and the main statement: every sequence in `H` bounded by `C` has a strictly
  increasing `σ` and a vector `w` such that `v ∘ σ` converges weakly to `w` and
  `‖w‖ ^ 2 ≤ liminf_n ‖v (σ n)‖ ^ 2`.
* `DGPS.Frontier.STR029.str029_41_weak_convergence_norm_lower_semicontinuity_weakSpace`: the weak
  convergence conclusion read in Mathlib's weak topology `WeakSpace ℝ H`: `toWeakSpace ℝ H (v (σ n))`
  tends to `toWeakSpace ℝ H w` along `atTop`, from the data of the main statement without the unused
  hypotheses `0 ≤ C` and `StrictMono σ`.
* `DGPS.Frontier.STR029.tendsto_inner_of_coordinates_STR02941`: the weak convergence part of the main
  statement (the pairing of `v (σ n)` with one test vector `x` converges to the pairing of `w` with `x`).
* `DGPS.Frontier.STR029.norm_le_of_coordinates_STR02941`: the weak limit satisfies `‖w‖ ≤ C`.
* `DGPS.Frontier.STR029.norm_sq_le_liminf_of_coordinates_STR02941`: the lower semicontinuity part of the
  main statement.

R5 notes:
* Carriers: `H` is a real inner product space (`[NormedAddCommGroup H] [InnerProductSpace ℝ H]`), complete
  (`[CompleteSpace H]`, as required by `HilbertBasis`). The basis `(b_j)_{j ≥ 0}` is a Mathlib
  `HilbertBasis ℕ ℝ H`, indexed by `ℕ` as in the specification. The inner product is written
  `inner ℝ _ _`; over the real numbers the order of its arguments is immaterial.
* "Under STR029.39 and STR029.40" is read as taking the data and hypotheses of their conclusions as given:
  `b`, `v`, `C`, `0 ≤ C`, `‖v n‖ ≤ C`, a strictly increasing `σ`, real numbers `a j` with
  `Tendsto (fun n => inner ℝ (v (σ n)) (b j)) atTop (𝓝 (a j))` (STR029.39), and the weak limit, called `w`
  because `v` is the name of the sequence (the specification reuses `v` for the limit). The vector `w` is
  assumed only through its coordinates `inner ℝ w (b j) = a j`. STR029.40 additionally lists
  `‖w‖ ^ 2 = ∑' j, a j ^ 2` and the bound `∑' j, a j ^ 2 ≤ C ^ 2`; both are consequences of the coordinate
  identity and the hypotheses on `v` (Parseval and the finite Bessel inequality, both proved in
  STR029.40), so they are not assumed and the statement is slightly stronger than a literal reading.
  The hypotheses `0 ≤ C` and `StrictMono σ` are listed by STR029.39 but not used by the proof (the first
  follows from the bound at `n = 0`); they are kept under the binder names `_hC` and `_hσ`. The chain
  statement shows that all data are supplied by STR029.39 and STR029.40 themselves.
* "`v_{σ(n)}` converges weakly to `v`" is read in the classical Hilbert-space form: for every test vector
  `x : H`, `⟪v (σ n), x⟫_ℝ → ⟪w, x⟫_ℝ` as `n → ∞` (`Tendsto … atTop (𝓝 …)` in `ℝ`). The variant `_weakSpace`
  restates it as convergence in the topological space `WeakSpace ℝ H` (via the Riesz representation of the
  continuous dual), so both common readings are covered.
* "`‖v‖² ≤ liminf_n ‖v_{σ(n)}‖²`" is read with `Filter.liminf` of the real sequence
  `n ↦ ‖v (σ n)‖ ^ 2` along `atTop`. This sequence is bounded in `[0, C ^ 2]`, so the liminf is the
  genuine limit inferior and not a junk value of `ℝ` as a conditionally complete lattice.
* Deviation from the written proof: the weak convergence part follows the written argument (approximate
  the test vector by a finite basis sum, bound the two tail pairings by `C` times the tail norm, use
  `‖w‖ ≤ C`); the finite basis sums are the partial sums of `HilbertBasis.hasSum_repr`. The norm bound
  `‖w‖ ≤ C` is obtained from STR029.40 (Parseval and `∑' j, a j ^ 2 ≤ C ^ 2`). Lower semicontinuity
  follows the written argument: each finite coefficient-square sum of `a` is the limit of the
  corresponding finite sums for `v (σ n)`, hence at most the liminf of the squared norms by the finite
  Bessel inequality; the supremum over finite sets is `∑' j, a j ^ 2 = ‖w‖ ^ 2` (Parseval, STR029.40).
-/

open Filter Topology

namespace DGPS.Frontier.STR029

/-- The weak limit built from coordinates has norm at most `C`: its squared norm is the sum of squares of the
coordinates, which is at most `C ^ 2`. -/
theorem norm_le_of_coordinates_STR02941 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (b : HilbertBasis ℕ ℝ H) (v : ℕ → H) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C)
    (σ : ℕ → ℕ) (a : ℕ → ℝ)
    (ha : ∀ j, Tendsto (fun n => inner ℝ (v (σ n)) (b j)) atTop (𝓝 (a j)))
    (w : H) (hw : ∀ j, inner ℝ w (b j) = a j) : ‖w‖ ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hv 0)
  have hsq : ‖w‖ ^ 2 ≤ C ^ 2 := by
    rw [norm_sq_eq_tsum_STR02940 b w]
    simpa only [hw] using (summable_sq_tsum_le_STR02940 b.orthonormal v C hv σ a ha).2
  exact (pow_le_pow_iff_left₀ (norm_nonneg w) hC two_ne_zero).mp hsq

/-- Weak convergence against one test vector `x`: approximate `x` by a finite basis sum within `δ`; the
finite pairing converges coordinatewise, and the two tail pairings are each at most `C * δ`. -/
theorem tendsto_inner_of_coordinates_STR02941 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (b : HilbertBasis ℕ ℝ H) (v : ℕ → H) (C : ℝ)
    (hv : ∀ n, ‖v n‖ ≤ C) (σ : ℕ → ℕ) (a : ℕ → ℝ)
    (ha : ∀ j, Tendsto (fun n => inner ℝ (v (σ n)) (b j)) atTop (𝓝 (a j)))
    (w : H) (hw : ∀ j, inner ℝ w (b j) = a j) (x : H) :
    Tendsto (fun n => inner ℝ (v (σ n)) x) atTop (𝓝 (inner ℝ w x)) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hv 0)
  have hwC := norm_le_of_coordinates_STR02941 b v C hv σ a ha w hw
  have hx : Tendsto (fun N => ∑ i ∈ Finset.range N, b.repr x i • b i) atTop (𝓝 x) :=
    (b.hasSum_repr x).tendsto_sum_nat
  have hfin : ∀ N, Tendsto (fun n => inner ℝ (v (σ n)) (∑ i ∈ Finset.range N, b.repr x i • b i))
      atTop (𝓝 (inner ℝ w (∑ i ∈ Finset.range N, b.repr x i • b i))) := by
    intro N
    simp only [inner_sum, inner_smul_right, hw]
    exact tendsto_finsetSum _ fun j _ => (ha j).const_mul _
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / (4 * (C + 1)) := by positivity
  obtain ⟨N, hN⟩ := (hx.eventually (Metric.ball_mem_nhds x hδ)).exists
  filter_upwards [(hfin N).eventually (Metric.ball_mem_nhds _ (half_pos hε))] with n hn
  set xN := ∑ i ∈ Finset.range N, b.repr x i • b i with hxN
  rw [Real.dist_eq] at hn ⊢
  have hr : ‖x - xN‖ < ε / (4 * (C + 1)) := by
    rw [← dist_eq_norm, dist_comm]; exact hN
  have h1 : |inner ℝ (v (σ n)) (x - xN)| ≤ C * (ε / (4 * (C + 1))) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (hv _) hr.le (norm_nonneg _) hC)
  have h2 : |inner ℝ w (x - xN)| ≤ C * (ε / (4 * (C + 1))) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul hwC hr.le (norm_nonneg _) hC)
  have hsplit : inner ℝ (v (σ n)) x - inner ℝ w x =
      (inner ℝ (v (σ n)) xN - inner ℝ w xN) +
        (inner ℝ (v (σ n)) (x - xN) - inner ℝ w (x - xN)) := by
    rw [inner_sub_right, inner_sub_right]; ring
  have hCε : 2 * (C * (ε / (4 * (C + 1)))) < ε / 2 := by
    have : C * (ε / (4 * (C + 1))) = ε / 4 * (C / (C + 1)) := by field_simp
    have hlt : C / (C + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    rw [this]; nlinarith
  rw [hsplit]
  calc |(inner ℝ (v (σ n)) xN - inner ℝ w xN) +
          (inner ℝ (v (σ n)) (x - xN) - inner ℝ w (x - xN))|
      ≤ |inner ℝ (v (σ n)) xN - inner ℝ w xN| +
          |inner ℝ (v (σ n)) (x - xN) - inner ℝ w (x - xN)| := abs_add_le _ _
    _ ≤ |inner ℝ (v (σ n)) xN - inner ℝ w xN| +
          (|inner ℝ (v (σ n)) (x - xN)| + |inner ℝ w (x - xN)|) := by
        gcongr; exact abs_sub _ _
    _ < ε := by linarith

/-- Lower semicontinuity of the squared norm along the subsequence: every finite coefficient-square sum of
`a` is the limit of the corresponding finite sums for `v (σ n)`, which are at most `‖v (σ n)‖ ^ 2` by the
finite Bessel inequality; so it is at most the liminf, and the supremum over finite sets is
`∑' j, a j ^ 2 = ‖w‖ ^ 2`. -/
theorem norm_sq_le_liminf_of_coordinates_STR02941 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (b : HilbertBasis ℕ ℝ H) (v : ℕ → H) (C : ℝ)
    (hv : ∀ n, ‖v n‖ ≤ C) (σ : ℕ → ℕ) (a : ℕ → ℝ)
    (ha : ∀ j, Tendsto (fun n => inner ℝ (v (σ n)) (b j)) atTop (𝓝 (a j)))
    (w : H) (hw : ∀ j, inner ℝ w (b j) = a j) :
    ‖w‖ ^ 2 ≤ liminf (fun n => ‖v (σ n)‖ ^ 2) atTop := by
  have hcob : IsCoboundedUnder (· ≥ ·) atTop (fun n => ‖v (σ n)‖ ^ 2) :=
    isCoboundedUnder_ge_of_le atTop (x := C ^ 2)
      fun n => pow_le_pow_left₀ (norm_nonneg _) (hv _) 2
  have hs : ∀ s : Finset ℕ, ∑ j ∈ s, a j ^ 2 ≤ liminf (fun n => ‖v (σ n)‖ ^ 2) atTop := by
    intro s
    have hlim : Tendsto (fun n => ∑ j ∈ s, inner ℝ (v (σ n)) (b j) ^ 2) atTop
        (𝓝 (∑ j ∈ s, a j ^ 2)) :=
      tendsto_finsetSum s fun j _ => (ha j).pow 2
    refine hlim.liminf_eq.symm.le.trans (liminf_le_liminf
      (Eventually.of_forall fun n => finset_sum_sq_le_STR02940 b.orthonormal (v (σ n)) s) ?_ hcob)
    exact isBoundedUnder_of ⟨0, fun n => Finset.sum_nonneg fun j _ => sq_nonneg _⟩
  have h0 : (0 : ℕ → ℝ) ≤ fun j => a j ^ 2 := fun j => sq_nonneg (a j)
  rw [norm_sq_eq_tsum_STR02940 b w]
  simp only [hw]
  exact Real.tsum_le_of_sum_le h0 hs

/-- Weak convergence and norm lower semicontinuity: under the conclusions of STR029.39 and STR029.40, the
sequence `v (σ n)` converges weakly to `w`, that is, `⟪v (σ n), x⟫_ℝ → ⟪w, x⟫_ℝ` for every `x : H`, and
`‖w‖ ^ 2 ≤ liminf_n ‖v (σ n)‖ ^ 2`. -/
theorem str029_41_weak_convergence_norm_lower_semicontinuity
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ℕ ℝ H) (v : ℕ → H) (C : ℝ) (_hC : 0 ≤ C) (hv : ∀ n, ‖v n‖ ≤ C)
    (σ : ℕ → ℕ) (_hσ : StrictMono σ) (a : ℕ → ℝ)
    (ha : ∀ j, Tendsto (fun n => inner ℝ (v (σ n)) (b j)) atTop (𝓝 (a j)))
    (w : H) (hw : ∀ j, inner ℝ w (b j) = a j) :
    (∀ x : H, Tendsto (fun n => inner ℝ (v (σ n)) x) atTop (𝓝 (inner ℝ w x))) ∧
      ‖w‖ ^ 2 ≤ liminf (fun n => ‖v (σ n)‖ ^ 2) atTop :=
  ⟨tendsto_inner_of_coordinates_STR02941 b v C hv σ a ha w hw,
    norm_sq_le_liminf_of_coordinates_STR02941 b v C hv σ a ha w hw⟩

/-- Composite with STR029.39 and STR029.40: every sequence in `H` bounded by `C` has a strictly increasing
`σ` and a vector `w` such that `v ∘ σ` converges weakly to `w` and `‖w‖ ^ 2 ≤ liminf_n ‖v (σ n)‖ ^ 2`. -/
theorem str029_41_weak_convergence_norm_lower_semicontinuity_chain
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ℕ ℝ H) (v : ℕ → H) (C : ℝ) (hC : 0 ≤ C) (hv : ∀ n, ‖v n‖ ≤ C) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ w : H,
      (∀ x : H, Tendsto (fun n => inner ℝ (v (σ n)) x) atTop (𝓝 (inner ℝ w x))) ∧
        ‖w‖ ^ 2 ≤ liminf (fun n => ‖v (σ n)‖ ^ 2) atTop := by
  obtain ⟨σ, hσ, a, ha, -, -, w, ⟨hw, -⟩, -⟩ :=
    str029_40_reconstruct_weak_limit_coordinate_limits_chain b v C hC hv
  exact ⟨σ, hσ, w, str029_41_weak_convergence_norm_lower_semicontinuity b v C hC hv σ hσ a ha w hw⟩

/-- The weak convergence conclusion read in Mathlib's weak topology `WeakSpace ℝ H`: a sequence converges
there exactly when every continuous linear functional converges, and by the Riesz representation every
continuous linear functional on `H` is a pairing against a vector. -/
theorem str029_41_weak_convergence_norm_lower_semicontinuity_weakSpace
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ℕ ℝ H) (v : ℕ → H) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C)
    (σ : ℕ → ℕ) (a : ℕ → ℝ)
    (ha : ∀ j, Tendsto (fun n => inner ℝ (v (σ n)) (b j)) atTop (𝓝 (a j)))
    (w : H) (hw : ∀ j, inner ℝ w (b j) = a j) :
    Tendsto (fun n => toWeakSpace ℝ H (v (σ n))) atTop (𝓝 (toWeakSpace ℝ H w)) := by
  have hinj : Function.Injective (topDualPairing ℝ H).flip := fun x y hxy =>
    (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr fun g => congrArg (fun F => F g) hxy
  refine (WeakBilin.tendsto_iff_forall_eval_tendsto (topDualPairing ℝ H).flip hinj).mpr fun f => ?_
  have key := tendsto_inner_of_coordinates_STR02941 b v C hv σ a ha w hw
    ((InnerProductSpace.toDual ℝ H).symm f)
  have e : ∀ y : H, inner ℝ y ((InnerProductSpace.toDual ℝ H).symm f) = f y := fun y => by
    rw [real_inner_comm]; exact InnerProductSpace.toDual_symm_apply
  simp only [e] at key
  exact key

end DGPS.Frontier.STR029
