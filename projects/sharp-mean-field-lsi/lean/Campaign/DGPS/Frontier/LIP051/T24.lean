import DGPS.Frontier.LIP051.T14
import DGPS.Frontier.LIP051.T23

/-!
# LIP051.24: Arbitrary finite positive-coordinate block and closing

Task id `LIP051.24`, title "Arbitrary finite positive-coordinate block and closing" (node LIP051,
"Joint Gaussian and quadratic fluctuation limit", leaf formalization, verification V1).
Dependencies: LIP051.23 (file T23), the pass to infinite rank, and LIP051.14 (file T14), the
countable Gaussian product. The continuous mapping theorem of Mathlib enters through
`TendstoInDistribution.continuous_comp`.
Source: `frontier_decomposition_20261024/nodes/LIP051.md`, the `LIP051.24` statement and proof.

## Provides

* `DGPS.Frontier.LIP051.lip051_24_arbitrary_finite_positive_coordinate_block_closing`: main
  statement. For the data of LIP051.23 (a probability measure `μ` on `DGPS.Torus d`, a bounded
  continuous symmetric kernel `W`, a real Hilbert basis `e` of `L²(μ)` with `e 0 = 1`, and
  measurable representatives `f j` of the classes `e j`) and any finite family `j : Fin m → ℕ` of
  distinct positive indices: (1) an `L²` Wick quadratic limit `Q_T` exists on `ℕ → ℝ` for the law
  `Measure.infinitePi (fun _ => gaussianReal 0 1)`; (2) for every `L²` limit `QT` and every
  measurable version `Q'` of it, the vector `(Z_{N,j k})_{k}` together with `U_N`, under
  `Measure.pi (fun _ => μ)`, converges in distribution to `((z (j k))_k, (Q' + d_K) / 2)`; (3) the
  block `(z (j k))_k` has the standard product Gaussian law under `Measure.infinitePi`.
* `DGPS.Frontier.LIP051.rankLIP05124`: the auxiliary rank `1 + ∑ k, j k`.
* `DGPS.Frontier.LIP051.rank_pos_LIP05124`: the rank is at least one.
* `DGPS.Frontier.LIP051.le_rank_LIP05124`: each listed index is at most the rank.
* `DGPS.Frontier.LIP051.idxLIP05124`: the position `j k - 1` of the listed coordinate in
  `Fin (rankLIP05124 j)`.
* `DGPS.Frontier.LIP051.idx_succ_LIP05124`: for positive indices, the position plus one is `j k`.
* `DGPS.Frontier.LIP051.blockProj_LIP05124`: the continuous map that keeps the listed coordinates
  of a rank-`rankLIP05124 j` vector, in the prescribed order, and keeps the last energy coordinate.
* `DGPS.Frontier.LIP051.continuous_blockProj_LIP05124`: continuity of `blockProj_LIP05124`.
* `DGPS.Frontier.LIP051.blockProj_apply_LIP05124`: the projection of an embedded vector
  `(a (i + 1))_i` is `(a (j k))_k`.

## R5 notes

1. Binder and resolution of the target. The binder is exactly that of LIP051.23 (`μ`, `W`, `M`,
   `hWc`, `hs`, `hM`, `hb`, `e`, `he0`, `f`, `hfm`, `hfe`), so the abstract measure, kernel,
   basis and features are those of the prerequisite units. `Spec`, `Aux`, `KData` and
   `InteractionData` are not used; the transport to the campaign declarations is the open adapter
   LIP051.01 and is not performed here. The finite block is generalized from the positive block
   `1..m` of LIP051.23 to an arbitrary finite family of positive indices.
2. Hypotheses. No hypothesis is added beyond the specification's list. "Distinct positive natural
   numbers" is `hinj : Function.Injective j` and `hpos : ∀ k, 0 < j k`. Distinctness is used only
   for the Gaussian product law (3), through LIP051.14; the convergence (2) and the Wick limit (1)
   do not use it.
3. Empty list. The index type `Fin m` allows `m = 0`, which the specification's proof covers by
   projection onto the energy alone. Then (2) is the energy and (3) is the law of the empty block.
4. Rank. The specification's `M = max(1, j_1, …, j_m)` is replaced by the rank
   `rankLIP05124 j = 1 + ∑ k, j k`. This is a non-literal reading of "apply .23 to the first `M`
   positive coordinates": the rank is at least one and exceeds every listed index, so the block
   `1..R` covers the listed coordinates. It is internal to the proof and does not appear in the
   statement.
5. Positive modes. The coordinate of index `k` is the normalised feature sum
   `zLIP05121 N f (j k) x` of LIP051.21, with basis index `j k ≥ 1`. The zero mode `e 0 = 1` and
   the coordinate `Z_{N,0} = √N` never occur in the statement. The shift `j k - 1 + 1 = j k` is
   used only inside the proof, where `hpos` is needed.
6. Features. The representatives `f` are measurable with `f j =ᵐ[μ] e j`, as in LIP051.23. The
   statement does not depend on the choice of representatives, because laws and coefficients are
   unchanged by null modifications.
7. Wick object. `Q_T` is the `L²(γ₀)` limit of the unsmoothed positive rectangular Wick sections
   `wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f)`. Existence is conjunct (1). The
   convergence (2) is stated for every such `QT` and every measurable version `Q'` of it, as in
   LIP051.23, so the target law is well defined. Uniqueness of the `L²` limit is not restated.
8. Original diagonal. `U_N` is `energyLIP05121 (centeredKernelOf_LIP05103 μ W) N`, which uses the
   pointwise centered kernel including its diagonal. `d_K` is `dK_LIP05145 μ W`, the integral of
   the pointwise diagonal, not an `L²` class.
9. Joint law. The vector is an element of `EuclideanSpace ℝ (Fin m) × ℝ`, and the limit is
   `((z (j k))_k, (Q' z + d_K) / 2)`. The energy is not asserted to be independent of the block,
   which matches the specification.
10. Non-literal reading of "law converges". This is Mathlib's `TendstoInDistribution` along `atTop`
   with the product laws `Measure.pi (fun _ => μ)` and the limit `Measure.infinitePi`, as in
   LIP051.23.
11. Proof route. Apply LIP051.23 at rank `rankLIP05124 j`, then push the result forward by the
   continuous map `blockProj_LIP05124 j`, which reads the listed coordinates and keeps the energy
   (`TendstoInDistribution.continuous_comp`). The two composed maps agree with the target maps
   pointwise. Conjunct (3) is LIP051.14 with `ι = j`.
12. Positive-mode indexing (node note FD-002). The statement never mentions index `0`, so the
   Gaussian fluctuation concerns only the positive modes.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace DGPS.Frontier.LIP051

/-- The auxiliary rank `1 + ∑ k, j k` of a finite family of indices. It is at least one and
exceeds every listed index. -/
def rankLIP05124 {m : ℕ} (j : Fin m → ℕ) : ℕ :=
  1 + ∑ k, j k

lemma rank_pos_LIP05124 {m : ℕ} (j : Fin m → ℕ) : 1 ≤ rankLIP05124 j := by
  unfold rankLIP05124
  omega

lemma le_rank_LIP05124 {m : ℕ} (j : Fin m → ℕ) (k : Fin m) : j k ≤ rankLIP05124 j := by
  have h := Finset.single_le_sum (f := j) (fun i _ => Nat.zero_le (j i)) (Finset.mem_univ k)
  unfold rankLIP05124
  omega

/-- The position `j k - 1` of the listed coordinate `j k` in the rank-`rankLIP05124 j` block. -/
def idxLIP05124 {m : ℕ} (j : Fin m → ℕ) (k : Fin m) : Fin (rankLIP05124 j) :=
  ⟨j k - 1, by
    have h1 := le_rank_LIP05124 j k
    have h2 := rank_pos_LIP05124 j
    omega⟩

lemma idx_succ_LIP05124 {m : ℕ} (j : Fin m → ℕ) (hpos : ∀ k, 0 < j k) (k : Fin m) :
    ((idxLIP05124 j k : Fin (rankLIP05124 j)) : ℕ) + 1 = j k := by
  have h := hpos k
  show j k - 1 + 1 = j k
  omega

/-- Keeps the listed coordinates `j k` (read at the positions `j k - 1`) of the first factor and
keeps the last coordinate. -/
def blockProj_LIP05124 {m : ℕ} (j : Fin m → ℕ) :
    EuclideanSpace ℝ (Fin (rankLIP05124 j)) × ℝ → EuclideanSpace ℝ (Fin m) × ℝ :=
  fun p => (WithLp.toLp 2 (fun k : Fin m => p.1 (idxLIP05124 j k)), p.2)

lemma continuous_blockProj_LIP05124 {m : ℕ} (j : Fin m → ℕ) :
    Continuous (blockProj_LIP05124 j) := by
  unfold blockProj_LIP05124
  fun_prop

lemma blockProj_apply_LIP05124 {m : ℕ} (j : Fin m → ℕ) (hpos : ∀ k, 0 < j k)
    (a : ℕ → ℝ) (t : ℝ) :
    blockProj_LIP05124 j (WithLp.toLp 2 (fun i : Fin (rankLIP05124 j) => a ((i : ℕ) + 1)), t)
      = (WithLp.toLp 2 (fun k : Fin m => a (j k)), t) := by
  unfold blockProj_LIP05124
  simp only [idx_succ_LIP05124 j hpos]

/-- LIP051.24: arbitrary finite positive-coordinate block and closing. See the module docstring,
R5 notes. -/
theorem lip051_24_arbitrary_finite_positive_coordinate_block_closing {d : ℕ}
    {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    {W : DGPS.Torus d → DGPS.Torus d → ℝ} {M : ℝ}
    (hWc : Continuous (Function.uncurry W)) (hs : ∀ x y, W x y = W y x)
    (hM : 0 ≤ M) (hb : ∀ x y, |W x y| ≤ M)
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (he0 : e 0 = Lp.const 2 μ (1 : ℝ))
    (f : ℕ → DGPS.Torus d → ℝ) (hfm : ∀ j, Measurable (f j))
    (hfe : ∀ j, f j =ᵐ[μ] (e j : DGPS.Torus d → ℝ))
    {m : ℕ} (j : Fin m → ℕ) (hpos : ∀ k, 0 < j k) (hinj : Function.Injective j) :
    (∃ QT : (ℕ → ℝ) → ℝ, MemLp QT 2 gam_LIP05144 ∧
        Tendsto (fun R : ℕ => lpNorm (fun z : ℕ → ℝ =>
          wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z - QT z) 2 gam_LIP05144)
          atTop (𝓝 0)) ∧
    (∀ QT : (ℕ → ℝ) → ℝ, MemLp QT 2 gam_LIP05144 →
        Tendsto (fun R : ℕ => lpNorm (fun z : ℕ → ℝ =>
          wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z - QT z) 2 gam_LIP05144)
          atTop (𝓝 0) →
        ∀ Q' : (ℕ → ℝ) → ℝ, Measurable Q' → Q' =ᵐ[gam_LIP05144] QT →
        TendstoInDistribution
          (fun (N : ℕ) (x : Fin N → DGPS.Torus d) =>
            ((WithLp.toLp 2 (fun k : Fin m => zLIP05121 N f (j k) x) :
                EuclideanSpace ℝ (Fin m)),
              energyLIP05121 (centeredKernelOf_LIP05103 μ W) N x))
          atTop
          (fun z : ℕ → ℝ =>
            ((WithLp.toLp 2 (fun k : Fin m => z (j k)) : EuclideanSpace ℝ (Fin m)),
              (Q' z + dK_LIP05145 μ W) / 2))
          (fun N : ℕ => Measure.pi fun _ : Fin N => μ)
          (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1))) ∧
    (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)).map
        (fun (z : ℕ → ℝ) (k : Fin m) => z (j k)) =
      Measure.pi (fun _ : Fin m => gaussianReal 0 1) := by
  have hR : 1 ≤ rankLIP05124 j := rank_pos_LIP05124 j
  obtain ⟨hex, hconv⟩ := lip051_23_pass_infinite_rank (m := rankLIP05124 j)
    hWc hs hM hb e he0 f hfm hfe hR
  refine ⟨hex, fun QT hQT hlim Q' hQ'm hQ'eq => ?_,
    lip051_14_countable_gaussian_product_block_law j hinj⟩
  have hcomp := hconv QT hQT hlim Q' hQ'm hQ'eq
  refine (hcomp.continuous_comp (continuous_blockProj_LIP05124 j)).congr
    (fun n => Filter.Eventually.of_forall fun x => ?_)
    (Filter.Eventually.of_forall fun z => ?_)
  · exact blockProj_apply_LIP05124 j hpos (fun i => zLIP05121 n f i x) _
  · exact blockProj_apply_LIP05124 j hpos z _

end DGPS.Frontier.LIP051
