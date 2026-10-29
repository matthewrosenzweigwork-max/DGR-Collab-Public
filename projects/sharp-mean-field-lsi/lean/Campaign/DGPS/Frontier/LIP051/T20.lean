import DGPS.Frontier.LIP051.T19
import DGPS.Frontier.LIP051.T07

/-!
# LIP051.20: Fixed-rank joint polynomial limit

Task id `LIP051.20`, title "Fixed-rank joint polynomial limit" (node LIP051, "Joint Gaussian and
quadratic fluctuation limit", leaf formalization, verification V1).
Dependencies: LIP051.19 (file T19, the finite vector central limit theorem) and the verified
continuous mapping theorem `MeasureTheory.TendstoInDistribution.continuous_comp`. The coefficients
`T i j` are the ones of LIP051.07 (`tIJ_LIP05107`, file T07).
Source: `frontier_decomposition_20261024/nodes/LIP051.md`, the `LIP051.20` statement and proof.

## Provides

* `DGPS.Frontier.LIP051.feature_sum_LIP05120`: the normalised feature sum
  `Z_{N,j} = N^{-1/2} ∑_{l<N} f (j+1) (x l)` of a sample `x : Fin N → α`, at the positive mode `j+1`.
* `DGPS.Frontier.LIP051.lip051_20_fixed_rank_joint_polynomial_limit`: main statement. For a
  probability measure `μ`, a real Hilbert basis `e` of `L²(μ)` with `e 0 = 1`, measurable
  representatives `f j` of the classes `e j`, any kernel `K`, and `1 ≤ m ≤ R`, the vectors
  `(Z_{N,1}, …, Z_{N,m}, V_{N,R})` converge in distribution under the product laws `μ^N` to
  `(z_1, …, z_m, V_{∞,R})` under `γ₀`, with `V_{N,R}` and `V_{∞,R}` as in the specification.

## R5 notes

1. Frozen statement and target. The conclusion is Mathlib's `TendstoInDistribution` along `atTop`
   on `ℕ`, with sample spaces `Fin N → α`, laws `Measure.pi (fun _ => μ)`, and limit law
   `Measure.infinitePi (fun _ => gaussianReal 0 1)` on `ℕ → ℝ`, as in LIP051.19. The joint vector
   is realised as a pair in `EuclideanSpace ℝ (Fin m) × ℝ`: the first component is the block
   `(Z_{N,1}, …, Z_{N,m})` in the order `1, …, m`, the second is the real number `V_{N,R}`. This
   pairing is an encoding of the specification's vector, not a change of its content.
2. Positive modes (FD-002 reading). Coordinate `j : Fin m` (the specification's `Z_{N,j+1}`) uses
   the basis index `(j : ℕ) + 1`, and the coefficients `T_{ab}` for `a, b : Fin R` use the indices
   `(a : ℕ) + 1`, `(b : ℕ) + 1`. Mode zero, the constant mode `e 0 = 1`, does not occur, so the
   defect `Z_{N,0} = √N` is not quantified over.
3. Hypotheses. The hypotheses on `μ`, `e`, `he0`, `f`, `hfm`, `hfe` are exactly those of
   LIP051.19, inherited unchanged. The integers satisfy `1 ≤ m` and `m ≤ R`, as written
   ("`m ≥ 1` and `R ≥ m`"). Nothing else is assumed. The specification's `Torus d` is replaced by
   a general measurable space `α`, as in LIP051.19.
4. The kernel. `K : α → α → ℝ` is arbitrary in the main statement. The quantity `V_{N,R}` is a
   polynomial in `Z_{N,1}, …, Z_{N,R}` with constant coefficients `T_{ab}` and `d_K`, so the
   convergence holds for every real kernel and no property of `K` is used. The frozen centered
   kernel is the instance `K := centeredKernelOf_LIP05103 μ W` (file T03) with `W` bounded,
   continuous and symmetric; that instance needs no hypothesis on `W`, so none is stated. The
   statistic `U_N`, the tilted law and the Wick object do not occur in this unit.
5. Coefficients `T_{ab}`. `T_{ab}` is `tIJ_LIP05107 μ K f (a+1) (b+1)`, the product-measure
   integral `∫ K(x,y) f_{a+1}(x) f_{b+1}(y) d(μ ⊗ μ)` of LIP051.07. It is computed from the
   representatives `f`; its value does not depend on the representatives, because two
   representatives of the same class differ on a `μ ⊗ μ`-null set.
6. Diagonal constant `d_K`. `d_K` is the Bochner integral `∫ K(x,x) dμ` of the pointwise diagonal
   of `K`, with no almost-everywhere representative of `K` taken. The Lean convention gives value
   zero to a non-integrable diagonal; the frozen centered kernel has a bounded diagonal, so the
   convention is not reached in the intended instance.
7. Gaussian quadratic `Q_R`. The packet names `Q_R` the `L²` Wick quadratic limit without a
   formula here. The statement reads it as `Q_R(z) = ∑_{a,b<R} T_{ab} (z_{a+1} z_{b+1} - δ_{ab})`,
   the same polynomial as `V_{N,R}` evaluated on the Gaussian block, as the proof sentence
   "exactly the stated target by the definition of `Q_R`" requires.
8. Normalisation at `N = 0`. The factor is the real power `(N : ℝ) ^ (-(1/2 : ℝ))`, which is zero
   at `N = 0`. The value at `N = 0` is immaterial for the limit, as in LIP051.19.
9. Convergence in distribution is read as in LIP051.19, note 8.
10. Proof route. LIP051.19 gives convergence in distribution of the feature block of length `R`
    (rank `R ≥ 1`). The map `g : EuclideanSpace ℝ (Fin R) → EuclideanSpace ℝ (Fin m) × ℝ` sends
    `v` to its first `m` coordinates together with `(1/2)(∑_{a,b} T_{ab}(v_a v_b - δ_{ab}) + d_K)`.
    It is continuous, since it is built from coordinate projections, finite sums and products.
    Composition with `g` (the continuous mapping theorem) gives the claim: `g` applied to the
    Gaussian block is exactly the stated target.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace DGPS.Frontier.LIP051

/-- The normalised feature sum `Z_{N,j} = N^{-1/2} ∑_{l<N} f (j+1) (x l)` of a sample
`x : Fin N → α`, at the positive mode `j + 1`. -/
noncomputable def feature_sum_LIP05120 {α : Type*} (f : ℕ → α → ℝ) (N : ℕ) (x : Fin N → α)
    (j : ℕ) : ℝ :=
  (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l : Fin N, f (j + 1) (x l)

/-- **LIP051.20.** Fixed-rank joint polynomial limit. For a probability measure `μ` on `α`, a real
Hilbert basis `e` of `L²(μ)` with `e 0 = 1`, measurable representatives `f j` of the classes
`e j`, any kernel `K`, and integers `1 ≤ m ≤ R`, the vectors
`(Z_{N,1}, …, Z_{N,m}, V_{N,R})` under the product laws `μ^N` converge in distribution to
`(z_1, …, z_m, V_{∞,R})` under `γ₀ = Measure.infinitePi (fun _ => gaussianReal 0 1)`, where
`V_{N,R} = (1/2) (∑_{a,b<R} T_{ab} (Z_{N,a+1} Z_{N,b+1} - δ_{ab}) + d_K)`,
`V_{∞,R} = (1/2) (∑_{a,b<R} T_{ab} (z_{a+1} z_{b+1} - δ_{ab}) + d_K)`,
`T_{ab} = ∬ K(x,y) f_{a+1}(x) f_{b+1}(y) dμ dμ` and `d_K = ∫ K(x,x) dμ`. -/
theorem lip051_20_fixed_rank_joint_polynomial_limit {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (he0 : e 0 = Lp.const 2 μ (1 : ℝ))
    (f : ℕ → α → ℝ) (hfm : ∀ j, Measurable (f j)) (hfe : ∀ j, f j =ᵐ[μ] (e j : α → ℝ))
    (K : α → α → ℝ) (m R : ℕ) (hm : 1 ≤ m) (hmR : m ≤ R) :
    TendstoInDistribution
      (fun (N : ℕ) (x : Fin N → α) =>
        ((WithLp.toLp 2 (fun j : Fin m => feature_sum_LIP05120 f N x (j : ℕ)) :
            EuclideanSpace ℝ (Fin m)),
          (1 / 2 : ℝ) * ((∑ a : Fin R, ∑ b : Fin R,
              tIJ_LIP05107 μ K f ((a : ℕ) + 1) ((b : ℕ) + 1) *
                (feature_sum_LIP05120 f N x (a : ℕ) * feature_sum_LIP05120 f N x (b : ℕ)
                  - (if a = b then (1 : ℝ) else 0)))
            + ∫ y, K y y ∂μ)))
      atTop
      (fun z : ℕ → ℝ =>
        ((WithLp.toLp 2 (fun j : Fin m => z ((j : ℕ) + 1)) : EuclideanSpace ℝ (Fin m)),
          (1 / 2 : ℝ) * ((∑ a : Fin R, ∑ b : Fin R,
              tIJ_LIP05107 μ K f ((a : ℕ) + 1) ((b : ℕ) + 1) *
                (z ((a : ℕ) + 1) * z ((b : ℕ) + 1) - (if a = b then (1 : ℝ) else 0)))
            + ∫ y, K y y ∂μ)))
      (fun N : ℕ => Measure.pi fun _ : Fin N => μ)
      (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) := by
  have hr : 1 ≤ R := le_trans hm hmR
  have hT := lip051_19_finite_vector_central_limit_theorem μ e he0 f hfm hfe R hr
  let g : EuclideanSpace ℝ (Fin R) → EuclideanSpace ℝ (Fin m) × ℝ := fun v =>
    ((WithLp.toLp 2 (fun j : Fin m => v (Fin.castLE hmR j)) : EuclideanSpace ℝ (Fin m)),
      (1 / 2 : ℝ) * ((∑ a : Fin R, ∑ b : Fin R,
          tIJ_LIP05107 μ K f ((a : ℕ) + 1) ((b : ℕ) + 1) *
            (v a * v b - (if a = b then (1 : ℝ) else 0)))
        + ∫ y, K y y ∂μ))
  have hg : Continuous g := by
    fun_prop
  exact hT.continuous_comp hg

end DGPS.Frontier.LIP051
