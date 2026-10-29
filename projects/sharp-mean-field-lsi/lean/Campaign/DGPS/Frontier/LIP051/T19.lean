import DGPS.Frontier.LIP051.T14
import DGPS.Frontier.LIP051.T18

/-!
# LIP051.19: Finite vector central limit theorem

Task id `LIP051.19`, title "Finite vector central limit theorem" (node LIP051, "Joint Gaussian and
quadratic fluctuation limit", leaf formalization, verification V1).
Dependencies: LIP051.14 (file T14, countable Gaussian product) and LIP051.18 (file T18, scalar
characteristic functions of feature sums).
Source: `frontier_decomposition_20261024/nodes/LIP051.md`, the `LIP051.19` statement and proof.

## Provides

* `DGPS.Frontier.LIP051.lip051_19_sample_charFun_LIP05119`: for a probability measure `μ`, `N`,
  `r` and `v : EuclideanSpace ℝ (Fin r)`, the characteristic function at `v` of the law under
  `μ^N` of the finite vector `(N^{-1/2} ∑_{l<N} f_{j+1}(X_l))_{j<r}` equals the expectation of
  `exp (i ∑_{j<r} v_j Z_{N,j})`.
* `DGPS.Frontier.LIP051.lip051_19_finite_vector_central_limit_theorem`: for every `r ≥ 1`, the
  finite vector `(Z_{N,1}, …, Z_{N,r})` under the product laws `μ^N` on `Fin N → α` converges in
  distribution (Mathlib `MeasureTheory.TendstoInDistribution`, along `atTop`) to the block
  `(z_1, …, z_r)` of the coordinates of `γ₀ = Measure.infinitePi (fun _ => gaussianReal 0 1)`,
  realised in `EuclideanSpace ℝ (Fin r)`.

## R5 notes

1. Frozen statement. The conclusion is the displayed convergence of the specification, written
   with Mathlib's `TendstoInDistribution`. The sample spaces are `Fin N → α` with the product
   laws `Measure.pi (fun _ => μ)`, which vary with `N`; the limit lives on `ℕ → ℝ` with law
   `γ₀`. The campaign identifications (`S.mu`, `Torus d`, `Hw d S.w`, `S.e`) are left to
   LIP051.01, as in LIP051.18.
2. Hypotheses. The hypotheses are exactly those of LIP051.18 and are inherited unchanged: `μ` a
   probability measure on `α`, `e` a real Hilbert basis of `L²(μ)` with `e 0 = 1`, measurable
   representatives `f j` of the classes `e j`. No boundedness, moment or continuity hypothesis is
   added, and none is used. The specification's `Torus d` is replaced by an arbitrary measurable
   space `α`; this generalisation is the one in LIP051.18.
3. Range of `r`. The binder `hr : 1 ≤ r` is kept as written ("for each fixed `r ≥ 1`"). It is
   passed to LIP051.18, which does not need it; the statement is therefore also true for `r = 0`,
   but that case is not stated.
4. Positive modes (FD-002 reading). The reading adopted is the positive-mode reading: the block
   coordinate `j : Fin r` (the specification's `Z_{N,j+1}`, `z_{j+1}`) is paired with the basis
   index `(j : ℕ) + 1` on the data side (`f ((j : ℕ) + 1)`) and with the Gaussian coordinate
   `z ((j : ℕ) + 1)` on the target side. Mode zero, the constant mode `e 0 = 1`, does not occur in
   the block, so the defect `Z_{N,0} = √N` is not quantified over. The mode-zero binder of
   LIP051.14 (which ranges over all injective index maps) is not used here; the block map is the
   injective map `j ↦ j + 1`, so only positive modes enter.
5. Vector realisation. The finite vector is realised in `EuclideanSpace ℝ (Fin r)` through
   `WithLp.toLp 2`, with entries in the order `j = 0, …, r-1` of the specification's coordinates
   `1, …, r`. The pairing in the characteristic function is Mathlib's real inner product on
   `EuclideanSpace`.
6. Normalisation at `N = 0`. The normalisation is written as the real power
   `(N : ℝ) ^ (-(1/2 : ℝ))`, which is `0` at `N = 0`, so the `N = 0` term is the zero vector. The
   value at `N = 0` is immaterial for the limit and is not a choice made by the statement. The
   statement is for all `N` (indexed by `atTop` on `ℕ`), as Mathlib requires; no finite
   modification argument is needed, because Mathlib's Lévy lemma quantifies over all indices.
7. Representatives. `Z_{N,j}` is built from the measurable representatives `f (j+1)`, not from
   the classes `e (j+1)`. Laws, and hence convergence in distribution, do not depend on the choice
   of representative; the proof is given for the representatives supplied, with no choice made
   inside it.
8. Convergence in distribution. "Converges in distribution" is read as Mathlib's
   `TendstoInDistribution`, that is convergence of the pushforward probability measures along
   `atTop` in the weak topology on `ProbabilityMeasure (EuclideanSpace ℝ (Fin r))`. The proof uses
   the finite-dimensional Lévy convergence lemma in the direction characteristic functions ⇒
   convergence in distribution.
9. Proof route. The characteristic functions of the finite vectors converge pointwise to
   `exp (-(1/2) ∑_j v_j²)` by LIP051.18 (after the rewriting in
   `lip051_19_sample_charFun_LIP05119`). The characteristic function of the Gaussian block is
   `exp (-(∑_j v_j²)/2)` by LIP051.14 with the injective index map `j ↦ j + 1`. The two agree, and
   the Lévy lemma gives the claim. The vector `Z_{N,j}` and the Gaussian block are measurable, so
   the almost-everywhere measurability hypotheses of the Lévy lemma hold.
10. Not used here. The tilted particle law, the kernel `K`, the statistic `U_N`, the Wick object,
    and the diagonal convention do not occur in this unit.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace DGPS.Frontier.LIP051

/-- Characteristic function of the law of the finite vector `(Z_{N,j})_{j<r}` under the product
measure `μ^N`, written as the expectation of `exp (i ∑_j v_j Z_{N,j})`. -/
theorem lip051_19_sample_charFun_LIP05119 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : ℕ → α → ℝ) (hfm : ∀ j, Measurable (f j)) (N r : ℕ)
    (v : EuclideanSpace ℝ (Fin r)) :
    charFun ((Measure.pi fun _ : Fin N => μ).map (fun x : Fin N → α =>
        (WithLp.toLp 2 (fun j : Fin r => (N : ℝ) ^ (-(1 / 2 : ℝ)) *
          ∑ l : Fin N, f ((j : ℕ) + 1) (x l)) : EuclideanSpace ℝ (Fin r)))) v =
      ∫ x : Fin N → α, Complex.exp (Complex.I * ∑ j : Fin r, (v j : ℂ) *
          (((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l : Fin N, f ((j : ℕ) + 1) (x l) : ℝ) : ℂ))
        ∂(Measure.pi fun _ : Fin N => μ) := by
  have hm : Measurable (fun x : Fin N → α => (WithLp.toLp 2 (fun j : Fin r =>
      (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l : Fin N, f ((j : ℕ) + 1) (x l)) :
      EuclideanSpace ℝ (Fin r))) := by
    fun_prop
  rw [charFun_apply, integral_map hm.aemeasurable
    (by fun_prop : Measurable _).aestronglyMeasurable]
  congr 1
  funext x
  congr 1
  simp [PiLp.inner_apply, mul_comm]

/-- **LIP051.19.** For a probability measure `μ` on `α`, a real Hilbert basis `e` of `L²(μ)` with
`e 0 = 1`, measurable representatives `f j` of the classes `e j`, and every `r ≥ 1`, the finite
vectors `(Z_{N,j})_{j<r}`, `Z_{N,j} = N^{-1/2} ∑_{l<N} f_{j+1}(X_l)`, under the product laws
`μ^N` on `Fin N → α` converge in distribution to `(z_{j+1})_{j<r}` under
`γ₀ = Measure.infinitePi (fun _ => gaussianReal 0 1)` on `ℕ → ℝ`, in `EuclideanSpace ℝ (Fin r)`. -/
theorem lip051_19_finite_vector_central_limit_theorem {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (he0 : e 0 = Lp.const 2 μ (1 : ℝ))
    (f : ℕ → α → ℝ) (hfm : ∀ j, Measurable (f j)) (hfe : ∀ j, f j =ᵐ[μ] (e j : α → ℝ))
    (r : ℕ) (hr : 1 ≤ r) :
    TendstoInDistribution
      (fun (N : ℕ) (x : Fin N → α) =>
        (WithLp.toLp 2 (fun j : Fin r => (N : ℝ) ^ (-(1 / 2 : ℝ)) *
          ∑ l : Fin N, f ((j : ℕ) + 1) (x l)) : EuclideanSpace ℝ (Fin r)))
      atTop
      (fun z : ℕ → ℝ => (WithLp.toLp 2 (fun j : Fin r => z ((j : ℕ) + 1)) :
        EuclideanSpace ℝ (Fin r)))
      (fun N : ℕ => Measure.pi fun _ : Fin N => μ)
      (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) := by
  have hι : Function.Injective (fun j : Fin r => (j : ℕ) + 1) := by
    intro a b h
    exact Fin.ext (by simpa using h)
  have hYm : Measurable (fun z : ℕ → ℝ => (WithLp.toLp 2 (fun j : Fin r => z ((j : ℕ) + 1)) :
      EuclideanSpace ℝ (Fin r))) := by
    fun_prop
  have hXm : ∀ N : ℕ, Measurable (fun x : Fin N → α => (WithLp.toLp 2 (fun j : Fin r =>
      (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l : Fin N, f ((j : ℕ) + 1) (x l)) :
      EuclideanSpace ℝ (Fin r))) := by
    intro N
    fun_prop
  refine TendstoInDistribution.of_tendsto_charFun (fun N => (hXm N).aemeasurable)
    hYm.aemeasurable (fun v => ?_)
  have hY : charFun ((Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)).map
      (fun z : ℕ → ℝ => (WithLp.toLp 2 (fun j : Fin r => z ((j : ℕ) + 1)) :
        EuclideanSpace ℝ (Fin r)))) v =
      Complex.exp (((-(∑ k : Fin r, v k ^ 2) / 2 : ℝ) : ℂ)) :=
    lip051_14_countable_gaussian_product_charFun (fun j : Fin r => (j : ℕ) + 1) hι v
  rw [hY]
  have hT := lip051_18_scalar_characteristic_functions_feature_sums μ e he0 f hfm hfe r hr v
  have hval : (-(1 / 2 : ℝ)) * ∑ j : Fin r, v j ^ 2 = -(∑ k : Fin r, v k ^ 2) / 2 := by ring
  rw [hval] at hT
  exact Tendsto.congr (fun N => (lip051_19_sample_charFun_LIP05119 μ f hfm N r v).symm) hT

end DGPS.Frontier.LIP051
