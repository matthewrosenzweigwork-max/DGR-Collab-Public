import DGPS.Frontier.LIP051.T07
import DGPS.Frontier.LIP051.T12

/-!
# LIP051.13: Fixed-rank diagonal correction

Task id `LIP051.13`, title "Fixed-rank diagonal correction" (node LIP051, "Joint Gaussian and
quadratic fluctuation limit", leaf formalization, verification V1, dispatch tier 4).

Let `μ` be a probability measure on the torus and `K` the centered kernel of a bounded continuous
`W` (LIP051.03). Let `e j` (`j ≥ 1`) be real functions in `L²(μ)` that are orthonormal for positive
indices, `T i j = ∬ K(x,y) e i(x) e j(y) dμ dμ`, `K_R(x,y) = ∑_{i,j=1}^R T i j e i(x) e j(y)` and
`F_R = K - K_R`. Put `δ_R(x) = F_R(x,x)` and, on the product space `μ^N` with coordinates `X_l`,
`D_{N,R} = (1/(2N)) ∑_{l=1}^N δ_R(X_l) - (1/2)(d_K - tr T_R)`, where `d_K = ∫ K(x,x) dμ` and
`tr T_R = ∑_{i=1}^R T i i`. For every fixed `R`, `D_{N,R}` is integrable for every `N`, and
`‖D_{N,R}‖_{L¹(μ^N)} → 0` as `N → ∞`. The rank `R` is fixed before the limit; no bound uniform in
`R` is asserted.

Proof route. `δ_R` is integrable with mean `d_K - tr T_R` by LIP051.07. Its measurable
`μ`-a.e. version `g` gives `D_{N,R} = (1/2)((1/N) ∑ g(X_l) - μ(g))` almost everywhere under `μ^N`,
and LIP051.12 (clause 2) applied to `g`, with the factor one half, gives the limit.

## Provides

* `DGPS.Frontier.LIP051.lip051_13_fixed_rank_diagonal_correction`: main statement; for every
  fixed `R`, the function `D_{N,R}` is `μ^N`-integrable for every `N`, and its `L¹(μ^N)` norm tends
  to `0` along `N → ∞`.
* `DGPS.Frontier.LIP051.ae_eval_eq_LIP05113`: helper; if `p = q` `μ`-almost everywhere, then for
  every `N`, almost every `x : Fin N → E` under `μ^N` satisfies `p (x l) = q (x l)` for all `l`.
* `DGPS.Frontier.LIP051.ae_diag_identity_LIP05113`: helper; the almost-everywhere identity
  `(1/(2N)) ∑ δ(x l) - (1/2) c = (1/2)((1/N) ∑ g(x l) - μ(g))` under `μ^N`, when `δ = g` a.e. and
  `μ(g) = c`.

## R5 notes

1. Data and hypotheses. The hypotheses are exactly those of LIP051.07 and are not strengthened:
   `μ` is a probability measure on `DGPS.Torus d`; `W` is continuous on the square (`hWc`) and
   bounded by `M` (`hb`); `e : ℕ → Torus d → ℝ` has `MemLp (e j) 2 μ` for `1 ≤ j` (`hL2`) and
   `∫ e i e j dμ = δ_ij` for positive `i, j` (`hon`). Symmetry of `W` is not assumed, since neither
   LIP051.07 nor this unit uses it. `R : ℕ` is a theorem argument, so the rank is fixed before
   the limit in `N`.
2. Kernel. `K` is `centeredKernelOf_LIP05103 μ W`, used pointwise on the diagonal as given. `d_K`
   is the Bochner integral `∫ x, K x x ∂μ` of this pointwise diagonal, and no almost-everywhere
   representative of `K` is taken.
3. Feature functions. `e j` is read as a pointwise function, not as an `L²` class. Since `MemLp`
   gives only almost-everywhere strong measurability, the diagonal `δ_R` is only almost-everywhere
   measurable. LIP051.12 requires `Measurable`, so a measurable `μ`-a.e. version `g` of `δ_R` is
   chosen inside the proof (the existence clause of `AEStronglyMeasurable`). The statement's
   function `D_{N,R}` is not replaced: it coincides with `(1/2)((1/N)∑ g(X_l) - μ(g))` on a
   `μ^N`-full set, because each coordinate has law `μ` (`measurePreserving_eval`), so the
   integrability and the `L¹` norm are unchanged.
4. Mean. "`d_K - tr T_R`" is `(∫ K x x dμ) - ∑_{i=1}^R T i i`, the same expression as in
   LIP051.07, whose fourth clause gives `∫ δ_R dμ` equal to it. Hence `μ(g) = d_K - tr T_R`.
5. Integrability. "`D_{N,R}` is L1" is read as `Integrable` on `Measure.pi` for every natural
   `N`, including `N = 0`, where the Lean convention `1/(2·0) = 0` makes the sum term vanish; the
   almost-everywhere identity holds uniformly in `N`, so no separate case is needed.
6. Norm. `‖D_{N,R}‖_1` is `∫ |D_{N,R}| dμ^N`. The limit is `Tendsto` along `Filter.atTop` on `ℕ`,
   so finitely many values of `N` do not matter. The identity is used for every `N`, so the limit
   statement is not weakened.
7. Uniformity. No bound uniform in `R` is stated or used. The only limit is in `N`.
8. Positive-mode convention (FD-002). The indices of this unit are `1, …, R` in the section `K_R`,
   in `tr T_R`, and in the orthonormality hypothesis `hon`, which quantifies only over positive
   indices. `e 0` is not used. No Gaussian object, no finite-coordinate block over `Finset ℕ`,
   and no binder for the joint limit occurs, so none of the FD-002 binder or mode-zero readings
   applies to this unit; the zero-mode refutation recorded in FD-002 does not touch this statement.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace DGPS.Frontier.LIP051

/-- Coordinatewise almost-everywhere equality under the product law: if `p = q` `μ`-almost
everywhere, then for every `N`, almost every sample `x : Fin N → E` under `μ^N` satisfies
`p (x l) = q (x l)` for all `l`. -/
lemma ae_eval_eq_LIP05113 {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    {p q : E → ℝ} (h : p =ᵐ[μ] q) (N : ℕ) :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin N => μ), ∀ l : Fin N, p (x l) = q (x l) := by
  rw [ae_all_iff]
  intro l
  exact (measurePreserving_eval (fun _ : Fin N => μ) l).quasiMeasurePreserving.ae h

/-- The almost-everywhere identity behind the diagonal correction: if `δ = g` `μ`-almost
everywhere and `μ(g) = c`, then under `μ^N` the centered empirical diagonal equals one half of the
centered empirical average of `g`, almost everywhere. -/
lemma ae_diag_identity_LIP05113 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {δ g : E → ℝ} (hae : δ =ᵐ[μ] g) (c : ℝ) (hc : ∫ y, g y ∂μ = c)
    (N : ℕ) :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin N => μ),
      (1 / (2 * (N : ℝ))) * (∑ l : Fin N, δ (x l)) - (1 / 2 : ℝ) * c
        = (1 / 2 : ℝ) * ((1 / (N : ℝ)) * (∑ l : Fin N, g (x l)) - ∫ y, g y ∂μ) := by
  filter_upwards [ae_eval_eq_LIP05113 μ hae N] with x hx
  have hs : ∑ l : Fin N, δ (x l) = ∑ l : Fin N, g (x l) :=
    Finset.sum_congr rfl fun l _ => hx l
  rw [hs, hc]
  ring

/-- **LIP051.13.** Fixed-rank diagonal correction. For the centered kernel `K` of a bounded
continuous `W` on the torus, a family `e` with `e j ∈ L²(μ)` and `∫ e i e j dμ = δ_ij` for positive
`i, j`, and a fixed rank `R`, the function
`D_{N,R}(x) = (1/(2N)) ∑_{l} (K - K_R)(x l, x l) - (1/2)(∫ K(x,x) dμ - ∑_{i=1}^R T i i)`
is integrable under `μ^N` for every `N`, and its `L¹(μ^N)` norm tends to `0` as `N → ∞`. -/
theorem lip051_13_fixed_rank_diagonal_correction {d : ℕ}
    (μ : Measure (DGPS.Torus d)) [IsProbabilityMeasure μ]
    (W : DGPS.Torus d → DGPS.Torus d → ℝ) {M : ℝ} (hWc : Continuous (Function.uncurry W))
    (hb : ∀ x y, |W x y| ≤ M)
    (e : ℕ → DGPS.Torus d → ℝ) (hL2 : ∀ j, 1 ≤ j → MemLp (e j) 2 μ)
    (hon : ∀ i j, 1 ≤ i → 1 ≤ j → ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0)
    (R : ℕ) :
    (∀ N : ℕ, Integrable (fun x : Fin N → DGPS.Torus d =>
        (1 / (2 * (N : ℝ))) * (∑ l : Fin N,
            (centeredKernelOf_LIP05103 μ W (x l) (x l)
              - kernelRankLIP05107 μ (centeredKernelOf_LIP05103 μ W) e R (x l) (x l)))
          - (1 / 2 : ℝ) * ((∫ x, centeredKernelOf_LIP05103 μ W x x ∂μ)
              - ∑ i ∈ Finset.Icc 1 R, tIJ_LIP05107 μ (centeredKernelOf_LIP05103 μ W) e i i))
        (Measure.pi fun _ : Fin N => μ)) ∧
    Tendsto (fun N : ℕ => ∫ x : Fin N → DGPS.Torus d,
        |(1 / (2 * (N : ℝ))) * (∑ l : Fin N,
            (centeredKernelOf_LIP05103 μ W (x l) (x l)
              - kernelRankLIP05107 μ (centeredKernelOf_LIP05103 μ W) e R (x l) (x l)))
          - (1 / 2 : ℝ) * ((∫ x, centeredKernelOf_LIP05103 μ W x x ∂μ)
              - ∑ i ∈ Finset.Icc 1 R, tIJ_LIP05107 μ (centeredKernelOf_LIP05103 μ W) e i i)|
        ∂(Measure.pi fun _ : Fin N => μ)) atTop (𝓝 0) := by
  obtain ⟨-, -, hδi, hδm⟩ := lip051_07_finite_diagonal_integral μ W hWc hb e hL2 hon R
  obtain ⟨g, hgm, hae⟩ : ∃ g : DGPS.Torus d → ℝ, Measurable g ∧
      (fun x => centeredKernelOf_LIP05103 μ W x x
        - kernelRankLIP05107 μ (centeredKernelOf_LIP05103 μ W) e R x x) =ᵐ[μ] g :=
    ⟨hδi.aestronglyMeasurable.mk _, hδi.aestronglyMeasurable.measurable_mk,
      hδi.aestronglyMeasurable.ae_eq_mk⟩
  have hgi : Integrable g μ := hδi.congr hae
  have hc : ∫ y, g y ∂μ = (∫ x, centeredKernelOf_LIP05103 μ W x x ∂μ)
      - ∑ i ∈ Finset.Icc 1 R, tIJ_LIP05107 μ (centeredKernelOf_LIP05103 μ W) e i i :=
    (integral_congr_ae hae).symm.trans hδm
  have hid := fun N : ℕ => ae_diag_identity_LIP05113 μ hae _ hc N
  refine ⟨fun N => ?_, ?_⟩
  · have hR : Integrable (fun x : Fin N → DGPS.Torus d =>
        (1 / 2 : ℝ) * ((1 / (N : ℝ)) * (∑ l : Fin N, g (x l)) - ∫ y, g y ∂μ))
        (Measure.pi fun _ : Fin N => μ) :=
      (((integrable_finsetSum _ fun l _ => marginal_integrable_LIP05111 μ l hgi).const_mul
        (1 / (N : ℝ))).sub (integrable_const _)).const_mul (1 / 2 : ℝ)
    exact hR.congr (by filter_upwards [hid N] with x hx; exact hx.symm)
  · have hT := ((lip051_12_l1_law_large_numbers_truncation μ g hgm hgi).2).const_mul (1 / 2 : ℝ)
    rw [mul_zero] at hT
    refine hT.congr fun N => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hid N] with x hx
    rw [hx, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]

end DGPS.Frontier.LIP051
