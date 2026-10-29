import DGPS.Frontier.LIP051.T46
import DGPS.Frontier.LIP051.T47
import DGPS.Frontier.LIP051.T48

/-!
# LIP051.18: Scalar characteristic functions of feature sums

Task id `LIP051.18`, title "Scalar characteristic functions of feature sums" (node LIP051,
"Joint Gaussian and quadratic fluctuation limit", size S, leaf formalization, verification V1).
Dependencies: LIP051.46 (file T46), LIP051.47 (file T47), LIP051.48 (file T48).
Source: `frontier_decomposition_20261024/nodes/LIP051.md`, the `LIP051.18` statement and proof.

## Provides

* `DGPS.Frontier.LIP051.lip051_18_scalar_characteristic_functions_feature_sums`: for a probability
  measure `μ`, a real Hilbert basis `e` of `L²(μ)` with `e 0 = 1`, measurable representatives `f j`
  of the classes `e j`, and every `r ≥ 1` and `v : Fin r → ℝ`, the characteristic functions
  `E_{μ^N} exp (i ∑_{j<r} v_j Z_{N,j})` of `Z_{N,j} = N^{-1/2} ∑_{l<N} f_{j+1}(X_l)` converge, as
  `N → ∞`, to `exp (-(1/2) ∑_j v_j²)`.

## R5 notes

1. Frozen statement. The statement is the displayed limit of the specification, with the
   campaign identifications (`S.mu`, `Torus d`, `Hw d S.w`, `S.e`) left to LIP051.01, as in
   LIP051.46-48. The hypotheses are exactly those of LIP051.48: `μ` a probability measure, `e` a
   real Hilbert basis of `L²(μ)`, `he0 : e 0 = Lp.const 2 μ 1`, measurable `f j` with
   `f j =ᵐ[μ] e j`. No moment, boundedness or continuity hypothesis is added, and none is needed.
   The specification says that no boundedness of the `e_j` is assumed; the proof uses only the
   `L²` clause of LIP051.46 and the pinned unit-variance central limit theorem.
2. Range of `r`. The specification says "every integer `r ≥ 1`". The binder `_hr : 1 ≤ r` is
   kept, as written. The proof does not use it: the limit is also true for `r = 0`, where both
   sides equal one. Dropping the binder would strengthen the statement, which is not done here.
3. Positive modes (FD-002 reading). The coordinate `j : Fin r` is paired with the basis index
   `(j : ℕ) + 1`, so the finite block is `Z_{N,1}, …, Z_{N,r}` in the specification's
   indexing. Index zero, the constant mode `e 0 = 1`, does not occur in any `Z_{N,j}`. Reason:
   `e 0 = 1` a.e. gives `Z_{N,0} = √N` identically, which cannot converge to a centred Gaussian.
   No reading with index zero is adopted. The hypothesis `he0` enters only through LIP051.46,
   where it gives the positive-mode mean zero. This is the repair proposed in FD-002 (indexing
   through `i + 1`); the defect is not closed by this unit.
4. Vector binder. The vector `v ∈ ℝ^r` is realised as `Fin r → ℝ`. The exponent `i ∑_j v_j Z_{N,j}`
   is written as `Complex.I * ∑ j, (v j : ℂ) * (Z_{N,j} : ℂ)`, with the normalisation written
   as the real power `(N : ℝ) ^ (-(1/2 : ℝ))`. The limit is `Complex.exp` of the real number
   `-(1/2) * ∑_j v_j²` cast to `ℂ`. The value at `N = 0` is immaterial to the limit.
5. Representatives. `Z_{N,j}` is built from the measurable representative `f (j+1)`, not the
   class `e (j+1)`. The specification's conclusions concern laws, so different representatives
   give the same limit; the statement is proved for the representatives given, and no
   representative choice is made inside the proof.
6. Sample space and law. The sample space is `Fin N → α`, `Q_N = Measure.pi (fun _ => μ)`, and
   the coordinates are `x l`. Expectations are complex Bochner integrals with respect to this
   product measure. The reference law `Q_N` is the only law used. The tilted particle law, the
   kernel `K`, the statistic `U_N`, the Wick object and the diagonal convention do not occur in
   this unit.
7. Zero variance. The specification treats `∑ v_j² = 0` separately. That case is handled in
   LIP051.48, through `Y_v =ᵐ[μ] 0` from LIP051.46, which makes both sides equal one.
8. Proof route. The conclusion of LIP051.48 is the displayed limit for `r` in the range given;
   the present unit is a direct specialisation with the binder `1 ≤ r` carried along. No helper
   declaration is needed, so none carries the `_LIP05118` suffix.
-/

open MeasureTheory Filter Topology

namespace DGPS.Frontier.LIP051

/-- **LIP051.18.** For a probability measure `μ`, a real Hilbert basis `e` of `L²(μ)` with
`e 0 = 1`, measurable representatives `f j` of the classes `e j`, every `r ≥ 1` and every
`v : Fin r → ℝ`, the characteristic functions of `∑_{j<r} v_j Z_{N,j}` with
`Z_{N,j} = N^{-1/2} ∑_{l<N} f_{j+1}(X_l)` under the product law `μ^N` on `Fin N → α` converge
to `exp (-(1/2) ∑_j v_j²)`. The indexing of the positive modes is that of LIP051.46. -/
theorem lip051_18_scalar_characteristic_functions_feature_sums
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (he0 : e 0 = Lp.const 2 μ (1 : ℝ))
    (f : ℕ → α → ℝ) (hfm : ∀ j, Measurable (f j)) (hfe : ∀ j, f j =ᵐ[μ] (e j : α → ℝ))
    (r : ℕ) (_hr : 1 ≤ r) (v : Fin r → ℝ) :
    Tendsto (fun N : ℕ => ∫ x : Fin N → α,
        Complex.exp (Complex.I * ∑ j : Fin r, (v j : ℂ) *
          (((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l : Fin N, f ((j : ℕ) + 1) (x l) : ℝ) : ℂ))
        ∂(Measure.pi fun _ : Fin N => μ))
      atTop (𝓝 (Complex.exp (((-(1 / 2 : ℝ)) * ∑ j : Fin r, v j ^ 2 : ℝ) : ℂ))) :=
  lip051_48_remove_unit_variance_normalization_scalar_limit μ e he0 f hfm hfe r v

end DGPS.Frontier.LIP051
