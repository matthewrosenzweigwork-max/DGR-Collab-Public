import DGPS.Lipschitz.GaussianKernelTilt

/-!
## Bindings

Paths are relative to `Campaign/`; line numbers refer to base commit `a2af2f91`.
`GKT` abbreviates `DGPS/Lipschitz/GaussianKernelTilt.lean`.

| Source object or notion | Actual declaration (full name, file:line) | Type / binders | Discrepancy with the specification |
|---|---|---|---|
| target theorem | `DGPS.Lipschitz.joint_gaussian_and_quadratic_fluctuation_limit`: NOT PRESENT in any `.lean` file of the pin (it occurs only in planning documents). Closest header: `DGPS.Lipschitz.finite_rank_covariance_positivity_and_wick_normalization`, `GKT:3162` | `{d : ℕ} (S : Spec d) (A : Aux S) (D : KData d) (J : InteractionData d) (hD : ∀ x y, D.K x y = DGPS.centeredKernel J (specProbability_LIP016 S) x y) {σ : ℝ} (hσ : 0 < σ) (hH : ...)` | The target does not exist, so its binders cannot be read off. The binders `S A D J hD` are those of the LIP016 header. Its `{σ} hσ hH` (Hessian coercivity) are not used by the frozen statement and are not assumed here. |
| torus `𝕋^d` | `DGPS.Torus` (abbrev of `SharpLSI.Torus d`), `DGPS/Foundations/Torus.lean:32` | `Torus (d : ℕ)` | none |
| `Spec` data `S` | `DGPS.Lipschitz.KernelApproximation.Spec`, `DGPS/Lipschitz/KernelParseval.lean:22` | structure with `w c C meas pos bound prob e lam lam_nonneg v vc ve form` | `Spec` alone does not contain `e 0 = 1`. |
| LIP009 witness carrier | `DGPS.Lipschitz.KernelApproximation.Aux`, `DGPS/Lipschitz/KernelApproximation.lean:39` (field `v0` at `:52`), built by `exists_spec_aux` (`:1618`) from `DGPS.Lipschitz.WeightedSpectrum.weighted_eigenbasis_and_growth` (`DGPS/Lipschitz/WeightedSpectrum.lean:768`) | `structure Aux (S : Spec d)`; `v0 : ∀ x, S.v 0 x = 1` | The specification lists no `Aux`; the constant vector needs `A : Aux S` (R5 note 2). |
| (a) `mu` | `DGPS.Lipschitz.KernelApproximation.Spec.mu`, `KernelParseval.lean:40` (an abbrev for `wMeasure d S.w`); `DGPS.Analysis.CompactResolvent.wMeasure`, `DGPS/Analysis/CompactResolvent.lean:1383`; `Spec.real_univ`, `KernelApproximation.lean:21`; `DGPS.Lipschitz.specProbability_LIP016`, `GKT:695` | `S.mu : Measure (Torus d)`; `wMeasure (d : ℕ) (w : Torus d → ℝ) : Measure (Torus d)`; `specProbability_LIP016 S : ProbabilityMeasure (Torus d)` | none: `S.mu = wMeasure d S.w` holds by `rfl`; it is a probability measure. |
| (b) `Hw d w` | `DGPS.Analysis.CompactResolvent.Hw`, `CompactResolvent.lean:1478`; inner product: `DGPS.Lipschitz.inner_Hw_eq_integral`, `DGPS/Lipschitz/WeightedMildSemigroup.lean:44` | `Hw d w = Lp ℝ 2 (wMeasure d w)` (real Hilbert space) | none: with `w = S.w` it is `Lp ℝ 2 S.mu` by `rfl`. |
| (c) basis `e` and representatives | `Spec.e`, `Spec.v`, `Spec.vc`, `Spec.ve` (`KernelParseval.lean:22`); `DGPS.Lipschitz.spectralBasis_LIP016`, `GKT:768` | `S.e : HilbertBasis ℕ ℝ (Hw d S.w)`; `S.v j : Torus d → ℝ` continuous with `S.v j =ᵐ[haar d] S.e j` | The specification's "measurable representatives" are the continuous `S.v j`. `ve` is stated for Haar measure and is transported to `S.mu` by absolute continuity (`Spec.ae_mu`, `KernelParseval.lean:51`). |
| (c) constant vector | `Aux.v0` (`KernelApproximation.lean:52`); `DGPS.Lipschitz.spectralBasis_zero_LIP016`, `GKT:2112`; first conjunct of `weighted_eigenbasis_and_growth` | `∀ x, S.v 0 x = 1`; `S.e 0 = Lp.const 2 S.mu 1` | holds everywhere (not only almost everywhere) for the representative `S.v 0`. |
| (d) original kernel `D.K` | `DGPS.Lipschitz.KernelApproximation.KData`, `KernelParseval.lean:123` | `K : Torus d → Torus d → ℝ`, `Kc : Continuous (Function.uncurry K)`, plus bounded weak slice gradients `G1 G2 g1 g2 B` | `KData` carries gradient data absent from the source (R5 note 5). `D.K` is not assumed symmetric or centered; both are derived from `hD`. |
| (d) centered kernel of the source | `DGPS.centeredKernel`, `DGPS/Equilibrium/Hessian.lean:33`; `DGPS.interactionConvolution` (`:25`), `DGPS.meanInteraction` (`:30`); `DGPS.InteractionData`, `DGPS/Model/Data.lean:22` | `centeredKernel (A : InteractionData d) (μ : ProbabilityMeasure (Torus d)) (x y : Torus d) : ℝ` | `InteractionData` has fields `V W V_continuous W_continuous W_symm W_diag`; the source has only a bounded continuous symmetric `W`, and `W_diag : W x x = 0` is extra. |
| (d) transport `D.K` to the source kernel | hypothesis `hD` of the LIP016 header; `original_kernel_symmetric_LIP016` (`GKT:2217`), `original_kernel_centered_LIP016` (`GKT:2224`), `kernelInteraction_LIP016` (`GKT:700`) | `hD : ∀ x y, D.K x y = centeredKernel J (specProbability_LIP016 S) x y` | none: a pointwise identity, so the original diagonal `D.K x x` is preserved (no almost-everywhere variant is needed). |
| (e) `Q_N` | no campaign declaration; `DGPS.Frontier.LIP051.refLaw_LIP05101` (this file) | `Measure.pi (fun _ : Fin N => S.mu)` on `Fin N → Torus d` | new definition |
| (e) `Z_{N,j}` | `DGPS.Frontier.LIP051.Z_LIP05101` (via `ZOf_LIP05101`) | `(√N)⁻¹ * ∑ l : Fin N, S.v j (x l)` | new definition; positive indices only in the blocks (R5 note 7) |
| (e) `U_N` | `DGPS.Frontier.LIP051.U_LIP05101` | `(2 * N)⁻¹ * ∑ l, ∑ k, K (x l) (x k)`, all `N²` terms | new definition; the diagonal terms `k = l` use the original `K` |
| (e) `T_ij` | `DGPS.Lipschitz.KernelApproximation.TK`, `KernelParseval.lean:141` (`TK_eq` `:217`, `hasSum_prod_sq` `:317`, `TK_zero_left` `:350`, `TK_zero_right` `:357`; `TK_symmetric_LIP016` `GKT:571`) | `TK S K i j = ∫ p, K p.1 p.2 * (S.v i p.1 * S.v j p.2) ∂(S.mu.prod S.mu)` | none; defined for all `i j`, the positive indices are used |
| (e) `d_K` | `DGPS.Frontier.LIP051.dK_LIP05101` | `∫ x, K x x ∂S.mu` | new definition; equals `-meanInteraction J (specProbability_LIP016 S)` for `D.K` |
| (e) `γ₀` | `DGPS.Lipschitz.gaussianCountable_LIP016`, `GKT:1260` | `Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)` on `ℕ → ℝ` | none; coordinate `0` is unused |
| (e) Wick sections | `finiteWickOn_LIP016` (`GKT:1276`), `finiteWickLp_LIP016` (`:1355`), `finiteWickLp_padding_LIP016` (`:1367`), `kernelWickLp_LIP016` (`:1405`), `kernelWick_completion_LIP016` (`:1441`) | `finiteWickLp_LIP016 (B : ℕ → ℕ → ℝ) (s : Finset ℕ) : Lp ℝ 2 gaussianCountable_LIP016` | LIP016 sums over `Finset.range (m + 1)`, which contains index `0`, and carries a smoothing parameter `t`; the coefficients of index `0` vanish for a centered `K`. |
| (e) `Q_T` | no campaign declaration; `DGPS.Frontier.LIP051.QT_LIP05101` (this file) | `limUnder atTop (wickSection_LIP05101 S K) : Lp ℝ 2 gaussianCountable_LIP016`, with `wickSection_LIP05101 S K R = finiteWickLp_LIP016 (TK S K) (Finset.Icc 1 R)` | new definition: the `L²(γ₀)` limit of the unsmoothed positive rectangular Wick sections. It is an `Lp` class (R5 note 8). |
| finite vector of coordinates | Mathlib `EuclideanSpace ℝ (Fin m)` | `blockZ_LIP05101`, `blockCoord_LIP05101`: entry `i` is coordinate `i + 1` | none (the type name exists at the pin) |
| frozen statement | `DGPS.Frontier.LIP051.JointFluctuationLimit_LIP05101` (a `Prop`, neither assumed nor proved here) | `∀ m, TendstoInDistribution (fun N x => (blockZ S m N x, U K N x)) atTop (fun z => (blockCoord m z, (QT z + dK) / 2)) (fun N => refLaw S N) gaussianCountable_LIP016` | transcription on the blocks `1..m`; see R5 notes 7 and 9 |

## LIP051.01 — Bind the campaign data to the source data

Gate unit of node LIP051 ("Joint Gaussian and quadratic fluctuation limit"). Wave 0, interface
resolution. Result: `statement_issue` (the target declaration is absent and a mode-zero
quantifier is refutable; everything provable about the actual declarations is proved below).

Throughout, `S : Spec d`, `A : Aux S`, `D : KData d`, `J : InteractionData d` and
`hD : ∀ x y, D.K x y = centeredKernel J (specProbability_LIP016 S) x y`.

## Provides

Public theorems (namespace `DGPS.Frontier.LIP051`):

* `DGPS.Frontier.LIP051.gate_lip051_01_bind_campaign_data_source_data`: the conjunction of all
  the bindings (a) to (e) for the actual binders `(S A D J hD)`, together with the Wick-section
  limit, the Gaussian marginals of `γ₀`, the transport of the frozen statement from `D.K` to the
  centered kernel, and the mode-zero obstruction.
* `..._mu`: `S.mu = wMeasure d S.w`, it is a probability measure, and `specProbability_LIP016 S`
  has underlying measure `S.mu`.
* `..._hilbert`: `Hw d S.w = Lp ℝ 2 S.mu`, its inner product and squared norm are the `S.mu`
  integrals, and the LIP016 basis `spectralBasis_LIP016 S` is `S.e`.
* `..._basis`: `S.v j` are continuous representatives of `S.e j` (`S.mu`-a.e.), `S.v 0 = 1`
  everywhere, `S.e 0 = Lp.const 2 S.mu 1`, the LIP009 conjunct, orthonormality of `S.v`, and
  `∫ S.v j dS.mu = 0` for `j ≥ 1`.
* `..._kernel`: the explicit formula for `D.K` in terms of `J.W`, symmetry, centering, the exact
  diagonal `D.K x x`, and invariance of `U_N`, `d_K`, `T` under the pointwise identity `hD`.
* `..._law`: `Q_N` is the product of `S.mu`, is a probability measure, and each coordinate map is
  measure preserving onto `S.mu`.
* `..._Z`: `Z_{N,j}` unfolds to the normalized sum of `S.v j`; the `e_j`-representative gives the
  same variable `Q_N`-a.e.; and `Z_{N,0} = √N` for `N ≥ 1`.
* `..._T`: `T_ij` is the iterated integral and the `L²(S.mu)` matrix element of the operator of
  `kernelOp J (specProbability_LIP016 S)` between basis vectors; it is symmetric, vanishes when an
  index is `0`, and its squares sum to the squared `L²(S.mu ⊗ S.mu)` norm of `D.K`.
* `..._dK`: the diagonal of `D.K` is continuous and integrable, and `d_K = ∫ D.K x x dS.mu =
  -meanInteraction J (specProbability_LIP016 S)`.
* `..._QT_unique`: every LIP016-style smoothed Wick limit `q` (with `t R → 0`, `t R ≥ 0`,
  strictly monotone `m`) equals `QT_LIP05101 S D.K`.
* `..._zero_mode`: `Z_{N,0}` does not converge in distribution under `Q_N` to the coordinate
  `z 0` of `γ₀`, because `Z_{N,0} = √N`.

Definitions and helpers (suffix `_LIP05101`):

* `refLaw_LIP05101` (`Q_N`), `ZOf_LIP05101` and `Z_LIP05101` (`Z_{N,j}`), `U_LIP05101` (`U_N`),
  `dK_LIP05101` (`d_K`), `wickSection_LIP05101` (positive rectangular Wick sections),
  `QT_LIP05101` (`Q_T`), `blockZ_LIP05101` and `blockCoord_LIP05101` (finite coordinate
  vectors), `JointFluctuationLimit_LIP05101` (the frozen statement on positive blocks).
* `instIsProbabilityMeasureMu_LIP05101`, `instIsProbabilityMeasureRefLaw_LIP05101`: probability
  instances for `S.mu` and `Q_N`.
* `ZOf_ae_congr_LIP05101`, `finiteWickLp_congr_LIP05101`, `wickSection_ae_LIP05101` (the section
  is a.e. the displayed Wick polynomial), `wickSection_eq_kernelWick_LIP05101` (it equals the
  LIP016 section with `t = 0`), `wickSection_tendsto_LIP05101` (convergence to `Q_T`),
  `kernelWick_dist_le_LIP05101`, `blockZ_apply_LIP05101`, `blockCoord_apply_LIP05101`,
  `gaussianCountable_marginal_LIP05101`, `jointFluctuationLimit_transport_LIP05101`.

## R5 notes

1. Absent target. `joint_gaussian_and_quadratic_fluctuation_limit` is not declared anywhere in
   the pin, so its binders are taken from the LIP016 header (`S A D J hD`). No hypothesis is
   added: `{σ} hσ hH` of that header play no role in the frozen statement and are not assumed.
2. `Aux S` is needed. `Spec` does not contain `e 0 = 1`. The campaign carries the LIP009 witness
   as `Aux.v0 : ∀ x, S.v 0 x = 1` (obtained in `exists_spec_aux` from the first conjunct of
   `weighted_eigenbasis_and_growth`). Statements about the constant vector, `Z_{N,0}`, the
   vanishing of `T_0j`, and `Q_T` use `A : Aux S`. Statements about `mu`, `Hw`, the kernel
   formulas, `Q_N` and `d_K` do not.
3. `mu` and `Hw`. Both identifications are definitional (`Spec.mu` is an abbrev for `wMeasure d S.w`
   and `Hw d w` for `Lp ℝ 2 (wMeasure d w)`). The global instance
   `instIsProbabilityMeasureMu_LIP05101` is introduced so that `Measure.pi` and Gaussian-style
   lemmas see `S.mu` as a probability measure; it is derived from `Spec.real_univ`.
4. Representatives. `Z_{N,j}` is built from the continuous representatives `S.v j` of `Spec`,
   not from an arbitrary chosen representative of the class `S.e j`. `_Z` shows that the
   representative `⇑(S.e j)` gives the same variable `Q_N`-almost surely, so every distributional
   statement is representative independent. The reading "e_0 = 1 almost everywhere" is
   strengthened to `S.v 0 x = 1` for all `x`.
5. Kernel. `hD` is a pointwise identity, so the specified original diagonal is preserved and the
   product-a.e. and diagonal-a.e. variants are not needed. The campaign structures are narrower
   than the source ("bounded continuous symmetric `W`"): `KData` also records bounded weak slice
   gradients, and `InteractionData` records `W_diag : W x x = 0`. The present file only uses `hD`,
   `D.Kc`, and the LIP016 lemmas `original_kernel_symmetric_LIP016` and
   `original_kernel_centered_LIP016` (symmetry and centering of `D.K` are derived, not assumed).
   Boundedness of `W` is not a field; continuity on the compact torus gives it.
6. `Q_N`, `U_N`, `d_K`, `Z`. These are new definitions (the campaign has none). They are total
   functions of `N`; at `N = 0` they take the Lean junk values (`0⁻¹ = 0`), which do not affect
   limits. `U_N` sums all `N²` pairs, including the diagonal pairs with the original `K`.
7. Positive modes. `blockZ_LIP05101 S m N` collects `Z_{N,1}, ..., Z_{N,m}` as an element of
   `EuclideanSpace ℝ (Fin m)` (entry `i` is index `i + 1`), and `blockCoord_LIP05101 m z` the
   coordinates `z 1, ..., z m`. The case `m = 0` is allowed. Every finite set of positive indices
   is reached from some block `1..m` by a coordinate projection (continuous mapping theorem);
   this reduction is not formalized here. LIP016 quantifies over `s : Finset ℕ`
   (`finiteCoordinateProjection_LIP016`, `GKT:3073`), which includes index `0`. The one-coordinate
   block `s = {0}` (without `U_N`) is refuted by `_zero_mode`. A larger joint block containing
   index `0` has `Z_{N,0}` as a continuous image, so it fails as well (this last step is the
   continuous mapping theorem and is not formalized).
8. `Q_T`. It is defined as `limUnder` of the unsmoothed rectangular sections over
   `Finset.Icc 1 R`, which is the construction named in the node preamble (no smoothing, no
   trace of an operator). The limit exists for `D.K` (`wickSection_tendsto_LIP05101`, proved
   through LIP016's completion theorem with `t = 0`); for a kernel without a limit the
   definition returns a junk element, so always use it together with `Tendsto`. `_QT_unique` ties
   it to every smoothed LIP016 limit. `Q_T` is an element of `Lp`; as a function on `ℕ → ℝ` the
   frozen statement uses the representative chosen by the coercion. Two representatives agree
   `γ₀`-almost everywhere and give the same law, which is not formalized here.
9. The frozen statement. `JointFluctuationLimit_LIP05101` is a definition only. It is not
   assumed in any theorem and not proved: its proof is the content of the later units of LIP051.
   Its target law is the image of `γ₀` under `z ↦ (blockCoord m z, (Q_T z + d_K) / 2)`, whose
   block coordinates have standard Gaussian marginals (`gaussianCountable_marginal_LIP05101`).
   Convergence is along `N → ∞` with sample spaces `Fin N → Torus d` and laws `Q_N`; the tilted
   law belongs to LIP052 and does not appear.
10. Outcome `statement_issue`, with the smallest repair: (i) declare
    `joint_gaussian_and_quadratic_fluctuation_limit` with binders `(S : Spec d) (A : Aux S)
    (D : KData d) (J : InteractionData d) (hD)` and the conclusion
    `JointFluctuationLimit_LIP05101 S D.K` (or its unfolding), quantifying over blocks
    `Fin m` with index `i + 1`, or over `s : Finset ℕ` with `∀ j ∈ s, 1 ≤ j`; (ii) never
    quantify over index `0`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace
open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent DGPS.Lipschitz
  DGPS.Lipschitz.KernelApproximation

namespace DGPS.Frontier.LIP051

variable {d : ℕ}

instance instIsProbabilityMeasureMu_LIP05101 (S : Spec d) : IsProbabilityMeasure S.mu :=
  isProbabilityMeasure_iff_real.mpr S.real_univ

noncomputable def refLaw_LIP05101 (S : Spec d) (N : ℕ) : Measure (Fin N → Torus d) :=
  Measure.pi fun _ => S.mu

instance instIsProbabilityMeasureRefLaw_LIP05101 (S : Spec d) (N : ℕ) :
    IsProbabilityMeasure (refLaw_LIP05101 S N) := by
  unfold refLaw_LIP05101; infer_instance

noncomputable def ZOf_LIP05101 (f : Torus d → ℝ) (N : ℕ) (x : Fin N → Torus d) : ℝ :=
  (Real.sqrt (N : ℝ))⁻¹ * ∑ l : Fin N, f (x l)

noncomputable def Z_LIP05101 (S : Spec d) (N j : ℕ) (x : Fin N → Torus d) : ℝ :=
  ZOf_LIP05101 (S.v j) N x

noncomputable def U_LIP05101 (K : Torus d → Torus d → ℝ) (N : ℕ) (x : Fin N → Torus d) : ℝ :=
  (2 * (N : ℝ))⁻¹ * ∑ l : Fin N, ∑ k : Fin N, K (x l) (x k)

noncomputable def dK_LIP05101 (S : Spec d) (K : Torus d → Torus d → ℝ) : ℝ :=
  ∫ x, K x x ∂S.mu

noncomputable def wickSection_LIP05101 (S : Spec d) (K : Torus d → Torus d → ℝ) (R : ℕ) :
    Lp ℝ 2 gaussianCountable_LIP016 :=
  finiteWickLp_LIP016 (fun i j => TK S K i j) (Finset.Icc 1 R)

noncomputable def QT_LIP05101 (S : Spec d) (K : Torus d → Torus d → ℝ) :
    Lp ℝ 2 gaussianCountable_LIP016 :=
  limUnder atTop (wickSection_LIP05101 S K)

noncomputable def blockZ_LIP05101 (S : Spec d) (m N : ℕ) (x : Fin N → Torus d) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i : Fin m => Z_LIP05101 S N (i.val + 1) x

noncomputable def blockCoord_LIP05101 (m : ℕ) (z : ℕ → ℝ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i : Fin m => z (i.val + 1)

def JointFluctuationLimit_LIP05101 (S : Spec d) (K : Torus d → Torus d → ℝ) : Prop :=
  ∀ m : ℕ, TendstoInDistribution
    (fun (N : ℕ) (x : Fin N → Torus d) => (blockZ_LIP05101 S m N x, U_LIP05101 K N x))
    atTop
    (fun z : ℕ → ℝ => (blockCoord_LIP05101 m z, ((QT_LIP05101 S K : (ℕ → ℝ) → ℝ) z + dK_LIP05101 S K) / 2))
    (fun N => refLaw_LIP05101 S N) gaussianCountable_LIP016


/-! ### (a) -/

theorem gate_lip051_01_bind_campaign_data_source_data_mu (S : Spec d) :
    S.mu = wMeasure d S.w ∧ IsProbabilityMeasure S.mu ∧ S.mu Set.univ = 1 ∧
      ((specProbability_LIP016 S : ProbabilityMeasure (Torus d)) : Measure (Torus d)) = S.mu :=
  ⟨rfl, inferInstance, measure_univ, rfl⟩

/-! ### (b) -/

theorem gate_lip051_01_bind_campaign_data_source_data_hilbert (S : Spec d) :
    (Hw d S.w = Lp ℝ 2 S.mu) ∧
    (Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d)) = Hw d S.w) ∧
    (∀ f g : Hw d S.w, ⟪f, g⟫_ℝ = ∫ x, f x * g x ∂S.mu) ∧
    (∀ f : Hw d S.w, ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂S.mu) ∧
    spectralBasis_LIP016 S = S.e := by
  refine ⟨rfl, rfl, fun f g => inner_Hw_eq_integral f g, fun f => ?_, rfl⟩
  rw [← real_inner_self_eq_norm_sq, inner_Hw_eq_integral]
  exact integral_congr_ae (Eventually.of_forall fun x => (sq _).symm)

/-! ### (c) -/

theorem gate_lip051_01_bind_campaign_data_source_data_basis (S : Spec d) (A : Aux S) :
    (∀ j, Continuous (S.v j)) ∧
    (∀ j, S.v j =ᵐ[S.mu] ((S.e j : Hw d S.w) : Torus d → ℝ)) ∧
    (∀ x, S.v 0 x = 1) ∧
    (((S.e 0 : Hw d S.w) : Torus d → ℝ) =ᵐ[wMeasure d S.w] fun _ => (1 : ℝ)) ∧
    (S.e 0 = Lp.const 2 S.mu (1 : ℝ)) ∧
    (∀ i j, ∫ x, S.v i x * S.v j x ∂S.mu = if i = j then 1 else 0) ∧
    (∀ j, 1 ≤ j → ∫ x, S.v j x ∂S.mu = 0) := by
  refine ⟨S.vc, fun j => (S.ae_mu (S.ve j)), A.v0, ?_, ?_, S.orth, ?_⟩
  · filter_upwards [S.ae_mu (S.ve 0)] with x hx
    rw [← hx]; exact A.v0 x
  · exact spectralBasis_zero_LIP016 S A
  · intro j hj
    have h := S.orth j 0
    simp only [A.v0, mul_one, Nat.pos_iff_ne_zero.mp hj, ite_false] at h
    exact h


/-! ### (d) -/

theorem gate_lip051_01_bind_campaign_data_source_data_kernel (S : Spec d) (D : KData d)
    (J : InteractionData d)
    (hD : ∀ x y, D.K x y = centeredKernel J (specProbability_LIP016 S) x y) :
    (∀ x y, D.K x y = J.W x y - ∫ u, J.W x u ∂S.mu - ∫ u, J.W u y ∂S.mu +
      ∫ p, J.W p.1 p.2 ∂(S.mu.prod S.mu)) ∧
    (∀ x y, D.K x y = D.K y x) ∧
    (∀ y, ∫ x, D.K x y ∂S.mu = 0) ∧
    (∀ x, D.K x x = -2 * ∫ u, J.W x u ∂S.mu + ∫ p, J.W p.1 p.2 ∂(S.mu.prod S.mu)) ∧
    (∀ N (x : Fin N → Torus d), U_LIP05101 D.K N x =
      U_LIP05101 (centeredKernel J (specProbability_LIP016 S)) N x) ∧
    dK_LIP05101 S D.K = dK_LIP05101 S (centeredKernel J (specProbability_LIP016 S)) ∧
    (∀ i j, TK S D.K i j = TK S (centeredKernel J (specProbability_LIP016 S)) i j) := by
  have hfun : D.K = centeredKernel J (specProbability_LIP016 S) := by
    funext x y; exact hD x y
  refine ⟨fun x y => ?_, original_kernel_symmetric_LIP016 S D J hD,
    original_kernel_centered_LIP016 S D J hD, fun x => ?_, fun N x => by rw [hfun],
    by rw [hfun], fun i j => by rw [hfun]⟩
  · rw [hD x y]
    unfold centeredKernel interactionConvolution meanInteraction
    simp_rw [J.W_symm _ y]
    rfl
  · rw [hD x x]
    unfold centeredKernel interactionConvolution meanInteraction
    rw [J.W_diag x]
    change 0 - ∫ u, J.W x u ∂S.mu - ∫ u, J.W x u ∂S.mu + ∫ p, J.W p.1 p.2 ∂(S.mu.prod S.mu) = _
    ring


/-! ### (e) -/

theorem gate_lip051_01_bind_campaign_data_source_data_law (S : Spec d) (N : ℕ) :
    refLaw_LIP05101 S N = Measure.pi (fun _ : Fin N => S.mu) ∧
    IsProbabilityMeasure (refLaw_LIP05101 S N) ∧
    (∀ l : Fin N, MeasurePreserving (fun x : Fin N → Torus d => x l)
      (refLaw_LIP05101 S N) S.mu) :=
  ⟨rfl, inferInstance, fun l => measurePreserving_eval (fun _ : Fin N => S.mu) l⟩

theorem ZOf_ae_congr_LIP05101 (S : Spec d) {f g : Torus d → ℝ} (h : f =ᵐ[S.mu] g) (N : ℕ) :
    ZOf_LIP05101 f N =ᵐ[refLaw_LIP05101 S N] ZOf_LIP05101 g N := by
  have hl : ∀ l : Fin N, (fun x : Fin N → Torus d => f (x l)) =ᵐ[refLaw_LIP05101 S N]
      fun x => g (x l) := fun l =>
    (measurePreserving_eval (fun _ : Fin N => S.mu) l).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [ae_all_iff.mpr hl] with x hx
  simp only [ZOf_LIP05101]
  congr 1
  exact Finset.sum_congr rfl fun l _ => hx l

theorem gate_lip051_01_bind_campaign_data_source_data_Z (S : Spec d) (A : Aux S) :
    (∀ N j (x : Fin N → Torus d),
      Z_LIP05101 S N j x = (Real.sqrt (N : ℝ))⁻¹ * ∑ l : Fin N, S.v j (x l)) ∧
    (∀ N j, ZOf_LIP05101 (fun x => ((S.e j : Hw d S.w) : Torus d → ℝ) x) N
      =ᵐ[refLaw_LIP05101 S N] Z_LIP05101 S N j) ∧
    (∀ N, 1 ≤ N → ∀ x : Fin N → Torus d, Z_LIP05101 S N 0 x = Real.sqrt (N : ℝ)) := by
  refine ⟨fun _ _ _ => rfl, fun N j => ?_, fun N hN x => ?_⟩
  · exact ZOf_ae_congr_LIP05101 S (Filter.EventuallyEq.symm (S.ae_mu (S.ve j))) N
  · have hpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
    have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    simp only [Z_LIP05101, ZOf_LIP05101, A.v0, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp
    exact (Real.sq_sqrt hpos.le).symm

/-! ### (e) the coefficients `T_ij` and `d_K` -/

theorem gate_lip051_01_bind_campaign_data_source_data_T (S : Spec d) (A : Aux S) (D : KData d)
    (J : InteractionData d)
    (hD : ∀ x y, D.K x y = centeredKernel J (specProbability_LIP016 S) x y) :
    (∀ i j, TK S D.K i j = ∫ x, ∫ y, D.K x y * (S.v i x * S.v j y) ∂S.mu ∂S.mu) ∧
    (∀ i j, TK S D.K i j = ⟪spectralBasis_LIP016 S i,
      kernelOp J (specProbability_LIP016 S) (spectralBasis_LIP016 S j)⟫_ℝ) ∧
    (∀ i j, TK S D.K i j = TK S D.K j i) ∧
    (∀ j, TK S D.K 0 j = 0) ∧ (∀ i, TK S D.K i 0 = 0) ∧
    HasSum (fun p : ℕ × ℕ => TK S D.K p.1 p.2 ^ 2) (∫ p, D.K p.1 p.2 ^ 2 ∂S.mu.prod S.mu) := by
  have hK := original_kernel_symmetric_LIP016 S D J hD
  have hc := original_kernel_centered_LIP016 S D J hD
  refine ⟨fun i j => ?_, fun i j => ?_, TK_symmetric_LIP016 S D hK, TK_zero_left S D A.v0 hc,
    TK_zero_right S D A.v0 hc hK, hasSum_prod_sq S D⟩
  · have hint : Integrable
        (fun p : Torus d × Torus d => D.K p.1 p.2 * (S.v i p.1 * S.v j p.2)) (S.mu.prod S.mu) :=
      (D.Kc.mul (((S.vc i).comp continuous_fst).mul ((S.vc j).comp continuous_snd))
        ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    exact integral_prod _ hint
  · rw [← kernelOperator_original_LIP016 S D hK hc J hD]
    exact (kernelOp_basis_coefficient_LIP016 S D hK hc i j).symm

theorem gate_lip051_01_bind_campaign_data_source_data_dK (S : Spec d) (D : KData d)
    (J : InteractionData d)
    (hD : ∀ x y, D.K x y = centeredKernel J (specProbability_LIP016 S) x y) :
    Continuous (fun x => D.K x x) ∧ Integrable (fun x => D.K x x) S.mu ∧
    dK_LIP05101 S D.K = ∫ x, D.K x x ∂S.mu ∧
    dK_LIP05101 S D.K = -meanInteraction J (specProbability_LIP016 S) := by
  have hdc : Continuous (fun x => D.K x x) := D.Kc.comp (continuous_id.prodMk continuous_id)
  refine ⟨hdc, hdc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), rfl, ?_⟩
  have hdiag := (gate_lip051_01_bind_campaign_data_source_data_kernel S D J hD).2.2.2.1
  have hconv : Integrable (interactionConvolution J (specProbability_LIP016 S)) S.mu :=
    (continuous_interactionConvolution J (specProbability_LIP016 S)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hI := integral_interactionConvolution J (specProbability_LIP016 S)
  change ∫ x, D.K x x ∂S.mu = _
  simp_rw [hdiag]
  change ∫ x, -2 * interactionConvolution J (specProbability_LIP016 S) x +
    meanInteraction J (specProbability_LIP016 S) ∂S.mu = _
  rw [integral_add (hconv.const_mul _) (integrable_const _), integral_const_mul]
  have hI' : ∫ x, interactionConvolution J (specProbability_LIP016 S) x ∂S.mu =
    meanInteraction J (specProbability_LIP016 S) := hI
  rw [hI']
  simp
  ring

/-! ### (e) the positive-index Wick sections and `Q_T` -/

theorem finiteWickLp_congr_LIP05101 (B C : ℕ → ℕ → ℝ) (s : Finset ℕ)
    (h : ∀ i ∈ s, ∀ j ∈ s, B i j = C i j) :
    finiteWickLp_LIP016 B s = finiteWickLp_LIP016 C s := by
  apply MemLp.toLp_congr
  refine Eventually.of_forall fun z => ?_
  rw [finiteWickOn_eq_LIP016, finiteWickOn_eq_LIP016]
  congr 1
  · exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by rw [h i hi j hj]
  · exact Finset.sum_congr rfl fun i hi => h i hi i hi

theorem wickSection_ae_LIP05101 (S : Spec d) (K : Torus d → Torus d → ℝ) (R : ℕ) :
    (wickSection_LIP05101 S K R : (ℕ → ℝ) → ℝ) =ᵐ[gaussianCountable_LIP016]
      fun z => (∑ i ∈ Finset.Icc 1 R, ∑ j ∈ Finset.Icc 1 R, TK S K i j * z i * z j) -
        ∑ i ∈ Finset.Icc 1 R, TK S K i i := by
  filter_upwards [(finiteWickOn_memLp_LIP016 (fun i j => TK S K i j) (Finset.Icc 1 R)).coeFn_toLp]
    with z hz
  change (finiteWickOn_memLp_LIP016 (fun i j => TK S K i j) (Finset.Icc 1 R)).toLp
    (finiteWickOn_LIP016 (fun i j => TK S K i j) (Finset.Icc 1 R)) z = _
  rw [hz, finiteWickOn_eq_LIP016]

theorem wickSection_eq_kernelWick_LIP05101 (S : Spec d) (A : Aux S) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x) (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (R : ℕ) :
    wickSection_LIP05101 S D.K R = kernelWickLp_LIP016 S D 0 R := by
  have hsub : Finset.Icc 1 R ⊆ Finset.range (R + 1) := fun i hi => by
    have := Finset.mem_Icc.mp hi
    exact Finset.mem_range.mpr (by omega)
  have hleft : ∀ i, i ∉ Finset.Icc 1 R → ∀ j, kernelCoefficient_LIP016 S D 0 R i j = 0 := by
    intro i hi j
    by_cases h0 : i = 0
    · subst h0; exact kernelCoefficient_zero_left_LIP016 S D A.v0 hc 0 R j
    · refine kernelCoefficient_support_left_LIP016 S D 0 R i (fun h => hi ?_) j
      have := Finset.mem_range.mp h
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hright : ∀ j, j ∉ Finset.Icc 1 R → ∀ i, kernelCoefficient_LIP016 S D 0 R i j = 0 := by
    intro j hj i
    by_cases h0 : j = 0
    · subst h0; exact kernelCoefficient_zero_right_LIP016 S D A.v0 hc hK 0 R i
    · refine kernelCoefficient_support_right_LIP016 S D 0 R j (fun h => hj ?_) i
      have := Finset.mem_range.mp h
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  unfold kernelWickLp_LIP016 wickSection_LIP05101
  rw [finiteWickLp_padding_LIP016 _ _ _ hsub hleft hright]
  apply finiteWickLp_congr_LIP05101
  intro i hi j hj
  have hi' := Finset.mem_Icc.mp hi
  have hj' := Finset.mem_Icc.mp hj
  simp [kernelCoefficient_LIP016, hi'.2, hj'.2]

theorem wickSection_tendsto_LIP05101 (S : Spec d) (A : Aux S) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x) (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) :
    Tendsto (wickSection_LIP05101 S D.K) atTop (𝓝 (QT_LIP05101 S D.K)) := by
  obtain ⟨q, hq, -⟩ := kernelWick_completion_LIP016 S D hK (fun _ => 0) id
    (fun _ => le_rfl) tendsto_const_nhds strictMono_id
  have hfun : wickSection_LIP05101 S D.K = fun R => kernelWickLp_LIP016 S D 0 (id R) :=
    funext fun R => wickSection_eq_kernelWick_LIP05101 S A D hK hc R
  have h : Tendsto (wickSection_LIP05101 S D.K) atTop (𝓝 q) := by
    rw [hfun]; exact hq
  exact tendsto_nhds_limUnder ⟨q, h⟩

/-! ### Identification of `Q_T` with the LIP016 Wick limit -/

theorem kernelWick_dist_le_LIP05101 (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x) {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) (m n : ℕ) :
    ‖kernelWickLp_LIP016 S D t m - kernelWickLp_LIP016 S D u n‖ ^ 2 ≤
      4 * ((∑' p : ℕ × ℕ, (kernelCoefficient_LIP016 S D t m p.1 p.2 - TK S D.K p.1 p.2) ^ 2) +
        ∑' p : ℕ × ℕ, (kernelCoefficient_LIP016 S D u n p.1 p.2 - TK S D.K p.1 p.2) ^ 2) := by
  let a (p : ℕ × ℕ) := kernelCoefficient_LIP016 S D t m p.1 p.2
  let a' (p : ℕ × ℕ) := kernelCoefficient_LIP016 S D u n p.1 p.2
  let b (p : ℕ × ℕ) := TK S D.K p.1 p.2
  have hEs : Summable (fun p : ℕ × ℕ => (a p - b p) ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun p => kernelCoefficient_error_le_LIP016 S D ht m p.1 p.2) (hasSum_prod_sq S D).summable
  have hEs' : Summable (fun p : ℕ × ℕ => (a' p - b p) ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun p => kernelCoefficient_error_le_LIP016 S D hu n p.1 p.2) (hasSum_prod_sq S D).summable
  have hd (p : ℕ × ℕ) : (a p - a' p) ^ 2 ≤ 2 * (a p - b p) ^ 2 + 2 * (a' p - b p) ^ 2 := by
    nlinarith [sq_nonneg (a p + a' p - 2 * b p)]
  have hds : Summable (fun p : ℕ × ℕ => (a p - a' p) ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hd ((hEs.mul_left 2).add (hEs'.mul_left 2))
  have hsum := Summable.tsum_le_tsum hd hds ((hEs.mul_left 2).add (hEs'.mul_left 2))
  rw [Summable.tsum_add (hEs.mul_left 2) (hEs'.mul_left 2), tsum_mul_left, tsum_mul_left] at hsum
  have hid := kernelWick_difference_sq_LIP016 S D hK t u m n
  change ‖kernelWickLp_LIP016 S D t m - kernelWickLp_LIP016 S D u n‖ ^ 2 =
    2 * ∑' p, (a p - a' p) ^ 2 at hid
  change _ ≤ 4 * ((∑' p : ℕ × ℕ, (a p - b p) ^ 2) + ∑' p : ℕ × ℕ, (a' p - b p) ^ 2)
  nlinarith

theorem gate_lip051_01_bind_campaign_data_source_data_QT_unique (S : Spec d) (A : Aux S)
    (D : KData d) (J : InteractionData d)
    (hD : ∀ x y, D.K x y = centeredKernel J (specProbability_LIP016 S) x y)
    (t : ℕ → ℝ) (m : ℕ → ℕ) (ht0 : ∀ R, 0 ≤ t R) (ht : Tendsto t atTop (𝓝 0))
    (hm : StrictMono m) (q : Lp ℝ 2 gaussianCountable_LIP016)
    (hq : Tendsto (fun R => kernelWickLp_LIP016 S D (t R) (m R)) atTop (𝓝 q)) :
    q = QT_LIP05101 S D.K := by
  have hK := original_kernel_symmetric_LIP016 S D J hD
  have hc := original_kernel_centered_LIP016 S D J hD
  have hE := kernelCoefficient_hilbertSchmidt_tendsto_LIP016 S D t m ht0 ht hm
  have hE0 := kernelCoefficient_hilbertSchmidt_tendsto_LIP016 S D (fun _ => 0) m
    (fun _ => le_rfl) tendsto_const_nhds hm
  have hsq : Tendsto (fun R => ‖kernelWickLp_LIP016 S D (t R) (m R) -
      kernelWickLp_LIP016 S D 0 (m R)‖ ^ 2) atTop (𝓝 0) := by
    have h4 := (hE.add hE0).const_mul 4
    rw [add_zero, mul_zero] at h4
    exact squeeze_zero (fun R => sq_nonneg _)
      (fun R => kernelWick_dist_le_LIP05101 S D hK (ht0 R) le_rfl (m R) (m R)) h4
  have hn : Tendsto (fun R => ‖kernelWickLp_LIP016 S D (t R) (m R) -
      kernelWickLp_LIP016 S D 0 (m R)‖) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at this
    refine this.congr fun R => ?_
    simp only [Function.comp_apply]
    exact Real.sqrt_sq (norm_nonneg _)
  have hdiff : Tendsto (fun R => kernelWickLp_LIP016 S D (t R) (m R) -
      kernelWickLp_LIP016 S D 0 (m R)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hn
  have h0 : Tendsto (fun R => kernelWickLp_LIP016 S D 0 (m R)) atTop (𝓝 q) := by
    have := hq.sub hdiff
    rw [sub_zero] at this
    exact this.congr fun R => sub_sub_cancel _ _
  have h1 : Tendsto (fun R => kernelWickLp_LIP016 S D 0 (m R)) atTop
      (𝓝 (QT_LIP05101 S D.K)) := by
    have := (wickSection_tendsto_LIP05101 S A D hK hc).comp hm.tendsto_atTop
    exact this.congr fun R => wickSection_eq_kernelWick_LIP05101 S A D hK hc (m R)
  exact tendsto_nhds_unique h0 h1

/-! ### The zero-mode obstruction -/

theorem gate_lip051_01_bind_campaign_data_source_data_zero_mode (S : Spec d) (A : Aux S) :
    ¬ TendstoInDistribution (fun (N : ℕ) (x : Fin N → Torus d) => Z_LIP05101 S N 0 x) atTop
      (fun z : ℕ → ℝ => z 0) (fun N => refLaw_LIP05101 S N) gaussianCountable_LIP016 := by
  intro h
  have h1 := h.tendsto_charFun (1 : ℝ)
  have hlim : ‖charFun (gaussianCountable_LIP016.map (fun z : ℕ → ℝ => z 0)) (1 : ℝ)‖ =
      Real.exp (-(1 / 2)) := by
    rw [gaussianCountable_LIP016, Measure.infinitePi_map_eval (fun _ : ℕ => gaussianReal 0 1) 0,
      charFun_gaussianReal, Complex.norm_exp]
    simp
  have hN : ∀ N : ℕ, 1 ≤ N →
      ‖charFun ((refLaw_LIP05101 S N).map (fun x => Z_LIP05101 S N 0 x)) (1 : ℝ)‖ = 1 := by
    intro N hN
    have hZ : (fun x : Fin N → Torus d => Z_LIP05101 S N 0 x) = fun _ => Real.sqrt (N : ℝ) :=
      funext fun x => (gate_lip051_01_bind_campaign_data_source_data_Z S A).2.2 N hN x
    rw [hZ, Measure.map_const, measure_univ, one_smul, charFun_apply_real, integral_dirac]
    simp
  have h2 : Tendsto (fun N : ℕ =>
      ‖charFun ((refLaw_LIP05101 S N).map (fun x => Z_LIP05101 S N 0 x)) (1 : ℝ)‖) atTop
      (𝓝 (Real.exp (-(1 / 2)))) := by
    rw [← hlim]; exact h1.norm
  have h3 : Tendsto (fun N : ℕ =>
      ‖charFun ((refLaw_LIP05101 S N).map (fun x => Z_LIP05101 S N 0 x)) (1 : ℝ)‖) atTop
      (𝓝 1) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop 1] with N hN'
      exact (hN N hN').symm)
  have h4 := tendsto_nhds_unique h2 h3
  have h5 : Real.exp (-(1 / 2)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith


/-! ### Transport of the frozen statement -/

theorem blockZ_apply_LIP05101 (S : Spec d) (m N : ℕ) (x : Fin N → Torus d) (i : Fin m) :
    blockZ_LIP05101 S m N x i = Z_LIP05101 S N (i.val + 1) x := rfl

theorem blockCoord_apply_LIP05101 (m : ℕ) (z : ℕ → ℝ) (i : Fin m) :
    blockCoord_LIP05101 m z i = z (i.val + 1) := rfl

theorem gaussianCountable_marginal_LIP05101 (j : ℕ) :
    gaussianCountable_LIP016.map (fun z : ℕ → ℝ => z j) = gaussianReal 0 1 := by
  rw [gaussianCountable_LIP016]
  exact Measure.infinitePi_map_eval (fun _ : ℕ => gaussianReal 0 1) j

theorem jointFluctuationLimit_transport_LIP05101 (S : Spec d) (D : KData d) (J : InteractionData d)
    (hD : ∀ x y, D.K x y = centeredKernel J (specProbability_LIP016 S) x y) :
    JointFluctuationLimit_LIP05101 S D.K ↔
      JointFluctuationLimit_LIP05101 S (centeredKernel J (specProbability_LIP016 S)) := by
  have hfun : D.K = centeredKernel J (specProbability_LIP016 S) := by
    funext x y; exact hD x y
  rw [hfun]

theorem gate_lip051_01_bind_campaign_data_source_data (S : Spec d) (A : Aux S) (D : KData d)
    (J : InteractionData d)
    (hD : ∀ x y, D.K x y = centeredKernel J (specProbability_LIP016 S) x y) :
    -- (a) `mu = S.mu = wMeasure d S.w`, a probability measure
    (S.mu = wMeasure d S.w ∧ IsProbabilityMeasure S.mu) ∧
    -- (b) `Hw d S.w` is `L^2(S.mu)` and the LIP016 basis is the chosen basis
    (Hw d S.w = Lp ℝ 2 S.mu ∧ spectralBasis_LIP016 S = S.e) ∧
    -- (c) the chosen basis, its continuous representatives, and the LIP009 constant vector
    ((∀ j, S.v j =ᵐ[S.mu] ((S.e j : Hw d S.w) : Torus d → ℝ)) ∧ (∀ x, S.v 0 x = 1) ∧
      (((S.e 0 : Hw d S.w) : Torus d → ℝ) =ᵐ[wMeasure d S.w] fun _ => (1 : ℝ)) ∧
      S.e 0 = Lp.const 2 S.mu (1 : ℝ)) ∧
    -- (d) the original pointwise kernel is the centered kernel, diagonal included
    (D.K = centeredKernel J (specProbability_LIP016 S) ∧
      (∀ x y, D.K x y = J.W x y - ∫ u, J.W x u ∂S.mu - ∫ u, J.W u y ∂S.mu +
        ∫ p, J.W p.1 p.2 ∂(S.mu.prod S.mu)) ∧
      (∀ x, D.K x x = -2 * ∫ u, J.W x u ∂S.mu + ∫ p, J.W p.1 p.2 ∂(S.mu.prod S.mu)) ∧
      (∀ N (x : Fin N → Torus d), U_LIP05101 D.K N x =
        U_LIP05101 (centeredKernel J (specProbability_LIP016 S)) N x) ∧
      dK_LIP05101 S D.K = dK_LIP05101 S (centeredKernel J (specProbability_LIP016 S))) ∧
    -- (e) `Q_N`, `U_N`, `Z_{N,j}`, `T`, `d_K`, `Q_T`
    ((∀ N, refLaw_LIP05101 S N = Measure.pi (fun _ : Fin N => S.mu)) ∧
      (∀ N j (x : Fin N → Torus d),
        Z_LIP05101 S N j x = (Real.sqrt (N : ℝ))⁻¹ * ∑ l : Fin N, S.v j (x l)) ∧
      (∀ N, 1 ≤ N → ∀ x : Fin N → Torus d, Z_LIP05101 S N 0 x = Real.sqrt (N : ℝ)) ∧
      (∀ i j, TK S D.K i j = ∫ x, ∫ y, D.K x y * (S.v i x * S.v j y) ∂S.mu ∂S.mu) ∧
      (∀ i j, TK S D.K i j = ⟪spectralBasis_LIP016 S i,
        kernelOp J (specProbability_LIP016 S) (spectralBasis_LIP016 S j)⟫_ℝ) ∧
      dK_LIP05101 S D.K = ∫ x, D.K x x ∂S.mu ∧
      Tendsto (wickSection_LIP05101 S D.K) atTop (𝓝 (QT_LIP05101 S D.K)) ∧
      (∀ j, gaussianCountable_LIP016.map (fun z : ℕ → ℝ => z j) = gaussianReal 0 1) ∧
      (JointFluctuationLimit_LIP05101 S D.K ↔
        JointFluctuationLimit_LIP05101 S (centeredKernel J (specProbability_LIP016 S))) ∧
      ¬ TendstoInDistribution (fun (N : ℕ) (x : Fin N → Torus d) => Z_LIP05101 S N 0 x) atTop
        (fun z : ℕ → ℝ => z 0) (fun N => refLaw_LIP05101 S N) gaussianCountable_LIP016) := by
  have hK := original_kernel_symmetric_LIP016 S D J hD
  have hc := original_kernel_centered_LIP016 S D J hD
  have hfun : D.K = centeredKernel J (specProbability_LIP016 S) := by
    funext x y; exact hD x y
  have ha := gate_lip051_01_bind_campaign_data_source_data_mu S
  have hb := gate_lip051_01_bind_campaign_data_source_data_hilbert S
  have hcc := gate_lip051_01_bind_campaign_data_source_data_basis S A
  have hdd := gate_lip051_01_bind_campaign_data_source_data_kernel S D J hD
  have hZ := gate_lip051_01_bind_campaign_data_source_data_Z S A
  have hT := gate_lip051_01_bind_campaign_data_source_data_T S A D J hD
  exact ⟨⟨ha.1, ha.2.1⟩, ⟨hb.1, hb.2.2.2.2⟩,
    ⟨hcc.2.1, hcc.2.2.1, hcc.2.2.2.1, hcc.2.2.2.2.1⟩,
    ⟨hfun, hdd.1, hdd.2.2.2.1, hdd.2.2.2.2.1, hdd.2.2.2.2.2.1⟩,
    fun N => (gate_lip051_01_bind_campaign_data_source_data_law S N).1, hZ.1, hZ.2.2,
    hT.1, hT.2.1, rfl, wickSection_tendsto_LIP05101 S A D hK hc,
    gaussianCountable_marginal_LIP05101, jointFluctuationLimit_transport_LIP05101 S D J hD,
    gate_lip051_01_bind_campaign_data_source_data_zero_mode S A⟩

end DGPS.Frontier.LIP051
