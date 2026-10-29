import DGPS.Frontier.LIP051.T44
import DGPS.Frontier.LIP051.T45

/-!
# LIP051.17: L2 Wick limit

Task id `LIP051.17`, title "L2 Wick limit" (node LIP051, "Joint Gaussian and quadratic fluctuation
limit", category leaf formalization, verification V1). Proved inputs: `LIP051.44`
(`DGPS.Frontier.LIP051.T44`) and `LIP051.45` (`DGPS.Frontier.LIP051.T45`).

Setting. The data `μ`, `W`, `e`, `f` and the coefficients `T i j = coefT_LIP05134 μ W f i j` are those
of `LIP051.06`. The reference law is `γ₀ = Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)` on
`ℕ → ℝ`. The Wick section of rank `R` is `Q_R z = ∑ i ∈ {1,…,R}, ∑ j ∈ {1,…,R}, T i j (z i z j - δ i j)`,
that is `wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z`. The tail `K - K_R` is
`tailKR_LIP05134 μ W f R`, and `d_K = ∫ K(x,x) dμ(x)` is `dK_LIP05145 μ W`.

## Provides

* `DGPS.Frontier.LIP051.lip051_17_l2_wick_limit`: the main theorem, the conjunction of three
  statements. (1) Some `L²(γ₀)` function `Q_T` is the `L²(γ₀)` limit of the Wick sections `Q_R`.
  (2) Any two `L²(γ₀)` limits of the Wick sections agree `γ₀`-almost everywhere. (3) For every
  `L²(γ₀)` limit `Q_T`: its mean under `γ₀` is zero; `‖Q_T - Q_R‖₂² = 2 ‖K - K_R‖₂²` holds for every
  rank `R`; and some measurable representative `Q'` of `Q_T` makes `(Q' + d_K) / 2` measurable and
  in `L²(γ₀)`.

No helper declaration is introduced. The proof assembles conjuncts 3 and 4 of `LIP051.44` (for
(1) and (2)) and conjunct 2 of `LIP051.45` (for (3)); conjunct 1 of `LIP051.45` is the same
existence statement as conjunct 3 of `LIP051.44`, and it is not repeated.

## R5 notes

1. Hypotheses. The binders are exactly those of `LIP051.06`, `LIP051.44` and `LIP051.45`:
   `IsProbabilityMeasure μ`, continuity of `Function.uncurry W`, symmetry of `W`, `0 ≤ M` with
   `|W x y| ≤ M`, the real Hilbert basis `e` of `L²(μ)` with `e 0 = 1`, and measurable
   representatives `f j =ᵐ[μ] e j`. They are the node setting, not hypotheses added by this unit;
   the specification of `LIP051.17` lists none of its own.
2. Positive modes (defect FD-002, open for R5). The sums defining `Q_R` run over `i, j ∈ {1,…,R}`,
   that is `Finset.Icc 1 R`, as the specification's sum from `1` to `R`. The zero mode is never read:
   `Q_R` depends only on the coordinates `z i` with `1 ≤ i ≤ R`. The zero-mode obstruction of the
   node (with `e 0 = 1`, the zero empirical variable is `√N`) concerns a different object and does not
   enter this statement.
3. Unique limit. "There is a unique `Q_T` in real `L²` of `γ₀` such that `Q_R → Q_T` in `L²`" is
   read as (1) existence of an `L²(γ₀)` function `Q_T : (ℕ → ℝ) → ℝ` with
   `lpNorm (Q_R - Q_T) 2 γ₀ → 0`, and (2) almost-everywhere uniqueness: any two such `L²` functions
   agree `γ₀`-a.e. The `L²(γ₀)` norm is `lpNorm … 2 γ₀`, which is `(eLpNorm … 2 γ₀).toReal`.
   Uniqueness is an a.e. statement, which is the meaning of a unique element of `L²`.
4. Quantifier over the limit. The mean, the tail identity and the representative of conjunct (3)
   are stated for every `L²(γ₀)` limit `Q_T`, not only for a chosen one. By conjunct (2) every such
   `Q_T` agrees a.e. with the unique one, and all three properties are invariant under a.e.
   modification (the integral and the `lpNorm` are, and the representative is chosen afterwards).
   So this is equivalent to the specification's reading of "its" and adds no content.
5. Mean. The mean is the Bochner integral `∫ Q_T dγ₀`, which is zero.
6. Tail identity. The left side is `lpNorm (Q_T - Q_R) 2 γ₀ ^ 2`, the squared `L²(γ₀)` norm. The right
   side is `2 * (eLpNorm (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)).toReal ^ 2`, that is twice the squared
   `L²(μ ⊗ μ)` norm of `K - K_R`. The kernel `K` is the pointwise continuous centered kernel
   `centeredKernelOf_LIP05103 μ W`, so the original diagonal is retained and `K` is never an arbitrary
   representative of its product-`L²` class.
7. Representative and `U_∞`. The specification's `U_∞ = (Q_T + d_K)/2` is not introduced as a named
   object. Its content is: there is a measurable `Q' : (ℕ → ℝ) → ℝ` with `Q' =ᵐ[γ₀] Q_T`, such that
   `z ↦ (Q' z + d_K) / 2` is measurable and lies in `L²(γ₀)`, where `d_K = dK_LIP05145 μ W`
   `= ∫ K(x,x) dμ(x)` is the Bochner integral of the pointwise diagonal. Since `Q'` is determined only
   up to a.e. equality, `U_∞` is determined only up to a.e. equality as well.
8. Identification. `μ`, `W`, `e`, `f` are arbitrary data of the stated types. The campaign objects
   `S.mu`, `D.K` and the campaign's named Gaussian limit are not referenced; that identification is
   the open adapter `LIP051.01` (FD-002), which is not resolved here.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace DGPS.Frontier.LIP051

/-- LIP051.17: L2 Wick limit. For the Wick sections `Q_R` of the centered kernel with coefficients
`T i j` over positive modes `1,…,R`: some `L²(γ₀)` function is the `L²` limit of the sections; any
two `L²` limits agree a.e.; and every `L²` limit `Q_T` has mean zero, satisfies
`‖Q_T - Q_R‖₂² = 2‖K - K_R‖₂²` for every `R`, and has a measurable representative `Q'` with
`(Q' + d_K)/2` measurable and in `L²(γ₀)`. See the module docstring, R5 notes. -/
theorem lip051_17_l2_wick_limit {d : ℕ}
    {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    {W : DGPS.Torus d → DGPS.Torus d → ℝ} {M : ℝ}
    (hWc : Continuous (Function.uncurry W)) (hs : ∀ x y, W x y = W y x)
    (hM : 0 ≤ M) (hb : ∀ x y, |W x y| ≤ M)
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (he0 : e 0 = Lp.const 2 μ (1 : ℝ))
    (f : ℕ → DGPS.Torus d → ℝ) (hfm : ∀ j, Measurable (f j))
    (hfe : ∀ j, f j =ᵐ[μ] (e j : DGPS.Torus d → ℝ)) :
    (∃ QT : (ℕ → ℝ) → ℝ, MemLp QT 2 gam_LIP05144 ∧
        Tendsto (fun R : ℕ => lpNorm (fun z : ℕ → ℝ =>
          wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z - QT z) 2 gam_LIP05144)
          atTop (𝓝 0)) ∧
    (∀ Q₁ Q₂ : (ℕ → ℝ) → ℝ, MemLp Q₁ 2 gam_LIP05144 → MemLp Q₂ 2 gam_LIP05144 →
        Tendsto (fun R : ℕ => lpNorm (fun z : ℕ → ℝ =>
          wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z - Q₁ z) 2 gam_LIP05144)
          atTop (𝓝 0) →
        Tendsto (fun R : ℕ => lpNorm (fun z : ℕ → ℝ =>
          wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z - Q₂ z) 2 gam_LIP05144)
          atTop (𝓝 0) →
        Q₁ =ᵐ[gam_LIP05144] Q₂) ∧
    (∀ QT : (ℕ → ℝ) → ℝ, MemLp QT 2 gam_LIP05144 →
        Tendsto (fun R : ℕ => lpNorm (fun z : ℕ → ℝ =>
          wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z - QT z) 2 gam_LIP05144)
          atTop (𝓝 0) →
        (∫ z, QT z ∂gam_LIP05144 = 0) ∧
        (∀ R : ℕ, lpNorm (fun z : ℕ → ℝ =>
            QT z - wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144 ^ 2
          = 2 * (eLpNorm (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)).toReal ^ 2) ∧
        (∃ Q' : (ℕ → ℝ) → ℝ, Measurable Q' ∧ Q' =ᵐ[gam_LIP05144] QT ∧
          Measurable (fun z : ℕ → ℝ => (Q' z + dK_LIP05145 μ W) / 2) ∧
          MemLp (fun z : ℕ → ℝ => (Q' z + dK_LIP05145 μ W) / 2) 2 gam_LIP05144)) := by
  obtain ⟨-, -, -, huniq⟩ :=
    lip051_44_cauchy_wick_sections_existence_limit hWc hs hM hb e he0 f hfm hfe
  obtain ⟨hex, hrep⟩ :=
    lip051_45_exact_wick_tail_mean_representative hWc hs hM hb e he0 f hfm hfe
  exact ⟨hex, huniq, hrep⟩

end DGPS.Frontier.LIP051
