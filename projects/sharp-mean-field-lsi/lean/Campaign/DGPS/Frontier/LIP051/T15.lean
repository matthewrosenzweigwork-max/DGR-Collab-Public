import DGPS.Frontier.LIP051.T41
import DGPS.Frontier.LIP051.T42
import DGPS.Frontier.LIP051.T43

/-!
# LIP051.15: Gaussian fourth moments

Task id `LIP051.15`, title "Gaussian fourth moments" (node LIP051, "Joint Gaussian and quadratic
fluctuation limit", category leaf formalization, verification V1).

## Provides

* `DGPS.Frontier.LIP051.lip051_15_gaussian_fourth_moments`: for the reference product law
  `γ₀ = Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)` on `ℕ → ℝ` with coordinates `z i`,
  the conjunction of (1) `∫ z i dγ₀ = 0`, (2) `∫ z i ^ 2 dγ₀ = 1`, (3) `∫ z i ^ 4 dγ₀ = 3` for
  every index `i`; (4) for all indices `i j k l`, `∫ z i * z j * z k * z l dγ₀` equals
  `δ_ij δ_kl + δ_ik δ_jl + δ_il δ_jk` (Kronecker symbols as `if a = b then 1 else 0` in `ℝ`); and
  (5) every coordinate monomial of total degree at most four is `γ₀`-integrable, the monomial
  being written as `f.prod (fun i n => z i ^ n)` with `f : ℕ →₀ ℕ` and `f.sum (fun _ n => n) ≤ 4`.
* Helpers (all suffixed `_LIP05115`), not intended for use outside this file: `zero_mom_LIP05115`
  (the zeroth scalar moment), `sum_single_LIP05115` (total degree of a single coordinate
  monomial), and `coord_moment_LIP05115` (the law of a single coordinate: for `p ≤ 4`,
  `∫ z i ^ p dγ₀ = ∫ x ^ p dγ₁` with `γ₁ = gaussianReal 0 1`).

## R5 notes

1. Mode index (FD-002). The statement quantifies over all coordinate indices `i j k l : ℕ`,
   index zero included, as written in the specification. It concerns the reference law `γ₀`
   itself, in which every coordinate, including coordinate zero, is a standard Gaussian. The
   zero-mode obstruction (`Z_{N,0} = sqrt N` almost surely, for the empirical sum with `e_0 = 1`)
   concerns the finite-`N` fluctuation variables and does not arise for `γ₀` coordinates. No
   positive-mode restriction is added or dropped here; the positive-mode convention matters only
   for the convergence statement of the node.
2. Reference law. `γ₀` is `Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)`, the same measure
   as in LIP051.42 and LIP051.43. "Coordinate functions" are the evaluations `z ↦ z i`.
3. Moments are Bochner integrals. In Lean, `∫` of a non-integrable function is `0`, so each moment
   identity is backed by an integrability fact: the coordinate powers `z i ^ p` with `p ≤ 4` are
   integrable by LIP051.42 (conjunct 5 applied to the single-coordinate exponent vector
   `Finsupp.single i p`), so the values `0`, `1`, `3` are genuine integrals and not vacuous
   defaults.
4. Monomials. "All degree-at-most-four coordinate monomials" is read through the grouped encoding
   of LIP051.42: a finitely supported exponent vector `f : ℕ →₀ ℕ` (distinct indices in the support,
   multiplicities as values) with total degree `f.sum (fun _ n => n) ≤ 4`. Every monomial in
   finitely many coordinates, with repeated indices merged, has this form, and the empty monomial
   (`f = 0`, degree zero) is included. The integrability conjunct concerns `γ₀`.
5. Kronecker symbols are read as `(if a = b then (1 : ℝ) else 0)`, and the three-term right-hand
   side is summed in `ℝ`, exactly as in LIP051.43.
6. Proof route. No new analysis is performed. Conjuncts (1)–(3) come from the scalar moments of
   LIP051.41 transported to the coordinate law by the one-coordinate instance of the LIP051.42
   factorization. Conjunct (4) is the pairing identity of LIP051.43. Conjunct (5) is the
   integrability part of LIP051.42. The file adds no hypotheses and no unproved placeholders.
-/

open MeasureTheory ProbabilityTheory

namespace DGPS.Frontier.LIP051

private lemma zero_mom_LIP05115 : ∫ x : ℝ, x ^ 0 ∂(gaussianReal 0 1) = 1 := by simp

private lemma sum_single_LIP05115 (a p : ℕ) : (Finsupp.single a p).sum (fun _ n => n) = p :=
  Finsupp.sum_single_index rfl

/-- The law of a single coordinate under `γ₀`: `∫ z i ^ p dγ₀ = ∫ x ^ p dγ₁` for `p ≤ 4`. -/
private lemma coord_moment_LIP05115 (i p : ℕ) (hp : p ≤ 4) :
    ∫ z : ℕ → ℝ, z i ^ p ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1))
      = ∫ x : ℝ, x ^ p ∂(gaussianReal 0 1) := by
  have hdeg : (Finsupp.single i p).sum (fun _ n => n) ≤ 4 := by
    rw [sum_single_LIP05115]
    exact hp
  have h := (lip051_42_gaussian_monomial_factorization (Finsupp.single i p) hdeg).2.2
  have hpt : ∀ z : ℕ → ℝ, (Finsupp.single i p).prod (fun j n => z j ^ n) = z i ^ p :=
    fun z => Finsupp.prod_single_index (pow_zero _)
  have hm : (Finsupp.single i p).prod (fun _ n => ∫ x : ℝ, x ^ n ∂(gaussianReal 0 1))
      = ∫ x : ℝ, x ^ p ∂(gaussianReal 0 1) :=
    Finsupp.prod_single_index zero_mom_LIP05115
  simp only [hpt, hm] at h
  exact h

/-- **LIP051.15.** Gaussian fourth moments under the reference product law
`γ₀ = Measure.infinitePi (fun _ => N(0,1))` on `ℕ → ℝ`: the coordinate moments `E z_i = 0`,
`E z_i ^ 2 = 1`, `E z_i ^ 4 = 3`; the four-index pairing identity
`E (z_i z_j z_k z_l) = δ_ij δ_kl + δ_ik δ_jl + δ_il δ_jk`; and integrability of every coordinate
monomial of total degree at most four. -/
theorem lip051_15_gaussian_fourth_moments :
    (∀ i : ℕ, ∫ z : ℕ → ℝ, z i ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) = 0) ∧
    (∀ i : ℕ, ∫ z : ℕ → ℝ, z i ^ 2 ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) = 1) ∧
    (∀ i : ℕ, ∫ z : ℕ → ℝ, z i ^ 4 ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) = 3) ∧
    (∀ i j k l : ℕ,
      ∫ z : ℕ → ℝ, z i * z j * z k * z l
          ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1))
        = (if i = j then (1 : ℝ) else 0) * (if k = l then (1 : ℝ) else 0)
          + (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
          + (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)) ∧
    (∀ f : ℕ →₀ ℕ, f.sum (fun _ n => n) ≤ 4 →
      Integrable (fun z : ℕ → ℝ => f.prod (fun i n => z i ^ n))
        (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1))) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_,
    fun i j k l => lip051_43_gaussian_fourth_moment_pairing_identity i j k l,
    fun f hf => (lip051_42_gaussian_monomial_factorization f hf).1⟩
  · have h := coord_moment_LIP05115 i 1 (by norm_num)
    simp only [pow_one] at h
    rw [h]
    exact (lip051_41_exact_scalar_gaussian_fourth_moment).1
  · rw [coord_moment_LIP05115 i 2 (by norm_num)]
    exact (lip051_41_exact_scalar_gaussian_fourth_moment).2.1
  · rw [coord_moment_LIP05115 i 4 (by norm_num)]
    exact (lip051_41_exact_scalar_gaussian_fourth_moment).2.2.2.1

end DGPS.Frontier.LIP051
