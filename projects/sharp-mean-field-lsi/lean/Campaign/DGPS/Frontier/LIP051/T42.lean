import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import DGPS.Frontier.LIP051.T14
import DGPS.Frontier.LIP051.T41

/-!
# LIP051.42: Gaussian monomial factorization

Task id `LIP051.42`, title "Gaussian monomial factorization" (node LIP051, "Joint Gaussian and
quadratic fluctuation limit", category leaf formalization, verification V1).

## Provides

* `DGPS.Frontier.LIP051.lip051_42_gaussian_monomial_factorization`: let `γ₀` be the infinite
  product `Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)` on `ℕ → ℝ`, and let a finite
  coordinate monomial be given by an exponent vector `f : ℕ →₀ ℕ` of total degree
  `f.sum (fun _ n => n) ≤ 4`, read as `∏ i ∈ f.support, z i ^ f i`. Then (1) the monomial is
  `γ₀`-integrable; (2) the integral of its absolute value is `∏ i ∈ f.support, ∫ |x| ^ f i dγ₁`;
  (3) its integral is `∏ i ∈ f.support, ∫ x ^ f i dγ₁`, where `γ₁ = gaussianReal 0 1`.
* `DGPS.Frontier.LIP051.lip051_42_gaussian_monomial_factorization_empty`: the empty monomial
  (`f = 0`) has integral one under `γ₀`.
* Helpers (all suffixed `_LIP05142`): `prod_subtype_LIP05142` (a `Finsupp.prod` as a product over
  the subtype of its support), `pow_integrable_LIP05142` (integrability of `x ^ n`, `n ≤ 4`, under
  `γ₁`), `block_integrable_LIP05142` and `block_integral_LIP05142` (integrability and the
  integral of a product of coordinatewise functions over a finite index set `I` under `γ₀`).

## R5 notes

1. Monomial encoding. The specification says: group equal indices and write the monomial as
   `∏_{r} z_{b_r} ^ {n_r}` with distinct `b_r` and `n_r ≥ 1`. The statement represents this
   grouped form directly as a finitely supported exponent vector `f : ℕ →₀ ℕ`: the support of `f`
   is the set of distinct indices `{b_r}`, the values `f i` are the multiplicities `n_r ≥ 1`, and
   the monomial is `f.prod (fun i n => z i ^ n)`. Equal indices are therefore merged by the
   encoding and are not left as a separate case. The empty monomial is `f = 0`.
2. Degree bound. "Total degree at most four" is read as `f.sum (fun _ n => n) ≤ 4`, that is the sum
   of all multiplicities is at most four. No other bound is imposed.
3. Coordinates. The specification states no restriction on the indices, so every `i : ℕ` is
   allowed, including `i = 0`. This is the literal reading and no positive-mode restriction is
   added (FD-002). The statement concerns `γ₀`, a product of standard Gaussians in every
   coordinate (LIP051.14, note 5), so index zero is covered by the same argument. Any positive-mode
   statement is the special case of an exponent vector whose support avoids `0`.
4. Scalar moments. The scalar moment is `∫ x ^ n dγ₁` with `γ₁ = gaussianReal 0 1`, and the
   absolute scalar moment is `∫ |x| ^ n dγ₁`. The absolute integral of the monomial is written as
   `∫ |M| dγ₀` with `|·|` the absolute value on `ℝ`, which equals the norm.
5. Integrability. The specification's "integrable" is Mathlib's `Integrable` with respect to
   `γ₀`. Each factor `x ^ n` with `n ≤ 4` is integrable under `γ₁` by LIP051.41, using its
   `|x| ^ k` integrability for `k ≤ 4` and the bound `|x ^ n| = |x| ^ n`.
6. Factorization route. The specification factors the monomial by LIP051.37 applied one coordinate
   at a time. This file instead uses the finite-block law of LIP051.14 (the finset form
   `Measure.infinitePi_map_restrict`) and Mathlib's Fubini identity for finite products of
   functions of separate coordinates, `MeasureTheory.integral_fintype_prod_eq_prod`, together with
   `MeasureTheory.Integrable.fintype_prod`. Both are the same product-law factorization that
   LIP051.37 proves for block functions. LIP051.37 is not used.
7. Empty monomial. The specification's "the empty monomial has integral one" is stated as the
   separate lemma `lip051_42_gaussian_monomial_factorization_empty`, which also follows from the
   general statement with `f = 0`.
-/

open MeasureTheory ProbabilityTheory

namespace DGPS.Frontier.LIP051

/-- A `Finsupp.prod` as the product over the subtype of its support. -/
lemma prod_subtype_LIP05142 (f : ℕ →₀ ℕ) {M : Type*} [CommMonoid M] (h : ℕ → ℕ → M) :
    f.prod h = ∏ i : f.support, h (i : ℕ) (f i) := by
  rw [Finsupp.prod]
  exact (Finset.prod_coe_sort f.support (fun i => h i (f i))).symm

/-- Integrability of `x ^ n` for `n ≤ 4` under the standard Gaussian law, from LIP051.41. -/
lemma pow_integrable_LIP05142 {n : ℕ} (hn : n ≤ 4) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 1) := by
  refine (lip051_41_exact_scalar_gaussian_fourth_moment_abs_integrable hn).mono'
    (by fun_prop) (ae_of_all _ fun x => ?_)
  simp

/-- Integrability of a product of coordinatewise functions over a finite index set `I`, under
the countable Gaussian product `γ₀`. -/
lemma block_integrable_LIP05142 (I : Finset ℕ) (g : ℕ → ℝ → ℝ)
    (hint : ∀ i ∈ I, Integrable (g i) (gaussianReal 0 1)) :
    Integrable (fun z : ℕ → ℝ => ∏ i : I, g (i : ℕ) (z (i : ℕ)))
      (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) := by
  have hφ : Measurable (I.restrict : (ℕ → ℝ) → (I → ℝ)) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  have hI : Integrable (fun x : I → ℝ => ∏ i : I, g (i : ℕ) (x i))
      (Measure.pi fun _ : I => gaussianReal 0 1) :=
    Integrable.fintype_prod (ι := I) (f := fun i : I => g (i : ℕ))
      (μ := fun _ : I => gaussianReal 0 1) (fun i => hint i i.2)
  rw [← lip051_14_countable_gaussian_product_finset I] at hI
  exact (integrable_map_measure hI.aestronglyMeasurable hφ.aemeasurable).1 hI

/-- The integral of a product of coordinatewise functions over a finite index set `I`, under
`γ₀`, is the product of the one-dimensional integrals. -/
lemma block_integral_LIP05142 (I : Finset ℕ) (g : ℕ → ℝ → ℝ) (hg : ∀ i, Measurable (g i)) :
    ∫ z : ℕ → ℝ, ∏ i : I, g (i : ℕ) (z (i : ℕ))
        ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1))
      = ∏ i : I, ∫ x, g (i : ℕ) x ∂(gaussianReal 0 1) := by
  have hφ : Measurable (I.restrict : (ℕ → ℝ) → (I → ℝ)) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  have hF : Measurable (fun x : I → ℝ => ∏ i : I, g (i : ℕ) (x i)) := by
    fun_prop
  refine Eq.trans ?_ (integral_fintype_prod_eq_prod (fun (i : I) (y : ℝ) => g (i : ℕ) y)
    (μ := fun _ : I => gaussianReal 0 1))
  rw [← lip051_14_countable_gaussian_product_finset I,
    integral_map hφ.aemeasurable hF.aestronglyMeasurable]
  rfl

/-- **LIP051.42.** Gaussian monomial factorization. Let `γ₀ = Measure.infinitePi (fun _ => N(0,1))`
on `ℕ → ℝ`, and let `f : ℕ →₀ ℕ` have total degree `∑ n ∈ supp f, f n ≤ 4`. The monomial
`z ↦ ∏ i ∈ supp f, z i ^ f i` (the grouped form of a finite coordinate monomial of degree at most
four) is `γ₀`-integrable; its absolute integral is `∏ i ∈ supp f, ∫ |x| ^ f i dγ₁`, and its integral
is `∏ i ∈ supp f, ∫ x ^ f i dγ₁`, where `γ₁ = N(0,1)` on `ℝ`. -/
theorem lip051_42_gaussian_monomial_factorization (f : ℕ →₀ ℕ)
    (hf : f.sum (fun _ n => n) ≤ 4) :
    Integrable (fun z : ℕ → ℝ => f.prod (fun i n => z i ^ n))
        (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) ∧
    ∫ z : ℕ → ℝ, |f.prod (fun i n => z i ^ n)|
        ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1))
      = f.prod (fun _ n => ∫ x : ℝ, |x| ^ n ∂(gaussianReal 0 1)) ∧
    ∫ z : ℕ → ℝ, f.prod (fun i n => z i ^ n)
        ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1))
      = f.prod (fun _ n => ∫ x : ℝ, x ^ n ∂(gaussianReal 0 1)) := by
  have hdeg : ∀ i ∈ f.support, f i ≤ 4 := by
    intro i hi
    simp only [Finsupp.sum] at hf
    exact le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi) hf
  simp only [prod_subtype_LIP05142]
  refine ⟨?_, ?_, ?_⟩
  · exact block_integrable_LIP05142 f.support (fun j y => y ^ f j)
      (fun j hj => pow_integrable_LIP05142 (hdeg j hj))
  · simp only [Finset.abs_prod, abs_pow]
    exact block_integral_LIP05142 f.support (fun j y => |y| ^ f j) (fun j => by fun_prop)
  · exact block_integral_LIP05142 f.support (fun j y => y ^ f j) (fun j => by fun_prop)

/-- The empty monomial has integral one under `γ₀`. -/
theorem lip051_42_gaussian_monomial_factorization_empty :
    ∫ z : ℕ → ℝ, (0 : ℕ →₀ ℕ).prod (fun i n => z i ^ n)
        ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) = 1 := by
  simp [Finsupp.prod_zero_index]

end DGPS.Frontier.LIP051
