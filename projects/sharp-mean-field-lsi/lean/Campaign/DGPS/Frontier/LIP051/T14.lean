import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# LIP051.14: Countable Gaussian product

Task id `LIP051.14`, title "Countable Gaussian product" (node LIP051, "Joint Gaussian and
quadratic fluctuation limit", category leaf formalization, verification V1).

## Provides

* `DGPS.Frontier.LIP051.lip051_14_countable_gaussian_product`: with
  `γ₀ = Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)` on `ℕ → ℝ`, (1) `γ₀` is a probability
  measure; (2) for every injective `ι : Fin m → ℕ` the law of the block `z ↦ (z (ι k))_k` under
  `γ₀` is `Measure.pi (fun _ : Fin m => gaussianReal 0 1)`; (3) for every `v` in
  `EuclideanSpace ℝ (Fin m)` the characteristic function of the block, realised in
  `EuclideanSpace ℝ (Fin m)`, at `v` is `exp (-(∑ k, v k ^ 2) / 2)`.
* `DGPS.Frontier.LIP051.lip051_14_countable_gaussian_product_block_law`: part (2) alone.
* `DGPS.Frontier.LIP051.lip051_14_countable_gaussian_product_charFun`: part (3) alone.
* `DGPS.Frontier.LIP051.lip051_14_countable_gaussian_product_integral`: the same statement as
  an integral, `∫ z, exp (i * ∑ k, v k * z (ι k)) ∂γ₀ = exp (-(∑ k, v k ^ 2) / 2)`.
* `DGPS.Frontier.LIP051.lip051_14_countable_gaussian_product_coord`: each single coordinate has
  law `gaussianReal 0 1`.
* `DGPS.Frontier.LIP051.lip051_14_countable_gaussian_product_finset`: the Finset form of (2),
  using `Finset.restrict`.

## R5 notes

1. Abstract statement. The specification gives no Lean binders, so the statement is the
   self-contained one about `Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)`. It does not
   use or mention `Spec`, `Aux`, `KData` or `InteractionData`; the identification with
   `DGPS.Lipschitz.gaussianCountable_LIP016` is definitional (the same expression) and belongs to
   LIP051.01. No hypotheses beyond those of the specification are added.
2. "Every finite family of distinct coordinate maps": read as an injective index map
   `ι : Fin m → ℕ` (any `m`, including `m = 0`), with the coordinate maps `z ↦ z (ι k)`. The
   Finset form is also provided.
3. "Product standard Gaussian law": `Measure.pi (fun _ => gaussianReal 0 1)` on `Fin m → ℝ`.
4. "Finite vector realised in `EuclideanSpace ℝ (Fin m)`": the block is mapped by
   `WithLp.toLp 2`, and `charFun` is Mathlib's characteristic function on that space (inner
   product pairing). The entries of `v` are the source coordinates, in the order of `ι`.
   The value `exp (-(∑ k, v k ^ 2) / 2)` is stated as a complex number, the cast of the real sum.
5. Positive-mode indexing (DEFECTS.md FD-002). The statement quantifies over all injective
   `ι : Fin m → ℕ`, so coordinate `0` is allowed: `γ₀` really is a product of standard Gaussians
   in every coordinate. This is a statement about the Gaussian side only; the issue that the data
   coordinate `Z_{N,0} = sqrt N` does not converge to a Gaussian is not touched here and nothing
   is strengthened or restricted. A caller that wants positive modes only composes with an `ι`
   taking values in `{j | 1 ≤ j}`.
6. Proof route. The marginal identity is `Measure.map_infinitePi_infinitePi_of_inj` followed by
   `Measure.infinitePi_eq_pi`, and the characteristic function is `charFun_pi` plus
   `charFun_gaussianReal`, so Fubini is carried by Mathlib's finite-product lemma.
-/

open MeasureTheory ProbabilityTheory Complex

namespace DGPS.Frontier.LIP051

/-- Block law for an injective index map. -/
theorem lip051_14_countable_gaussian_product_block_law {m : ℕ} (ι : Fin m → ℕ)
    (hι : Function.Injective ι) :
    (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)).map
        (fun (z : ℕ → ℝ) (k : Fin m) => z (ι k)) =
      Measure.pi (fun _ : Fin m => gaussianReal 0 1) := by
  rw [Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => gaussianReal 0 1) hι,
    Measure.infinitePi_eq_pi]

/-- Single coordinates are standard Gaussian. -/
theorem lip051_14_countable_gaussian_product_coord (j : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)).map (fun z : ℕ → ℝ => z j) =
      gaussianReal 0 1 :=
  Measure.infinitePi_map_eval (fun _ : ℕ => gaussianReal 0 1) j

/-- Finset form of the block law. -/
theorem lip051_14_countable_gaussian_product_finset (I : Finset ℕ) :
    (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)).map I.restrict =
      Measure.pi (fun _ : I => gaussianReal 0 1) :=
  Measure.infinitePi_map_restrict (fun _ : ℕ => gaussianReal 0 1)

/-- Characteristic function of a Gaussian block in `EuclideanSpace`. -/
theorem lip051_14_countable_gaussian_product_charFun {m : ℕ} (ι : Fin m → ℕ)
    (hι : Function.Injective ι) (v : EuclideanSpace ℝ (Fin m)) :
    charFun ((Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)).map
        (fun z : ℕ → ℝ => (WithLp.toLp 2 (fun k : Fin m => z (ι k)) : EuclideanSpace ℝ (Fin m))))
      v = Complex.exp (((-(∑ k, v k ^ 2) / 2 : ℝ) : ℂ)) := by
  have hmeas : Measurable (fun (z : ℕ → ℝ) (k : Fin m) => z (ι k)) := by fun_prop
  have h1 : (fun z : ℕ → ℝ => (WithLp.toLp 2 (fun k : Fin m => z (ι k)) :
      EuclideanSpace ℝ (Fin m))) =
      (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m)) ∘
        (fun (z : ℕ → ℝ) (k : Fin m) => z (ι k)) := rfl
  rw [h1, ← Measure.map_map (WithLp.measurable_toLp 2 (Fin m → ℝ)) hmeas,
    lip051_14_countable_gaussian_product_block_law ι hι]
  rw [charFun_pi (E := fun _ : Fin m => ℝ) (μ := fun _ => gaussianReal 0 1) v]
  simp_rw [charFun_gaussianReal]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp [Finset.sum_neg_distrib, neg_div, Finset.sum_div]

/-- Integral form of the characteristic function. -/
theorem lip051_14_countable_gaussian_product_integral {m : ℕ} (ι : Fin m → ℕ)
    (hι : Function.Injective ι) (v : Fin m → ℝ) :
    ∫ z : ℕ → ℝ, Complex.exp (((∑ k, v k * z (ι k) : ℝ) : ℂ) * Complex.I)
        ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) =
      Complex.exp (((-(∑ k, v k ^ 2) / 2 : ℝ) : ℂ)) := by
  have h := lip051_14_countable_gaussian_product_charFun ι hι (WithLp.toLp 2 v)
  rw [charFun, integral_map] at h
  · rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp [PiLp.inner_apply, mul_comm]
  · exact (by fun_prop : Measurable _).aemeasurable
  · exact (by fun_prop : Measurable _).aestronglyMeasurable

/-- The countable Gaussian product: probability, finite block laws and characteristic functions. -/
theorem lip051_14_countable_gaussian_product :
    IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) ∧
    (∀ (m : ℕ) (ι : Fin m → ℕ), Function.Injective ι →
      (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)).map
          (fun (z : ℕ → ℝ) (k : Fin m) => z (ι k)) =
        Measure.pi (fun _ : Fin m => gaussianReal 0 1)) ∧
    (∀ (m : ℕ) (ι : Fin m → ℕ), Function.Injective ι → ∀ v : EuclideanSpace ℝ (Fin m),
      charFun ((Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)).map
          (fun z : ℕ → ℝ => (WithLp.toLp 2 (fun k : Fin m => z (ι k)) :
            EuclideanSpace ℝ (Fin m)))) v =
        Complex.exp (((-(∑ k, v k ^ 2) / 2 : ℝ) : ℂ))) :=
  ⟨inferInstance, fun _ ι hι => lip051_14_countable_gaussian_product_block_law ι hι,
    fun _ ι hι v => lip051_14_countable_gaussian_product_charFun ι hι v⟩

end DGPS.Frontier.LIP051
