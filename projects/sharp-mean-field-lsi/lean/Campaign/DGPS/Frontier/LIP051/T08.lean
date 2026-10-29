import Mathlib
import DGPS.Frontier.LIP051.T35
import DGPS.Frontier.LIP051.T36
import DGPS.Frontier.LIP051.T37

/-!
# LIP051.08: Finite-product marginals and a.e. bookkeeping

Task id: LIP051.08 (node LIP051, joint Gaussian and quadratic fluctuation limit).
Title: Finite-product marginals and a.e. bookkeeping.

Provides:
* `DGPS.Frontier.LIP051.lip051_08_finite_product_marginals_e_bookkeeping`: for a probability measure
  `μ` on a measurable space `E` and a scalar field `𝕜` (`RCLike`, with its Borel structure), the
  four clauses of the specification hold: (1) every injective `q`-tuple of coordinate maps
  `X_{b k}` pushes `μ^N` to `μ^q`; (2) for injective blocks `b₁`, `b₂` with disjoint ranges and
  integrable block functions `f`, `g`, the product integral factors whenever the sampled product is
  integrable; (3) a measurable `f` on `E^q` that vanishes `μ^q`-a.e. makes `f (X_b ·)` vanish
  `μ^N`-a.e.; (4) for an `L²` kernel `K` on `E²` and distinct labels `l ≠ k`, evaluation at `(X_l, X_k)`
  preserves the `L²` seminorm.
* Helper `DGPS.Frontier.LIP051.injective_pair_LIP05108`: a pair of distinct labels is an injective
  selection `![l, k] : Fin 2 → Fin N`.

Dependencies: LIP051.35 (`DGPS.Frontier.LIP051.T35`, restriction law), LIP051.36 (`DGPS.Frontier.LIP051.T36`,
pullback of a.e. and integrability facts), LIP051.37 (`DGPS.Frontier.LIP051.T37`, factorization across
disjoint blocks).

R5 notes:
* Ambient spaces. `E` is an arbitrary measurable space and `μ` an arbitrary probability measure on it;
  `Torus d` with its Borel structure is one instance. The sample space is `Fin N → E` with the product
  σ-algebra, and `Q_N = Measure.pi (fun _ => μ)`. The scalar field `𝕜` is any `RCLike` field with
  `MeasurableSpace` and `BorelSpace`; the cases `ℝ` and `ℂ` are instances. No object of the campaign
  (`Spec`, `KData`, `Hw`, the Gaussian law, the kernel `K` of LIP051) is used or identified here.
* Clause (1), "distinct q-tuple of coordinate maps". A distinct tuple is an injective
  `b : Fin q → Fin N`; the tuple of coordinate maps is `restrictCoords_LIP05135 b`. Its law is the
  pushforward `Measure.map`. The conjunct `Measurable` records that the pushforward is genuine; it is
  the first conjunct of LIP051.35.
* Clause (2), "integrable functions of disjoint coordinate sets". A coordinate set is read as the range
  of an injective block (distinct labels, which is what makes the block law equal `μ^q`), and disjoint
  coordinate sets as disjoint ranges. "Integrable" is Mathlib's `Integrable` against the block laws
  `μ^{q₁}`, `μ^{q₂}`. "Whenever the product is integrable" is kept literally as the hypothesis
  `Integrable (f (X_{b₁} ·) * g (X_{b₂} ·))` under `μ^N`; the conclusion is the factorization
  `∫ = (∫ f) * (∫ g)` and nothing more. The product is in fact integrable under the other hypotheses
  (LIP051.37), but that fact is not part of this statement.
* Clause (3), "a measurable function ... vanishes almost everywhere". Read as `Measurable f` and
  `∀ᵐ y ∂μ^q, f y = 0`, with conclusion `∀ᵐ x ∂μ^N, f (X_b x) = 0`. Only this direction is claimed.
  The injectivity of `b` is the "distinct" hypothesis.
* Clause (4), "an L2 kernel ... at two distinct labels ... preserves its L2 norm". The kernel is a
  function `K : (Fin 2 → E) → 𝕜` on the two-coordinate block, carried as `Measurable K` and
  `MemLp K 2 μ^2`. The labels are `l k : Fin N` with `l ≠ k`, and the evaluated kernel is
  `x ↦ K (X_l x, X_k x)`, realised as `K (restrictCoords_LIP05135 ![l, k] x)`. "Preserves its L2 norm" is
  the equality of the extended L2 seminorms `eLpNorm · 2`, stated as an equality of `ℝ≥0∞` values.
  The `MemLp K 2` hypothesis is kept to match the phrase "L2 kernel"; the proof does not use it, since
  the norm identity holds for every measurable kernel (LIP051.36 clause (e)). The measurability
  hypothesis is the one that clause requires, and it is read as part of the phrase "kernel".
* Pointwise values. Every clause is about functions as written; no representative is chosen, and no
  value of a function on a null set is altered. The statement is for the given functions only.
* Mode indexing (FD-002). This unit involves no Gaussian object, no Fourier or Hilbert-basis mode, and
  no mode index. No positive-mode or mode-zero reading is adopted; the issue recorded in FD-002 is not
  touched.
* No statement is strengthened or weakened beyond the notes above. The four clauses are stated in a
  single conjunction, each universally quantified over its own data.
-/

namespace DGPS.Frontier.LIP051

open MeasureTheory

/-- A pair of distinct labels gives an injective two-element selection `![l, k] : Fin 2 → Fin N`. -/
lemma injective_pair_LIP05108 {N : ℕ} {l k : Fin N} (hlk : l ≠ k) :
    Function.Injective (![l, k] : Fin 2 → Fin N) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

/-- **LIP051.08.** Finite-product marginals and a.e. bookkeeping on `μ^N = Measure.pi (fun _ => μ)`:
(1) injective coordinate tuples have law `μ^q`; (2) factorization of the product integral across
disjoint integrable blocks, under integrability of the product; (3) a.e. vanishing of a measurable
function on `E^q` pulls back to a.e. vanishing at distinct labels; (4) evaluation of an `L²` kernel at
two distinct labels preserves the `L²` seminorm. -/
theorem lip051_08_finite_product_marginals_e_bookkeeping
    {𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] :
    (∀ (q N : ℕ) (b : Fin q → Fin N), Function.Injective b →
        Measurable (restrictCoords_LIP05135 (E := E) b) ∧
        Measure.map (restrictCoords_LIP05135 (E := E) b) (Measure.pi fun _ : Fin N => μ)
          = Measure.pi fun _ : Fin q => μ) ∧
    (∀ (q₁ q₂ N : ℕ) (b₁ : Fin q₁ → Fin N) (b₂ : Fin q₂ → Fin N),
        Function.Injective b₁ → Function.Injective b₂ →
        Disjoint (Set.range b₁) (Set.range b₂) →
        ∀ (f : (Fin q₁ → E) → 𝕜) (g : (Fin q₂ → E) → 𝕜),
          Integrable f (Measure.pi fun _ : Fin q₁ => μ) →
          Integrable g (Measure.pi fun _ : Fin q₂ => μ) →
          Integrable (fun x : Fin N → E =>
              f (restrictCoords_LIP05135 b₁ x) * g (restrictCoords_LIP05135 b₂ x))
            (Measure.pi fun _ : Fin N => μ) →
          ∫ x, f (restrictCoords_LIP05135 b₁ x) * g (restrictCoords_LIP05135 b₂ x)
              ∂(Measure.pi fun _ : Fin N => μ)
            = (∫ y, f y ∂(Measure.pi fun _ : Fin q₁ => μ)) *
              ∫ y, g y ∂(Measure.pi fun _ : Fin q₂ => μ)) ∧
    (∀ (q N : ℕ) (b : Fin q → Fin N), Function.Injective b →
        ∀ f : (Fin q → E) → 𝕜, Measurable f →
          (∀ᵐ y ∂(Measure.pi fun _ : Fin q => μ), f y = 0) →
          ∀ᵐ x ∂(Measure.pi fun _ : Fin N => μ), f (restrictCoords_LIP05135 b x) = 0) ∧
    (∀ (N : ℕ) (K : (Fin 2 → E) → 𝕜) (l k : Fin N), l ≠ k → Measurable K →
        MemLp K 2 (Measure.pi fun _ : Fin 2 => μ) →
        eLpNorm (fun x : Fin N → E => K (restrictCoords_LIP05135 (E := E) (![l, k] : Fin 2 → Fin N) x))
            2 (Measure.pi fun _ : Fin N => μ)
          = eLpNorm K 2 (Measure.pi fun _ : Fin 2 => μ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q N b hb
    exact lip051_35_finite_coordinate_restriction_law μ b hb
  · intro q₁ q₂ N b₁ b₂ h₁ h₂ hd f g hf hg _
    exact (lip051_37_factorization_across_disjoint_blocks μ b₁ b₂ h₁ h₂ hd f g hf hg).2.1
  · intro q N b hb f hf hae
    have h := (lip051_36_pullback_almost_everywhere_integrability_facts μ b hb f hf).1
      (fun _ => 0) measurable_const hae
    filter_upwards [h] with x hx
    exact hx
  · intro N K l k hlk hK _
    exact (lip051_36_pullback_almost_everywhere_integrability_facts μ (![l, k] : Fin 2 → Fin N)
      (injective_pair_LIP05108 hlk) K hK).2.2.2.2.1

end DGPS.Frontier.LIP051
