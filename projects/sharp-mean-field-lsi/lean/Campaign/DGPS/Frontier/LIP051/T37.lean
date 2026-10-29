import Mathlib
import DGPS.Frontier.LIP051.T36

/-!
# LIP051.37: Factorization across disjoint blocks

Task id: LIP051.37 (node LIP051, joint Gaussian and quadratic fluctuation limit).
Title: Factorization across disjoint blocks.

Provides:
* `DGPS.Frontier.LIP051.lip051_37_factorization_across_disjoint_blocks`: for a probability measure
  `μ` on `E`, injective `b₁ : Fin q₁ → Fin N` and `b₂ : Fin q₂ → Fin N` with disjoint ranges, and
  integrable `f : (Fin q₁ → E) → 𝕜`, `g : (Fin q₂ → E) → 𝕜` (`𝕜` an `RCLike` field), on the finite
  product `(Fin N → E, μ^N)` the sampled product `x ↦ f (X_A x) * g (X_B x)`, with `X_A x = x ∘ b₁`
  and `X_B x = x ∘ b₂` (`restrictCoords_LIP05135`), is integrable; its expectation is
  `(∫ f dμ^{q₁}) * (∫ g dμ^{q₂})`; and the expectation of its norm is `(∫ ‖f‖ dμ^{q₁}) * (∫ ‖g‖ dμ^{q₂})`.
* `DGPS.Frontier.LIP051.lip051_37_factorization_across_disjoint_blocks_probability_space`: the same
  three conclusions on an arbitrary probability space `(Ω, P)` and a map `X : Ω → (Fin N → E)`
  whose combined selected coordinates `restrictCoords_LIP05135 (Fin.append b₁ b₂) ∘ X` have the law
  `μ^(q₁+q₂)`; the expectations are taken under `P`.
* Helpers (all suffixed `_LIP05137`): `splitBlocks_LIP05137` (the split `E^(q₁+q₂) ≃ E^q₁ × E^q₂`
  as a measurable map), `splitBlocks_apply_LIP05137` (its explicit formula),
  `measurePreserving_splitBlocks_LIP05137` (it carries `μ^(q₁+q₂)` to the product `μ^q₁ ⊗ μ^q₂`),
  `factor_LIP05137` (the product-law factorization of integrability and of the integral).
  The probability-space theorem carries the extra almost-everywhere measurability hypothesis `hX`
  (see R5).

R5 notes:
* Scalar field. `𝕜` is any `RCLike` field, as in LIP051.36; the specification's cases `ℝ` and `ℂ`
  are instances. The specification's absolute value `|·|` is the norm `‖·‖`, which agrees with it
  for `ℝ` and `ℂ`. Integrals are Bochner integrals.
* Integrability. The specification's "integrable" is Mathlib's `Integrable` for the block product
  measures. No measurability of `f` or `g` is assumed; `Integrable` supplies strong measurability,
  which is all the proof uses.
* Blocks. Injectivity of `b₁`, `b₂` and disjointness of their ranges are the specification's
  hypotheses. They enter the main theorem through LIP051.35 (`Fin.append b₁ b₂` is injective, so
  its restriction pushes `μ^N` to `μ^(q₁+q₂)`). The combined selection is `Fin.append b₁ b₂`.
* Probability-space clause. The specification's sentence "the identical conclusion holds on any
  probability space whose combined selected coordinates have this finite product law" is read as
  the probability-space theorem: `P` is a probability measure on any measurable space `Ω`, and
  `X : Ω → (Fin N → E)` is a random vector whose combined selected coordinates
  `restrictCoords_LIP05135 (Fin.append b₁ b₂) ∘ X` are almost everywhere measurable (hypothesis `hX`)
  and have law `μ^(q₁+q₂)`. The hypothesis `hX` is an addition to the specification's listed
  hypotheses, flagged for review. It is the reading of "has this law" that the proof needs: Mathlib's
  `Measure.map` sends a probability measure along a map that is not almost everywhere measurable to a
  Dirac measure, so the equation of push-forwards alone does not fix the distribution of `X`. The
  main theorem discharges `hX` by the measurability of the restriction (`X = id`). The
  injectivity and disjointness hypotheses are not needed in the probability-space theorem, since the
  law already fixes the combined selection, so they are omitted. The clause "including the Gaussian
  product in .14" is not formalized: LIP051.14 is not among this unit's prerequisites, and the theorem
  covers every probability law `μ^(q₁+q₂)` of the stated form, including a Gaussian one only if it is
  supplied as such a product law.
* Sampled coordinates. `X_A` is `restrictCoords_LIP05135 b₁`, that is `x ↦ (k ↦ x (b₁ k))`; the
  same map is used in LIP051.35 and LIP051.36.
* Product identities. The two identities are the factorization of the expectation of
  `f (X_A) * g (X_B)` and of its norm; the norm identity is the case `𝕜 := ℝ` applied to `‖f‖`
  and `‖g‖`, after `‖f a * g b‖ = ‖f a‖ * ‖g b‖`.
* Mode indexing (FD-002). No mode index occurs in this unit: there is no Gaussian object, no
  Fourier or Hilbert-basis mode, and no `Finset ℕ` of coordinate indices. The statement is abstract
  in `E`, `μ`, `b₁`, `b₂`, `f`, `g`. No positive-mode or mode-zero reading is adopted, and the
  issue recorded in FD-002 is not touched.
* No strengthening beyond the specification is claimed in the main theorem; its hypotheses are
  exactly those listed above.
-/

namespace DGPS.Frontier.LIP051

open MeasureTheory

/-- The split of a coordinate vector `E^(q₁+q₂)` into its two blocks, as a measurable map. -/
def splitBlocks_LIP05137 {E : Type*} [MeasurableSpace E] (q₁ q₂ : ℕ) :
    (Fin (q₁ + q₂) → E) → (Fin q₁ → E) × (Fin q₂ → E) :=
  ⇑(MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin q₁ ⊕ Fin q₂ => E)) ∘
    ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin (q₁ + q₂) => E) finSumFinEquiv).symm

/-- Explicit formula: the split sends `y` to `(y ∘ castAdd, y ∘ natAdd)`. -/
lemma splitBlocks_apply_LIP05137 {E : Type*} [MeasurableSpace E] (q₁ q₂ : ℕ)
    (y : Fin (q₁ + q₂) → E) :
    splitBlocks_LIP05137 q₁ q₂ y
      = (fun k => y (Fin.castAdd q₂ k), fun k => y (Fin.natAdd q₁ k)) := by
  refine Prod.ext ?_ ?_ <;> funext k <;>
    simp only [splitBlocks_LIP05137, Function.comp_apply, MeasurableEquiv.piCongrLeft,
      MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk, MeasurableEquiv.coe_sumPiEquivProdPi,
      Equiv.sumPiEquivProdPi_apply, Equiv.piCongrLeft_symm_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right]

/-- The split carries the finite product `μ^(q₁+q₂)` to the product `μ^q₁ ⊗ μ^q₂`. -/
lemma measurePreserving_splitBlocks_LIP05137 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] (q₁ q₂ : ℕ) :
    MeasurePreserving (splitBlocks_LIP05137 (E := E) q₁ q₂)
      (Measure.pi fun _ : Fin (q₁ + q₂) => μ)
      ((Measure.pi fun _ : Fin q₁ => μ).prod (Measure.pi fun _ : Fin q₂ => μ)) :=
  (measurePreserving_sumPiEquivProdPi (fun _ : Fin q₁ ⊕ Fin q₂ => μ)).comp
    (measurePreserving_piCongrLeft (fun _ : Fin (q₁ + q₂) => μ) finSumFinEquiv).symm

/-- Factorization on a product law: if `Φ` pushes `P` to the product `μ_A ⊗ μ_B`, then
`f (Φ₁ ω) * g (Φ₂ ω)` is integrable with expectation the product of the marginal integrals. -/
lemma factor_LIP05137 {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] {𝕜 : Type*} [RCLike 𝕜] (P : Measure Ω) (μA : Measure A)
    (μB : Measure B) [SFinite μA] [SFinite μB] (Φ : Ω → A × B) (hΦ : AEMeasurable Φ P)
    (hlaw : Measure.map Φ P = μA.prod μB) (f : A → 𝕜) (g : B → 𝕜)
    (hf : Integrable f μA) (hg : Integrable g μB) :
    Integrable (fun ω => f (Φ ω).1 * g (Φ ω).2) P ∧
      ∫ ω, f (Φ ω).1 * g (Φ ω).2 ∂P = (∫ a, f a ∂μA) * ∫ b, g b ∂μB := by
  have hH : Integrable (fun z : A × B => f z.1 * g z.2) (Measure.map Φ P) := by
    rw [hlaw]
    exact hf.mul_prod hg
  refine ⟨(integrable_map_measure hH.aestronglyMeasurable hΦ).1 hH, ?_⟩
  have key := integral_map hΦ hH.aestronglyMeasurable
  rw [hlaw, integral_prod_mul] at key
  exact key.symm

/-- **LIP051.37, probability-space form.** Let `P` be a probability measure on `Ω` and
`X : Ω → (Fin N → E)` such that the combined selected coordinates `X ↦ (X_{b₁ k}, X_{b₂ k})`, that is
`restrictCoords_LIP05135 (Fin.append b₁ b₂) ∘ X`, are almost everywhere measurable (`hX`) and have the
finite product law `μ^(q₁+q₂)`. Then for
integrable block functions `f`, `g` (with respect to `μ^q₁`, `μ^q₂`), the sampled product
`f (X_A) * g (X_B)` is integrable under `P`, its expectation factors, and so does the expectation of
its norm. -/
theorem lip051_37_factorization_across_disjoint_blocks_probability_space
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {N q₁ q₂ : ℕ} (b₁ : Fin q₁ → Fin N) (b₂ : Fin q₂ → Fin N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → (Fin N → E))
    (hX : AEMeasurable (restrictCoords_LIP05135 (E := E) (Fin.append b₁ b₂) ∘ X) P)
    (hlaw : Measure.map (restrictCoords_LIP05135 (E := E) (Fin.append b₁ b₂) ∘ X) P
      = Measure.pi (fun _ : Fin (q₁ + q₂) => μ))
    (f : (Fin q₁ → E) → 𝕜) (g : (Fin q₂ → E) → 𝕜)
    (hf : Integrable f (Measure.pi fun _ : Fin q₁ => μ))
    (hg : Integrable g (Measure.pi fun _ : Fin q₂ => μ)) :
    Integrable (fun ω => f (restrictCoords_LIP05135 b₁ (X ω)) *
        g (restrictCoords_LIP05135 b₂ (X ω))) P ∧
      ∫ ω, f (restrictCoords_LIP05135 b₁ (X ω)) * g (restrictCoords_LIP05135 b₂ (X ω)) ∂P
        = (∫ y, f y ∂(Measure.pi fun _ : Fin q₁ => μ)) *
          ∫ y, g y ∂(Measure.pi fun _ : Fin q₂ => μ) ∧
      ∫ ω, ‖f (restrictCoords_LIP05135 b₁ (X ω)) * g (restrictCoords_LIP05135 b₂ (X ω))‖ ∂P
        = (∫ y, ‖f y‖ ∂(Measure.pi fun _ : Fin q₁ => μ)) *
          ∫ y, ‖g y‖ ∂(Measure.pi fun _ : Fin q₂ => μ) := by
  have hR := hX
  have hΨ := measurePreserving_splitBlocks_LIP05137 μ q₁ q₂
  have hfun : (fun ω => (restrictCoords_LIP05135 b₁ (X ω), restrictCoords_LIP05135 b₂ (X ω)))
      = splitBlocks_LIP05137 q₁ q₂ ∘ (restrictCoords_LIP05135 (E := E) (Fin.append b₁ b₂) ∘ X) := by
    funext ω
    simp only [Function.comp_apply, splitBlocks_apply_LIP05137, restrictCoords_LIP05135,
      Fin.append_left, Fin.append_right]
    rfl
  have hΦ : AEMeasurable (fun ω => (restrictCoords_LIP05135 b₁ (X ω),
      restrictCoords_LIP05135 b₂ (X ω))) P := by
    rw [hfun]
    exact hΨ.measurable.comp_aemeasurable hR
  have hΘ : AEMeasurable (splitBlocks_LIP05137 (E := E) q₁ q₂)
      (Measure.map (restrictCoords_LIP05135 (E := E) (Fin.append b₁ b₂) ∘ X) P) := by
    rw [hlaw]
    exact hΨ.measurable.aemeasurable
  have hmap : Measure.map (fun ω => (restrictCoords_LIP05135 b₁ (X ω),
      restrictCoords_LIP05135 b₂ (X ω))) P
      = (Measure.pi fun _ : Fin q₁ => μ).prod (Measure.pi fun _ : Fin q₂ => μ) := by
    rw [hfun, ← AEMeasurable.map_map_of_aemeasurable hΘ hR, hlaw, hΨ.map_eq]
  have hF := factor_LIP05137 P (Measure.pi fun _ : Fin q₁ => μ)
    (Measure.pi fun _ : Fin q₂ => μ) _ hΦ hmap f g hf hg
  have hN := factor_LIP05137 (𝕜 := ℝ) P (Measure.pi fun _ : Fin q₁ => μ)
    (Measure.pi fun _ : Fin q₂ => μ) _ hΦ hmap (fun y => ‖f y‖) (fun y => ‖g y‖) hf.norm hg.norm
  refine ⟨hF.1, hF.2, ?_⟩
  simp only [norm_mul]
  exact hN.2

/-- **LIP051.37.** Let `μ` be a probability measure on `E`, let `b₁ : Fin q₁ → Fin N` and
`b₂ : Fin q₂ → Fin N` be injective with disjoint ranges, and let `f`, `g` be integrable with respect
to the block product laws `μ^q₁`, `μ^q₂`. Then on the finite product `μ^N` the sampled product
`f (X_A) * g (X_B)` is integrable, `E[f (X_A) * g (X_B)] = (∫ f dμ^q₁) * (∫ g dμ^q₂)`, and
`E[‖f (X_A) * g (X_B)‖] = (∫ ‖f‖ dμ^q₁) * (∫ ‖g‖ dμ^q₂)`. -/
theorem lip051_37_factorization_across_disjoint_blocks
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {N q₁ q₂ : ℕ} (b₁ : Fin q₁ → Fin N) (b₂ : Fin q₂ → Fin N)
    (h₁ : Function.Injective b₁) (h₂ : Function.Injective b₂)
    (hd : Disjoint (Set.range b₁) (Set.range b₂))
    (f : (Fin q₁ → E) → 𝕜) (g : (Fin q₂ → E) → 𝕜)
    (hf : Integrable f (Measure.pi fun _ : Fin q₁ => μ))
    (hg : Integrable g (Measure.pi fun _ : Fin q₂ => μ)) :
    Integrable (fun x : Fin N → E => f (restrictCoords_LIP05135 b₁ x) *
        g (restrictCoords_LIP05135 b₂ x)) (Measure.pi fun _ : Fin N => μ) ∧
      ∫ x, f (restrictCoords_LIP05135 b₁ x) * g (restrictCoords_LIP05135 b₂ x)
          ∂(Measure.pi fun _ : Fin N => μ)
        = (∫ y, f y ∂(Measure.pi fun _ : Fin q₁ => μ)) *
          ∫ y, g y ∂(Measure.pi fun _ : Fin q₂ => μ) ∧
      ∫ x, ‖f (restrictCoords_LIP05135 b₁ x) * g (restrictCoords_LIP05135 b₂ x)‖
          ∂(Measure.pi fun _ : Fin N => μ)
        = (∫ y, ‖f y‖ ∂(Measure.pi fun _ : Fin q₁ => μ)) *
          ∫ y, ‖g y‖ ∂(Measure.pi fun _ : Fin q₂ => μ) :=
  lip051_37_factorization_across_disjoint_blocks_probability_space μ b₁ b₂
    (Measure.pi fun _ : Fin N => μ) id
    ((measurable_restrictCoords_LIP05135 (Fin.append b₁ b₂)).comp measurable_id).aemeasurable
    (lip051_35_finite_coordinate_restriction_law_append μ b₁ b₂ h₁ h₂ hd).2 f g hf hg

end DGPS.Frontier.LIP051
