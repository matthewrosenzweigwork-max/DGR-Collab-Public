import Mathlib
import DGPS.Frontier.LIP051.T35

/-!
# LIP051.36: Pullback of almost-everywhere and integrability facts

Task id: LIP051.36 (node LIP051, joint Gaussian and quadratic fluctuation limit).
Title: Pullback of almost-everywhere and integrability facts.

Provides:
* `DGPS.Frontier.LIP051.lip051_36_pullback_almost_everywhere_integrability_facts`: for a probability
  measure `μ` on a measurable space `E`, an injective `b : Fin q → Fin N`, and a measurable scalar
  function `f : E^q → 𝕜` (with `r = restrictCoords_LIP05135 b : E^N → E^q`, `μ^N = Measure.pi`
  on `Fin N → E`, `μ^q = Measure.pi` on `Fin q → E`), the following hold:
  (a) for every measurable `g`, `f =ᵐ[μ^q] g` implies `f ∘ r =ᵐ[μ^N] g ∘ r`;
  (b) `Integrable (f ∘ r) μ^N ↔ Integrable f μ^q`;
  (c) `MemLp (f ∘ r) 2 μ^N ↔ MemLp f 2 μ^q`;
  (d) `eLpNorm (f ∘ r) 1 μ^N = eLpNorm f 1 μ^q` (the `L¹` norm);
  (e) `eLpNorm (f ∘ r) 2 μ^N = eLpNorm f 2 μ^q` (the `L²` norm);
  (f) if `f` is integrable, `∫ f ∘ r dμ^N = ∫ f dμ^q`.
* Helpers: none. The proof uses the restriction law `lip051_35_finite_coordinate_restriction_law_measurePreserving`
  of LIP051.35 (`DGPS.Frontier.LIP051.T35`), which states that `r` is measure preserving from `μ^N` to `μ^q`,
  and Mathlib's pullback lemmas for measure-preserving maps.

R5 notes:
* Scalar field. `𝕜` is any `RCLike` field with `[MeasurableSpace 𝕜] [BorelSpace 𝕜]`. The two
  instances the specification names, `ℝ` and `ℂ`, are both `RCLike`, so the statement covers them;
  it is not restricted to them and no other field is claimed. Integrals are Bochner integrals.
* Measurability. "Measurable scalar functions on `E^q`" is read as `Measurable` for the product
  σ-algebra on `Fin q → E` and the Borel σ-algebra on `𝕜`. Both `f` and `g` are assumed measurable;
  `g` appears only in clause (a), where it is quantified over with its measurability as in the
  specification. `f` alone is the subject of clauses (b)–(f).
* Restriction map. The specification's `r_b` is `restrictCoords_LIP05135 b` of LIP051.35. That map is
  defined and proved to be the restriction law only for injective `b`, so `hb : Function.Injective b`
  is a hypothesis of this statement. It is the hypothesis of LIP051.35, not an additional assumption.
* Probability measure. `μ` is `[IsProbabilityMeasure μ]`, as in LIP051.35 ("probability measure").
  The product measures `μ^N = Measure.pi (fun _ : Fin N => μ)` and `μ^q` are the pushforward source and
  target of LIP051.35.
* Pushforward. The specification's "pushforward integral formula" and "pushforward" are used through
  `MeasurePreserving`, which LIP051.35 establishes; no pushforward is taken for a non-measurable map.
* Norms. "Norms are equal under this pullback" is read as equality of the extended `L^p` seminorms
  `eLpNorm ... 1` and `eLpNorm ... 2`, which are the `L¹` and `L²` norms (the real norm is their
  `toReal`). Equality of the `ℝ≥0∞` values is at least as strong as equality of the finite real norms,
  and holds also when both are infinite. The specification does not ask for more.
* Membership. `L¹` membership is `Integrable` (Mathlib's `Integrable`, equivalent to `MemLp · 1`).
  `L²` membership is `MemLp · 2`. "Preserved and reflected" is read as the two-sided `↔`.
* Almost-everywhere clause. The specification's implication is kept in its single direction: from
  `f = g` almost everywhere to `f ∘ r = g ∘ r` almost everywhere. No converse is claimed.
* Integral clause. The specification's clause "for integrable `f`" is the hypothesis
  `Integrable f μ^q`; the conclusion is the equality of the two Bochner integrals.
* Mode indexing (FD-002). This unit involves no Gaussian object, no Fourier mode and no `Finset ℕ`
  of coordinate indices. The statement is abstract in `E`, `μ`, `b` and `f`, so no positive-mode or
  mode-zero reading is adopted here; the issue recorded in FD-002 is not touched.
* No strengthening. Every clause above is the specification's clause, with the measurability and
  injectivity hypotheses as described. Nothing is added beyond them.
-/

namespace DGPS.Frontier.LIP051

open MeasureTheory

/-- **LIP051.36.** For a probability measure `μ` on `E` and an injective `b : Fin q → Fin N`, with
`r = restrictCoords_LIP05135 b` pushing `μ^N` to `μ^q` (LIP051.35), a measurable scalar function
`f` on `E^q` satisfies the almost-everywhere pullback, the `L¹` and `L²` membership and norm
equalities, and the integral identity under `r`. -/
theorem lip051_36_pullback_almost_everywhere_integrability_facts
    {𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    {q N : ℕ} (b : Fin q → Fin N) (hb : Function.Injective b)
    (f : (Fin q → E) → 𝕜) (hf : Measurable f) :
    (∀ g : (Fin q → E) → 𝕜, Measurable g →
        f =ᵐ[Measure.pi (fun _ : Fin q => μ)] g →
          (f ∘ restrictCoords_LIP05135 (E := E) b)
            =ᵐ[Measure.pi (fun _ : Fin N => μ)] (g ∘ restrictCoords_LIP05135 (E := E) b)) ∧
    (Integrable (f ∘ restrictCoords_LIP05135 (E := E) b) (Measure.pi (fun _ : Fin N => μ)) ↔
        Integrable f (Measure.pi (fun _ : Fin q => μ))) ∧
    (MemLp (f ∘ restrictCoords_LIP05135 (E := E) b) 2 (Measure.pi (fun _ : Fin N => μ)) ↔
        MemLp f 2 (Measure.pi (fun _ : Fin q => μ))) ∧
    (eLpNorm (f ∘ restrictCoords_LIP05135 (E := E) b) 1 (Measure.pi (fun _ : Fin N => μ)) =
        eLpNorm f 1 (Measure.pi (fun _ : Fin q => μ))) ∧
    (eLpNorm (f ∘ restrictCoords_LIP05135 (E := E) b) 2 (Measure.pi (fun _ : Fin N => μ)) =
        eLpNorm f 2 (Measure.pi (fun _ : Fin q => μ))) ∧
    (Integrable f (Measure.pi (fun _ : Fin q => μ)) →
        ∫ x, f (restrictCoords_LIP05135 (E := E) b x) ∂(Measure.pi (fun _ : Fin N => μ)) =
          ∫ y, f y ∂(Measure.pi (fun _ : Fin q => μ))) := by
  have hT := lip051_35_finite_coordinate_restriction_law_measurePreserving μ b hb
  have hfa : AEStronglyMeasurable f (Measure.pi (fun _ : Fin q => μ)) := hf.aestronglyMeasurable
  refine ⟨fun g _ h => hT.quasiMeasurePreserving.ae_eq_comp h, ?_, ?_, ?_, ?_, ?_⟩
  · exact hT.integrable_comp hfa
  · constructor
    · intro h2
      have h3 := eLpNorm_comp_measurePreserving (p := 2) hfa hT
      show eLpNorm f 2 _ < ⊤
      rw [← h3]
      exact h2
    · intro h2
      exact MemLp.comp_measurePreserving h2 hT
  · exact eLpNorm_comp_measurePreserving (p := 1) hfa hT
  · exact eLpNorm_comp_measurePreserving (p := 2) hfa hT
  · intro _
    have hfm : AEStronglyMeasurable f (Measure.map (restrictCoords_LIP05135 (E := E) b)
        (Measure.pi (fun _ : Fin N => μ))) := by
      rw [hT.map_eq]
      exact hfa
    have h4 := integral_map hT.measurable.aemeasurable hfm
    rw [hT.map_eq] at h4
    exact h4.symm

end DGPS.Frontier.LIP051
