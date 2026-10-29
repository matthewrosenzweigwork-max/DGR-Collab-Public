import Mathlib

/-!
# LIP051.35: Finite coordinate restriction law

Task id: LIP051.35 (node LIP051, joint Gaussian and quadratic fluctuation limit).
Title: Finite coordinate restriction law.

Provides:
* `DGPS.Frontier.LIP051.lip051_35_finite_coordinate_restriction_law`: for a probability measure `μ` on
  a measurable space `E` and an injective `b : Fin q → Fin N`, the restriction
  `restrictCoords_LIP05135 b : (Fin N → E) → (Fin q → E)`, `x ↦ fun k => x (b k)`, is measurable
  and pushes `Measure.pi (fun _ : Fin N => μ)` forward to `Measure.pi (fun _ : Fin q => μ)`.
* `DGPS.Frontier.LIP051.lip051_35_finite_coordinate_restriction_law_measurePreserving`: the same
  statement as `MeasurePreserving (restrictCoords_LIP05135 b) (Measure.pi _) (Measure.pi _)`.
* `DGPS.Frontier.LIP051.lip051_35_finite_coordinate_restriction_law_append`: the "in particular"
  clause: two coordinate blocks `b₁ : Fin q₁ → Fin N`, `b₂ : Fin q₂ → Fin N`, each injective with
  disjoint ranges, are combined into the single injective selection `Fin.append b₁ b₂`, and the
  restriction along it pushes `μ^N` to `μ^(q₁+q₂)`.
* Helpers (all suffixed `_LIP05135`): `restrictCoords_LIP05135` (the map `r_b`),
  `measurable_restrictCoords_LIP05135` (its measurability),
  `preimage_pi_restrictCoords_LIP05135` (the preimage of a measurable rectangle is a rectangle
  with `univ` at the unselected coordinates), `prod_extend_LIP05135` (the product of the
  rectangle factors reduces to the selected coordinates), `injective_append_LIP05135`
  (injectivity of the concatenated selection).

R5 notes:
* Hypotheses are exactly those of the specification: `μ` is a probability measure on an arbitrary
  measurable space `E` (`[MeasurableSpace E] [IsProbabilityMeasure μ]`); `q N : ℕ`;
  `b : Fin q → Fin N` injective. Nothing else is assumed.
* `E^N` is `Fin N → E` with the product sigma algebra, and `μ^N` is `Measure.pi (fun _ => μ)`.
  `Measure.pi` needs `SigmaFinite` of the factors; this is supplied by the probability instance.
  The case `q = 0` and the case `N = 0` need no separate treatment.
* "Pushforward" is `Measure.map`; since `r_b` is proved measurable, `Measure.map` is the genuine
  pushforward (not the junk value `0` for non-measurable maps).
* The final sentence ("any disjoint finite coordinate blocks can be combined into one such
  restriction") is realised as the corollary `_append`: the combined selection is
  `Fin.append b₁ b₂ : Fin (q₁ + q₂) → Fin N`, whose injectivity is derived from injectivity of each
  block and disjointness of their ranges (`Disjoint (Set.range b₁) (Set.range b₂)`). This is the
  only reading given to that clause; for `q = q₁ + q₂` it is an instance of the main statement.
* The node note on positive versus zero modes (FD-002) is not involved: the statement is abstract
  in `E` and `μ` and makes no mention of Fourier modes, so no indexing convention is chosen here.
-/

namespace DGPS.Frontier.LIP051

open MeasureTheory

/-- The coordinate restriction `r_b : E^N → E^q`, `r_b(x)_k = x_{b(k)}`. -/
def restrictCoords_LIP05135 {E : Type*} {q N : ℕ} (b : Fin q → Fin N) :
    (Fin N → E) → (Fin q → E) :=
  fun x k => x (b k)

/-- `r_b` is measurable: its components are coordinate evaluations. -/
lemma measurable_restrictCoords_LIP05135 {E : Type*} [MeasurableSpace E] {q N : ℕ}
    (b : Fin q → Fin N) : Measurable (restrictCoords_LIP05135 (E := E) b) :=
  Measurable.of_eval fun k => measurable_pi_apply (b k)

/-- The preimage of the rectangle `∏ₖ Aₖ` is the rectangle imposing `x_{b k} ∈ Aₖ` on the selected
coordinates and nothing on the others. -/
lemma preimage_pi_restrictCoords_LIP05135 {E : Type*} {q N : ℕ} {b : Fin q → Fin N}
    (hb : Function.Injective b) (s : Fin q → Set E) :
    restrictCoords_LIP05135 b ⁻¹' Set.pi Set.univ s
      = Set.pi Set.univ (Function.extend b s (fun _ => Set.univ)) := by
  ext x
  simp only [restrictCoords_LIP05135, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
  constructor
  · intro h i
    by_cases hi : ∃ k, b k = i
    · obtain ⟨k, rfl⟩ := hi
      rw [hb.extend_apply]
      exact h k
    · rw [Function.extend_apply' _ _ _ hi]
      exact Set.mem_univ _
  · intro h k
    have := h (b k)
    rwa [hb.extend_apply] at this

/-- The product of the rectangle factors, with `μ univ = 1` at unselected coordinates, reduces to
the product over the selected coordinates. -/
lemma prod_extend_LIP05135 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {q N : ℕ} {b : Fin q → Fin N} (hb : Function.Injective b)
    (s : Fin q → Set E) :
    ∏ i : Fin N, μ (Function.extend b s (fun _ => Set.univ) i) = ∏ k : Fin q, μ (s k) := by
  classical
  have h1 : ∏ i ∈ Finset.univ.image b, μ (Function.extend b s (fun _ => Set.univ) i)
      = ∏ k : Fin q, μ (s k) := by
    rw [Finset.prod_image (fun x _ y _ h => hb h)]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hb.extend_apply]
  rw [← h1]
  symm
  refine Finset.prod_subset (Finset.subset_univ _) fun i _ hi => ?_
  have hi' : ¬ ∃ k, b k = i := by
    rintro ⟨k, rfl⟩
    exact hi (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  rw [Function.extend_apply' _ _ _ hi', measure_univ]

/-- **LIP051.35.** For a probability measure `μ` on a measurable space `E` and an injective
`b : Fin q → Fin N`, the restriction `r_b : E^N → E^q` pushes `μ^N` forward to `μ^q`. -/
theorem lip051_35_finite_coordinate_restriction_law {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] {q N : ℕ} (b : Fin q → Fin N)
    (hb : Function.Injective b) :
    Measurable (restrictCoords_LIP05135 (E := E) b) ∧
      Measure.map (restrictCoords_LIP05135 b) (Measure.pi (fun _ : Fin N => μ))
        = Measure.pi (fun _ : Fin q => μ) := by
  refine ⟨measurable_restrictCoords_LIP05135 b, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (measurable_restrictCoords_LIP05135 b) (MeasurableSet.univ_pi hs),
    preimage_pi_restrictCoords_LIP05135 hb, Measure.pi_pi, prod_extend_LIP05135 μ hb]

/-- The restriction law as a `MeasurePreserving` statement. -/
theorem lip051_35_finite_coordinate_restriction_law_measurePreserving {E : Type*}
    [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] {q N : ℕ} (b : Fin q → Fin N)
    (hb : Function.Injective b) :
    MeasurePreserving (restrictCoords_LIP05135 (E := E) b)
      (Measure.pi (fun _ : Fin N => μ)) (Measure.pi (fun _ : Fin q => μ)) :=
  ⟨(lip051_35_finite_coordinate_restriction_law μ b hb).1,
    (lip051_35_finite_coordinate_restriction_law μ b hb).2⟩

/-- Concatenating two injective blocks with disjoint ranges gives an injective selection. -/
lemma injective_append_LIP05135 {q₁ q₂ N : ℕ} {b₁ : Fin q₁ → Fin N} {b₂ : Fin q₂ → Fin N}
    (h₁ : Function.Injective b₁) (h₂ : Function.Injective b₂)
    (hd : Disjoint (Set.range b₁) (Set.range b₂)) :
    Function.Injective (Fin.append b₁ b₂ : Fin (q₁ + q₂) → Fin N) := by
  intro i j hij
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [Fin.append_left] at hij
      rw [h₁ hij]
    | right j =>
      simp only [Fin.append_left, Fin.append_right] at hij
      exact absurd ⟨j, hij.symm⟩ (Set.disjoint_left.mp hd ⟨i, rfl⟩)
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [Fin.append_left, Fin.append_right] at hij
      exact absurd ⟨i, hij⟩ (Set.disjoint_left.mp hd ⟨j, rfl⟩)
    | right j =>
      simp only [Fin.append_right] at hij
      rw [h₂ hij]

/-- Disjoint finite coordinate blocks combine into one restriction pushing `μ^N` to `μ^(q₁+q₂)`. -/
theorem lip051_35_finite_coordinate_restriction_law_append {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] {q₁ q₂ N : ℕ} (b₁ : Fin q₁ → Fin N)
    (b₂ : Fin q₂ → Fin N) (h₁ : Function.Injective b₁) (h₂ : Function.Injective b₂)
    (hd : Disjoint (Set.range b₁) (Set.range b₂)) :
    Function.Injective (Fin.append b₁ b₂ : Fin (q₁ + q₂) → Fin N) ∧
      Measure.map (restrictCoords_LIP05135 (E := E) (Fin.append b₁ b₂))
          (Measure.pi (fun _ : Fin N => μ))
        = Measure.pi (fun _ : Fin (q₁ + q₂) => μ) :=
  ⟨injective_append_LIP05135 h₁ h₂ hd,
    (lip051_35_finite_coordinate_restriction_law μ _ (injective_append_LIP05135 h₁ h₂ hd)).2⟩

end DGPS.Frontier.LIP051
