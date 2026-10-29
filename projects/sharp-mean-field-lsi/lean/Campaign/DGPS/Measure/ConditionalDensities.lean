import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Conditional densities on finite products (FOU012)

INTERFACES/common_lemmas.md FOU012. For probabilities `P, Q` and a nonnegative measurable
`p` with `∫ p d(P×Q) = 1`, put `m x = ∫ p(x,y) dQ(y)` and `c(x,y) = p(x,y)/m x` when `m x > 0`,
`c = 1` on the zero-marginal branch. Then `m` is a density (`P.withDensity m` is a probability
measure), `p = m·c` a.e., and `c(x,·)` is a probability density for `mP`-a.e. `x`.

Design choices (R5 note).
* Densities are `ℝ≥0∞`-valued (the standard form for `withDensity`/`lintegral`); `p` nonnegative
  measurable with `∫⁻ p = 1` is exactly the contract's hypothesis.
* `conditional_densities_prod` is the two-factor theorem. The finite-product statement
  `conditional_densities_on_finite_products` splits `∀ i, X i` along an arbitrary subset `S`
  of the (finite) index type as `(coords in S) × (rest)` through
  `MeasurableEquiv.piEquivPiSubtypeProd`, which is measure preserving for `Measure.pi`. The
  rest is again a finite product of probability spaces and each slice `c(x,·)` is a measurable
  mass-one density on it, so the same theorem re-applies to the slice: iterating over an ordered
  tuple of distinct labels is repeated application.
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS.Analysis

section TwoFactor

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The marginal density `m x = ∫ p(x,y) dQ(y)`. -/
noncomputable def condMarginal (Q : Measure β) (p : α × β → ℝ≥0∞) (x : α) : ℝ≥0∞ :=
  ∫⁻ y, p (x, y) ∂Q

/-- The conditional density `c = p/m` on `m > 0`, and `c = 1` on the zero-marginal branch. -/
noncomputable def condDensity (Q : Measure β) (p : α × β → ℝ≥0∞) (z : α × β) : ℝ≥0∞ :=
  if condMarginal Q p z.1 = 0 then 1 else p z / condMarginal Q p z.1

theorem measurable_condMarginal {Q : Measure β} [SFinite Q] {p : α × β → ℝ≥0∞}
    (hp : Measurable p) : Measurable (condMarginal Q p) :=
  hp.lintegral_prod_right'

theorem lintegral_condMarginal {P : Measure α} {Q : Measure β} [SFinite P] [SFinite Q]
    {p : α × β → ℝ≥0∞} (hp : Measurable p) :
    ∫⁻ x, condMarginal Q p x ∂P = ∫⁻ z, p z ∂P.prod Q :=
  (lintegral_prod _ hp.aemeasurable).symm

theorem measurable_condDensity {Q : Measure β} [SFinite Q] {p : α × β → ℝ≥0∞}
    (hp : Measurable p) : Measurable (condDensity Q p) := by
  have hm : Measurable fun z : α × β => condMarginal Q p z.1 :=
    (measurable_condMarginal (Q := Q) hp).comp measurable_fst
  refine Measurable.ite (hm (measurableSet_singleton 0)) measurable_const ?_
  exact hp.div hm

/-- FOU012, two-factor form. -/
theorem conditional_densities_prod {P : Measure α} {Q : Measure β}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {p : α × β → ℝ≥0∞}
    (hp : Measurable p) (hmass : ∫⁻ z, p z ∂P.prod Q = 1) :
    Measurable (condMarginal Q p) ∧
    IsProbabilityMeasure (P.withDensity (condMarginal Q p)) ∧
    Measurable (condDensity Q p) ∧
    (p =ᵐ[P.prod Q] fun z => condMarginal Q p z.1 * condDensity Q p z) ∧
    (∀ᵐ x ∂(P.withDensity (condMarginal Q p)), ∫⁻ y, condDensity Q p (x, y) ∂Q = 1) := by
  have hm : Measurable (condMarginal Q p) := measurable_condMarginal hp
  have hmP : ∫⁻ x, condMarginal Q p x ∂P = 1 := by rw [lintegral_condMarginal hp, hmass]
  have hfin : ∀ᵐ x ∂P, condMarginal Q p x ≠ ∞ := by
    have := ae_lt_top hm (by rw [hmP]; exact ENNReal.one_ne_top)
    filter_upwards [this] with x hx using hx.ne
  refine ⟨hm, ⟨?_⟩, measurable_condDensity hp, ?_, ?_⟩
  · rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hmP]
  · rw [Filter.EventuallyEq, Measure.ae_prod_iff_ae_ae]
    · filter_upwards [hfin] with x hx
      by_cases h0 : condMarginal Q p x = 0
      · have : ∀ᵐ y ∂Q, p (x, y) = 0 :=
          (lintegral_eq_zero_iff (hp.comp measurable_prodMk_left)).1 h0
        filter_upwards [this] with y hy
        simp [condDensity, h0, hy]
      · filter_upwards with y
        simp only [condDensity, h0, ite_false]
        exact (ENNReal.mul_div_cancel h0 hx).symm
    · exact measurableSet_eq_fun hp
        (((hm.comp measurable_fst : Measurable fun z : α × β => condMarginal Q p z.1)).mul
          (measurable_condDensity hp))
  · rw [ae_withDensity_iff hm]
    filter_upwards [hfin] with x hx h0
    have : ∀ y, condDensity Q p (x, y) = p (x, y) * (condMarginal Q p x)⁻¹ := by
      intro y; simp [condDensity, h0, div_eq_mul_inv]
    simp_rw [this]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 h0)]
    exact ENNReal.mul_inv_cancel h0 hx

end TwoFactor

section FiniteProduct

variable {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : ∀ i, Measure (X i)) (S : ι → Prop) [DecidablePred S]

/-- The measurable splitting `(∀ i, X i) ≃ᵐ (coords in S) × (rest)`. -/
abbrev splitEquiv : (∀ i, X i) ≃ᵐ (∀ i : Subtype S, X i) × ∀ i : {i // ¬S i}, X i :=
  MeasurableEquiv.piEquivPiSubtypeProd X S

/-- The marginal density of the `S`-coordinates. -/
noncomputable def subsetMarginal (p : (∀ i, X i) → ℝ≥0∞) :
    (∀ i : Subtype S, X i) → ℝ≥0∞ :=
  condMarginal (Measure.pi fun i : {i // ¬S i} => μ i) (p ∘ (splitEquiv S).symm)

/-- The conditional density of the rest given the `S`-coordinates. -/
noncomputable def subsetCondDensity (p : (∀ i, X i) → ℝ≥0∞) :
    (∀ i : Subtype S, X i) × (∀ i : {i // ¬S i}, X i) → ℝ≥0∞ :=
  condDensity (Measure.pi fun i : {i // ¬S i} => μ i) (p ∘ (splitEquiv S).symm)

/-- FOU012 (canonical output): conditional densities on a finite product, conditioning on
the coordinates in an arbitrary subset `S`. -/
theorem conditional_densities_on_finite_products [∀ i, IsProbabilityMeasure (μ i)]
    {p : (∀ i, X i) → ℝ≥0∞} (hp : Measurable p) (hmass : ∫⁻ w, p w ∂Measure.pi μ = 1) :
    Measurable (subsetMarginal μ S p) ∧
    IsProbabilityMeasure
      ((Measure.pi fun i : Subtype S => μ i).withDensity (subsetMarginal μ S p)) ∧
    Measurable (subsetCondDensity μ S p) ∧
    (p =ᵐ[Measure.pi μ] fun w =>
      subsetMarginal μ S p (splitEquiv S w).1 * subsetCondDensity μ S p (splitEquiv S w)) ∧
    (∀ᵐ x ∂((Measure.pi fun i : Subtype S => μ i).withDensity (subsetMarginal μ S p)),
      Measurable (fun y => subsetCondDensity μ S p (x, y)) ∧
      ∫⁻ y, subsetCondDensity μ S p (x, y) ∂(Measure.pi fun i : {i // ¬S i} => μ i) = 1) := by
  have hpres := measurePreserving_piEquivPiSubtypeProd μ S
  have hq : Measurable (p ∘ (splitEquiv S).symm) := hp.comp (splitEquiv S).symm.measurable
  have hq1 : ∫⁻ z, (p ∘ (splitEquiv S).symm) z
      ∂(Measure.pi fun i : Subtype S => μ i).prod (Measure.pi fun i : {i // ¬S i} => μ i) = 1 := by
    rw [← hpres.lintegral_comp_emb (splitEquiv S).measurableEmbedding]
    simpa using hmass
  obtain ⟨h1, h2, h3, h4, h5⟩ := conditional_densities_prod hq hq1
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · have := hpres.quasiMeasurePreserving.ae_eq_comp h4
    refine this.mono fun w hw => ?_
    have e1 : ((p ∘ (splitEquiv S).symm) ∘ splitEquiv S) w = p w := by simp
    exact e1.symm.trans hw
  · filter_upwards [h5] with x hx
    exact ⟨h3.comp measurable_prodMk_left, hx⟩

end FiniteProduct

end DGPS.Analysis
