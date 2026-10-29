import DGPS.Foundations.RelativeEntropy
import DGPS.Measure.ConditionalDensities
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.Kernel.Composition.WithDensity


/-!
# Finite product entropy chain rule (FOU013)

INTERFACES/common_lemmas.md FOU013. In the FOU012 setting (`m = condMarginal Q p`,
`c = condDensity Q p`),
`H(p(P×Q) | P×Q) = H(mP | P) + ∫ H(c(x,·)Q | Q) d(mP)(x)` in `ℝ≥0∞`, and finiteness of the left
side gives finiteness of both terms and of a.e. conditional entropy.

Design choices (R5 note).
* Proof route: `relativeEntropy = klDiv` for probabilities (`relativeEntropy_eq_klDiv`), the
  Mathlib chain rule `InformationTheory.klDiv_compProd_eq_add` applied to the Markov kernel
  `x ↦ Q.withDensity (c(x,·))` (corrected to `1` off the mass-one fibers, a `mP`-null change,
  which also handles zero-marginal fibers), and a direct density computation for the conditional
  term. The conditional integral is an `ℝ≥0∞` lintegral over `mP`.
* `entropy_chain_rule_prod` is the two-factor form; `finite_product_entropy_chain_rule`
  (canonical output) conditions on the coordinates in an arbitrary subset `S` via FOU012's
  `splitEquiv`, transported by `relativeEntropy_map_equiv`. Ordered repeated conditioning is
  repeated application to the slice densities, which are mass-one densities on the finite
  product of the remaining coordinates (FOU012), exactly as in FOU012's iteration note.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace DGPS.Analysis

section Aux
variable {α : Type*} [MeasurableSpace α]

theorem relativeEntropy_eq_klDiv {ν P : Measure α} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure P] : relativeEntropy ν P = klDiv ν P := by
  by_cases h : ν ≪ P
  · rw [relativeEntropy_of_absolutelyContinuous h, klDiv_eq_lintegral_klFun_of_ac h,
      entropy_mass_one (by rw [Measure.integral_toReal_rnDeriv h]; simp)]
    refine lintegral_congr fun x => ?_
    rw [klFun_apply]
    congr 1
    ring
  · rw [relativeEntropy_of_not_absolutelyContinuous h, klDiv_of_not_ac h]

theorem relativeEntropy_withDensity_eq_lintegral {ρ : Measure α} [IsProbabilityMeasure ρ]
    {G : α → ℝ≥0∞} (hG : Measurable G) [IsProbabilityMeasure (ρ.withDensity G)] :
    relativeEntropy (ρ.withDensity G) ρ = ∫⁻ x, ENNReal.ofReal (klFun (G x).toReal) ∂ρ := by
  rw [relativeEntropy_eq_klDiv,
    klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous _ _)]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_withDensity ρ hG] with x hx
  rw [hx]

end Aux

section TwoFactor
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem entropy_chain_rule_core {P : Measure α} {Q : Measure β}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {m : α → ℝ≥0∞} {c : α × β → ℝ≥0∞}
    (hm : Measurable m) (hc : Measurable c) [IsProbabilityMeasure (P.withDensity m)]
    (hfib : ∀ᵐ x ∂(P.withDensity m), ∫⁻ y, c (x, y) ∂Q = 1) :
    relativeEntropy ((P.prod Q).withDensity fun z => m z.1 * c z) (P.prod Q)
      = relativeEntropy (P.withDensity m) P
        + ∫⁻ x, relativeEntropy (Q.withDensity fun y => c (x, y)) Q ∂(P.withDensity m) := by
  classical
  set μ := P.withDensity m with hμ
  let g : α → β → ℝ≥0∞ := fun x y => if ∫⁻ y, c (x, y) ∂Q = 1 then c (x, y) else 1
  have hI : Measurable fun z : α × β => ∫⁻ y, c (z.1, y) ∂Q :=
    hc.lintegral_prod_right'.comp measurable_fst
  have hg : Measurable (Function.uncurry g) :=
    Measurable.ite (hI (measurableSet_singleton 1)) hc measurable_const
  have hg1 : ∀ x, ∫⁻ y, g x y ∂Q = 1 := by
    intro x
    by_cases h : ∫⁻ y, c (x, y) ∂Q = 1
    · simp [g, h]
    · simp [g, h]
  let κ : Kernel α β := Kernel.withDensity (Kernel.const α Q) g
  have hκ : ∀ x, κ x = Q.withDensity (g x) := fun x => by
    simp [κ, Kernel.withDensity_apply _ hg]
  have : IsMarkovKernel κ :=
    ⟨fun x => ⟨by rw [hκ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hg1]⟩⟩
  -- a.e. identification of `g` with `c`
  have hae : ∀ᵐ x ∂P, m x ≠ 0 → ∫⁻ y, c (x, y) ∂Q = 1 := (ae_withDensity_iff hm).1 hfib
  have hmg : (fun z : α × β => m z.1 * g z.1 z.2) =ᵐ[P.prod Q] fun z => m z.1 * c z := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hae] with z hz
    by_cases h0 : m z.1 = 0
    · simp [h0]
    · simp [g, hz h0]
  have h1 : μ ⊗ₘ κ = (P.prod Q).withDensity fun z => m z.1 * c z := by
    have := Measure.withDensity_compProd_withDensity (μ := P) (κ := Kernel.const α Q) hm hg
    rw [Measure.compProd_const] at this
    rw [show μ ⊗ₘ κ = _ from this]
    exact withDensity_congr_ae hmg
  have : IsProbabilityMeasure ((P.prod Q).withDensity fun z => m z.1 * c z) := by
    rw [← h1]; infer_instance
  -- the chain rule
  have h2 : (P.prod Q) = P ⊗ₘ (Kernel.const α Q) := (Measure.compProd_const).symm
  have h3 := klDiv_compProd_eq_add μ P κ (Kernel.const α Q)
  rw [h1, ← h2] at h3
  -- second term
  have h4 : μ ⊗ₘ κ = (μ.prod Q).withDensity (fun z => g z.1 z.2) := by
    have := Measure.compProd_withDensity (μ := μ) (κ := Kernel.const α Q) hg
    rwa [Measure.compProd_const] at this
  have h5 : μ ⊗ₘ (Kernel.const α Q) = μ.prod Q := Measure.compProd_const
  rw [h5] at h3
  have h6 : klDiv ((P.prod Q).withDensity fun z => m z.1 * c z) (P.prod Q)
      = relativeEntropy ((P.prod Q).withDensity fun z => m z.1 * c z) (P.prod Q) :=
    relativeEntropy_eq_klDiv.symm
  rw [h6, ← relativeEntropy_eq_klDiv (ν := μ) (P := P)] at h3
  rw [h3]
  congr 1
  have hG : Measurable fun z : α × β => g z.1 z.2 := hg
  have hprob : IsProbabilityMeasure ((μ.prod Q).withDensity fun z => g z.1 z.2) := by
    rw [← h4]; infer_instance
  have hmeas : Measurable fun z : α × β => ENNReal.ofReal (klFun (g z.1 z.2).toReal) :=
    (measurable_klFun.comp hG.ennreal_toReal).ennreal_ofReal
  rw [← h1, h4, ← relativeEntropy_eq_klDiv, relativeEntropy_withDensity_eq_lintegral hG,
    lintegral_prod _ hmeas.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [hfib] with x hx
  have hgx : g x = fun y => c (x, y) := by
    funext y; simp [g, hx]
  have hcx : Measurable fun y => c (x, y) := hc.comp measurable_prodMk_left
  have : IsProbabilityMeasure (Q.withDensity fun y => c (x, y)) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hx]⟩
  rw [relativeEntropy_withDensity_eq_lintegral hcx, hgx]


/-- The fiber relative entropies are a.e. equal to a measurable function, hence a.e.-measurable. -/
theorem aemeasurable_fiberEntropy {P : Measure α} {Q : Measure β}
    [IsProbabilityMeasure Q] {m : α → ℝ≥0∞} {c : α × β → ℝ≥0∞} (hc : Measurable c)
    (hfib : ∀ᵐ x ∂(P.withDensity m), ∫⁻ y, c (x, y) ∂Q = 1) :
    AEMeasurable (fun x => relativeEntropy (Q.withDensity fun y => c (x, y)) Q)
      (P.withDensity m) := by
  have hmeas : Measurable fun z : α × β => ENNReal.ofReal (klFun (c z).toReal) :=
    (measurable_klFun.comp hc.ennreal_toReal).ennreal_ofReal
  refine ⟨fun x => ∫⁻ y, ENNReal.ofReal (klFun (c (x, y)).toReal) ∂Q,
    hmeas.lintegral_prod_right', ?_⟩
  filter_upwards [hfib] with x hx
  have hcx : Measurable fun y => c (x, y) := hc.comp measurable_prodMk_left
  have : IsProbabilityMeasure (Q.withDensity fun y => c (x, y)) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hx]⟩
  exact relativeEntropy_withDensity_eq_lintegral hcx

/-- FOU013, two-factor form. In the FOU012 setting, with `m = condMarginal Q p` and
`c = condDensity Q p`,
`H(p(P×Q) | P×Q) = H(mP | P) + ∫ H(c(x,·)Q | Q) d(mP)(x)` in `ℝ≥0∞`; if the left side is finite,
both right terms and a.e. conditional entropy are finite. -/
theorem entropy_chain_rule_prod {P : Measure α} {Q : Measure β}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {p : α × β → ℝ≥0∞}
    (hp : Measurable p) (hmass : ∫⁻ z, p z ∂P.prod Q = 1) :
    relativeEntropy ((P.prod Q).withDensity p) (P.prod Q)
      = relativeEntropy (P.withDensity (condMarginal Q p)) P
        + ∫⁻ x, relativeEntropy (Q.withDensity fun y => condDensity Q p (x, y)) Q
            ∂(P.withDensity (condMarginal Q p)) ∧
    (relativeEntropy ((P.prod Q).withDensity p) (P.prod Q) ≠ ∞ →
      relativeEntropy (P.withDensity (condMarginal Q p)) P ≠ ∞ ∧
      ∫⁻ x, relativeEntropy (Q.withDensity fun y => condDensity Q p (x, y)) Q
        ∂(P.withDensity (condMarginal Q p)) ≠ ∞ ∧
      ∀ᵐ x ∂(P.withDensity (condMarginal Q p)),
        relativeEntropy (Q.withDensity fun y => condDensity Q p (x, y)) Q ≠ ∞) := by
  obtain ⟨hm, hprob, hc, hae, hfib⟩ := conditional_densities_prod (P := P) (Q := Q) hp hmass
  have hcore := entropy_chain_rule_core (P := P) (Q := Q) hm hc hfib
  have hν : (P.prod Q).withDensity p
      = (P.prod Q).withDensity fun z => condMarginal Q p z.1 * condDensity Q p z :=
    withDensity_congr_ae hae
  rw [hν]
  refine ⟨hcore, fun h => ?_⟩
  rw [hcore] at h
  have h1 := (ENNReal.add_ne_top.1 h)
  refine ⟨h1.1, h1.2, ?_⟩
  exact ae_lt_top' (aemeasurable_fiberEntropy hc hfib) h1.2 |>.mono fun x hx => hx.ne

end TwoFactor

section FiniteProduct

variable {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : ∀ i, Measure (X i)) (S : ι → Prop) [DecidablePred S]

theorem relativeEntropy_map_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ν P : Measure α} [IsProbabilityMeasure ν] [IsProbabilityMeasure P] (e : α ≃ᵐ β) :
    relativeEntropy (ν.map e) (P.map e) = relativeEntropy ν P := by
  have : IsProbabilityMeasure (ν.map e) :=
    ⟨by rw [Measure.map_apply e.measurable MeasurableSet.univ]; simp⟩
  have : IsProbabilityMeasure (P.map e) :=
    ⟨by rw [Measure.map_apply e.measurable MeasurableSet.univ]; simp⟩
  rw [relativeEntropy_eq_klDiv, relativeEntropy_eq_klDiv]
  refine le_antisymm (klDiv_map_le ν P e.measurable) ?_
  have := klDiv_map_le (ν.map e) (P.map e) e.symm.measurable
  rwa [MeasurableEquiv.map_symm_map, MeasurableEquiv.map_symm_map] at this

/-- FOU013 (canonical output): the finite-product entropy chain rule, conditioning on the
coordinates in an arbitrary subset `S` (FOU012 splitting). The slice densities
`subsetCondDensity μ S p (x, ·)` are mass-one densities on the finite product of the remaining
coordinates, so the same theorem re-applies to them: ordered repeated conditioning is repeated
application. -/
theorem finite_product_entropy_chain_rule [∀ i, IsProbabilityMeasure (μ i)]
    {p : (∀ i, X i) → ℝ≥0∞} (hp : Measurable p) (hmass : ∫⁻ w, p w ∂Measure.pi μ = 1) :
    relativeEntropy ((Measure.pi μ).withDensity p) (Measure.pi μ)
      = relativeEntropy
          ((Measure.pi fun i : Subtype S => μ i).withDensity (subsetMarginal μ S p))
          (Measure.pi fun i : Subtype S => μ i)
        + ∫⁻ x, relativeEntropy
            ((Measure.pi fun i : {i // ¬S i} => μ i).withDensity
              fun y => subsetCondDensity μ S p (x, y))
            (Measure.pi fun i : {i // ¬S i} => μ i)
          ∂((Measure.pi fun i : Subtype S => μ i).withDensity (subsetMarginal μ S p)) ∧
    (relativeEntropy ((Measure.pi μ).withDensity p) (Measure.pi μ) ≠ ∞ →
      relativeEntropy
          ((Measure.pi fun i : Subtype S => μ i).withDensity (subsetMarginal μ S p))
          (Measure.pi fun i : Subtype S => μ i) ≠ ∞ ∧
      ∫⁻ x, relativeEntropy
            ((Measure.pi fun i : {i // ¬S i} => μ i).withDensity
              fun y => subsetCondDensity μ S p (x, y))
            (Measure.pi fun i : {i // ¬S i} => μ i)
          ∂((Measure.pi fun i : Subtype S => μ i).withDensity (subsetMarginal μ S p)) ≠ ∞ ∧
      ∀ᵐ x ∂((Measure.pi fun i : Subtype S => μ i).withDensity (subsetMarginal μ S p)),
        relativeEntropy
            ((Measure.pi fun i : {i // ¬S i} => μ i).withDensity
              fun y => subsetCondDensity μ S p (x, y))
            (Measure.pi fun i : {i // ¬S i} => μ i) ≠ ∞) := by
  have hpres := measurePreserving_piEquivPiSubtypeProd μ S
  have hq : Measurable (p ∘ (splitEquiv S).symm) := hp.comp (splitEquiv S).symm.measurable
  have hq1 : ∫⁻ z, (p ∘ (splitEquiv S).symm) z
      ∂(Measure.pi fun i : Subtype S => μ i).prod (Measure.pi fun i : {i // ¬S i} => μ i) = 1 := by
    rw [← hpres.lintegral_comp_emb (splitEquiv S).measurableEmbedding]
    simpa using hmass
  have key := entropy_chain_rule_prod hq hq1
  have hmap : ((Measure.pi μ).withDensity p).map (splitEquiv S)
      = ((Measure.pi fun i : Subtype S => μ i).prod
          (Measure.pi fun i : {i // ¬S i} => μ i)).withDensity (p ∘ (splitEquiv S).symm) := by
    ext s hs
    rw [Measure.map_apply (splitEquiv S).measurable hs, withDensity_apply _ (hs.preimage
      (splitEquiv S).measurable), withDensity_apply _ hs]
    have := hpres.setLIntegral_comp_preimage_emb (splitEquiv S).measurableEmbedding
      (p ∘ (splitEquiv S).symm) s
    simpa using this
  have hLHS : relativeEntropy ((Measure.pi μ).withDensity p) (Measure.pi μ)
      = relativeEntropy
        (((Measure.pi fun i : Subtype S => μ i).prod
          (Measure.pi fun i : {i // ¬S i} => μ i)).withDensity (p ∘ (splitEquiv S).symm))
        ((Measure.pi fun i : Subtype S => μ i).prod
          (Measure.pi fun i : {i // ¬S i} => μ i)) := by
    have : IsProbabilityMeasure ((Measure.pi μ).withDensity p) :=
      ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact hmass⟩
    rw [← hmap, ← hpres.map_eq]
    exact (relativeEntropy_map_equiv (splitEquiv S)).symm
  rw [hLHS]
  exact key

end FiniteProduct

end DGPS.Analysis
