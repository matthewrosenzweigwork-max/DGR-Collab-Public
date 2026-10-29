import LeanResearch.PeriodicAttractiveLogGas.ConditionalLawEstimates
import LeanResearch.PeriodicAttractiveLogGas.ConditionalKernelL2

/-! Bridge from the actual disintegration in Proposition 3.4
to the coordinate kernels in Lemma 3.7. The source domains are genuine
products of measurable cell subtypes. Their influence suprema therefore
do not include configurations outside the prescribed patches. The
retractions below construct the subtype laws; they are identities on the
actual domains, and the conditional laws are identified there explicitly.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace PeriodicAttractiveLogGas.CoordinateConditionalKernels

open CoordinateOscillation ConditionalL2Projections ConditionalKernelL2
open OneCoordinateConditionals MeshCells MeshAdjacentCells CellRestrictions
open GreenPointWeights LabelOccupations ConditionalParameters
open NormalizedExponentialInterpolation TotalVariationOscillation

section GeneralKernels

variable {ι : Type*} {E : ι → Type*} [DecidableEq ι]
variable [∀ i, MeasurableSpace (E i)]

/-- An outside-coordinate kernel composed with the actual omission map. -/
def outsideLift (q : ∀ i, Kernel (∀ j : {j : ι // j ≠ i}, E j) (E i))
    (i : ι) : Kernel (∀ k, E k) (E i) :=
  (q i).comap (omitCoordinate E i) (measurable_omitCoordinate E i)

instance isMarkovKernel_outsideLift
    (q : ∀ i, Kernel (∀ j : {j : ι // j ≠ i}, E j) (E i))
    [∀ i, IsMarkovKernel (q i)] (i : ι) : IsMarkovKernel (outsideLift q i) := by
  unfold outsideLift
  infer_instance

omit [DecidableEq ι] in
theorem independentSite_outsideLift
    (q : ∀ i, Kernel (∀ j : {j : ι // j ≠ i}, E j) (E i)) :
    IndependentSite (outsideLift q) := by
  intro i x y hxy
  change q i (omitCoordinate E i x) = q i (omitCoordinate E i y)
  congr 1
  funext j
  exact hxy j j.property

variable (κ : ∀ i, Kernel (∀ k, E k) (E i)) [∀ i, IsMarkovKernel (κ i)]

theorem lintegral_resample (μ : Measure (∀ k, E k)) [SFinite μ]
    (hstat : PreservesLaw κ μ) (i : ι) {F : (∀ k, E k) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x, ∫⁻ z, F (Function.update x i z) ∂κ i x ∂μ) = ∫⁻ x, F x ∂μ := by
  calc
    _ = ∫⁻ p : (∀ k, E k) × E i, F (Function.update p.1 i p.2) ∂(μ ⊗ₘ κ i) :=
      (Measure.lintegral_compProd (hF.comp measurable_update')).symm
    _ = ∫⁻ x, F x ∂Measure.map
        (fun p : (∀ k, E k) × E i ↦ Function.update p.1 i p.2) (μ ⊗ₘ κ i) :=
      (lintegral_map hF measurable_update').symm
    _ = _ := by rw [hstat i]

/-- The measure identity follows by testing against nonnegative measurable
functions; it is not an operator or variance hypothesis. -/
theorem preservesLaw_of_lintegral (μ : Measure (∀ k, E k)) [SFinite μ]
    (h : ∀ i, ∀ F : (∀ k, E k) → ℝ≥0∞, Measurable F →
      (∫⁻ x, ∫⁻ z, F (Function.update x i z) ∂κ i x ∂μ) = ∫⁻ x, F x ∂μ) :
    PreservesLaw κ μ := by
  intro i
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF measurable_update']
  rw [Measure.lintegral_compProd (show Measurable
    (fun p : (∀ k, E k) × E i ↦ F (Function.update p.1 i p.2)) from
      hF.comp measurable_update')]
  exact h i F hF

end GeneralKernels

section FiniteConfiguration

variable {n : ℕ}

/-- The finite-index deletion is precisely omission followed by its
increasing enumeration; it keeps the original particle labels. -/
theorem removeSite_apply_eq_omitCoordinate (i : Fin (n + 1))
    (X : Configuration (n + 1)) (j : Fin n) :
    removeSite i X j = omitCoordinate (fun _ : Fin (n + 1) ↦ Torus) i X
      ⟨i.succAbove j, Fin.succAbove_ne i j⟩ := rfl

theorem removeSite_sameExcept {i : Fin (n + 1)} {X Y : Configuration (n + 1)}
    (h : SameExcept i X Y) : removeSite i X = removeSite i Y := by
  funext j
  exact h (i.succAbove j) (Fin.succAbove_ne i j)

theorem insertSite_eq_update (i : Fin (n + 1)) (X : Configuration (n + 1)) (z : Torus) :
    insertSite i z (removeSite i X) = Function.update X i z := by
  funext k
  by_cases hki : k = i
  · subst k
    simp only [insertSite_self, Function.update_self]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hki
    simp only [insertSite_succAbove, removeSite,
      Function.update_of_ne (Fin.succAbove_ne i j)]

def finLift (q : Fin (n + 1) → Kernel (Configuration n) Torus) (i : Fin (n + 1)) :
    Kernel (Configuration (n + 1)) Torus :=
  (q i).comap (removeSite i) (measurable_removeSite i)

instance isMarkovKernel_finLift (q : Fin (n + 1) → Kernel (Configuration n) Torus)
    [∀ i, IsMarkovKernel (q i)] (i : Fin (n + 1)) : IsMarkovKernel (finLift q i) := by
  unfold finLift
  infer_instance

theorem independentSite_finLift (q : Fin (n + 1) → Kernel (Configuration n) Torus) :
    IndependentSite (finLift q) := by
  intro i X Y hXY
  change q i (removeSite i X) = q i (removeSite i Y)
  rw [removeSite_sameExcept hXY]

/-- The existing disintegration, with its actual outside marginal,
implies resampling invariance on the full ambient configuration space. -/
theorem preservesLaw_finLift (q : Fin (n + 1) → Kernel (Configuration n) Torus)
    [∀ i, IsMarkovKernel (q i)] (P : Measure (Configuration (n + 1))) [SFinite P]
    (hdis : ∀ i, ∀ F : Configuration (n + 1) → ℝ≥0∞, Measurable F →
      (∫⁻ X, F X ∂P) = ∫⁻ Y, ∫⁻ z, F (insertSite i z Y) ∂q i Y
        ∂Measure.map (removeSite i) P) : PreservesLaw (finLift q) P := by
  apply preservesLaw_of_lintegral
  intro i F hF
  have hinner : Measurable (fun Y : Configuration n ↦
      ∫⁻ z, F (insertSite i z Y) ∂q i Y) :=
    (hF.comp ((measurable_insertSite i).comp measurable_swap)).lintegral_kernel_prod_right'
  change (∫⁻ X, ∫⁻ z, F (Function.update X i z) ∂q i (removeSite i X) ∂P) = _
  calc
    _ = ∫⁻ X, ∫⁻ z, F (insertSite i z (removeSite i X)) ∂q i (removeSite i X) ∂P := by
      simp_rw [insertSite_eq_update]
    _ = ∫⁻ Y, ∫⁻ z, F (insertSite i z Y) ∂q i Y ∂Measure.map (removeSite i) P :=
      (lintegral_map hinner (measurable_removeSite i)).symm
    _ = _ := (hdis i F hF).symm

def gibbsKernel (μ : Fin (n + 1) → Measure Torus) [∀ j, SFinite (μ j)] (β : ℝ) :
    Fin (n + 1) → Kernel (Configuration (n + 1)) Torus :=
  finLift fun i ↦ conditionalKernel (μ i) i β

instance isMarkovKernel_gibbsKernel (μ : Fin (n + 1) → Measure Torus)
    [∀ j, SFinite (μ j)] [∀ j, NeZero (μ j)] (β : ℝ) (i : Fin (n + 1)) :
    IsMarkovKernel (gibbsKernel μ β i) := by
  unfold gibbsKernel
  infer_instance

theorem independentSite_gibbsKernel (μ : Fin (n + 1) → Measure Torus)
    [∀ j, SFinite (μ j)] (β : ℝ) : IndependentSite (gibbsKernel μ β) :=
  independentSite_finLift _

theorem productNormalizer_ne_zero (μ : Fin (n + 1) → Measure Torus)
    [∀ j, IsProbabilityMeasure (μ j)] (β : ℝ) : productNormalizer μ β ≠ 0 := by
  intro h
  have hae := (lintegral_eq_zero_iff (measurable_jointDensity (n + 1) β)).mp h
  obtain ⟨X, hX⟩ := hae.exists
  exact (jointDensity_pos (n + 1) β X).ne' hX

theorem productGibbs_probability (μ : Fin (n + 1) → Measure Torus)
    [∀ j, IsProbabilityMeasure (μ j)] (β : ℝ) (hfin : productNormalizer μ β ≠ ⊤) :
    IsProbabilityMeasure (productGibbs μ β) := by
  constructor
  rw [productGibbs, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel (productNormalizer_ne_zero μ β) hfin

theorem preservesLaw_gibbsKernel (μ : Fin (n + 1) → Measure Torus)
    [∀ j, IsProbabilityMeasure (μ j)] (β : ℝ) (hfin : productNormalizer μ β ≠ ⊤) :
    PreservesLaw (gibbsKernel μ β) (productGibbs μ β) := by
  let hprob : IsProbabilityMeasure (productGibbs μ β) := productGibbs_probability μ β hfin
  apply preservesLaw_finLift
  intro i F hF
  exact lintegral_disintegrate μ i β hfin hF

end FiniteConfiguration

section ProductDomains

variable {ι : Type*} {E : ι → Type*} [DecidableEq ι]
variable [∀ i, MeasurableSpace (E i)]
variable (D : ∀ i, Set (E i)) (hD : ∀ i, MeasurableSet (D i)) (p : ∀ i, D i)

def domainInclusion (X : ∀ i, D i) (i : ι) : E i := X i

def subtypeRetraction {A : Type*} (s : Set A) (a : s) (x : A) : s := by
  classical
  exact if hx : x ∈ s then ⟨x, hx⟩ else a

theorem measurable_subtypeRetraction {A : Type*} [MeasurableSpace A]
    (s : Set A) (hs : MeasurableSet s) (a : s) : Measurable (subtypeRetraction s a) := by
  classical
  exact (measurable_id : Measurable (fun x : s ↦ x)).dite
    (measurable_const (a := a) : Measurable (fun _ : ↥(sᶜ) ↦ a)) hs

@[simp] theorem subtypeRetraction_coe {A : Type*} (s : Set A) (a x : s) :
    subtypeRetraction s a (x : A) = x := by
  classical
  simp only [subtypeRetraction, dite_eq_left x.property]

theorem coe_subtypeRetraction_of_mem {A : Type*} (s : Set A) (a : s) {x : A}
    (hx : x ∈ s) : (subtypeRetraction s a x : A) = x := by
  classical
  simp only [subtypeRetraction, dite_eq_left hx]

def domainRetraction (X : ∀ i, E i) (i : ι) : D i := subtypeRetraction (D i) (p i) (X i)

omit [DecidableEq ι] in
theorem measurable_domainInclusion : Measurable (domainInclusion D) :=
  measurable_pi_iff.mpr fun i ↦ measurable_subtype_coe.comp (measurable_pi_apply i)

include hD in
omit [DecidableEq ι] in
theorem measurable_domainRetraction : Measurable (domainRetraction D p) :=
  measurable_pi_iff.mpr fun i ↦
    (measurable_subtypeRetraction (D i) (hD i) (p i)).comp (measurable_pi_apply i)

omit [DecidableEq ι] [∀ i, MeasurableSpace (E i)] in
@[simp] theorem domainRetraction_inclusion (X : ∀ i, D i) :
    domainRetraction D p (domainInclusion D X) = X := by
  funext i
  exact subtypeRetraction_coe (D i) (p i) (X i)

omit [DecidableEq ι] [∀ i, MeasurableSpace (E i)] in
theorem domainInclusion_retraction_of_mem {X : ∀ i, E i} (hX : ∀ i, X i ∈ D i) :
    domainInclusion D (domainRetraction D p X) = X := by
  funext i
  exact coe_subtypeRetraction_of_mem (D i) (p i) (hX i)

omit [∀ i, MeasurableSpace (E i)] in
theorem domainInclusion_update (X : ∀ k, D k) (i : ι) (z : D i) :
    domainInclusion D (Function.update X i z) = Function.update (domainInclusion D X) i z := by
  funext k
  by_cases hki : k = i
  · subst k
    simp only [domainInclusion, Function.update_self]
  · simp only [domainInclusion, Function.update_of_ne hki]

omit [∀ i, MeasurableSpace (E i)] in
theorem domainRetraction_update (X : ∀ k, E k) (i : ι) (z : E i) :
    domainRetraction D p (Function.update X i z) =
      Function.update (domainRetraction D p X) i (subtypeRetraction (D i) (p i) z) := by
  funext k
  by_cases hki : k = i
  · subst k
    simp only [domainRetraction, Function.update_self]
  · simp only [domainRetraction, Function.update_of_ne hki]

omit [DecidableEq ι] [∀ i, MeasurableSpace (E i)] in
theorem domainInclusion_sameExcept {i : ι} {X Y : ∀ k, D k} (h : SameExcept i X Y) :
    SameExcept i (domainInclusion D X) (domainInclusion D Y) := by
  intro k hki
  exact congrArg Subtype.val (h k hki)

def domainMeasure (μ : Measure (∀ k, E k)) : Measure (∀ k, D k) :=
  Measure.map (domainRetraction D p) μ

instance isProbabilityMeasure_domainMeasure (μ : Measure (∀ k, E k)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (domainMeasure D p μ) := by
  unfold domainMeasure
  infer_instance

include hD in
omit [DecidableEq ι] in
theorem map_domainInclusion_domainMeasure (μ : Measure (∀ k, E k))
    (hμ : ∀ᵐ X ∂μ, ∀ i, X i ∈ D i) :
    Measure.map (domainInclusion D) (domainMeasure D p μ) = μ := by
  rw [domainMeasure, Measure.map_map (measurable_domainInclusion D)
    (measurable_domainRetraction D hD p)]
  have hae : (domainInclusion D ∘ domainRetraction D p) =ᵐ[μ] id :=
    hμ.mono fun X hX ↦ domainInclusion_retraction_of_mem D p hX
  rw [Measure.map_congr hae, Measure.map_id]

variable (κ : ∀ i, Kernel (∀ k, E k) (E i)) [∀ i, IsMarkovKernel (κ i)]

def domainKernel (i : ι) : Kernel (∀ k, D k) (D i) :=
  ((κ i).comap (domainInclusion D) (measurable_domainInclusion D)).mapOfMeasurable
    (subtypeRetraction (D i) (p i)) (measurable_subtypeRetraction (D i) (hD i) (p i))

instance isMarkovKernel_domainKernel (i : ι) : IsMarkovKernel (domainKernel D hD p κ i) := by
  unfold domainKernel
  rw [Kernel.mapOfMeasurable_eq_map]
  exact Kernel.IsMarkovKernel.map _ (measurable_subtypeRetraction (D i) (hD i) (p i))

omit [DecidableEq ι] [∀ i, IsMarkovKernel (κ i)] in
theorem domainKernel_apply (i : ι) (X : ∀ k, D k) :
    domainKernel D hD p κ i X =
      Measure.map (subtypeRetraction (D i) (p i)) (κ i (domainInclusion D X)) := by
  rw [domainKernel, Kernel.mapOfMeasurable_eq_map,
    Kernel.map_apply _ (measurable_subtypeRetraction (D i) (hD i) (p i)),
    Kernel.comap_apply]

omit [DecidableEq ι] [∀ i, IsMarkovKernel (κ i)] in
theorem independentSite_domainKernel (hind : IndependentSite κ) :
    IndependentSite (domainKernel D hD p κ) := by
  intro i X Y hXY
  rw [domainKernel_apply D hD p κ, domainKernel_apply D hD p κ,
    hind i _ _ (domainInclusion_sameExcept D hXY)]

/-- Transport of actual resampling invariance to a product of measurable
subsets. Concentration is a genuine measure statement, not a cap holding
only almost everywhere in an unrestricted influence supremum. -/
theorem preservesLaw_domainKernel (μ : Measure (∀ k, E k)) [IsProbabilityMeasure μ]
    (hstat : PreservesLaw κ μ) (hμ : ∀ᵐ X ∂μ, ∀ i, X i ∈ D i) :
    PreservesLaw (domainKernel D hD p κ) (domainMeasure D p μ) := by
  apply preservesLaw_of_lintegral
  intro i F hF
  have hinner : Measurable (fun X : (∀ k, D k) ↦
      ∫⁻ z, F (Function.update X i z) ∂domainKernel D hD p κ i X) :=
    (hF.comp measurable_update').lintegral_kernel_prod_right'
  have hFR : Measurable (fun X ↦ F (domainRetraction D p X)) :=
    hF.comp (measurable_domainRetraction D hD p)
  change (∫⁻ X, ∫⁻ z, F (Function.update X i z) ∂domainKernel D hD p κ i X
      ∂Measure.map (domainRetraction D p) μ) = ∫⁻ X, F X ∂Measure.map (domainRetraction D p) μ
  rw [lintegral_map hinner (measurable_domainRetraction D hD p),
    lintegral_map hF (measurable_domainRetraction D hD p)]
  calc
    _ = ∫⁻ X, ∫⁻ z, F (domainRetraction D p (Function.update X i z)) ∂κ i X ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hμ] with X hX
      rw [domainKernel_apply D hD p κ,
        domainInclusion_retraction_of_mem D p hX,
        lintegral_map (show Measurable
          (fun z : D i ↦ F (Function.update (domainRetraction D p X) i z)) from
            hF.comp (measurable_update (domainRetraction D p X) (a := i)))
          (measurable_subtypeRetraction (D i) (hD i) (p i))]
      apply lintegral_congr
      intro z
      rw [domainRetraction_update]
    _ = _ := lintegral_resample κ μ hstat i hFR

omit [DecidableEq ι] [∀ i, IsMarkovKernel (κ i)] in
/-- On a legitimate placement with a supported ambient conditional law,
the subtype construction has exactly that law as its pushforward. -/
theorem map_val_domainKernel (i : ι) (X : ∀ k, D k)
    (hs : ∀ᵐ z ∂κ i (domainInclusion D X), z ∈ D i) :
    Measure.map (Subtype.val : D i → E i) (domainKernel D hD p κ i X) =
      κ i (domainInclusion D X) := by
  rw [domainKernel_apply D hD p κ, Measure.map_map measurable_subtype_coe
    (measurable_subtypeRetraction (D i) (hD i) (p i))]
  have hae : ((Subtype.val : D i → E i) ∘ subtypeRetraction (D i) (p i))
      =ᵐ[κ i (domainInclusion D X)] id :=
    hs.mono fun z hz ↦ coe_subtypeRetraction_of_mem (D i) (p i) hz
  rw [Measure.map_congr hae, Measure.map_id]

end ProductDomains

section InfluenceDomains

/-- Pushforward cannot increase the source convention of total variation. -/
theorem setTV_map_le {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : A → B} (hf : Measurable f) :
    setTotalVariation (Measure.map f μ) (Measure.map f ν) ≤ setTotalVariation μ ν := by
  have hb : BddAbove ((fun s : Set A ↦ |(μ s).toReal - (ν s).toReal|) ''
      {s | MeasurableSet s}) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨s, _, rfl⟩
    have hm : (μ s).toReal ≤ 1 := measureReal_le_one
    have hn : (ν s).toReal ≤ 1 := measureReal_le_one
    exact abs_le.mpr ⟨by linarith [ENNReal.toReal_nonneg (a := μ s)],
      by linarith [ENNReal.toReal_nonneg (a := ν s)]⟩
  apply csSup_le
  · exact ⟨_, ∅, MeasurableSet.empty, rfl⟩
  · rintro _ ⟨s, hs, rfl⟩
    change |((Measure.map f μ) s).toReal - ((Measure.map f ν) s).toReal| ≤ _
    rw [Measure.map_apply hf hs, Measure.map_apply hf hs]
    exact le_csSup hb ⟨f ⁻¹' s, hf hs, rfl⟩

variable {ι : Type*} {E : ι → Type*} [DecidableEq ι]
variable [∀ i, MeasurableSpace (E i)]
variable (D : ∀ i, Set (E i)) (hD : ∀ i, MeasurableSet (D i)) (p : ∀ i, D i)
variable (κ : ∀ i, Kernel (∀ k, E k) (E i)) [∀ i, IsMarkovKernel (κ i)]

omit [DecidableEq ι] in
/-- Under the actual support property, subtype transport preserves the
total-variation distance exactly; there is no normalization factor. -/
theorem setTV_domainKernel_eq (i : ι) (X Y : ∀ k, D k)
    (hX : ∀ᵐ z ∂κ i (domainInclusion D X), z ∈ D i)
    (hY : ∀ᵐ z ∂κ i (domainInclusion D Y), z ∈ D i) :
    setTotalVariation (domainKernel D hD p κ i X) (domainKernel D hD p κ i Y) =
      setTotalVariation (κ i (domainInclusion D X)) (κ i (domainInclusion D Y)) := by
  apply le_antisymm
  · rw [domainKernel_apply D hD p κ, domainKernel_apply D hD p κ]
    exact setTV_map_le _ _ (measurable_subtypeRetraction (D i) (hD i) (p i))
  · rw [← map_val_domainKernel D hD p κ i X hX,
      ← map_val_domainKernel D hD p κ i Y hY]
    exact setTV_map_le _ _ measurable_subtype_coe

omit [DecidableEq ι] in
/-- An influence bound is needed only for ambient configurations in the
actual product domains, because the resulting supremum is on those subtypes. -/
theorem influence_domainKernel_le (i j : ι) {C : ℝ}
    (h : ∀ X Y : (∀ k, E k), (∀ k, X k ∈ D k) → (∀ k, Y k ∈ D k) →
      SameExcept j X Y → setTotalVariation (κ i X) (κ i Y) ≤ C) :
    influence (domainKernel D hD p κ) i j ≤ C := by
  apply csSup_le
  · exact ⟨_, p, p, sameExcept_refl j p, rfl⟩
  · rintro _ ⟨X, Y, hXY, rfl⟩
    rw [domainKernel_apply D hD p κ, domainKernel_apply D hD p κ]
    exact (setTV_map_le _ _ (measurable_subtypeRetraction (D i) (hD i) (p i))).trans
      (h _ _ (fun k ↦ (X k).property) (fun k ↦ (Y k).property)
        (domainInclusion_sameExcept D hXY))

end InfluenceDomains

section SourcePatches

variable {n J : ℕ}

/-- The actual half-open product, including the prescribed boundary labels. -/
abbrev PatchCoordinates {N : ℕ} (hJ : 0 < J) (a : Fin N → MeshIndex J) (b : Fin N → Patch) :=
  ∀ i, patchDomain J hJ (a i) (b i)

def patchPoint (hJ : 0 < J) (hJ2 : 2 ≤ J) (a : MeshIndex J) (b : Patch) :
    patchDomain J hJ a b :=
  ⟨Classical.choose (ae_mem_patchDomain J hJ hJ2 a b).exists,
    Classical.choose_spec (ae_mem_patchDomain J hJ hJ2 a b).exists⟩

def patchInclusion {N : ℕ} (hJ : 0 < J) (a : Fin N → MeshIndex J) (b : Fin N → Patch) :
    PatchCoordinates hJ a b → Configuration N :=
  domainInclusion fun i ↦ patchDomain J hJ (a i) (b i)

theorem measurable_patchInclusion {N : ℕ} (hJ : 0 < J)
    (a : Fin N → MeshIndex J) (b : Fin N → Patch) : Measurable (patchInclusion hJ a b) :=
  measurable_domainInclusion _

def patchLaw (hJ : 0 < J) (hJ2 : 2 ≤ J) (a : Fin (n + 1) → MeshIndex J)
    (b : Fin (n + 1) → Patch) (β : ℝ) : Measure (PatchCoordinates hJ a b) :=
  domainMeasure (fun i ↦ patchDomain J hJ (a i) (b i))
    (fun i ↦ patchPoint hJ hJ2 (a i) (b i))
    (productGibbs (fun i ↦ patchMeasure J hJ (a i) (b i)) β)

def patchKernels (hJ : 0 < J) (hJ2 : 2 ≤ J) (a : Fin (n + 1) → MeshIndex J)
    (b : Fin (n + 1) → Patch) (β : ℝ) (i : Fin (n + 1)) :
    Kernel (PatchCoordinates hJ a b) (patchDomain J hJ (a i) (b i)) :=
  domainKernel (fun k ↦ patchDomain J hJ (a k) (b k))
    (fun k ↦ measurableSet_patchDomain J hJ (a k) (b k))
    (fun k ↦ patchPoint hJ hJ2 (a k) (b k))
    (gibbsKernel (fun k ↦ patchMeasure J hJ (a k) (b k)) β) i

instance isMarkovKernel_patchKernels (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch) (β : ℝ) (i : Fin (n + 1)) :
    IsMarkovKernel (patchKernels hJ hJ2 a b β i) := by
  unfold patchKernels
  infer_instance

theorem independentSite_patchKernels (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch) (β : ℝ) :
    IndependentSite (patchKernels hJ hJ2 a b β) :=
  independentSite_domainKernel _ (fun k ↦ measurableSet_patchDomain J hJ (a k) (b k))
    _ _ (independentSite_gibbsKernel _ β)

theorem productGibbs_ae_mem_patches (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch) (β : ℝ) :
    ∀ᵐ X ∂productGibbs (fun k ↦ patchMeasure J hJ (a k) (b k)) β,
      ∀ i, X i ∈ patchDomain J hJ (a i) (b i) := by
  have hbase : ∀ᵐ X ∂Measure.pi (fun k ↦ patchMeasure J hJ (a k) (b k)),
      ∀ i, X i ∈ patchDomain J hJ (a i) (b i) := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun k ↦ patchMeasure J hJ (a k) (b k)) i).quasiMeasurePreserving.ae
      (ae_mem_patchDomain J hJ hJ2 (a i) (b i))
  exact Measure.ae_smul_measure
    ((withDensity_absolutelyContinuous _ _).ae_le hbase) _

theorem patchLaw_probability (hJ : 0 < J) (hJ2 : 2 ≤ J) (hn : 2 ≤ n + 1)
    (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) : IsProbabilityMeasure (patchLaw hJ hJ2 a b β) := by
  let hprob : IsProbabilityMeasure (productGibbs (fun k ↦ patchMeasure J hJ (a k) (b k)) β) :=
    productGibbs_probability _ β (productNormalizer_patch_ne_top hJ hJ2 hn a b hβ hsub)
  unfold patchLaw
  infer_instance

/-- These are the two kernel hypotheses used by the actual L2 bridge.
Both are proved for the real source product law, without a cap or influence
assumption. Caps are used below for all-placement analytic formulas. -/
theorem preservesLaw_patchKernels (hJ : 0 < J) (hJ2 : 2 ≤ J) (hn : 2 ≤ n + 1)
    (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    PreservesLaw (patchKernels hJ hJ2 a b β) (patchLaw hJ hJ2 a b β) := by
  let hprob : IsProbabilityMeasure (productGibbs (fun k ↦ patchMeasure J hJ (a k) (b k)) β) :=
    productGibbs_probability _ β (productNormalizer_patch_ne_top hJ hJ2 hn a b hβ hsub)
  exact preservesLaw_domainKernel _ (fun k ↦ measurableSet_patchDomain J hJ (a k) (b k)) _ _ _
    (preservesLaw_gibbsKernel _ β (productNormalizer_patch_ne_top hJ hJ2 hn a b hβ hsub))
    (productGibbs_ae_mem_patches hJ hJ2 a b β)

/-- The actual kernel average is the conditional expectation generated
by the other coordinates of the actual product of patch subtypes. -/
theorem patch_siteAverage_ae_eq_condExp (hJ : 0 < J) (hJ2 : 2 ≤ J) (hn : 2 ≤ n + 1)
    (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    {f : PatchCoordinates hJ a b → ℝ} {B : ℝ}
    (hm : Measurable f) (hf : ∀ X, |f X| ≤ B) (i : Fin (n + 1)) :
    siteAverage (patchKernels hJ hJ2 a b β) f i =ᵐ[patchLaw hJ hJ2 a b β]
      (patchLaw hJ hJ2 a b β)[f | outsideSigma
        (fun k ↦ patchDomain J hJ (a k) (b k)) i] := by
  let hprob : IsProbabilityMeasure (patchLaw hJ hJ2 a b β) :=
    patchLaw_probability hJ hJ2 hn a b hβ hsub
  exact siteAverage_ae_eq_condExp _ _ (independentSite_patchKernels hJ hJ2 a b β)
    (preservesLaw_patchKernels hJ hJ2 hn a b hβ hsub) hm hf i

theorem map_patchInclusion_patchLaw (hJ : 0 < J) (hJ2 : 2 ≤ J) (hn : 2 ≤ n + 1)
    (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    Measure.map (patchInclusion hJ a b) (patchLaw hJ hJ2 a b β) =
      ProbabilityTheory.cond (gibbsMeasure greenRealRepresentative (n + 1) β)
        (patchProductEvent hJ a b) := by
  calc
    _ = productGibbs (fun k ↦ patchMeasure J hJ (a k) (b k)) β :=
      map_domainInclusion_domainMeasure _
        (fun k ↦ measurableSet_patchDomain J hJ (a k) (b k)) _ _
        (productGibbs_ae_mem_patches hJ hJ2 a b β)
    _ = _ := productGibbs_patch_eq_cond hJ hJ2 hn a b hβ hsub

theorem map_patchLaw_cells (hJ : 0 < J) (hJ2 : 2 ≤ J) (hn : 2 ≤ n + 1)
    (η : Fin (n + 1) → MeshIndex J) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    Measure.map (patchInclusion hJ η (fun _ ↦ .cell))
      (patchLaw hJ hJ2 η (fun _ ↦ .cell) β) = labelGibbsMeasure hJ η β := by
  rw [map_patchInclusion_patchLaw hJ hJ2 hn η (fun _ ↦ .cell) hβ hsub,
    patchProductEvent_cells, labelGibbsMeasure_eq_cond hJ hn η hβ hsub]

theorem map_patchLaw_adjacent (hJ : 0 < J) (hJ2 : 2 ≤ J) (hn : 2 ≤ n + 1)
    (η : Fin (n + 1) → MeshIndex J) (t : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    Measure.map (patchInclusion hJ (Function.update η t a) (adjacentShapes t d))
      (patchLaw hJ hJ2 (Function.update η t a) (adjacentShapes t d) β) =
        twoCellGibbsMeasure hJ η t a (nextCell J hJ a d) β := by
  rw [map_patchInclusion_patchLaw hJ hJ2 hn _ _ hβ hsub, patchProductEvent_adjacent]
  rfl

theorem patchOutside_inclusion (hJ : 0 < J) (a : Fin (n + 1) → MeshIndex J)
    (b : Fin (n + 1) → Patch) (i : Fin (n + 1)) (X : PatchCoordinates hJ a b) :
    PatchOutside hJ a b i (removeSite i (patchInclusion hJ a b X)) :=
  fun j ↦ subset_closure (X (i.succAbove j)).property

theorem conditionalKernel_ae_mem_patchDomain (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : MeshIndex J) (b : Patch) (i : Fin (n + 1)) (β : ℝ) (Y : Configuration n)
    (hi : Integrable (OneCoordinateConditionals.sourceWeight β Y) (patchMeasure J hJ a b))
    (hz : 0 < ∫ z, OneCoordinateConditionals.sourceWeight β Y z ∂patchMeasure J hJ a b) :
    ∀ᵐ z ∂conditionalKernel (patchMeasure J hJ a b) i β Y, z ∈ patchDomain J hJ a b := by
  rw [conditionalKernel_eq_pointLaw _ i β Y hi hz, pointLaw]
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_mem_patchDomain J hJ hJ2 a b)

/-- A finite actual section is unchanged when regarded as a law on its
own cell subtype. In particular no Dirac mass is inserted at its boundary. -/
theorem map_val_patchKernel (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch)
    (β : ℝ) (i : Fin (n + 1)) (X : PatchCoordinates hJ a b)
    (hi : Integrable (OneCoordinateConditionals.sourceWeight β
      (removeSite i (patchInclusion hJ a b X))) (patchMeasure J hJ (a i) (b i)))
    (hz : 0 < ∫ z, OneCoordinateConditionals.sourceWeight β
      (removeSite i (patchInclusion hJ a b X)) z ∂patchMeasure J hJ (a i) (b i)) :
    Measure.map (Subtype.val : patchDomain J hJ (a i) (b i) → Torus)
      (patchKernels hJ hJ2 a b β i X) =
        conditionalKernel (patchMeasure J hJ (a i) (b i)) i β
          (removeSite i (patchInclusion hJ a b X)) := by
  exact map_val_domainKernel _ _ _ _ i X
    (conditionalKernel_ae_mem_patchDomain hJ hJ2 (a i) (b i) i β _ hi hz)

/-- Literal normalized Green conditional density for every allowed point
of a capped product of cells. The actual Green bounds and normalizers are
discharged by the previously proved source constants, including β=0. -/
theorem map_val_labelKernel_raw {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ ConditionalLawEstimates.occupationBound β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η) (i : Fin (n + 1))
    (X : PatchCoordinates (ConditionalLawEstimates.mesh_pos hmesh) η (fun _ ↦ .cell)) :
    let hJ := ConditionalLawEstimates.mesh_pos hmesh
    let Y := removeSite i (patchInclusion hJ η (fun _ ↦ .cell) X)
    let μ := meshCellMeasure J hJ (η i)
    Measure.map (Subtype.val : patchDomain J hJ (η i) .cell → Torus)
      (patchKernels hJ (ConditionalLawEstimates.mesh_two_le hmesh) η (fun _ ↦ .cell) β i X) =
        μ.withDensity (fun z ↦ ENNReal.ofReal (ConditionalLawEstimates.rawDensity μ β Y z)) := by
  dsimp only
  have hY : PrescribedOutside (ConditionalLawEstimates.mesh_pos hmesh) η i
      (removeSite i (patchInclusion (ConditionalLawEstimates.mesh_pos hmesh) η (fun _ ↦ .cell) X)) :=
    patchOutside_inclusion _ η (fun _ ↦ .cell) i X
  have hb := ConditionalLawEstimates.capped_patch_law _ hβ hβ₀ hδ hmesh η hη i _ hY (η i) .cell
  exact (map_val_patchKernel _ (ConditionalLawEstimates.mesh_two_le hmesh) η (fun _ ↦ .cell)
    β i X hb.regular_integrable hb.regular_normalizer_pos).trans hb.kernel_eq_raw

/-- All coordinates, including i≠t, are covered on the entire adjacent
product. The cap is imposed on both completed labels before any placement
is chosen. Coincident positions and prescribed cell boundaries are allowed. -/
theorem map_val_adjacentKernel_raw {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ ConditionalLawEstimates.occupationBound β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (t i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    (hadm : AdjacentAdmissible (ConditionalLawEstimates.mesh_pos hmesh) δ η t a d)
    (X : PatchCoordinates (ConditionalLawEstimates.mesh_pos hmesh)
      (Function.update η t a) (adjacentShapes t d)) :
    let hJ := ConditionalLawEstimates.mesh_pos hmesh
    let A := Function.update η t a
    let B := adjacentShapes t d
    let Y := removeSite i (patchInclusion hJ A B X)
    let μ := patchMeasure J hJ (A i) (B i)
    Measure.map (Subtype.val : patchDomain J hJ (A i) (B i) → Torus)
      (patchKernels hJ (ConditionalLawEstimates.mesh_two_le hmesh) A B β i X) =
        μ.withDensity (fun z ↦ ENNReal.ofReal (ConditionalLawEstimates.rawDensity μ β Y z)) := by
  dsimp only
  obtain ⟨ζ, hζ, hY⟩ := exists_capped_adjacent_outside (ConditionalLawEstimates.mesh_pos hmesh)
    η t i a d hadm _ (patchOutside_inclusion _ _ _ i X)
  have hb := ConditionalLawEstimates.capped_patch_law _ hβ hβ₀ hδ hmesh ζ hζ i _ hY
    (Function.update η t a i) (adjacentShapes t d i)
  exact (map_val_patchKernel _ (ConditionalLawEstimates.mesh_two_le hmesh) _ _ β i X
    hb.regular_integrable hb.regular_normalizer_pos).trans hb.kernel_eq_raw

end SourcePatches

end PeriodicAttractiveLogGas.CoordinateConditionalKernels
