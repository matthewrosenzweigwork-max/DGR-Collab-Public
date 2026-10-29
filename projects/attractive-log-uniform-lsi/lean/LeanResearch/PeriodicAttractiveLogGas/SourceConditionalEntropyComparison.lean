import LeanResearch.PeriodicAttractiveLogGas.ConditionalEntropyReduction

/-! The source conditional-entropy comparison under the actual bounded
tilt of the original label Gibbs law. Section masses, zero-mass fallbacks,
outside marginals and real integrability are retained before summation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped ENNReal NNReal BigOperators

namespace PeriodicAttractiveLogGas.SourceConditionalEntropyComparison

open ConditionalEntropyDisintegration ConditionalEntropyReduction
  RelativeEntropyReferenceChange ReferenceDensityChange ReferenceConditionalNormalization
  ReferencePotentialBounds ReferenceExponentialComparison ResidualExponential
  GreenGradientOscillation MeshCells LabelOccupations CellRestrictions
  ReferenceResidual ReferenceSelfTerms ResidualNearExponential ResidualFarExponential
  MovingPoleCalculus OneCoordinateConditionals GreenPointWeights

section Transport
variable {A B Ω : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Ω]

/-- Zero section masses are null under the true tilted outside law. -/
theorem ae_sectionMass_pos (κ : Kernel A B) [IsMarkovKernel κ]
    (ρ : Measure A) {F : A × B → ℝ} (hF : Measurable F) {K : ℝ}
    (hb : ∀ a b, 0 ≤ F (a,b) ∧ F (a,b) ≤ K) :
    ∀ᵐ a ∂normalizedTilt ρ (sectionMass κ F), 0 < sectionMass κ F a := by
  apply (ae_withDensity_iff ((measurable_sectionMass κ hF).div_const _).ennreal_ofReal).mpr
  apply Eventually.of_forall
  intro a ha
  have hn : sectionMass κ F a ≠ 0 := by
    intro hz
    exact ha (by simp only [hz, zero_div, ENNReal.ofReal_zero])
  exact lt_of_le_of_ne (sectionMass_bounds κ hF hb a).1 (Ne.symm hn)

/-- Real Fubini through a genuine split disintegration. Integrability of
the joint observable is a prerequisite, and outer integrability a conclusion. -/
theorem split_integral (Q : Measure Ω) [IsProbabilityMeasure Q]
    (e : Ω ≃ᵐ A × B) (ρ : Measure A) [IsProbabilityMeasure ρ]
    (κ : Kernel A B) [IsMarkovKernel κ] (hdis : ρ ⊗ₘ κ = Q.map e)
    {H : Ω → ℝ} (hH : Integrable H Q) :
    Integrable (fun a => ∫ b, H (e.symm (a,b)) ∂κ a) ρ ∧
    (∫ a, ∫ b, H (e.symm (a,b)) ∂κ a ∂ρ) = ∫ x, H x ∂Q := by
  have hmp : MeasurePreserving e Q (ρ ⊗ₘ κ) := ⟨e.measurable, hdis.symm⟩
  let H' : A × B → ℝ := H ∘ e.symm
  have hi : Integrable H' (ρ ⊗ₘ κ) :=
    (hmp.integrable_comp_emb e.measurableEmbedding).mp
      (by simpa only [H', Function.comp_def, e.symm_apply_apply] using hH)
  refine ⟨hi.integral_compProd, ?_⟩
  calc
    _ = ∫ p, H' p ∂(ρ ⊗ₘ κ) := (Measure.integral_compProd hi).symm
    _ = ∫ x, H' (e x) ∂Q := (hmp.integral_comp' H').symm
    _ = _ := by simp only [H', Function.comp_apply, e.symm_apply_apply]

end Transport

section Source
variable {J n : ℕ} (hJ : 0 < J) (hN : 2 ≤ n + 1)
  (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
  (η : LabelVector J (n + 1)) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
  (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
    ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))

include hN hβ hsub hformula

/-- The actual original label law split over its own outside marginal. -/
theorem source_reference_split (i : Fin (n + 1)) :
    (labelGibbsMeasure hJ η β).map (configurationSplit i) =
      ((labelGibbsMeasure hJ η β).map (removeSite i)) ⊗ₘ
        PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
          (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i := by
  let : IsProbabilityMeasure (labelGibbsMeasure hJ η β) :=
    isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ hsub
  let κ := PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
    (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
  let : IsMarkovKernel κ :=
    PositiveProductConditionals.isMarkovKernel_conditionalKernel _ _ _ _ _
  apply split_law_of_lintegral i (labelGibbsMeasure hJ η β) κ
  intro G hG
  exact reference_lintegral_disintegrate hJ hN μ η hβ hsub hformula i hG

/-- Both the conditional law and the positive-mass support are derived
under the original tilted joint law. The original particle count is unchanged. -/
theorem source_tilt_disintegration {F : Configuration (n + 1) → ℝ}
    (hF : Measurable F) {K : ℝ} (hb : ∀ X, 0 ≤ F X ∧ F X ≤ K)
    (hS : 0 < ∫ X, F X ∂labelGibbsMeasure hJ η β) (i : Fin (n + 1)) :
    let P := labelGibbsMeasure hJ η β
    let Q := normalizedTilt P F
    let κ := PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
    letI : IsMarkovKernel κ :=
      PositiveProductConditionals.isMarkovKernel_conditionalKernel _ _ _ _ _
    let F' := F ∘ (configurationSplit i).symm
    let hF' : Measurable F' := hF.comp (configurationSplit i).symm.measurable
    let hb' : ∀ Y z, 0 ≤ F' (Y,z) ∧ F' (Y,z) ≤ K :=
      fun Y z => hb ((configurationSplit i).symm (Y,z))
    Q.map (removeSite i) = normalizedTilt (P.map (removeSite i)) (sectionMass κ F') ∧
    (Q.map (removeSite i)) ⊗ₘ conditionalTiltKernel κ F' hF' hb' = Q.map (configurationSplit i) ∧
    (∀ᵐ Y ∂Q.map (removeSite i),
      0 < sectionMass κ F' Y ∧ PrescribedOutside hJ η i Y) ∧
    Integrable (fun X => conditionalLogEntropy κ F' (removeSite i X)) Q := by
  dsimp only
  let P := labelGibbsMeasure hJ η β
  let : IsProbabilityMeasure P := isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ hsub
  let ρ := P.map (removeSite i)
  let κ := PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
    (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
  let : IsMarkovKernel κ :=
    PositiveProductConditionals.isMarkovKernel_conditionalKernel _ _ _ _ _
  let F' := F ∘ (configurationSplit i).symm
  have hf : Measurable F' := hF.comp (configurationSplit i).symm.measurable
  have hfb : ∀ Y z, 0 ≤ F' (Y,z) ∧ F' (Y,z) ≤ K :=
    fun Y z => hb ((configurationSplit i).symm (Y,z))
  have hs := source_reference_split hJ hN μ η hβ hsub hformula i
  have hd := tilt_equiv_disintegration κ P (configurationSplit i) ρ hs hF hb hS
  have hout : (normalizedTilt P F).map (removeSite i) = normalizedTilt ρ (sectionMass κ F') := by
    simpa only [configurationSplit_apply] using hd.2.1
  have hpos : ∀ᵐ Y ∂(normalizedTilt P F).map (removeSite i), 0 < sectionMass κ F' Y := by
    rw [hout]
    exact ae_sectionMass_pos κ ρ hf hfb
  have hpres : ∀ᵐ Y ∂(normalizedTilt P F).map (removeSite i), PrescribedOutside hJ η i Y := by
    rw [hout]
    exact (withDensity_absolutelyContinuous _ _).ae_le
      (SourceEntropyTests.ae_prescribedOutside_labelGibbs hJ η β i)
  have hi := source_entropy_disintegration hJ hN μ η hβ hsub hformula i hF hb hS
  refine ⟨hout, ?_, hpos.and hpres, ?_⟩
  · simpa only [configurationSplit_apply] using hd.2.2
  · simpa only [F', Function.comp_def, configurationSplit_symm_apply] using! hi.1

end Source

section Comparison
variable {J n : ℕ} (hJ : 0 < J)
  (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
  (η : LabelVector J (n + 1))

/-- Each own-coordinate potential is bounded and integrable under every
finite joint law, independently of whether that law has a product density. -/
theorem evaluated_potential_integrable
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (Q : Measure (Configuration (n + 1))) [IsFiniteMeasure Q] (i : Fin (n + 1)) :
    Integrable (fun X => potential (μ (η i)) (X i)) Q := by
  apply Integrable.of_bound
    ((ReferenceDensityChange.measurable_potential (μ (η i))).comp
      (measurable_pi_apply i)).aestronglyMeasurable (globalPotentialBound J)
  exact Eventually.of_forall fun X => by
    simpa only [Real.norm_eq_abs, Function.comp_apply] using!
      (global_potential_bound hJ (η i) _ (hμ (η i)) (X i)).2

/-- The exact self-term cancellation is an equality of genuine integrals. -/
theorem sum_potential_integrals
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (Q : Measure (Configuration (n + 1))) [IsFiniteMeasure Q] (β : ℝ) :
    (β / (n + 1 : ℕ)) * (∑ i, ∫ X, potential (μ (η i)) (X i) ∂Q) =
      β * ∫ X, selfTerm μ η X ∂Q := by
  rw [← integral_finsetSum _ (fun i _ => evaluated_potential_integrable hJ μ η hμ Q i)]
  simp only [selfTerm, integral_div]
  ring

/-- Source eq:sum-conditional-entropy before the final exponential estimate.
The two analytic premises here are intermediate facts about the actual joint
law; the full source endpoint below derives both from the source hypotheses. -/
theorem comparison_of_integrable_residual (hN : 2 ≤ n + 1)
    {β β₀ t : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀) (hsub : β₀ < 4)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
    (hdensity : ∀ a, ∀ᵐ z ∂meshCellMeasure J hJ a,
      Real.exp (-1) ≤ Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ∧
      Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ≤ Real.exp 1)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (ht : t ≤ ConditionalLawEstimates.occupationBound β₀) (hη : OccupationCap t η)
    {F : Configuration (n + 1) → ℝ} (hF : Measurable F) {K : ℝ}
    (hb : ∀ X, 0 ≤ F X ∧ F X ≤ K)
    (hS : 0 < ∫ X, F X ∂labelGibbsMeasure hJ η β)
    (hfin : klDiv (normalizedTilt (labelGibbsMeasure hJ η β) F)
      (Measure.pi (fun i => μ (η i))) ≠ ∞)
    (hY : Integrable (fun X => β * residualSum μ η X)
      (normalizedTilt (labelGibbsMeasure hJ η β) F)) :
    let Q := normalizedTilt (labelGibbsMeasure hJ η β) F
    let L := fun i X => conditionalLogEntropy
      (PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
        (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i)
      (F ∘ (configurationSplit i).symm) (removeSite i X)
    (∀ i, Integrable (L i) Q) ∧
    (klDiv Q (Measure.pi (fun i => μ (η i)))).toReal -
        2 * (∫ X, β * residualSum μ η X ∂Q) + β * (∫ X, selfTerm μ η X ∂Q) -
        (β / (n + 1 : ℕ)) * ∑ i, pairAverage (μ (η i)) (μ (η i)) ≤
      ∑ i, ∫ X, L i X ∂Q := by
  let P := labelGibbsMeasure hJ η β
  let Q := normalizedTilt P F
  let : IsProbabilityMeasure P :=
    isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ (hβle.trans_lt hsub)
  let : IsProbabilityMeasure Q := normalizedTilt_probability
    (Eventually.of_forall fun X => (hb X).1)
    (RelativeEntropyVariational.bounded_density_integrable hF (Eventually.of_forall hb)).1 hS
  let κ (i : Fin (n + 1)) := PositiveProductConditionals.conditionalKernel
    (μ (η i)) (referenceTilt μ η β) (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
  let (i : Fin (n + 1)) : IsMarkovKernel (κ i) :=
    PositiveProductConditionals.isMarkovKernel_conditionalKernel _ _ _ _ _
  let F' (i : Fin (n + 1)) := F ∘ (configurationSplit i).symm
  have hf (i : Fin (n + 1)) : Measurable (F' i) :=
    hF.comp (configurationSplit i).symm.measurable
  have hfb (i : Fin (n + 1)) : ∀ Y z, 0 ≤ F' i (Y,z) ∧ F' i (Y,z) ≤ K :=
    fun Y z => hb ((configurationSplit i).symm (Y,z))
  let ψ (i : Fin (n + 1)) := conditionalTiltKernel (κ i) (F' i) (hf i) (hfb i)
  let (i : Fin (n + 1)) : IsMarkovKernel (ψ i) := by dsimp [ψ]; infer_instance
  let ρ (i : Fin (n + 1)) := Q.map (removeSite i)
  let T (i : Fin (n + 1)) (Y : Configuration n) := (klDiv (ψ i Y) (μ (η i))).toReal
  let R (i : Fin (n + 1)) (Y : Configuration n) :=
    ∫ z, β * residualSection μ η i Y z ∂ψ i Y
  let H (i : Fin (n + 1)) (Y : Configuration n) := ∫ z, potential (μ (η i)) z ∂ψ i Y
  let L (i : Fin (n + 1)) := conditionalLogEntropy (κ i) (F' i)
  have hd (i : Fin (n + 1)) := source_tilt_disintegration hJ hN μ η hβ
    (hβle.trans_lt hsub) hformula hF hb hS i
  have hdis (i : Fin (n + 1)) : ρ i ⊗ₘ ψ i = Q.map (configurationSplit i) := (hd i).2.1
  have hten := ConditionalRelativeEntropy.product_tensorization_integral Q
    (fun i => μ (η i)) ψ hdis hfin
  have hten' : (klDiv Q (Measure.pi (fun i => μ (η i)))).toReal ≤
      ∑ i, ∫ Y, T i Y ∂ρ i := hten.2.2
  have hμ := source_reference_domination hJ μ η β hformula hdensity
  have hw := weighted_section_integrals_of_residual_integrable hJ μ hμ η hβ Q hY
  have hr (i : Fin (n + 1)) : Integrable (R i) (ρ i) ∧
      (∫ Y, R i Y ∂ρ i) = ∫ X, β * residualSection μ η i (removeSite i X) (X i) ∂Q := by
    simpa only [configurationSplit_symm_apply, removeSite_insertSite, insertSite_self] using!
      split_integral Q (configurationSplit i) (ρ i) (ψ i) (hdis i) (hw.1 i)
  have hp (i : Fin (n + 1)) : Integrable (H i) (ρ i) ∧
      (∫ Y, H i Y ∂ρ i) = ∫ X, potential (μ (η i)) (X i) ∂Q := by
    simpa only [configurationSplit_symm_apply, insertSite_self] using!
      split_integral Q (configurationSplit i) (ρ i) (ψ i) (hdis i)
        (evaluated_potential_integrable hJ μ η hμ Q i)
  have hl (i : Fin (n + 1)) : Integrable (L i) (ρ i) :=
    (integrable_map_measure (measurable_conditionalLogEntropy (κ i) (hf i) (hfb i)).aestronglyMeasurable
      (measurable_removeSite i).aemeasurable).mpr (hd i).2.2.2
  have hlo (i : Fin (n + 1)) : ∀ᵐ Y ∂ρ i,
      T i Y - R i Y + (β / (n + 1 : ℕ)) * H i Y -
        (β / (n + 1 : ℕ)) * pairAverage (μ (η i)) (μ (η i)) ≤ L i Y := by
    filter_upwards [(hd i).2.2.1] with Y hY
    have hq : Measurable (fun z => F' i (Y,z) / sectionMass (κ i) (F' i) Y) :=
      ((hf i).comp measurable_prodMk_left).div_const _
    have hqB : ∀ᵐ z ∂κ i Y,
        0 ≤ F' i (Y,z) / sectionMass (κ i) (F' i) Y ∧
        F' i (Y,z) / sectionMass (κ i) (F' i) Y ≤ K / sectionMass (κ i) (F' i) Y :=
      Eventually.of_forall fun z => ⟨div_nonneg (hfb i Y z).1 hY.1.le,
        div_le_div_of_nonneg_right (hfb i Y z).2 hY.1.le⟩
    have hψ : ψ i Y = (κ i Y).withDensity
        (fun z => ENNReal.ofReal (F' i (Y,z) / sectionMass (κ i) (F' i) Y)) :=
      conditionalTiltKernel_apply (κ i) (hf i) (hfb i) Y hY.1.ne'
    obtain ⟨_, _, _, _, _, _, _, hi⟩ := source_section_tilt_kl_change hJ μ η hβ hβle
      hformula hdensity hmesh ht hη i Y hY.2 (ψ i Y)
      (fun z => F' i (Y,z) / sectionMass (κ i) (F' i) Y) hq hψ hqB
    rw [(conditionalTilt_kl (κ i) (hf i) (hfb i) Y).2] at hi
    exact hi
  have hInt (i : Fin (n + 1)) :
      (∫ Y, T i Y ∂ρ i) - (∫ Y, R i Y ∂ρ i) +
        (β / (n + 1 : ℕ)) * (∫ Y, H i Y ∂ρ i) -
        (β / (n + 1 : ℕ)) * pairAverage (μ (η i)) (μ (η i)) ≤ ∫ Y, L i Y ∂ρ i := by
    have hTi : Integrable (T i) (ρ i) := hten.2.1 i
    have hRi := (hr i).1
    have hHi := (hp i).1.const_mul (β / (n + 1 : ℕ))
    have hCi : Integrable
        (fun _ : Configuration n => (β / (n + 1 : ℕ)) * pairAverage (μ (η i)) (μ (η i))) (ρ i) :=
      integrable_const _
    have hi := integral_mono_ae (((hTi.sub hRi).add hHi).sub hCi) (hl i) (hlo i)
    change (∫ Y, T i Y - R i Y + (β / (n + 1 : ℕ)) * H i Y -
      (β / (n + 1 : ℕ)) * pairAverage (μ (η i)) (μ (η i)) ∂ρ i) ≤ ∫ Y, L i Y ∂ρ i at hi
    have e₁ := integral_sub ((hTi.sub hRi).add hHi) hCi
    have e₂ := integral_add (hTi.sub hRi) hHi
    have e₃ := integral_sub hTi hRi
    simp only [Pi.sub_apply, Pi.add_apply] at e₁ e₂ e₃
    rw [e₁, e₂, e₃] at hi
    simpa only [integral_const_mul, integral_const,
      probReal_univ, one_smul] using hi
  refine ⟨fun i => (hd i).2.2.2, ?_⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ => hInt i
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  simp only [(hr _).2, (hp _).2] at hsum
  rw [hw.2, sum_potential_integrals hJ μ η hμ Q β] at hsum
  have hmap (i : Fin (n + 1)) : (∫ Y, L i Y ∂ρ i) = ∫ X, L i (removeSite i X) ∂Q :=
    integral_map (measurable_removeSite i).aemeasurable (hl i).aestronglyMeasurable
  simp only [hmap] at hsum
  change (klDiv Q (Measure.pi (fun i => μ (η i)))).toReal -
      2 * (∫ X, β * residualSum μ η X ∂Q) + β * (∫ X, selfTerm μ η X ∂Q) -
      (β / (n + 1 : ℕ)) * ∑ i, pairAverage (μ (η i)) (μ (η i)) ≤
    ∑ i, ∫ X, L i (removeSite i X) ∂Q
  linarith only [hten', hsum]

end Comparison

/-- An essentially bounded Gibbs density has an everywhere bounded
nonnegative measurable representative defining exactly the same probability.
Neither boundedness nor positivity outside the original law is assumed. -/
theorem bounded_probability_representative {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure Q] {q : Ω → ℝ}
    (hq : AEMeasurable q P) {K : ℝ}
    (hQ : Q = P.withDensity (fun X => ENNReal.ofReal (q X)))
    (hb : ∀ᵐ X ∂P, 0 ≤ q X ∧ q X ≤ K) :
    ∃ F : Ω → ℝ, Measurable F ∧ (∀ X, 0 ≤ F X ∧ F X ≤ max K 0) ∧
      F =ᵐ[P] q ∧ (∫ X, F X ∂P) = 1 ∧ Q = normalizedTilt P F := by
  let F : Ω → ℝ := fun X => max 0 (min (hq.mk q X) (max K 0))
  have hF : Measurable F := measurable_const.max (hq.measurable_mk.min measurable_const)
  have hFb (X : Ω) : 0 ≤ F X ∧ F X ≤ max K 0 :=
    ⟨le_max_left _ _, max_le (le_max_right _ _) (min_le_right _ _)⟩
  have he : F =ᵐ[P] q := by
    filter_upwards [hq.ae_eq_mk, hb] with X hX hB
    simp only [F, ← hX, min_eq_left (hB.2.trans (le_max_left K 0)), max_eq_right hB.1]
  have hQF : Q = P.withDensity (fun X => ENNReal.ofReal (F X)) :=
    hQ.trans (withDensity_congr_ae (he.symm.mono fun X hX => congrArg ENNReal.ofReal hX))
  have hS : (∫ X, F X ∂P) = 1 :=
    DensityMoments.integral_density_one hQF hF (Eventually.of_forall fun X => (hFb X).1)
  refine ⟨F, hF, hFb, he, hS, ?_⟩
  simpa only [normalizedTilt, hS, div_one] using hQF

section SourceBounds
variable {J n : ℕ} (hJ : 0 < J) (hN : 2 ≤ n + 1)
  {β β₀ t C₂ : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀) (hsub : β₀ < 4)
  (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
  (hmesh : 8 * (chosenRadius β₀ C₂ + 1) ≤ J)
  (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
  (η : LabelVector J (n + 1)) (ht : 0 ≤ t) (hη : OccupationCap t η)
  (hcap : 24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
    nearScale (chosenRadius β₀ C₂) * t ≤ 1)
  (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
    ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
  (hdensity : ∀ a, ∀ᵐ z ∂meshCellMeasure J hJ a,
    Real.exp (-1) ≤ Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ∧
    Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ≤ Real.exp 1)
  (hmeshC : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
  (htC : t ≤ ConditionalLawEstimates.occupationBound β₀)

include hN hβ hβle hsub hC hk hmesh ht hη hcap hformula hdensity hmeshC htC

/-- The actual source comparison and exact cancellation, with all real
integrability derived for an arbitrary bounded nonnegative test. No product
density bound, residual moment, or conditional entropy assumption is imposed. -/
theorem source_normalized_tilt_comparison {F : Configuration (n + 1) → ℝ}
    (hF : Measurable F) {K : ℝ} (hb : ∀ X, 0 ≤ F X ∧ F X ≤ K)
    (hS : 0 < ∫ X, F X ∂labelGibbsMeasure hJ η β) :
    let P := labelGibbsMeasure hJ η β
    let Q := normalizedTilt P F
    let S := ∫ X, F X ∂P
    let L := fun i X => conditionalLogEntropy
      (PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
        (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i)
      (F ∘ (configurationSplit i).symm) (removeSite i X)
    Integrable (fun X => Real.log (F X / S)) Q ∧
    Integrable (fun X => β * residualSum μ η X) Q ∧
    (∀ i, Integrable (L i) Q) ∧
    ((klDiv Q (Measure.pi (fun i => μ (η i)))).toReal -
        2 * (∫ X, β * residualSum μ η X ∂Q) + β * (∫ X, selfTerm μ η X ∂Q) -
        (β / (n + 1 : ℕ)) * ∑ i, pairAverage (μ (η i)) (μ (η i)) =
      (∫ X, Real.log (F X / S) ∂Q) - (∫ X, β * residualSum μ η X ∂Q) -
        Real.log (referenceNormalizer μ η β) -
        (β / (n + 1 : ℕ)) * ∑ i, pairAverage (μ (η i)) (μ (η i))) ∧
    (∫ X, Real.log (F X / S) ∂Q) - (∫ X, β * residualSum μ η X ∂Q) -
        Real.log (referenceNormalizer μ η β) -
        (β / (n + 1 : ℕ)) * ∑ i, pairAverage (μ (η i)) (μ (η i)) ≤
      ∑ i, ∫ X, L i X ∂Q := by
  let P := labelGibbsMeasure hJ η β
  let S := ∫ X, F X ∂P
  let Q := normalizedTilt P F
  let q : Configuration (n + 1) → ℝ := fun X => F X / S
  let : IsProbabilityMeasure P :=
    isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ (hβle.trans_lt hsub)
  let : IsProbabilityMeasure Q := normalizedTilt_probability
    (Eventually.of_forall fun X => (hb X).1)
    (RelativeEntropyVariational.bounded_density_integrable hF (Eventually.of_forall hb)).1 hS
  have hq : Measurable q := hF.div_const _
  have hqb : ∀ᵐ X ∂P, 0 ≤ q X ∧ q X ≤ K / S :=
    Eventually.of_forall fun X => ⟨div_nonneg (hb X).1 hS.le,
      div_le_div_of_nonneg_right (hb X).2 hS.le⟩
  have hQ : Q = P.withDensity (fun X => ENNReal.ofReal (q X)) := rfl
  have hi := source_reference_log_integrable hJ hN hβ hβle hsub hC hk hmesh μ η ht hη hcap
    hformula hdensity Q q hq hQ hqb
  have hkL := source_kl_change hJ hN hβ hβle hsub hC hk hmesh μ η ht hη hcap
    hformula hdensity Q q hq hQ hqb
  have hc := comparison_of_integrable_residual hJ μ η hN hβ hβle hsub hformula hdensity
    hmeshC htC hη hF hb hS hkL.2.2.2.1 hi.2.1
  have hlog : Integrable (fun X => Real.log (q X)) Q := hi.2.2.2.1
  have hKLP : (klDiv Q P).toReal = ∫ X, Real.log (q X) ∂Q :=
    toReal_klDiv_eq_log_density hQ hq (hqb.mono fun _ h => h.1) hlog
  have he : (klDiv Q (Measure.pi (fun i => μ (η i)))).toReal -
        2 * (∫ X, β * residualSum μ η X ∂Q) + β * (∫ X, selfTerm μ η X ∂Q) -
        (β / (n + 1 : ℕ)) * ∑ i, pairAverage (μ (η i)) (μ (η i)) =
      (∫ X, Real.log (q X) ∂Q) - (∫ X, β * residualSum μ η X ∂Q) -
        Real.log (referenceNormalizer μ η β) -
        (β / (n + 1 : ℕ)) * ∑ i, pairAverage (μ (η i)) (μ (η i)) := by
    rw [hkL.2.2.2.2, hKLP]
    ring
  refine ⟨hlog, hi.2.1, hc.1, he, ?_⟩
  rw [← he]
  exact hc.2

/-- Source eq:conditional-entropy-reduction for every actual normalized
bounded test of positive Gibbs mass, including beta zero. The conditional
law is the actual Markov tilt over the original outside marginal. -/
theorem source_normalized_tilt_reduction {F : Configuration (n + 1) → ℝ}
    (hF : Measurable F) {K : ℝ} (hb : ∀ X, 0 ≤ F X ∧ F X ≤ K)
    (hS : 0 < ∫ X, F X ∂labelGibbsMeasure hJ η β) :
    (1 / 2 : ℝ) * (∫ X, Real.log (F X / ∫ X, F X ∂labelGibbsMeasure hJ η β)
        ∂normalizedTilt (labelGibbsMeasure hJ η β) F) - defectConstant J β₀ C₂ ≤
      ∑ i, ∫ X, conditionalLogEntropy
        (PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
          (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i)
        (F ∘ (configurationSplit i).symm) (removeSite i X)
          ∂normalizedTilt (labelGibbsMeasure hJ η β) F := by
  let P := labelGibbsMeasure hJ η β
  let S := ∫ X, F X ∂P
  let Q := normalizedTilt P F
  let q : Configuration (n + 1) → ℝ := fun X => F X / S
  let : IsProbabilityMeasure P :=
    isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ (hβle.trans_lt hsub)
  let : IsProbabilityMeasure Q := normalizedTilt_probability
    (Eventually.of_forall fun X => (hb X).1)
    (RelativeEntropyVariational.bounded_density_integrable hF (Eventually.of_forall hb)).1 hS
  have hq : Measurable q := hF.div_const _
  have hqb : ∀ᵐ X ∂P, 0 ≤ q X ∧ q X ≤ K / S :=
    Eventually.of_forall fun X => ⟨div_nonneg (hb X).1 hS.le,
      div_le_div_of_nonneg_right (hb X).2 hS.le⟩
  have hc := source_normalized_tilt_comparison hJ hN hβ hβle hsub hC hk hmesh μ η ht hη hcap
    hformula hdensity hmeshC htC hF hb hS
  have hr := bounded_tilt_remaining_term hJ hN hβ hβle hsub hC hk hmesh μ η ht hη hcap
    hformula hdensity Q q hq rfl hqb
  have htwo : (1 / 2 : ℝ) * (∫ X, 2 * β * residualSum μ η X ∂Q) =
      ∫ X, β * residualSum μ η X ∂Q := by
    rw [← integral_const_mul]
    congr 1
    funext X
    ring
  have hlo : (1 / 2 : ℝ) * (∫ X, Real.log (q X) ∂Q) - defectConstant J β₀ C₂ ≤
      (∫ X, Real.log (q X) ∂Q) - (∫ X, β * residualSum μ η X ∂Q) -
        Real.log (referenceNormalizer μ η β) -
        (β / (n + 1 : ℕ)) * ∑ i, pairAverage (μ (η i)) (μ (η i)) := by
    have hh := hr.2.2.2
    rw [htwo] at hh
    have hnonneg := mul_nonneg (hβ.trans hβle) (ReferenceSelfTerms.selfBound_nonneg hJ)
    dsimp only [defectConstant]
    linarith only [hh, hnonneg]
  exact hlo.trans hc.2.2.2.2

/-- At beta zero the source comparison reduces to product tensorization
with coefficient one and no defect, without an unweighted residual moment. -/
theorem source_normalized_tilt_zero (hzero : β = 0)
    {F : Configuration (n + 1) → ℝ} (hF : Measurable F) {K : ℝ}
    (hb : ∀ X, 0 ≤ F X ∧ F X ≤ K)
    (hS : 0 < ∫ X, F X ∂labelGibbsMeasure hJ η β) :
    (∫ X, Real.log (F X / ∫ X, F X ∂labelGibbsMeasure hJ η β)
        ∂normalizedTilt (labelGibbsMeasure hJ η β) F) ≤
      ∑ i, ∫ X, conditionalLogEntropy
        (PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
          (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i)
        (F ∘ (configurationSplit i).symm) (removeSite i X)
          ∂normalizedTilt (labelGibbsMeasure hJ η β) F := by
  have hc := source_normalized_tilt_comparison hJ hN hβ hβle hsub hC hk hmesh μ η ht hη hcap
    hformula hdensity hmeshC htC hF hb hS
  have hZ : referenceNormalizer μ η β = 1 := by
    subst β
    exact (source_reference_zero hJ hN μ η hformula).2.1
  have hZ0 : referenceNormalizer μ η 0 = 1 := by simpa only [hzero] using hZ
  simpa only [hzero, hZ0, zero_mul, integral_zero, Real.log_one, zero_div, sub_zero] using! hc.2.2.2.2

/-- The manuscript's arbitrary probability with bounded density relative
to the original Gibbs law. A bounded measurable representative is constructed;
the displayed kernels disintegrate this very Q, and their finite KL costs
are genuinely integrable under Q's true outside marginals. -/
theorem source_bounded_density_reduction
    (Q : Measure (Configuration (n + 1))) [IsProbabilityMeasure Q]
    {q : Configuration (n + 1) → ℝ} (hq : AEMeasurable q (labelGibbsMeasure hJ η β)) {K : ℝ}
    (hQ : Q = (labelGibbsMeasure hJ η β).withDensity (fun X => ENNReal.ofReal (q X)))
    (hb : ∀ᵐ X ∂labelGibbsMeasure hJ η β, 0 ≤ q X ∧ q X ≤ K) :
    ∃ F : Configuration (n + 1) → ℝ, ∃ hF : Measurable F,
    ∃ hbF : ∀ X, 0 ≤ F X ∧ F X ≤ max K 0,
      F =ᵐ[labelGibbsMeasure hJ η β] q ∧
      (∫ X, F X ∂labelGibbsMeasure hJ η β) = 1 ∧
      Q = normalizedTilt (labelGibbsMeasure hJ η β) F ∧
      klDiv Q (labelGibbsMeasure hJ η β) ≠ ∞ ∧
      let κ := fun i => PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
        (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
      letI : ∀ i, IsMarkovKernel (κ i) := fun i =>
        PositiveProductConditionals.isMarkovKernel_conditionalKernel _ _ _ _ i
      let ψ := fun i => conditionalTiltKernel (κ i) (F ∘ (configurationSplit i).symm)
        (hF.comp (configurationSplit i).symm.measurable)
        (fun Y z => hbF ((configurationSplit i).symm (Y,z)))
      (∀ i, (Q.map (removeSite i)) ⊗ₘ ψ i = Q.map (configurationSplit i)) ∧
      (∀ i Y, klDiv (ψ i Y) (κ i Y) ≠ ∞) ∧
      (∀ i, Integrable (fun Y => (klDiv (ψ i Y) (κ i Y)).toReal) (Q.map (removeSite i))) ∧
      (1 / 2 : ℝ) * (klDiv Q (labelGibbsMeasure hJ η β)).toReal - defectConstant J β₀ C₂ ≤
        ∑ i, ∫ Y, (klDiv (ψ i Y) (κ i Y)).toReal ∂Q.map (removeSite i) := by
  let P := labelGibbsMeasure hJ η β
  let : IsProbabilityMeasure P :=
    isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ (hβle.trans_lt hsub)
  obtain ⟨F, hF, hbF, he, hS, hQF⟩ := bounded_probability_representative P Q hq hQ hb
  have hS' : (∫ X, F X ∂labelGibbsMeasure hJ η β) = 1 := hS
  have hQ' : normalizedTilt (labelGibbsMeasure hJ η β) F = Q := hQF.symm
  have hSpos : 0 < ∫ X, F X ∂P := by rw [hS]; norm_num
  have hc := source_normalized_tilt_comparison hJ hN hβ hβle hsub hC hk hmesh μ η ht hη hcap
    hformula hdensity hmeshC htC hF hbF hSpos
  have hr := source_normalized_tilt_reduction hJ hN hβ hβle hsub hC hk hmesh μ η ht hη hcap
    hformula hdensity hmeshC htC hF hbF hSpos
  dsimp only at hc
  rw [hQ'] at hc hr
  have hQdens : Q = P.withDensity (fun X => ENNReal.ofReal (F X)) := by
    simpa only [normalizedTilt, hS, div_one] using hQF
  have hF0 : ∀ᵐ X ∂P, 0 ≤ F X := Eventually.of_forall fun X => (hbF X).1
  have hlog : Integrable (fun X => Real.log (F X)) Q := by
    simpa only [hS', div_one] using! hc.1
  have hfin := klDiv_ne_top_of_log_density hQdens hF hF0 hlog
  have hKL := toReal_klDiv_eq_log_density hQdens hF hF0 hlog
  refine ⟨F, hF, hbF, he, hS, hQF, hfin, ?_⟩
  let κ (i : Fin (n + 1)) := PositiveProductConditionals.conditionalKernel
    (μ (η i)) (referenceTilt μ η β) (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
  let (i : Fin (n + 1)) : IsMarkovKernel (κ i) :=
    PositiveProductConditionals.isMarkovKernel_conditionalKernel _ _ _ _ _
  let F' (i : Fin (n + 1)) := F ∘ (configurationSplit i).symm
  have hf (i : Fin (n + 1)) : Measurable (F' i) := hF.comp (configurationSplit i).symm.measurable
  have hfb (i : Fin (n + 1)) : ∀ Y z, 0 ≤ F' i (Y,z) ∧ F' i (Y,z) ≤ max K 0 :=
    fun Y z => hbF ((configurationSplit i).symm (Y,z))
  let ψ (i : Fin (n + 1)) := conditionalTiltKernel (κ i) (F' i) (hf i) (hfb i)
  let L (i : Fin (n + 1)) := conditionalLogEntropy (κ i) (F' i)
  have hdata (i : Fin (n + 1)) := source_tilt_disintegration hJ hN μ η hβ
    (hβle.trans_lt hsub) hformula hF hbF hSpos i
  have hd (i : Fin (n + 1)) : (Q.map (removeSite i)) ⊗ₘ ψ i = Q.map (configurationSplit i) := by
    simpa only [hQ'] using! (hdata i).2.1
  have hl (i : Fin (n + 1)) : Integrable (L i) (Q.map (removeSite i)) :=
    (integrable_map_measure (measurable_conditionalLogEntropy (κ i) (hf i) (hfb i)).aestronglyMeasurable
      (measurable_removeSite i).aemeasurable).mpr (hc.2.2.1 i)
  have hcost (i : Fin (n + 1)) (Y : Configuration n) :
      (klDiv (ψ i Y) (κ i Y)).toReal = L i Y := (conditionalTilt_kl (κ i) (hf i) (hfb i) Y).2
  have hcostI (i : Fin (n + 1)) :
      Integrable (fun Y => (klDiv (ψ i Y) (κ i Y)).toReal) (Q.map (removeSite i)) :=
    (hl i).congr (Eventually.of_forall fun Y => (hcost i Y).symm)
  have hcostE (i : Fin (n + 1)) :
      (∫ Y, (klDiv (ψ i Y) (κ i Y)).toReal ∂Q.map (removeSite i)) =
        ∫ X, L i (removeSite i X) ∂Q := by
    simp_rw [hcost]
    exact integral_map (measurable_removeSite i).aemeasurable (hl i).aestronglyMeasurable
  refine ⟨hd, fun i Y => (conditionalTilt_kl (κ i) (hf i) (hfb i) Y).1, hcostI, ?_⟩
  change (1 / 2 : ℝ) * (klDiv Q P).toReal - defectConstant J β₀ C₂ ≤
    ∑ i, ∫ Y, (klDiv (ψ i Y) (κ i Y)).toReal ∂Q.map (removeSite i)
  rw [hKL]
  simp only [hcostE]
  simpa only [hS', div_one] using! hr

end SourceBounds

end PeriodicAttractiveLogGas.SourceConditionalEntropyComparison
