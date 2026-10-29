import LeanResearch.PeriodicAttractiveLogGas.MovingPoleCalculus
import LeanResearch.PeriodicAttractiveLogGas.WeakChartCalculus
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Source-only continuation of manuscript Lemma 3.5.

The regularized numerator is an actual integral over the literal patch
reference probability. Its ordinary source derivative is proved by
differentiation under the integral on a compact tube. The capped moment
bounds and off-pole convergence then construct the approximation data
needed by `WeakChartCalculus`. There is no presumed weak chain rule,
Lipschitz representative, or derivative of the limiting integral.

Central elaboration and all verifier steps are pending for this candidate.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology ContDiff RealInnerProductSpace

namespace PeriodicAttractiveLogGas.MovingPoleNormalized

open MovingPoleIntegrability MovingPoleWeakLimit MovingPoleNumerators MovingPoleCharts
open MovingPoleCalculus GreenPointWeights MeshCells MeshAdjacentCells LabelOccupations
open ConditionalParameters WeakChartCalculus

variable {ι : Type*} [Fintype ι]

section CompactIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- Continuity only on the compact support of a finite measure suffices.
No measurability is imposed away from that support. -/
theorem integrable_of_continuousOn_compact {B : Set PlanarSpace} (hB : IsCompact B)
    {μ : Measure PlanarSpace} [IsFiniteMeasure μ] (hμ : ∀ᵐ z ∂μ, z ∈ B)
    {f : PlanarSpace → E} (hf : ContinuousOn f B) : Integrable f μ := by
  have hm := hf.aestronglyMeasurable (μ := μ) hB.measurableSet
  rw [Measure.restrict_eq_self_of_ae_mem hμ] at hm
  obtain ⟨C, _, hb⟩ := (hB.image_of_continuousOn hf).isBounded.exists_pos_norm_le
  exact Integrable.of_bound hm C (hμ.mono fun z hz ↦ hb (f z) (mem_image_of_mem f hz))

end CompactIntegral

/-- Actual parameter-integral differentiation on a compact integration
domain. The hypotheses concern the ordinary derivative of the integrand,
not the desired derivative of its integral. Compactness provides the
integrable derivative bound on a common source neighborhood. -/
theorem hasFDerivAt_integral_of_compact_tube
    {B : Set PlanarSpace} (hB : IsCompact B) {μ : Measure PlanarSpace}
    [IsFiniteMeasure μ] (hμ : ∀ᵐ z ∂μ, z ∈ B)
    {F : SourceSpace ι × PlanarSpace → ℝ}
    {G : SourceSpace ι × PlanarSpace → SourceSpace ι}
    {U : Set (SourceSpace ι × PlanarSpace)} (hU : IsOpen U)
    (hF : ContinuousOn F U) (hG : ContinuousOn G U)
    (hD : ∀ p ∈ U, HasFDerivAt (fun X ↦ F (X, p.2))
      (InnerProductSpace.toDual ℝ (SourceSpace ι) (G p)) p.1)
    {X : SourceSpace ι} (hX : {X} ×ˢ B ⊆ U) :
    HasFDerivAt (fun Y ↦ ∫ Z, F (Y, Z) ∂μ)
      (InnerProductSpace.toDual ℝ (SourceSpace ι) (∫ Z, G (X, Z) ∂μ)) X := by
  obtain ⟨V, W, hV, _, hXV, hBW, hVW⟩ :=
    generalized_tube_lemma isCompact_singleton hB hU hX
  have hXV' : X ∈ V := hXV (mem_singleton X)
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hXV')
  have hprod : Metric.closedBall X r ×ˢ B ⊆ U :=
    fun p hp ↦ hVW ⟨hball hp.1, hBW hp.2⟩
  have hcompact : IsCompact (Metric.closedBall X r ×ˢ B) := (isCompact_closedBall X r).prod hB
  obtain ⟨C, _, hC⟩ := (hcompact.image_of_continuousOn (hG.mono hprod)).isBounded.exists_pos_norm_le
  have hfibre (Y : SourceSpace ι) (hY : Y ∈ Metric.closedBall X r) :
      ContinuousOn (fun Z ↦ F (Y, Z)) B := by
    exact hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun Z hZ ↦ hprod ⟨hY, hZ⟩)
  have hgfibre : ContinuousOn (fun Z ↦ G (X, Z)) B :=
    hG.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun Z hZ ↦ hprod ⟨Metric.mem_closedBall_self hr.le, hZ⟩)
  have hFm : ∀ᶠ Y in 𝓝 X, AEStronglyMeasurable (fun Z ↦ F (Y, Z)) μ := by
    filter_upwards [Metric.closedBall_mem_nhds X hr] with Y hY
    exact (integrable_of_continuousOn_compact hB hμ (hfibre Y hY)).aestronglyMeasurable
  have hFi := integrable_of_continuousOn_compact hB hμ
    (hfibre X (Metric.mem_closedBall_self hr.le))
  have hGi := integrable_of_continuousOn_compact hB hμ hgfibre
  have hGm : AEStronglyMeasurable
      (fun Z ↦ InnerProductSpace.toDual ℝ (SourceSpace ι) (G (X, Z))) μ :=
    (InnerProductSpace.toDual ℝ (SourceSpace ι)).continuous.comp_aestronglyMeasurable
      hGi.aestronglyMeasurable
  have hb : ∀ᵐ Z ∂μ, ∀ Y ∈ Metric.closedBall X r,
      ‖InnerProductSpace.toDual ℝ (SourceSpace ι) (G (Y, Z))‖ ≤ C := by
    filter_upwards [hμ] with Z hZ
    intro Y hY
    rw [(InnerProductSpace.toDual ℝ (SourceSpace ι)).norm_map]
    exact hC _ (mem_image_of_mem _ ⟨hY, hZ⟩)
  have hd : ∀ᵐ Z ∂μ, ∀ Y ∈ Metric.closedBall X r,
      HasFDerivAt (fun Y ↦ F (Y, Z))
        (InnerProductSpace.toDual ℝ (SourceSpace ι) (G (Y, Z))) Y := by
    filter_upwards [hμ] with Z hZ
    exact fun Y hY ↦ hD (Y, Z) (hprod ⟨hY, hZ⟩)
  have hh := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (Metric.closedBall_mem_nhds X hr) hFm hFi hGm hb (integrable_const C) hd
  have he : (∫ Z, InnerProductSpace.toDual ℝ (SourceSpace ι) (G (X, Z)) ∂μ) =
      InnerProductSpace.toDual ℝ (SourceSpace ι) (∫ Z, G (X, Z) ∂μ) :=
    (InnerProductSpace.toDual ℝ (SourceSpace ι)).toLinearIsometry.integral_comp_comm (fun Z ↦ G (X, Z))
  exact hh.congr_fderiv he

def regularizedProductGradient (w : ι → ℝ) (J : ℕ) (a : MeshIndex J)
    (ε : ℝ) (hε : 0 < ε) (f : SourceSpace ι × PlanarSpace → ℝ)
    (p : SourceSpace ι × PlanarSpace) : SourceSpace ι :=
  smoothWeight w J a ε hε p • factorGradient f p +
    fullGradient (fun j ↦ f p • smoothGradient w J a ε hε j p)

def regularizedNumerator (w : ι → ℝ) (J : ℕ) (a : MeshIndex J) (b : Patch)
    (ε : ℝ) (hε : 0 < ε) (f : SourceSpace ι × PlanarSpace → ℝ)
    (X : SourceSpace ι) : ℝ :=
  ∫ Z, smoothWeight w J a ε hε (X, Z) * f (X, Z) ∂patchReference b

def regularizedNumeratorGradient (w : ι → ℝ) (J : ℕ) (a : MeshIndex J) (b : Patch)
    (ε : ℝ) (hε : 0 < ε) (f : SourceSpace ι × PlanarSpace → ℝ)
    (X : SourceSpace ι) : SourceSpace ι :=
  ∫ Z, regularizedProductGradient w J a ε hε f (X, Z) ∂patchReference b

theorem regularizedProductGradient_inner (w : ι → ℝ) (J : ℕ) (a : MeshIndex J)
    (ε : ℝ) (hε : 0 < ε) (f : SourceSpace ι × PlanarSpace → ℝ)
    (p : SourceSpace ι × PlanarSpace) (v : SourceSpace ι) :
    inner ℝ (regularizedProductGradient w J a ε hε f p) v =
      productD (smoothWeight w J a ε hε) (smoothGradient w J a ε hε) f v p := by
  simp only [regularizedProductGradient, inner_add_left, real_inner_smul_left,
    factorGradient_inner, fullGradient_inner, productD]
  congr 1
  exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

theorem continuousAt_regularizedProductGradient (w : ι → ℝ) (J : ℕ) (a : MeshIndex J)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ))
    {f : SourceSpace ι × PlanarSpace → ℝ} {p : SourceSpace ι × PlanarSpace}
    (hf : ContDiffAt ℝ 1 f p) : ContinuousAt (regularizedProductGradient w J a ε hε f) p := by
  have hD : ContinuousAt (factorGradient f) p :=
    (InnerProductSpace.toDual ℝ (SourceSpace ι)).symm.continuous.continuousAt.comp
      ((hf.continuousAt_fderiv one_ne_zero).clm_comp continuousAt_const)
  apply ((continuous_smoothWeight w J a ε hε).continuousAt.smul hD).add
  apply tendsto_finsetSum Finset.univ
  intro j _
  exact (sourceProjection j).adjoint.continuous.continuousAt.comp
    (hf.continuousAt.smul (continuous_smoothGradient w J a ε hε hs j).continuousAt)

theorem hasFDerivAt_regularizedProduct (w : ι → ℝ) (J : ℕ) (a : MeshIndex J)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ))
    {f : SourceSpace ι × PlanarSpace → ℝ} {X : SourceSpace ι} {Z : PlanarSpace}
    (hf : ContDiffAt ℝ 1 f (X, Z)) :
    HasFDerivAt (fun Y ↦ smoothWeight w J a ε hε (Y, Z) * f (Y, Z))
      (InnerProductSpace.toDual ℝ (SourceSpace ι)
        (regularizedProductGradient w J a ε hε f (X, Z))) X := by
  have hdf := hf.differentiableAt one_ne_zero
  have hdf' := hdf.hasFDerivAt.comp X (hasFDerivAt_prodMk_left (𝕜 := ℝ) X Z)
  have hw' := (hasFDerivAt_smoothWeight w J a ε hε hs Z X).differentiableAt.hasFDerivAt
  have hp := hw'.mul hdf'
  have he : InnerProductSpace.toDual ℝ (SourceSpace ι)
      (regularizedProductGradient w J a ε hε f (X, Z)) =
      smoothWeight w J a ε hε (X, Z) •
        ((fderiv ℝ f (X, Z)).comp (ContinuousLinearMap.inl ℝ (SourceSpace ι) PlanarSpace)) +
      f (X, Z) • fderiv ℝ (fun Y ↦ smoothWeight w J a ε hε (Y, Z)) X := by
    ext v
    rw [InnerProductSpace.toDual_apply_apply, regularizedProductGradient_inner]
    simp only [productD, add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, smul_eq_mul]
    rw [← Finset.sum_mul, ← fderiv_smoothWeight_apply w J a ε hε hs Z X v]
    simp only [sourceD]
    ring
  rw [he]
  convert hp using 1 <;> rfl

/-- No differentiation-under-the-integral premise remains: neighborhood
smoothness of the actual factor and the compact tube give that derivative. -/
theorem hasFDerivAt_regularizedNumerator (w : ι → ℝ) (J : ℕ) (a : MeshIndex J) (b : Patch)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ))
    {S : Set (SourceSpace ι)} {f : SourceSpace ι × PlanarSpace → ℝ}
    (hf : SmoothOnChart S (patchClosed b) f) {X : SourceSpace ι} (hX : X ∈ S) :
    HasFDerivAt (regularizedNumerator w J a b ε hε f)
      (InnerProductSpace.toDual ℝ (SourceSpace ι)
        (regularizedNumeratorGradient w J a b ε hε f X)) X := by
  obtain ⟨U, hU, hSU, hfu⟩ := hf
  unfold regularizedNumerator regularizedNumeratorGradient
  apply hasFDerivAt_integral_of_compact_tube (F := fun p ↦ smoothWeight w J a ε hε p * f p)
    (G := regularizedProductGradient w J a ε hε f)
    (isCompact_patchClosed b) (ae_mem_patchClosed b) hU
  · exact (continuous_smoothWeight w J a ε hε).continuousOn.mul hfu.continuousOn
  · intro p hp
    exact (continuousAt_regularizedProductGradient w J a ε hε hs
      (hfu.contDiffAt (hU.mem_nhds hp))).continuousWithinAt
  · intro p hp
    exact hasFDerivAt_regularizedProduct w J a ε hε hs (hfu.contDiffAt (hU.mem_nhds hp))
  · rintro ⟨Y, Z⟩ ⟨hY, hZ⟩
    simp only [mem_singleton_iff] at hY
    subst Y
    exact hSU ⟨hX, hZ⟩

/-- Pullback of the checked physical three-halves bounds through the
literal patch map. The constants are uniform in every source placement
and in the mollifier scale. -/
theorem capped_reference_bounds (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (X : SourceSpace I) (η : LabelVector J N)
    (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (hX : ∀ i ∈ I, extendedSources I X i ∈ closure (meshCell J hJ (η i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) :
    MemLp (fun Z ↦ smoothWeight (fun i : I ↦ w i) J a ε hε (X, Z))
        (ENNReal.ofReal (3 / 2 : ℝ)) (patchReference b) ∧
      lpNorm (fun Z ↦ smoothWeight (fun i : I ↦ w i) J a ε hε (X, Z))
        (ENNReal.ofReal (3 / 2 : ℝ)) (patchReference b) ≤
          weightConstant K β₀ J (nearRadius β₀ C₁) * normConstant ∧
      ∀ j : I, MemLp (fun Z ↦ smoothGradient (fun i : I ↦ w i) J a ε hε j (X, Z))
        (ENNReal.ofReal (3 / 2 : ℝ)) (patchReference b) ∧
      lpNorm (fun Z ↦ smoothGradient (fun i : I ↦ w i) J a ε hε j (X, Z))
        (ENNReal.ofReal (3 / 2 : ℝ)) (patchReference b) ≤
          sourceNormBound K β₀ J (nearRadius β₀ C₁) := by
  have hm := capped_mesh_bounds K hJ hN hβ hβ₀ hC₀ hmesh η hη I (extendedSources I X) hX
    w hw₀ hw a b ε hε hs
  simp only [extendedSources_subtype] at hm
  have hmp := measurePreserving_patch J hJ a b
  have heW : eLpNorm (fun Z ↦ smoothWeight (fun i : I ↦ w i) J a ε hε (X, Z))
      (ENNReal.ofReal (3 / 2 : ℝ)) (patchReference b) =
      eLpNorm (regularizedTorusWeight (sources X) (fun i : I ↦ w i) ε hε)
        (ENNReal.ofReal (3 / 2 : ℝ)) (patchMeasure J hJ a b) := by
    simpa only [Function.comp_def, smoothWeight] using eLpNorm_comp_measurePreserving
      (continuous_regularizedTorusWeight (sources X) (fun i : I ↦ w i) ε hε).aestronglyMeasurable
      hmp (p := ENNReal.ofReal (3 / 2 : ℝ))
  refine ⟨?_, ?_, fun j ↦ ?_⟩
  · change eLpNorm _ _ _ < (∞ : ℝ≥0∞)
    rw [heW]
    exact hm.1
  · change (eLpNorm _ _ _).toReal ≤ _
    rw [heW]
    exact hm.2.1
  · have heG : eLpNorm (fun Z ↦ smoothGradient (fun i : I ↦ w i) J a ε hε j (X, Z))
        (ENNReal.ofReal (3 / 2 : ℝ)) (patchReference b) =
        eLpNorm (regularizedSourceGradient (sources X) (fun i : I ↦ w i) ε hε j)
          (ENNReal.ofReal (3 / 2 : ℝ)) (patchMeasure J hJ a b) := by
      simpa only [Function.comp_def, smoothGradient] using eLpNorm_comp_measurePreserving
        (continuous_regularizedSourceGradient (sources X) (fun i : I ↦ w i) ε hε hs j).aestronglyMeasurable
        hmp (p := ENNReal.ofReal (3 / 2 : ℝ))
    constructor
    · change eLpNorm _ _ _ < (∞ : ℝ≥0∞)
      rw [heG]
      exact (hm.2.2 j).1
    · change (eLpNorm _ _ _).toReal ≤ _
      rw [heG]
      exact (hm.2.2 j).2

structure FibreL1Data (w : ι → ℝ) (J : ℕ) (a : MeshIndex J) (b : Patch)
    (X : SourceSpace ι) : Prop where
  smooth_weight : ∀ n, Integrable (fun Z ↦ smoothWeight w J a
    (approximationScale n) (approximationScale_pos n) (X, Z)) (patchReference b)
  smooth_gradient : ∀ n j, Integrable (fun Z ↦ smoothGradient w J a
    (approximationScale n) (approximationScale_pos n) j (X, Z)) (patchReference b)
  weight_integrable : Integrable (fun Z ↦ weight w J a (X, Z)) (patchReference b)
  gradient_integrable : ∀ j, Integrable (fun Z ↦ gradient w J a j (X, Z)) (patchReference b)
  weight_limit : Tendsto (fun n ↦ eLpNorm (fun Z ↦
    smoothWeight w J a (approximationScale n) (approximationScale_pos n) (X, Z) -
      weight w J a (X, Z)) 1 (patchReference b)) atTop (𝓝 0)
  gradient_limit : ∀ j, Tendsto (fun n ↦ eLpNorm (fun Z ↦
    smoothGradient w J a (approximationScale n) (approximationScale_pos n) j (X, Z) -
      gradient w J a j (X, Z)) 1 (patchReference b)) atTop (𝓝 0)

/-- Vitali is applied at each fixed placement, with no exclusion of
coincident sources. Only integration-variable collisions are removed by
the actual quotient probability measure's null singleton property. -/
theorem capped_fibreL1Data (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (X : SourceSpace I) (η : LabelVector J N)
    (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (hX : ∀ i ∈ I, extendedSources I X i ∈ closure (meshCell J hJ (η i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) : FibreL1Data (fun i : I ↦ w i) J a b X := by
  have hb (n : ℕ) := capped_reference_bounds K hJ hN hβ hβ₀ hC₀ hmesh I X η hη hX
    w hw₀ hw a b (approximationScale n) (approximationScale_pos n) (approximationScale_small n)
  have huW := uniformIntegrable_of_three_halves_bound
    (mul_nonneg (weightConstant_pos K β₀ J (nearRadius β₀ C₁)).le normConstant_nonneg)
    (fun n ↦ (hb n).1) (fun n ↦ (hb n).2.1)
  have huG (j : I) := uniformIntegrable_of_three_halves_bound
    (sourceNormBound_nonneg K (hβ.trans hβ₀) (by positivity) (by positivity))
    (fun n ↦ ((hb n).2.2 j).1) (fun n ↦ ((hb n).2.2 j).2)
  have hac := patchMeasure_absolutelyContinuous hJ (by omega) a b
  have hcoll : ∀ᵐ z ∂patchMeasure J hJ a b, ∀ i : I, z - sources X i ≠ 0 := by
    rw [ae_all_iff]
    intro i
    exact ((torusMeasure.ae_ne (sources X i)).filter_mono hac.ae_le).mono
      fun z hz ↦ sub_ne_zero.mpr hz
  have hcoll' := (measurePreserving_patch J hJ a b).quasiMeasurePreserving.ae hcoll
  have hlW := integrable_and_tendsto_L1_of_uniformIntegrable huW
    (hcoll'.mono fun Z hZ ↦ tendsto_weight approximationScale_pos approximationScale_small
      approximationScale_tendsto (sources X) (fun i : I ↦ w i) (meshChart J a Z) hZ)
  have hlG (j : I) := integrable_and_tendsto_L1_of_uniformIntegrable (huG j)
    (hcoll'.mono fun Z hZ ↦ tendsto_sourceGradient approximationScale_pos approximationScale_small
      approximationScale_tendsto (sources X) (fun i : I ↦ w i) j (meshChart J a Z) hZ)
  exact ⟨fun n ↦ memLp_one_iff_integrable.mp (huW.memLp n),
    fun n j ↦ memLp_one_iff_integrable.mp ((huG j).memLp n),
    hlW.1, fun j ↦ (hlG j).1, hlW.2, fun j ↦ (hlG j).2⟩

section L1Products

variable {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure A}

omit [CompleteSpace E] in
theorem tendsto_integral_smul_of_L1 {f : ℕ → A → ℝ} {g : A → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hg : Integrable g μ)
    (ht : Tendsto (fun n ↦ eLpNorm (f n - g) 1 μ) atTop (𝓝 0))
    (D : A → E) (hD : AEStronglyMeasurable D μ) {C : ℝ}
    (hb : ∀ᵐ x ∂μ, ‖D x‖ ≤ C) :
    Tendsto (fun n ↦ ∫ x, f n x • D x ∂μ) atTop (𝓝 (∫ x, g x • D x ∂μ)) := by
  have hi (n : ℕ) := (hf n).smul_bdd C hD hb
  have hig := hg.smul_bdd C hD hb
  apply tendsto_integral_of_L1' _ (Eventually.of_forall hi)
  have hbound (n : ℕ) : eLpNorm (fun x ↦ f n x • D x - g x • D x) 1 μ ≤
      ENNReal.ofReal C * eLpNorm (f n - g) 1 μ := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul ((hi n).sub hig).aestronglyMeasurable
    filter_upwards [hb] with x hx
    change ‖f n x • D x - g x • D x‖ ≤ C * ‖f n x - g x‖
    rw [← sub_smul, norm_smul, mul_comm C]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [mul_zero] using
      (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) ht (Or.inr ENNReal.ofReal_ne_top)))
    (fun _ ↦ bot_le) hbound

omit [CompleteSpace E] in
theorem tendsto_integral_bounded_smul_of_L1 {F : ℕ → A → E} {G : A → E}
    (hF : ∀ n, Integrable (F n) μ) (hG : Integrable G μ)
    (ht : Tendsto (fun n ↦ eLpNorm (F n - G) 1 μ) atTop (𝓝 0))
    (f : A → ℝ) (hf : AEStronglyMeasurable f μ) {C : ℝ}
    (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    Tendsto (fun n ↦ ∫ x, f x • F n x ∂μ) atTop (𝓝 (∫ x, f x • G x ∂μ)) := by
  have hi (n : ℕ) := (hF n).bdd_smul C hf hb
  have hig := hG.bdd_smul C hf hb
  apply tendsto_integral_of_L1' _ (Eventually.of_forall hi)
  have hbound (n : ℕ) : eLpNorm (fun x ↦ f x • F n x - f x • G x) 1 μ ≤
      ENNReal.ofReal C * eLpNorm (F n - G) 1 μ := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul ((hi n).sub hig).aestronglyMeasurable
    filter_upwards [hb] with x hx
    change ‖f x • F n x - f x • G x‖ ≤ C * ‖F n x - G x‖
    rw [← smul_sub, norm_smul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [mul_zero] using
      (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) ht (Or.inr ENNReal.ofReal_ne_top)))
    (fun _ ↦ bot_le) hbound

end L1Products

theorem local_factor_bounds {S : Set (SourceSpace ι)} (hS : IsCompact S) (b : Patch)
    {f : SourceSpace ι × PlanarSpace → ℝ} (hf : SmoothOnChart S (patchClosed b) f) :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧ ∀ X ∈ S, ∀ Z ∈ patchClosed b,
      ‖f (X, Z)‖ ≤ A ∧ ‖factorGradient f (X, Z)‖ ≤ D := by
  obtain ⟨A, hA, hbA⟩ := ((hS.prod (isCompact_patchClosed b)).image_of_continuousOn
    hf.continuousOn).isBounded.exists_pos_norm_le
  obtain ⟨D, hD, hbD⟩ := ((hS.prod (isCompact_patchClosed b)).image_of_continuousOn
    hf.continuousOn_factorGradient).isBounded.exists_pos_norm_le
  exact ⟨A, D, hA, hD, fun X hX Z hZ ↦
    ⟨hbA _ (mem_image_of_mem _ ⟨hX, hZ⟩), hbD _ (mem_image_of_mem _ ⟨hX, hZ⟩)⟩⟩

theorem factor_fibre_measurable {S : Set (SourceSpace ι)} (b : Patch)
    {f : SourceSpace ι × PlanarSpace → ℝ} (hf : SmoothOnChart S (patchClosed b) f)
    {X : SourceSpace ι} (hX : X ∈ S) :
    AEStronglyMeasurable (fun Z ↦ f (X, Z)) (patchReference b) ∧
      AEStronglyMeasurable (fun Z ↦ factorGradient f (X, Z)) (patchReference b) := by
  have hfC : ContinuousOn (fun Z ↦ f (X, Z)) (patchClosed b) :=
    hf.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hZ ↦ ⟨hX, hZ⟩)
  have hDC : ContinuousOn (fun Z ↦ factorGradient f (X, Z)) (patchClosed b) :=
    hf.continuousOn_factorGradient.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hZ ↦ ⟨hX, hZ⟩)
  exact ⟨(integrable_of_continuousOn_compact (isCompact_patchClosed b) (ae_mem_patchClosed b) hfC).1,
    (integrable_of_continuousOn_compact (isCompact_patchClosed b) (ae_mem_patchClosed b) hDC).1⟩

theorem integral_regularizedProductGradient (w : ι → ℝ) (J : ℕ) (a : MeshIndex J) (b : Patch)
    (ε : ℝ) (hε : 0 < ε) {f : SourceSpace ι × PlanarSpace → ℝ} (X : SourceSpace ι)
    (hW : Integrable (fun Z ↦ smoothWeight w J a ε hε (X, Z)) (patchReference b))
    (hG : ∀ j, Integrable (fun Z ↦ smoothGradient w J a ε hε j (X, Z)) (patchReference b))
    {A D : ℝ} (hfm : AEStronglyMeasurable (fun Z ↦ f (X, Z)) (patchReference b))
    (hDm : AEStronglyMeasurable (fun Z ↦ factorGradient f (X, Z)) (patchReference b))
    (hbF : ∀ᵐ Z ∂patchReference b, ‖f (X, Z)‖ ≤ A)
    (hbD : ∀ᵐ Z ∂patchReference b, ‖factorGradient f (X, Z)‖ ≤ D) :
    regularizedNumeratorGradient w J a b ε hε f X =
      (∫ Z, smoothWeight w J a ε hε (X, Z) • factorGradient f (X, Z) ∂patchReference b) +
        fullGradient (fun j ↦ ∫ Z, f (X, Z) • smoothGradient w J a ε hε j (X, Z) ∂patchReference b) := by
  unfold regularizedNumeratorGradient regularizedProductGradient
  have hiW : Integrable (fun Z ↦ smoothWeight w J a ε hε (X, Z) • factorGradient f (X, Z))
      (patchReference b) := hW.smul_bdd D hDm hbD
  have hiG (j : ι) : Integrable (fun Z ↦ f (X, Z) • smoothGradient w J a ε hε j (X, Z))
      (patchReference b) := (hG j).bdd_smul A hfm hbF
  rw [integral_add hiW (integrable_fullGradient hiG), integral_fullGradient hiG]

theorem integral_productGradient (w : ι → ℝ) (J : ℕ) (a : MeshIndex J) (b : Patch)
    {f : SourceSpace ι × PlanarSpace → ℝ} (X : SourceSpace ι)
    (hW : Integrable (fun Z ↦ weight w J a (X, Z)) (patchReference b))
    (hG : ∀ j, Integrable (fun Z ↦ gradient w J a j (X, Z)) (patchReference b))
    {A D : ℝ} (hfm : AEStronglyMeasurable (fun Z ↦ f (X, Z)) (patchReference b))
    (hDm : AEStronglyMeasurable (fun Z ↦ factorGradient f (X, Z)) (patchReference b))
    (hbF : ∀ᵐ Z ∂patchReference b, ‖f (X, Z)‖ ≤ A)
    (hbD : ∀ᵐ Z ∂patchReference b, ‖factorGradient f (X, Z)‖ ≤ D) :
    numeratorGradient w J a b f X =
      (∫ Z, weight w J a (X, Z) • factorGradient f (X, Z) ∂patchReference b) +
        fullGradient (fun j ↦ ∫ Z, f (X, Z) • gradient w J a j (X, Z) ∂patchReference b) := by
  unfold numeratorGradient productGradient
  have hiW : Integrable (fun Z ↦ weight w J a (X, Z) • factorGradient f (X, Z))
      (patchReference b) := hW.smul_bdd D hDm hbD
  have hiG (j : ι) : Integrable (fun Z ↦ f (X, Z) • gradient w J a j (X, Z))
      (patchReference b) := (hG j).bdd_smul A hfm hbF
  rw [integral_add hiW (integrable_fullGradient hiG), integral_fullGradient hiG]

/-- Both actual parameter integrals converge at every fixed source point;
in particular the limiting vector is the integral of the literal proposed
physical product-gradient field. -/
theorem numerator_limits (w : ι → ℝ) (J : ℕ) (a : MeshIndex J) (b : Patch)
    {S : Set (SourceSpace ι)} (hS : IsCompact S)
    {f : SourceSpace ι × PlanarSpace → ℝ} (hf : SmoothOnChart S (patchClosed b) f)
    {X : SourceSpace ι} (hX : X ∈ S) (hL : FibreL1Data w J a b X) :
    Tendsto (fun n ↦ regularizedNumerator w J a b
      (approximationScale n) (approximationScale_pos n) f X) atTop (𝓝 (numerator w J a b f X)) ∧
    Tendsto (fun n ↦ regularizedNumeratorGradient w J a b
      (approximationScale n) (approximationScale_pos n) f X) atTop (𝓝 (numeratorGradient w J a b f X)) := by
  obtain ⟨A, D, _, _, hb⟩ := local_factor_bounds hS b hf
  obtain ⟨hfm, hDm⟩ := factor_fibre_measurable b hf hX
  have hbF := (ae_mem_patchClosed b).mono fun Z hZ ↦ (hb X hX Z hZ).1
  have hbD := (ae_mem_patchClosed b).mono fun Z hZ ↦ (hb X hX Z hZ).2
  refine ⟨tendsto_integral_mul_of_L1 hL.smooth_weight hL.weight_integrable hL.weight_limit
    (fun Z ↦ f (X, Z)) hfm hbF, ?_⟩
  have hD := tendsto_integral_smul_of_L1 hL.smooth_weight hL.weight_integrable hL.weight_limit
    (fun Z ↦ factorGradient f (X, Z)) hDm hbD
  have hG (j : ι) := tendsto_integral_bounded_smul_of_L1 (fun n ↦ hL.smooth_gradient n j)
    (hL.gradient_integrable j) (hL.gradient_limit j) (fun Z ↦ f (X, Z)) hfm hbF
  have hsum := tendsto_finsetSum (Finset.univ : Finset ι) fun j _ ↦
    (sourceProjection j).adjoint.continuous.continuousAt.tendsto.comp (hG j)
  have hh := hD.add hsum
  have he (n : ℕ) := integral_regularizedProductGradient w J a b
    (approximationScale n) (approximationScale_pos n) X (hL.smooth_weight n)
    (hL.smooth_gradient n) hfm hDm hbF hbD
  have he0 := integral_productGradient w J a b X hL.weight_integrable hL.gradient_integrable
    hfm hDm hbF hbD
  simp_rw [he, he0, fullGradient]
  exact hh

theorem regularized_numerator_bounds (w : ι → ℝ) (J : ℕ) (a : MeshIndex J) (b : Patch)
    (ε : ℝ) (hε : 0 < ε) {f : SourceSpace ι × PlanarSpace → ℝ} (X : SourceSpace ι)
    {A D CW CG : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hW : Integrable (fun Z ↦ smoothWeight w J a ε hε (X, Z)) (patchReference b))
    (hG : ∀ j, Integrable (fun Z ↦ smoothGradient w J a ε hε j (X, Z)) (patchReference b))
    (hfm : AEStronglyMeasurable (fun Z ↦ f (X, Z)) (patchReference b))
    (hDm : AEStronglyMeasurable (fun Z ↦ factorGradient f (X, Z)) (patchReference b))
    (hbF : ∀ᵐ Z ∂patchReference b, ‖f (X, Z)‖ ≤ A)
    (hbD : ∀ᵐ Z ∂patchReference b, ‖factorGradient f (X, Z)‖ ≤ D)
    (hWb : (∫ Z, ‖smoothWeight w J a ε hε (X, Z)‖ ∂patchReference b) ≤ CW)
    (hGb : ∀ j, (∫ Z, ‖smoothGradient w J a ε hε j (X, Z)‖ ∂patchReference b) ≤ CG) :
    ‖regularizedNumerator w J a b ε hε f X‖ ≤ A * CW ∧
      ‖regularizedNumeratorGradient w J a b ε hε f X‖ ≤
        D * CW + ∑ j : ι, ‖(sourceProjection j).adjoint‖ * (A * CG) := by
  constructor
  · change ‖∫ Z, smoothWeight w J a ε hε (X, Z) • f (X, Z) ∂patchReference b‖ ≤ _
    exact (norm_integral_smul_bounded hW hbF).trans (mul_le_mul_of_nonneg_left hWb hA)
  · rw [integral_regularizedProductGradient w J a b ε hε X hW hG hfm hDm hbF hbD]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact (norm_integral_smul_bounded hW hbD).trans (mul_le_mul_of_nonneg_left hWb hD)
    · apply (norm_fullGradient_le _).trans
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_integral_bounded_smul (hG j) hbF).trans
        (mul_le_mul_of_nonneg_left (hGb j) hA)

def valueBound (K : KernelBounds) (β₀ J C₁ A : ℝ) : ℝ :=
  A * (weightConstant K β₀ J (nearRadius β₀ C₁) * normConstant)

def gradientBound (ι : Type*) [Fintype ι] (K : KernelBounds) (β₀ J C₁ A D : ℝ) : ℝ :=
  D * (weightConstant K β₀ J (nearRadius β₀ C₁) * normConstant) +
    ∑ j : ι, ‖(sourceProjection j).adjoint‖ * (A * sourceNormBound K β₀ J (nearRadius β₀ C₁))

theorem valueBound_nonneg (K : KernelBounds) (β₀ J C₁ : ℝ) {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ valueBound K β₀ J C₁ A :=
  mul_nonneg hA (mul_nonneg (weightConstant_pos K β₀ J (nearRadius β₀ C₁)).le normConstant_nonneg)

theorem gradientBound_nonneg (K : KernelBounds) {β₀ J C₁ A D : ℝ}
    (hβ₀ : 0 ≤ β₀) (hJ : 0 ≤ J) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    0 ≤ gradientBound ι K β₀ J C₁ A D := by
  apply add_nonneg (valueBound_nonneg K β₀ J C₁ hD)
  exact Finset.sum_nonneg fun _ _ ↦ mul_nonneg (norm_nonneg _)
    (mul_nonneg hA (sourceNormBound_nonneg K hβ₀ hJ (by positivity)))

/-- Explicit construction of the approximation data from the actual Green
weights, the actual occupation cap and local C1 regularity of the factor.
In particular none of its analytic limiting conclusions is a premise. -/
def cappedApproximation (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (S : Set (SourceSpace I)) (hS : IsCompact S)
    (η : SourceSpace I → LabelVector J N)
    (hη : ∀ X ∈ S, OccupationCap (fixedDelta β₀ C₀ C₁) (η X))
    (hX : ∀ X ∈ S, ∀ i ∈ I, extendedSources I X i ∈ closure (meshCell J hJ (η X i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) {f : SourceSpace I × PlanarSpace → ℝ}
    (hf : SmoothOnChart S (patchClosed b) f) {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hb : ∀ X ∈ S, ∀ Z ∈ patchClosed b, ‖f (X, Z)‖ ≤ A ∧ ‖factorGradient f (X, Z)‖ ≤ D) :
    BoundedGradientApproximation S (numerator (fun i : I ↦ w i) J a b f)
      (numeratorGradient (fun i : I ↦ w i) J a b f)
      (valueBound K β₀ J C₁ A) (gradientBound I K β₀ J C₁ A D) where
  value n := regularizedNumerator (fun i : I ↦ w i) J a b
    (approximationScale n) (approximationScale_pos n) f
  gradient n := regularizedNumeratorGradient (fun i : I ↦ w i) J a b
    (approximationScale n) (approximationScale_pos n) f
  nonneg_value_bound := valueBound_nonneg K β₀ J C₁ hA
  nonneg_gradient_bound := gradientBound_nonneg K (hβ.trans hβ₀) (by positivity) hA hD
  derivative n X hXS := hasFDerivAt_regularizedNumerator _ J a b
    (approximationScale n) (approximationScale_pos n) (approximationScale_small n) hf hXS
  value_bound n X hXS := by
    have hp := capped_reference_bounds K hJ hN hβ hβ₀ hC₀ hmesh I X (η X) (hη X hXS)
      (hX X hXS) w hw₀ hw a b (approximationScale n) (approximationScale_pos n)
      (approximationScale_small n)
    obtain ⟨hfm, hDm⟩ := factor_fibre_measurable b hf hXS
    have hW := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2 : ℝ)) hp.1
    have hG (j : I) := MemLp.integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2 : ℝ)) (hp.2.2 j).1
    exact (regularized_numerator_bounds _ J a b (approximationScale n) (approximationScale_pos n)
      X hA hD hW hG hfm hDm
      ((ae_mem_patchClosed b).mono fun Z hZ ↦ (hb X hXS Z hZ).1)
      ((ae_mem_patchClosed b).mono fun Z hZ ↦ (hb X hXS Z hZ).2)
      ((integral_norm_le_lpNorm (by norm_num) hp.1).trans hp.2.1)
      (fun j ↦ (integral_norm_le_lpNorm (by norm_num) (hp.2.2 j).1).trans (hp.2.2 j).2)).1
  gradient_bound n X hXS := by
    have hp := capped_reference_bounds K hJ hN hβ hβ₀ hC₀ hmesh I X (η X) (hη X hXS)
      (hX X hXS) w hw₀ hw a b (approximationScale n) (approximationScale_pos n)
      (approximationScale_small n)
    obtain ⟨hfm, hDm⟩ := factor_fibre_measurable b hf hXS
    have hW := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2 : ℝ)) hp.1
    have hG (j : I) := MemLp.integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2 : ℝ)) (hp.2.2 j).1
    exact (regularized_numerator_bounds _ J a b (approximationScale n) (approximationScale_pos n)
      X hA hD hW hG hfm hDm
      ((ae_mem_patchClosed b).mono fun Z hZ ↦ (hb X hXS Z hZ).1)
      ((ae_mem_patchClosed b).mono fun Z hZ ↦ (hb X hXS Z hZ).2)
      ((integral_norm_le_lpNorm (by norm_num) hp.1).trans hp.2.1)
      (fun j ↦ (integral_norm_le_lpNorm (by norm_num) (hp.2.2 j).1).trans (hp.2.2 j).2)).2
  value_limit X hXS := (numerator_limits _ J a b hS hf hXS
    (capped_fibreL1Data K hJ hN hβ hβ₀ hC₀ hmesh I X (η X) (hη X hXS) (hX X hXS)
      w hw₀ hw a b)).1
  gradient_limit X hXS := (numerator_limits _ J a b hS hf hXS
    (capped_fibreL1Data K hJ hN hβ hβ₀ hC₀ hmesh I X (η X) (hη X hXS) (hX X hXS)
      w hw₀ hw a b)).2

theorem factorGradient_one (p : SourceSpace ι × PlanarSpace) :
    factorGradient (fun _ ↦ (1 : ℝ)) p = 0 := by
  simp [factorGradient]

theorem regularized_normalizer_lower (w : ι → ℝ) (J : ℕ) (a : MeshIndex J) (b : Patch)
    {β₀ : ℝ} (hw : ∀ i, 0 ≤ w i) (ht : ∑ i, w i ≤ β₀)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) (X : SourceSpace ι) :
    normalizerLower β₀ ≤ regularizedNumerator w J a b ε hε (fun _ ↦ 1) X := by
  have hi : Integrable (fun Z ↦ smoothWeight w J a ε hε (X, Z)) (patchReference b) :=
    integrable_of_continuousOn_compact (isCompact_patchClosed b) (ae_mem_patchClosed b)
      ((continuous_smoothWeight w J a ε hε).comp (continuous_const.prodMk continuous_id)).continuousOn
  have hh := integral_mono_ae (integrable_const (normalizerLower β₀)) hi
    (ae_of_all _ fun Z ↦ regularizedTorusWeight_lower (sources X) w hw ht ε hε hs (meshChart J a Z))
  simpa only [regularizedNumerator, mul_one, integral_const, probReal_univ, one_smul] using hh

def referenceNormalizer (w : ι → ℝ) (J : ℕ) (a : MeshIndex J) (b : Patch) : SourceSpace ι → ℝ :=
  numerator w J a b (fun _ ↦ 1)

def referenceNormalizerGradient (w : ι → ℝ) (J : ℕ) (a : MeshIndex J) (b : Patch) :
    SourceSpace ι → SourceSpace ι := numeratorGradient w J a b (fun _ ↦ 1)

/-- Fully instantiated weak logarithm and normalized numerator on any
compact convex physical chart whose actual labels satisfy the cap.
The coefficient interval includes every allowed deletion and zero coupling.
The constants may depend on this fixed chart, as in the manuscript proof. -/
theorem capped_reference_log_quotient (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (S : Set (SourceSpace I)) (hS : IsCompact S) (hconv : Convex ℝ S)
    (η : SourceSpace I → LabelVector J N)
    (hη : ∀ X ∈ S, OccupationCap (fixedDelta β₀ C₀ C₁) (η X))
    (hX : ∀ X ∈ S, ∀ i ∈ I, extendedSources I X i ∈ closure (meshCell J hJ (η X i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) {f : SourceSpace I × PlanarSpace → ℝ}
    (hf : SmoothOnChart S (patchClosed b) f) :
    let w' : I → ℝ := fun i ↦ w i
    let u := referenceNormalizer w' J a b
    let U := referenceNormalizerGradient w' J a b
    let v := numerator w' J a b f
    let V := numeratorGradient w' J a b f
    (∀ X ∈ S, 0 < u X) ∧
      WeakGradientOn S (fun X ↦ Real.log (u X)) (logGradient u U) ∧
      WeakGradientOn S (fun X ↦ v X / u X) (quotientGradient u v U V) ∧
      ∃ Clog Cquot : ℝ≥0, LipschitzOnWith Clog (fun X ↦ Real.log (u X)) S ∧
        LipschitzOnWith Cquot (fun X ↦ v X / u X) S := by
  obtain ⟨A, D, hA, hD, hb⟩ := local_factor_bounds hS b hf
  have h1 : SmoothOnChart S (patchClosed b) (fun _ ↦ (1 : ℝ)) :=
    smoothOnChart_of_contDiff contDiff_const
  have hb1 : ∀ X ∈ S, ∀ Z ∈ patchClosed b,
      ‖(1 : ℝ)‖ ≤ (1 : ℝ) ∧ ‖factorGradient (fun _ ↦ (1 : ℝ)) (X, Z)‖ ≤ (0 : ℝ) := by
    intro X _ Z _
    simp only [norm_one, factorGradient_one, norm_zero, le_refl, and_self]
  let hu := cappedApproximation K hJ hN hβ hβ₀ hC₀ hmesh I S hS η hη hX w hw₀ hw a b
    h1 zero_le_one (le_refl 0) hb1
  let hv := cappedApproximation K hJ hN hβ hβ₀ hC₀ hmesh I S hS η hη hX w hw₀ hw a b
    hf hA.le hD.le hb
  have htotal : ∑ i : I, w i ≤ β₀ := by
    rw [Finset.sum_coe_sort]
    exact total_source_weight_le hN hβ hβ₀ I hw
  have hl : ∀ n X, X ∈ S → normalizerLower β₀ ≤ hu.value n X := by
    intro n X _
    exact regularized_normalizer_lower (fun i : I ↦ w i) J a b (fun i : I ↦ hw₀ i i.property) htotal
      (approximationScale n) (approximationScale_pos n) (approximationScale_small n) X
  have hlog := hu.log (normalizerLower_pos β₀) hl
  have hquot := hu.quotient hv (normalizerLower_pos β₀) hl
  refine ⟨?_, hlog.weakGradientOn hS, hquot.weakGradientOn hS,
    ⟨_, hlog.nonneg_gradient_bound⟩, ⟨_, hquot.nonneg_gradient_bound⟩,
    hlog.lipschitzOnWith hconv, hquot.lipschitzOnWith hconv⟩
  intro X hXS
  exact (normalizerLower_pos β₀).trans_le
    (ge_of_tendsto (hu.value_limit X hXS) (Eventually.of_forall fun n ↦ hl n X hXS))

/-- Multiplying the actual reference integrals by their physical patch
area transports the approximation, including its full Riesz field. -/
def scaledApproximation {d : Type*} [Fintype d] {S : Set (ChartSpace d)}
    {f F : ChartSpace d → ℝ} {G H : ChartSpace d → ChartSpace d} {A C c : ℝ}
    (h : BoundedGradientApproximation S f G A C) (hc : 0 ≤ c)
    (hF : ∀ x ∈ S, F x = c * f x) (hH : ∀ x ∈ S, H x = c • G x) :
    BoundedGradientApproximation S F H (c * A) (c * C) where
  value n x := c * h.value n x
  gradient n x := c • h.gradient n x
  nonneg_value_bound := mul_nonneg hc h.nonneg_value_bound
  nonneg_gradient_bound := mul_nonneg hc h.nonneg_gradient_bound
  derivative n x hx := by
    simpa only [map_smul] using (h.derivative n x hx).const_mul c
  value_bound n x hx := by
    rw [norm_mul, Real.norm_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (h.value_bound n x hx) hc
  gradient_bound n x hx := by
    rw [norm_smul, Real.norm_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (h.gradient_bound n x hx) hc
  value_limit x hx := by
    rw [hF x hx]
    exact (h.value_limit x hx).const_mul c
  gradient_limit x hx := by
    rw [hH x hx]
    exact tendsto_const_nhds.smul (h.gradient_limit x hx)

def rawNormalizer (w : ι → ℝ) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (b : Patch) :
    SourceSpace ι → ℝ := rawNumerator w J hJ a b (fun _ _ ↦ 1)

def rawNormalizerGradient (w : ι → ℝ) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (b : Patch) :
    SourceSpace ι → SourceSpace ι := rawNumeratorGradient w J hJ a b (fun _ _ ↦ 1)

def rawLog (w : ι → ℝ) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (b : Patch)
    (X : SourceSpace ι) : ℝ := Real.log (rawNormalizer w J hJ a b X)

def rawMean (w : ι → ℝ) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (b : Patch)
    (F : SourceSpace ι → Torus → ℝ) (X : SourceSpace ι) : ℝ :=
  rawNumerator w J hJ a b F X / rawNormalizer w J hJ a b X

def rawLogGradient (w : ι → ℝ) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (b : Patch) :
    SourceSpace ι → SourceSpace ι :=
  logGradient (rawNormalizer w J hJ a b) (rawNormalizerGradient w J hJ a b)

def rawMeanGradient (w : ι → ℝ) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (b : Patch)
    (F : SourceSpace ι → Torus → ℝ) : SourceSpace ι → SourceSpace ι :=
  quotientGradient (rawNormalizer w J hJ a b) (rawNumerator w J hJ a b F)
    (rawNormalizerGradient w J hJ a b) (rawNumeratorGradient w J hJ a b F)

/-- The actual raw-Haar conclusions, with no reference-area normalization
left implicit. A separate field records equality with the normalized
probability integral, so a totalized Bochner value cannot stand in for an
unproved conditional law. -/
structure RawNormalizedCalculus (w : ι → ℝ) (J : ℕ) (hJ : 0 < J)
    (a : MeshIndex J) (b : Patch) (S : Set (SourceSpace ι))
    (F : SourceSpace ι → Torus → ℝ) : Prop where
  normalizer_pos : ∀ X ∈ S, 0 < rawNormalizer w J hJ a b X
  log_weak : WeakGradientOn S (rawLog w J hJ a b) (rawLogGradient w J hJ a b)
  mean_weak : WeakGradientOn S (rawMean w J hJ a b F) (rawMeanGradient w J hJ a b F)
  lipschitz : ∃ Clog Cmean : ℝ≥0, LipschitzOnWith Clog (rawLog w J hJ a b) S ∧
    LipschitzOnWith Cmean (rawMean w J hJ a b F) S
  probability : ∀ X ∈ S, IsProbabilityMeasure
    (pointLaw (torusMeasure.restrict (patchDomain J hJ a b)) (sources X) w)
  factor_integrable : ∀ X ∈ S, Integrable (F X)
    (pointLaw (torusMeasure.restrict (patchDomain J hJ a b)) (sources X) w)
  mean_eq_integral : ∀ X ∈ S, rawMean w J hJ a b F X =
    ∫ z, F X z ∂pointLaw (torusMeasure.restrict (patchDomain J hJ a b)) (sources X) w

theorem rawNormalizer_eq_integral (w : ι → ℝ) (J : ℕ) (hJ : 0 < J)
    (a : MeshIndex J) (b : Patch) (X : SourceSpace ι) :
    rawNormalizer w J hJ a b X = ∫ z in patchDomain J hJ a b,
      torusWeight (sources X) w z ∂torusMeasure := by
  simp only [rawNormalizer, rawNumerator, mul_one]

/-- Actual raw normalizer, logarithm, conditional average and full physical
weak gradients on the closed chart. All approximation and measure scaling
premises have been discharged. -/
theorem capped_raw_normalized_calculus (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (S : Set (SourceSpace I)) (hS : IsCompact S) (hconv : Convex ℝ S)
    (η : SourceSpace I → LabelVector J N)
    (hη : ∀ X ∈ S, OccupationCap (fixedDelta β₀ C₀ C₁) (η X))
    (hX : ∀ X ∈ S, ∀ i ∈ I, extendedSources I X i ∈ closure (meshCell J hJ (η X i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) {F : SourceSpace I → Torus → ℝ}
    (hf : SmoothOnChart S (patchClosed b) (torusFactor F J a)) :
    RawNormalizedCalculus (fun i : I ↦ w i) J hJ a b S F := by
  have hJ₂ : 2 ≤ J := by omega
  obtain ⟨A, D, hA, hD, hb⟩ := local_factor_bounds hS b hf
  have h1 : SmoothOnChart S (patchClosed b) (fun _ ↦ (1 : ℝ)) :=
    smoothOnChart_of_contDiff contDiff_const
  have hb1 : ∀ X ∈ S, ∀ Z ∈ patchClosed b,
      ‖(1 : ℝ)‖ ≤ (1 : ℝ) ∧ ‖factorGradient (fun _ ↦ (1 : ℝ)) (X, Z)‖ ≤ (0 : ℝ) := by
    intro X _ Z _
    simp only [norm_one, factorGradient_one, norm_zero, le_refl, and_self]
  let hu := cappedApproximation K hJ hN hβ hβ₀ hC₀ hmesh I S hS η hη hX w hw₀ hw a b
    h1 zero_le_one (le_refl 0) hb1
  let hv := cappedApproximation K hJ hN hβ hβ₀ hC₀ hmesh I S hS η hη hX w hw₀ hw a b
    hf hA.le hD.le hb
  let ur := scaledApproximation hu (patchArea_pos hJ b).le
    (fun X hXS ↦ rawNumerator_eq_scaled_local hJ hJ₂ a b (F := fun _ _ ↦ 1) h1 _ hXS)
    (fun X hXS ↦ rawNumeratorGradient_eq_scaled hJ hJ₂ a b (F := fun _ _ ↦ 1) h1 _ hXS)
  let vr := scaledApproximation hv (patchArea_pos hJ b).le
    (fun X hXS ↦ rawNumerator_eq_scaled_local hJ hJ₂ a b hf _ hXS)
    (fun X hXS ↦ rawNumeratorGradient_eq_scaled hJ hJ₂ a b hf _ hXS)
  have htotal : ∑ i : I, w i ≤ β₀ := by
    rw [Finset.sum_coe_sort]
    exact total_source_weight_le hN hβ hβ₀ I hw
  have hl : ∀ n X, X ∈ S → patchArea J b * normalizerLower β₀ ≤ ur.value n X := by
    intro n X _
    exact mul_le_mul_of_nonneg_left
      (regularized_normalizer_lower (fun i : I ↦ w i) J a b (fun i : I ↦ hw₀ i i.property) htotal
        (approximationScale n) (approximationScale_pos n) (approximationScale_small n) X)
      (patchArea_pos hJ b).le
  have hc : 0 < patchArea J b * normalizerLower β₀ :=
    mul_pos (patchArea_pos hJ b) (normalizerLower_pos β₀)
  have hp (X : SourceSpace I) (hXS : X ∈ S) :
      0 < rawNormalizer (fun i : I ↦ w i) J hJ a b X :=
    hc.trans_le (ge_of_tendsto (ur.value_limit X hXS) (Eventually.of_forall fun n ↦ hl n X hXS))
  have hlog := ur.log hc hl
  have hquot := ur.quotient vr hc hl
  refine ⟨hp, hlog.weakGradientOn hS, hquot.weakGradientOn hS,
    ⟨⟨_, hlog.nonneg_gradient_bound⟩, ⟨_, hquot.nonneg_gradient_bound⟩,
      hlog.lipschitzOnWith hconv, hquot.lipschitzOnWith hconv⟩, ?_, ?_, ?_⟩
  · intro X hXS
    have hi := capped_raw_normalizer_bounds K hJ hN hβ hβ₀ hC₀ hmesh (η X) (hη X hXS)
      I (extendedSources I X) (hX X hXS) w hw₀ hw a b
    simp only [extendedSources_subtype] at hi
    apply pointLaw_probability hi.1
    simpa only [rawNormalizer_eq_integral] using hp X hXS
  · intro X hXS
    have hz : 0 < ∫ z in patchDomain J hJ a b, torusWeight (sources X) (fun i : I ↦ w i) z
        ∂torusMeasure := by simpa only [rawNormalizer_eq_integral] using hp X hXS
    have hi := (capped_raw_fibres_integrable K hJ hN hβ hβ₀ hC₀ hmesh I S X hXS
      (η X) (hη X hXS) (hX X hXS) w hw₀ hw a b hf).1
    apply (pointLaw_integrable_iff (sources X) (fun i : I ↦ w i) hz (F X)).mpr
    simpa only [pointDensity, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using hi.const_mul ((∫ z in patchDomain J hJ a b,
        torusWeight (sources X) (fun i : I ↦ w i) z ∂torusMeasure)⁻¹)
  · intro X hXS
    have hz : 0 < ∫ z in patchDomain J hJ a b, torusWeight (sources X) (fun i : I ↦ w i) z
        ∂torusMeasure := by simpa only [rawNormalizer_eq_integral] using hp X hXS
    simpa only [rawMean, rawNumerator, rawNormalizer_eq_integral] using
      normalized_factor_eq_mean (sources X) (fun i : I ↦ w i) hz (F X)

/-- Source-facing cell-product wrapper. The integration patch can be a cell
or either oriented adjacent-cell union, including torus wrap-around. -/
theorem cellChart_raw_normalized_calculus (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (η : LabelVector J N)
    (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) {F : SourceSpace I → Torus → ℝ}
    (hf : SmoothOnChart (cellChart I η) (patchClosed b) (torusFactor F J a)) :
    RawNormalizedCalculus (fun i : I ↦ w i) J hJ a b (cellChart I η) F :=
  capped_raw_normalized_calculus K hJ hN hβ hβ₀ hC₀ hmesh I (cellChart I η)
    (isCompact_closedChart J (fun i : I ↦ η i) (fun _ ↦ .cell))
    (convex_closedChart J (fun i : I ↦ η i) (fun _ ↦ .cell))
    (fun _ ↦ η) (fun _ _ ↦ hη) (fun _ hX ↦ cellChart_placement hJ I η hX)
    w hw₀ hw a b hf

/-- Source-facing wrapper with one moving source in an adjacent union.
Both endpoint label vectors satisfy the cap; the integration patch is a
cell, so at most one coordinate domain is an adjacent union. -/
theorem adjacentChart_raw_normalized_calculus (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (η : LabelVector J N) (k : Fin N) (d : Fin 2)
    (hη₀ : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (hη₁ : OccupationCap (fixedDelta β₀ C₀ C₁) (Function.update η k (nextCell J hJ (η k) d)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) {F : SourceSpace I → Torus → ℝ}
    (hf : SmoothOnChart (adjacentChart I η k d) (patchClosed .cell) (torusFactor F J a)) :
    RawNormalizedCalculus (fun i : I ↦ w i) J hJ a .cell (adjacentChart I η k d) F := by
  obtain ⟨labels, hcap, hplace⟩ := exists_capped_labels_one_adjacent hJ I
    (adjacentChart I η k d) η k d (fixedDelta β₀ C₀ C₁) hη₀ hη₁
    (fun _ hX ↦ adjacentChart_cell_placement hJ I η k d hX)
    (fun _ hX hk ↦ adjacentChart_edge_placement hJ I η k d hX hk)
  exact capped_raw_normalized_calculus K hJ hN hβ hβ₀ hC₀ hmesh I (adjacentChart I η k d)
    (isCompact_closedChart J (fun i : I ↦ η i) (adjacentShapes I k d))
    (convex_closedChart J (fun i : I ↦ η i) (adjacentShapes I k d))
    labels (fun X _ ↦ hcap X) hplace w hw₀ hw a .cell hf

end PeriodicAttractiveLogGas.MovingPoleNormalized
