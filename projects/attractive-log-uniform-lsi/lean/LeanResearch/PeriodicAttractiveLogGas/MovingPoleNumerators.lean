import LeanResearch.PeriodicAttractiveLogGas.MovingPoleWeakLimit
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! Source-only candidate for the unnormalized part of manuscript Lemma 3.5.

The source variables have their genuine Euclidean product norm. The patch
variable uses the literal square/edge reference probability measure and the
actual mesh chart. Regularized derivatives are calculated before taking the
checked capped joint L1 limit. Tests may depend on all source coordinates
and on the patch variable. A smooth factor is only required on an open
neighborhood of the closed chart; its behavior elsewhere is unrestricted.

No weak derivative, uniform integrability, or limiting numerator formula is
an assumption of the capped endpoint. Normalized logarithmic and quotient
calculus, Lipschitz representatives, and weighted almost-everywhere transfer
are outside this module. This candidate has not been elaborated by its author.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology ContDiff RealInnerProductSpace

namespace PeriodicAttractiveLogGas.MovingPoleNumerators

open MovingPoleIntegrability MovingPoleWeakLimit GreenPointWeights
open MeshCells MeshAdjacentCells LabelOccupations ConditionalParameters

variable {ι : Type*} [Fintype ι]

/-- Physical coordinates of the retained sources, with the Euclidean norm. -/
abbrev SourceSpace (ι : Type*) := EuclideanSpace ℝ (ι × Fin 2)

def sourceProjectionLinear (j : ι) : SourceSpace ι →ₗ[ℝ] PlanarSpace where
  toFun X := WithLp.toLp 2 (fun k ↦ X (j, k))
  map_add' X Y := by ext k; rfl
  map_smul' c X := by ext k; rfl

def sourceProjection (j : ι) : SourceSpace ι →L[ℝ] PlanarSpace :=
  (sourceProjectionLinear j).toContinuousLinearMap

@[simp] theorem sourceProjection_apply (j : ι) (X : SourceSpace ι) (k : Fin 2) :
    sourceProjection j X k = X (j, k) := rfl

def sources (X : SourceSpace ι) (j : ι) : Torus := torusQuotient (sourceProjection j X)

theorem continuous_sources (j : ι) : Continuous (fun X : SourceSpace ι ↦ sources X j) :=
  isOpenQuotientMap_torusQuotient.continuous.comp (sourceProjection j).continuous

def weight (w : ι → ℝ) (J : ℕ) (a : MeshIndex J)
    (p : SourceSpace ι × PlanarSpace) : ℝ :=
  torusWeight (sources p.1) w (meshChart J a p.2)

def gradient (w : ι → ℝ) (J : ℕ) (a : MeshIndex J) (j : ι)
    (p : SourceSpace ι × PlanarSpace) : PlanarSpace :=
  sourceGradient (sources p.1) w j (meshChart J a p.2)

def smoothWeight (w : ι → ℝ) (J : ℕ) (a : MeshIndex J) (ε : ℝ) (hε : 0 < ε)
    (p : SourceSpace ι × PlanarSpace) : ℝ :=
  regularizedTorusWeight (sources p.1) w ε hε (meshChart J a p.2)

def smoothGradient (w : ι → ℝ) (J : ℕ) (a : MeshIndex J) (ε : ℝ) (hε : 0 < ε)
    (j : ι) (p : SourceSpace ι × PlanarSpace) : PlanarSpace :=
  regularizedSourceGradient (sources p.1) w ε hε j (meshChart J a p.2)

/-- The vector represents the full ordinary source differential, using
adjoints in the physical Euclidean spaces, with no norm-comparison factor. -/
def fullGradient (G : ι → PlanarSpace) : SourceSpace ι :=
  ∑ j, (sourceProjection j).adjoint (G j)

theorem fullGradient_inner (G : ι → PlanarSpace) (v : SourceSpace ι) :
    inner ℝ (fullGradient G) v = ∑ j, inner ℝ (G j) (sourceProjection j v) := by
  simp only [fullGradient, sum_inner, ContinuousLinearMap.adjoint_inner_left]

theorem measurable_weight (w : ι → ℝ) (J : ℕ) (a : MeshIndex J) :
    Measurable (weight w J a) := by
  have hm : Measurable (fun p : SourceSpace ι × Torus ↦ torusWeight (sources p.1) w p.2) :=
    MovingPoleWeakLimit.measurable_joint_weight (sources : SourceSpace ι → ι → Torus)
      (fun j ↦ (continuous_sources j).measurable) w
  have hp : Measurable (fun p : SourceSpace ι × PlanarSpace ↦ (p.1, meshChart J a p.2)) :=
    measurable_fst.prodMk ((continuous_meshChart J a).measurable.comp measurable_snd)
  change Measurable ((fun p : SourceSpace ι × Torus ↦ torusWeight (sources p.1) w p.2) ∘
    (fun p : SourceSpace ι × PlanarSpace ↦ (p.1, meshChart J a p.2)))
  exact hm.comp hp

theorem measurable_gradient (w : ι → ℝ) (J : ℕ) (a : MeshIndex J) (j : ι) :
    Measurable (gradient w J a j) := by
  have hm : Measurable (fun p : SourceSpace ι × Torus ↦ sourceGradient (sources p.1) w j p.2) :=
    MovingPoleWeakLimit.measurable_joint_sourceGradient (sources : SourceSpace ι → ι → Torus)
      (fun i ↦ (continuous_sources i).measurable) w j
  have hp : Measurable (fun p : SourceSpace ι × PlanarSpace ↦ (p.1, meshChart J a p.2)) :=
    measurable_fst.prodMk ((continuous_meshChart J a).measurable.comp measurable_snd)
  change Measurable ((fun p : SourceSpace ι × Torus ↦ sourceGradient (sources p.1) w j p.2) ∘
    (fun p : SourceSpace ι × PlanarSpace ↦ (p.1, meshChart J a p.2)))
  exact hm.comp hp

theorem continuous_smoothWeight (w : ι → ℝ) (J : ℕ) (a : MeshIndex J)
    (ε : ℝ) (hε : 0 < ε) : Continuous (smoothWeight w J a ε hε) := by
  apply Real.continuous_exp.comp
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul ((continuous_regularizedGreen ε hε).comp
    (((continuous_meshChart J a).comp continuous_snd).sub
      ((continuous_sources j).comp continuous_fst)))

theorem continuous_smoothGradient (w : ι → ℝ) (J : ℕ) (a : MeshIndex J)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) (j : ι) :
    Continuous (smoothGradient w J a ε hε j) :=
  (continuous_const.mul (continuous_smoothWeight w J a ε hε)).smul
    ((continuous_regularizedGreenGradient ε hε hs).comp
      (((continuous_meshChart J a).comp continuous_snd).sub
        ((continuous_sources j).comp continuous_fst)))

theorem hasFDerivAt_green_source (ε : ℝ) (hε : 0 < ε)
    (hs : ε ≤ (1 / 16 : ℝ)) (z : Torus) (j : ι) (X : SourceSpace ι) :
    HasFDerivAt (fun Y : SourceSpace ι ↦ regularizedGreen ε hε (z - sources Y j))
      (-((regularizedGreenDifferential ε hε (z - sources X j)).comp
        (sourceProjection j))) X := by
  have hd := ((contDiff_regularizedGreen_lift ε hε hs).differentiable (by simp))
    (centeredLift z - sourceProjection j X)
  have hh := hd.hasFDerivAt.comp X
    ((sourceProjection j).hasFDerivAt.const_sub (centeredLift z))
  have hD : fderiv ℝ (fun Y : PlanarSpace ↦ regularizedGreen ε hε (torusQuotient Y))
      (centeredLift z - sourceProjection j X) =
      regularizedGreenDifferential ε hε (z - sources X j) := by
    simpa only [torusQuotient_sub, torusQuotient_centeredLift, sources] using
      (regularizedGreenDifferential_lift ε hε (centeredLift z - sourceProjection j X)).symm
  simpa only [Function.comp_def, torusQuotient_sub, torusQuotient_centeredLift,
    hD, ContinuousLinearMap.comp_neg, sources] using hh

theorem hasFDerivAt_smoothWeight (w : ι → ℝ) (J : ℕ) (a : MeshIndex J)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ))
    (Z : PlanarSpace) (X : SourceSpace ι) :
    HasFDerivAt (fun Y ↦ smoothWeight w J a ε hε (Y, Z))
      (∑ j, (-w j * smoothWeight w J a ε hε (X, Z)) •
        ((regularizedGreenDifferential ε hε (meshChart J a Z - sources X j)).comp
          (sourceProjection j))) X := by
  have hd : HasFDerivAt
      (fun Y : SourceSpace ι ↦ ∑ j, w j * regularizedGreen ε hε (meshChart J a Z - sources Y j))
      (∑ j, w j • -((regularizedGreenDifferential ε hε (meshChart J a Z - sources X j)).comp
        (sourceProjection j))) X :=
    HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦
      (hasFDerivAt_green_source ε hε hs (meshChart J a Z) j X).const_mul (w j))
  have he : (∑ j, (-w j * smoothWeight w J a ε hε (X, Z)) •
      ((regularizedGreenDifferential ε hε (meshChart J a Z - sources X j)).comp
        (sourceProjection j))) =
      Real.exp (∑ j, w j * regularizedGreen ε hε (meshChart J a Z - sources X j)) •
        (∑ j, w j • -((regularizedGreenDifferential ε hε (meshChart J a Z - sources X j)).comp
          (sourceProjection j))) := by
    ext v
    simp only [sum_apply, smul_apply, neg_apply, ContinuousLinearMap.comp_apply,
      smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    unfold smoothWeight regularizedTorusWeight
    ring
  change HasFDerivAt
    (fun Y : SourceSpace ι ↦ Real.exp (∑ j, w j * regularizedGreen ε hε
      (meshChart J a Z - sources Y j))) _ X
  rw [he]
  exact hd.exp

theorem fderiv_smoothWeight_apply (w : ι → ℝ) (J : ℕ) (a : MeshIndex J)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ))
    (Z : PlanarSpace) (X v : SourceSpace ι) :
    fderiv ℝ (fun Y ↦ smoothWeight w J a ε hε (Y, Z)) X v =
      ∑ j, inner ℝ (smoothGradient w J a ε hε j (X, Z)) (sourceProjection j v) := by
  rw [(hasFDerivAt_smoothWeight w J a ε hε hs Z X).fderiv]
  simp only [sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, smoothGradient, regularizedSourceGradient,
    real_inner_smul_left, regularizedGreenGradient_inner, smoothWeight]

/-- Ordinary source-direction derivative of a function on the full chart. -/
def sourceD (f : SourceSpace ι × PlanarSpace → ℝ) (v : SourceSpace ι)
    (p : SourceSpace ι × PlanarSpace) : ℝ := fderiv ℝ f p (v, 0)

theorem sourceD_eq_fderiv_fibre {f : SourceSpace ι × PlanarSpace → ℝ}
    {X : SourceSpace ι} {Z : PlanarSpace} (hf : DifferentiableAt ℝ f (X, Z))
    (v : SourceSpace ι) : sourceD f v (X, Z) = fderiv ℝ (fun Y ↦ f (Y, Z)) X v := by
  simpa only [sourceD, Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply] using!
    congrArg (fun L : SourceSpace ι →L[ℝ] ℝ ↦ L v)
      (hf.hasFDerivAt.comp X (hasFDerivAt_prodMk_left X Z)).fderiv.symm

/-- Literal neighborhood smoothness; there is no restriction on `f` away
from the specified open neighborhood. -/
def SmoothOnChart (S : Set (SourceSpace ι)) (B : Set PlanarSpace)
    (f : SourceSpace ι × PlanarSpace → ℝ) : Prop :=
  ∃ U, IsOpen U ∧ S ×ˢ B ⊆ U ∧ ContDiffOn ℝ 1 f U

theorem SmoothOnChart.contDiffAt {S : Set (SourceSpace ι)} {B : Set PlanarSpace}
    {f : SourceSpace ι × PlanarSpace → ℝ} (hf : SmoothOnChart S B f)
    {p : SourceSpace ι × PlanarSpace} (hp : p ∈ S ×ˢ B) : ContDiffAt ℝ 1 f p := by
  obtain ⟨U, hU, hSU, hfu⟩ := hf
  exact hfu.contDiffAt (hU.mem_nhds (hSU hp))

theorem SmoothOnChart.continuousOn {S : Set (SourceSpace ι)} {B : Set PlanarSpace}
    {f : SourceSpace ι × PlanarSpace → ℝ} (hf : SmoothOnChart S B f) :
    ContinuousOn f (S ×ˢ B) := fun _ hp ↦ (hf.contDiffAt hp).continuousAt.continuousWithinAt

theorem SmoothOnChart.continuousOn_sourceD {S : Set (SourceSpace ι)} {B : Set PlanarSpace}
    {f : SourceSpace ι × PlanarSpace → ℝ} (hf : SmoothOnChart S B f)
    (v : SourceSpace ι) : ContinuousOn (sourceD f v) (S ×ˢ B) := by
  intro p hp
  exact (((hf.contDiffAt hp).continuousAt_fderiv one_ne_zero).clm_apply
    continuousAt_const).continuousWithinAt

theorem smoothOnChart_of_contDiff {S : Set (SourceSpace ι)} {B : Set PlanarSpace}
    {f : SourceSpace ι × PlanarSpace → ℝ} (hf : ContDiff ℝ 1 f) : SmoothOnChart S B f :=
  ⟨univ, isOpen_univ, subset_univ _, hf.contDiffOn⟩

theorem isCompact_patchClosed (b : Patch) : IsCompact (patchClosed b) := by
  cases b with
  | cell => exact isCompact_closedUnitSquare
  | edge j => exact isCompact_closedEdgeRectangle j

/-- Compactness supplies actual finite bounds and measurability under a
measure supported by the closed chart, including for the ordinary derivative. -/
theorem chart_bounded_measurable {V : Type*} [NormedAddCommGroup V]
    {S : Set (SourceSpace ι)} {B : Set PlanarSpace}
    (hS : IsCompact S) (hB : IsCompact B)
    {μ : Measure (SourceSpace ι × PlanarSpace)}
    (hμ : ∀ᵐ p ∂μ, p ∈ S ×ˢ B) {g : SourceSpace ι × PlanarSpace → V}
    (hg : ContinuousOn g (S ×ˢ B)) :
    AEStronglyMeasurable g μ ∧ ∃ C : ℝ, 0 < C ∧ ∀ᵐ p ∂μ, ‖g p‖ ≤ C := by
  have hm : AEStronglyMeasurable g (μ.restrict (S ×ˢ B)) :=
    hg.aestronglyMeasurable (μ := μ) (hS.prod hB).measurableSet
  rw [Measure.restrict_eq_self_of_ae_mem hμ] at hm
  obtain ⟨C, hC, hb⟩ := ((hS.prod hB).image_of_continuousOn hg).isBounded.exists_pos_norm_le
  exact ⟨hm, C, hC, hμ.mono fun p hp ↦ hb (g p) (mem_image_of_mem g hp)⟩

theorem ae_mem_chart {S : Set (SourceSpace ι)} (hS : MeasurableSet S)
    (c : ℝ≥0∞) (b : Patch) :
    ∀ᵐ p ∂(c • (volume : Measure (SourceSpace ι)).restrict S).prod (patchReference b),
      p ∈ S ×ˢ patchClosed b := by
  apply (Measure.ae_prod_iff_ae_ae (hS.prod (isCompact_patchClosed b).measurableSet)).2
  have hs : ∀ᵐ X ∂c • (volume : Measure (SourceSpace ι)).restrict S, X ∈ S :=
    Measure.ae_smul_measure (ae_restrict_mem hS) c
  filter_upwards [hs] with X hX
  exact (ae_mem_patchClosed b).mono fun Z hZ ↦ ⟨hX, hZ⟩

theorem integrable_mul_on_tsupport {f g : SourceSpace ι → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g)
    (hf : ∀ X ∈ tsupport g, ContinuousAt f X) :
    Integrable (fun X ↦ f X * g X) volume := by
  have hp : Continuous (fun X ↦ f X * g X) := by
    apply continuous_iff_continuousAt.mpr
    intro X
    by_cases hx : X ∈ tsupport g
    · exact (hf X hx).mul hg.continuousAt
    · apply (continuousAt_const : ContinuousAt (fun _ : SourceSpace ι ↦ (0 : ℝ)) X).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hx] with Y hY
      simp only [image_eq_zero_of_notMem_tsupport hY, mul_zero]
  exact hp.integrable_of_hasCompactSupport hc.mul_left

def productD (W : SourceSpace ι × PlanarSpace → ℝ)
    (G : ι → SourceSpace ι × PlanarSpace → PlanarSpace)
    (f : SourceSpace ι × PlanarSpace → ℝ) (v : SourceSpace ι)
    (p : SourceSpace ι × PlanarSpace) : ℝ :=
  W p * sourceD f v p + ∑ j, inner ℝ (G j p) (sourceProjection j v) * f p

theorem fderiv_smoothProduct_apply (w : ι → ℝ) (J : ℕ) (a : MeshIndex J)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ))
    {S : Set (SourceSpace ι)} {B : Set PlanarSpace}
    {f : SourceSpace ι × PlanarSpace → ℝ} (hf : SmoothOnChart S B f)
    {X : SourceSpace ι} {Z : PlanarSpace} (hX : X ∈ S) (hZ : Z ∈ B)
    (v : SourceSpace ι) :
    fderiv ℝ (fun Y ↦ smoothWeight w J a ε hε (Y, Z) * f (Y, Z)) X v =
      productD (smoothWeight w J a ε hε) (smoothGradient w J a ε hε) f v (X, Z) := by
  have hdf : DifferentiableAt ℝ f (X, Z) :=
    (hf.contDiffAt (p := (X, Z)) ⟨hX, hZ⟩).differentiableAt one_ne_zero
  have hdf' : HasFDerivAt (fun Y : SourceSpace ι ↦ f (Y, Z))
      ((fderiv ℝ f (X, Z)).comp (ContinuousLinearMap.inl ℝ (SourceSpace ι) PlanarSpace)) X :=
    hdf.hasFDerivAt.comp X (hasFDerivAt_prodMk_left (𝕜 := ℝ) X Z)
  change (fderiv ℝ ((fun Y ↦ smoothWeight w J a ε hε (Y, Z)) *
    (fun Y ↦ f (Y, Z))) X) v = _
  rw [fderiv_mul (hasFDerivAt_smoothWeight w J a ε hε hs Z X).differentiableAt
    hdf'.differentiableAt]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_smoothWeight_apply w J a ε hε hs Z X v,
    ← sourceD_eq_fderiv_fibre hdf v]
  simp only [productD]
  rw [← Finset.sum_mul]
  ring

theorem continuousAt_productD (w : ι → ℝ) (J : ℕ) (a : MeshIndex J)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ))
    {S : Set (SourceSpace ι)} {B : Set PlanarSpace}
    {f : SourceSpace ι × PlanarSpace → ℝ} (hf : SmoothOnChart S B f)
    {p : SourceSpace ι × PlanarSpace} (hp : p ∈ S ×ˢ B) (v : SourceSpace ι) :
    ContinuousAt (productD (smoothWeight w J a ε hε)
      (smoothGradient w J a ε hε) f v) p := by
  have hfc := (hf.contDiffAt hp).continuousAt
  have hdc : ContinuousAt (sourceD f v) p :=
    ((hf.contDiffAt hp).continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const
  apply ((continuous_smoothWeight w J a ε hε).continuousAt.mul hdc).add
  exact tendsto_finsetSum Finset.univ fun j _ ↦
    (((continuous_smoothGradient w J a ε hε hs j).continuousAt).inner continuousAt_const).mul hfc

/-- Integration by parts for the actual regularized product, on every
fibre of the reference patch. The source test is not a tensor product. -/
theorem smooth_product_fibre_identity (w : ι → ℝ) (J : ℕ) (a : MeshIndex J)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ))
    (S : Set (SourceSpace ι)) (B : Set PlanarSpace)
    {f : SourceSpace ι × PlanarSpace → ℝ} (hf : SmoothOnChart S B f)
    {φ : SourceSpace ι × PlanarSpace → ℝ} (hφ : ContDiff ℝ 1 φ)
    {Z : PlanarSpace} (hZ : Z ∈ B)
    (hc : HasCompactSupport (fun X ↦ φ (X, Z)))
    (hφS : tsupport (fun X ↦ φ (X, Z)) ⊆ S) (v : SourceSpace ι) :
    (∫ X, smoothWeight w J a ε hε (X, Z) * f (X, Z) * sourceD φ v (X, Z)) =
      -(∫ X, productD (smoothWeight w J a ε hε)
        (smoothGradient w J a ε hε) f v (X, Z) * φ (X, Z)) := by
  let F : SourceSpace ι → ℝ := fun X ↦ smoothWeight w J a ε hε (X, Z) * f (X, Z)
  let ψ : SourceSpace ι → ℝ := fun X ↦ φ (X, Z)
  have hψ : ContDiff ℝ 1 ψ := hφ.comp (contDiff_id.prodMk contDiff_const)
  have hψD (X : SourceSpace ι) : sourceD φ v (X, Z) = fderiv ℝ ψ X v :=
    sourceD_eq_fderiv_fibre (hφ.differentiable one_ne_zero (X, Z)) v
  have hFc (X : SourceSpace ι) (hX : X ∈ S) : ContinuousAt F X :=
    ((continuous_smoothWeight w J a ε hε).comp
      (continuous_id.prodMk continuous_const)).continuousAt.mul
        ((hf.contDiffAt ⟨hX, hZ⟩).continuousAt.comp
          (continuous_id.prodMk continuous_const).continuousAt)
  have hFG : Integrable (fun X ↦ productD (smoothWeight w J a ε hε)
      (smoothGradient w J a ε hε) f v (X, Z) * ψ X) volume :=
    integrable_mul_on_tsupport hψ.continuous hc fun X hX ↦
      (continuousAt_productD w J a ε hε hs hf ⟨hφS hX, hZ⟩ v).comp
        (continuous_id.prodMk continuous_const).continuousAt
  have hDeq (X : SourceSpace ι) : fderiv ℝ F X v * ψ X =
      productD (smoothWeight w J a ε hε) (smoothGradient w J a ε hε) f v (X, Z) * ψ X := by
    by_cases hx : X ∈ tsupport ψ
    · rw [fderiv_smoothProduct_apply w J a ε hε hs hf (hφS hx) hZ v]
    · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hDF : Integrable (fun X ↦ fderiv ℝ F X v * ψ X) volume :=
    hFG.congr (ae_of_all _ fun X ↦ (hDeq X).symm)
  have hFD : Integrable (fun X ↦ F X * fderiv ℝ ψ X v) volume :=
    integrable_mul_on_tsupport
      ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (hc.fderiv_apply ℝ v) fun X hX ↦ hFc X (hφS (tsupport_fderiv_apply_subset ℝ v hX))
  have hFψ : Integrable (fun X ↦ F X * ψ X) volume :=
    integrable_mul_on_tsupport hψ.continuous hc fun X hX ↦ hFc X (hφS hX)
  have hI := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hDF hFD hFψ
    (fun X hX ↦ (hasFDerivAt_smoothWeight w J a ε hε hs Z X).differentiableAt.mul
      (((hf.contDiffAt ⟨hφS hX, hZ⟩).differentiableAt one_ne_zero).comp X
        (hasFDerivAt_prodMk_left X Z).differentiableAt))
    (fun X _ ↦ hψ.differentiable one_ne_zero X)
  simpa only [← hψD, hDeq, F, ψ] using hI

theorem smooth_product_setIntegral_identity (w : ι → ℝ) (J : ℕ) (a : MeshIndex J)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ))
    (S : Set (SourceSpace ι)) (c : ℝ≥0∞) (B : Set PlanarSpace)
    {f : SourceSpace ι × PlanarSpace → ℝ} (hf : SmoothOnChart S B f)
    {φ : SourceSpace ι × PlanarSpace → ℝ} (hφ : ContDiff ℝ 1 φ)
    {Z : PlanarSpace} (hZ : Z ∈ B)
    (hc : HasCompactSupport (fun X ↦ φ (X, Z)))
    (hφS : tsupport (fun X ↦ φ (X, Z)) ⊆ S) (v : SourceSpace ι) :
    (∫ X, smoothWeight w J a ε hε (X, Z) * f (X, Z) * sourceD φ v (X, Z)
      ∂c • volume.restrict S) =
      -(∫ X, productD (smoothWeight w J a ε hε)
        (smoothGradient w J a ε hε) f v (X, Z) * φ (X, Z) ∂c • volume.restrict S) := by
  have hL : (∫ X in S, smoothWeight w J a ε hε (X, Z) * f (X, Z) * sourceD φ v (X, Z)) =
      ∫ X, smoothWeight w J a ε hε (X, Z) * f (X, Z) * sourceD φ v (X, Z) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro X hX
    rw [sourceD_eq_fderiv_fibre (hφ.differentiable one_ne_zero (X, Z)) v]
    have hn : X ∉ tsupport (fun Y ↦ fderiv ℝ (fun Y ↦ φ (Y, Z)) Y v) :=
      fun hh ↦ hX (hφS (tsupport_fderiv_apply_subset ℝ v hh))
    simp only [image_eq_zero_of_notMem_tsupport hn, mul_zero]
  have hR : (∫ X in S, productD (smoothWeight w J a ε hε)
      (smoothGradient w J a ε hε) f v (X, Z) * φ (X, Z)) =
      ∫ X, productD (smoothWeight w J a ε hε)
        (smoothGradient w J a ε hε) f v (X, Z) * φ (X, Z) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro X hX
    simp only [image_eq_zero_of_notMem_tsupport (fun hh ↦ hX (hφS hh)), mul_zero]
  rw [integral_smul_measure, integral_smul_measure, hL, hR,
    smooth_product_fibre_identity w J a ε hε hs S B hf hφ hZ hc hφS v, smul_neg]

/-- A small analytic interface; the final local theorem obtains it from
neighborhood smoothness and compactness, rather than assuming a bound. -/
def BoundedAE {A : Type*} [MeasurableSpace A] (μ : Measure A) (f : A → ℝ) : Prop :=
  AEStronglyMeasurable f μ ∧ ∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂μ, ‖f x‖ ≤ C

theorem BoundedAE.mul {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f g : A → ℝ} (hf : BoundedAE μ f) (hg : BoundedAE μ g) :
    BoundedAE μ (fun x ↦ f x * g x) := by
  obtain ⟨hmf, C, hC, hbC⟩ := hf
  obtain ⟨hmg, D, hD, hbD⟩ := hg
  refine ⟨hmf.mul hmg, C * D, mul_pos hC hD, ?_⟩
  filter_upwards [hbC, hbD] with x hx hy
  rw [norm_mul]
  exact mul_le_mul hx hy (norm_nonneg _) hC.le

theorem BoundedAE.integrable_mul {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f g : A → ℝ} (hg : BoundedAE μ g) (hf : Integrable f μ) :
    Integrable (fun x ↦ f x * g x) μ := by
  obtain ⟨hm, C, _, hb⟩ := hg
  exact hf.mul_bdd hm hb

theorem BoundedAE.tendsto_integral_mul {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {F : ℕ → A → ℝ} {G : A → ℝ} (hF : ∀ n, Integrable (F n) μ)
    (hG : Integrable G μ) (ht : Tendsto (fun n ↦ eLpNorm (F n - G) 1 μ) atTop (𝓝 0))
    {ψ : A → ℝ} (hψ : BoundedAE μ ψ) :
    Tendsto (fun n ↦ ∫ x, F n x * ψ x ∂μ) atTop (𝓝 (∫ x, G x * ψ x ∂μ)) := by
  obtain ⟨hm, C, _, hb⟩ := hψ
  exact tendsto_integral_mul_of_L1 hF hG ht ψ hm hb

theorem BoundedAE.tendsto_integral_inner_mul {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {F : ℕ → A → PlanarSpace} {G : A → PlanarSpace}
    (hF : ∀ n, Integrable (F n) μ) (hG : Integrable G μ)
    (ht : Tendsto (fun n ↦ eLpNorm (F n - G) 1 μ) atTop (𝓝 0))
    (v : PlanarSpace) {ψ : A → ℝ} (hψ : BoundedAE μ ψ) :
    Tendsto (fun n ↦ ∫ x, inner ℝ (F n x) v * ψ x ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (G x) v * ψ x ∂μ)) := by
  obtain ⟨hm, C, _, hb⟩ := hψ
  exact tendsto_integral_inner_mul_of_L1 hF hG ht v ψ hm hb

theorem integrable_productD {μ : Measure (SourceSpace ι × PlanarSpace)}
    {W : SourceSpace ι × PlanarSpace → ℝ}
    {G : ι → SourceSpace ι × PlanarSpace → PlanarSpace}
    {f : SourceSpace ι × PlanarSpace → ℝ} (v : SourceSpace ι)
    (hW : Integrable W μ) (hG : ∀ j, Integrable (G j) μ)
    (hf : BoundedAE μ f) (hDf : BoundedAE μ (sourceD f v)) :
    Integrable (productD W G f v) μ := by
  exact (hDf.integrable_mul hW).add
    (integrable_finsetSum Finset.univ fun j _ ↦
      hf.integrable_mul (integrable_inner_const (hG j) (sourceProjection j v)))

theorem integral_productD_mul {μ : Measure (SourceSpace ι × PlanarSpace)}
    {W : SourceSpace ι × PlanarSpace → ℝ}
    {G : ι → SourceSpace ι × PlanarSpace → PlanarSpace}
    {f φ : SourceSpace ι × PlanarSpace → ℝ} (v : SourceSpace ι)
    (hW : Integrable W μ) (hG : ∀ j, Integrable (G j) μ)
    (hf : BoundedAE μ f) (hDf : BoundedAE μ (sourceD f v)) (hφ : BoundedAE μ φ) :
    (∫ p, productD W G f v p * φ p ∂μ) =
      (∫ p, W p * (sourceD f v p * φ p) ∂μ) +
      ∑ j, ∫ p, inner ℝ (G j p) (sourceProjection j v) * (f p * φ p) ∂μ := by
  simp only [productD, add_mul, Finset.sum_mul, mul_assoc]
  rw [integral_add ((hDf.mul hφ).integrable_mul hW)
    (integrable_finsetSum Finset.univ fun j _ ↦
      (hf.mul hφ).integrable_mul (integrable_inner_const (hG j) (sourceProjection j v))),
    integral_finsetSum]
  intro j _
  exact (hf.mul hφ).integrable_mul (integrable_inner_const (hG j) (sourceProjection j v))

theorem smooth_product_joint_identity (w : ι → ℝ) (J : ℕ) (a : MeshIndex J)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ))
    (S : Set (SourceSpace ι)) (hS : IsCompact S) (c : ℝ≥0∞) (b : Patch)
    [IsFiniteMeasure (c • (volume : Measure (SourceSpace ι)).restrict S)]
    (hW : Integrable (smoothWeight w J a ε hε)
      ((c • volume.restrict S).prod (patchReference b)))
    (hG : ∀ j, Integrable (smoothGradient w J a ε hε j)
      ((c • volume.restrict S).prod (patchReference b)))
    {f : SourceSpace ι × PlanarSpace → ℝ} (hf : SmoothOnChart S (patchClosed b) f)
    {φ : SourceSpace ι × PlanarSpace → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : ∀ Z ∈ patchClosed b, HasCompactSupport (fun X ↦ φ (X, Z)))
    (hφS : ∀ Z ∈ patchClosed b, tsupport (fun X ↦ φ (X, Z)) ⊆ S)
    (v : SourceSpace ι) :
    (∫ p, smoothWeight w J a ε hε p * f p * sourceD φ v p
      ∂(c • volume.restrict S).prod (patchReference b)) =
      -(∫ p, productD (smoothWeight w J a ε hε) (smoothGradient w J a ε hε) f v p * φ p
        ∂(c • volume.restrict S).prod (patchReference b)) := by
  have hb (g : SourceSpace ι × PlanarSpace → ℝ) (hg : ContinuousOn g (S ×ˢ patchClosed b)) :
      BoundedAE ((c • volume.restrict S).prod (patchReference b)) g :=
    chart_bounded_measurable hS (isCompact_patchClosed b) (ae_mem_chart hS.measurableSet c b) hg
  have hfb : BoundedAE _ f := hb _ hf.continuousOn
  have hDfb : BoundedAE _ (sourceD f v) := hb _ (hf.continuousOn_sourceD v)
  have hφb : BoundedAE _ φ := hb _ hφ.continuous.continuousOn
  have hDφb : BoundedAE _ (sourceD φ v) :=
    hb _ ((smoothOnChart_of_contDiff hφ).continuousOn_sourceD v)
  have hL := hDφb.integrable_mul (hfb.integrable_mul hW)
  have hR := hφb.integrable_mul (integrable_productD v hW hG hfb hDfb)
  rw [integral_prod_symm _ hL, integral_prod_symm _ hR, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [ae_mem_patchClosed b] with Z hZ
  exact smooth_product_setIntegral_identity w J a ε hε hs S c (patchClosed b)
    hf hφ hZ (hc Z hZ) (hφS Z hZ) v

/-- Actual integrability and L1 convergence, assembled from the previous
capped estimates below. This structure stores conclusions, not axioms. -/
structure ChartL1Data (w : ι → ℝ) (J : ℕ) (a : MeshIndex J)
    (μ : Measure (SourceSpace ι × PlanarSpace)) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) : Prop where
  smooth_weight : ∀ n, Integrable (smoothWeight w J a (ε n) (hε n)) μ
  smooth_gradient : ∀ n j, Integrable (smoothGradient w J a (ε n) (hε n) j) μ
  weight_integrable : Integrable (weight w J a) μ
  gradient_integrable : ∀ j, Integrable (gradient w J a j) μ
  weight_limit : Tendsto (fun n ↦ eLpNorm (smoothWeight w J a (ε n) (hε n) - weight w J a) 1 μ)
    atTop (𝓝 0)
  gradient_limit : ∀ j, Tendsto (fun n ↦ eLpNorm
    (smoothGradient w J a (ε n) (hε n) j - gradient w J a j) 1 μ) atTop (𝓝 0)

/-- Joint weak product identity for arbitrary, possibly non-tensor tests.
The limiting weight and each limiting field are the literal Green objects. -/
theorem product_joint_identity_of_L1 (w : ι → ℝ) (J : ℕ) (a : MeshIndex J)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hs : ∀ n, ε n ≤ (1 / 16 : ℝ))
    (S : Set (SourceSpace ι)) (hS : IsCompact S) (c : ℝ≥0∞) (b : Patch)
    [IsFiniteMeasure (c • (volume : Measure (SourceSpace ι)).restrict S)]
    (hL : ChartL1Data w J a ((c • volume.restrict S).prod (patchReference b)) ε hε)
    {f : SourceSpace ι × PlanarSpace → ℝ} (hf : SmoothOnChart S (patchClosed b) f)
    {φ : SourceSpace ι × PlanarSpace → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : ∀ Z ∈ patchClosed b, HasCompactSupport (fun X ↦ φ (X, Z)))
    (hφS : ∀ Z ∈ patchClosed b, tsupport (fun X ↦ φ (X, Z)) ⊆ S)
    (v : SourceSpace ι) :
    (∫ p, weight w J a p * f p * sourceD φ v p
      ∂(c • volume.restrict S).prod (patchReference b)) =
      -(∫ p, productD (weight w J a) (gradient w J a) f v p * φ p
        ∂(c • volume.restrict S).prod (patchReference b)) := by
  have hb (g : SourceSpace ι × PlanarSpace → ℝ) (hg : ContinuousOn g (S ×ˢ patchClosed b)) :
      BoundedAE ((c • volume.restrict S).prod (patchReference b)) g :=
    chart_bounded_measurable hS (isCompact_patchClosed b) (ae_mem_chart hS.measurableSet c b) hg
  have hfb : BoundedAE _ f := hb _ hf.continuousOn
  have hDfb : BoundedAE _ (sourceD f v) := hb _ (hf.continuousOn_sourceD v)
  have hφb : BoundedAE _ φ := hb _ hφ.continuous.continuousOn
  have hDφb : BoundedAE _ (sourceD φ v) :=
    hb _ ((smoothOnChart_of_contDiff hφ).continuousOn_sourceD v)
  have htL := BoundedAE.tendsto_integral_mul hL.smooth_weight hL.weight_integrable
    hL.weight_limit (hfb.mul hDφb)
  have htD := BoundedAE.tendsto_integral_mul hL.smooth_weight hL.weight_integrable
    hL.weight_limit (hDfb.mul hφb)
  have htG := tendsto_finsetSum Finset.univ fun j _ ↦
    BoundedAE.tendsto_integral_inner_mul (fun n ↦ hL.smooth_gradient n j)
      (hL.gradient_integrable j) (hL.gradient_limit j) (sourceProjection j v) (hfb.mul hφb)
  have htR := (htD.add htG).neg
  have he : ∀ᶠ n in atTop,
      (∫ p, smoothWeight w J a (ε n) (hε n) p * (f p * sourceD φ v p)
        ∂(c • volume.restrict S).prod (patchReference b)) =
      -((∫ p, smoothWeight w J a (ε n) (hε n) p * (sourceD f v p * φ p)
          ∂(c • volume.restrict S).prod (patchReference b)) +
        ∑ j, ∫ p, inner ℝ (smoothGradient w J a (ε n) (hε n) j p) (sourceProjection j v) *
          (f p * φ p) ∂(c • volume.restrict S).prod (patchReference b)) := by
    apply Eventually.of_forall
    intro n
    rw [← integral_productD_mul v (hL.smooth_weight n) (hL.smooth_gradient n) hfb hDfb hφb]
    simpa only [mul_assoc] using smooth_product_joint_identity w J a (ε n) (hε n) (hs n)
      S hS c b (hL.smooth_weight n) (hL.smooth_gradient n) hf hφ hc hφS v
  have heq := tendsto_nhds_unique (htL.congr' he) htR
  rw [← integral_productD_mul v hL.weight_integrable hL.gradient_integrable hfb hDfb hφb] at heq
  simpa only [mul_assoc] using heq

/-- Coordinates outside the retained finite family never enter the weight.
Their extension is only used to call the checked occupation-count estimate. -/
def extendedSources {N : ℕ} (I : Finset (Fin N)) (X : SourceSpace I) : Configuration N :=
  fun i ↦ if hi : i ∈ I then sources X ⟨i, hi⟩ else 0

@[simp] theorem extendedSources_subtype {N : ℕ} (I : Finset (Fin N))
    (X : SourceSpace I) (i : I) : extendedSources I X i = sources X i := by
  simp [extendedSources, i.property]

theorem measurable_extendedSources {N : ℕ} (I : Finset (Fin N)) (i : Fin N) :
    Measurable (fun X : SourceSpace I ↦ extendedSources I X i) := by
  classical
  by_cases hi : i ∈ I
  · simpa [extendedSources, hi] using (continuous_sources (⟨i, hi⟩ : I)).measurable
  · simp only [extendedSources, dite_eq_right hi]
    exact measurable_const

/-- Pullback through the actual patch quotient. Its only geometric inputs
are the occupation cap and closed-cell placement already used by the
checked `51/32` estimate. There is no analytic assumption about the limit. -/
theorem capped_chart_L1Data (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) {σ : Measure (SourceSpace I)} [IsProbabilityMeasure σ]
    (η : SourceSpace I → LabelVector J N)
    (hη : ∀ᵐ X ∂σ, OccupationCap (fixedDelta β₀ C₀ C₁) (η X))
    (hX : ∀ᵐ X ∂σ, ∀ i ∈ I, extendedSources I X i ∈ closure (meshCell J hJ (η X i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hs : ∀ n, ε n ≤ (1 / 16 : ℝ)) (ht : Tendsto ε atTop (𝓝 0)) :
    ChartL1Data (fun i : I ↦ w i) J a (σ.prod (patchReference b)) ε hε := by
  classical
  let := patchMeasure_probability J hJ a b
  have hmp : MeasurePreserving
      (Prod.map (id : SourceSpace I → SourceSpace I) (meshChart J a))
      (σ.prod (patchReference b)) (σ.prod (patchMeasure J hJ a b)) :=
    (MeasurePreserving.id σ).prod (measurePreserving_patch J hJ a b)
  obtain ⟨huW, huG⟩ := capped_joint_uniformIntegrable K hJ hN hβ hβ₀ hC₀ hmesh
    η hη I (extendedSources I) (measurable_extendedSources I) hX w hw₀ hw a b ε hε hs
  obtain ⟨hlW, hlG⟩ := capped_joint_L1 K hJ hN hβ hβ₀ hC₀ hmesh
    η hη I (extendedSources I) (measurable_extendedSources I) hX w hw₀ hw a b ε hε hs ht
  have hmW := MovingPoleWeakLimit.measurable_joint_weight sources
    (fun j : I ↦ (continuous_sources j).measurable) (fun i : I ↦ w i)
  have hmG (j : I) := MovingPoleWeakLimit.measurable_joint_sourceGradient sources
    (fun i : I ↦ (continuous_sources i).measurable) (fun i : I ↦ w i) j
  have hmsW (n : ℕ) := MovingPoleIntegrability.measurable_joint_weight sources
    (fun j : I ↦ (continuous_sources j).measurable) (fun i : I ↦ w i) (ε n) (hε n)
  have hmsG (n : ℕ) (j : I) := MovingPoleIntegrability.measurable_joint_sourceGradient sources
    (fun i : I ↦ (continuous_sources i).measurable) (fun i : I ↦ w i) (ε n) (hε n) (hs n) j
  constructor
  · intro n
    simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq,
      extendedSources_subtype, smoothWeight]
      using! hmp.integrable_comp_of_integrable (memLp_one_iff_integrable.mp (huW.memLp n))
  · intro n j
    simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq,
      extendedSources_subtype, smoothGradient]
      using! hmp.integrable_comp_of_integrable (memLp_one_iff_integrable.mp (huG.memLp (n, j)))
  · simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq,
      extendedSources_subtype, weight] using! hmp.integrable_comp_of_integrable hlW.1
  · intro j
    simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq,
      extendedSources_subtype, gradient] using! hmp.integrable_comp_of_integrable (hlG j).1
  · have he (n : ℕ) := eLpNorm_comp_measurePreserving
      ((hmsW n).aestronglyMeasurable.sub hmW.aestronglyMeasurable) hmp (p := 1)
    have hh := hlW.2
    simp only [extendedSources_subtype] at hh
    convert hh using 1
    funext n
    simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq, Pi.sub_apply,
      smoothWeight, weight] using! he n
  · intro j
    have he (n : ℕ) := eLpNorm_comp_measurePreserving
      ((hmsG n j).aestronglyMeasurable.sub (hmG j).aestronglyMeasurable) hmp (p := 1)
    have hh := (hlG j).2
    simp only [extendedSources_subtype] at hh
    convert hh using 1
    funext n
    simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq, Pi.sub_apply,
      smoothGradient, gradient] using! he n

/-- A single source may occupy either of two adjacent closed cells. Both
endpoint label vectors are required to obey the actual occupation cap.
Boundary overlap is assigned to the first endpoint; no measurable choice
or exclusion of boundary positions is needed in the cap estimate. -/
theorem exists_capped_labels_one_adjacent {J N : ℕ} (hJ : 0 < J)
    (I : Finset (Fin N)) (S : Set (SourceSpace I)) (η : LabelVector J N)
    (k : Fin N) (d : Fin 2) (δ : ℝ)
    (hcap₀ : OccupationCap δ η)
    (hcap₁ : OccupationCap δ (Function.update η k (nextCell J hJ (η k) d)))
    (hcell : ∀ X ∈ S, ∀ i ∈ I, i ≠ k →
      extendedSources I X i ∈ closure (meshCell J hJ (η i)))
    (hedge : ∀ X ∈ S, k ∈ I → extendedSources I X k ∈
      closure (edgeCellUnion J hJ (η k) d)) :
    ∃ labels : SourceSpace I → LabelVector J N,
      (∀ X, OccupationCap δ (labels X)) ∧
      ∀ X ∈ S, ∀ i ∈ I, extendedSources I X i ∈ closure (meshCell J hJ (labels X i)) := by
  classical
  let labels : SourceSpace I → LabelVector J N := fun X ↦
    if extendedSources I X k ∈ closure (meshCell J hJ (η k)) then η
      else Function.update η k (nextCell J hJ (η k) d)
  refine ⟨labels, ?_, ?_⟩
  · intro X
    dsimp [labels]
    split_ifs <;> assumption
  · intro X hX i hi
    by_cases hk : extendedSources I X k ∈ closure (meshCell J hJ (η k))
    · simp only [labels, ite_eq_left hk]
      by_cases hik : i = k
      · subst i; exact hk
      · exact hcell X hX i hi hik
    · simp only [labels, ite_eq_right hk]
      by_cases hik : i = k
      · subst i
        rw [Function.update_self]
        have he := hedge X hX hi
        rw [edgeCellUnion, closure_union] at he
        exact he.resolve_left hk
      · rw [Function.update_of_ne hik]
        exact hcell X hX i hi hik

/-- Capped chart identity with all source coordinates and arbitrary joint
tests. The geometry is pointwise on the closed chart. The next two public
wrappers construct these labels for cells or one adjacent source union. -/
theorem capped_product_joint_identity (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (S : Set (SourceSpace I)) (hS : IsCompact S) (c : ℝ≥0∞)
    [IsProbabilityMeasure (c • (volume : Measure (SourceSpace I)).restrict S)]
    (η : SourceSpace I → LabelVector J N)
    (hη : ∀ X ∈ S, OccupationCap (fixedDelta β₀ C₀ C₁) (η X))
    (hX : ∀ X ∈ S, ∀ i ∈ I, extendedSources I X i ∈ closure (meshCell J hJ (η X i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hs : ∀ n, ε n ≤ (1 / 16 : ℝ)) (ht : Tendsto ε atTop (𝓝 0))
    {f : SourceSpace I × PlanarSpace → ℝ} (hf : SmoothOnChart S (patchClosed b) f)
    {φ : SourceSpace I × PlanarSpace → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : ∀ Z ∈ patchClosed b, HasCompactSupport (fun X ↦ φ (X, Z)))
    (hφS : ∀ Z ∈ patchClosed b, tsupport (fun X ↦ φ (X, Z)) ⊆ S)
    (v : SourceSpace I) :
    (∫ p, weight (fun i : I ↦ w i) J a p * f p * sourceD φ v p
      ∂(c • volume.restrict S).prod (patchReference b)) =
      -(∫ p, productD (weight (fun i : I ↦ w i) J a) (gradient (fun i : I ↦ w i) J a)
        f v p * φ p ∂(c • volume.restrict S).prod (patchReference b)) := by
  have ha : ∀ᵐ X ∂c • (volume : Measure (SourceSpace I)).restrict S, X ∈ S :=
    Measure.ae_smul_measure (ae_restrict_mem hS.measurableSet) c
  have hL := capped_chart_L1Data K hJ hN hβ hβ₀ hC₀ hmesh I η
    (ha.mono fun X hXs ↦ hη X hXs) (ha.mono fun X hXs ↦ hX X hXs)
    w hw₀ hw a b ε hε hs ht
  exact product_joint_identity_of_L1 (fun i : I ↦ w i) J a ε hε hs S hS c b hL hf hφ hc hφS v

/-- Riesz vector of the ordinary source differential of the smooth factor. -/
def factorGradient (f : SourceSpace ι × PlanarSpace → ℝ)
    (p : SourceSpace ι × PlanarSpace) : SourceSpace ι :=
  (InnerProductSpace.toDual ℝ (SourceSpace ι)).symm
    ((fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ (SourceSpace ι) PlanarSpace))

theorem factorGradient_inner (f : SourceSpace ι × PlanarSpace → ℝ)
    (p : SourceSpace ι × PlanarSpace) (v : SourceSpace ι) :
    inner ℝ (factorGradient f p) v = sourceD f v p :=
  InnerProductSpace.toDual_symm_apply

theorem factorGradient_eq_riesz_fibre {f : SourceSpace ι × PlanarSpace → ℝ}
    {X : SourceSpace ι} {Z : PlanarSpace} (hf : DifferentiableAt ℝ f (X, Z)) :
    factorGradient f (X, Z) = (InnerProductSpace.toDual ℝ (SourceSpace ι)).symm
      (fderiv ℝ (fun Y ↦ f (Y, Z)) X) := by
  unfold factorGradient
  congr 1
  exact (hf.hasFDerivAt.comp X (hasFDerivAt_prodMk_left X Z)).fderiv.symm

theorem norm_factorGradient (f : SourceSpace ι × PlanarSpace → ℝ)
    (p : SourceSpace ι × PlanarSpace) :
    ‖factorGradient f p‖ =
      ‖(fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ (SourceSpace ι) PlanarSpace)‖ :=
  (InnerProductSpace.toDual ℝ (SourceSpace ι)).symm.norm_map _

theorem SmoothOnChart.continuousOn_factorGradient {S : Set (SourceSpace ι)}
    {B : Set PlanarSpace} {f : SourceSpace ι × PlanarSpace → ℝ}
    (hf : SmoothOnChart S B f) : ContinuousOn (factorGradient f) (S ×ˢ B) := by
  intro p hp
  exact ((InnerProductSpace.toDual ℝ (SourceSpace ι)).symm.continuous.continuousAt.comp
    (((hf.contDiffAt hp).continuousAt_fderiv one_ne_zero).clm_comp
      continuousAt_const)).continuousWithinAt

/-- Literal joint source-gradient field for the unnormalized product. -/
def productGradient (w : ι → ℝ) (J : ℕ) (a : MeshIndex J)
    (f : SourceSpace ι × PlanarSpace → ℝ) (p : SourceSpace ι × PlanarSpace) : SourceSpace ι :=
  weight w J a p • factorGradient f p +
    fullGradient (fun j ↦ f p • gradient w J a j p)

theorem productGradient_inner (w : ι → ℝ) (J : ℕ) (a : MeshIndex J)
    (f : SourceSpace ι × PlanarSpace → ℝ) (p : SourceSpace ι × PlanarSpace)
    (v : SourceSpace ι) :
    inner ℝ (productGradient w J a f p) v =
      productD (weight w J a) (gradient w J a) f v p := by
  simp only [productGradient, inner_add_left, real_inner_smul_left,
    factorGradient_inner, fullGradient_inner, productD]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem integrable_productGradient (w : ι → ℝ) (J : ℕ) (a : MeshIndex J)
    (S : Set (SourceSpace ι)) (hS : IsCompact S) (c : ℝ≥0∞) (b : Patch)
    {f : SourceSpace ι × PlanarSpace → ℝ} (hf : SmoothOnChart S (patchClosed b) f)
    (hW : Integrable (weight w J a) ((c • volume.restrict S).prod (patchReference b)))
    (hG : ∀ j, Integrable (gradient w J a j) ((c • volume.restrict S).prod (patchReference b))) :
    Integrable (productGradient w J a f) ((c • volume.restrict S).prod (patchReference b)) := by
  obtain ⟨hfm, C, _, hfb⟩ := chart_bounded_measurable hS (isCompact_patchClosed b)
    (ae_mem_chart hS.measurableSet c b) hf.continuousOn
  obtain ⟨hDm, D, _, hDb⟩ := chart_bounded_measurable hS (isCompact_patchClosed b)
    (ae_mem_chart hS.measurableSet c b) hf.continuousOn_factorGradient
  apply (hW.smul_bdd D hDm hDb).add
  apply integrable_finsetSum Finset.univ
  intro j _
  exact (sourceProjection j).adjoint.integrable_comp ((hG j).bdd_smul C hfm hfb)

def numerator (w : ι → ℝ) (J : ℕ) (a : MeshIndex J) (b : Patch)
    (f : SourceSpace ι × PlanarSpace → ℝ) (X : SourceSpace ι) : ℝ :=
  ∫ Z, weight w J a (X, Z) * f (X, Z) ∂patchReference b

def numeratorGradient (w : ι → ℝ) (J : ℕ) (a : MeshIndex J) (b : Patch)
    (f : SourceSpace ι × PlanarSpace → ℝ) (X : SourceSpace ι) : SourceSpace ι :=
  ∫ Z, productGradient w J a f (X, Z) ∂patchReference b

theorem sourceD_fst {ψ : SourceSpace ι → ℝ} (hψ : Differentiable ℝ ψ)
    (v X : SourceSpace ι) (Z : PlanarSpace) :
    sourceD (fun p : SourceSpace ι × PlanarSpace ↦ ψ p.1) v (X, Z) = fderiv ℝ ψ X v := by
  simpa only [sourceD, Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst'] using!
    congrArg (fun L : (SourceSpace ι × PlanarSpace) →L[ℝ] ℝ ↦ L (v, 0))
      ((hψ X).hasFDerivAt.comp (X, Z) hasFDerivAt_fst).fderiv

/-- Complete unnormalized weak-gradient conclusion on the source chart,
including actual Bochner integrability and the fibre integrability gates. -/
structure NumeratorWeakDerivative (w : ι → ℝ) (J : ℕ) (a : MeshIndex J) (b : Patch)
    (S : Set (SourceSpace ι)) (c : ℝ≥0∞) (f : SourceSpace ι × PlanarSpace → ℝ) : Prop where
  value_integrable : Integrable (numerator w J a b f) (c • volume.restrict S)
  gradient_integrable : Integrable (numeratorGradient w J a b f) (c • volume.restrict S)
  fibre_integrable : ∀ᵐ X ∂c • volume.restrict S,
    Integrable (fun Z ↦ weight w J a (X, Z) * f (X, Z)) (patchReference b)
  gradient_fibre_integrable : ∀ᵐ X ∂c • volume.restrict S,
    Integrable (fun Z ↦ productGradient w J a f (X, Z)) (patchReference b)
  weak_identity : ∀ (ψ : SourceSpace ι → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ S → ∀ v : SourceSpace ι,
    (∫ X, numerator w J a b f X * fderiv ℝ ψ X v ∂c • volume.restrict S) =
      -(∫ X, inner ℝ (numeratorGradient w J a b f X) v * ψ X ∂c • volume.restrict S)

theorem numerator_weakDerivative_of_L1 (w : ι → ℝ) (J : ℕ) (a : MeshIndex J)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hs : ∀ n, ε n ≤ (1 / 16 : ℝ))
    (S : Set (SourceSpace ι)) (hS : IsCompact S) (c : ℝ≥0∞) (b : Patch)
    [IsFiniteMeasure (c • (volume : Measure (SourceSpace ι)).restrict S)]
    (hL : ChartL1Data w J a ((c • volume.restrict S).prod (patchReference b)) ε hε)
    {f : SourceSpace ι × PlanarSpace → ℝ} (hf : SmoothOnChart S (patchClosed b) f) :
    NumeratorWeakDerivative w J a b S c f := by
  have hb (g : SourceSpace ι × PlanarSpace → ℝ) (hg : ContinuousOn g (S ×ˢ patchClosed b)) :
      BoundedAE ((c • volume.restrict S).prod (patchReference b)) g :=
    chart_bounded_measurable hS (isCompact_patchClosed b) (ae_mem_chart hS.measurableSet c b) hg
  have hfb : BoundedAE _ f := hb _ hf.continuousOn
  have hF := hfb.integrable_mul hL.weight_integrable
  have hV := integrable_productGradient w J a S hS c b hf hL.weight_integrable hL.gradient_integrable
  refine ⟨hF.integral_prod_left, hV.integral_prod_left, hF.prod_right_ae, hV.prod_right_ae, ?_⟩
  intro ψ hψ hc hψS v
  let φ : SourceSpace ι × PlanarSpace → ℝ := fun p ↦ ψ p.1
  have hφ : ContDiff ℝ 1 φ := hψ.comp contDiff_fst
  have hφb : BoundedAE _ φ := hb _ hφ.continuous.continuousOn
  have hDφb : BoundedAE _ (sourceD φ v) :=
    hb _ ((smoothOnChart_of_contDiff hφ).continuousOn_sourceD v)
  have hDf : BoundedAE _ (sourceD f v) := hb _ (hf.continuousOn_sourceD v)
  have hleft := hDφb.integrable_mul hF
  have hright := hφb.integrable_mul
    (integrable_productD v hL.weight_integrable hL.gradient_integrable hfb hDf)
  have he := product_joint_identity_of_L1 w J a ε hε hs S hS c b hL hf hφ
    (fun _ _ ↦ hc) (fun _ _ ↦ hψS) v
  rw [integral_prod _ hleft, integral_prod _ hright] at he
  have heL : (∫ X, ∫ Z, weight w J a (X, Z) * f (X, Z) * sourceD φ v (X, Z)
      ∂patchReference b ∂c • volume.restrict S) =
      ∫ X, numerator w J a b f X * fderiv ℝ ψ X v ∂c • volume.restrict S := by
    apply integral_congr_ae
    filter_upwards with X
    simp only [φ, sourceD_fst (hψ.differentiable one_ne_zero), integral_mul_const, numerator]
  have heR : (∫ X, ∫ Z, productD (weight w J a) (gradient w J a) f v (X, Z) * φ (X, Z)
      ∂patchReference b ∂c • volume.restrict S) =
      ∫ X, inner ℝ (numeratorGradient w J a b f X) v * ψ X ∂c • volume.restrict S := by
    apply integral_congr_ae
    filter_upwards [hV.prod_right_ae] with X hVX
    change (∫ Z, productD (weight w J a) (gradient w J a) f v (X, Z) * ψ X
      ∂patchReference b) = inner ℝ (numeratorGradient w J a b f X) v * ψ X
    rw [integral_mul_const]
    congr 1
    change (∫ Z, productD (weight w J a) (gradient w J a) f v (X, Z) ∂patchReference b) =
      inner ℝ (∫ Z, productGradient w J a f (X, Z) ∂patchReference b) v
    calc
      _ = ∫ Z, inner ℝ v (productGradient w J a f (X, Z)) ∂patchReference b := by
        apply integral_congr_ae
        filter_upwards with Z
        rw [← productGradient_inner, real_inner_comm]
      _ = _ := (integral_inner hVX v).trans (real_inner_comm _ _)
  rwa [heL, heR] at he

def approximationScale (n : ℕ) : ℝ := (1 / 32 : ℝ) * (1 / ((n : ℝ) + 1))

theorem approximationScale_pos (n : ℕ) : 0 < approximationScale n := by
  unfold approximationScale
  positivity

theorem approximationScale_small (n : ℕ) : approximationScale n ≤ (1 / 16 : ℝ) := by
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hi : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).2 hn
  unfold approximationScale
  nlinarith

theorem approximationScale_tendsto : Tendsto approximationScale atTop (𝓝 0) := by
  simpa only [approximationScale, mul_zero] using!
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 32 : ℝ)

/-- Main capped unnormalized numerator theorem. Smoothness only near the
closed product chart is required. All analytic inputs, the full product
rule, ordinary Riesz gradient, and limit passages are proved internally. -/
theorem capped_numerator_weakDerivative (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (S : Set (SourceSpace I)) (hS : IsCompact S) (c : ℝ≥0∞)
    [IsProbabilityMeasure (c • (volume : Measure (SourceSpace I)).restrict S)]
    (η : SourceSpace I → LabelVector J N)
    (hη : ∀ X ∈ S, OccupationCap (fixedDelta β₀ C₀ C₁) (η X))
    (hX : ∀ X ∈ S, ∀ i ∈ I, extendedSources I X i ∈ closure (meshCell J hJ (η X i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch)
    {f : SourceSpace I × PlanarSpace → ℝ} (hf : SmoothOnChart S (patchClosed b) f) :
    NumeratorWeakDerivative (fun i : I ↦ w i) J a b S c f := by
  have ha : ∀ᵐ X ∂c • (volume : Measure (SourceSpace I)).restrict S, X ∈ S :=
    Measure.ae_smul_measure (ae_restrict_mem hS.measurableSet) c
  have hL := capped_chart_L1Data K hJ hN hβ hβ₀ hC₀ hmesh I η
    (ha.mono fun X hXs ↦ hη X hXs) (ha.mono fun X hXs ↦ hX X hXs)
    w hw₀ hw a b approximationScale approximationScale_pos approximationScale_small
    approximationScale_tendsto
  exact numerator_weakDerivative_of_L1 (fun i : I ↦ w i) J a approximationScale
    approximationScale_pos approximationScale_small S hS c b hL hf

theorem cells_numerator_weakDerivative (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (S : Set (SourceSpace I)) (hS : IsCompact S) (c : ℝ≥0∞)
    [IsProbabilityMeasure (c • (volume : Measure (SourceSpace I)).restrict S)]
    (η : LabelVector J N) (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (hX : ∀ X ∈ S, ∀ i ∈ I, extendedSources I X i ∈ closure (meshCell J hJ (η i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch)
    {f : SourceSpace I × PlanarSpace → ℝ} (hf : SmoothOnChart S (patchClosed b) f) :
    NumeratorWeakDerivative (fun i : I ↦ w i) J a b S c f :=
  capped_numerator_weakDerivative K hJ hN hβ hβ₀ hC₀ hmesh I S hS c (fun _ ↦ η)
    (fun _ _ ↦ hη) hX w hw₀ hw a b hf

/-- One adjacent source union, with both endpoint caps explicit. This also
covers coincident sources and the common boundary of the two endpoint cells.
The integration patch can be a cell or either oriented adjacent union. -/
theorem adjacent_source_numerator_weakDerivative (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (S : Set (SourceSpace I)) (hS : IsCompact S) (c : ℝ≥0∞)
    [IsProbabilityMeasure (c • (volume : Measure (SourceSpace I)).restrict S)]
    (η : LabelVector J N) (k : Fin N) (d : Fin 2)
    (hcap₀ : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (hcap₁ : OccupationCap (fixedDelta β₀ C₀ C₁) (Function.update η k (nextCell J hJ (η k) d)))
    (hcell : ∀ X ∈ S, ∀ i ∈ I, i ≠ k →
      extendedSources I X i ∈ closure (meshCell J hJ (η i)))
    (hedge : ∀ X ∈ S, k ∈ I → extendedSources I X k ∈ closure (edgeCellUnion J hJ (η k) d))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch)
    {f : SourceSpace I × PlanarSpace → ℝ} (hf : SmoothOnChart S (patchClosed b) f) :
    NumeratorWeakDerivative (fun i : I ↦ w i) J a b S c f := by
  obtain ⟨labels, hlabels, hplace⟩ := exists_capped_labels_one_adjacent hJ I S η k d
    (fixedDelta β₀ C₀ C₁) hcap₀ hcap₁ hcell hedge
  exact capped_numerator_weakDerivative K hJ hN hβ hβ₀ hC₀ hmesh I S hS c labels
    (fun X _ ↦ hlabels X) hplace w hw₀ hw a b hf

def patchDomain (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) : Patch → Set Torus
  | .cell => meshCell J hJ a
  | .edge d => edgeCellUnion J hJ a d

def patchNormalization (J : ℕ) : Patch → ℝ≥0∞
  | .cell => (J : ℝ≥0∞) ^ 2
  | .edge _ => (J : ℝ≥0∞) ^ 2 / 2

def patchArea (J : ℕ) (b : Patch) : ℝ := (patchNormalization J b).toReal⁻¹

theorem patchNormalization_ne_zero {J : ℕ} (hJ : 0 < J) (b : Patch) :
    patchNormalization J b ≠ 0 := by
  cases b <;> simp [patchNormalization, hJ.ne']

theorem patchNormalization_ne_top (J : ℕ) (b : Patch) : patchNormalization J b ≠ (∞ : ℝ≥0∞) := by
  cases b with
  | cell => exact ENNReal.pow_ne_top (ENNReal.natCast_ne_top J)
  | edge d =>
    exact ENNReal.div_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top J)) (by norm_num)

theorem patchArea_pos {J : ℕ} (hJ : 0 < J) (b : Patch) : 0 < patchArea J b :=
  inv_pos.mpr (ENNReal.toReal_pos (patchNormalization_ne_zero hJ b) (patchNormalization_ne_top J b))

theorem patchArea_cell (J : ℕ) : patchArea J .cell = 1 / (J : ℝ) ^ 2 := by
  simp [patchArea, patchNormalization, one_div]

theorem patchArea_edge (J : ℕ) (d : Fin 2) : patchArea J (.edge d) = 2 / (J : ℝ) ^ 2 := by
  simp [patchArea, patchNormalization, div_eq_mul_inv, mul_comm]

theorem patchMeasure_eq_normalized {J : ℕ} (hJ : 0 < J) (hJ₂ : 2 ≤ J)
    (a : MeshIndex J) (b : Patch) :
    patchMeasure J hJ a b = patchNormalization J b • torusMeasure.restrict (patchDomain J hJ a b) := by
  cases b with
  | cell => rfl
  | edge d => exact edgeCellMeasure_eq_normalized J hJ hJ₂ a d

def torusFactor (F : SourceSpace ι → Torus → ℝ) (J : ℕ) (a : MeshIndex J)
    (p : SourceSpace ι × PlanarSpace) : ℝ := F p.1 (meshChart J a p.2)

/-- The manuscript numerator with raw restricted Haar measure, not the
mass-one patch law used to prove the singular moment estimates. -/
def rawNumerator (w : ι → ℝ) (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (b : Patch)
    (F : SourceSpace ι → Torus → ℝ) (X : SourceSpace ι) : ℝ :=
  ∫ z in patchDomain J hJ a b, torusWeight (sources X) w z * F X z ∂torusMeasure

theorem rawNumerator_eq_scaled (w : ι → ℝ) {J : ℕ} (hJ : 0 < J) (hJ₂ : 2 ≤ J)
    (a : MeshIndex J) (b : Patch) (F : SourceSpace ι → Torus → ℝ) (X : SourceSpace ι)
    (hF : AEStronglyMeasurable (F X) (patchMeasure J hJ a b)) :
    rawNumerator w J hJ a b F X =
      patchArea J b * numerator w J a b (torusFactor F J a) X := by
  have hm := (measurable_torusWeight (sources X) w).aestronglyMeasurable.mul hF
  have hmp := measurePreserving_patch J hJ a b
  have he : numerator w J a b (torusFactor F J a) X =
      ∫ z, torusWeight (sources X) w z * F X z ∂patchMeasure J hJ a b := by
    change (∫ Z, (torusWeight (sources X) w (meshChart J a Z) * F X (meshChart J a Z))
      ∂patchReference b) = _
    rw [← hmp.map_eq] at hm ⊢
    exact (integral_map hmp.aemeasurable hm).symm
  rw [patchMeasure_eq_normalized hJ hJ₂ a b, integral_smul_measure] at he
  rw [rawNumerator, he, patchArea, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (ENNReal.toReal_ne_zero.mpr
      ⟨patchNormalization_ne_zero hJ b, patchNormalization_ne_top J b⟩), one_mul]

theorem integrable_rawFibre_of_reference (w : ι → ℝ) {J : ℕ}
    (hJ : 0 < J) (hJ₂ : 2 ≤ J) (a : MeshIndex J) (b : Patch)
    (F : SourceSpace ι → Torus → ℝ) (X : SourceSpace ι)
    (hF : AEStronglyMeasurable (F X) (patchMeasure J hJ a b))
    (hi : Integrable (fun Z ↦ weight w J a (X, Z) * torusFactor F J a (X, Z)) (patchReference b)) :
    Integrable (fun z ↦ torusWeight (sources X) w z * F X z)
      (torusMeasure.restrict (patchDomain J hJ a b)) := by
  have hm := (measurable_torusWeight (sources X) w).aestronglyMeasurable.mul hF
  have h := ((measurePreserving_patch J hJ a b).integrable_comp hm).mp hi
  rw [patchMeasure_eq_normalized hJ hJ₂ a b] at h
  exact (integrable_smul_measure (patchNormalization_ne_zero hJ b)
    (patchNormalization_ne_top J b)).mp h

/-- Exact scaling of an already proved unnormalized weak gradient from
the patch probability law to the manuscript's raw restricted Haar integral.
The measurability premise is local to the patch and does not constrain the
factor away from it. The constant factor is `J⁻²` or `2 J⁻²`. -/
theorem raw_numerator_weak_identity (w : ι → ℝ) {J : ℕ}
    (hJ : 0 < J) (hJ₂ : 2 ≤ J) (a : MeshIndex J) (b : Patch)
    (S : Set (SourceSpace ι)) (c : ℝ≥0∞) (F : SourceSpace ι → Torus → ℝ)
    (hF : ∀ᵐ X ∂c • volume.restrict S, AEStronglyMeasurable (F X) (patchMeasure J hJ a b))
    (hN : NumeratorWeakDerivative w J a b S c (torusFactor F J a)) :
    Integrable (rawNumerator w J hJ a b F) (c • volume.restrict S) ∧
    Integrable (fun X ↦ patchArea J b • numeratorGradient w J a b (torusFactor F J a) X)
      (c • volume.restrict S) ∧
    (∀ᵐ X ∂c • volume.restrict S, Integrable (fun z ↦ torusWeight (sources X) w z * F X z)
      (torusMeasure.restrict (patchDomain J hJ a b))) ∧
    ∀ (ψ : SourceSpace ι → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ S →
      ∀ v : SourceSpace ι,
      (∫ X, rawNumerator w J hJ a b F X * fderiv ℝ ψ X v ∂c • volume.restrict S) =
        -(∫ X, inner ℝ (patchArea J b • numeratorGradient w J a b (torusFactor F J a) X) v * ψ X
          ∂c • volume.restrict S) := by
  have he : rawNumerator w J hJ a b F =ᵐ[c • volume.restrict S]
      fun X ↦ patchArea J b * numerator w J a b (torusFactor F J a) X :=
    hF.mono fun X hFX ↦ rawNumerator_eq_scaled w hJ hJ₂ a b F X hFX
  refine ⟨(hN.value_integrable.const_mul _).congr he.symm,
    Integrable.smul (patchArea J b) hN.gradient_integrable, ?_, ?_⟩
  · filter_upwards [hF, hN.fibre_integrable] with X hFX hNX
    exact integrable_rawFibre_of_reference w hJ hJ₂ a b F X hFX hNX
  · intro ψ hψ hc hψS v
    calc
      _ = patchArea J b *
          (∫ X, numerator w J a b (torusFactor F J a) X * fderiv ℝ ψ X v
            ∂c • volume.restrict S) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [he] with X hX
        rw [hX, mul_assoc]
      _ = -(patchArea J b *
          (∫ X, inner ℝ (numeratorGradient w J a b (torusFactor F J a) X) v * ψ X
            ∂c • volume.restrict S)) := by
        rw [hN.weak_identity ψ hψ hc hψS v, mul_neg]
      _ = _ := by
        rw [← integral_const_mul]
        simp only [real_inner_smul_left, mul_assoc]

/-- Constant smooth factor: the value is the actual normalizer. This
specialization requires no measurability hypothesis for an auxiliary factor. -/
theorem capped_normalizer_weak_identity (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (S : Set (SourceSpace I)) (hS : IsCompact S) (c : ℝ≥0∞)
    [IsProbabilityMeasure (c • (volume : Measure (SourceSpace I)).restrict S)]
    (η : SourceSpace I → LabelVector J N)
    (hη : ∀ X ∈ S, OccupationCap (fixedDelta β₀ C₀ C₁) (η X))
    (hX : ∀ X ∈ S, ∀ i ∈ I, extendedSources I X i ∈ closure (meshCell J hJ (η X i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) :
    Integrable (rawNumerator (fun i : I ↦ w i) J hJ a b (fun _ _ ↦ 1)) (c • volume.restrict S) ∧
    ∀ (ψ : SourceSpace I → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ S →
      ∀ v : SourceSpace I,
      (∫ X, rawNumerator (fun i : I ↦ w i) J hJ a b (fun _ _ ↦ 1) X * fderiv ℝ ψ X v
        ∂c • volume.restrict S) =
      -(∫ X, inner ℝ (patchArea J b • numeratorGradient (fun i : I ↦ w i) J a b
        (fun _ ↦ 1) X) v * ψ X ∂c • volume.restrict S) := by
  have hJ₂ : 2 ≤ J := by omega
  have hnum := capped_numerator_weakDerivative K hJ hN hβ hβ₀ hC₀ hmesh I S hS c
    η hη hX w hw₀ hw a b
      (smoothOnChart_of_contDiff (f := fun _ : SourceSpace I × PlanarSpace ↦ (1 : ℝ)) contDiff_const)
  have hraw := raw_numerator_weak_identity (fun i : I ↦ w i) hJ hJ₂ a b S c
    (fun _ _ ↦ 1) (ae_of_all _ fun _ ↦ aestronglyMeasurable_const) hnum
  exact ⟨hraw.1, hraw.2.2.2⟩

/-- Every fixed source placement satisfying the cap, including coincident
placements, has finite actual unregularized weight and gradient integrals.
Using a Dirac source law avoids replacing this assertion by an AE assertion. -/
theorem capped_fixed_fibre_integrable (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (X : SourceSpace I) (η : LabelVector J N)
    (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (hX : ∀ i ∈ I, extendedSources I X i ∈ closure (meshCell J hJ (η i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) :
    Integrable (fun Z ↦ weight (fun i : I ↦ w i) J a (X, Z)) (patchReference b) ∧
    ∀ j : I, Integrable (fun Z ↦ gradient (fun i : I ↦ w i) J a j (X, Z)) (patchReference b) := by
  have hcap : ∀ᵐ Y ∂Measure.dirac X, OccupationCap (fixedDelta β₀ C₀ C₁) η :=
    ae_of_all _ fun _ ↦ hη
  have hplace : ∀ᵐ Y ∂Measure.dirac X, ∀ i ∈ I,
      extendedSources I Y i ∈ closure (meshCell J hJ (η i)) := by
    simpa only [ae_dirac_eq, Filter.eventually_pure] using hX
  have hL := capped_chart_L1Data (σ := Measure.dirac X) K hJ hN hβ hβ₀ hC₀ hmesh I
    (fun _ ↦ η) hcap hplace w hw₀ hw a b approximationScale approximationScale_pos
    approximationScale_small approximationScale_tendsto
  constructor
  · simpa only [ae_dirac_eq, Filter.eventually_pure] using hL.weight_integrable.prod_right_ae
  · intro j
    simpa only [ae_dirac_eq, Filter.eventually_pure] using
      (hL.gradient_integrable j).prod_right_ae

theorem factorGradient_const (r : ℝ) (p : SourceSpace ι × PlanarSpace) :
    factorGradient (fun _ ↦ r) p = 0 := by
  simp [factorGradient]

theorem productGradient_one (w : ι → ℝ) (J : ℕ) (a : MeshIndex J)
    (p : SourceSpace ι × PlanarSpace) :
    productGradient w J a (fun _ ↦ 1) p = fullGradient (fun j ↦ gradient w J a j p) := by
  simp only [productGradient, factorGradient_const, smul_zero, one_smul, zero_add]

theorem numeratorGradient_one (w : ι → ℝ) (J : ℕ) (a : MeshIndex J) (b : Patch)
    (X : SourceSpace ι) :
    numeratorGradient w J a b (fun _ ↦ 1) X =
      ∫ Z, fullGradient (fun j ↦ (-w j * weight w J a (X, Z)) •
        greenGradient (meshChart J a Z - sources X j)) ∂patchReference b := by
  simp only [numeratorGradient, productGradient_one, gradient, sourceGradient, weight]

/-- Exact physical normalization of a finite closed source chart. The
positive-volume condition below follows from nonempty interior, not from
an assumed probability instance. -/
def sourceChartMeasure (S : Set (SourceSpace ι)) : Measure (SourceSpace ι) :=
  ((volume : Measure (SourceSpace ι)) S)⁻¹ • volume.restrict S

theorem sourceChartMeasure_probability {S : Set (SourceSpace ι)}
    (hS : IsCompact S) (hint : (interior S).Nonempty) : IsProbabilityMeasure (sourceChartMeasure S) := by
  have hp : (volume : Measure (SourceSpace ι)) S ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior volume hint).ne'
  have ht : (volume : Measure (SourceSpace ι)) S ≠ (∞ : ℝ≥0∞) := hS.measure_lt_top.ne
  constructor
  simp only [sourceChartMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
    ENNReal.inv_mul_cancel hp ht]

/-- The closed source chart is integrated against its actual normalized
Lebesgue restriction. No pre-existing probability instance is required. -/
theorem normalized_chart_numerator_weakDerivative (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (S : Set (SourceSpace I)) (hS : IsCompact S) (hint : (interior S).Nonempty)
    (η : SourceSpace I → LabelVector J N)
    (hη : ∀ X ∈ S, OccupationCap (fixedDelta β₀ C₀ C₁) (η X))
    (hX : ∀ X ∈ S, ∀ i ∈ I, extendedSources I X i ∈ closure (meshCell J hJ (η X i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch)
    {f : SourceSpace I × PlanarSpace → ℝ} (hf : SmoothOnChart S (patchClosed b) f) :
    NumeratorWeakDerivative (fun i : I ↦ w i) J a b S
      (((volume : Measure (SourceSpace I)) S)⁻¹) f := by
  have : IsProbabilityMeasure
      ((((volume : Measure (SourceSpace I)) S)⁻¹) • volume.restrict S) := by
    simpa only [sourceChartMeasure] using sourceChartMeasure_probability hS hint
  exact capped_numerator_weakDerivative K hJ hN hβ hβ₀ hC₀ hmesh I S hS _
    η hη hX w hw₀ hw a b hf

/-- Actual raw-Haar numerator endpoint for a local smooth torus factor.
Only AE measurability on the integration patch is required separately;
neither regularity nor boundedness is required outside the closed chart. -/
theorem capped_rawNumerator_weak_identity (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (S : Set (SourceSpace I)) (hS : IsCompact S) (c : ℝ≥0∞)
    [IsProbabilityMeasure (c • (volume : Measure (SourceSpace I)).restrict S)]
    (η : SourceSpace I → LabelVector J N)
    (hη : ∀ X ∈ S, OccupationCap (fixedDelta β₀ C₀ C₁) (η X))
    (hX : ∀ X ∈ S, ∀ i ∈ I, extendedSources I X i ∈ closure (meshCell J hJ (η X i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) (F : SourceSpace I → Torus → ℝ)
    (hf : SmoothOnChart S (patchClosed b) (torusFactor F J a))
    (hFm : ∀ᵐ X ∂c • volume.restrict S, AEStronglyMeasurable (F X) (patchMeasure J hJ a b)) :
    Integrable (rawNumerator (fun i : I ↦ w i) J hJ a b F) (c • volume.restrict S) ∧
    Integrable (fun X ↦ patchArea J b • numeratorGradient (fun i : I ↦ w i) J a b
      (torusFactor F J a) X) (c • volume.restrict S) ∧
    (∀ᵐ X ∂c • volume.restrict S, Integrable (fun z ↦ torusWeight (sources X) (fun i : I ↦ w i) z * F X z)
      (torusMeasure.restrict (patchDomain J hJ a b))) ∧
    ∀ (ψ : SourceSpace I → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ S →
      ∀ v : SourceSpace I,
      (∫ X, rawNumerator (fun i : I ↦ w i) J hJ a b F X * fderiv ℝ ψ X v ∂c • volume.restrict S) =
        -(∫ X, inner ℝ (patchArea J b • numeratorGradient (fun i : I ↦ w i) J a b
          (torusFactor F J a) X) v * ψ X ∂c • volume.restrict S) := by
  have hJ₂ : 2 ≤ J := by omega
  exact raw_numerator_weak_identity (fun i : I ↦ w i) hJ hJ₂ a b S c F hFm
    (capped_numerator_weakDerivative K hJ hN hβ hβ₀ hC₀ hmesh I S hS c
      η hη hX w hw₀ hw a b hf)

/-- A positive finite scalar multiplying the source Lebesgue measure does
not change the distributional derivative. This removes the source-chart
probability normalization from the weak conclusion. -/
theorem NumeratorWeakDerivative.volume {w : ι → ℝ} {J : ℕ} {a : MeshIndex J} {b : Patch}
    {S : Set (SourceSpace ι)} {c : ℝ≥0∞} {f : SourceSpace ι × PlanarSpace → ℝ}
    (h : NumeratorWeakDerivative w J a b S c f) (hc₀ : c ≠ 0) (hc_top : c ≠ (∞ : ℝ≥0∞)) :
    NumeratorWeakDerivative w J a b S 1 f := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [one_smul] using (integrable_smul_measure hc₀ hc_top).mp h.value_integrable
  · simpa only [one_smul] using (integrable_smul_measure hc₀ hc_top).mp h.gradient_integrable
  · simpa only [one_smul] using
      (Measure.ae_ennreal_smul_measure_iff hc₀).mp h.fibre_integrable
  · simpa only [one_smul] using
      (Measure.ae_ennreal_smul_measure_iff hc₀).mp h.gradient_fibre_integrable
  · intro ψ hψ hs hsub v
    have he := h.weak_identity ψ hψ hs hsub v
    simp only [integral_smul_measure, smul_eq_mul, ← mul_neg] at he
    simpa only [one_smul] using
      (mul_left_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hc₀, hc_top⟩) he)

theorem NumeratorWeakDerivative.normalized_volume {w : ι → ℝ} {J : ℕ}
    {a : MeshIndex J} {b : Patch} {S : Set (SourceSpace ι)}
    {f : SourceSpace ι × PlanarSpace → ℝ} (hS : IsCompact S) (hint : (interior S).Nonempty)
    (h : NumeratorWeakDerivative w J a b S (((MeasureTheory.volume : Measure (SourceSpace ι)) S)⁻¹) f) :
    NumeratorWeakDerivative w J a b S 1 f :=
  h.volume (ENNReal.inv_ne_zero.mpr hS.measure_lt_top.ne)
    (ENNReal.inv_ne_top.mpr
      (Measure.measure_pos_of_nonempty_interior MeasureTheory.volume hint).ne')

theorem bounded_measurable_on_patch {V : Type*} [NormedAddCommGroup V]
    (b : Patch) {g : PlanarSpace → V} (hg : ContinuousOn g (patchClosed b)) :
    AEStronglyMeasurable g (patchReference b) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ᵐ Z ∂patchReference b, ‖g Z‖ ≤ C := by
  have hm : AEStronglyMeasurable g ((patchReference b).restrict (patchClosed b)) :=
    hg.aestronglyMeasurable (μ := patchReference b) (isCompact_patchClosed b).measurableSet
  rw [Measure.restrict_eq_self_of_ae_mem (ae_mem_patchClosed b)] at hm
  obtain ⟨C, hC, hb⟩ := ((isCompact_patchClosed b).image_of_continuousOn hg).isBounded.exists_pos_norm_le
  exact ⟨hm, C, hC, (ae_mem_patchClosed b).mono fun Z hZ ↦ hb (g Z) (mem_image_of_mem g hZ)⟩

/-- Fixed-source integrability for the full factor product and its entire
physical Riesz-gradient field. This includes boundary and coincident source
positions and does not discard them by an AE qualification. -/
theorem capped_fixed_productFibre_integrable (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (I : Finset (Fin N)) (S : Set (SourceSpace I)) (X : SourceSpace I) (hXS : X ∈ S)
    (η : LabelVector J N) (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (hX : ∀ i ∈ I, extendedSources I X i ∈ closure (meshCell J hJ (η i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) {f : SourceSpace I × PlanarSpace → ℝ}
    (hf : SmoothOnChart S (patchClosed b) f) :
    Integrable (fun Z ↦ weight (fun i : I ↦ w i) J a (X, Z) * f (X, Z)) (patchReference b) ∧
    Integrable (fun Z ↦ productGradient (fun i : I ↦ w i) J a f (X, Z)) (patchReference b) := by
  obtain ⟨hW, hG⟩ := capped_fixed_fibre_integrable K hJ hN hβ hβ₀ hC₀ hmesh I X η
    hη hX w hw₀ hw a b
  have hfc : ContinuousOn (fun Z ↦ f (X, Z)) (patchClosed b) := by
    intro Z hZ
    exact ((hf.contDiffAt ⟨hXS, hZ⟩).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have hDc : ContinuousOn (fun Z ↦ factorGradient f (X, Z)) (patchClosed b) := by
    apply hf.continuousOn_factorGradient.comp (continuous_const.prodMk continuous_id).continuousOn
    intro Z hZ
    exact ⟨hXS, hZ⟩
  obtain ⟨hfm, C, _, hfb⟩ := bounded_measurable_on_patch b hfc
  obtain ⟨hDm, D, _, hDb⟩ := bounded_measurable_on_patch b hDc
  refine ⟨hW.mul_bdd hfm hfb, ?_⟩
  apply (hW.smul_bdd D hDm hDb).add
  apply integrable_finsetSum Finset.univ
  intro j _
  exact (sourceProjection j).adjoint.integrable_comp ((hG j).bdd_smul C hfm hfb)

end PeriodicAttractiveLogGas.MovingPoleNumerators
