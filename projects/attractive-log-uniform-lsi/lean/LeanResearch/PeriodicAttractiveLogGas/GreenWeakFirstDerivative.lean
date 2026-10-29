import LeanResearch.PeriodicAttractiveLogGas.GreenConvolution
import LeanResearch.PeriodicAttractiveLogGas.LogRegularization
import LeanResearch.PeriodicAttractiveLogGas.GreenIntegrability
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Actual first-derivative integration by parts for the local Green
convolution. Integrability of the classical gradient is used only for
integrability. The weak derivative identity at the pole is proved separately
from the exact local expansion and the checked logarithmic weak identity.
-/

noncomputable section
open MeasureTheory Metric Set Filter InnerProductSpace
open scoped Topology ContDiff Convolution RealInnerProductSpace

namespace PeriodicAttractiveLogGas

theorem integrable_greenDifferential_apply (v : PlanarSpace) :
    Integrable (fun z ↦ greenDifferential z v) torusMeasure := by
  have heq : (fun z ↦ greenDifferential z v) =
      (fun z ↦ innerSL ℝ v (greenGradient z)) := by
    funext z
    rw [innerSL_apply_apply, real_inner_comm, greenGradient_inner]
  rw [heq]
  exact (innerSL ℝ v).integrable_comp integrable_greenGradient

theorem locallyIntegrable_fderiv_regularGreenLift_apply (v : PlanarSpace) :
    LocallyIntegrable (fun x ↦ fderiv ℝ regularGreenLift x v) volume := by
  simpa only [greenDifferential_lift] using
    locallyIntegrable_torus_lift (integrable_greenDifferential_apply v)

theorem integrable_fderiv_regularGreenLift_mul (v : PlanarSpace)
    {g : PlanarSpace → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) :
    Integrable (fun y ↦ fderiv ℝ regularGreenLift y v * g y) volume :=
  (locallyIntegrable_fderiv_regularGreenLift_apply v).integrable_smul_right_of_hasCompactSupport hg hc

/-- A compact multiplier permits local continuity of the other factor.
No measurability or continuity outside the multiplier's support is assumed. -/
theorem integrable_mul_of_continuousAt_on_tsupport {f g : PlanarSpace → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g)
    (hf : ∀ x ∈ tsupport g, ContinuousAt f x) :
    Integrable (fun x ↦ f x * g x) volume := by
  have hp : Continuous (fun x ↦ f x * g x) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x ∈ tsupport g
    · exact (hf x hx).mul hg.continuousAt
    · apply (continuousAt_const : ContinuousAt (fun _ : PlanarSpace ↦ (0 : ℝ)) x).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hx] with y hy
      simp only [image_eq_zero_of_notMem_tsupport hy, mul_zero]
  exact hp.integrable_of_hasCompactSupport hc.mul_left

def greenSmoothLocalPart (x : PlanarSpace) : ℝ :=
  planarGreenQuadratic x + smoothGreenLogRemainder x

theorem contDiffOn_greenSmoothLocalPart :
    ContDiffOn ℝ ∞ greenSmoothLocalPart (euclideanOpenBox (centeredBoxAnchor 0)) :=
  contDiff_planarGreenQuadratic.contDiffOn.add contDiffOn_smoothGreenLogRemainder

theorem regularGreenLift_eventuallyEq_log_add_localPart {x : PlanarSpace}
    (hx : x ∈ euclideanOpenBox (centeredBoxAnchor 0)) (hne : x ≠ 0) :
    regularGreenLift =ᶠ[𝓝 x] (fun y ↦ planarLogKernel y + greenSmoothLocalPart y) := by
  filter_upwards [(isOpen_euclideanOpenBox _).mem_nhds hx,
    eventually_ne_nhds hne] with y hy hyne
  rw [regularGreenLift_of_mem (mem_offIntegerLattice_of_mem_centeredOpenBox hy hyne),
    smoothGreenLift_local_expansion hy hyne]
  simp only [greenSmoothLocalPart, add_assoc]

theorem fderiv_regularGreenLift_localPart {x : PlanarSpace}
    (hx : x ∈ euclideanOpenBox (centeredBoxAnchor 0)) (hne : x ≠ 0) :
    fderiv ℝ regularGreenLift x =
      fderiv ℝ planarLogKernel x + fderiv ℝ greenSmoothLocalPart x := by
  rw [(regularGreenLift_eventuallyEq_log_add_localPart hx hne).fderiv_eq]
  have hd := ((contDiffAt_planarLogKernel hne).differentiableAt (by simp)).hasFDerivAt.add
    ((contDiffOn_greenSmoothLocalPart.contDiffAt
      ((isOpen_euclideanOpenBox _).mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  exact hd.fderiv

/-- Ordinary weak first integration by parts across the Green pole, for
every compact C1 test supported in the closed quarter ball. -/
theorem integral_regularGreenLift_mul_fderiv_eq_neg_fderiv_mul_local
    {g : PlanarSpace → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ closedBall (0 : PlanarSpace) (1 / 4 : ℝ)) (v : PlanarSpace) :
    (∫ y, regularGreenLift y * fderiv ℝ g y v) =
      -(∫ y, fderiv ℝ regularGreenLift y v * g y) := by
  have hU : tsupport g ⊆ euclideanOpenBox (centeredBoxAnchor 0) :=
    hs.trans closedBall_quarter_subset_centeredOpenBox
  have hgc : Continuous (fun y ↦ fderiv ℝ g y v) :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hgs : tsupport (fun y ↦ fderiv ℝ g y v) ⊆ tsupport g :=
    tsupport_fderiv_apply_subset ℝ v
  have hF (y) (hy : y ∈ tsupport g) : ContDiffAt ℝ ∞ greenSmoothLocalPart y :=
    contDiffOn_greenSmoothLocalPart.contDiffAt ((isOpen_euclideanOpenBox _).mem_nhds (hU hy))
  have hFd (y) (hy : y ∈ tsupport g) : ContinuousAt (fderiv ℝ greenSmoothLocalPart) y :=
    ((contDiffOn_greenSmoothLocalPart.fderiv_of_isOpen (m := ∞) (isOpen_euclideanOpenBox _)
      (by simp)).contDiffAt ((isOpen_euclideanOpenBox _).mem_nhds (hU hy))).continuousAt
  have hFg : Integrable (fun y ↦ greenSmoothLocalPart y * g y) volume :=
    integrable_mul_of_continuousAt_on_tsupport hg.continuous hc
      (fun y hy ↦ (hF y hy).continuousAt)
  have hFg' : Integrable (fun y ↦ greenSmoothLocalPart y * fderiv ℝ g y v) volume :=
    integrable_mul_of_continuousAt_on_tsupport hgc (hc.fderiv_apply ℝ v)
      (fun y hy ↦ (hF y (hgs hy)).continuousAt)
  have hF'g : Integrable (fun y ↦ fderiv ℝ greenSmoothLocalPart y v * g y) volume :=
    integrable_mul_of_continuousAt_on_tsupport hg.continuous hc
      (fun y hy ↦ (hFd y hy).clm_apply continuousAt_const)
  have hFibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := greenSmoothLocalPart) (g := g) (v := v) hF'g hFg' hFg
    (fun y hy ↦ (hF y hy).differentiableAt (by simp))
    (fun y _ ↦ hg.differentiable one_ne_zero y)
  have hleft : (fun y ↦ regularGreenLift y * fderiv ℝ g y v) =ᵐ[volume]
      (fun y ↦ planarLogKernel y * fderiv ℝ g y v +
        greenSmoothLocalPart y * fderiv ℝ g y v) := by
    filter_upwards [volume.ae_ne (0 : PlanarSpace)] with y hyne
    by_cases hy : y ∈ tsupport g
    · rw [(regularGreenLift_eventuallyEq_log_add_localPart (hU hy) hyne).eq_of_nhds]
      ring
    · rw [fderiv_of_notMem_tsupport ℝ hy]
      simp
  have hright : (fun y ↦ fderiv ℝ regularGreenLift y v * g y) =ᵐ[volume]
      (fun y ↦ fderiv ℝ planarLogKernel y v * g y +
        fderiv ℝ greenSmoothLocalPart y v * g y) := by
    filter_upwards [volume.ae_ne (0 : PlanarSpace)] with y hyne
    by_cases hy : y ∈ tsupport g
    · rw [fderiv_regularGreenLift_localPart (hU hy) hyne, add_apply]
      ring
    · simp only [image_eq_zero_of_notMem_tsupport hy, mul_zero, add_zero]
  rw [integral_congr_ae hleft,
    integral_add (integrable_planarLogKernel_mul_fderiv hg hc v) hFg',
    integral_congr_ae hright,
    integral_add (integrable_fderiv_planarLogKernel_mul v hg.continuous hc) hF'g,
    integral_planarLogKernel_mul_fderiv_eq_neg_fderiv_mul hg hc v, hFibp]
  ring

def translatedScaledMollifier (ε : ℝ) (x y : PlanarSpace) : ℝ :=
  scaledRadialMollifier ε (x - y)

theorem contDiff_translatedScaledMollifier (ε : ℝ) (x : PlanarSpace) :
    ContDiff ℝ ∞ (translatedScaledMollifier ε x) :=
  (contDiff_scaledRadialMollifier ε).comp (contDiff_const.sub contDiff_id)

theorem hasCompactSupport_translatedScaledMollifier (ε : ℝ) (hε : 0 < ε)
    (x : PlanarSpace) : HasCompactSupport (translatedScaledMollifier ε x) := by
  change HasCompactSupport (scaledRadialMollifier ε ∘ Homeomorph.subLeft x)
  exact (hasCompactSupport_scaledRadialMollifier ε hε).comp_homeomorph (Homeomorph.subLeft x)

theorem tsupport_translatedScaledMollifier_subset (ε : ℝ) (hε : 0 < ε)
    (x : PlanarSpace) :
    tsupport (translatedScaledMollifier ε x) ⊆ closedBall x (ε / 2) := by
  have hts : tsupport (translatedScaledMollifier ε x) =
      (Homeomorph.subLeft x) ⁻¹' tsupport (scaledRadialMollifier ε) := by
    change tsupport (scaledRadialMollifier ε ∘ Homeomorph.subLeft x) = _
    exact tsupport_comp_eq_preimage (scaledRadialMollifier ε) (Homeomorph.subLeft x)
  rw [hts]
  intro y hy
  have hb := tsupport_scaledRadialMollifier_subset_closedBall ε hε hy
  change x - y ∈ closedBall (0 : PlanarSpace) (ε / 2) at hb
  have hn : ‖x - y‖ ≤ ε / 2 := by simpa only [mem_closedBall, dist_zero_right] using hb
  simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hn

theorem fderiv_translatedScaledMollifier_apply (ε : ℝ) (x y v : PlanarSpace) :
    fderiv ℝ (translatedScaledMollifier ε x) y v =
      -(fderiv ℝ (scaledRadialMollifier ε) (x - y) v) := by
  have hd := ((contDiff_scaledRadialMollifier ε).differentiable (by simp) (x - y)).hasFDerivAt.comp y
    ((hasFDerivAt_id y).const_sub x)
  change fderiv ℝ (scaledRadialMollifier ε ∘ HSub.hSub x) y v = _
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.id_apply, map_neg]

/-- The far-support condition is geometric and excludes every integer pole. -/
theorem translatedScaledMollifier_support_off_lattice (ε : ℝ) (hε : 0 < ε)
    {x : PlanarSpace} (hx : 2 * ε ≤ torusEuclideanNorm (torusQuotient x)) :
    tsupport (translatedScaledMollifier ε x) ⊆ offIntegerLattice := by
  intro y hy
  have hball := tsupport_translatedScaledMollifier_subset ε hε x hy
  have hdist : ‖x - y‖ ≤ ε / 2 := by
    simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hball
  change torusQuotient y ≠ 0
  intro hz
  have ht := torusEuclideanDist_quotient_le x y
  rw [hz, torusEuclideanDist_zero, dist_eq_norm] at ht
  linarith

theorem integral_regularGreenLift_mul_fderiv_eq_neg_fderiv_mul_off_lattice
    {g : PlanarSpace → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ offIntegerLattice) (v : PlanarSpace) :
    (∫ y, regularGreenLift y * fderiv ℝ g y v) =
      -(∫ y, fderiv ℝ regularGreenLift y v * g y) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact integrable_fderiv_regularGreenLift_mul v hg.continuous hc
  · exact locallyIntegrable_regularGreenLift.integrable_smul_right_of_hasCompactSupport
      ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hc.fderiv_apply ℝ v)
  · exact locallyIntegrable_regularGreenLift.integrable_smul_right_of_hasCompactSupport hg.continuous hc
  · intro y hy
    exact (contDiffOn_regularGreenLift.contDiffAt
      (isOpen_offIntegerLattice.mem_nhds (hs hy))).differentiableAt (by simp)
  · intro y _
    exact hg.differentiable one_ne_zero y

/-- Every centered convolution test is handled either by the actual local
weak identity across the pole or by ordinary off-lattice integration by parts. -/
theorem integral_regularGreenLift_mul_fderiv_translatedScaledMollifier
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ (1 / 16 : ℝ)) (z : Torus) (v : PlanarSpace) :
    (∫ y, regularGreenLift y *
      fderiv ℝ (translatedScaledMollifier ε (centeredLift z)) y v) =
      -(∫ y, fderiv ℝ regularGreenLift y v * translatedScaledMollifier ε (centeredLift z) y) := by
  have hg : ContDiff ℝ 1 (translatedScaledMollifier ε (centeredLift z)) :=
    (contDiff_translatedScaledMollifier ε (centeredLift z)).of_le (by simp)
  have hc := hasCompactSupport_translatedScaledMollifier ε hε (centeredLift z)
  by_cases hfar : 2 * ε ≤ torusEuclideanNorm z
  · exact integral_regularGreenLift_mul_fderiv_eq_neg_fderiv_mul_off_lattice hg hc
      (translatedScaledMollifier_support_off_lattice ε hε
        (by simpa only [torusQuotient_centeredLift] using hfar)) v
  · apply integral_regularGreenLift_mul_fderiv_eq_neg_fderiv_mul_local hg hc _ v
    intro y hy
    have hball := tsupport_translatedScaledMollifier_subset ε hε (centeredLift z) hy
    have hd : ‖y - centeredLift z‖ ≤ ε / 2 := by
      simpa only [mem_closedBall, dist_eq_norm] using hball
    have hx : ‖centeredLift z‖ < 2 * ε := by
      simpa only [norm_centeredLift] using lt_of_not_ge hfar
    apply mem_closedBall_zero_iff.mpr
    have ht : ‖y‖ ≤ ‖y - centeredLift z‖ + ‖centeredLift z‖ := by
      simpa only [sub_add_cancel] using norm_add_le (y - centeredLift z) (centeredLift z)
    linarith

end PeriodicAttractiveLogGas
