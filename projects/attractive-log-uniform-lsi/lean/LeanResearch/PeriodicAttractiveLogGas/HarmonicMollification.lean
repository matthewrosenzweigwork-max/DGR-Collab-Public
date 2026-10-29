/-
The weak-harmonic mollification argument is adapted from Scott Armstrong and
Vlad Vicol, CKN/Foundation/Harmonic/InteriorWeak.lean, immutable commit
25bde5b5b47a929a510e7f06699391f484531559 (Apache 2.0).
Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
The exact upstream source and license are retained in research/discovery/.
Here the domain is real Euclidean two-space, the kernel is arbitrary smooth
and compactly supported, and the hypotheses require only local L1.
The derivative interchange uses the pinned Mathlib convolution API directly.
-/
import LeanResearch.PeriodicAttractiveLogGas.LaplacianGeometry
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! Smooth harmonic mollifications of locally integrable weakly harmonic
planar functions. No theorem in this file asserts the existence of a smooth
representative of the original function; identification and gluing remain
separate proof obligations. -/

noncomputable section

open MeasureTheory InnerProductSpace Laplacian Filter Set Metric
open scoped Topology ContDiff Convolution

namespace PeriodicAttractiveLogGas

/-- Real convolution with the canonical volume on `PlanarSpace`. -/
def planarConvolution (f κ : PlanarSpace → ℝ) : PlanarSpace → ℝ :=
  f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ

/-- A fixed-direction derivative, used to sum the two Euclidean second derivatives. -/
def planarDirectionalDeriv (f : PlanarSpace → ℝ) (v : PlanarSpace) :
    PlanarSpace → ℝ := fun x ↦ fderiv ℝ f x v

theorem contDiff_planarDirectionalDeriv {f : PlanarSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (v : PlanarSpace) :
    ContDiff ℝ ∞ (planarDirectionalDeriv f v) := by
  have h := hf.contDiff_fderiv_apply (m := (∞ : ℕ∞ω))
    (n := (∞ : ℕ∞ω)) (by simp)
  have hc : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ (x, v)) := by fun_prop
  simpa only [planarDirectionalDeriv, Function.comp_def] using! h.comp hc

theorem hasCompactSupport_planarDirectionalDeriv {f : PlanarSpace → ℝ}
    (hf : HasCompactSupport f) (v : PlanarSpace) :
    HasCompactSupport (planarDirectionalDeriv f v) :=
  hf.fderiv_apply (𝕜 := ℝ) v

theorem planarDirectionalDeriv_second {f : PlanarSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (v w x : PlanarSpace) :
    planarDirectionalDeriv (planarDirectionalDeriv f w) v x =
      (fderiv ℝ (fderiv ℝ f) x v) w := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) :=
    (contDiff_infty_iff_fderiv.mp hf).2
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hfd.differentiable (by simp)) x
  have h := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (x := x) w)
  simpa [planarDirectionalDeriv, ContinuousLinearMap.comp_apply] using!
    congrArg (fun L : PlanarSpace →L[ℝ] ℝ ↦ L v) h.fderiv

theorem laplacian_eq_sum_planarDirectionalDeriv {f : PlanarSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : PlanarSpace) :
    Δ f x = ∑ i : Fin 2,
      planarDirectionalDeriv (planarDirectionalDeriv f
        (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (EuclideanSpace.basisFun (Fin 2) ℝ i) x := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin 2) ℝ)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact (planarDirectionalDeriv_second hf _ _ x).symm

theorem contDiff_laplacian_planar {f : PlanarSpace → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (Δ f) := by
  have heq : Δ f = fun x ↦ ∑ i : Fin 2,
      planarDirectionalDeriv (planarDirectionalDeriv f
        (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (EuclideanSpace.basisFun (Fin 2) ℝ i) x :=
    funext (laplacian_eq_sum_planarDirectionalDeriv hf)
  rw [heq]
  exact ContDiff.sum fun i _ ↦
    contDiff_planarDirectionalDeriv (contDiff_planarDirectionalDeriv hf _) _

theorem hasCompactSupport_laplacian_planar {f : PlanarSpace → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (Δ f) :=
  hf.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset f)

theorem contDiff_planarConvolution {f κ : PlanarSpace → ℝ}
    (hf : LocallyIntegrable f volume) (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ ∞ κ) : ContDiff ℝ ∞ (planarConvolution f κ) :=
  hκc.contDiff_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ) hf hκ

theorem planarDirectionalDeriv_convolution {f κ : PlanarSpace → ℝ}
    (hf : LocallyIntegrable f volume) (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ ∞ κ) (v : PlanarSpace) :
    planarDirectionalDeriv (planarConvolution f κ) v =
      planarConvolution f (planarDirectionalDeriv κ v) := by
  funext x
  have hd := hκc.hasFDerivAt_convolution_right
    (L := ContinuousLinearMap.lsmul ℝ ℝ) hf (hκ.of_le (by simp)) x
  change (fderiv ℝ (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ) x) v = _
  rw [hd.fderiv]
  exact MeasureTheory.convolution_precompR_apply
    (L := ContinuousLinearMap.lsmul ℝ ℝ) hf (hκc.fderiv (𝕜 := ℝ))
    (hκ.continuous_fderiv (by simp)) x v

/-- The Laplacian passes to the smooth compact kernel of a locally L1 convolution. -/
theorem laplacian_planarConvolution {f κ : PlanarSpace → ℝ}
    (hf : LocallyIntegrable f volume) (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ ∞ κ) :
    Δ (planarConvolution f κ) = planarConvolution f (Δ κ) := by
  let e : Fin 2 → PlanarSpace := EuclideanSpace.basisFun (Fin 2) ℝ
  let q : Fin 2 → PlanarSpace → ℝ := fun i ↦
    planarDirectionalDeriv (planarDirectionalDeriv κ (e i)) (e i)
  have hq (i : Fin 2) : ContDiff ℝ ∞ (q i) :=
    contDiff_planarDirectionalDeriv (contDiff_planarDirectionalDeriv hκ _) _
  have hqc (i : Fin 2) : HasCompactSupport (q i) :=
    hasCompactSupport_planarDirectionalDeriv
      (hasCompactSupport_planarDirectionalDeriv hκc _) _
  have hsecond (i : Fin 2) :
      planarDirectionalDeriv
        (planarDirectionalDeriv (planarConvolution f κ) (e i)) (e i) =
        planarConvolution f (q i) := by
    rw [planarDirectionalDeriv_convolution hf hκc hκ (e i)]
    exact planarDirectionalDeriv_convolution hf
      (hasCompactSupport_planarDirectionalDeriv hκc _)
      (contDiff_planarDirectionalDeriv hκ _) _
  funext x
  have hint (i : Fin 2) : Integrable (fun t ↦ f t * q i (x - t)) volume := by
    simpa only [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      (hqc i).convolutionExists_right (L := ContinuousLinearMap.lsmul ℝ ℝ)
        hf (hq i).continuous x
  calc
    Δ (planarConvolution f κ) x = ∑ i : Fin 2, planarConvolution f (q i) x := by
      rw [laplacian_eq_sum_planarDirectionalDeriv (contDiff_planarConvolution hf hκc hκ)]
      exact Finset.sum_congr rfl fun i _ ↦ congrFun (hsecond i) x
    _ = ∫ t, ∑ i : Fin 2, f t * q i (x - t) := by
      simp only [planarConvolution, MeasureTheory.convolution_def,
        ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      exact (MeasureTheory.integral_finsetSum Finset.univ (fun i _ ↦ hint i)).symm
    _ = planarConvolution f (Δ κ) x := by
      simp only [planarConvolution, MeasureTheory.convolution_def,
        ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      apply integral_congr_ae
      filter_upwards with t
      rw [laplacian_eq_sum_planarDirectionalDeriv hκ]
      simp only [e, q, Finset.mul_sum]

/-- Compact tests make the weak Laplacian pairing genuinely integrable. -/
theorem integrable_planarLaplacian_pairing {U : Set PlanarSpace}
    {u φ : PlanarSpace → ℝ} (hu : LocallyIntegrableOn u U volume)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    Integrable (fun y ↦ u y * Δ φ y) volume := by
  have huK := hu.integrableOn_compact_subset hφU hφc.isCompact
  have hprod : IntegrableOn (fun y ↦ u y * Δ φ y) (tsupport φ) volume :=
    huK.mul_continuousOn (contDiff_laplacian_planar hφ).continuous.continuousOn
      hφc.isCompact
  exact hprod.integrable_of_forall_notMem_eq_zero fun y hy ↦ by
    have hzero : Δ φ y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h ↦ hy (tsupport_laplacian_subset φ h))
    rw [hzero, mul_zero]

/-- Local L1 and zero Laplacian pairing against every smooth compact test in the set. -/
def PlanarWeaklyHarmonicOn (U : Set PlanarSpace) (u : PlanarSpace → ℝ) : Prop :=
  LocallyIntegrableOn u U volume ∧
    ∀ φ : PlanarSpace → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → ∫ y, u y * Δ φ y = 0

/-- At points whose kernel neighborhood stays in the weak equation's domain,
the mollified function has zero ordinary Euclidean Laplacian. -/
theorem laplacian_planarConvolution_eq_zero_of_weak
    {U : Set PlanarSpace} {f κ : PlanarSpace → ℝ}
    (hf : LocallyIntegrable f volume)
    (hweak : ∀ φ : PlanarSpace → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → ∫ y, f y * Δ φ y = 0)
    (hκc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ) {r : ℝ}
    (hκsupport : tsupport κ ⊆ closedBall 0 r) {x : PlanarSpace}
    (hx : closedBall x r ⊆ U) : Δ (planarConvolution f κ) x = 0 := by
  let φ : PlanarSpace → ℝ := fun y ↦ κ (x - y)
  have hφ : ContDiff ℝ ∞ φ := hκ.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport φ := by
    simpa [φ, Function.comp_def] using hκc.comp_homeomorph (Homeomorph.subLeft x)
  have hφsupport : tsupport φ ⊆ U := by
    have hts : tsupport φ = (Homeomorph.subLeft x) ⁻¹' tsupport κ := by
      simpa [φ, Function.comp_def] using
        tsupport_comp_eq_preimage κ (Homeomorph.subLeft x)
    rw [hts]
    intro y hy
    apply hx
    have hk : x - y ∈ closedBall (0 : PlanarSpace) r := hκsupport hy
    rw [mem_closedBall, dist_zero_right] at hk
    rw [mem_closedBall, dist_eq_norm]
    calc
      ‖y - x‖ = ‖-(y - x)‖ := (norm_neg _).symm
      _ = ‖x - y‖ := by congr 1; abel
      _ ≤ r := hk
  rw [laplacian_planarConvolution hf hκc hκ]
  calc
    planarConvolution f (Δ κ) x = ∫ y, f y * Δ φ y := by
      simp only [planarConvolution, MeasureTheory.convolution_def,
        ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      apply integral_congr_ae
      filter_upwards with y
      have hreflection := congrFun (laplacian_comp_const_sub κ x) y
      change Δ φ y = Δ κ (x - y) at hreflection
      rw [hreflection]
    _ = 0 := hweak φ hφ hφc hφsupport

/-- Cut off at radius `4R`; the convolution is globally smooth and harmonic
on the radius-`3R` ball for every kernel supported in the radius-`R` ball. -/
theorem smooth_harmonic_localConvolution
    {U : Set PlanarSpace} {u κ : PlanarSpace → ℝ} {a : PlanarSpace} {R : ℝ}
    (hu : PlanarWeaklyHarmonicOn U u) (_hR : 0 < R)
    (hball : closedBall a (4 * R) ⊆ U)
    (hκ : ContDiff ℝ ∞ κ) (hκsupport : tsupport κ ⊆ closedBall 0 R) :
    let f := (closedBall a (4 * R)).indicator u
    ContDiff ℝ ∞ (planarConvolution f κ) ∧
      HarmonicOnNhd (planarConvolution f κ) (ball a (3 * R)) := by
  classical
  let K : Set PlanarSpace := closedBall a (4 * R)
  let f : PlanarSpace → ℝ := K.indicator u
  have hK : IsCompact K := isCompact_closedBall _ _
  have hfint : Integrable f volume :=
    (integrable_indicator_iff hK.measurableSet).2
      (hu.1.integrableOn_compact_subset hball hK)
  have hf : LocallyIntegrable f volume := hfint.locallyIntegrable
  have hκc : HasCompactSupport κ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 R)
      ((subset_tsupport κ).trans hκsupport)
  have hweak : ∀ φ : PlanarSpace → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ K → ∫ y, f y * Δ φ y = 0 := by
    intro φ hφ hφc hφK
    have heq : (fun y ↦ f y * Δ φ y) = (fun y ↦ u y * Δ φ y) := by
      funext y
      by_cases hy : y ∈ K
      · simp [f, hy]
      · have hzero : Δ φ y = 0 := image_eq_zero_of_notMem_tsupport
          (fun h ↦ hy (hφK (tsupport_laplacian_subset φ h)))
        simp [hzero]
    rw [heq]
    exact hu.2 φ hφ hφc (hφK.trans hball)
  have hmargin (x : PlanarSpace) (hx : x ∈ ball a (3 * R)) :
      closedBall x R ⊆ K := by
    intro y hy
    have hx' : dist x a < 3 * R := hx
    have hy' : dist y x ≤ R := hy
    change dist y a ≤ 4 * R
    calc
      dist y a ≤ dist y x + dist x a := dist_triangle _ _ _
      _ ≤ R + 3 * R := add_le_add hy' hx'.le
      _ = 4 * R := by ring
  have hsmooth : ContDiff ℝ ∞ (planarConvolution f κ) :=
    contDiff_planarConvolution hf hκc hκ
  have hzero : ∀ x ∈ ball a (3 * R), Δ (planarConvolution f κ) x = 0 :=
    fun x hx ↦ laplacian_planarConvolution_eq_zero_of_weak hf hweak hκc hκ
      hκsupport (hmargin x hx)
  refine ⟨hsmooth, ?_⟩
  intro x hx
  refine ⟨(hsmooth.of_le (by simp)).contDiffAt, ?_⟩
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  exact hzero y hy

/-- A standard smooth planar approximate-identity kernel; radiality is not asserted. -/
def planarMollifierBump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : PlanarSpace) :=
  ⟨ε / 2, ε, half_pos hε, by linarith⟩

def planarMollifier (ε : ℝ) (hε : 0 < ε) : PlanarSpace → ℝ :=
  (planarMollifierBump ε hε).normed volume

theorem planarMollifier_nonneg {ε : ℝ} (hε : 0 < ε) (x : PlanarSpace) :
    0 ≤ planarMollifier ε hε x :=
  (planarMollifierBump ε hε).nonneg_normed x

theorem integral_planarMollifier {ε : ℝ} (hε : 0 < ε) :
    ∫ x, planarMollifier ε hε x = 1 :=
  (planarMollifierBump ε hε).integral_normed

theorem contDiff_planarMollifier {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (planarMollifier ε hε) :=
  (planarMollifierBump ε hε).contDiff_normed

theorem tsupport_planarMollifier {ε : ℝ} (hε : 0 < ε) :
    tsupport (planarMollifier ε hε) = closedBall (0 : PlanarSpace) ε :=
  (planarMollifierBump ε hε).tsupport_normed_eq

/-- Every positive mollification scale at most `R` gives a smooth harmonic
function on the radius-`3R` ball after the radius-`4R` localization. -/
theorem smooth_harmonic_localMollification
    {U : Set PlanarSpace} {u : PlanarSpace → ℝ} {a : PlanarSpace} {R ε : ℝ}
    (hu : PlanarWeaklyHarmonicOn U u) (hR : 0 < R)
    (hball : closedBall a (4 * R) ⊆ U) (hε : 0 < ε) (hεR : ε ≤ R) :
    let f := (closedBall a (4 * R)).indicator u
    ContDiff ℝ ∞ (planarConvolution f (planarMollifier ε hε)) ∧
      HarmonicOnNhd (planarConvolution f (planarMollifier ε hε))
        (ball a (3 * R)) := by
  apply smooth_harmonic_localConvolution hu hR hball (contDiff_planarMollifier hε)
  rw [tsupport_planarMollifier hε]
  exact closedBall_subset_closedBall hεR

end PeriodicAttractiveLogGas
