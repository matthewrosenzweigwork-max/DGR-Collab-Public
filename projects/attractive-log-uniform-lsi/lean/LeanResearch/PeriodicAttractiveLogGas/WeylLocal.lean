import LeanResearch.PeriodicAttractiveLogGas.HarmonicMollification
import LeanResearch.PeriodicAttractiveLogGas.RadialHarmonicReproduction
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.SpecificLimits.Basic

/-! Local smooth harmonic representatives of weakly harmonic planar functions.

One fixed radial mollification reproduces every smaller standard mollification
on the inner ball. Convolution association and the two approximate-identity
limits then identify that smooth function with the original function almost
everywhere. All measures below are the canonical volume on `PlanarSpace`.
No global gluing statement is asserted. -/

noncomputable section

open MeasureTheory InnerProductSpace Filter Set Metric
open scoped Topology ContDiff Convolution

namespace PeriodicAttractiveLogGas

/-- Scalar convolution is commutative, with the same canonical volume. -/
theorem planarConvolution_comm (f g : PlanarSpace → ℝ) :
    planarConvolution f g = planarConvolution g f := by
  have hL : (ContinuousLinearMap.lsmul ℝ ℝ).flip =
      ContinuousLinearMap.lsmul ℝ ℝ := by
    ext
    rfl
  exact MeasureTheory.convolution_symm (ContinuousLinearMap.lsmul ℝ ℝ) hL

/-- Pointwise association when the last two factors are continuous and compactly
supported. The first factor need only be locally integrable. -/
theorem planarConvolution_assoc_compact {f g k : PlanarSpace → ℝ}
    (hf : LocallyIntegrable f volume)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hk : Continuous k) (hkc : HasCompactSupport k) :
    planarConvolution (planarConvolution f g) k =
      planarConvolution f (planarConvolution g k) := by
  let ng : PlanarSpace → ℝ := fun x ↦ ‖g x‖
  let nk : PlanarSpace → ℝ := fun x ↦ ‖k x‖
  have hng : Continuous ng := hg.norm
  have hnk : Continuous nk := hk.norm
  have hngc : HasCompactSupport ng := hgc.norm
  have hnkc : HasCompactSupport nk := hkc.norm
  have hngk : Continuous
      (ng ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] nk) :=
    hnkc.continuous_convolution_right (L := ContinuousLinearMap.mul ℝ ℝ)
      hng.locallyIntegrable hnk
  have hngkc : HasCompactSupport
      (ng ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] nk) :=
    hngc.convolution (L := ContinuousLinearMap.mul ℝ ℝ) hnkc
  have hfnorm : LocallyIntegrable (fun y ↦ ‖f y‖) volume :=
    locallyIntegrableOn_univ.mp (hf.locallyIntegrableOn univ).norm
  funext x
  have hfg : ∀ᵐ y ∂volume, ConvolutionExistsAt f g y
      (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    Eventually.of_forall (hgc.convolutionExists_right
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hf hg)
  have hnormgk : ∀ᵐ y ∂volume, ConvolutionExistsAt ng nk y
      (ContinuousLinearMap.mul ℝ ℝ) volume :=
    Eventually.of_forall (hnkc.convolutionExists_right
      (L := ContinuousLinearMap.mul ℝ ℝ) hng.locallyIntegrable hnk)
  have hnormfgk : ConvolutionExistsAt (fun y ↦ ‖f y‖)
      (ng ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] nk) x
      (ContinuousLinearMap.mul ℝ ℝ) volume :=
    hngkc.convolutionExists_right (L := ContinuousLinearMap.mul ℝ ℝ) hfnorm hngk x
  exact MeasureTheory.convolution_assoc
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (L₂ := ContinuousLinearMap.lsmul ℝ ℝ)
    (L₃ := ContinuousLinearMap.lsmul ℝ ℝ)
    (L₄ := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := (volume : Measure PlanarSpace)) (ν := (volume : Measure PlanarSpace))
    (by intro r s t; simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_assoc])
    hf.aestronglyMeasurable hg.aestronglyMeasurable hk.aestronglyMeasurable
    hfg hnormgk hnormfgk

/-- The two continuous compact kernels can be moved around a locally L1 factor
without losing pointwise equality. -/
theorem planarConvolution_compact_exchange {f g k : PlanarSpace → ℝ}
    (hf : LocallyIntegrable f volume)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hk : Continuous k) (hkc : HasCompactSupport k) :
    planarConvolution (planarConvolution f g) k =
      planarConvolution g (planarConvolution f k) := by
  calc
    planarConvolution (planarConvolution f g) k =
        planarConvolution f (planarConvolution g k) :=
      planarConvolution_assoc_compact hf hg hgc hk hkc
    _ = planarConvolution f (planarConvolution k g) := by
      rw [planarConvolution_comm g k]
    _ = planarConvolution (planarConvolution f k) g :=
      (planarConvolution_assoc_compact hf hk hkc hg hgc).symm
    _ = planarConvolution g (planarConvolution f k) :=
      planarConvolution_comm _ _

/-- The fixed radial mollification is an actual almost-everywhere representative
of a locally L1 weakly harmonic function on the inner ball. -/
theorem ae_eq_radialMollification_on_ball
    {U : Set PlanarSpace} {u : PlanarSpace → ℝ} {a : PlanarSpace} {R : ℝ}
    (hu : PlanarWeaklyHarmonicOn U u) (hR : 0 < R)
    (hball : closedBall a (4 * R) ⊆ U) :
    u =ᵐ[volume.restrict (ball a R)]
      planarConvolution ((closedBall a (4 * R)).indicator u) (radialMollifier R hR) := by
  classical
  let f : PlanarSpace → ℝ := (closedBall a (4 * R)).indicator u
  let ψ : PlanarSpace → ℝ := radialMollifier R hR
  let h : PlanarSpace → ℝ := planarConvolution f ψ
  have hfint : Integrable f volume :=
    (integrable_indicator_iff measurableSet_closedBall).2
      (hu.1.integrableOn_compact_subset hball (isCompact_closedBall _ _))
  have hf : LocallyIntegrable f volume := hfint.locallyIntegrable
  have hψ : ContDiff ℝ ∞ ψ := contDiff_radialMollifier R hR
  have hψc : HasCompactSupport ψ := hasCompactSupport_radialMollifier R hR
  have hsmooth : ContDiff ℝ ∞ h := contDiff_planarConvolution hf hψc hψ
  let ε : ℕ → ℝ := fun n ↦ R / ((n : ℝ) + 1)
  have hεpos (n : ℕ) : 0 < ε n := div_pos hR (by positivity)
  have hεR (n : ℕ) : ε n ≤ R := by
    dsimp [ε]
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn hR.le
  have hεzero : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, mul_one_div, mul_zero] using
      (tendsto_const_nhds (x := R)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let β : ℕ → ContDiffBump (0 : PlanarSpace) :=
    fun n ↦ planarMollifierBump (ε n) (hεpos n)
  let κ : ℕ → PlanarSpace → ℝ := fun n ↦ planarMollifier (ε n) (hεpos n)
  let v : ℕ → PlanarSpace → ℝ := fun n ↦ planarConvolution f (κ n)
  have hβzero : Tendsto (fun n ↦ (β n).rOut) atTop (𝓝 0) := hεzero
  have hβratio : ∀ᶠ n in atTop, (β n).rOut ≤ (2 : ℝ) * (β n).rIn := by
    filter_upwards with n
    change ε n ≤ 2 * (ε n / 2)
    linarith
  have hκsmooth (n : ℕ) : ContDiff ℝ ∞ (κ n) := contDiff_planarMollifier (hεpos n)
  have hκc (n : ℕ) : HasCompactSupport (κ n) :=
    (β n).hasCompactSupport_normed
  have hv (n : ℕ) : ContDiff ℝ ∞ (v n) ∧
      HarmonicOnNhd (v n) (ball a (3 * R)) :=
    smooth_harmonic_localMollification hu hR hball (hεpos n) (hεR n)
  have hmargin {x : PlanarSpace} (hx : x ∈ ball a R) :
      closedBall x R ⊆ ball a (3 * R) := by
    intro y hy
    have hx' : dist x a < R := hx
    have hy' : dist y x ≤ R := hy
    change dist y a < 3 * R
    calc
      dist y a ≤ dist y x + dist x a := dist_triangle _ _ _
      _ < R + R := add_lt_add_of_le_of_lt hy' hx'
      _ < 3 * R := by linarith
  have hidentify (n : ℕ) {x : PlanarSpace} (hx : x ∈ ball a R) :
      v n x = planarConvolution (κ n) h x := by
    have hlocal : HarmonicOnNhd (v n) (closedBall x R) :=
      fun y hy ↦ (hv n).2 y (hmargin hx hy)
    have hreproduce : planarConvolution (v n) ψ x = v n x := by
      simpa only [ψ, planarConvolution] using
        convolution_radialMollifier_eq R hR (hv n).1.continuous hlocal
    calc
      v n x = planarConvolution (v n) ψ x := hreproduce.symm
      _ = planarConvolution (κ n) h x :=
        congrFun (planarConvolution_compact_exchange hf
          (hκsmooth n).continuous (hκc n) hψ.continuous hψc) x
  have hflimit : ∀ᵐ x ∂volume,
      Tendsto (fun n ↦ v n x) atTop (𝓝 (f x)) := by
    have hraw := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (φ := β) (μ := (volume : Measure PlanarSpace)) hβzero hβratio hf
    filter_upwards [hraw] with x hx
    change Tendsto (fun n ↦ planarConvolution (κ n) f x) atTop (𝓝 (f x)) at hx
    have heq : (fun n ↦ v n x) = fun n ↦ planarConvolution (κ n) f x := by
      funext n
      exact congrFun (planarConvolution_comm f (κ n)) x
    rw [heq]
    exact hx
  have hhlimit (x : PlanarSpace) :
      Tendsto (fun n ↦ planarConvolution (κ n) h x) atTop (𝓝 (h x)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous
      (φ := β) (μ := (volume : Measure PlanarSpace)) hβzero hsmooth.continuous x
  have hfeq : f =ᵐ[volume.restrict (ball a R)] h := by
    filter_upwards [ae_restrict_of_ae hflimit, ae_restrict_mem measurableSet_ball]
      with x hxlimit hx
    have heq : (fun n ↦ v n x) = fun n ↦ planarConvolution (κ n) h x :=
      funext (fun n ↦ hidentify n hx)
    rw [heq] at hxlimit
    exact tendsto_nhds_unique hxlimit (hhlimit x)
  filter_upwards [hfeq, ae_restrict_mem measurableSet_ball] with x hxeq hx
  have hxK : x ∈ closedBall a (4 * R) := by
    have hx' : dist x a < R := hx
    change dist x a ≤ 4 * R
    linarith
  have hfx : f x = u x := by simp only [f, indicator_of_mem hxK]
  exact hfx.symm.trans hxeq

/-- One-ball Weyl regularity: a globally smooth function is harmonic and agrees
almost everywhere with the original weakly harmonic function on the inner ball. -/
theorem exists_smooth_harmonic_representative_ball
    {U : Set PlanarSpace} {u : PlanarSpace → ℝ} {a : PlanarSpace} {R : ℝ}
    (hu : PlanarWeaklyHarmonicOn U u) (hR : 0 < R)
    (hball : closedBall a (4 * R) ⊆ U) :
    ∃ h : PlanarSpace → ℝ, ContDiff ℝ ∞ h ∧
      HarmonicOnNhd h (ball a R) ∧ u =ᵐ[volume.restrict (ball a R)] h := by
  let h : PlanarSpace → ℝ :=
    planarConvolution ((closedBall a (4 * R)).indicator u) (radialMollifier R hR)
  have hs := smooth_harmonic_localConvolution hu hR hball
    (contDiff_radialMollifier R hR) (tsupport_radialMollifier_subset R hR)
  refine ⟨h, hs.1, ?_, ae_eq_radialMollification_on_ball hu hR hball⟩
  intro x hx
  apply hs.2 x
  have hx' : dist x a < R := hx
  change dist x a < 3 * R
  linarith

end PeriodicAttractiveLogGas
