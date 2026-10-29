import LeanResearch.PeriodicAttractiveLogGas.GreenGradientMoments
import LeanResearch.PeriodicAttractiveLogGas.GreenGradientOscillation
import LeanResearch.PeriodicAttractiveLogGas.MovingPoleCalculus
import LeanResearch.PeriodicAttractiveLogGas.DeletedConditionalPoincare

/-! Source Proposition 3.11, the covariance estimate at lines 884--909.
The covariance is the actual physical vector covariance. Centering, Holder
integrability, and the one-site ordinary-gradient energy are proved before
the near and far bounds. This file is a SOURCE_ONLY candidate pending the
root's serialized Lean checking and independent semantic review.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

namespace PeriodicAttractiveLogGas.GreenCovarianceBounds

open MeshCells MeshAdjacentCells GreenPointWeights LabelOccupations
  OneCoordinateConditionals ConditionalLawEstimates GreenGradientOscillation MovingPoleCalculus
open GreenConditionalInfluence hiding patchDomain

/-- Chosen once from the actual Green Hessian theorem, before all gas,
mesh, source-placement and observable parameters. -/
def hessianConstant : ℝ := Classical.choose exists_kernelHessianBound

theorem hessianConstant_pos : 0 < hessianConstant :=
  (Classical.choose_spec exists_kernelHessianBound).1

theorem kernel_hessian_bound : KernelHessianBound hessianConstant :=
  (Classical.choose_spec exists_kernelHessianBound).2

def nearCoefficient (β₀ : ℝ) : ℝ :=
  fourthMomentBound β₀ ^ 2 * densityNormBound β₀ ^ (3 / 2 : ℝ) *
    kernelConstant ^ 2 * (1 + 9 * Real.pi) ^ (9 / 8 : ℝ)

def farCoefficient (β₀ C₂ : ℝ) (R : ℕ) : ℝ :=
  5 * fourthMomentBound β₀ ^ 2 * C₂ ^ 2 / (R : ℝ) ^ 4

theorem fourthMomentBound_nonneg (β₀ : ℝ) : 0 ≤ fourthMomentBound β₀ := by
  have hK := (densityNormBound_pos β₀).le
  have hc := (lowerBound_pos β₀).le
  have hS := rectangleSobolevConstant_nonneg (16 / 3)
  unfold fourthMomentBound OneSiteConstants.fourthMoment
  positivity

theorem nearCoefficient_nonneg (β₀ : ℝ) : 0 ≤ nearCoefficient β₀ := by
  have hK := (densityNormBound_pos β₀).le
  unfold nearCoefficient
  positivity

theorem farCoefficient_nonneg (β₀ C₂ : ℝ) (R : ℕ) :
    0 ≤ farCoefficient β₀ C₂ R := by
  unfold farCoefficient
  positivity

section VectorHolder

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
variable {ν : Measure Torus} [IsProbabilityMeasure ν]
variable {f : Torus → ℝ} {G : Torus → V}

omit [CompleteSpace V] in
/-- These integrability statements include the original product in the
definition of vector covariance and every constant-shifted centered product. -/
theorem covariance_integrability (hf : MemLp f 4 ν)
    (hG : MemLp G conjugateExponent ν) (v : V) :
    Integrable f ν ∧ Integrable G ν ∧ Integrable (fun z ↦ f z • G z) ν ∧
      Integrable (fun z ↦ (f z - ∫ w, f w ∂ν) • (G z - v)) ν := by
  have hfc : MemLp (fun z ↦ f z - ∫ w, f w ∂ν) 4 ν :=
    hf.sub (memLp_const _)
  have hGc : MemLp (fun z ↦ G z - v) conjugateExponent ν :=
    hG.sub (memLp_const v)
  exact ⟨hf.integrable (by norm_num), hG.integrable (by norm_num [conjugateExponent]),
    memLp_one_iff_integrable.mp (hf.smul hG),
    memLp_one_iff_integrable.mp (hfc.smul hGc)⟩

/-- The centered identity is proved from probability normalization and
integrable products; it is not imposed as an extra covariance premise. -/
theorem vectorCovariance_eq_centered (hf : MemLp f 4 ν)
    (hG : MemLp G conjugateExponent ν) (v : V) :
    vectorCovariance ν f G =
      ∫ z, (f z - ∫ w, f w ∂ν) • (G z - v) ∂ν := by
  have hfi := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  have hGi := hG.integrable (by norm_num [conjugateExponent] : 1 ≤ conjugateExponent)
  have hfc : MemLp (fun z ↦ f z - ∫ w, f w ∂ν) 4 ν :=
    hf.sub (memLp_const _)
  have hfci := hfc.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  have hfG : Integrable (fun z ↦ f z • G z) ν :=
    memLp_one_iff_integrable.mp (hf.smul hG)
  have hfcG : Integrable (fun z ↦ (f z - ∫ w, f w ∂ν) • G z) ν :=
    memLp_one_iff_integrable.mp (hfc.smul hG)
  have hcG : Integrable (fun z ↦ (∫ w, f w ∂ν) • G z) ν := hGi.smul _
  have hzero : (∫ z, f z - ∫ w, f w ∂ν ∂ν) = 0 := by
    rw [integral_sub hfi (integrable_const _), integral_const,
      probReal_univ, one_smul, sub_self]
  calc
    vectorCovariance ν f G = ∫ z, (f z - ∫ w, f w ∂ν) • G z ∂ν := by
      simp_rw [sub_smul]
      rw [integral_sub hfG hcG, integral_smul]
      rfl
    _ = ∫ z, (f z - ∫ w, f w ∂ν) • (G z - v) ∂ν := by
      symm
      simp_rw [smul_sub]
      rw [integral_sub hfcG (hfci.smul_const v), integral_smul_const,
        hzero, zero_smul, sub_zero]

/-- Vector Holder follows by taking the norm of the actual Bochner integral
and applying the checked real L4--L4/3 product inequality. -/
theorem norm_vectorCovariance_le (hf : MemLp f 4 ν)
    (hG : MemLp G conjugateExponent ν) (v : V) :
    ‖vectorCovariance ν f G‖ ≤
      lpNorm (fun z ↦ f z - ∫ w, f w ∂ν) 4 ν *
        lpNorm (fun z ↦ G z - v) conjugateExponent ν := by
  have hfc : MemLp (fun z ↦ f z - ∫ w, f w ∂ν) 4 ν :=
    hf.sub (memLp_const _)
  have hGc : MemLp (fun z ↦ G z - v) conjugateExponent ν :=
    hG.sub (memLp_const v)
  rw [vectorCovariance_eq_centered hf hG v]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hh := integral_norm_mul_le hfc hGc.norm
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    lpNorm_norm hGc.aestronglyMeasurable] using hh

theorem covariance_oneSite_holder {β₀ : ℝ} {J : ℕ} {b : Patch}
    (h : FunctionEstimates β₀ J b ν f) (hG : MemLp G conjugateExponent ν) (v : V) :
    ‖vectorCovariance ν f G‖ ≤
      (fourthMomentBound β₀ / (J : ℝ)) * lpNorm (torusOrdinaryGradient f) 2 ν *
        lpNorm (fun z ↦ G z - v) conjugateExponent ν :=
  (norm_vectorCovariance_le (h.function_memLp 4) hG v).trans
    (mul_le_mul_of_nonneg_right h.uniform_fourth lpNorm_nonneg)

omit [NormedSpace ℝ V] [CompleteSpace V] in
/-- A pointwise vector oscillation bound gives the required conjugate
moment without any density comparison and without a factor of two. -/
theorem vector_conjugate_norm_le_of_bound {H : Torus → V} {D : ℝ}
    (hH : AEStronglyMeasurable H ν) (hD : 0 ≤ D)
    (hb : ∀ᵐ z ∂ν, ‖H z‖ ≤ D) :
    MemLp H conjugateExponent ν ∧ lpNorm H conjugateExponent ν ≤ D := by
  have hm : MemLp H conjugateExponent ν := MemLp.of_bound hH D hb
  have hn := lpNorm_le_of_bound hH.norm hD
    (by simpa only [abs_of_nonneg (norm_nonneg _)] using hb)
  exact ⟨hm, by simpa only [lpNorm_norm hH] using hn.2⟩

end VectorHolder

section OneSite

variable {ν : Measure Torus} [IsProbabilityMeasure ν]
variable {β₀ : ℝ} {J : ℕ} {b : Patch} {f : Torus → ℝ} {y : Torus}

/-- The two occurrences of J cancel before squaring. The fractional
powers are combined exactly, giving the source's 9/8 exponent. -/
theorem near_covariance_squared (hJ : 0 < J)
    (hf : FunctionEstimates β₀ J b ν f)
    (hG : GreenGradientMoments.Estimates ν y kernelConstant (densityNormBound β₀) J) :
    ‖vectorCovariance ν f (fun z ↦ greenGradient (z - y))‖ ^ 2 ≤
      nearCoefficient β₀ * ∫ z, ‖torusOrdinaryGradient f z‖ ^ 2 ∂ν := by
  have hj : (0 : ℝ) < J := by exact_mod_cast hJ
  have hS := fourthMomentBound_nonneg β₀
  have hK := (densityNormBound_pos β₀).le
  have hB : 0 ≤ 1 + 9 * Real.pi := by positivity
  have hh := covariance_oneSite_holder hf hG.conjugate_memLp (0 : PlanarSpace)
  simp only [sub_zero] at hh
  have hmul := mul_le_mul_of_nonneg_left hG.conjugate_norm_le
    (mul_nonneg (div_nonneg hS hj.le) (lpNorm_nonneg (f := torusOrdinaryGradient f) (μ := ν) (p := 2)))
  have hbound : ‖vectorCovariance ν f (fun z ↦ greenGradient (z - y))‖ ≤
      (fourthMomentBound β₀ * densityNormBound β₀ ^ (3 / 4 : ℝ) * kernelConstant *
        (1 + 9 * Real.pi) ^ (9 / 16 : ℝ)) * lpNorm (torusOrdinaryGradient f) 2 ν := by
    calc
      _ ≤ _ := hh.trans hmul
      _ = _ := by field_simp [hj.ne']
  have hKpow : (densityNormBound β₀ ^ (3 / 4 : ℝ)) ^ 2 =
      densityNormBound β₀ ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_mul_natCast hK]
    norm_num
  have hBpow : ((1 + 9 * Real.pi) ^ (9 / 16 : ℝ)) ^ 2 =
      (1 + 9 * Real.pi) ^ (9 / 8 : ℝ) := by
    rw [← Real.rpow_mul_natCast hB]
    norm_num
  calc
    _ ≤ ((fourthMomentBound β₀ * densityNormBound β₀ ^ (3 / 4 : ℝ) * kernelConstant *
        (1 + 9 * Real.pi) ^ (9 / 16 : ℝ)) * lpNorm (torusOrdinaryGradient f) 2 ν) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = _ := by
      simp only [mul_pow, hKpow, hBpow,
        DensityMoments.lpNorm_two_sq (hf.gradient_memLp 2), nearCoefficient]

/-- The far estimate uses an actual fixed point of the closed target patch.
No density transfer is used, so neither K-star nor a near-field moment occurs. -/
theorem far_covariance_squared {R : ℕ} (hJ : 0 < J) (hR : 1 ≤ R)
    {C₂ : ℝ} (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (a c : MeshIndex J) (d : Patch) (hfar : ¬ NearPair J hJ R a c b d)
    (hy : y ∈ closure (patchDomain J hJ c d))
    (hν : ∀ᵐ z ∂ν, z ∈ closure (patchDomain J hJ a b))
    (hf : FunctionEstimates β₀ J b ν f) :
    ‖vectorCovariance ν f (fun z ↦ greenGradient (z - y))‖ ^ 2 ≤
      farCoefficient β₀ C₂ R * ∫ z, ‖torusOrdinaryGradient f z‖ ^ 2 ∂ν := by
  obtain ⟨z₀, hz₀⟩ := hν.exists
  let v : PlanarSpace := greenGradient (z₀ - y)
  let D : ℝ := Real.sqrt 5 * C₂ * J / (R : ℝ) ^ 2
  have hj : (0 : ℝ) < J := by exact_mod_cast hJ
  have hr : (0 : ℝ) < R := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hm : Measurable (fun z ↦ greenGradient (z - y) - v) :=
    (GreenGradientMoments.measurable_shiftedGradient y).sub measurable_const
  have hy' : y ∈ closure (GreenConditionalInfluence.patchDomain J hJ c d) := by
    simpa only [patchDomain_eq_existing] using hy
  have hν' : ∀ᵐ z ∂ν, z ∈ closure (GreenConditionalInfluence.patchDomain J hJ a b) := by
    simpa only [patchDomain_eq_existing] using hν
  have hosc : ∀ᵐ z ∂ν, ‖greenGradient (z - y) - v‖ ≤ D :=
    hν'.mono fun z hz ↦ far_patch_gradient_oscillation hJ hR hC hk a c b d hfar hy' hz
      (by simpa only [patchDomain_eq_existing] using hz₀)
  have hshift := vector_conjugate_norm_le_of_bound hm.aestronglyMeasurable hD hosc
  have hG : MemLp (fun z ↦ greenGradient (z - y)) conjugateExponent ν := by
    have hh : MemLp (fun z ↦ (greenGradient (z - y) - v) + v) conjugateExponent ν :=
      hshift.1.add (memLp_const v)
    simpa only [sub_add_cancel] using hh
  have hh := covariance_oneSite_holder hf hG v
  have hmul := mul_le_mul_of_nonneg_left hshift.2
    (mul_nonneg (div_nonneg (fourthMomentBound_nonneg β₀) hj.le)
      (lpNorm_nonneg (f := torusOrdinaryGradient f) (μ := ν) (p := 2)))
  have hbound : ‖vectorCovariance ν f (fun z ↦ greenGradient (z - y))‖ ≤
      (Real.sqrt 5 * fourthMomentBound β₀ * C₂ / (R : ℝ) ^ 2) *
        lpNorm (torusOrdinaryGradient f) 2 ν := by
    calc
      _ ≤ _ := hh.trans hmul
      _ = _ := by dsimp [D]; field_simp [hj.ne', hr.ne']
  calc
    _ ≤ ((Real.sqrt 5 * fourthMomentBound β₀ * C₂ / (R : ℝ) ^ 2) *
        lpNorm (torusOrdinaryGradient f) 2 ν) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = _ := by
      rw [mul_pow, DensityMoments.lpNorm_two_sq (hf.gradient_memLp 2)]
      congr 1
      simp only [farCoefficient, div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
      ring

end OneSite

/-- Conclusions for the actual covariance, including all Bochner gates.
The moment and Sobolev hypotheses used in its construction are not fields
of this output record and must be discharged by the actual law theorem. -/
structure Estimates (β₀ : ℝ) (J : ℕ) (ν : Measure Torus)
    (f : Torus → ℝ) (y : Torus) : Prop where
  function_integrable : Integrable f ν
  energy_integrable : Integrable (fun z ↦ ‖torusOrdinaryGradient f z‖ ^ 2) ν
  green_integrable : Integrable (fun z ↦ greenGradient (z - y)) ν
  product_integrable : Integrable (fun z ↦ f z • greenGradient (z - y)) ν
  shifted_integrable : ∀ v : PlanarSpace,
    Integrable (fun z ↦ (f z - ∫ w, f w ∂ν) • (greenGradient (z - y) - v)) ν
  centered_identity : ∀ v : PlanarSpace,
    vectorCovariance ν f (fun z ↦ greenGradient (z - y)) =
      ∫ z, (f z - ∫ w, f w ∂ν) • (greenGradient (z - y) - v) ∂ν
  holder : ∀ v : PlanarSpace,
    ‖vectorCovariance ν f (fun z ↦ greenGradient (z - y))‖ ≤
      (fourthMomentBound β₀ / (J : ℝ)) * lpNorm (torusOrdinaryGradient f) 2 ν *
        lpNorm (fun z ↦ greenGradient (z - y) - v) conjugateExponent ν
  near_squared : ‖vectorCovariance ν f (fun z ↦ greenGradient (z - y))‖ ^ 2 ≤
    nearCoefficient β₀ * ∫ z, ‖torusOrdinaryGradient f z‖ ^ 2 ∂ν

theorem conditional_covariance_estimates {n J : ℕ} (hJ : 0 < J) {β₀ β : ℝ}
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (i : Fin (n + 1)) (Y : Configuration n) (a : MeshIndex J) (b : Patch)
    (hb : LawBounds hJ β₀ β i Y a b) {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (patchDomain J hJ a b))) (y : Torus) :
    Estimates β₀ J (conditionalKernel (patchMeasure J hJ a b) i β Y) f y := by
  let ν := conditionalKernel (patchMeasure J hJ a b) i β Y
  let : IsProbabilityMeasure ν := hb.probability
  have hF := hb.estimates hf
  have hG := GreenGradientMoments.conditional_gradient_moments hJ hmesh i Y a b hb y
  have hi := covariance_integrability (hF.function_memLp 4) hG.conjugate_memLp (0 : PlanarSpace)
  exact ⟨hi.1, hF.integrable_energy, hi.2.1, hi.2.2.1,
    fun v ↦ (covariance_integrability (hF.function_memLp 4) hG.conjugate_memLp v).2.2.2,
    fun v ↦ vectorCovariance_eq_centered (hF.function_memLp 4) hG.conjugate_memLp v,
    fun v ↦ covariance_oneSite_holder hF hG.conjugate_memLp v,
    near_covariance_squared hJ hF hG⟩

/-- Generic explicit-C2 far endpoint for an actual conditional kernel.
Its only remaining geometric gate is the literal source near-pair complement. -/
theorem conditional_covariance_far_squared {n J R : ℕ} (hJ : 0 < J) (hR : 1 ≤ R)
    {β₀ β C₂ : ℝ} (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (i : Fin (n + 1)) (Y : Configuration n) (a c : MeshIndex J) (b d : Patch)
    (hb : LawBounds hJ β₀ β i Y a b) {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (patchDomain J hJ a b)))
    (hfar : ¬ NearPair J hJ R a c b d) {y : Torus}
    (hy : y ∈ closure (patchDomain J hJ c d)) :
    ‖vectorCovariance (conditionalKernel (patchMeasure J hJ a b) i β Y) f
      (fun z ↦ greenGradient (z - y))‖ ^ 2 ≤
      farCoefficient β₀ C₂ R *
        ∫ z, ‖torusOrdinaryGradient f z‖ ^ 2 ∂conditionalKernel (patchMeasure J hJ a b) i β Y := by
  let : IsProbabilityMeasure (conditionalKernel (patchMeasure J hJ a b) i β Y) := hb.probability
  exact far_covariance_squared hJ hR hC hk a c d hfar hy
    (by simpa only [patchDomain_eq_existing] using conditionalKernel_ae_closure hJ i Y a b hb)
    (hb.estimates hf)

/-- A completed cap supplies all analytic and normalization gates. The
target may be either orientation of an edge patch or a single cell. -/
theorem capped_covariance_estimates {n J : ℕ} (hJ : 0 < J) {β₀ β δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PrescribedOutside hJ η i Y)
    (a : MeshIndex J) (b : Patch) {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (patchDomain J hJ a b))) (y : Torus) :
    Estimates β₀ J (conditionalKernel (patchMeasure J hJ a b) i β Y) f y :=
  conditional_covariance_estimates hJ hmesh i Y a b
    (capped_patch_law hJ hβ hβ₀ hδ hmesh η hη i Y hY a b) hf y

theorem capped_covariance_far_squared {n J : ℕ} (hJ : 0 < J) {β₀ β δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PrescribedOutside hJ η i Y)
    (a : MeshIndex J) (b : Patch) {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (patchDomain J hJ a b))) (j : Fin n)
    (hfar : ¬ NearPair J hJ (radius β₀) a (η (i.succAbove j)) b .cell) :
    ‖vectorCovariance (conditionalKernel (patchMeasure J hJ a b) i β Y) f
      (fun z ↦ greenGradient (z - Y j))‖ ^ 2 ≤
      farCoefficient β₀ hessianConstant (radius β₀) *
        ∫ z, ‖torusOrdinaryGradient f z‖ ^ 2 ∂conditionalKernel (patchMeasure J hJ a b) i β Y :=
  conditional_covariance_far_squared hJ (radius_one_le β₀)
    hessianConstant_pos.le kernel_hessian_bound i Y a (η (i.succAbove j)) b .cell
    (capped_patch_law hJ hβ hβ₀ hδ hmesh η hη i Y hY a b) hf hfar (hY j)

/-- Literal specified-label endpoint, retaining the source global gates. -/
theorem label_covariance_estimates {n J : ℕ} {β₀ β δ : ℝ}
    (_hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (_hsub : β₀ < 4)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PrescribedOutside (mesh_pos hmesh) η i Y)
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (meshCell J (mesh_pos hmesh) (η i))))
    (y : Torus) :
    Estimates β₀ J (conditionalKernel (meshCellMeasure J (mesh_pos hmesh) (η i)) i β Y) f y :=
  capped_covariance_estimates (mesh_pos hmesh) hβ hβ₀ hδ hmesh η hη i Y hY (η i) .cell hf y

/-- Both endpoint caps are used by the actual adjacent-law theorem.
The conditioned coordinate i is independent of the exceptional coordinate t. -/
theorem adjacent_covariance_estimates {n J : ℕ} {β₀ β δ : ℝ}
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (t i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η t a d)
    (Y : Configuration n)
    (hY : PatchOutside (mesh_pos hmesh) (Function.update η t a) (adjacentShapes t d) i Y)
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (patchDomain J (mesh_pos hmesh)
      (Function.update η t a i) (adjacentShapes t d i)))) (y : Torus) :
    Estimates β₀ J (conditionalKernel (patchMeasure J (mesh_pos hmesh)
      (Function.update η t a i) (adjacentShapes t d i)) i β Y) f y :=
  conditional_covariance_estimates (mesh_pos hmesh) hmesh i Y
    (Function.update η t a i) (adjacentShapes t d i)
    ((adjacent_conditionals hN hβ hβ₀ hsub hδ hmesh η t i a d hadm).1 Y hY) hf y

theorem adjacent_covariance_far_squared {n J : ℕ} {β₀ β δ : ℝ}
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (t i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η t a d)
    (Y : Configuration n)
    (hY : PatchOutside (mesh_pos hmesh) (Function.update η t a) (adjacentShapes t d) i Y)
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (patchDomain J (mesh_pos hmesh)
      (Function.update η t a i) (adjacentShapes t d i)))) (j : Fin n)
    (hfar : ¬ NearPair J (mesh_pos hmesh) (radius β₀)
      (Function.update η t a i) (Function.update η t a (i.succAbove j))
      (adjacentShapes t d i) (adjacentShapes t d (i.succAbove j))) :
    let ν := conditionalKernel (patchMeasure J (mesh_pos hmesh)
      (Function.update η t a i) (adjacentShapes t d i)) i β Y
    ‖vectorCovariance ν f (fun z ↦ greenGradient (z - Y j))‖ ^ 2 ≤
      farCoefficient β₀ hessianConstant (radius β₀) *
        ∫ z, ‖torusOrdinaryGradient f z‖ ^ 2 ∂ν :=
  conditional_covariance_far_squared (mesh_pos hmesh) (radius_one_le β₀)
    hessianConstant_pos.le kernel_hessian_bound i Y
    (Function.update η t a i) (Function.update η t a (i.succAbove j))
    (adjacentShapes t d i) (adjacentShapes t d (i.succAbove j))
    ((adjacent_conditionals hN hβ hβ₀ hsub hδ hmesh η t i a d hadm).1 Y hY) hf hfar (hY j)

/-- This is a fixed-outside probe. It asserts no integrated marginal
identity and requires every allowed endpoint completion to be capped. -/
theorem probe_covariance_estimates {n J : ℕ} {β₀ β δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (b : Patch)
    (hadm : ProbeAdmissible δ η i (allowedPatchLabels (mesh_pos hmesh) a b))
    (Y : Configuration n) (hY : PrescribedOutside (mesh_pos hmesh) η i Y)
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (patchDomain J (mesh_pos hmesh) a b))) (y : Torus) :
    Estimates β₀ J (conditionalKernel (patchMeasure J (mesh_pos hmesh) a b) i β Y) f y :=
  conditional_covariance_estimates (mesh_pos hmesh) hmesh i Y a b
    (probe_law hβ hβ₀ hδ hmesh η i a b hadm Y hY) hf y

theorem probe_covariance_far_squared {n J : ℕ} {β₀ β δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (b : Patch)
    (hadm : ProbeAdmissible δ η i (allowedPatchLabels (mesh_pos hmesh) a b))
    (Y : Configuration n) (hY : PrescribedOutside (mesh_pos hmesh) η i Y)
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (patchDomain J (mesh_pos hmesh) a b)))
    (j : Fin n) (hfar : ¬ NearPair J (mesh_pos hmesh) (radius β₀)
      a (η (i.succAbove j)) b .cell) :
    let ν := conditionalKernel (patchMeasure J (mesh_pos hmesh) a b) i β Y
    ‖vectorCovariance ν f (fun z ↦ greenGradient (z - Y j))‖ ^ 2 ≤
      farCoefficient β₀ hessianConstant (radius β₀) *
        ∫ z, ‖torusOrdinaryGradient f z‖ ^ 2 ∂ν :=
  conditional_covariance_far_squared (mesh_pos hmesh) (radius_one_le β₀)
    hessianConstant_pos.le kernel_hessian_bound i Y a (η (i.succAbove j)) b .cell
    (probe_law hβ hβ₀ hδ hmesh η i a b hadm Y hY) hf hfar (hY j)

section ConfigurationSections

theorem insertSite_eq_update {n : ℕ} (i : Fin (n + 1)) (Y : Configuration n) (z : Torus) :
    insertSite i z Y = Function.update (insertSite i 0 Y) i z := by
  funext k
  by_cases hki : k = i
  · subst k
    simp only [insertSite_self, Function.update_self]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hki
    simp only [insertSite_succAbove, Function.update_of_ne (Fin.succAbove_ne i j)]

/-- Exact identification with the physical coordinate gradient, including
the total ordinary-derivative representatives at exceptional points. -/
theorem torusOrdinaryGradient_section {n : ℕ} (f : Configuration (n + 1) → ℝ)
    (i : Fin (n + 1)) (Y : Configuration n) (z : Torus) :
    torusOrdinaryGradient (fun w ↦ f (insertSite i w Y)) z =
      coordinateOrdinaryGradient f i (insertSite i z Y) := by
  have he : (fun w ↦ f (insertSite i w Y)) =
      (fun w ↦ f (Function.update (insertSite i 0 Y) i w)) := by
    funext w
    rw [insertSite_eq_update i Y w]
  rw [he, insertSite_eq_update i Y z, coordinateOrdinaryGradient_update]

theorem physicalLipschitzOn_section {n J : ℕ} (hJ : 0 < J)
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    {f : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hf : ConfigurationPhysicalLipschitzOn L f
      (DeletedConditionalPoincare.closedPatchProduct hJ A B))
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PatchOutside hJ A B i Y) :
    PhysicalLipschitzOn L (fun z ↦ f (insertSite i z Y))
      (closure (patchDomain J hJ (A i) (B i))) := by
  have hX : ∀ k, k ≠ i →
      insertSite i 0 Y k ∈ closure (patchDomain J hJ (A k) (B k)) := by
    intro k hki
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hki
    simpa only [insertSite_succAbove] using hY j
  have hs := hf.section (insertSite i 0 Y) i hX
  have he : (fun z ↦ f (insertSite i z Y)) =
      (fun z ↦ f (Function.update (insertSite i 0 Y) i z)) := by
    funext z
    rw [insertSite_eq_update i Y z]
  rw [he]
  exact hs

/-- Near estimate for an actual configuration section, with the literal
unscaled physical one-site energy as the conclusion. -/
theorem conditional_section_near_squared {n J : ℕ} (hJ : 0 < J) {β₀ β : ℝ}
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PatchOutside hJ A B i Y)
    (hb : LawBounds hJ β₀ β i Y (A i) (B i))
    {f : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hf : ConfigurationPhysicalLipschitzOn L f
      (DeletedConditionalPoincare.closedPatchProduct hJ A B)) (y : Torus) :
    let ν := conditionalKernel (patchMeasure J hJ (A i) (B i)) i β Y
    ‖vectorCovariance ν (fun z ↦ f (insertSite i z Y))
      (fun z ↦ greenGradient (z - y))‖ ^ 2 ≤
      nearCoefficient β₀ * ∫ z, ‖coordinateOrdinaryGradient f i (insertSite i z Y)‖ ^ 2 ∂ν := by
  have hh := conditional_covariance_estimates hJ hmesh i Y (A i) (B i) hb
    (physicalLipschitzOn_section hJ A B hf i Y hY) y
  simpa only [torusOrdinaryGradient_section] using hh.near_squared

/-- Explicit-C2 far estimate for an actual configuration section. -/
theorem conditional_section_far_squared {n J R : ℕ} (hJ : 0 < J) (hR : 1 ≤ R)
    {β₀ β C₂ : ℝ} (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PatchOutside hJ A B i Y)
    (hb : LawBounds hJ β₀ β i Y (A i) (B i))
    {f : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hf : ConfigurationPhysicalLipschitzOn L f
      (DeletedConditionalPoincare.closedPatchProduct hJ A B)) (j : Fin n)
    (hfar : ¬ NearPair J hJ R (A i) (A (i.succAbove j)) (B i) (B (i.succAbove j))) :
    let ν := conditionalKernel (patchMeasure J hJ (A i) (B i)) i β Y
    ‖vectorCovariance ν (fun z ↦ f (insertSite i z Y))
      (fun z ↦ greenGradient (z - Y j))‖ ^ 2 ≤
      farCoefficient β₀ C₂ R *
        ∫ z, ‖coordinateOrdinaryGradient f i (insertSite i z Y)‖ ^ 2 ∂ν := by
  have hh := conditional_covariance_far_squared hJ hR hC hk i Y
    (A i) (A (i.succAbove j)) (B i) (B (i.succAbove j)) hb
    (physicalLipschitzOn_section hJ A B hf i Y hY) hfar (hY j)
  simpa only [torusOrdinaryGradient_section] using hh

/-- Actual adjacent configuration sections; the returned pointwise
alternative is ready for the separate collective near/far counting step. -/
theorem adjacent_section_covariance_squared {n J : ℕ} {β₀ β δ : ℝ}
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (t i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η t a d)
    (Y : Configuration n)
    (hY : PatchOutside (mesh_pos hmesh) (Function.update η t a) (adjacentShapes t d) i Y)
    {f : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hf : ConfigurationPhysicalLipschitzOn L f (DeletedConditionalPoincare.closedPatchProduct
      (mesh_pos hmesh) (Function.update η t a) (adjacentShapes t d))) (j : Fin n) :
    let ν := conditionalKernel (patchMeasure J (mesh_pos hmesh)
      (Function.update η t a i) (adjacentShapes t d i)) i β Y
    let E := ∫ z, ‖coordinateOrdinaryGradient f i (insertSite i z Y)‖ ^ 2 ∂ν
    let C := vectorCovariance ν (fun z ↦ f (insertSite i z Y))
      (fun z ↦ greenGradient (z - Y j))
    ‖C‖ ^ 2 ≤ nearCoefficient β₀ * E ∧
      (¬ NearPair J (mesh_pos hmesh) (radius β₀)
        (Function.update η t a i) (Function.update η t a (i.succAbove j))
        (adjacentShapes t d i) (adjacentShapes t d (i.succAbove j)) →
        ‖C‖ ^ 2 ≤ farCoefficient β₀ hessianConstant (radius β₀) * E) := by
  have hb := (adjacent_conditionals hN hβ hβ₀ hsub hδ hmesh η t i a d hadm).1 Y hY
  exact ⟨conditional_section_near_squared (mesh_pos hmesh) hmesh
      (Function.update η t a) (adjacentShapes t d) i Y hY hb hf (Y j),
    fun hfar ↦ conditional_section_far_squared (mesh_pos hmesh) (radius_one_le β₀)
      hessianConstant_pos.le kernel_hessian_bound (Function.update η t a)
      (adjacentShapes t d) i Y hY hb hf j hfar⟩

end ConfigurationSections

end PeriodicAttractiveLogGas.GreenCovarianceBounds
