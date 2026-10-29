import DGRHS.Commutator.SourceRieszTruncatedTransportKernelIteratedIntegral
import DGRHS.Commutator.SourceRieszTruncatedTransportKernelBound
import DGRHS.Commutator.SourceLogTransportLocal
import DGRHS.Gaussian.GaussianLogShortRange
import DGRHS.Gaussian.GaussianLogInfraredScalar

/-! UNCOMPILED necessary LOG finite-short-scale adapter. The coefficient is ONE.
No use of the positive Riesz coefficient at zero; no candidate Lean ran on host.
All derivative properness is derived on Ioc 0 eta; no all-Ioi logarithmic integral.
The actual ROOT1335 submitted proof forest is untouched. -/
noncomputable section
open MeasureTheory Set Metric
open scoped NNReal Topology
namespace DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
-- Explicit local instances select the existing native operator-norm topologies.
-- They change neither the norm nor any imported instance declaration.
local instance (n : ℕ) : AddCommMonoid (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toAddCommMonoid
local instance (n : ℕ) : Module ℝ (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E [×n]→L[ℝ] ℝ)).toModule
local instance (n : ℕ) : UniformSpace (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toUniformSpace
local instance (n : ℕ) : TopologicalSpace (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toUniformSpace.toTopologicalSpace
local instance (n : ℕ) : UniformSpace (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedAddCommGroup (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toUniformSpace
local instance (n : ℕ) : TopologicalSpace (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedAddCommGroup (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toUniformSpace.toTopologicalSpace
local instance (n : ℕ) : AddCommMonoid (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedAddCommGroup (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toAddCommMonoid
local instance (n : ℕ) : Module ℝ (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedSpace ℝ (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toModule


lemma integrable_sourceLogGaussian_scale_majorant (n : ℕ) (η : ℝ) (hη : 0 < η)
    {z : E} (hz : z ≠ 0) :
    Integrable (fun t : ℝ => sourceRieszGaussianDerivativeConstant n *
      t ^ (-(n : ℝ) - 1) * Real.exp (-‖z‖ ^ 2 / (32 * t ^ 2)))
      (volume.restrict (Ioc 0 η)) := by
  cases n with
  | zero =>
    have hi := DGRHS.Gaussian.integrableOn_gaussianLog_profile_short
      η (‖z‖ / 4) hη (by have h := norm_pos_iff.mpr hz; positivity)
    convert hi.const_mul (sourceRieszGaussianDerivativeConstant 0) using 1
    ext t
    simp only [Nat.cast_zero, neg_zero, zero_sub, Real.rpow_neg_one]
    have he : -‖z‖ ^ 2 / (32 * t ^ 2) = -(‖z‖ / 4) ^ 2 / (2 * t ^ 2) := by ring
    rw [he]
    ring
  | succ n =>
    have hi := (DGRHS.Gaussian.integrableOn_gaussianRiesz_full_scale
      ((n + 1 : ℕ) : ℝ) (‖z‖ ^ 2 / 32) (by positivity)
      (by have h := norm_pos_iff.mpr hz; positivity)).mono_set
      (s := Ioc 0 η) Ioc_subset_Ioi_self
    convert hi.const_mul (sourceRieszGaussianDerivativeConstant (n + 1)) using 1
    ext t
    have he : -‖z‖ ^ 2 / (32 * t ^ 2) = -(‖z‖ ^ 2 / 32) / t ^ 2 := by ring
    rw [he]
    ring

lemma integrable_sourceLogGaussian_derivative_scale (n : ℕ) (η : ℝ) (hη : 0 < η)
    {z : E} (hz : z ≠ 0) :
    Integrable (fun t : ℝ => t⁻¹ • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) z)
      (volume.restrict (Ioc 0 η)) := by
  have ht : ∀ᵐ t ∂volume.restrict (Ioc 0 η), t ∈ Ioc 0 η :=
    self_mem_ae_restrict measurableSet_Ioc
  have hm := (sourceRieszGaussian_derivative_scale_continuousOn n 0 (Ioc 0 η)
    Ioc_subset_Ioi_self z).aestronglyMeasurable (μ := volume) measurableSet_Ioc
  apply (integrable_sourceLogGaussian_scale_majorant n η hη hz).mono'
    (by simpa only [neg_zero, zero_sub, Real.rpow_neg_one] using hm)
  apply ht.mono
  intro t ht
  simpa only [neg_zero, zero_sub, zero_add, Real.rpow_neg_one] using
    sourceRieszGaussian_iteratedFDeriv_local_scale_bound n 0 t ht.1
      (z := z) (y := z) (mem_ball_self (half_pos (norm_pos_iff.mpr hz)))

lemma integrable_sourceLogGaussian_fderiv_scale (n : ℕ) (η : ℝ) (hη : 0 < η)
    {z : E} (hz : z ≠ 0) :
    Integrable (fun t : ℝ => t⁻¹ •
      fderiv ℝ (iteratedFDeriv ℝ n (sourceRieszGaussianScale t : E → ℝ)) z)
      (volume.restrict (Ioc 0 η)) := by
  let C : (E [×(n+1)]→L[ℝ] ℝ) →L[ℝ] (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hc : ContinuousOn (fun t : ℝ => t⁻¹ •
      fderiv ℝ (iteratedFDeriv ℝ n (sourceRieszGaussianScale t : E → ℝ)) z) (Ioc 0 η) := by
    have hc0 := C.continuous.comp_continuousOn
      (sourceRieszGaussian_derivative_scale_continuousOn (n+1) 0 (Ioc 0 η) Ioc_subset_Ioi_self z)
    simp only [neg_zero, zero_sub, Real.rpow_neg_one] at hc0
    apply hc0.congr
    intro t ht
    dsimp only [Function.comp_apply]
    rw [map_smul]
    rfl
  have ht : ∀ᵐ t ∂volume.restrict (Ioc 0 η), t ∈ Ioc 0 η :=
    self_mem_ae_restrict measurableSet_Ioc
  exact (integrable_sourceLogGaussian_scale_majorant (n+1) η hη hz).mono'
    (hc.aestronglyMeasurable measurableSet_Ioc) (ht.mono (fun t ht => by
      simpa only [norm_smul, norm_fderiv_iteratedFDeriv, neg_zero, zero_sub,
        zero_add, Real.rpow_neg_one] using
        sourceRieszGaussian_iteratedFDeriv_local_scale_bound (n+1) 0 t ht.1
          (z := z) (y := z) (mem_ball_self (half_pos (norm_pos_iff.mpr hz)))))

lemma hasFDerivAt_sourceLogGaussian_scale_integral (n : ℕ) (η : ℝ) (hη : 0 < η)
    {z : E} (hz : z ≠ 0) :
    HasFDerivAt
      (fun y : E => ∫ t in Ioc 0 η, t⁻¹ • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) y)
      (∫ t in Ioc 0 η, t⁻¹ • fderiv ℝ (iteratedFDeriv ℝ n (sourceRieszGaussianScale t)) z) z := by
  have ht : ∀ᵐ t ∂volume.restrict (Ioc 0 η), t ∈ Ioc 0 η :=
    self_mem_ae_restrict measurableSet_Ioc
  have hdiff (t : ℝ) : Differentiable ℝ (iteratedFDeriv ℝ n (sourceRieszGaussianScale t : E → ℝ)) :=
    (contDiff_sourceRieszGaussianScale (n+1) t).differentiable_iteratedFDeriv
      (by exact_mod_cast Nat.lt_succ_self n)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y (t : ℝ) => t⁻¹ • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) y)
    (F' := fun y (t : ℝ) => t⁻¹ • fderiv ℝ (iteratedFDeriv ℝ n (sourceRieszGaussianScale t)) y)
    (bound := fun t : ℝ => sourceRieszGaussianDerivativeConstant (n+1) *
      t ^ (-((n+1 : ℕ) : ℝ) - 1) * Real.exp (-‖z‖ ^ 2 / (32 * t ^ 2)))
    (μ := volume.restrict (Ioc 0 η)) (ball_mem_nhds z (half_pos (norm_pos_iff.mpr hz)))
    (Filter.Eventually.of_forall (fun y => by
      simpa only [neg_zero, zero_sub, Real.rpow_neg_one] using
        (sourceRieszGaussian_derivative_scale_continuousOn n 0 (Ioc 0 η)
          Ioc_subset_Ioi_self y).aestronglyMeasurable measurableSet_Ioc))
    (integrable_sourceLogGaussian_derivative_scale n η hη hz)
    (integrable_sourceLogGaussian_fderiv_scale n η hη hz).aestronglyMeasurable
    ?_ (integrable_sourceLogGaussian_scale_majorant (n+1) η hη hz) ?_
  · apply ht.mono
    intro t ht y hy
    simpa only [norm_smul, norm_fderiv_iteratedFDeriv, neg_zero, zero_sub,
      zero_add, Real.rpow_neg_one] using
      sourceRieszGaussian_iteratedFDeriv_local_scale_bound (n+1) 0 t ht.1 hy
  · exact ht.mono (fun t ht y _ =>
      (hdiff t).differentiableAt.hasFDerivAt.const_smul t⁻¹)

lemma sourceLogShortRange_iteratedFDeriv_formula {ι : Type*} [Fintype ι]
    (n : ℕ) (η : ℝ) (hη : 0 < η) {z : EuclideanSpace ℝ ι} (hz : z ≠ 0) :
    iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianLogShortRange η) z =
      ∫ t in Ioc 0 η, t⁻¹ • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) z := by
  induction n generalizing z with
  | zero =>
    ext m
    rw [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.integral_apply
      (integrable_sourceLogGaussian_derivative_scale 0 η hη hz)]
    simp only [smul_apply, iteratedFDeriv_zero_apply, smul_eq_mul,
      DGRHS.Gaussian.gaussianLogShortRange, sourceRieszGaussianScale]
  | succ n IH =>
    have he : iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianLogShortRange η) =ᶠ[𝓝 z]
        (fun y => ∫ t in Ioc 0 η, t⁻¹ • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) y) := by
      filter_upwards [eventually_ne_nhds hz] with y hy
      exact IH hy
    have hf := hasFDerivAt_sourceLogGaussian_scale_integral n η hη hz
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, he.fderiv_eq, hf.fderiv]
    let U := (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (n+1) => EuclideanSpace ℝ ι) ℝ).symm
    have hc := U.toContinuousLinearEquiv.integral_comp_comm
      (μ := volume.restrict (Ioc 0 η))
      (fun t : ℝ => t⁻¹ • fderiv ℝ (iteratedFDeriv ℝ n
        (sourceRieszGaussianScale t : EuclideanSpace ℝ ι → ℝ)) z)
    change (∫ t in Ioc 0 η, U (t⁻¹ • fderiv ℝ (iteratedFDeriv ℝ n
      (sourceRieszGaussianScale t : EuclideanSpace ℝ ι → ℝ)) z)) =
      U (∫ t in Ioc 0 η, t⁻¹ • fderiv ℝ (iteratedFDeriv ℝ n
        (sourceRieszGaussianScale t : EuclideanSpace ℝ ι → ℝ)) z) at hc
    change U (∫ t in Ioc 0 η, t⁻¹ • fderiv ℝ (iteratedFDeriv ℝ n
      (sourceRieszGaussianScale t : EuclideanSpace ℝ ι → ℝ)) z) = _
    rw [← hc]
    congr 1

lemma sourceLogShortRange_all_order_transport_bound {ι : Type*} [Fintype ι]
    (n : ℕ) (η : ℝ) (hη : 0 < η) {K : ℝ≥0}
    {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hv : LipschitzWith K v)
    {x y : EuclideanSpace ℝ ι} (hxy : x ≠ y) :
    |iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianLogShortRange η) (x-y)
      (fun _ => v x-v y)| ≤
      sourceRieszGaussianDerivativeConstant n * (K : ℝ)^n *
        DGRHS.Gaussian.gaussianLogShortRange (2*η) (x-y) := by
  have hz : x-y ≠ 0 := sub_ne_zero.mpr hxy
  have hi := integrable_sourceLogGaussian_derivative_scale n η hη hz
  rw [sourceLogShortRange_iteratedFDeriv_formula n η hη hz,
    ContinuousMultilinearMap.integral_apply hi]
  have hEval : Integrable (fun t : ℝ =>
      (t⁻¹ • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (x-y))
        (fun _ => v x-v y)) (volume.restrict (Ioc 0 η)) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => EuclideanSpace ℝ ι) ℝ
      (fun _ => v x-v y)).integrable_comp hi
  have hG : Integrable (fun t : ℝ => t⁻¹ * Real.exp (-‖x-y‖^2/(8*t^2)))
      (volume.restrict (Ioc 0 η)) := by
    have hh := DGRHS.Gaussian.integrableOn_gaussianLog_profile_short η
      (‖x-y‖/2) hη (by have h := norm_pos_iff.mpr hz; positivity)
    have he : (fun t : ℝ => t⁻¹ * Real.exp (-‖x-y‖^2/(8*t^2))) =
        (fun t : ℝ => t⁻¹ * Real.exp (-(‖x-y‖/2)^2/(2*t^2))) := by
      funext t
      congr 2
      ring
    rw [he]
    exact hh
  have hAbs : Integrable (fun t : ℝ =>
      |(t⁻¹ • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (x-y))
        (fun _ => v x-v y)|) (volume.restrict (Ioc 0 η)) := by
    simpa only [Real.norm_eq_abs] using hEval.norm
  have hB : (∫ t in Ioc 0 η,
      |(t⁻¹ • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (x-y))
        (fun _ => v x-v y)|) ≤
      sourceRieszGaussianDerivativeConstant n * (K : ℝ)^n *
        (∫ t in Ioc 0 η, t⁻¹ * Real.exp (-‖x-y‖^2/(8*t^2))) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hAbs (hG.const_mul _)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    simp only [smul_apply, smul_eq_mul, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr ht.1.le)]
    have hb := sourceRieszGaussian_all_order_transport_bound n t ht.1 hv x y
    calc
      _ ≤ t⁻¹ * (sourceRieszGaussianDerivativeConstant n * (K : ℝ)^n *
        Real.exp (-‖x-y‖^2/(8*t^2))) :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr ht.1.le)
      _ = _ := by ring
  calc
    _ ≤ ∫ t in Ioc 0 η,
        |(t⁻¹ • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (x-y))
          (fun _ => v x-v y)| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun t : ℝ => (t⁻¹ • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (x-y))
          (fun _ => v x-v y))
    _ ≤ _ := hB.trans_eq (by
      have hw := sourceRieszShortScale_widen 0 η ‖x-y‖ hη
      simp only [neg_zero, zero_sub, Real.rpow_neg_one, Real.rpow_zero, one_mul] at hw
      rw [hw]
      rfl)

end DGRHS.Commutator
