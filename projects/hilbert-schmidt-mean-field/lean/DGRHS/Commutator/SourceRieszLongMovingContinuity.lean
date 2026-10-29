import DGRHS.Commutator.SourceRieszLocalDecomposition
import DGRHS.Commutator.SourceMovingLawIntegral

/-! UNCOMPILED singular-generator ingredient. The positive-cutoff first
transport kernel is represented by its actual Gaussian scale integral even
on the collision diagonal, where its single multilinear argument is zero.
Uniform Lipschitz control gives a scale-integrable majorant independent of
space and time, hence joint continuity and moving-law integral continuity. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local instance (n : ℕ) : AddCommMonoid (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toAddCommMonoid
local instance (n : ℕ) : Module ℝ (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E [×n]→L[ℝ] ℝ)).toModule
local instance (n : ℕ) : UniformSpace (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toUniformSpace
local instance (n : ℕ) : TopologicalSpace (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toUniformSpace.toTopologicalSpace

lemma sourceRieszLongTransportKernel_one_scale_formula
    (s η : ℝ) (hs : 0<s) (hη : 0<η) (v : E→E) (p : E×E) :
    sourceRieszLongTransportKernel 1 s η v p =
      gaussianRieszSourceCoefficient s * ∫ t in Ioi η,
        (t^(-s-1) • iteratedFDeriv ℝ 1 (sourceRieszGaussianScale t) (p.1-p.2))
          (fun _ : Fin 1 => v p.1-v p.2) := by
  classical
  by_cases hp : p.1=p.2
  · simp [sourceRieszLongTransportKernel, hp]
  · have hz : p.1-p.2≠0 := sub_ne_zero.mpr hp
    have hi := integrable_sourceRieszGaussian_scale_on 1 s (Ioi η)
      measurableSet_Ioi (Ioi_subset_Ioi hη.le) hs hz
    rw [sourceRieszLongTransportKernel, if_neg hp,
      sourceRieszLongRange_iteratedFDeriv_formula 1 s η hs hη hz,
      smul_apply, smul_eq_mul, ContinuousMultilinearMap.integral_apply hi]

lemma continuous_sourceRieszLongTransportKernel_one_moving
    (s η : ℝ) (hs : 0<s) (hη : 0<η) (v : ℝ→E→E)
    (hv : Continuous (Function.uncurry v)) (K : ℝ≥0)
    (hK : ∀ r, LipschitzWith K (v r)) :
    Continuous (fun p : ℝ×(E×E) => sourceRieszLongTransportKernel 1 s η (v p.1) p.2) := by
  let F : (ℝ×(E×E))→ℝ→ℝ := fun p t =>
    (t^(-s-1) • iteratedFDeriv ℝ 1 (sourceRieszGaussianScale t) (p.2.1-p.2.2))
      (fun _ : Fin 1 => v p.1 p.2.1-v p.1 p.2.2)
  let B : ℝ→ℝ := fun t => (sourceRieszGaussianDerivativeConstant 1*(K:ℝ))*t^(-s-1)
  have hFm (p : ℝ×(E×E)) : AEStronglyMeasurable (F p) (volume.restrict (Ioi η)) := by
    have hc := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => E) ℝ
      (fun _ => v p.1 p.2.1-v p.1 p.2.2)).continuous.comp_continuousOn
      (sourceRieszGaussian_derivative_scale_continuousOn 1 s (Ioi η)
        (Ioi_subset_Ioi hη.le) (p.2.1-p.2.2))
    exact hc.aestronglyMeasurable measurableSet_Ioi
  have hFb (p : ℝ×(E×E)) : ∀ᵐ t ∂volume.restrict (Ioi η), ‖F p t‖≤B t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0<t := hη.trans ht
    have he : Real.exp (-‖p.2.1-p.2.2‖^2/(8*t^2))≤1 :=
      Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
        (by positivity))
    have hC : 0≤sourceRieszGaussianDerivativeConstant 1*(K:ℝ) :=
      mul_nonneg (sourceRieszGaussianDerivativeConstant_pos 1).le K.coe_nonneg
    have hb := sourceRieszGaussian_all_order_transport_bound 1 t ht0 (hK p.1) p.2.1 p.2.2
    simp only [pow_one] at hb
    have hb' : |iteratedFDeriv ℝ 1 (sourceRieszGaussianScale t) (p.2.1-p.2.2)
        (fun _ : Fin 1 => v p.1 p.2.1-v p.1 p.2.2)| ≤
        sourceRieszGaussianDerivativeConstant 1*(K:ℝ) := by
      exact hb.trans ((mul_le_mul_of_nonneg_left he hC).trans_eq (mul_one _))
    dsimp only [F, B]
    simp only [smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb' (Real.rpow_nonneg ht0.le _)
  have hBi : Integrable B (volume.restrict (Ioi η)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s-1 < -1) hη).const_mul
      (sourceRieszGaussianDerivativeConstant 1*(K:ℝ))
  have hFc : ∀ᵐ t ∂volume.restrict (Ioi η), Continuous (fun p => F p t) := by
    apply Eventually.of_forall
    intro t
    have hd : Continuous (fun p : ℝ×(E×E) =>
        t^(-s-1) • iteratedFDeriv ℝ 1 (sourceRieszGaussianScale t) (p.2.1-p.2.2)) :=
      by
        have hderiv : Continuous (fun z : E =>
            iteratedFDeriv ℝ 1 (sourceRieszGaussianScale t) z) :=
          (contDiff_sourceRieszGaussianScale 1 t).continuous_iteratedFDeriv le_rfl
        have harg : Continuous (fun p : ℝ×(E×E) => p.2.1-p.2.2) :=
          (continuous_fst.comp continuous_snd).sub (continuous_snd.comp continuous_snd)
        have hconst : Continuous (fun _ : ℝ×(E×E) => (t^(-s-1):ℝ)) :=
          continuous_const
        exact hconst.smul (hderiv.comp harg)
    have hw : Continuous (fun p : ℝ×(E×E) =>
        fun _ : Fin 1 => v p.1 p.2.1-v p.1 p.2.2) := by
      apply continuous_pi
      intro i
      exact (hv.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).sub
        (hv.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
    have heval : Continuous (fun q : (E [×1]→L[ℝ] ℝ)×(Fin 1→E) => q.1 q.2) :=
      (ContinuousLinearMap.id ℝ (E [×1]→L[ℝ] ℝ)).continuous_uncurry_of_multilinear
    exact heval.comp (hd.prodMk hw)
  have hc := (continuous_of_dominated hFm hFb hBi hFc).const_mul (gaussianRieszSourceCoefficient s)
  simpa only [F, sourceRieszLongTransportKernel_one_scale_formula s η hs hη] using hc

lemma continuous_integral_sourceRieszLongTransportKernel_one_moving
    (s η : ℝ) (hs : 0<s) (hη : 0<η) (v : ℝ→E→E)
    (hv : Continuous (Function.uncurry v)) (K : ℝ≥0)
    (hK : ∀ r, LipschitzWith K (v r))
    (μ : ℝ→ProbabilityMeasure E) (hμ : Continuous μ) :
    Continuous (fun r => ∫ x, ∫ y, sourceRieszLongTransportKernel 1 s η (v r) (x,y)
      ∂(μ r : Measure E) ∂(μ r : Measure E)) := by
  let A := (sourceRieszGaussianDerivativeConstant 1*(2:ℝ)^s)*(K:ℝ)
  have hA : 0≤A := by
    have hc := sourceRieszGaussianDerivativeConstant_pos 1
    dsimp only [A]
    positivity
  have hb (p : ℝ×(E×E)) : |sourceRieszLongTransportKernel 1 s η (v p.1) p.2| ≤
      A*(gaussianRieszSourceCoefficient s/s*η^(-s)) := by
    have h := sourceRieszLongTransportKernel_all_order_bound 1 s η hs hη (hK p.1) p.2
    simp only [pow_one] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ hA
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
      gaussianRieszEuclideanTruncation_le_diagonal s η hs hη (p.2.1-p.2.2))
  exact continuous_integral_moving_probability_pair (fun r : ℝ => r) continuous_id μ hμ
    (fun p => sourceRieszLongTransportKernel 1 s η (v p.1) p.2)
    (continuous_sourceRieszLongTransportKernel_one_moving s η hs hη v hv K hK)
    (A*(gaussianRieszSourceCoefficient s/s*η^(-s))) hb

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.sourceRieszLongTransportKernel_one_scale_formula
#print axioms DGRHS.Commutator.sourceRieszLongTransportKernel_one_scale_formula
#check @DGRHS.Commutator.continuous_sourceRieszLongTransportKernel_one_moving
#print axioms DGRHS.Commutator.continuous_sourceRieszLongTransportKernel_one_moving
#check @DGRHS.Commutator.continuous_integral_sourceRieszLongTransportKernel_one_moving
#print axioms DGRHS.Commutator.continuous_integral_sourceRieszLongTransportKernel_one_moving
