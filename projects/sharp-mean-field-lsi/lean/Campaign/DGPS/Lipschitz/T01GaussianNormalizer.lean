import DGPS.Lipschitz.T01SmoothingWitness
import DGPS.Lipschitz.GaussianKernelTilt
import DGPS.Frontier.LIP051.T01
import DGPS.Frontier.LIP051.T14

/-!
# The finite Gaussian normalizer on the same smoothing witness

Legacy coordinate i represents physical mode i+1. The Gaussian-preserving shift explicitly
relates its integral to the campaign's physical coordinates; no pointwise same-coordinate
identification is used.
-/

namespace DGPS.Lipschitz

open MeasureTheory ProbabilityTheory Filter Topology KernelApproximation
  DGPS.Frontier.LIP051

/-- Shifting the countable iid Gaussian coordinates preserves their product law. -/
theorem t01_gaussian_shift_preserving :
    MeasurePreserving (fun (z : ℕ → ℝ) (i : ℕ) => z (i + 1))
      gaussianCountable_LIP016 SharpLSI.gammaRef := by
  refine ⟨by fun_prop, ?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ => gaussianReal 0 1) (add_left_injective 1)

/-- The finite legacy Gaussian integral equals the physical-coordinate raw Gaussian integral. -/
theorem t01_kappaR_eq_kernelRawGaussian {d : ℕ} (S : Spec d) (aux : Aux S)
    (D : KData d) (hsym : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0)
    (J : InteractionData d) (F : SharpLSI.FL.FiniteRankApprox J.W S.mu S.v)
    (R : ℕ) (t : ℝ) (m : ℕ) (hs : F.s R = Finset.range m)
    (ha : ∀ i j, F.a R i j = positiveKernelCoefficient S D t m i j) :
    SharpLSI.FL.kappaR F R =
      ∫ z, kernelRawGaussian_LIP016 S D t m z ∂gaussianCountable_LIP016 := by
  have hquad : ∀ z : ℕ → ℝ,
      (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        kernelCoefficient_LIP016 S D t m i j * z i * z j) =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
        positiveKernelCoefficient S D t m i j * z (i + 1) * z (j + 1) := by
    intro z
    rw [Finset.sum_range_succ']
    simp only [kernelCoefficient_zero_left_LIP016 S D aux.v0 hc,
      zero_mul, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_range_succ']
    simp only [kernelCoefficient_zero_right_LIP016 S D aux.v0 hc hsym, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    rw [kernelCoefficient_LIP016, if_pos ⟨by omega, by omega⟩,
      positiveKernelCoefficient, if_pos ⟨hi', hj'⟩]
  have hm : Measurable (fun z => Real.exp (-SharpLSI.FL.uR F R z)) := by
    unfold SharpLSI.FL.uR
    fun_prop
  unfold SharpLSI.FL.kappaR
  rw [← t01_gaussian_shift_preserving.map_eq,
    integral_map t01_gaussian_shift_preserving.measurable.aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    rw [kernelRawGaussian_quadratic_LIP016, hquad]
    unfold SharpLSI.FL.uR
    simp only [hs, ha]
    congr 1
    ring

/-- Same-witness finite normalizers converge to the canonical physical-coordinate integral. -/
theorem t01_kappaR_tendsto_canonicalQT {d : ℕ} (S : Spec d) (aux : Aux S)
    (J : InteractionData d) (D : KData d) (hD : D.K = centeredKernel J S.mu)
    {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ inner ℝ g (DGPS.densityHessian J (specProbability_LIP016 S) g))
    (t : ℕ → ℝ) (m : ℕ → ℕ) (ht : ∀ R, 0 ≤ t R)
    (htlim : Tendsto t atTop (𝓝 0)) (hm : StrictMono m) {C : ℝ}
    (hbd : ∀ R x y, |smoothK S D (t R) (m R) x y| ≤ C)
    (hU : TendstoUniformly (fun R (p : Torus d × Torus d) => smoothK S D (t R) (m R) p.1 p.2)
      (fun p => D.K p.1 p.2) atTop)
    (F : SharpLSI.FL.FiniteRankApprox J.W S.mu S.v)
    (hs : ∀ R, F.s R = Finset.range (m R))
    (ha : ∀ R i j, F.a R i j = positiveKernelCoefficient S D (t R) (m R) i j) :
    Integrable (fun z => Real.exp (-((QT_LIP05101 S D.K : (ℕ → ℝ) → ℝ) z +
        dK_LIP05101 S D.K) / 2)) gaussianCountable_LIP016 ∧
    0 < ∫ z, Real.exp (-((QT_LIP05101 S D.K : (ℕ → ℝ) → ℝ) z + dK_LIP05101 S D.K) / 2)
      ∂gaussianCountable_LIP016 ∧
    Tendsto (fun R => SharpLSI.FL.kappaR F R) atTop
      (𝓝 (∫ z, Real.exp (-((QT_LIP05101 S D.K : (ℕ → ℝ) → ℝ) z + dK_LIP05101 S D.K) / 2)
        ∂gaussianCountable_LIP016)) := by
  have hD' : ∀ x y, D.K x y = centeredKernel J (specProbability_LIP016 S) x y :=
    fun x y => congrFun (congrFun hD x) y
  have hsym := original_kernel_symmetric_LIP016 S D J hD'
  have hc := original_kernel_centered_LIP016 S D J hD'
  have hH' := original_hessian_transport_LIP016 S D hsym hc J hD' hH
  obtain ⟨q, hq, -⟩ := kernelWick_completion_LIP016 S D hsym t m ht htlim hm
  have hqeq := gate_lip051_01_bind_campaign_data_source_data_QT_unique
    S aux D J hD' t m ht htlim hm q hq
  have htrace := kernelTrace_tendsto_LIP016 S D t m hbd hU
  have hUI := kernelRawGaussian_uniformIntegrable_LIP016 S D hsym hc hσ hH' t m ht hbd
  let f (R : ℕ) := finiteWickOn_LIP016 (kernelCoefficient_LIP016 S D (t R) (m R))
    (Finset.range (m R + 1))
  have hf (R : ℕ) : MemLp (f R) 2 gaussianCountable_LIP016 := finiteWickOn_memLp_LIP016 _ _
  have hAE (R : ℕ) :
      (kernelWickLp_LIP016 S D (t R) (m R) : (ℕ → ℝ) → ℝ) =ᵐ[gaussianCountable_LIP016] f R :=
    (hf R).coeFn_toLp
  have hqm : TendstoInMeasure gaussianCountable_LIP016 f atTop q :=
    TendstoInMeasure.congr_left hAE (tendstoInMeasure_of_tendsto_Lp hq)
  have hFm (R : ℕ) : AEStronglyMeasurable
      (fun z => Real.exp (-(f R z + kernelTrace_LIP016 S D (t R) (m R)) / 2))
      gaussianCountable_LIP016 := by
    apply Measurable.aestronglyMeasurable
    unfold f finiteWickOn_LIP016 matrixWick_LIP016 matrixQuadratic_LIP016 Finset.restrict
    fun_prop
  have hlim := exponential_integral_limit_LIP016 gaussianCountable_LIP016 f q
    (fun R => kernelTrace_LIP016 S D (t R) (m R)) (∫ x, D.K x x ∂S.mu)
    (fun R => (hf R).aestronglyMeasurable) hFm hqm htrace hUI
  rw [hqeq] at hlim
  refine ⟨hlim.1, hlim.2.1, ?_⟩
  apply hlim.2.2.congr
  intro R
  exact (t01_kappaR_eq_kernelRawGaussian S aux D hsym hc J F R (t R) (m R) (hs R) (ha R)).symm

end DGPS.Lipschitz
