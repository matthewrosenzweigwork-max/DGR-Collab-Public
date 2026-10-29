import DGRHS.Gaussian.PeriodicLogTruncatedFeature
import DGRHS.Gaussian.PeriodicHeatGaussianField
import DGRHS.Gaussian.OriginalFeatureProposition
import DGRHS.Concentration.SourcePartitionRate

/-!
Packet P9g, unit 2 (part 2): truncated feature-space Laplace estimate on the torus for the LOG
kernel (TeX Step 1 of Proposition 5.5 at `s = 0`, with the heat-shifted Fourier feature of the
truncation `g_τ`), a direct instance of the generic Proposition 5.4
`original_boundedFeatureQuadLaplace_of_memLp_top`.  The feature diagonal is logarithmic, so the
Laplace constant is `L exp(L (1 + log(1/τ)))` (polynomial in `1/τ`), not `L exp(L τ^{-s/2})`.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Hoeffding-centered truncated periodic kernel (continuous Fourier representative). -/
abbrev periodicLogTruncCentered (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] (τ : ℝ) :
    PeriodicTorus ι × PeriodicTorus ι → ℝ :=
  hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogTruncKernel τ (q.1 - q.2))

theorem periodicLogTruncatedLaplace_diag (β τ : ℝ) (hβ : 0 ≤ β) (hτ : 0 < τ)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] :
    ∃ (hh : MemLp (periodicLogTruncCentered μ τ) 2 (μ.prod μ))
      (σ : Type u) (eig : σ → ℝ) (e : HilbertBasis σ ℝ (Lp ℝ 2 μ)),
      Countable σ ∧
      (∀ i, DGRHS.Kernel.integralOperator (periodicLogTruncCentered μ τ) hh (e i) = eig i • e i) ∧
      (∀ i, 0 ≤ eig i) ∧ Summable eig ∧
      HasProd (fun i => (1 + β * eig i) * Real.exp (-(β * eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => β * eig i)) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (-β / 2 *
          DGRHS.CanonicalVariance.normalizedOffDiagonalSum (periodicLogTruncCentered μ τ) x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        |canonicalPartition μ β (periodicLogTruncCentered μ τ) N -
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          featureBoundedRateConstant β * Real.exp (featureBoundedRateConstant β * β *
            (4 * ∑' k, periodicLogTruncCoeff (ι := ι) τ k)) / (N : ℝ) := by
  borelize ↥(PeriodicHeatFeatureSpace ι)
  have ha := periodicLogTruncCoeff_nonneg (ι := ι) τ
  have hsum := periodicLogTruncCoeff_summable (ι := ι) τ hτ
  have hr := periodicLogTruncCoeff_sqrt_summable (ι := ι) τ hτ
  let a := periodicLogTruncCoeff (ι := ι) τ
  let k := periodicCenteredPositiveFourierFeature a ha hsum μ
  have hkcont : Continuous (periodicPositiveFourierFeature a ha hsum) :=
    periodicPositiveFourierFeature_continuous a ha hsum hr
  have hk : StronglyMeasurable k :=
    (hkcont.stronglyMeasurable).sub stronglyMeasurable_const
  have hμ : μ ≠ 0 := by
    intro hzero
    have hm : μ Set.univ = 1 := measure_univ
    simp [hzero] at hm
  have hkbound (x : PeriodicTorus ι) : ‖k x‖ ≤ 2 * Real.sqrt (∑' j, a j) :=
    periodicCenteredPositiveFourierFeature_norm_le a ha hsum hr μ x
  have hkinf : MemLp k ∞ μ := by
    apply (memLp_const (2 * Real.sqrt (∑' j, a j))).of_le hk.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_of_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))]
    exact hkbound x
  have hmean : (∫ x, k x ∂μ) = 0 := by
    have hi := periodicPositiveFourierFeature_integrable a ha hsum hr μ
    show (∫ x, (periodicPositiveFourierFeature a ha hsum x -
      ∫ y, periodicPositiveFourierFeature a ha hsum y ∂μ) ∂μ) = 0
    rw [integral_sub hi (integrable_const _)]
    simp
  have heq : periodicLogTruncCentered μ τ =ᵐ[μ.prod μ] featureKernel k := by
    filter_upwards with p
    exact (periodicCenteredPositiveFourierFeature_gram a ha hsum hr μ p.1 p.2).symm
  obtain ⟨hh, σ, eig, e, hi, he, hnn, hsm, htr, hP, hD, hC, hRate⟩ :=
    original_boundedFeatureQuadLaplace_of_memLp_top β hβ (periodicLogTruncCentered μ τ) k hk hkinf hmean heq
  have hnorm : (lpNorm k ∞ μ) ^ 2 ≤ 4 * ∑' j, a j := by
    have hsumnn : 0 ≤ ∑' j, a j := tsum_nonneg ha
    have hbound := lpNorm_mono_real
      (memLp_const (2 * Real.sqrt (∑' j, a j)) :
        MemLp (fun _ : PeriodicTorus ι => 2 * Real.sqrt (∑' j, a j)) ∞ μ)
      (fun x => hkbound x)
    rw [lpNorm_const (p := ∞) (by simp) hμ (2 * Real.sqrt (∑' j, a j))] at hbound
    have hn : lpNorm k ∞ μ ≤ 2 * Real.sqrt (∑' j, a j) := by
      simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (∑' j, a j))] using hbound
    have hh2 := pow_le_pow_left₀ lpNorm_nonneg hn 2
    simpa only [mul_pow, Real.sq_sqrt hsumnn, show (2 : ℝ) ^ 2 = 4 by norm_num] using hh2
  refine ⟨hh, σ, eig, e, hi, he, hnn, hsm, hP, hD, ?_⟩
  intro N hN
  have hC0 := featureBoundedRateConstant_pos β hβ
  refine ⟨?_, ?_⟩
  · have := (hRate N hN).1
    simpa only [sourceKernelParticleStatistic_eq_normalized] using this
  · have hb := (hRate N hN).2
    simp_rw [sourceKernelParticleStatistic_eq_normalized] at hb
    change |canonicalPartition μ β (periodicLogTruncCentered μ τ) N - _| ≤ _
    refine hb.trans ?_
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    apply mul_le_mul_of_nonneg_left _ hC0.le
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hnorm (mul_nonneg hC0.le hβ)

/-- Laplace constant of the periodic LOG truncation: `L exp(L (1 + log(1/τ))) / N`. -/
theorem periodicLogTruncatedLaplace (β : ℝ) (hβ : 0 ≤ β) :
    ∃ L : ℝ, 0 < L ∧ ∀ (τ : ℝ), 0 < τ → τ ≤ 1 →
      ∀ (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ],
      ∃ (hh : MemLp (periodicLogTruncCentered μ τ) 2 (μ.prod μ))
        (σ : Type u) (eig : σ → ℝ) (e : HilbertBasis σ ℝ (Lp ℝ 2 μ)),
        Countable σ ∧
        (∀ i, DGRHS.Kernel.integralOperator (periodicLogTruncCentered μ τ) hh (e i) = eig i • e i) ∧
        0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
        Tendsto (canonicalPartition μ β (periodicLogTruncCentered μ τ)) atTop
          (𝓝 ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹)) ∧
        ∀ N : ℕ, 1 ≤ N →
          Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (-β / 2 *
            DGRHS.CanonicalVariance.normalizedOffDiagonalSum (periodicLogTruncCentered μ τ) x))
            (Measure.pi (fun _ : Fin N => μ)) ∧
          |canonicalPartition μ β (periodicLogTruncCentered μ τ) N -
            (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
            L * Real.exp (L * (1 + Real.log (1 / τ))) / (N : ℝ) := by
  obtain ⟨CD, hCD0, hCD⟩ := periodicLogTruncCoeff_tsum_le (ι := ι)
  have hC0 := featureBoundedRateConstant_pos β hβ
  refine ⟨featureBoundedRateConstant β + 4 * featureBoundedRateConstant β * β * CD, by positivity, ?_⟩
  intro τ hτ hτ1 μ _
  obtain ⟨hh, σ, eig, e, hi, he, hnn, hsm, hP, hD, hR⟩ :=
    periodicLogTruncatedLaplace_diag β τ hβ hτ μ
  refine ⟨hh, σ, eig, e, hi, he, hD, ?_, fun N hN => ⟨(hR N hN).1, ?_⟩⟩
  · apply partition_tendsto_of_reciprocal_error _ _
      (featureBoundedRateConstant β * Real.exp (featureBoundedRateConstant β * β *
            (4 * ∑' k, periodicLogTruncCoeff (ι := ι) τ k)))
    intro N hN
    exact (hR N hN).2
  · refine (hR N hN).2.trans ?_
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    have hdiag := hCD τ hτ hτ1
    have hl0 : 0 ≤ Real.log (1 / τ) := Real.log_nonneg (by rw [le_div_iff₀ hτ]; linarith)
    have hLge : featureBoundedRateConstant β ≤
        featureBoundedRateConstant β + 4 * featureBoundedRateConstant β * β * CD := by
      have : 0 ≤ 4 * featureBoundedRateConstant β * β * CD := by positivity
      linarith
    apply mul_le_mul hLge _ (Real.exp_pos _).le (by positivity)
    apply Real.exp_le_exp.mpr
    calc featureBoundedRateConstant β * β * (4 * ∑' k, periodicLogTruncCoeff (ι := ι) τ k)
        ≤ featureBoundedRateConstant β * β * (4 * (CD * (1 + Real.log (1 / τ)))) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC0.le hβ)
      _ = (4 * featureBoundedRateConstant β * β * CD) * (1 + Real.log (1 / τ)) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        have : 0 ≤ featureBoundedRateConstant β := hC0.le
        linarith

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicLogTruncCentered
#print axioms DGRHS.Periodic.periodicLogTruncatedLaplace_diag
#print axioms DGRHS.Periodic.periodicLogTruncatedLaplace
