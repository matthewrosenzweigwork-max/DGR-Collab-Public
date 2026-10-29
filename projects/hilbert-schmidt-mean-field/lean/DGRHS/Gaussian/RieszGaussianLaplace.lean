import DGRHS.Gaussian.RieszGaussianCentering
import DGRHS.Gaussian.OriginalFeatureProposition

/-! Actual original-proposition instantiation for the constructed centered
Gaussian-profile Riesz scale integral. No Gaussian, covariance, spectral
matching, determinant-limit, or rate conclusion is supplied as a premise.
The source coefficient normalization and Euclidean norm adapter remain separate. -/
noncomputable section
open MeasureTheory TopologicalSpace
open scoped BigOperators ENNReal
namespace DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι]

def rieszGaussianLaplaceConstant (β c s : ℝ) : ℝ :=
  featureBoundedRateConstant β + 4 * featureBoundedRateConstant β * β * (c / s) + 1

lemma lpNorm_sq_centeredRieszGaussianFourierFeature_le (c s η : ℝ)
    (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η) (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] :
    (lpNorm (centeredRieszGaussianFourierFeature c s η hc hs hη μ) ∞ μ) ^ 2 ≤
      4 * (c / s * η ^ (-s)) := by
  have hμ : μ ≠ 0 := by
    intro hzero
    have hm : μ Set.univ = 1 := measure_univ
    simp [hzero] at hm
  have hR : 0 ≤ c / s * η ^ (-s) :=
    mul_nonneg (div_nonneg hc hs.le) (Real.rpow_nonneg hη.le _)
  have hbound := lpNorm_mono_real
    (memLp_const (2 * Real.sqrt (c / s * η ^ (-s))) :
      MemLp (fun _ : ι → ℝ => 2 * Real.sqrt (c / s * η ^ (-s))) ∞ μ)
    (fun x => norm_centeredRieszGaussianFourierFeature_le c s η hc hs hη μ x)
  have hnorm : lpNorm (centeredRieszGaussianFourierFeature c s η hc hs hη μ) ∞ μ ≤
      2 * Real.sqrt (c / s * η ^ (-s)) := by
    rw [lpNorm_const (p := ∞) (by simp) hμ (2 * Real.sqrt (c / s * η ^ (-s)))] at hbound
    simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (c / s * η ^ (-s)))] using hbound
  have hh := pow_le_pow_left₀ lpNorm_nonneg hnorm 2
  simpa only [mul_pow, Real.sq_sqrt hR, show (2 : ℝ) ^ 2 = 4 by norm_num] using hh

lemma rieszGaussianLaplace_numeric (β c s η Z L : ℝ)
    (hβ : 0 ≤ β) (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η)
    (K : ℝ) (hK : K ^ 2 ≤ 4 * (c / s * η ^ (-s))) (N : ℕ) (hN : 1 ≤ N)
    (h : |Z - L| ≤ featureBoundedRateConstant β *
      Real.exp (featureBoundedRateConstant β * β * K ^ 2) / (N : ℝ)) :
    0 < rieszGaussianLaplaceConstant β c s ∧
      |Z - L| ≤ rieszGaussianLaplaceConstant β c s *
        Real.exp (rieszGaussianLaplaceConstant β c s * η ^ (-s)) / (N : ℝ) := by
  have hC := featureBoundedRateConstant_pos β hβ
  have hterm : 0 ≤ 4 * featureBoundedRateConstant β * β * (c / s) := by positivity
  have hlarger : featureBoundedRateConstant β ≤ rieszGaussianLaplaceConstant β c s := by
    unfold rieszGaussianLaplaceConstant
    linarith
  have hcoef : 4 * featureBoundedRateConstant β * β * (c / s) ≤
      rieszGaussianLaplaceConstant β c s := by
    unfold rieszGaussianLaplaceConstant
    linarith
  have hpos : 0 < rieszGaussianLaplaceConstant β c s := lt_of_lt_of_le hC hlarger
  have he : featureBoundedRateConstant β * β * K ^ 2 ≤
      rieszGaussianLaplaceConstant β c s * η ^ (-s) := by
    calc
      _ ≤ featureBoundedRateConstant β * β * (4 * (c / s * η ^ (-s))) :=
        mul_le_mul_of_nonneg_left hK (mul_nonneg hC.le hβ)
      _ = (4 * featureBoundedRateConstant β * β * (c / s)) * η ^ (-s) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hη.le _)
  refine ⟨hpos, h.trans ?_⟩
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact mul_le_mul hlarger (Real.exp_le_exp.mpr he) (Real.exp_pos _).le hpos.le

 theorem rieszGaussianTruncatedLaplace
    (β c s η : ℝ) (hβ : 0 ≤ β) (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η)
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] :
    ∃ (hh : MemLp (fun p : (ι → ℝ) × (ι → ℝ) =>
        centeredRieszGaussianTruncatedKernel c s η μ p.1 p.2) 2 (μ.prod μ))
      (σ : Type u) (eig : σ → ℝ) (e : HilbertBasis σ ℝ (Lp ℝ 2 μ)),
      Countable σ ∧
      (∀ i, DGRHS.Kernel.integralOperator
        (fun p => centeredRieszGaussianTruncatedKernel c s η μ p.1 p.2) hh (e i) = eig i • e i) ∧
      (∀ i, 0 ≤ eig i) ∧ Summable eig ∧
      HasProd (fun i => (1 + β * eig i) * Real.exp (-(β * eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => β * eig i)) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      0 < rieszGaussianLaplaceConstant β c s ∧
      ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x => Real.exp (-β / 2 * sourceKernelParticleStatistic
          (fun p => centeredRieszGaussianTruncatedKernel c s η μ p.1 p.2) N x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        |(∫ x, Real.exp (-β / 2 * sourceKernelParticleStatistic
          (fun p => centeredRieszGaussianTruncatedKernel c s η μ p.1 p.2) N x)
          ∂Measure.pi (fun _ : Fin N => μ)) -
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          rieszGaussianLaplaceConstant β c s *
            Real.exp (rieszGaussianLaplaceConstant β c s * η ^ (-s)) / (N : ℝ) := by
  letI := finite_rieszGaussianScaleMeasure c s η hc hs hη
  letI := separableSpace_gaussianScaleMixtureHilbert (ι := ι) (rieszGaussianScaleMeasure c s η)
  letI : MeasurableSpace (Lp ℂ 2 ((rieszGaussianScaleMeasure c s η).prod (finiteStandardGaussian ι))) := borel _
  letI : BorelSpace (Lp ℂ 2 ((rieszGaussianScaleMeasure c s η).prod (finiteStandardGaussian ι))) := ⟨rfl⟩
  let k := centeredRieszGaussianFourierFeature (ι := ι) c s η hc hs hη μ
  let h := fun p : (ι → ℝ) × (ι → ℝ) => centeredRieszGaussianTruncatedKernel c s η μ p.1 p.2
  have heq : h =ᵐ[μ.prod μ] featureKernel k := by
    filter_upwards with p
    exact (inner_centeredRieszGaussianFourierFeature c s η hc hs hη μ p.1 p.2).symm
  obtain ⟨hh, σ, eig, e, hi, he, ha, hsum, htrace, hP, hD, hC, hRate⟩ :=
    original_boundedFeatureQuadLaplace_of_memLp_top β hβ h k
      (stronglyMeasurable_centeredRieszGaussianFourierFeature c s η hc hs hη μ)
      (memLp_centeredRieszGaussianFourierFeature c s η hc hs hη μ ∞)
      (integral_centeredRieszGaussianFourierFeature c s η hc hs hη μ) heq
  have hCl : 0 < rieszGaussianLaplaceConstant β c s := by
    have ht : 0 ≤ 4 * featureBoundedRateConstant β * β * (c / s) := by positivity
    unfold rieszGaussianLaplaceConstant
    linarith
  refine ⟨hh, σ, eig, e, hi, he, ha, hsum, hP, hD, hCl, ?_⟩
  intro N hN
  refine ⟨(hRate N hN).1, ?_⟩
  exact (rieszGaussianLaplace_numeric β c s η _ _ hβ hc hs hη (lpNorm k ∞ μ)
    (lpNorm_sq_centeredRieszGaussianFourierFeature_le c s η hc hs hη μ)
    N hN (hRate N hN).2).2

end DGRHS.Gaussian
#check DGRHS.Gaussian.rieszGaussianLaplaceConstant
#check DGRHS.Gaussian.lpNorm_sq_centeredRieszGaussianFourierFeature_le
#check DGRHS.Gaussian.rieszGaussianLaplace_numeric
#check DGRHS.Gaussian.rieszGaussianTruncatedLaplace
#print axioms DGRHS.Gaussian.rieszGaussianLaplaceConstant
#print axioms DGRHS.Gaussian.lpNorm_sq_centeredRieszGaussianFourierFeature_le
#print axioms DGRHS.Gaussian.rieszGaussianLaplace_numeric
#print axioms DGRHS.Gaussian.rieszGaussianTruncatedLaplace
