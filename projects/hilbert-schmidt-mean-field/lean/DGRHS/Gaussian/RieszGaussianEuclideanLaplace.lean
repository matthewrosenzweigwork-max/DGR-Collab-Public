import DGRHS.Gaussian.RieszGaussianEuclideanCentering
import DGRHS.Gaussian.RieszGaussianLaplace

/-! Actual normalized Euclidean physical cutoff partition-function endpoint.
The source coefficient, source scale profile, centered kernel, actual integral
operator, full eigenbasis and determinant product are constructed, not premises.
This is the Gaussian-profile Riesz s>0 branch of eq:truncatedLaplaceRateEta. -/
noncomputable section
open MeasureTheory TopologicalSpace
open scoped BigOperators ENNReal
namespace DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι]

lemma lpNorm_sq_centeredGaussianRieszEuclideanFourierFeature_le (s η : ℝ)
     (hs : 0 < s) (hη : 0 < η) (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    (lpNorm (centeredGaussianRieszEuclideanFourierFeature s η hs hη μ) ∞ μ) ^ 2 ≤
      4 * (gaussianRieszSourceCoefficient s / s * η ^ (-s)) := by
  have hμ : μ ≠ 0 := by
    intro hzero
    have hm : μ Set.univ = 1 := measure_univ
    simp [hzero] at hm
  have hR : 0 ≤ gaussianRieszSourceCoefficient s / s * η ^ (-s) :=
    mul_nonneg (div_nonneg (gaussianRieszSourceCoefficient_pos s hs).le hs.le) (Real.rpow_nonneg hη.le _)
  have hbound := lpNorm_mono_real
    (memLp_const (2 * Real.sqrt (gaussianRieszSourceCoefficient s / s * η ^ (-s))) :
      MemLp (fun _ : EuclideanSpace ℝ ι => 2 * Real.sqrt (gaussianRieszSourceCoefficient s / s * η ^ (-s))) ∞ μ)
    (fun x => norm_centeredGaussianRieszEuclideanFourierFeature_le s η hs hη μ x)
  have hnorm : lpNorm (centeredGaussianRieszEuclideanFourierFeature s η hs hη μ) ∞ μ ≤
      2 * Real.sqrt (gaussianRieszSourceCoefficient s / s * η ^ (-s)) := by
    rw [lpNorm_const (p := ∞) (by simp) hμ (2 * Real.sqrt (gaussianRieszSourceCoefficient s / s * η ^ (-s)))] at hbound
    simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (gaussianRieszSourceCoefficient s / s * η ^ (-s)))] using hbound
  have hh := pow_le_pow_left₀ lpNorm_nonneg hnorm 2
  simpa only [mul_pow, Real.sq_sqrt hR, show (2 : ℝ) ^ 2 = 4 by norm_num] using hh

 theorem gaussianRieszEuclideanTruncatedLaplace
    (β s η : ℝ) (hβ : 0 ≤ β) (hs : 0 < s) (hη : 0 < η)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    ∃ (hh : MemLp (fun p : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι) =>
        centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2) 2 (μ.prod μ))
      (σ : Type u) (eig : σ → ℝ) (e : HilbertBasis σ ℝ (Lp ℝ 2 μ)),
      Countable σ ∧
      (∀ i, DGRHS.Kernel.integralOperator
        (fun p => centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2) hh (e i) = eig i • e i) ∧
      (∀ i, 0 ≤ eig i) ∧ Summable eig ∧
      HasProd (fun i => (1 + β * eig i) * Real.exp (-(β * eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => β * eig i)) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      0 < rieszGaussianLaplaceConstant β (gaussianRieszSourceCoefficient s) s ∧
      ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x => Real.exp (-β / 2 * sourceKernelParticleStatistic
          (fun p => centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2) N x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        |(∫ x, Real.exp (-β / 2 * sourceKernelParticleStatistic
          (fun p => centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2) N x)
          ∂Measure.pi (fun _ : Fin N => μ)) -
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          rieszGaussianLaplaceConstant β (gaussianRieszSourceCoefficient s) s *
            Real.exp (rieszGaussianLaplaceConstant β (gaussianRieszSourceCoefficient s) s * η ^ (-s)) / (N : ℝ) := by
  have hc : 0 ≤ gaussianRieszSourceCoefficient s := (gaussianRieszSourceCoefficient_pos s hs).le
  letI := finite_rieszGaussianScaleMeasure (gaussianRieszSourceCoefficient s) s η (gaussianRieszSourceCoefficient_pos s hs).le hs hη
  letI := separableSpace_gaussianScaleMixtureHilbert (ι := ι) (rieszGaussianScaleMeasure (gaussianRieszSourceCoefficient s) s η)
  letI : MeasurableSpace (Lp ℂ 2 ((rieszGaussianScaleMeasure (gaussianRieszSourceCoefficient s) s η).prod (finiteStandardGaussian ι))) := borel _
  letI : BorelSpace (Lp ℂ 2 ((rieszGaussianScaleMeasure (gaussianRieszSourceCoefficient s) s η).prod (finiteStandardGaussian ι))) := ⟨rfl⟩
  let k := centeredGaussianRieszEuclideanFourierFeature (ι := ι) s η hs hη μ
  let h := fun p : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι) => centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2
  have heq : h =ᵐ[μ.prod μ] featureKernel k := by
    filter_upwards with p
    exact (inner_centeredGaussianRieszEuclideanFourierFeature s η hs hη μ p.1 p.2).symm
  obtain ⟨hh, σ, eig, e, hi, he, ha, hsum, htrace, hP, hD, hC, hRate⟩ :=
    original_boundedFeatureQuadLaplace_of_memLp_top β hβ h k
      (stronglyMeasurable_centeredGaussianRieszEuclideanFourierFeature s η hs hη μ)
      (memLp_centeredGaussianRieszEuclideanFourierFeature s η hs hη μ ∞)
      (integral_centeredGaussianRieszEuclideanFourierFeature s η hs hη μ) heq
  have hCl : 0 < rieszGaussianLaplaceConstant β (gaussianRieszSourceCoefficient s) s := by
    have ht : 0 ≤ 4 * featureBoundedRateConstant β * β * (gaussianRieszSourceCoefficient s / s) := by positivity
    unfold rieszGaussianLaplaceConstant
    linarith
  refine ⟨hh, σ, eig, e, hi, he, ha, hsum, hP, hD, hCl, ?_⟩
  intro N hN
  refine ⟨(hRate N hN).1, ?_⟩
  exact (rieszGaussianLaplace_numeric β (gaussianRieszSourceCoefficient s) s η _ _ hβ (gaussianRieszSourceCoefficient_pos s hs).le hs hη (lpNorm k ∞ μ)
    (lpNorm_sq_centeredGaussianRieszEuclideanFourierFeature_le s η hs hη μ)
    N hN (hRate N hN).2).2

end DGRHS.Gaussian
#check DGRHS.Gaussian.lpNorm_sq_centeredGaussianRieszEuclideanFourierFeature_le
#print axioms DGRHS.Gaussian.lpNorm_sq_centeredGaussianRieszEuclideanFourierFeature_le
#check DGRHS.Gaussian.gaussianRieszEuclideanTruncatedLaplace
#print axioms DGRHS.Gaussian.gaussianRieszEuclideanTruncatedLaplace
