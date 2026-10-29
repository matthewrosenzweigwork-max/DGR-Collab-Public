/- UNCHECKED outside frozen proof. Finite spectral particle law converges to
an explicit finite chaos on the SAME countable Gaussian product. Every CLT and
law transport premise is supplied by the actual construction. -/
import DGRHS.CLT.SpectralResidual
import DGRHS.CLT.LawTransport
import DGRHS.CLT.ProductTransport
import Mathlib.Algebra.BigOperators.Fin
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology InnerProductSpace BigOperators
namespace DGRHS.CLT
variable {S E j : Type*} [MeasurableSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype j]
  {μ : Measure S} [IsProbabilityMeasure μ]

lemma finiteSpectralQuadratic_standardVector (a : j → ℝ)
    (b : HilbertBasis j ℝ E) (z : j → ℝ) :
    finiteSpectralQuadratic a b (finiteStandardVector b z) - ∑ i, a i =
      ∑ i, a i * ((z i)^2 - 1) := by
  classical
  unfold finiteSpectralQuadratic finiteStandardVector
  simp only [inner_sum, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma normalizedFiniteKernel_eq_chaosStatistic (a : j → ℝ)
    (b : HilbertBasis j ℝ E) (e : j → Lp ℝ 2 μ) (N : ℕ) (x : Fin N → S) :
    DGRHS.CanonicalVariance.normalizedOffDiagonalSum (finiteSpectralKernel a e) x =
      finiteSpectralQuadratic a b ((Real.sqrt N)⁻¹ • ∑ i : Fin N,
        finiteEigenFeature b e (x i)) -
      (N : ℝ)⁻¹ * ∑ i : Fin N, finiteSpectralDiagonal a e (x i) := by
  classical
  rw [normalizedOffDiagonalSum_finiteSpectralKernel,
    finiteSpectralQuadratic_finiteEigenFeature_sum]
  unfold finiteSpectralDiagonal
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.mul_sum]
  ring

/-- Actual finite-rank convergence, on the changing finite particle products,
with no desired convergence hypothesis and no new Gaussian witness. -/
theorem finiteParticleChaosCLT (a : j → ℝ) (b : HilbertBasis j ℝ E)
    (e : j → Lp ℝ 2 μ) (he : Orthonormal ℝ e)
    (hm : ∀ i, (∫ x, e i x ∂μ) = 0)
    (f : j → ℕ) (hf : Function.Injective f) :
    TendstoInDistribution
      (fun N => DGRHS.CanonicalVariance.normalizedOffDiagonalSum
        (ι := Fin N) (finiteSpectralKernel a e)) atTop
      (fun ω : ℕ → ℝ => ∑ i, a i * ((ω (f i))^2 - 1))
      (fun N => Measure.pi (fun _ : Fin N => μ)) IsonormalProcess.iidStdGaussian := by
  classical
  have hc := tendstoInDistribution_finiteSpectralChaos a b e he hm
  have hsource :
      (fun (N : ℕ) (ω : ℕ → S) => finiteSpectralQuadratic a b ((Real.sqrt N)⁻¹ •
        ∑ i ∈ Finset.range N, finiteEigenFeature b e (ω i)) -
        (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, finiteSpectralDiagonal a e (ω i)) =
      (fun (N : ℕ) (ω : ℕ → S) => DGRHS.CanonicalVariance.normalizedOffDiagonalSum
        (finiteSpectralKernel a e) (fun i : Fin N => ω i)) := by
    funext N ω
    rw [normalizedFiniteKernel_eq_chaosStatistic a b e N]
    simp only [Finset.sum_range]
  have htarget : (fun z : j → ℝ =>
      finiteSpectralQuadratic a b (finiteStandardVector b z) - ∑ i, a i) =
      (fun z : j → ℝ => ∑ i, a i * ((z i)^2 - 1)) := by
    funext z
    exact finiteSpectralQuadratic_standardVector a b z
  rw [hsource, htarget] at hc
  have hfinite := tendstoInDistribution_transport_source
    (fun N => DGRHS.CanonicalVariance.normalizedOffDiagonalSum
      (ι := Fin N) (finiteSpectralKernel a e))
    (fun z : j → ℝ => ∑ i, a i * ((z i)^2 - 1))
    (fun (N : ℕ) (ω : ℕ → S) => fun i : Fin N => ω i)
    (prefixSample_measurePreserving μ)
    (fun N => (memLp_normalizedOffDiagonalSum (ι := Fin N)
      (finiteSpectralKernel a e) (memLp_finiteSpectralKernel a e)).aemeasurable) hc
  exact tendstoInDistribution_transport_target hfinite
    (identDistrib_selectedGaussian_polynomial f hf
      (fun z : j → ℝ => ∑ i, a i * ((z i)^2 - 1)) (by fun_prop)).symm

end DGRHS.CLT
#print axioms DGRHS.CLT.normalizedFiniteKernel_eq_chaosStatistic
#print axioms DGRHS.CLT.finiteParticleChaosCLT
