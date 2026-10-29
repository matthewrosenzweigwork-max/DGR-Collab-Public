/- UNCHECKED outside the frozen coordinator snapshot. The finite spectral
kernel has exact canonical rows, even though the original kernel is only
canonical almost everywhere. Residual particle estimates use index diagonals.
The complete spectrum theorem must supply the actual eigenbasis and its
nonzero-label truncations. -/
import DGRHS.CLT.FiniteKernelEnergy
import DGRHS.CLT.Approximation
import DGRHS.Kernel.SpectralExpansion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology InnerProductSpace
namespace DGRHS.CLT
variable {S j ι : Type*} [MeasurableSpace S] [Fintype j] [Fintype ι]
    {μ : Measure S} [IsProbabilityMeasure μ]

lemma measurable_finiteSpectralKernel (a : j → ℝ) (e : j → Lp ℝ 2 μ) :
    Measurable (finiteSpectralKernel a e) := by
  classical
  unfold finiteSpectralKernel
  apply Finset.measurable_sum
  intro i _
  exact (measurable_const.mul ((Lp.stronglyMeasurable (e i)).measurable.comp
    measurable_fst)).mul ((Lp.stronglyMeasurable (e i)).measurable.comp measurable_snd)

lemma memLp_finiteSpectralKernel (a : j → ℝ) (e : j → Lp ℝ 2 μ) :
    MemLp (finiteSpectralKernel a e) 2 (μ.prod μ) := by
  classical
  unfold finiteSpectralKernel
  apply memLp_finsetSum
  intro i _
  simpa only [mul_assoc] using
    (DGRHS.Kernel.memLp_separated_mul μ (Lp.memLp (e i)) (Lp.memLp (e i))).const_mul (a i)

lemma symmetric_finiteSpectralKernel (a : j → ℝ) (e : j → Lp ℝ 2 μ) (p : S × S) :
    finiteSpectralKernel a e p.swap = finiteSpectralKernel a e p := by
  classical
  unfold finiteSpectralKernel
  apply Finset.sum_congr rfl
  intro i _
  change a i * e i p.2 * e i p.1 = a i * e i p.1 * e i p.2
  ring

lemma canonical_finiteSpectralKernel (a : j → ℝ) (e : j → Lp ℝ 2 μ)
    (hm : ∀ i, (∫ x, e i x ∂μ) = 0) (x : S) :
    (∫ y, finiteSpectralKernel a e (x,y) ∂μ) = 0 := by
  classical
  unfold finiteSpectralKernel
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i _
    change (∫ y, (a i * e i x) * e i y ∂μ) = 0
    rw [integral_const_mul, hm i, mul_zero]
  · intro i _
    exact ((Lp.memLp (e i)).integrable (by norm_num)).const_mul (a i * e i x)

lemma memLp_normalizedOffDiagonalSum (h : S × S → ℝ)
    (hh : MemLp h 2 (μ.prod μ)) :
    MemLp (DGRHS.CanonicalVariance.normalizedOffDiagonalSum (ι := ι) h)
      2 (Measure.pi (fun _ : ι => μ)) := by
  classical
  unfold DGRHS.CanonicalVariance.normalizedOffDiagonalSum
    DGRHS.CanonicalVariance.offDiagonalSum
  apply MemLp.const_mul
  apply memLp_finsetSum
  intro p hp
  exact DGRHS.Decoupling.memLp_coupled_term μ h 2 hh p.1 p.2
    (Finset.mem_offDiag.mp hp).2.2

lemma normalizedOffDiagonalSum_sub (h g : S × S → ℝ) (x : ι → S) :
    DGRHS.CanonicalVariance.normalizedOffDiagonalSum (fun p => h p - g p) x =
      DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x -
        DGRHS.CanonicalVariance.normalizedOffDiagonalSum g x := by
  classical
  unfold DGRHS.CanonicalVariance.normalizedOffDiagonalSum DGRHS.CanonicalVariance.offDiagonalSum
  rw [Finset.sum_sub_distrib,mul_sub]

lemma norm_particle_residual_le (h : S × S → ℝ)
    (hhm : Measurable h) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0) :
    ‖(memLp_normalizedOffDiagonalSum (ι := ι) h hh).toLp
      (DGRHS.CanonicalVariance.normalizedOffDiagonalSum h)‖ ≤
      Real.sqrt 2 * ‖hh.toLp h‖ := by
  have hn := DGRHS.CanonicalVariance.integral_normalizedOffDiagonalSum_sq_le
    (ι := ι) μ h hhm hh hs hc
  rw [← DGRHS.Kernel.norm_toLp_sq (memLp_normalizedOffDiagonalSum (ι := ι) h hh),
    ← DGRHS.Kernel.norm_toLp_sq hh] at hn
  have hr : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 ≤ Real.sqrt 2 * ‖hh.toLp h‖ := by positivity
  nlinarith [norm_nonneg ((memLp_normalizedOffDiagonalSum (ι := ι) h hh).toLp
    (DGRHS.CanonicalVariance.normalizedOffDiagonalSum h))]

end DGRHS.CLT
#print axioms DGRHS.CLT.canonical_finiteSpectralKernel
#print axioms DGRHS.CLT.memLp_normalizedOffDiagonalSum
#print axioms DGRHS.CLT.norm_particle_residual_le
