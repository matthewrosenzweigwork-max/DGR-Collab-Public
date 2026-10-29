/- UNCHECKED outside frozen proof. Nonzero-label restriction is necessary:
zero-eigenvalue basis vectors need not have zero spatial mean. The HasSum below
is restricted by actual zero coefficients, without falsely treating the
nonzero finite sets as cofinal in the entire ambient eigenbasis. -/
import DGRHS.Kernel.SpectralExpansion
import DGRHS.Gaussian.CenteredChaos
import Mathlib.Order.Filter.AtTopBot.Finset
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.CLT
variable {S ι : Type*} [MeasurableSpace S]
    {μ : Measure S} [IsProbabilityMeasure μ]

def nonzeroSpectralExhaustion (eig : ι → ℝ) (f : {i // eig i ≠ 0} → ℕ)
    (hf : Function.Injective f) (n : ℕ) : Finset {i // eig i ≠ 0} := by
  classical
  exact (Finset.range n).preimage f hf.injOn

lemma tendsto_nonzeroSpectralExhaustion (eig : ι → ℝ)
    (f : {i // eig i ≠ 0} → ℕ) (hf : Function.Injective f) :
    Tendsto (nonzeroSpectralExhaustion eig f hf) atTop atTop := by
  classical
  exact (tendsto_finset_preimage_atTop_atTop hf).comp tendsto_finset_range

lemma nonzero_eigenfunctions_mean_zero
    (k : S × S → ℝ) (hk : MemLp k 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, k p.swap = k p)
    (hc : ∀ᵐ x ∂μ, (∫ y, k (x,y) ∂μ) = 0)
    (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (hb : ∀ i, DGRHS.Kernel.integralOperator k hk (b i) = eig i • b i)
    (i : {i // eig i ≠ 0}) :
    (∫ x, b i.val x ∂μ) = 0 :=
  DGRHS.Kernel.integral_eigenfunction_eq_zero k hk hs hc (b i.val) i.property (hb i.val)

lemma hasSum_kernel_nonzero_spectral [Countable ι]
    (k : S × S → ℝ) (hk : MemLp k 2 (μ.prod μ))
    (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (hb : ∀ i, DGRHS.Kernel.integralOperator k hk (b i) = eig i • b i) :
    HasSum (fun i : {i // eig i ≠ 0} => eig i.val •
      DGRHS.Kernel.separatedLp (b i.val) (b i.val)) (hk.toLp k) := by
  have hfull := DGRHS.Kernel.hasSum_kernel_diagonal_spectral (hk.toLp k) eig b hb
  have hsupport : Function.support (fun i => eig i •
      DGRHS.Kernel.separatedLp (b i) (b i)) ⊆ {i | eig i ≠ 0} := by
    intro i hi hz
    exact hi (by simp [hz])
  exact (hasSum_subtype_iff_of_support_subset hsupport).mpr hfull

lemma tendsto_kernel_nonzero_spectral [Countable ι]
    (k : S × S → ℝ) (hk : MemLp k 2 (μ.prod μ))
    (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (hb : ∀ i, DGRHS.Kernel.integralOperator k hk (b i) = eig i • b i)
    (f : {i // eig i ≠ 0} → ℕ) (hf : Function.Injective f) :
    Tendsto (fun n => ∑ i ∈ nonzeroSpectralExhaustion eig f hf n,
      eig i.val • DGRHS.Kernel.separatedLp (b i.val) (b i.val))
      atTop (𝓝 (hk.toLp k)) :=
  (hasSum_kernel_nonzero_spectral k hk eig b hb).comp
    (tendsto_nonzeroSpectralExhaustion eig f hf)

end DGRHS.CLT
#print axioms DGRHS.CLT.nonzero_eigenfunctions_mean_zero
#print axioms DGRHS.CLT.hasSum_kernel_nonzero_spectral
#print axioms DGRHS.CLT.tendsto_kernel_nonzero_spectral
