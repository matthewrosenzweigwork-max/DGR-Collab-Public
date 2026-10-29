/- UNCHECKED outside frozen proof. Full signed Hilbert-Schmidt particle CLT:
all finite limits and both approximation errors are supplied by the actual
spectral construction. No trace, positivity, fourth spatial moment or desired
limiting-law hypothesis is imposed. Measurable source representative is explicit;
AE-representative transfer to the paper's L2 equivalence class remains separate. -/
import DGRHS.CLT.SpectralApproximationBridge
import DGRHS.CLT.BoundedLipschitz
import Mathlib.Topology.Algebra.InfiniteSum.Group
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.CLT
universe u
variable {S : Type u} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

/-- The supplied basis belongs to the actual operator. The proof constructs
finite-rank CLTs and both residual limits rather than assuming them. -/
theorem hilbertSchmidtParticleChaosCLT {ι : Type*} [Countable ι]
    (h : S × S → ℝ) (hhm : Measurable h) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0)
    (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (hb : ∀ i, DGRHS.Kernel.integralOperator h hh (b i) = eig i • b i)
    (f : {i // eig i ≠ 0} → ℕ) (hf : Function.Injective f) :
    TendstoInDistribution
      (fun N => DGRHS.CanonicalVariance.normalizedOffDiagonalSum (ι := Fin N) h)
      atTop (DGRHS.Gaussian.centeredGaussianChaos (fun i : {i // eig i ≠ 0} => eig i.val) f)
      (fun N => Measure.pi (fun _ : Fin N => μ)) IsonormalProcess.iidStdGaussian := by
  classical
  let ss := nonzeroSpectralExhaustion eig f hf
  have hss : Tendsto ss atTop atTop := tendsto_nonzeroSpectralExhaustion eig f hf
  let a : ∀ m, ss m → ℝ := fun m i => eig i.val.val
  let e : ∀ m, ss m → Lp ℝ 2 μ := fun m i => b i.val.val
  let bf : ∀ m, HilbertBasis (ss m) ℝ (EuclideanSpace ℝ (ss m)) :=
    fun m => (EuclideanSpace.basisFun (ss m) ℝ).toHilbertBasis
  let km := fun m => finiteSpectralKernel (a m) (e m)
  let Gm := fun m (ω : ℕ → ℝ) => ∑ i ∈ ss m, eig i.val * ((ω (f i))^2 - 1)
  let Q := DGRHS.Gaussian.centeredGaussianChaos (fun i : {i // eig i ≠ 0} => eig i.val) f
  have hm : ∀ m i, (∫ x, e m i x ∂μ) = 0 := by
    intro m i
    exact nonzero_eigenfunctions_mean_zero h hh hs hc eig b hb i.val
  have he : ∀ m, Orthonormal ℝ (e m) := by
    intro m
    exact b.orthonormal.comp (fun i : ss m => i.val.val)
      (Subtype.val_injective.comp Subtype.val_injective)
  have hf' : ∀ m, Function.Injective (fun i : ss m => f i.val) := by
    intro m
    exact hf.comp Subtype.val_injective
  have hfinite : ∀ m, TendstoInDistribution
      (fun N => DGRHS.CanonicalVariance.normalizedOffDiagonalSum (ι := Fin N) (km m))
      atTop (Gm m) (fun N => Measure.pi (fun _ : Fin N => μ))
      IsonormalProcess.iidStdGaussian := by
    intro m
    have ht := finiteParticleChaosCLT (a m) (bf m) (e m) (he m) (hm m)
        (fun i : ss m => f i.val) (hf' m)
    have hg : (fun ω : ℕ → ℝ => ∑ i : ss m,
        eig i.val.val * ((ω (f i.val))^2 - 1)) = Gm m := by
      funext ω
      exact Finset.sum_coe_sort (ss m)
        (fun i : {i // eig i ≠ 0} => eig i.val * ((ω (f i))^2 - 1))
    change TendstoInDistribution
      (fun N => DGRHS.CanonicalVariance.normalizedOffDiagonalSum (ι := Fin N) (km m))
      atTop (fun ω : ℕ → ℝ => ∑ i : ss m,
        eig i.val.val * ((ω (f i.val))^2 - 1))
      (fun N => Measure.pi (fun _ : Fin N => μ)) IsonormalProcess.iidStdGaussian at ht
    rw [hg] at ht
    exact ht
  have ha : Summable (fun i : {i // eig i ≠ 0} => (eig i.val)^2) :=
    (DGRHS.Kernel.summable_integralOperator_eigenvalue_sq h hh eig b hb).subtype _
  have hQ : TendstoInDistribution Gm atTop Q
      (fun _ => IsonormalProcess.iidStdGaussian) IsonormalProcess.iidStdGaussian := by
    exact (DGRHS.Gaussian.tendstoInMeasure_centeredGaussianChaos
      (fun i : {i // eig i ≠ 0} => eig i.val) f hf ha hss).tendstoInDistribution
        (fun m => (show Measurable (fun ω : ℕ → ℝ =>
          ∑ i ∈ ss m, eig i.val * ((ω (f i))^2 - 1)) from by fun_prop).aemeasurable)
  have hK := tendsto_kernel_nonzero_spectral h hh eig b hb f hf
  have hkm : ∀ m, (memLp_finiteSpectralKernel (a m) (e m)).toLp (km m) =
      ∑ i ∈ ss m, eig i.val • DGRHS.Kernel.separatedLp (b i.val) (b i.val) := by
    intro m
    rw [toLp_finiteSpectralKernel]
    simpa only [a, e] using Finset.sum_coe_sort (ss m)
      (fun i : {i // eig i ≠ 0} => eig i.val • DGRHS.Kernel.separatedLp (b i.val) (b i.val))
  apply tendstoInDistribution_of_bounded_lipschitz _ Q
    (fun N => (memLp_normalizedOffDiagonalSum (ι := Fin N) h hh).aemeasurable)
    (Lp.memLp Q).aemeasurable
  intro F hbounded L hL
  let u := fun N => ∫ x : Fin N → S,
    F (DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
      ∂Measure.pi (fun _ : Fin N => μ)
  let v := fun m N => ∫ x : Fin N → S,
    F (DGRHS.CanonicalVariance.normalizedOffDiagonalSum (km m) x)
      ∂Measure.pi (fun _ : Fin N => μ)
  let z := ∫ ω, F (Q ω) ∂IsonormalProcess.iidStdGaussian
  let am := fun m => ∫ ω, F (Gm m ω) ∂IsonormalProcess.iidStdGaussian
  let r := fun m => (L : ℝ) * Real.sqrt 2 *
    ‖hh.toLp h - ∑ i ∈ ss m, eig i.val • DGRHS.Kernel.separatedLp (b i.val) (b i.val)‖
  have hr : Tendsto r atTop (𝓝 0) := by
    have ht := ((tendsto_const_nhds (x := hh.toLp h)).sub hK).norm
    simpa only [r, sub_self, norm_zero, mul_zero] using
      (tendsto_const_nhds.mul ht : Tendsto
        (fun m => (L : ℝ) * Real.sqrt 2 *
          ‖hh.toLp h - ∑ i ∈ ss m, eig i.val • DGRHS.Kernel.separatedLp (b i.val) (b i.val)‖)
        atTop (𝓝 ((L : ℝ) * Real.sqrt 2 * ‖hh.toLp h - hh.toLp h‖)))
  have ham : Tendsto am atTop (𝓝 z) :=
    bounded_lipschitz_integral_tendsto_of_tendstoInDistribution Gm Q hQ F hbounded L hL
  have hv : ∀ m, Tendsto (v m) atTop (𝓝 (am m)) := by
    intro m
    exact bounded_lipschitz_integral_tendsto_of_tendstoInDistribution _ _
      (hfinite m) F hbounded L hL
  have huv : ∀ m N, dist (u N) (v m N) ≤ r m := by
    intro m N
    have hbound := finiteSpectral_particle_test_error (ι := Fin N)
      h hhm hh hs hc (a m) (e m) (hm m) F L hL hbounded
    have hsum : (∑ i : ss m, a m i • DGRHS.Kernel.separatedLp (e m i) (e m i)) =
        ∑ i ∈ ss m, eig i.val • DGRHS.Kernel.separatedLp (b i.val) (b i.val) := by
      simpa only [a, e] using Finset.sum_coe_sort (ss m)
        (fun i : {i // eig i ≠ 0} => eig i.val • DGRHS.Kernel.separatedLp (b i.val) (b i.val))
    rw [hsum] at hbound
    exact hbound
  exact tendsto_of_uniform_approximation u v am r z hr ham hv huv

/-- Actual full eigenbasis and injection are constructed from the source
kernel; neither a favorable enumeration nor a limiting law is assumed. -/
theorem exists_hilbertSchmidtParticleChaosCLT [MeasurableSpace.CountablyGenerated S]
    (h : S × S → ℝ) (hhm : Measurable h) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0) :
    ∃ (ι : Type u) (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
      (f : {i // eig i ≠ 0} → ℕ),
      Countable ι ∧ Function.Injective f ∧
      (∀ i, DGRHS.Kernel.integralOperator h hh (b i) = eig i • b i) ∧
      TendstoInDistribution
        (fun N => DGRHS.CanonicalVariance.normalizedOffDiagonalSum (ι := Fin N) h)
        atTop (DGRHS.Gaussian.centeredGaussianChaos (fun i : {i // eig i ≠ 0} => eig i.val) f)
        (fun N => Measure.pi (fun _ : Fin N => μ)) IsonormalProcess.iidStdGaussian := by
  obtain ⟨ι, eig, b, hcount, hb⟩ := DGRHS.Kernel.exists_integralOperator_eigenbasis h hh hs
  letI := hcount
  let f := DGRHS.Gaussian.countableGaussianIndex (ι := {i // eig i ≠ 0})
  exact ⟨ι, eig, b, f, hcount, f.injective, hb,
    hilbertSchmidtParticleChaosCLT h hhm hh hs hc eig b hb f f.injective⟩

end DGRHS.CLT
#print axioms DGRHS.CLT.hilbertSchmidtParticleChaosCLT
#print axioms DGRHS.CLT.exists_hilbertSchmidtParticleChaosCLT
