/- Development: actual full signed HS joint particle limit with a centered L2
readout, on the SAME full-basis Gaussian process. No desired law is assumed. -/
import DGRHS.CLT.HilbertSchmidtChaosCLT
import DGRHS.CLT.FiniteJointReadout
import DGRHS.CLT.JointApproximation
import DGRHS.Gaussian.NonzeroChaos
import DGRHS.Gaussian.BasisReadout
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators InnerProductSpace NNReal
namespace DGRHS.CLT
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

theorem hilbertSchmidtParticleJointCLT {ι : Type*} [Countable ι]
    (h : S × S → ℝ) (hhm : Measurable h) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0)
    (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (hb : ∀ i, DGRHS.Kernel.integralOperator h hh (b i) = eig i • b i)
    (f : ι → ℕ) (hf : Function.Injective f)
    (v : Lp ℝ 2 μ) (hv : (∫ x, v x ∂μ) = 0) :
    TendstoInDistribution
      (fun N (x : Fin N → S) => ((Real.sqrt N)⁻¹*∑ i : Fin N, v (x i),
        DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) atTop
      (fun ω => (DGRHS.Gaussian.indexedGaussianIsometry b f hf v ω,
        DGRHS.Gaussian.centeredGaussianChaos eig f ω))
      (fun N => Measure.pi (fun _ : Fin N => μ)) IsonormalProcess.iidStdGaussian := by
  classical
  let fn : {i // eig i ≠ 0} → ℕ := fun i => f i.val
  have hfn : Function.Injective fn := hf.comp Subtype.val_injective
  let ss := nonzeroSpectralExhaustion eig fn hfn
  have hss : Tendsto ss atTop atTop := tendsto_nonzeroSpectralExhaustion eig fn hfn
  let a : ∀ m, ss m → ℝ := fun m i => eig i.val.val
  let e : ∀ m, ss m → Lp ℝ 2 μ := fun m i => b i.val.val
  let km := fun m => finiteSpectralKernel (a m) (e m)
  let A := fun N (x : Fin N → S) => (Real.sqrt N)⁻¹*∑ i : Fin N, v (x i)
  let W := DGRHS.Gaussian.indexedGaussianIsometry b f hf v
  let Gm := fun m (ω : ℕ → ℝ) => ∑ i ∈ ss m, eig i.val*((ω (fn i))^2-1)
  let Q := DGRHS.Gaussian.centeredGaussianChaos eig f
  let Zm := fun m (ω : ℕ → ℝ) => (W ω,Gm m ω)
  let Z := fun ω : ℕ → ℝ => (W ω,Q ω)
  have hA : ∀ N, Measurable (A N) := by
    intro N
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i _
    exact (Lp.stronglyMeasurable v).measurable.comp (measurable_pi_apply i)
  have hm : ∀ m i, (∫ x, e m i x ∂μ) = 0 := by
    intro m i
    exact nonzero_eigenfunctions_mean_zero h hh hs hc eig b hb i.val
  have hn : ∀ m i, ‖e m i‖^2 = 1 := by
    intro m i
    rw [← real_inner_self_eq_norm_sq]
    simpa only [e, ite_true] using orthonormal_iff_ite.mp b.orthonormal i.val.val i.val.val
  have hfinite : ∀ m, TendstoInDistribution
      (fun N (x : Fin N → S) => (A N x,DGRHS.CanonicalVariance.normalizedOffDiagonalSum (km m) x))
      atTop (Zm m) (fun N => Measure.pi (fun _ : Fin N => μ)) IsonormalProcess.iidStdGaussian := by
    intro m
    have ht := finiteParticleJointReadoutCLT (a m) (e m) (hm m) v hv b f hf
    apply ht.congr (fun N => ae_eq_refl _) 
    filter_upwards [ae_all_iff.mpr (fun i : ss m =>
      DGRHS.Gaussian.indexedGaussianIsometry_basis_ae b f hf i.val.val)] with ω hω
    change (W ω,∑ i : ss m, a m i *
      ((DGRHS.Gaussian.indexedGaussianIsometry b f hf (e m i) ω)^2-‖e m i‖^2)) = (W ω,Gm m ω)
    apply Prod.ext
    · rfl
    · change (∑ i : ss m, a m i *
        ((DGRHS.Gaussian.indexedGaussianIsometry b f hf (e m i) ω)^2-‖e m i‖^2)) =
        ∑ i ∈ ss m, eig i.val*((ω (fn i))^2-1)
      rw [← Finset.sum_coe_sort (ss m) (fun i : {i // eig i ≠ 0} => eig i.val*((ω (fn i))^2-1))]
      apply Finset.sum_congr rfl
      intro i _
      rw [hn m i]
      dsimp only [a,e,fn]
      rw [hω i]
  have ha : Summable (fun i => (eig i)^2) :=
    DGRHS.Kernel.summable_integralOperator_eigenvalue_sq h hh eig b hb
  have hQ : TendstoInDistribution Zm atTop Z
      (fun _ => IsonormalProcess.iidStdGaussian) IsonormalProcess.iidStdGaussian := by
    have hqc : DGRHS.Gaussian.centeredGaussianChaos (fun i : {i // eig i ≠ 0} => eig i.val) fn = Q :=
      DGRHS.Gaussian.centeredGaussianChaos_restrict_nonzero eig f
    have hq := DGRHS.Gaussian.tendstoInMeasure_centeredGaussianChaos
      (fun i : {i // eig i ≠ 0} => eig i.val) fn hfn (ha.subtype _) hss
    rw [hqc] at hq
    exact (tendstoInMeasure_fixed_pair (W : (ℕ → ℝ) → ℝ) hq).tendstoInDistribution
      (fun m => (Lp.memLp W).aemeasurable.prodMk
        (show Measurable (Gm m) from by dsimp [Gm]; fun_prop).aemeasurable)
  have hK := tendsto_kernel_nonzero_spectral h hh eig b hb fn hfn
  apply tendstoInDistribution_of_bounded_lipschitz _ Z
    (fun N => (hA N).aemeasurable.prodMk (memLp_normalizedOffDiagonalSum (ι := Fin N) h hh).aemeasurable)
    ((Lp.memLp W).aemeasurable.prodMk (Lp.memLp Q).aemeasurable)
  intro F hbounded L hL
  let u := fun N => ∫ x : Fin N → S, F (A N x,DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
    ∂Measure.pi (fun _ : Fin N => μ)
  let vm := fun m N => ∫ x : Fin N → S, F (A N x,DGRHS.CanonicalVariance.normalizedOffDiagonalSum (km m) x)
    ∂Measure.pi (fun _ : Fin N => μ)
  let z := ∫ ω, F (Z ω) ∂IsonormalProcess.iidStdGaussian
  let am := fun m => ∫ ω, F (Zm m ω) ∂IsonormalProcess.iidStdGaussian
  let r := fun m => (L : ℝ)*Real.sqrt 2*
    ‖hh.toLp h-∑ i ∈ ss m, eig i.val • DGRHS.Kernel.separatedLp (b i.val) (b i.val)‖
  have hr : Tendsto r atTop (𝓝 0) := by
    have ht := ((tendsto_const_nhds (x := hh.toLp h)).sub hK).norm
    simpa only [r,sub_self,norm_zero,mul_zero] using
      (tendsto_const_nhds.mul ht : Tendsto (fun m => (L : ℝ)*Real.sqrt 2*
        ‖hh.toLp h-∑ i ∈ ss m, eig i.val • DGRHS.Kernel.separatedLp (b i.val) (b i.val)‖)
        atTop (𝓝 ((L : ℝ)*Real.sqrt 2*‖hh.toLp h-hh.toLp h‖)))
  have ham : Tendsto am atTop (𝓝 z) :=
    bounded_lipschitz_integral_tendsto_of_tendstoInDistribution Zm Z hQ F hbounded L hL
  have hvm : ∀ m, Tendsto (vm m) atTop (𝓝 (am m)) := by
    intro m
    exact bounded_lipschitz_integral_tendsto_of_tendstoInDistribution _ _ (hfinite m) F hbounded L hL
  have huv : ∀ m N, dist (u N) (vm m N) ≤ r m := by
    intro m N
    have hbound := finiteSpectral_particle_joint_test_error (ι := Fin N)
      h hhm hh hs hc (a m) (e m) (hm m) (A N) (hA N).aemeasurable F L hL hbounded
    have hsum : (∑ i : ss m, a m i • DGRHS.Kernel.separatedLp (e m i) (e m i)) =
        ∑ i ∈ ss m, eig i.val • DGRHS.Kernel.separatedLp (b i.val) (b i.val) := by
      simpa only [a,e] using Finset.sum_coe_sort (ss m)
        (fun i : {i // eig i ≠ 0} => eig i.val • DGRHS.Kernel.separatedLp (b i.val) (b i.val))
    rw [hsum] at hbound
    exact hbound
  exact tendsto_of_uniform_approximation u vm am r z hr ham hvm huv
end DGRHS.CLT
#print axioms DGRHS.CLT.hilbertSchmidtParticleJointCLT
#check @DGRHS.CLT.hilbertSchmidtParticleJointCLT
