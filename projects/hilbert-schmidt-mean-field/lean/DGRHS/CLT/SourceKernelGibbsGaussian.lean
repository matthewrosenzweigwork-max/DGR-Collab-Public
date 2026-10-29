/- Combine the actual source particle limit and Gaussian covariance using the
SAME existential basis, spectral labels and process. Physical higher moments
are explicit inputs to discharge in original physical theorems. -/
import DGRHS.CLT.SourceTiltedJointFactory
import DGRHS.Gaussian.HilbertTiltedCovariance
import DGRHS.Kernel.L2Centering
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology InnerProductSpace BigOperators
namespace DGRHS.CLT
universe u
variable {S : Type u} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

theorem exists_sourceKernelGibbsGaussian [MeasurableSpace.CountablyGenerated S]
    (m : ℕ) (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0)
    (hpos : ∀ v : Lp ℝ 2 μ, 0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator h hh v)) :
    ∃ (ι : Type u) (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
      (f : ι → ℕ) (hf : Function.Injective f),
    Countable ι ∧ (∀ i, DGRHS.Kernel.integralOperator h hh (b i) = eig i • b i) ∧
    ∀ (β : ℝ), 0 ≤ β → ∃ R0 : DGRHS.Kernel.meanZeroL2 μ →L[ℝ] DGRHS.Kernel.meanZeroL2 μ,
      (∀ v, R0 v + β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hs hc (R0 v) = v) ∧
      (∀ v, R0 (v + β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hs hc v) = v) ∧
    ∀ (v : Fin m → DGRHS.Kernel.meanZeroL2 μ) (F : S → ℝ), Integrable F μ →
      ∀ (I p C : ℝ), 1 < p →
      (∀ N, Integrable (fun x : Fin N → S => Real.exp (p*sourceParticleExponent h F I β N x))
        (Measure.pi (fun _ : Fin N => μ))) →
      (∀ N, (∫ x : Fin N → S, Real.exp (p*sourceParticleExponent h F I β N x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ C) →
      ∃ (particleProbability : ∀ N, IsProbabilityMeasure
        ((Measure.pi (fun _ : Fin N => μ)).tilted (sourceParticleExponent h F I β N)))
        (limitProbability : IsProbabilityMeasure
          (IsonormalProcess.iidStdGaussian.tilted
            (fun ω => -(β/2)*DGRHS.Gaussian.centeredGaussianChaos eig f ω))),
      letI := particleProbability
      letI := limitProbability
      TendstoInDistribution
        (fun N (x : Fin N → S) k => (Real.sqrt N)⁻¹*∑ i : Fin N, (v k : Lp ℝ 2 μ) (x i)) atTop
        (fun ω k => DGRHS.Gaussian.indexedGaussianIsometry b f hf (v k) ω)
        (fun N => (Measure.pi (fun _ : Fin N => μ)).tilted (sourceParticleExponent h F I β N))
        (IsonormalProcess.iidStdGaussian.tilted
          (fun ω => -(β/2)*DGRHS.Gaussian.centeredGaussianChaos eig f ω)) ∧
      HasGaussianLaw (fun ω k => DGRHS.Gaussian.indexedGaussianIsometry b f hf (v k) ω)
        (IsonormalProcess.iidStdGaussian.tilted
          (fun ω => -(β/2)*DGRHS.Gaussian.centeredGaussianChaos eig f ω)) ∧
      (∀ k, (∫ ω, DGRHS.Gaussian.indexedGaussianIsometry b f hf (v k) ω
        ∂IsonormalProcess.iidStdGaussian.tilted
          (fun ω => -(β/2)*DGRHS.Gaussian.centeredGaussianChaos eig f ω)) = 0) ∧
      ∀ k l, Integrable (fun ω =>
          DGRHS.Gaussian.indexedGaussianIsometry b f hf (v k) ω *
          DGRHS.Gaussian.indexedGaussianIsometry b f hf (v l) ω)
        (IsonormalProcess.iidStdGaussian.tilted
          (fun ω => -(β/2)*DGRHS.Gaussian.centeredGaussianChaos eig f ω)) ∧
        (∫ ω, DGRHS.Gaussian.indexedGaussianIsometry b f hf (v k) ω *
          DGRHS.Gaussian.indexedGaussianIsometry b f hf (v l) ω
          ∂IsonormalProcess.iidStdGaussian.tilted
            (fun ω => -(β/2)*DGRHS.Gaussian.centeredGaussianChaos eig f ω)) = inner ℝ (v k) (R0 (v l)) := by
  obtain ⟨ι,eig,b,f,hf,hcount,hb,hjoint⟩ :=
    exists_originalKernelTiltedJointCLT (j := Fin m) h hh hs hc hpos
  letI := hcount
  have hsum := DGRHS.Kernel.summable_integralOperator_eigenvalue_sq h hh eig b hb
  have heig : ∀ i, 0 ≤ eig i := by
    intro i
    have hi := hpos (b i)
    rw [hb,real_inner_smul_right,real_inner_self_eq_norm_sq,b.orthonormal.1 i,one_pow,mul_one] at hi
    exact hi
  refine ⟨ι,eig,b,f,hf,hcount,hb,fun β hβ => ?_⟩
  have hmargin : ∀ i, 0 < 1+β*eig i := fun i => by nlinarith [mul_nonneg hβ (heig i)]
  obtain ⟨R,hR1,hR2,hmap,hcov⟩ := DGRHS.Gaussian.exists_hilbert_tilted_covariance
    (DGRHS.Kernel.integralOperator h hh) (DGRHS.Kernel.integralOperator_isSymmetric h hh hs)
    b eig hb β hsum hmargin f hf
  let R0 := DGRHS.Kernel.kernelResolventOnMeanZero h hh hs hc β R hR1
  have hR0 := DGRHS.Kernel.kernelResolventOnMeanZero_inverse h hh hs hc β R hR1 hR2
  refine ⟨R0,hR0.1,hR0.2,fun v F hF I p C hp hm hC => ?_⟩
  have hv : ∀ k, (∫ x, (v k : Lp ℝ 2 μ) x ∂μ) = 0 :=
    fun k => (DGRHS.Kernel.mem_meanZeroL2_iff _).mp (v k).property
  obtain ⟨hparticle,hgaussian,hweak⟩ := hjoint (fun k => (v k : Lp ℝ 2 μ)) hv F hF I β p C hβ hp hm hC
  refine ⟨hparticle,hgaussian,?_⟩
  letI := hparticle
  letI := hgaussian
  have hproj := hweak.continuous_comp
    (g := fun z (k : Fin m) => z (Sum.inl k))
    (continuous_pi (fun k => PiLp.continuous_apply 2 (fun _ : Fin m ⊕ Unit => ℝ) (Sum.inl k)))
  refine ⟨?_,?_,?_,fun k l => hcov (v k) (v l)⟩
  · simpa [jointReadoutVector,Function.comp_def] using hproj
  · exact DGRHS.Gaussian.indexedGaussian_tuple_under_ac_gaussian_readouts
      b f hf _ (tilted_absolutelyContinuous _ _) (fun v => inner ℝ v (R v)) hmap
      (fun k => (v k : Lp ℝ 2 μ))
  · intro k
    have hl : HasLaw (DGRHS.Gaussian.indexedGaussianIsometry b f hf (v k) : (ℕ → ℝ) → ℝ)
        (gaussianReal 0 (Real.toNNReal (inner ℝ (v k : Lp ℝ 2 μ) (R (v k)))))
        (IsonormalProcess.iidStdGaussian.tilted
          (fun ω => -(β/2)*DGRHS.Gaussian.centeredGaussianChaos eig f ω)) :=
      ⟨(Lp.aestronglyMeasurable _).aemeasurable.mono_ac (tilted_absolutelyContinuous _ _),hmap (v k)⟩
    rw [hl.integral_eq,integral_id_gaussianReal]
end DGRHS.CLT
#print axioms DGRHS.CLT.exists_sourceKernelGibbsGaussian
#check @DGRHS.CLT.exists_sourceKernelGibbsGaussian
