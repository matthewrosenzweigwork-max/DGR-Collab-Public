/- Actual normalized source-kernel Gibbs joint limit from the true kernel
factory. Proper particle moments are explicit physical obligations; the limit
Gaussian integrability, spectrum and constant cancellation are derived here. -/
import DGRHS.CLT.SourceExponentCLT
import DGRHS.CLT.ExponentialTiltLaw
import DGRHS.CLT.ConstantTilt
import DGRHS.Kernel.SpectralHilbertSchmidt
import DGRHS.Gaussian.WeakMarginChaosLaplace
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.CLT
universe u
variable {S : Type u} [MeasurableSpace S] {j : Type*} [Fintype j]
  {μ : Measure S} [IsProbabilityMeasure μ]

def sourceParticleExponent (h : S × S → ℝ) (F : S → ℝ) (I β : ℝ)
    (N : ℕ) (x : Fin N → S) : ℝ :=
  -β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x +
    β*((N : ℝ)⁻¹*∑ i : Fin N, F (x i))-β*I

theorem exists_originalKernelTiltedJointCLT [MeasurableSpace.CountablyGenerated S]
    (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y,h (x,y) ∂μ) = 0)
    (hpos : ∀ v : Lp ℝ 2 μ, 0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator h hh v)) :
    ∃ (ι : Type u) (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
      (f : ι → ℕ) (hf : Function.Injective f),
      Countable ι ∧
      (∀ i, DGRHS.Kernel.integralOperator h hh (b i) = eig i • b i) ∧
      ∀ (v : j → Lp ℝ 2 μ), (∀ l, (∫ x,v l x ∂μ) = 0) →
      ∀ (F : S → ℝ), Integrable F μ → ∀ (I β p C : ℝ), 0 ≤ β → 1 < p →
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
        (fun N (x : Fin N → S) => jointReadoutVector
          (fun l => (Real.sqrt N)⁻¹*∑ i : Fin N, v l (x i))
          (DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) atTop
        (fun ω => jointReadoutVector
          (fun l => DGRHS.Gaussian.indexedGaussianIsometry b f hf (v l) ω)
          (DGRHS.Gaussian.centeredGaussianChaos eig f ω))
        (fun N => (Measure.pi (fun _ : Fin N => μ)).tilted (sourceParticleExponent h F I β N))
        (IsonormalProcess.iidStdGaussian.tilted
          (fun ω => -(β/2)*DGRHS.Gaussian.centeredGaussianChaos eig f ω)) := by
  obtain ⟨ι,eig,b,f,hf,hcount,hb,hlimit⟩ := exists_originalKernelSourceExponentCLT (j := j) h hh hs hc
  letI := hcount
  have hsum := DGRHS.Kernel.summable_integralOperator_eigenvalue_sq h hh eig b hb
  have heig : ∀ i, 0 ≤ eig i := by
    intro i
    have hi := hpos (b i)
    rw [hb,real_inner_smul_right,real_inner_self_eq_norm_sq,b.orthonormal.1 i,one_pow,mul_one] at hi
    exact hi
  refine ⟨ι,eig,b,f,hf,hcount,hb,fun v hv F hi I β p C hβ hp hm hC => ?_⟩
  let X := fun N (x : Fin N → S) =>
    (jointReadoutVector (fun l => (Real.sqrt N)⁻¹*∑ i : Fin N,v l (x i))
      (DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x),sourceParticleExponent h F I β N x)
  let Y := fun ω => -(β/2)*DGRHS.Gaussian.centeredGaussianChaos eig f ω
  let c := β*(∫ x,F x ∂μ)-β*I
  let Z := fun ω =>
    (jointReadoutVector (fun l => DGRHS.Gaussian.indexedGaussianIsometry b f hf (v l) ω)
      (DGRHS.Gaussian.centeredGaussianChaos eig f ω),Y ω+c)
  have hweak : TendstoInDistribution X atTop Z
      (fun N => Measure.pi (fun _ : Fin N => μ)) IsonormalProcess.iidStdGaussian := by
    convert hlimit v hv F hi β I using 1 <;> funext ω <;> dsimp [X,Z,Y,c,sourceParticleExponent] <;> congr 1 <;> ring
  have hmargin : ∀ i, 0 < 1+β*eig i := fun i => by nlinarith [mul_nonneg hβ (heig i)]
  have hY : Integrable (fun ω => Real.exp (Y ω)) IsonormalProcess.iidStdGaussian :=
    (DGRHS.Gaussian.integral_exp_signed_centeredGaussianChaos_weak_margin β eig hmargin hsum f hf).1
  have hZ := integrable_exp_add_const Y hY c
  have hmX : ∀ N, Integrable (fun x => Real.exp (p*(X N x).2))
      (Measure.pi (fun _ : Fin N => μ)) := hm
  have hiX : ∀ N, Integrable (fun x => Real.exp ((X N x).2))
      (Measure.pi (fun _ : Fin N => μ)) := fun N =>
    integrable_exp_of_higher_exp ((continuous_snd.measurable).comp_aemeasurable
      (hweak.forall_aemeasurable N)) hp.le (hmX N)
  have hparticle : ∀ N, IsProbabilityMeasure
      ((Measure.pi (fun _ : Fin N => μ)).tilted (sourceParticleExponent h F I β N)) :=
    fun N => isProbabilityMeasure_tilted (hiX N)
  have hgaussian : IsProbabilityMeasure (IsonormalProcess.iidStdGaussian.tilted Y) :=
    isProbabilityMeasure_tilted hY
  refine ⟨hparticle,hgaussian,?_⟩
  letI : ∀ N, IsProbabilityMeasure
      (exponentialTiltMeasure (Measure.pi (fun _ : Fin N => μ)) (fun x => (X N x).2)) :=
    fun N => exponentialTiltMeasure_probability _ (hiX N)
  letI : IsProbabilityMeasure
      (exponentialTiltMeasure IsonormalProcess.iidStdGaussian (fun ω => Y ω+c)) :=
    exponentialTiltMeasure_probability _ hZ
  letI : IsProbabilityMeasure (exponentialTiltMeasure IsonormalProcess.iidStdGaussian Y) :=
    exponentialTiltMeasure_probability _ hY
  have ht := exponentialTilt_tendstoInDistribution X Z hweak Prod.snd continuous_snd
    hiX hZ p C hp hmX hC
  have hproj := ht.continuous_comp (g := Prod.fst) continuous_fst
  change TendstoInDistribution (fun N x => (X N x).1) atTop (fun ω => (Z ω).1)
    (fun N => exponentialTiltMeasure (Measure.pi (fun _ : Fin N => μ)) (fun x => (X N x).2))
    (exponentialTiltMeasure IsonormalProcess.iidStdGaussian (fun ω => Y ω+c)) at hproj
  simpa only [exponentialTiltMeasure_add_const Y hY c,exponentialTiltMeasure_eq_native,
    X,Z,Y] using hproj
end DGRHS.CLT
#print axioms DGRHS.CLT.exists_originalKernelTiltedJointCLT
#check @DGRHS.CLT.exists_originalKernelTiltedJointCLT
