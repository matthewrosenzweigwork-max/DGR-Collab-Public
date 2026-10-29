/- Actual true-kernel partition limit and determinant normalization.
Higher particle exponential moments remain actual physical inputs to discharge.
The spectrum, untilted exponent CLT and proper Gaussian normalization are derived. -/
import DGRHS.CLT.SourceTiltedJointFactory
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.CLT
universe u
variable {S : Type u} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

theorem exists_originalKernelPartitionLimit [MeasurableSpace.CountablyGenerated S]
    (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y,h (x,y) ∂μ) = 0)
    (hpos : ∀ v : Lp ℝ 2 μ, 0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator h hh v)) :
    ∃ (ι : Type u) (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
      (f : ι → ℕ) (hf : Function.Injective f),
      Countable ι ∧
      (∀ i, DGRHS.Kernel.integralOperator h hh (b i) = eig i • b i) ∧
      ∀ (F : S → ℝ), Integrable F μ → ∀ (I β p C : ℝ), 0 ≤ β → 1 < p →
      (∀ N, Integrable (fun x : Fin N → S => Real.exp (p*sourceParticleExponent h F I β N x))
        (Measure.pi (fun _ : Fin N => μ))) →
      (∀ N, (∫ x : Fin N → S,Real.exp (p*sourceParticleExponent h F I β N x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ C) →
      Tendsto (fun N => ∫ x : Fin N → S,Real.exp (sourceParticleExponent h F I β N x)
        ∂Measure.pi (fun _ : Fin N => μ)) atTop
        (𝓝 (Real.exp (β*(∫ x,F x ∂μ)-β*I)*
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β*eig i)))⁻¹)) := by
  obtain ⟨ι,eig,b,f,hf,hcount,hb,hlimit⟩ :=
    exists_originalKernelSourceExponentCLT (j := Fin 0) h hh hs hc
  letI := hcount
  have hsum := DGRHS.Kernel.summable_integralOperator_eigenvalue_sq h hh eig b hb
  have heig : ∀ i, 0 ≤ eig i := by
    intro i
    have hi := hpos (b i)
    rw [hb,real_inner_smul_right,real_inner_self_eq_norm_sq,b.orthonormal.1 i,one_pow,mul_one] at hi
    exact hi
  refine ⟨ι,eig,b,f,hf,hcount,hb,fun F hi I β p C hβ hp hm hC => ?_⟩
  let Y := fun ω => -(β/2)*DGRHS.Gaussian.centeredGaussianChaos eig f ω
  let c := β*(∫ x,F x ∂μ)-β*I
  have hweak : TendstoInDistribution (fun N => sourceParticleExponent h F I β N) atTop
      (fun ω => Y ω+c) (fun N => Measure.pi (fun _ : Fin N => μ)) IsonormalProcess.iidStdGaussian := by
    have hl := hlimit (fun _ : Fin 0 => (0 : Lp ℝ 2 μ))
      (fun l => Fin.elim0 l) F hi β I
    convert hl.continuous_comp (g := Prod.snd) continuous_snd using 1
    · rfl
    · funext ω
      dsimp [Y,c]
      ring
  have hmargin : ∀ i, 0 < 1+β*eig i := fun i => by nlinarith [mul_nonneg hβ (heig i)]
  obtain ⟨hY,hvalue⟩ := DGRHS.Gaussian.integral_exp_signed_centeredGaussianChaos_weak_margin
    β eig hmargin hsum f hf
  have hZ := integrable_exp_add_const Y hY c
  have ht := exponential_integral_tendsto_of_distribution_moment
    (fun N => sourceParticleExponent h F I β N) (fun ω => Y ω+c) hweak hZ p C hp hm hC
  have he : (∫ ω,Real.exp (Y ω+c) ∂IsonormalProcess.iidStdGaussian) =
      Real.exp c*(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β*eig i)))⁻¹ := by
    rw [integral_exp_add_const Y c]
    exact congrArg (fun a => Real.exp c*a) hvalue
  rw [he] at ht
  exact ht
end DGRHS.CLT
#print axioms DGRHS.CLT.exists_originalKernelPartitionLimit
#check @DGRHS.CLT.exists_originalKernelPartitionLimit
