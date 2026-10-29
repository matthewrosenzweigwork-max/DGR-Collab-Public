/- Original bounded scalar tests, their actual mean centering, and all real
MGF parameters. The inverse is the genuine restriction to L2_0(mu).
Proper physical higher weight moments are still upstream obligations. -/
import DGRHS.CLT.SourceEnergyTilt
import DGRHS.Kernel.L2Centering
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.CLT
universe u
variable {S : Type u} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

lemma centeredL2_bounded (φ : Lp ℝ 2 μ) (K : ℝ) (hK : ∀ᵐ x ∂μ, |φ x| ≤ K) :
    ∀ᵐ x ∂μ, |DGRHS.Kernel.centeredL2 φ x| ≤ 2*K := by
  have hm : |∫ x,φ x ∂μ| ≤ K := by
    have ht := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => φ x) (C := K) (hK.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
    simpa [Real.norm_eq_abs] using ht
  filter_upwards [DGRHS.Kernel.centeredL2_coeFn φ,hK] with x hx hk
  rw [hx]
  exact (abs_sub _ _).trans (by linarith)

lemma particle_scaled_centeredL2_fluctuation (φ : Lp ℝ 2 μ) (t : ℝ) (N : ℕ) :
    (fun x : Fin N → S => (Real.sqrt N)⁻¹*∑ i : Fin N,(t • DGRHS.Kernel.centeredL2 φ : Lp ℝ 2 μ) (x i))
      =ᵐ[Measure.pi (fun _ : Fin N => μ)]
    fun x => t*(Real.sqrt N*((N : ℝ)⁻¹*∑ i : Fin N,φ (x i)-∫ y,φ y ∂μ)) := by
  have hs : ∀ i : Fin N, ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ),
      (t • DGRHS.Kernel.centeredL2 φ : Lp ℝ 2 μ) (x i) = t*DGRHS.Kernel.centeredL2 φ (x i) := by
    intro i
    exact (measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving.ae
      (Lp.coeFn_smul t (DGRHS.Kernel.centeredL2 φ))
  filter_upwards [ae_all_iff.mpr hs,DGRHS.Kernel.particle_centeredL2_fluctuation φ N] with x hx hf
  simp_rw [hx,←Finset.mul_sum]
  calc
    _ = t*((Real.sqrt N)⁻¹*∑ i : Fin N,DGRHS.Kernel.centeredL2 φ (x i)) := by ring
    _ = _ := by rw [hf]

theorem exists_sourceMeanZeroBoundedMGF [MeasurableSpace.CountablyGenerated S]
    (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ z ∂μ.prod μ,h z.swap = h z)
    (hc : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ) = 0)
    (hpos : ∀ v : Lp ℝ 2 μ,0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator h hh v))
    (β : ℝ) (hβ : 0 ≤ β) :
    ∃ R0 : DGRHS.Kernel.meanZeroL2 μ →L[ℝ] DGRHS.Kernel.meanZeroL2 μ,
      (∀ v,R0 v+β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hs hc (R0 v) = v) ∧
      (∀ v,R0 (v+β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hs hc v) = v) ∧
    ∀ (φ : Lp ℝ 2 μ) (K : ℝ), (∀ᵐ x ∂μ,|φ x| ≤ K) → ∀ t : ℝ,
    ∀ (F : S → ℝ),Integrable F μ → ∀ (I p C : ℝ),1 < p →
      (∀ N,Integrable (fun x : Fin N → S => Real.exp ((2*p)*sourceParticleExponent h F I β N x))
        (Measure.pi (fun _ : Fin N => μ))) →
      (∀ N,(∫ x : Fin N → S,Real.exp ((2*p)*sourceParticleExponent h F I β N x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ C) →
      (∀ N,Integrable (fun x : Fin N → S => Real.exp
        (t*(Real.sqrt N*((N : ℝ)⁻¹*∑ i : Fin N,φ (x i)-∫ y,φ y ∂μ))))
        ((Measure.pi (fun _ : Fin N => μ)).tilted
          (fun x => -β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N x))) ∧
      Tendsto (fun N => ∫ x : Fin N → S,Real.exp
        (t*(Real.sqrt N*((N : ℝ)⁻¹*∑ i : Fin N,φ (x i)-∫ y,φ y ∂μ)))
        ∂(Measure.pi (fun _ : Fin N => μ)).tilted
          (fun x => -β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N x)) atTop
        (𝓝 (Real.exp (t^2*inner ℝ (DGRHS.Kernel.sourceCenteredL2 φ)
          (R0 (DGRHS.Kernel.sourceCenteredL2 φ))/2))) := by
  obtain ⟨ι,eig,b,f,hf,hcount,hb,hmgf⟩ := exists_sourceBoundedMGF h hh hs hc hpos
  obtain ⟨R,hR1,hR2,hlimit⟩ := hmgf β hβ
  let R0 := DGRHS.Kernel.kernelResolventOnMeanZero h hh hs hc β R hR1
  have hRI := DGRHS.Kernel.kernelResolventOnMeanZero_inverse h hh hs hc β R hR1 hR2
  refine ⟨R0,hRI.1,hRI.2,fun φ K hK t F hF I p C hp hm hC => ?_⟩
  let v : Lp ℝ 2 μ := t • DGRHS.Kernel.centeredL2 φ
  have hv : (∫ x,v x ∂μ) = 0 := by
    apply (DGRHS.Kernel.mem_meanZeroL2_iff v).mp
    exact (DGRHS.Kernel.meanZeroL2 μ).smul_mem t (DGRHS.Kernel.centeredL2_mem_meanZero φ)
  have hvK : ∀ᵐ x ∂μ,|v x| ≤ |t| *(2*K) := by
    filter_upwards [Lp.coeFn_smul t (DGRHS.Kernel.centeredL2 φ),centeredL2_bounded φ K hK] with x hx hk
    change |(t • DGRHS.Kernel.centeredL2 φ : Lp ℝ 2 μ) x| ≤ _
    rw [hx,Pi.smul_apply,smul_eq_mul,abs_mul]
    exact mul_le_mul_of_nonneg_left hk (abs_nonneg t)
  obtain ⟨hi,ht⟩ := hlimit v hv (|t| *(2*K)) hvK F hF I p C hp hm hC
  have he : ∀ N,
      (fun x : Fin N → S => Real.exp ((Real.sqrt N)⁻¹*∑ i : Fin N,v (x i)))
      =ᵐ[(Measure.pi (fun _ : Fin N => μ)).tilted (sourceParticleExponent h F I β N)]
      fun x => Real.exp (t*(Real.sqrt N*((N : ℝ)⁻¹*∑ i : Fin N,φ (x i)-∫ y,φ y ∂μ))) := by
    intro N
    apply (tilted_absolutelyContinuous _ _).ae_le
    exact (particle_scaled_centeredL2_fluctuation φ t N).mono fun _ hx => congrArg Real.exp hx
  have hcoeff : inner ℝ v (R v) = t^2*inner ℝ (DGRHS.Kernel.sourceCenteredL2 φ)
      (R0 (DGRHS.Kernel.sourceCenteredL2 φ)) := by
    dsimp [v]
    rw [map_smul,real_inner_smul_left,real_inner_smul_right]
    change t*(t*inner ℝ (DGRHS.Kernel.centeredL2 φ) (R (DGRHS.Kernel.centeredL2 φ))) = _
    change t*(t*inner ℝ (DGRHS.Kernel.centeredL2 φ) (R (DGRHS.Kernel.centeredL2 φ))) =
      t^2*inner ℝ (DGRHS.Kernel.centeredL2 φ) (R (DGRHS.Kernel.centeredL2 φ))
    ring
  rw [hcoeff] at ht
  refine ⟨fun N => ?_,?_⟩
  · rw [sourceEnergyTilt_eq]
    exact (hi N).congr (he N)
  · have heInt : ∀ N,(∫ x : Fin N → S,Real.exp ((Real.sqrt N)⁻¹*∑ i : Fin N,v (x i))
        ∂(Measure.pi (fun _ : Fin N => μ)).tilted (sourceParticleExponent h F I β N)) =
        ∫ x : Fin N → S,Real.exp (t*(Real.sqrt N*((N : ℝ)⁻¹*∑ i : Fin N,φ (x i)-∫ y,φ y ∂μ)))
          ∂(Measure.pi (fun _ : Fin N => μ)).tilted (sourceParticleExponent h F I β N) :=
      fun N => integral_congr_ae (he N)
    simpa only [sourceEnergyTilt_eq,heInt] using ht
end DGRHS.CLT
#print axioms DGRHS.CLT.centeredL2_bounded
#print axioms DGRHS.CLT.particle_scaled_centeredL2_fluctuation
#print axioms DGRHS.CLT.exists_sourceMeanZeroBoundedMGF
#check @DGRHS.CLT.exists_sourceMeanZeroBoundedMGF
