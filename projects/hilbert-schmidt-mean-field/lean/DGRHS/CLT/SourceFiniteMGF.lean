/- Proper finite-tuple MGF from the actual bounded scalar factory and true
L2 linearity. The covariance uses one fixed genuine mean-zero resolvent. -/
import DGRHS.CLT.SourceMeanZeroBoundedMGF
import DGRHS.CLT.SourceObservableFluctuation
import DGRHS.Kernel.LinearCentering
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.CLT
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

lemma sourceFiniteCombination_fluctuation {m : ℕ} (φ : Fin m → Lp ℝ 2 μ)
    (θ : Fin m → ℝ) (N : ℕ) :
    (fun x : Fin N → S => Real.sqrt N*((N : ℝ)⁻¹*
      ∑ i : Fin N,(∑ k : Fin m,θ k • φ k : Lp ℝ 2 μ) (x i) -
        ∫ y,(∑ k : Fin m,θ k • φ k : Lp ℝ 2 μ) y ∂μ))
      =ᵐ[Measure.pi (fun _ : Fin N => μ)]
      fun x => ∑ k : Fin m,θ k*sourceObservableFluctuation φ N x k := by
  classical
  have he : ∀ i : Fin N,∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ),
      (∑ k : Fin m,θ k • φ k : Lp ℝ 2 μ) (x i) = ∑ k : Fin m,θ k*φ k (x i) :=
    fun i => (measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving.ae
      (DGRHS.Kernel.lp_finite_sum_smul_coeFn Finset.univ θ φ)
  filter_upwards [ae_all_iff.mpr he] with x hx
  rw [DGRHS.Kernel.mean_finite_sum_smul]
  simp_rw [hx]
  rw [Finset.sum_comm]
  simp_rw [←Finset.mul_sum]
  unfold sourceObservableFluctuation
  calc
    _ = ∑ k : Fin m,Real.sqrt N*((N : ℝ)⁻¹*(θ k*∑ i : Fin N,φ k (x i)) -
        θ k*(∫ y,φ k y ∂μ)) := by
      rw [Finset.mul_sum,←Finset.sum_sub_distrib,Finset.mul_sum]
    _ = _ := Finset.sum_congr rfl (fun k _ => by ring)

theorem exists_sourceFiniteMGF [MeasurableSpace.CountablyGenerated S]
    (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ z ∂μ.prod μ,h z.swap = h z)
    (hc : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ) = 0)
    (hpos : ∀ v : Lp ℝ 2 μ,0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator h hh v))
    (β : ℝ) (hβ : 0 ≤ β) :
    ∃ R0 : DGRHS.Kernel.meanZeroL2 μ →L[ℝ] DGRHS.Kernel.meanZeroL2 μ,
      (∀ v,R0 v+β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hs hc (R0 v) = v) ∧
      (∀ v,R0 (v+β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hs hc v) = v) ∧
    ∀ (m : ℕ) (φ : Fin m → Lp ℝ 2 μ) (K θ : Fin m → ℝ),
      (∀ k,∀ᵐ x ∂μ,|φ k x| ≤ K k) →
    ∀ (F : S → ℝ),Integrable F μ → ∀ (I p C : ℝ),1 < p →
      (∀ N,Integrable (fun x : Fin N → S => Real.exp ((2*p)*sourceParticleExponent h F I β N x))
        (Measure.pi (fun _ : Fin N => μ))) →
      (∀ N,(∫ x : Fin N → S,Real.exp ((2*p)*sourceParticleExponent h F I β N x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ C) →
      (∀ N,Integrable (fun x : Fin N → S => Real.exp (∑ k : Fin m,θ k*sourceObservableFluctuation φ N x k))
        ((Measure.pi (fun _ : Fin N => μ)).tilted
          (fun x => -β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N x))) ∧
      Tendsto (fun N => ∫ x : Fin N → S,Real.exp (∑ k : Fin m,θ k*sourceObservableFluctuation φ N x k)
        ∂(Measure.pi (fun _ : Fin N => μ)).tilted
          (fun x => -β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N x)) atTop
        (𝓝 (Real.exp ((∑ k : Fin m,∑ l : Fin m,θ k*θ l*
          inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
            (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l))))/2))) := by
  obtain ⟨R0,hR1,hR2,hfactory⟩ := exists_sourceMeanZeroBoundedMGF h hh hs hc hpos β hβ
  refine ⟨R0,hR1,hR2,fun m φ K θ hK F hF I p C hp hm hC => ?_⟩
  let ψ : Lp ℝ 2 μ := ∑ k : Fin m,θ k • φ k
  have hψ := DGRHS.Kernel.lp_finite_sum_smul_bounded Finset.univ θ K φ hK
  obtain ⟨hi,ht⟩ := hfactory ψ (∑ k : Fin m,|θ k| * K k) hψ 1 F hF I p C hp hm hC
  simp only [one_mul,one_pow] at hi ht
  have hcoef : inner ℝ (DGRHS.Kernel.sourceCenteredL2 ψ)
      (R0 (DGRHS.Kernel.sourceCenteredL2 ψ)) = ∑ k : Fin m,∑ l : Fin m,θ k*θ l*
        inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k)) (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l))) := by
    change inner ℝ (DGRHS.Kernel.sourceCenteredL2 ψ : Lp ℝ 2 μ)
      (R0 (DGRHS.Kernel.sourceCenteredL2 ψ) : Lp ℝ 2 μ) = ∑ k : Fin m,∑ l : Fin m,θ k*θ l*
        inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k) : Lp ℝ 2 μ)
          (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l)) : Lp ℝ 2 μ)
    exact DGRHS.Kernel.centered_covariance_finite_sum Finset.univ θ φ R0
  rw [hcoef] at ht
  have he : ∀ N,(fun x : Fin N → S => Real.exp (Real.sqrt N*((N : ℝ)⁻¹*∑ i : Fin N,ψ (x i)-∫ y,ψ y ∂μ)))
      =ᵐ[(Measure.pi (fun _ : Fin N => μ)).tilted
        (fun x => -β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N x)]
      fun x => Real.exp (∑ k : Fin m,θ k*sourceObservableFluctuation φ N x k) := by
    intro N
    exact (tilted_absolutelyContinuous _ _).ae_le
      ((sourceFiniteCombination_fluctuation φ θ N).mono fun _ hx => congrArg Real.exp hx)
  refine ⟨fun N => (hi N).congr (he N),?_⟩
  exact ht.congr' (Filter.Eventually.of_forall (fun N => integral_congr_ae (he N)))
end DGRHS.CLT
#print axioms DGRHS.CLT.sourceFiniteCombination_fluctuation
#print axioms DGRHS.CLT.exists_sourceFiniteMGF
#check @DGRHS.CLT.exists_sourceFiniteMGF
