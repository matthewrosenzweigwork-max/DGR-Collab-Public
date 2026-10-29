/- Time measurability of the ACTUAL logarithmic commutator.
Native measurable probability kernels handle the moving reference law;
finite sums and original physical raw expansion handle every configuration. -/
import DGRHS.Commutator.SourceLogTransportAllLaws
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.Prod
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal RealInnerProductSpace
namespace DGRHS.Dynamics
open DGRHS.Commutator
variable {τ Ω E : Type*} [MeasurableSpace τ] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem measurable_sourceLogTransportKernel_time (v : τ→E→E)
    (hv : Measurable (Function.uncurry v)) :
    Measurable (fun p : τ×(E×E)=>sourceLogTransportKernel 1 (v p.1) p.2) := by
  have hz : Measurable (fun p : τ×(E×E)=>p.2.1-p.2.2) := measurable_snd.fst.sub measurable_snd.snd
  have h1 : Measurable (fun p : τ×(E×E)=>v p.1 p.2.1) := hv.comp (measurable_fst.prodMk measurable_snd.fst)
  have h2 : Measurable (fun p : τ×(E×E)=>v p.1 p.2.2) := hv.comp (measurable_fst.prodMk measurable_snd.snd)
  simp_rw [sourceLogTransportKernel_one]
  exact (hz.inner (h1.sub h2)).neg.div (hz.norm.pow_const 2)

theorem measurable_sourceLogTransportPotential_time (κ : Kernel τ E) [IsSFiniteKernel κ]
    (v : τ→E→E) (hv : Measurable (Function.uncurry v)) :
    Measurable (fun p : τ×E=>∫ y,sourceLogTransportKernel 1 (v p.1) (p.2,y) ∂κ p.1) := by
  have hk := measurable_sourceLogTransportKernel_time v hv
  have hf := hk.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hp := hf.stronglyMeasurable.integral_kernel_prod_right'
    (κ:=κ.comap Prod.fst measurable_fst)
  exact hp.measurable

theorem measurable_sourceLogTransportEnergy_time (κ : Kernel τ E) [IsSFiniteKernel κ]
    (v : τ→E→E) (hv : Measurable (Function.uncurry v))
    (N : ℕ) (hN : 0<N) (X : τ×Ω→Fin N→E) (hX : Measurable X) :
    Measurable (fun p : τ×Ω=>sourceTransportEnergy (κ p.1)
      (sourceLogTransportKernel 1 (v p.1)) N (X p)) := by
  classical
  have hk := measurable_sourceLogTransportKernel_time v hv
  have hp := measurable_sourceLogTransportPotential_time κ v hv
  have hI : Measurable (fun r=>∫ z,sourceLogTransportKernel 1 (v r) z ∂(κ r).prod (κ r)) := by
    have ht := hk.stronglyMeasurable.integral_kernel_prod_right' (κ:=κ.prod κ)
    simpa only [Kernel.prod_apply] using ht.measurable
  have hsum : Measurable (fun p : τ×Ω=>DGRHS.CanonicalVariance.offDiagonalSum
      (sourceLogTransportKernel 1 (v p.1)) (X p)) := by
    unfold DGRHS.CanonicalVariance.offDiagonalSum
    exact Finset.measurable_sum _ (fun ij _=>hk.comp (measurable_fst.prodMk
      (((measurable_pi_apply ij.1).comp hX).prodMk ((measurable_pi_apply ij.2).comp hX))))
  have hpSum : Measurable (fun p : τ×Ω=>∑ i : Fin N,
      ∫ y,sourceLogTransportKernel 1 (v p.1) (X p i,y) ∂κ p.1) :=
    Finset.measurable_sum _ (fun i _=>hp.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp hX)))
  have heq : (fun p : τ×Ω=>sourceTransportEnergy (κ p.1)
      (sourceLogTransportKernel 1 (v p.1)) N (X p))=
      (fun p=>((N:ℝ)^2)⁻¹*DGRHS.CanonicalVariance.offDiagonalSum
        (sourceLogTransportKernel 1 (v p.1)) (X p)-
        2*(N:ℝ)⁻¹*(∑ i : Fin N,∫ y,sourceLogTransportKernel 1 (v p.1) (X p i,y) ∂κ p.1)+
        (∫ z,sourceLogTransportKernel 1 (v p.1) z ∂(κ p.1).prod (κ p.1))) := by
    funext p
    exact sourceTransportEnergy_raw (κ p.1) _
      (fun a b=>(sourceLogTransportKernel_swap 1 (v p.1) (a,b)).symm) N hN (X p)
  rw [heq]
  exact ((hsum.const_mul _).sub (hpSum.const_mul _)).add (hI.comp measurable_fst)
end DGRHS.Dynamics
#check @DGRHS.Dynamics.measurable_sourceLogTransportKernel_time
#check @DGRHS.Dynamics.measurable_sourceLogTransportPotential_time
#check @DGRHS.Dynamics.measurable_sourceLogTransportEnergy_time
#print axioms DGRHS.Dynamics.measurable_sourceLogTransportKernel_time
#print axioms DGRHS.Dynamics.measurable_sourceLogTransportPotential_time
#print axioms DGRHS.Dynamics.measurable_sourceLogTransportEnergy_time
