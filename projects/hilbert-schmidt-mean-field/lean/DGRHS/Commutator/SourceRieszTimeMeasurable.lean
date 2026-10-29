import DGRHS.Commutator.SourceRieszDynamicForceEmpirical
import DGRHS.Dynamics.SourceDensityKernel
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.Prod

/-! Native measurable SFinite kernels give joint measurability of the actual
singular Riesz commutator. No global probability, boundedness or Lipschitz
hypothesis is needed: the actual n1 force formula handles measurability.
Adaptation reference root SourceLogTimeMeasurable; no LOG proof imports. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal RealInnerProductSpace
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Dynamics
variable {τ Ω : Type*} [MeasurableSpace τ] [MeasurableSpace Ω]
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

 theorem measurable_sourceRieszTransportKernel_time (s : ℝ) (hs : 0<s)
    (v : τ→E→E) (hv : Measurable (Function.uncurry v)) :
    Measurable (fun p : τ×(E×E)=>sourceRieszTransportKernel 1 s (v p.1) p.2) := by
  have hz : Measurable (fun p : τ×(E×E)=>p.2.1-p.2.2) := measurable_snd.fst.sub measurable_snd.snd
  have h1 : Measurable (fun p : τ×(E×E)=>v p.1 p.2.1) := hv.comp (measurable_fst.prodMk measurable_snd.fst)
  have h2 : Measurable (fun p : τ×(E×E)=>v p.1 p.2.2) := hv.comp (measurable_fst.prodMk measurable_snd.snd)
  have he : (fun p : τ×(E×E)=>sourceRieszTransportKernel 1 s (v p.1) p.2)=
      (fun p=>⟪sourceRieszForce s (p.2.1-p.2.2),v p.1 p.2.1-v p.1 p.2.2⟫) :=
    funext fun p=>sourceRieszTransportKernel_force s hs (v p.1) p.2.1 p.2.2
  rw [he]
  exact ((measurable_sourceRieszForce s).comp hz).inner (h1.sub h2)

 theorem measurable_sourceRieszTransportPotential_time (s : ℝ) (hs : 0<s)
    (κ : Kernel τ E) [IsSFiniteKernel κ] (v : τ→E→E)
    (hv : Measurable (Function.uncurry v)) :
    Measurable (fun p : τ×E=>∫ y,sourceRieszTransportKernel 1 s (v p.1) (p.2,y) ∂κ p.1) := by
  have hk := measurable_sourceRieszTransportKernel_time s hs v hv
  have hf := hk.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  exact (hf.stronglyMeasurable.integral_kernel_prod_right'
    (κ:=κ.comap Prod.fst measurable_fst)).measurable

 theorem measurable_sourceRieszTransportEnergy_time (s : ℝ) (hs : 0<s)
    (ρ : τ→E→ℝ) (hρ : Measurable (Function.uncurry ρ))
    (v : τ→E→E) (hv : Measurable (Function.uncurry v))
    (N : ℕ) (hN : 0<N) (X : τ×Ω→Fin N→E) (hX : Measurable X) :
    Measurable (fun p : τ×Ω=>sourceRieszLocalTransportEnergy (ρ p.1) s 1 (v p.1) N (X p)) := by
  classical
  let κ := sourceDensityKernel volume ρ
  letI := sourceDensityKernel_sfinite volume ρ
  have hκ (r : τ) : κ r=gaussianRieszDensityMeasure (ρ r) := sourceDensityKernel_apply volume ρ hρ r
  have hk := measurable_sourceRieszTransportKernel_time s hs v hv
  have hp := measurable_sourceRieszTransportPotential_time s hs κ v hv
  have hI : Measurable (fun r=>∫ z,sourceRieszTransportKernel 1 s (v r) z ∂(κ r).prod (κ r)) := by
    have ht := hk.stronglyMeasurable.integral_kernel_prod_right' (κ:=κ.prod κ)
    simpa only [Kernel.prod_apply] using ht.measurable
  have hsum : Measurable (fun p : τ×Ω=>DGRHS.CanonicalVariance.offDiagonalSum
      (sourceRieszTransportKernel 1 s (v p.1)) (X p)) := by
    unfold DGRHS.CanonicalVariance.offDiagonalSum
    exact Finset.measurable_sum _ (fun ij _=>hk.comp (measurable_fst.prodMk
      (((measurable_pi_apply ij.1).comp hX).prodMk ((measurable_pi_apply ij.2).comp hX))))
  have hpSum : Measurable (fun p : τ×Ω=>∑ i : Fin N,
      ∫ y,sourceRieszTransportKernel 1 s (v p.1) (X p i,y) ∂κ p.1) :=
    Finset.measurable_sum _ (fun i _=>hp.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp hX)))
  have heq : (fun p : τ×Ω=>sourceRieszLocalTransportEnergy (ρ p.1) s 1 (v p.1) N (X p))=
      (fun p=>((N:ℝ)^2)⁻¹*DGRHS.CanonicalVariance.offDiagonalSum
        (sourceRieszTransportKernel 1 s (v p.1)) (X p)-
        2*(N:ℝ)⁻¹*(∑ i : Fin N,∫ y,sourceRieszTransportKernel 1 s (v p.1) (X p i,y) ∂κ p.1)+
        (∫ z,sourceRieszTransportKernel 1 s (v p.1) z ∂(κ p.1).prod (κ p.1))) := by
    funext p
    simpa only [hκ] using sourceRieszLocalTransportEnergy_raw (ρ p.1) s 1 (v p.1) N hN (X p)
  rw [heq]
  exact ((hsum.const_mul _).sub (hpSum.const_mul _)).add (hI.comp measurable_fst)

end DGRHS.Commutator
#check @DGRHS.Commutator.measurable_sourceRieszTransportKernel_time
#print axioms DGRHS.Commutator.measurable_sourceRieszTransportKernel_time
#check @DGRHS.Commutator.measurable_sourceRieszTransportPotential_time
#print axioms DGRHS.Commutator.measurable_sourceRieszTransportPotential_time
#check @DGRHS.Commutator.measurable_sourceRieszTransportEnergy_time
#print axioms DGRHS.Commutator.measurable_sourceRieszTransportEnergy_time
