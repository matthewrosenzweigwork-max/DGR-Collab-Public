import DGRHS.Commutator.SourceLogGaussianPositiveOrder
import DGRHS.Gaussian.GaussianLogShortRangeSource
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! UNCOMPILED next derivative identification. All finite orders of the actual
coefficient-one short profile are smooth off zero. Therefore the derivative of
actual physical-minus-short is the difference of the actual derivatives.
The profile matches gaussianLogTruncatedPair, not an assumed substitute. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace DGRHS.Commutator
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
-- Explicit local instances select the existing native operator-norm topologies.
-- They change neither the norm nor any imported instance declaration.
local instance sourceLogGaussianLongNative1 (n : ℕ) : AddCommMonoid (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toAddCommMonoid
local instance sourceLogGaussianLongNative2 (n : ℕ) : Module ℝ (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E [×n]→L[ℝ] ℝ)).toModule
local instance sourceLogGaussianLongNative3 (n : ℕ) : UniformSpace (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toUniformSpace
local instance sourceLogGaussianLongNative4 (n : ℕ) : TopologicalSpace (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toUniformSpace.toTopologicalSpace
local instance sourceLogGaussianLongNative5 (n : ℕ) : UniformSpace (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedAddCommGroup (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toUniformSpace
local instance sourceLogGaussianLongNative6 (n : ℕ) : TopologicalSpace (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedAddCommGroup (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toUniformSpace.toTopologicalSpace
local instance sourceLogGaussianLongNative7 (n : ℕ) : AddCommMonoid (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedAddCommGroup (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toAddCommMonoid
local instance sourceLogGaussianLongNative8 (n : ℕ) : Module ℝ (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedSpace ℝ (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toModule


lemma contDiffOn_sourceLogGaussianShortRange (η : ℝ) (hη : 0<η) (n : ℕ) :
    ContDiffOn ℝ n (DGRHS.Gaussian.gaussianLogShortRange (ι:=ι) η) {z : E | z ≠ 0} := by
  let U : Set E := {z |z≠0}
  have hU : IsOpen U := isClosed_singleton.isOpen_compl
  apply (contDiffOn_nat_iff_continuousOn_differentiableOn hU.uniqueDiffOn).mpr
  constructor
  · intro m hm z hz
    have he : (fun y : E=>iteratedFDerivWithin ℝ m (DGRHS.Gaussian.gaussianLogShortRange η) U y)
        =ᶠ[𝓝 z] (iteratedFDeriv ℝ m (DGRHS.Gaussian.gaussianLogShortRange η)) :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hz) (fun y hy=>iteratedFDerivWithin_of_isOpen m hU hy)
    exact ((continuousAt_congr he).mpr
      (continuousAt_sourceLogGaussianShortRange_iteratedFDeriv η m hη hz)).continuousWithinAt
  · intro m hm z hz
    have he : (iteratedFDeriv ℝ m (DGRHS.Gaussian.gaussianLogShortRange η)) =ᶠ[𝓝 z]
        (fun y : E=>∫ t in Ioc 0 η,t⁻¹ • iteratedFDeriv ℝ m (sourceRieszGaussianScale t) y) :=
      (eventually_ne_nhds hz).mono (fun y hy=>sourceLogShortRange_iteratedFDeriv_formula m η hη hy)
    have hg := (hasFDerivAt_sourceLogGaussian_scale_integral m η hη hz).differentiableAt.congr_of_eventuallyEq he
    have hw : (fun y : E=>iteratedFDerivWithin ℝ m (DGRHS.Gaussian.gaussianLogShortRange η) U y)
        =ᶠ[𝓝 z] (iteratedFDeriv ℝ m (DGRHS.Gaussian.gaussianLogShortRange η)) :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hz) (fun y hy=>iteratedFDerivWithin_of_isOpen m hU hy)
    exact (hg.congr_of_eventuallyEq hw).differentiableWithinAt

lemma contDiffAt_sourceLogGaussianShortRange (η : ℝ) (hη : 0<η) (n : ℕ)
    {z : E} (hz : z≠0) :
    ContDiffAt ℝ n (DGRHS.Gaussian.gaussianLogShortRange η) z := by
  exact (contDiffOn_sourceLogGaussianShortRange η hη n).contDiffAt
    (isClosed_singleton.isOpen_compl.mem_nhds hz)

def sourceLogGaussianLongRange (η : ℝ) (z : E) : ℝ :=
  sourceLogPotential z-DGRHS.Gaussian.gaussianLogShortRange η z

def sourceLogGaussianLongTransportKernel (n : ℕ) (η : ℝ) (v : E→E) (p : E×E) : ℝ := by
  classical
  exact if p.1=p.2 then 0 else
    iteratedFDeriv ℝ n (sourceLogGaussianLongRange η) (p.1-p.2) (fun _=>v p.1-v p.2)

lemma sourceLogGaussianLongTransportKernel_eq_sub (n : ℕ) (η : ℝ) (hη : 0<η)
    (v : E→E) (p : E×E) :
    sourceLogGaussianLongTransportKernel n η v p=
      sourceLogTransportKernel n v p-sourceLogGaussianShortTransportKernel n η v p := by
  classical
  by_cases hp : p.1=p.2
  · simp [sourceLogGaussianLongTransportKernel,sourceLogTransportKernel,sourceLogGaussianShortTransportKernel,hp]
  have hz : p.1-p.2≠0 := sub_ne_zero.mpr hp
  simp only [sourceLogGaussianLongTransportKernel,sourceLogTransportKernel,
    sourceLogGaussianShortTransportKernel,if_neg hp]
  change iteratedFDeriv ℝ n ((sourceLogPotential:E→ℝ)-DGRHS.Gaussian.gaussianLogShortRange η)
    (p.1-p.2) (fun _=>v p.1-v p.2)=_
  rw [iteratedFDeriv_sub_apply (contDiffAt_sourceLogPotential n hz)
    (contDiffAt_sourceLogGaussianShortRange η hη n hz)]
  rfl

lemma gaussianLogTruncatedPair_eq_sourceLogGaussianLongRange (η : ℝ) (p : E×E) :
    DGRHS.Gaussian.gaussianLogTruncatedPair η p=sourceLogGaussianLongRange η (p.1-p.2) := by
  rfl

lemma exists_sourceLogGaussianLongTransportKernel_uniform_bound (n : ℕ) (hn : 0<n) :
    ∃ C : ℝ,0<C ∧ ∀ (η : ℝ),0<η → ∀ (K : ℝ≥0) (v : E→E),LipschitzWith K v →
      ∀ p : E×E,|sourceLogGaussianLongTransportKernel n η v p|≤C*(K:ℝ)^n := by
  obtain ⟨C,hC,hb⟩ := exists_sourceLogGaussianComplementTransportKernel_uniform_bound (ι:=ι) n hn
  refine ⟨C,hC,?_⟩
  intro η hη K v hv p
  rw [sourceLogGaussianLongTransportKernel_eq_sub n η hη v p]
  exact hb η hη K v hv p

end DGRHS.Commutator
