/- Source centered L2 space and restriction of the SAME actual kernel operator.
Constants are removed by a genuine continuous linear functional, not a new
assumption on every basis mode. Constructed resolvents preserve this space. -/
import DGRHS.Kernel.Spectrum
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace DGRHS.Kernel
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

def meanZeroL2 (μ : Measure S) [IsProbabilityMeasure μ] : Submodule ℝ (Lp ℝ 2 μ) :=
  (innerSL ℝ (oneL2 (μ := μ))).ker

lemma mem_meanZeroL2_iff (v : Lp ℝ 2 μ) :
    v ∈ meanZeroL2 μ ↔ (∫ x, v x ∂μ) = 0 := by
  change inner ℝ (oneL2 (μ := μ)) v = 0 ↔ _
  rw [inner_oneL2_eq_integral]

lemma integralOperator_mem_meanZeroL2 (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y,h (x,y) ∂μ) = 0) (v : Lp ℝ 2 μ) :
    integralOperator h hh v ∈ meanZeroL2 μ :=
  inner_one_integralOperator_eq_zero h hh hs hc v

def integralOperatorOnMeanZero (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y,h (x,y) ∂μ) = 0) :
    meanZeroL2 μ →L[ℝ] meanZeroL2 μ :=
  ((integralOperator h hh).domRestrict (meanZeroL2 μ)).codRestrict (meanZeroL2 μ)
    (fun v => integralOperator_mem_meanZeroL2 h hh hs hc v)

lemma kernel_resolvent_preserves_mean (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y,h (x,y) ∂μ) = 0)
    (β : ℝ) (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hR : ∀ v, R v + β • integralOperator h hh (R v) = v) (v : Lp ℝ 2 μ) :
    inner ℝ (oneL2 (μ := μ)) (R v) = inner ℝ (oneL2 (μ := μ)) v := by
  have he := congrArg (fun z => inner ℝ (oneL2 (μ := μ)) z) (hR v)
  simpa only [inner_add_right,real_inner_smul_right,
    inner_one_integralOperator_eq_zero h hh hs hc,mul_zero,add_zero] using he

lemma kernel_resolvent_mem_meanZeroL2 (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y,h (x,y) ∂μ) = 0)
    (β : ℝ) (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hR : ∀ v, R v + β • integralOperator h hh (R v) = v)
    (v : meanZeroL2 μ) : R v ∈ meanZeroL2 μ := by
  change inner ℝ (oneL2 (μ := μ)) (R v) = 0
  exact (kernel_resolvent_preserves_mean h hh hs hc β R hR v).trans v.property

def kernelResolventOnMeanZero (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y,h (x,y) ∂μ) = 0)
    (β : ℝ) (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hR : ∀ v, R v + β • integralOperator h hh (R v) = v) :
    meanZeroL2 μ →L[ℝ] meanZeroL2 μ :=
  (R.domRestrict (meanZeroL2 μ)).codRestrict (meanZeroL2 μ)
    (kernel_resolvent_mem_meanZeroL2 h hh hs hc β R hR)

lemma kernelResolventOnMeanZero_inverse (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y,h (x,y) ∂μ) = 0)
    (β : ℝ) (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hR : ∀ v, R v + β • integralOperator h hh (R v) = v)
    (hR' : ∀ v, R (v + β • integralOperator h hh v) = v) :
    (∀ v, kernelResolventOnMeanZero h hh hs hc β R hR v +
      β • integralOperatorOnMeanZero h hh hs hc
        (kernelResolventOnMeanZero h hh hs hc β R hR v) = v) ∧
    ∀ v, kernelResolventOnMeanZero h hh hs hc β R hR
      (v + β • integralOperatorOnMeanZero h hh hs hc v) = v := by
  constructor
  · intro v
    apply Subtype.ext
    exact hR v
  · intro v
    apply Subtype.ext
    exact hR' v
end DGRHS.Kernel
#print axioms DGRHS.Kernel.inner_oneL2_eq_integral
#print axioms DGRHS.Kernel.mem_meanZeroL2_iff
#print axioms DGRHS.Kernel.integralOperator_mem_meanZeroL2
#print axioms DGRHS.Kernel.kernel_resolvent_preserves_mean
#print axioms DGRHS.Kernel.kernelResolventOnMeanZero_inverse
#check @DGRHS.Kernel.kernelResolventOnMeanZero_inverse
