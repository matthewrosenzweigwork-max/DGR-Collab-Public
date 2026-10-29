/- Outside proof until exact upstream A8 semantic review and integration.
Source2490–2595: full original generic uniform partition from its row hypothesis.
No desired canonical moment or weight is supplied. -/
import DGRHS.Attractive.CanonicalExponential
import DGRHS.Attractive.SourceOneBody
import DGRHS.CLT.IidCanonicalNormalization
import DGRHS.Gaussian.HoeffdingLinearity
import DGRHS.Gaussian.SingularLogIntegrability
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace DGRHS.Attractive
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

theorem source_uniform_partition (W : S → S → ℝ)
    (hWm : StronglyMeasurable (Function.uncurry W))
    (hWi : Integrable (Function.uncurry W) (μ.prod μ))
    (hWs : ∀ x y,W x y = W y x) (C β : ℝ)
    (hrow : RowFactorialMoments μ
      (fun p => DGRHS.centeredKernel μ W p.1 p.2) C)
    (hβ : 0 ≤ β) (hsmall : β*(attractiveMomentConstant*C)<1)
    (htail : Integrable (fun x => Real.exp (2*β*DGRHS.potential μ W x)) μ)
    (N : ℕ) (hN : 0 < N) :
    Integrable (fun x : Fin N → S => Real.exp (-β*(N : ℝ)*
      DGRHS.CLT.sourceCanonicalModulatedEnergy
        (fun p => DGRHS.centeredKernel μ W p.1 p.2)
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x))
      (Measure.pi (fun _ : Fin N => μ)) ∧
    (∫ x : Fin N → S,Real.exp (-β*(N : ℝ)*
      DGRHS.CLT.sourceCanonicalModulatedEnergy
        (fun p => DGRHS.centeredKernel μ W p.1 p.2)
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x)
      ∂Measure.pi (fun _ : Fin N => μ)) ≤
      Real.exp (β*|DGRHS.interactionEnergy μ W|)*
        Real.sqrt (2/(1-(β*(attractiveMomentConstant*C))^2))*
        Real.sqrt (∫ x,Real.exp (2*β*DGRHS.potential μ W x) ∂μ) := by
  let h : S × S → ℝ := fun p => DGRHS.centeredKernel μ W p.1 p.2
  have hm : Measurable h :=
    (DGRHS.Gaussian.stronglyMeasurable_hoeffdingCentered μ
      (Function.uncurry W) hWm).measurable
  have hs : ∀ x y,h (x,y)=h (y,x) := DGRHS.centeredKernel_symmetric μ W hWs
  have hc : ∀ᵐ y ∂μ,∫ x,h (x,y) ∂μ = 0 :=
    DGRHS.integral_centeredKernel_left μ W hWi
  obtain ⟨hip,hbp⟩ := attractiveCanonical_uniform_exponential μ h hm C hrow hs hc β
    (by simpa only [abs_of_nonneg hβ] using hsmall) N
  have he : (fun x : Fin N → S => Real.exp (β*attractiveNormalizedStatistic N h x)) =
      fun x => Real.exp (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x) := by
    funext x
    congr 1
    rw [←DGRHS.CLT.sourceStatistic_eq_normalized]
    unfold attractiveNormalizedStatistic DGRHS.Gaussian.sourceKernelParticleStatistic
      DGRHS.Decoupling.offDiagonalSum
    simp only [ne_eq,ite_not]
    ring
  rw [he] at hip hbp
  obtain ⟨hi,hb⟩ := source_one_body_reduction h (DGRHS.potential μ W)
    (DGRHS.integrable_potential μ W hWi) (DGRHS.interactionEnergy μ W) β hβ htail N hN hip
  have hweight : (fun x : Fin N → S => Real.exp (-β*(N : ℝ)*
      DGRHS.CLT.sourceCanonicalModulatedEnergy h
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x)) =
      (fun x => Real.exp (DGRHS.CLT.sourceParticleExponent h
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) β N x)) := by
    funext x
    congr 1
    exact DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent h
      (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) β hN x
  rw [hweight]
  refine ⟨hi,hb.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbp) (Real.exp_pos _).le)
    (Real.sqrt_nonneg _)

end DGRHS.Attractive
#check @DGRHS.Attractive.source_uniform_partition
#print axioms DGRHS.Attractive.source_uniform_partition
