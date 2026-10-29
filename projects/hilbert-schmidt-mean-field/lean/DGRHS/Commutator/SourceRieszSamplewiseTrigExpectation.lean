import DGRHS.Commutator.SourceRieszBrownianPhaseCoefficients
import DGRHS.Commutator.SourceRieszFinitePhase

/-! Proper expectation of the two primitive samplewise trigonometric Ito
identities. The stochastic terms here are explicit inputs with integrability
and zero expectation; the concrete Brownian consumer discharges those facts.
No expected phase identity or characteristic factorization is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator

lemma sourceRieszFinitePhase_re (x : ℝ) : (sourceRieszFinitePhase x).re=Real.cos x := by
  rw [sourceRieszFinitePhase,mul_comm,Complex.exp_ofReal_mul_I_re]

lemma sourceRieszFinitePhase_im (x : ℝ) : (sourceRieszFinitePhase x).im=Real.sin x := by
  rw [sourceRieszFinitePhase,mul_comm,Complex.exp_ofReal_mul_I_im]

lemma integrable_sourceRieszFinitePhase {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : Ω→ℝ) (hA : Measurable A) :
    Integrable (fun ω=>sourceRieszFinitePhase (A ω)) P := by
  apply (integrable_const (1:ℝ)).mono'
    (measurable_sourceRieszFinitePhase.comp hA).aestronglyMeasurable
  exact ae_of_all _ (fun ω=>(norm_sourceRieszFinitePhase _).le)

theorem sourceRiesz_samplewise_trig_expected_phase
    {Ω τ : Type*} [MeasurableSpace Ω] [MeasurableSpace τ]
    (P : Measure Ω) [IsProbabilityMeasure P] (η : Measure τ) [SFinite η]
    (A Y : Ω→ℝ) (hA : Measurable A) (hY : Measurable Y)
    (R H : τ→Ω→ℝ) (hR : Measurable (Function.uncurry R))
    (hH : Measurable (Function.uncurry H)) (hiH : Integrable (Function.uncurry H) (η.prod P))
    (Ns Nc : Ω→ℝ) (hiNs : Integrable Ns P) (hiNc : Integrable Nc P)
    (hNs : (∫ ω,Ns ω ∂P)=0) (hNc : (∫ ω,Nc ω ∂P)=0) (q : ℝ)
    (hcos : ∀ᵐ ω ∂P,Real.cos (Y ω)=Real.cos (A ω)-Ns ω-
      q*(∫ r,Real.cos (R r ω)*H r ω ∂η))
    (hsin : ∀ᵐ ω ∂P,Real.sin (Y ω)=Real.sin (A ω)+Nc ω-
      q*(∫ r,Real.sin (R r ω)*H r ω ∂η)) :
    (∫ ω,sourceRieszFinitePhase (Y ω) ∂P)=
      (∫ ω,sourceRieszFinitePhase (A ω) ∂P)-
        q • (∫ r,∫ ω,sourceRieszFinitePhase (R r ω)*(H r ω:ℂ) ∂P ∂η) := by
  let Z := fun p:τ×Ω=>sourceRieszFinitePhase (R p.1 p.2)*(H p.1 p.2:ℂ)
  have hiZ : Integrable Z (η.prod P) := by
    apply hiH.abs.mono'
      ((measurable_sourceRieszFinitePhase.comp hR).mul
        (Complex.continuous_ofReal.measurable.comp hH)).aestronglyMeasurable
    exact ae_of_all _ (fun p=>by
      change ‖sourceRieszFinitePhase (R p.1 p.2)*(H p.1 p.2:ℂ)‖≤|H p.1 p.2|
      simp only [norm_mul,norm_sourceRieszFinitePhase,one_mul,Complex.norm_real,Real.norm_eq_abs]
      exact le_rfl)
  have hre (p : τ×Ω) : (Z p).re=Real.cos (R p.1 p.2)*H p.1 p.2 := by
    simp only [Z,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,sourceRieszFinitePhase_re]
  have him (p : τ×Ω) : (Z p).im=Real.sin (R p.1 p.2)*H p.1 p.2 := by
    simp only [Z,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add,sourceRieszFinitePhase_im]
  have hiC : Integrable (fun p:τ×Ω=>Real.cos (R p.1 p.2)*H p.1 p.2) (η.prod P) := by
    have hh := hiZ.re
    change Integrable (fun p=>(Z p).re) (η.prod P) at hh
    simpa only [hre] using hh
  have hiS : Integrable (fun p:τ×Ω=>Real.sin (R p.1 p.2)*H p.1 p.2) (η.prod P) := by
    have hh := hiZ.im
    change Integrable (fun p=>(Z p).im) (η.prod P) at hh
    simpa only [him] using hh
  have hiA := integrable_sourceRieszFinitePhase P A hA
  have hiY := integrable_sourceRieszFinitePhase P Y hY
  have hiAc : Integrable (fun ω=>Real.cos (A ω)) P := by
    have hh := hiA.re
    change Integrable (fun ω=>(sourceRieszFinitePhase (A ω)).re) P at hh
    simpa only [sourceRieszFinitePhase_re] using hh
  have hiAs : Integrable (fun ω=>Real.sin (A ω)) P := by
    have hh := hiA.im
    change Integrable (fun ω=>(sourceRieszFinitePhase (A ω)).im) P at hh
    simpa only [sourceRieszFinitePhase_im] using hh
  have hid : Integrable (fun ω=>Real.cos (A ω)-Ns ω) P := hiAc.sub' hiNs
  have his : Integrable (fun ω=>Real.sin (A ω)+Nc ω) P :=
    (integrable_add_iff_integrable_left' hiNc).mpr hiAs
  have hc := integral_congr_ae hcos
  rw [integral_sub hid ((hiC.integral_prod_right).const_mul q),
    integral_sub hiAc hiNs,integral_const_mul,hNs,sub_zero,
    ←integral_prod_symm _ hiC] at hc
  have hs := integral_congr_ae hsin
  rw [integral_sub his ((hiS.integral_prod_right).const_mul q),
    integral_add hiAs hiNc,integral_const_mul,hNc,add_zero,
    ←integral_prod_symm _ hiS] at hs
  change (∫ ω,sourceRieszFinitePhase (Y ω) ∂P)=
    (∫ ω,sourceRieszFinitePhase (A ω) ∂P)-q • (∫ r,∫ ω,Z (r,ω) ∂P ∂η)
  rw [←integral_prod Z hiZ]
  have hreY := (integral_re hiY).symm
  have hreA := (integral_re hiA).symm
  have hreZ := (integral_re hiZ).symm
  have himY := (integral_im hiY).symm
  have himA := (integral_im hiA).symm
  have himZ := (integral_im hiZ).symm
  change (∫ ω,sourceRieszFinitePhase (Y ω) ∂P).re =
    ∫ ω,(sourceRieszFinitePhase (Y ω)).re ∂P at hreY
  change (∫ ω,sourceRieszFinitePhase (A ω) ∂P).re =
    ∫ ω,(sourceRieszFinitePhase (A ω)).re ∂P at hreA
  change (∫ p,Z p ∂(η.prod P)).re = ∫ p,(Z p).re ∂(η.prod P) at hreZ
  change (∫ ω,sourceRieszFinitePhase (Y ω) ∂P).im =
    ∫ ω,(sourceRieszFinitePhase (Y ω)).im ∂P at himY
  change (∫ ω,sourceRieszFinitePhase (A ω) ∂P).im =
    ∫ ω,(sourceRieszFinitePhase (A ω)).im ∂P at himA
  change (∫ p,Z p ∂(η.prod P)).im = ∫ p,(Z p).im ∂(η.prod P) at himZ
  apply Complex.ext
  · simp only [Complex.sub_re,Complex.smul_re,smul_eq_mul,hreY,hreA,hreZ,
      sourceRieszFinitePhase_re,hre]
    exact hc
  · simp only [Complex.sub_im,Complex.smul_im,smul_eq_mul,himY,himA,himZ,
      sourceRieszFinitePhase_im,him]
    exact hs

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszFinitePhase_re
#print axioms DGRHS.Commutator.sourceRieszFinitePhase_re
#check @DGRHS.Commutator.sourceRieszFinitePhase_im
#print axioms DGRHS.Commutator.sourceRieszFinitePhase_im
#check @DGRHS.Commutator.integrable_sourceRieszFinitePhase
#print axioms DGRHS.Commutator.integrable_sourceRieszFinitePhase
#check @DGRHS.Commutator.sourceRiesz_samplewise_trig_expected_phase
#print axioms DGRHS.Commutator.sourceRiesz_samplewise_trig_expected_phase
