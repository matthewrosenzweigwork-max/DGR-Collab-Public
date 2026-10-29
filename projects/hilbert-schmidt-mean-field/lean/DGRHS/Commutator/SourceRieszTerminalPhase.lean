import DGRHS.Commutator.SourceRieszFinitePhase
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/- DGR source4011 terminal phase perturbation. Actual unit-phase derivative and
native real-segment mean value give global Lipschitz1. Proper phase expectations
need no moment of Y; the remainder itself is required proper. No terminal
fluctuation representation or characteristic factorization is assumed here. -/
noncomputable section
open MeasureTheory Set
namespace DGRHS.Commutator

lemma sourceRiesz_phase_add_perturbation (s r : ℝ) :
    ‖sourceRieszFinitePhase (s+r)-sourceRieszFinitePhase s‖≤|r| := by
  let c : ℂ := Complex.I*(r:ℂ)
  let F : ℝ→ℂ := fun t=>Complex.exp (Complex.I*(s:ℂ)+t • c)
  have hd (t : ℝ) : HasDerivAt F (c*F t) t := by
    have hlin := (hasDerivAt_const t (Complex.I*(s:ℂ))).add
      ((hasDerivAt_id t).smul_const c)
    simpa [F,mul_comm] using hlin.cexp
  have hb (t : ℝ) : ‖c*F t‖≤|r| := by
    simp [c,F,norm_mul,Complex.norm_exp,Complex.real_smul,Real.norm_eq_abs]
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t (_ : t∈Icc (0:ℝ) 1)=>(hd t).hasDerivWithinAt)
    (fun t (_ : t∈Ico (0:ℝ) 1)=>hb t)
  simpa [F,c,sourceRieszFinitePhase,Complex.ofReal_add,mul_add] using hh

/-- Genuine proper characteristic expectations and L1 phase perturbation.
No L1 premise on the base phase argument Y is needed. -/
theorem sourceRiesz_terminal_phase_expectation {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Y R : Ω→ℝ) (hY : Measurable Y) (hR : Measurable R) (hiR : Integrable R ν) :
    Integrable (fun ω=>sourceRieszFinitePhase (Y ω+R ω)) ν ∧
    Integrable (fun ω=>sourceRieszFinitePhase (Y ω)) ν ∧
    ‖(∫ ω,sourceRieszFinitePhase (Y ω+R ω) ∂ν)-
      (∫ ω,sourceRieszFinitePhase (Y ω) ∂ν)‖≤∫ ω,|R ω| ∂ν := by
  have h1 : Integrable (fun ω=>sourceRieszFinitePhase (Y ω+R ω)) ν := by
    apply (integrable_const (1:ℝ)).mono'
      (measurable_sourceRieszFinitePhase.comp (hY.add hR)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω=>(norm_sourceRieszFinitePhase _).le
  have h0 : Integrable (fun ω=>sourceRieszFinitePhase (Y ω)) ν := by
    apply (integrable_const (1:ℝ)).mono'
      (measurable_sourceRieszFinitePhase.comp hY).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω=>(norm_sourceRieszFinitePhase _).le
  refine ⟨h1,h0,?_⟩
  rw [←integral_sub h1 h0]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono (h1.sub h0).norm hiR.abs
  intro ω
  exact sourceRiesz_phase_add_perturbation (Y ω) (R ω)

#check sourceRiesz_phase_add_perturbation
#print axioms sourceRiesz_phase_add_perturbation
#check sourceRiesz_terminal_phase_expectation
#print axioms sourceRiesz_terminal_phase_expectation
end DGRHS.Commutator
