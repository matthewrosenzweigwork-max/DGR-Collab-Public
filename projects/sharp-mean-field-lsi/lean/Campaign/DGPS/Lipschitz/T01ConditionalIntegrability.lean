import DGPS.Lipschitz.T01ConditionalInformation

/-!
# Integrability of the actual conditional entropy and interaction gap

Finite joint reference entropy controls the conditional relative entropies. The interaction
correction is bounded and measurable solely from the current continuous centered kernel.
These facts give the left-side integrability needed by the shared reveal integration step.
-/

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal

namespace DGPS.Lipschitz

/-- The actual continuous interaction correction is measurable along any Markov kernel. -/
theorem measurable_Jfun_kernel_of_current_data {d : ℕ} (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) {Ω : Type*} [MeasurableSpace Ω]
    (κ : Kernel Ω (Torus d)) [IsMarkovKernel κ] :
    Measurable (fun a => SharpLSI.Jfun A.W (μ : Measure (Torus d)) (κ a)) := by
  have hK := DGPS.continuous_centeredKernel A μ
  have hB : Measurable (fun z : Fin 2 → Torus d =>
      DGPS.centeredKernel A μ (z 0) (z 1) / 2) := by
    have hp : Measurable (fun z : Fin 2 → Torus d => (z 0, z 1)) :=
      (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using
      (hK.measurable.comp hp).div_const (2 : ℝ)
  have hm := ((hB.comp measurable_snd).stronglyMeasurable.integral_kernel_prod_right'
    (κ := SharpLSI.piK κ 2)).measurable
  have he : (fun a => SharpLSI.Jfun A.W (μ : Measure (Torus d)) (κ a)) =
      (fun a => ∫ z, DGPS.centeredKernel A μ (z 0) (z 1) / 2 ∂SharpLSI.piK κ 2 a) := by
    funext a
    rw [SharpLSI.piK_apply, Jfun_eq_pi_of_current_data]
  rw [he]
  exact hm

/-- The conditional-barycenter interaction is integrable without an equilibrium premise. -/
theorem conditional_Jfun_integrable {d N : ℕ} (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (ν : Measure (SharpLSI.Config N d))
    [IsProbabilityMeasure ν] (S : Finset (Fin N)) (hS : 1 ≤ Sᶜ.card) :
    Integrable (fun X => SharpLSI.Jfun A.W (μ : Measure (Torus d))
      (SharpLSI.FL.barCond ν S X)) ν := by
  letI : IsMarkovKernel (SharpLSI.FL.barKer ν S) :=
    ⟨fun a => SharpLSI.FL.isProbabilityMeasure_barCondA ν S hS a⟩
  have hm : Measurable (fun X => SharpLSI.Jfun A.W (μ : Measure (Torus d))
      (SharpLSI.FL.barCond ν S X)) := by
    exact (measurable_Jfun_kernel_of_current_data A μ (SharpLSI.FL.barKer ν S)).comp
      (SharpLSI.FL.measurable_restrictS S)
  obtain ⟨B, hB⟩ := SharpLSI.exists_bound_of_continuous (DGPS.continuous_centeredKernel A μ)
  refine Integrable.of_bound hm.aestronglyMeasurable (|B| / 2) (Eventually.of_forall fun X => ?_)
  letI : IsProbabilityMeasure (SharpLSI.FL.barCond ν S X) := by
    change IsProbabilityMeasure (SharpLSI.FL.barCondA ν S (SharpLSI.FL.restrictS S X))
    exact SharpLSI.FL.isProbabilityMeasure_barCondA ν S hS (SharpLSI.FL.restrictS S X)
  rw [Jfun_eq_pi_of_current_data]
  have hnorm : ∀ᵐ z ∂Measure.pi (fun _ : Fin 2 => SharpLSI.FL.barCond ν S X),
      ‖DGPS.centeredKernel A μ (z 0) (z 1) / 2‖ ≤ |B| / 2 :=
    Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_div, abs_two]
      exact div_le_div_of_nonneg_right ((hB (z 0, z 1)).trans (le_abs_self _)) zero_le_two
  simpa using norm_integral_le_of_norm_le_const hnorm

/-- The exact left side of the conditional scalar/species rate inequality is integrable.
No finite conditional dissipation or sign of the interaction correction is assumed. -/
theorem conditional_rate_left_integrable {d N : ℕ} (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    {Q : SharpLSI.Config N d → ℝ} {c C : ℝ} (hQ : SharpLSI.FL.IsBddDens Q c C)
    (ν : Measure (SharpLSI.Config N d)) [IsProbabilityMeasure ν]
    (hν : ν = SharpLSI.FL.qMeasure Q)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≠ ⊤)
    (S : Finset (Fin N)) (hS : 1 ≤ Sᶜ.card) (r : ℝ) :
    Integrable (fun X => 2 * r * ((Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ,
      (klDiv (SharpLSI.densMeasure (SharpLSI.FL.condDensS Q S i (SharpLSI.FL.restrictS S X)))
        (μ : Measure (Torus d))).toReal + SharpLSI.Jfun A.W (μ : Measure (Torus d))
        (SharpLSI.densMeasure (SharpLSI.FL.barDensS Q S (SharpLSI.FL.restrictS S X))))) ν := by
  have hKL : ∀ i ∈ Sᶜ, Integrable (fun X =>
      (klDiv (SharpLSI.densMeasure (SharpLSI.FL.condDensS Q S i (SharpLSI.FL.restrictS S X)))
        (μ : Measure (Torus d))).toReal) ν := by
    intro i hi
    have hiS := Finset.mem_compl.mp hi
    apply (conditional_information_integrable ν (μ : Measure (Torus d)) hH S i hiS).1.congr
    filter_upwards [SharpLSI.FL.condLawS_ae_eq_X hQ hiS hν] with X hX
    rw [hX]
  have hJ : Integrable (fun X => SharpLSI.Jfun A.W (μ : Measure (Torus d))
      (SharpLSI.densMeasure (SharpLSI.FL.barDensS Q S (SharpLSI.FL.restrictS S X)))) ν := by
    apply (conditional_Jfun_integrable A μ ν S hS).congr
    filter_upwards [SharpLSI.FL.barCond_ae_eq_densMeasure hQ hν (S := S)] with X hX
    rw [hX]
  exact (((integrable_finsetSum _ hKL).const_mul _).add hJ).const_mul _

end DGPS.Lipschitz
