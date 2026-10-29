import DGRHS.CLT.MacroscopicFreeEnergy

/-! Genuine thermal free energy with potential and entropy combined before
integration. Serfaty arXiv2407.21194v1, chapter-eqmeas.tex, thermal-existence
remark explicitly permits divergent separate entropy at a finite thermal cost.
The actual cost βV+llr is defined independently of the normalizer. Its properness
and normalizer identity are proved from EL and proper pair interaction.
Agreement with the existing separate-integral definition is explicit.
This source-domain extension is not a claim that infinity-minus-infinity in
the printed separate-integral notation has a real value. -/
noncomputable section
open MeasureTheory
namespace DGRHS.CLT
variable {S : Type*} [MeasurableSpace S]

def thermalMacroscopicFreeEnergy (ν₀ μ : Measure S) (W : S → S → ℝ)
    (V : S → ℝ) (β : ℝ) : ℝ :=
  DGRHS.interactionEnergy μ W + β⁻¹ * (∫ x, β * V x + llr μ ν₀ x ∂μ)

theorem thermalMacroscopicFreeEnergy_eq_separate (ν₀ μ : Measure S)
    (W : S → S → ℝ) (V : S → ℝ) (β : ℝ) (hβ : β ≠ 0)
    (hV : Integrable V μ) (hL : Integrable (llr μ ν₀) μ) :
    thermalMacroscopicFreeEnergy ν₀ μ W V β = macroscopicFreeEnergy ν₀ μ W V β := by
  unfold thermalMacroscopicFreeEnergy macroscopicFreeEnergy
  rw [integral_add (hV.const_mul β) hL, integral_const_mul]
  field_simp
  ring

theorem equilibrium_thermal_combined_cost (ν₀ μ : Measure S) [SigmaFinite ν₀]
    [IsProbabilityMeasure μ] (W : S → S → ℝ) (V : S → ℝ) (β : ℝ) (hβ : β ≠ 0)
    (hW : Integrable (Function.uncurry W) (μ.prod μ))
    (hEL : ν₀.tilted (fun x => -β * (V x + DGRHS.potential μ W x)) = μ) :
    Integrable (fun x => β * V x + llr μ ν₀ x) μ ∧
    (∫ x, β * V x + llr μ ν₀ x ∂μ) =
      -2 * β * DGRHS.interactionEnergy μ W -
        Real.log (∫ x, Real.exp (-β * (V x + DGRHS.potential μ W x)) ∂ν₀) ∧
    -β * thermalMacroscopicFreeEnergy ν₀ μ W V β =
      Real.log (∫ x, Real.exp (-β * (V x + DGRHS.potential μ W x)) ∂ν₀) +
        β * DGRHS.interactionEnergy μ W := by
  let f := fun x => -β * (V x + DGRHS.potential μ W x)
  have hf := integrable_exp_of_tilted_probability f hEL
  have hμν : μ ≪ ν₀ := by rw [← hEL]; exact tilted_absolutelyContinuous ν₀ f
  have he : llr μ ν₀ =ᵐ[μ] (fun x => f x - Real.log (∫ y, Real.exp (f y) ∂ν₀)) := by
    have h := hμν.ae_le (log_rnDeriv_tilted_left_self hf)
    rw [hEL] at h
    exact h
  have hcost : (fun x => β * V x + llr μ ν₀ x) =ᵐ[μ]
      (fun x => -β * DGRHS.potential μ W x - Real.log (∫ y, Real.exp (f y) ∂ν₀)) := by
    filter_upwards [he] with x hx
    rw [hx]
    dsimp only [f]
    ring
  have hF := DGRHS.integrable_potential μ W hW
  have hC : Integrable (fun x => β * V x + llr μ ν₀ x) μ :=
    ((hF.const_mul (-β)).sub (integrable_const _)).congr hcost.symm
  have hInt : (∫ x, β * V x + llr μ ν₀ x ∂μ) =
      -2 * β * DGRHS.interactionEnergy μ W - Real.log (∫ y, Real.exp (f y) ∂ν₀) := by
    rw [integral_congr_ae hcost, integral_sub (hF.const_mul (-β)) (integrable_const _),
      integral_const_mul, DGRHS.integral_potential μ W hW, integral_const]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one]
    ring
  refine ⟨hC, hInt, ?_⟩
  unfold thermalMacroscopicFreeEnergy
  rw [hInt]
  dsimp only [f]
  field_simp
  ring

end DGRHS.CLT
#check @DGRHS.CLT.thermalMacroscopicFreeEnergy
#print axioms DGRHS.CLT.thermalMacroscopicFreeEnergy
#check @DGRHS.CLT.thermalMacroscopicFreeEnergy_eq_separate
#print axioms DGRHS.CLT.thermalMacroscopicFreeEnergy_eq_separate
#check @DGRHS.CLT.equilibrium_thermal_combined_cost
#print axioms DGRHS.CLT.equilibrium_thermal_combined_cost
