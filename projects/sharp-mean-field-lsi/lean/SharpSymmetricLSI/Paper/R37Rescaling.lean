import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D09_ParticleRates
import SharpSymmetricLSI.Defs.D14_Conditional
import SharpSymmetricLSI.Infra.SmoothWeakGrad

/-!
# R37 (Remark 8.1): the mean-field rescaling identities (Phase 1)

The mean-field conjuncts of `physical_convention`: `F_β = β F_phys` (`freeEnergy_rescale`, for
every measure), `D_β = β² D_phys` (`dissipation_rescale`) and the infimum of `D_phys/G_phys`
(`physical_rStar`). The particle conjuncts are in `Paper/R37Particle.lean`.
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-! Verbatim copies of the definitions `physFreeEnergy`, `physGap`, `physDiss` of
`Statements/R37_Remark_8_1.lean`, so that the statement file can import this file; the frozen
definitions unfold to these by `rfl`. -/

/-- Copy of `physFreeEnergy`. -/
noncomputable def physFreeEnergy' (β : ℝ) (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ)
    (ρ : Measure (Torus d)) : EReal :=
  ((β⁻¹ : ℝ) : EReal) * ((klDiv ρ (haar d) : ENNReal) : EReal) +
    ((potE V ρ + interE W ρ ρ / 2 : ℝ) : EReal)

/-- Copy of `physGap`. -/
noncomputable def physGap' (β : ℝ) (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ)
    (ρ : Measure (Torus d)) : EReal :=
  physFreeEnergy' β V W ρ - ⨅ η : ProbabilityMeasure (Torus d), physFreeEnergy' β V W η

open Classical in
/-- Copy of `physDiss`. -/
noncomputable def physDiss' (β : ℝ) (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ)
    (ρ : Torus d → ℝ) : ℝ≥0∞ :=
  if MemH1 (haar d) (fun x => Real.sqrt (ρ x)) ∧
      HasWeakGrad (fun x => V x + convDens W ρ x) then
    ∫⁻ x, ENNReal.ofReal (∑ k, (2 * β⁻¹ * weakGrad (fun y => Real.sqrt (ρ y)) x k +
      Real.sqrt (ρ x) * weakGrad (fun y => V y + convDens W ρ y) x k) ^ 2) ∂haar d
  else ⊤

theorem potE_smul (β : ℝ) (V : Torus d → ℝ) (ρ : Measure (Torus d)) :
    potE (fun x => β * V x) ρ = β * potE V ρ := by
  simp [potE, integral_const_mul]

theorem interE_smul (β : ℝ) (W : Torus d → Torus d → ℝ) (ρ η : Measure (Torus d)) :
    interE (fun x y => β * W x y) ρ η = β * interE W ρ η := by
  simp [interE, integral_const_mul]

/-- Remark 8.1: `F_β = β F_phys`. -/
theorem freeEnergy_rescale {β : ℝ} (hβ : 0 < β) (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ)
    (ρ : Measure (Torus d)) :
    freeEnergy (fun x => β * V x) (fun x y => β * W x y) ρ =
      ((β : ℝ) : EReal) * physFreeEnergy' β V W ρ := by
  unfold freeEnergy physFreeEnergy'
  rw [potE_smul, interE_smul,
    EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hβ.le) (EReal.coe_ne_top β),
    ← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hβ.ne', EReal.coe_one, one_mul, ← EReal.coe_mul]
  congr 2
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem IsWeakGrad.const_mul {f : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad f g) (c : ℝ) : IsWeakGrad (fun x => c * f x) (fun x k => c * g x k) := by
  refine ⟨?_, fun k => (h.locInt_grad k).smul c, fun φ hφ hφc k => ?_⟩
  · exact h.locInt.smul c
  · simp only [mul_assoc]
    rw [integral_const_mul, integral_const_mul, h.ibp φ hφ hφc k, mul_neg]

theorem hasWeakGrad_const_mul_iff {f : UnitAddTorus ι → ℝ} {c : ℝ} (hc : c ≠ 0) :
    HasWeakGrad (fun x => c * f x) ↔ HasWeakGrad f := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨fun x k => c⁻¹ * g x k, ?_⟩
    have := hg.const_mul c⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ hc] using this
  · rintro ⟨g, hg⟩; exact ⟨_, hg.const_mul c⟩

theorem weakGrad_const_mul_ae {f : UnitAddTorus ι → ℝ} (hf : HasWeakGrad f) (c : ℝ) :
    weakGrad (fun x => c * f x) =ᵐ[volume] fun x k => c * weakGrad f x k := by
  have hf' : HasWeakGrad (fun x => c * f x) := ⟨_, hf.choose_spec.const_mul c⟩
  have e1 : weakGrad (fun x => c * f x) = hf'.choose := by simp [weakGrad, hf']
  have e2 : weakGrad f = hf.choose := by simp [weakGrad, hf]
  rw [e1, e2]
  exact weakGrad_ae_unique hf'.choose_spec (hf.choose_spec.const_mul c)

/-- Remark 8.1: `D_β = β² D_phys`. -/
theorem dissipation_rescale {β : ℝ} (hβ : 0 < β) (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ)
    (ρ : Torus d → ℝ) :
    dissipation (fun x => β * V x) (fun x y => β * W x y) ρ =
      ENNReal.ofReal (β ^ 2) * physDiss' β V W ρ := by
  have hF : (fun x => β * V x + convDens (fun x y => β * W x y) ρ x) =
      fun x => β * (V x + convDens W ρ x) := by
    funext x; simp [convDens, mul_assoc, integral_const_mul, mul_add]
  unfold dissipation physDiss'
  rw [hF]
  by_cases hc : MemH1 (haar d) (fun x => Real.sqrt (ρ x)) ∧
      HasWeakGrad (fun x => V x + convDens W ρ x)
  · have hc' : MemH1 (haar d) (fun x => Real.sqrt (ρ x)) ∧
        HasWeakGrad (fun x => β * (V x + convDens W ρ x)) :=
      ⟨hc.1, (hasWeakGrad_const_mul_iff hβ.ne').mpr hc.2⟩
    simp only [hc', hc, and_self, ↓reduceIte]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr_ae
    filter_upwards [weakGrad_const_mul_ae hc.2 β] with x hx
    rw [hx, ← ENNReal.ofReal_mul (by positivity), Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    field_simp
  · have hc' : ¬ (MemH1 (haar d) (fun x => Real.sqrt (ρ x)) ∧
        HasWeakGrad (fun x => β * (V x + convDens W ρ x))) := by
      rwa [hasWeakGrad_const_mul_iff hβ.ne']
    simp only [hc', hc, ↓reduceIte]
    rw [ENNReal.mul_top (by simp; positivity)]

theorem ereal_mul_iInf {β : ℝ} (hβ : 0 < β) {α : Type*} (f : α → EReal) :
    ((β : ℝ) : EReal) * ⨅ a, f a = ⨅ a, ((β : ℝ) : EReal) * f a := by
  have hb : (0 : EReal) ≤ (β : EReal) := EReal.coe_nonneg.mpr hβ.le
  have hb' : (0 : EReal) ≤ ((β⁻¹ : ℝ) : EReal) := EReal.coe_nonneg.mpr (inv_nonneg.mpr hβ.le)
  have hcancel : ∀ x : EReal, ((β⁻¹ : ℝ) : EReal) * (((β : ℝ) : EReal) * x) = x := fun x => by
    rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hβ.ne', EReal.coe_one, one_mul]
  have hcancel' : ∀ x : EReal, ((β : ℝ) : EReal) * (((β⁻¹ : ℝ) : EReal) * x) = x := fun x => by
    rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hβ.ne', EReal.coe_one, one_mul]
  apply le_antisymm
  · exact le_iInf fun a => mul_le_mul_of_nonneg_left (iInf_le f a) hb
  · have h1 : ((β⁻¹ : ℝ) : EReal) * (⨅ a, ((β : ℝ) : EReal) * f a) ≤ ⨅ a, f a :=
      le_iInf fun a => (mul_le_mul_of_nonneg_left (iInf_le _ a) hb').trans_eq (hcancel _)
    have h2 := mul_le_mul_of_nonneg_left h1 hb
    rwa [hcancel'] at h2

/-- `G_β = β G_phys`. -/
theorem gap_rescale {β : ℝ} (hβ : 0 < β) (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ)
    (ρ : Measure (Torus d)) :
    gap (fun x => β * V x) (fun x y => β * W x y) ρ = ((β : ℝ) : EReal) * physGap' β V W ρ := by
  unfold gap Fstar physGap'
  simp_rw [freeEnergy_rescale hβ]
  rw [← ereal_mul_iInf hβ, sub_eq_add_neg, sub_eq_add_neg,
    EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hβ.le) (EReal.coe_ne_top β),
    mul_neg]

theorem ennreal_rescale_ratio {b : ℝ≥0∞} (hb0 : b ≠ 0) (hbt : b ≠ ⊤) (P Q : ℝ≥0∞) :
    2 * (b ^ 2 * P / (2 * (b * Q))) * b⁻¹ = P / Q := by
  have h2 : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
  have hb : b * b⁻¹ = 1 := ENNReal.mul_inv_cancel hb0 hbt
  rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl two_ne_zero)
      (Or.inl ENNReal.ofNat_ne_top), ENNReal.mul_inv (Or.inl hb0) (Or.inl hbt)]
  calc 2 * (b ^ 2 * P * (2⁻¹ * (b⁻¹ * Q⁻¹))) * b⁻¹
      = (2 * 2⁻¹) * (b * b⁻¹) * (b * b⁻¹) * (P * Q⁻¹) := by ring
    _ = P * Q⁻¹ := by rw [h2, hb, one_mul, one_mul, one_mul]

/-- Remark 8.1: the infimum of `D_phys/G_phys` over the admissible densities is `2r_*/β`. -/
theorem physical_rStar {β : ℝ} (hβ : 0 < β) (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) :
    (⨅ ρ ∈ {ρ | Admissible (fun x => β * V x) (fun x y => β * W x y) ρ},
        physDiss' β V W ρ / (physGap' β V W (densMeasure ρ)).toENNReal) =
      2 * rStar (fun x => β * V x) (fun x y => β * W x y) / ENNReal.ofReal β := by
  have hb0 : ENNReal.ofReal β ≠ 0 := by simp [hβ]
  have hbt : ENNReal.ofReal β ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold rStar
  rw [div_eq_mul_inv, ENNReal.mul_iInf_of_ne two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.iInf_mul_of_ne (ENNReal.inv_ne_zero.mpr hbt) (ENNReal.inv_ne_top.mpr hb0)]
  refine iInf_congr fun ρ => ?_
  rw [ENNReal.mul_iInf_of_ne two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.iInf_mul_of_ne (ENNReal.inv_ne_zero.mpr hbt) (ENNReal.inv_ne_top.mpr hb0)]
  refine iInf_congr fun _ => ?_
  rw [dissipation_rescale hβ, gap_rescale hβ,
    EReal.toENNReal_mul (EReal.coe_nonneg.mpr hβ.le),
    EReal.toENNReal_of_ne_top (EReal.coe_ne_top β), EReal.toReal_coe,
    ENNReal.ofReal_pow hβ.le, ennreal_rescale_ratio hb0 hbt]

end SharpLSI
