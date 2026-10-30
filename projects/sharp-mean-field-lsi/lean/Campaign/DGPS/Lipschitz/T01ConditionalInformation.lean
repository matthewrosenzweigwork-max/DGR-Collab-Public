import DGPS.Lipschitz.T01ReferenceMoments
import FullLabeledLSI.Paper.Sec5LNC
import FullLabeledLSI.Paper.Sec5Pinsker

/-!
# Real conditional information identities without semiconvexity

Finite joint relative entropy gives finite information in every conditional unrevealed label.
This suffices for the real reveal average; boundedness of an equilibrium density is unnecessary.
The conditional interaction identity uses only the actual continuous centered kernel.
-/

open MeasureTheory InformationTheory Filter
open scoped ENNReal

namespace DGPS.Lipschitz

variable {d N : ℕ}

/-- Finite joint entropy gives integrability and the exact real conditional-information formula. -/
theorem conditional_information_integrable (ν : Measure (SharpLSI.Config N d))
    [IsProbabilityMeasure ν] (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤)
    (S : Finset (Fin N)) (i : Fin N) (hi : i ∉ S) :
    Integrable (fun X => (klDiv (SharpLSI.FL.condLawS ν S i
      (SharpLSI.FL.restrictS S X)) μ).toReal) ν ∧
    (∫⁻ X, klDiv (SharpLSI.FL.condLawS ν S i (SharpLSI.FL.restrictS S X)) μ ∂ν).toReal =
      ∫ X, (klDiv (SharpLSI.FL.condLawS ν S i (SharpLSI.FL.restrictS S X)) μ).toReal ∂ν := by
  have hm := SharpLSI.FL.measurable_klDiv_condLawS ν μ S i
  have hfin := SharpLSI.FL.gRev_ne_top ν μ hH S i hi
  change (∫⁻ X, klDiv (SharpLSI.FL.condLawS ν S i (SharpLSI.FL.restrictS S X)) μ ∂ν) ≠ ⊤ at hfin
  exact ⟨integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfin,
    (integral_toReal hm.aemeasurable (ae_lt_top hm hfin)).symm⟩

/-- Exact real reveal average under finite joint entropy, for arbitrary laws. -/
theorem hRev_toReal_eq_of_finite_entropy (ν : Measure (SharpLSI.Config N d))
    [IsProbabilityMeasure ν] (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {j : ℕ} (hj : j < N) :
    (SharpLSI.FL.hRev ν μ j).toReal = SharpLSI.FL.avg1R N j fun S i =>
      ∫ X, (klDiv (SharpLSI.FL.condLawS ν S i (SharpLSI.FL.restrictS S X)) μ).toReal ∂ν := by
  classical
  have hne : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, Sᶜ.Nonempty := by
    intro S hS
    rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin, (Finset.mem_powersetCard.mp hS).2]
    omega
  have hℓ : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, ∀ i ∈ Sᶜ,
      (∫⁻ X, klDiv (SharpLSI.FL.condLawS ν S i (SharpLSI.FL.restrictS S X)) μ ∂ν) ≠ ⊤ :=
    fun S _ i hi => SharpLSI.FL.gRev_ne_top ν μ hH S i (Finset.mem_compl.mp hi)
  have hterm : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
      ((Sᶜ.card : ℝ≥0∞)⁻¹ * ∑ i ∈ Sᶜ,
        ∫⁻ X, klDiv (SharpLSI.FL.condLawS ν S i (SharpLSI.FL.restrictS S X)) μ ∂ν) ≠ ⊤ := by
    intro S hS
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr
      (by exact_mod_cast (Finset.card_pos.mpr (hne S hS)).ne'))
      (ENNReal.sum_ne_top.mpr fun i hi => hℓ S hS i hi)
  unfold SharpLSI.FL.hRev SharpLSI.FL.avg1R
  rw [if_pos hj, ENNReal.toReal_mul, ENNReal.toReal_sum hterm, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  congr 1
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum fun i hi => hℓ S hS i hi]
  congr 1
  exact Finset.sum_congr rfl fun i hi =>
    (conditional_information_integrable ν μ hH S i (Finset.mem_compl.mp hi)).2

/-- The inherited interaction correction is the actual two-particle centered-kernel integral. -/
theorem Jfun_eq_pi_of_current_data (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (ρ : Measure (Torus d)) [IsProbabilityMeasure ρ] :
    SharpLSI.Jfun A.W (μ : Measure (Torus d)) ρ =
      ∫ z, DGPS.centeredKernel A μ (z 0) (z 1) / 2
        ∂Measure.pi (fun _ : Fin 2 => ρ) := by
  have hK := DGPS.continuous_centeredKernel A μ
  obtain ⟨B, hB⟩ := SharpLSI.exists_bound_of_continuous hK
  rw [SharpLSI.integral_pi_two_S5
    (F := fun x y => DGPS.centeredKernel A μ x y / 2)
    (hK.measurable.div_const 2) (B := |B| / 2) (fun x y => by
      rw [abs_div, abs_two]
      exact div_le_div_of_nonneg_right ((hB (x, y)).trans (le_abs_self _)) zero_le_two)]
  unfold SharpLSI.Jfun SharpLSI.interE
  simp_rw [t01_legacy_centeredKernel_eq, integral_div]

/-- The current continuous centered interaction identifies the conditional-product mean
with the real reveal average of the interaction correction, without potential hypotheses. -/
theorem condMeanS_eq_avg1R_Jfun_of_current_data (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (ν : Measure (SharpLSI.Config N d))
    [IsProbabilityMeasure ν] {j : ℕ} (hj : j < N) :
    SharpLSI.FL.condMeanS ν 2 (SharpLSI.FL.Bk A.W (μ : Measure (Torus d))) j =
      SharpLSI.FL.avg1R N j fun S _ =>
        ∫ X, SharpLSI.Jfun A.W (μ : Measure (Torus d)) (SharpLSI.FL.barCond ν S X) ∂ν := by
  classical
  unfold SharpLSI.FL.condMeanS SharpLSI.FL.avg1R
  congr 1
  refine Finset.sum_congr rfl fun S hS => ?_
  have hcard : 0 < Sᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin, (Finset.mem_powersetCard.mp hS).2]
    omega
  have hn : (Sᶜ.card : ℝ) ≠ 0 := by exact_mod_cast hcard.ne'
  have he : (∫ X, (∫ z, SharpLSI.FL.Bk A.W (μ : Measure (Torus d)) z
      ∂Measure.pi (fun _ : Fin 2 => SharpLSI.FL.barCond ν S X)) ∂ν) =
      ∫ X, SharpLSI.Jfun A.W (μ : Measure (Torus d)) (SharpLSI.FL.barCond ν S X) ∂ν := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro X
    letI : IsProbabilityMeasure (SharpLSI.FL.barCond ν S X) := by
      change IsProbabilityMeasure (SharpLSI.FL.barCondA ν S (SharpLSI.FL.restrictS S X))
      exact SharpLSI.FL.isProbabilityMeasure_barCondA ν S hcard (SharpLSI.FL.restrictS S X)
    change (∫ z, SharpLSI.FL.Bk A.W (μ : Measure (Torus d)) z
      ∂Measure.pi (fun _ : Fin 2 => SharpLSI.FL.barCond ν S X)) =
      SharpLSI.Jfun A.W (μ : Measure (Torus d)) (SharpLSI.FL.barCond ν S X)
    rw [Jfun_eq_pi_of_current_data]
    simp only [SharpLSI.FL.Bk, t01_legacy_centeredKernel_eq]
  rw [he, Finset.sum_const, nsmul_eq_mul]
  field_simp [hn]

end DGPS.Lipschitz
