import DGPS.FiniteN.AnisotropicQuarticConditionalCore
import DGPS.FiniteN.AnisotropicQuarticSmallCoreMass
import DGPS.FiniteN.AnisotropicQuarticOccupationUpper
import DGPS.FiniteN.AnisotropicQuarticAuxiliaryTransfer

/-! Actual canonical rare-core lower bound by conditional concentration and the
genuine smaller latent-core mass. All witnesses refer to the fixed quartic model. -/

open MeasureTheory Set
open DGPS.Models DGPS.FiniteN.QuarticSaddleGlobalFIN066
open DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.GaussianCoupling
open scoped ENNReal

namespace DGPS.FiniteN

/-- FIN073 actual empirical core lower bound. No conditional probability, rare
mass, mean, covariance or rate estimate is assumed as a public premise. -/
theorem quartic_empirical_core_rare_lower :
    ∃ t : ℝ, 1 < t ∧
      (∀ w, quarticPsi_FIN066 !₂[t, 0] ≤ quarticPsi_FIN066 w) ∧
      (∀ w, quarticPsi_FIN066 w ≤ quarticPsi_FIN066 !₂[t, 0] → w = !₂[t, 0]) ∧
      0 < quarticPsi_FIN066 !₂[-4, 0] - quarticPsi_FIN066 !₂[t, 0] ∧
      ∀ δ : ℝ, 0 < δ → ∃ c M : ℝ, 0 < c ∧ 1 ≤ M ∧ ∀ N : ℕ+, M ≤ (N : ℝ) →
        c * (N : ℝ) ^ (1 / 4 : ℝ) * Real.exp
            (-((N : ℝ) * (quarticPsi_FIN066 !₂[-4, 0] - quarticPsi_FIN066 !₂[t, 0]))) ≤
          (particleLaw anisotropicQuarticSaddle N).real
            ((posteriorCenter quarticHubbardD quarticHubbardField quarticHubbardFeature N) ⁻¹'
              quarticFieldBox (δ / 2) ((N : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  obtain ⟨k, hk, hk1, hcond⟩ := quartic_conditional_core_probability
  obtain ⟨t, ht, hmin, huniq, hgap, hmass⟩ := quartic_small_rare_core_mass_lower
  obtain ⟨c, M0, hc, hM0, hmass⟩ := hmass k hk hk1
  refine ⟨t, ht, hmin, huniq, hgap, fun δ hδ => ?_⟩
  obtain ⟨M1, hM1, hcond⟩ := hcond δ hδ
  refine ⟨c / 2, max M0 M1, by positivity, hM0.trans (le_max_left _ _), fun N hN => ?_⟩
  let s := (N : ℝ) ^ (-(1 / 4 : ℝ))
  let A := quarticFieldBox ((k * s) ^ 2) (k * s)
  let C := (posteriorCenter quarticHubbardD quarticHubbardField quarticHubbardFeature N) ⁻¹'
    quarticFieldBox (δ / 2) s
  have hAm : MeasurableSet A := quarticFieldBox_measurable _ _
  have hCm : MeasurableSet C := (quarticFieldBox_measurable _ _).preimage
    (measurable_posteriorCenter quartic_hubbard_hyp quarticHubbardD quarticHubbardField N)
  have hPint : particleLaw anisotropicQuarticSaddle N C =
      ∫⁻ w, (Measure.pi fun _ : Fin N => siteLaw quarticHubbardU quarticHubbardFeature (DGPS.haar 1) w) C
        ∂auxLaw quarticHubbardD quarticHubbardField quarticHubbardU quarticHubbardFeature (DGPS.haar 1) N := by
    rw [← quartic_hubbard_particle_law N,
      ← hubbardJoint_map_snd quartic_hubbard_hyp quartic_hubbard_D_posDef quarticHubbardField N,
      Measure.map_apply measurable_snd hCm,
      hubbardJoint_apply quartic_hubbard_hyp quartic_hubbard_D_posDef quarticHubbardField N
        (hCm.preimage measurable_snd)]
    rfl
  have hLow : ENNReal.ofReal (1 / 2) *
      auxLaw quarticHubbardD quarticHubbardField quarticHubbardU quarticHubbardFeature (DGPS.haar 1) N A ≤
        particleLaw anisotropicQuarticSaddle N C := by
    rw [hPint]
    calc
      _ = ∫⁻ w, A.indicator (fun _ => ENNReal.ofReal (1 / 2)) w
          ∂auxLaw quarticHubbardD quarticHubbardField quarticHubbardU quarticHubbardFeature (DGPS.haar 1) N := by
        rw [lintegral_indicator hAm, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
      _ ≤ _ := lintegral_mono fun w => by
        by_cases hw : w ∈ A
        · rw [Set.indicator_of_mem hw]
          exact hcond N ((le_max_right _ _).trans hN) w hw.1 hw.2
        · rw [Set.indicator_of_notMem hw]
          exact bot_le
  let e := MeasurableEquiv.toLp 2 (Fin 2 → ℝ)
  have hAux : auxLaw quarticHubbardD quarticHubbardField quarticHubbardU quarticHubbardFeature
      (DGPS.haar 1) N A = (imsEta (N : ℝ) quarticPsi_FIN066) (quarticRareRectangle (k * s)) := by
    rw [← quartic_auxLaw_map N, Measure.map_apply e.measurable (quarticRareRectangle_measurable (k * s))]
    congr 1
    ext w
    rw [mem_preimage, quarticRareRectangle_mem]
    rfl
  have hReal := ENNReal.toReal_mono (measure_ne_top (particleLaw anisotropicQuarticSaddle N) C) hLow
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2), hAux] at hReal
  have hMass := hmass (N : ℝ) ((le_max_left _ _).trans hN)
  change c / 2 * (N : ℝ) ^ (1 / 4 : ℝ) * Real.exp
      (-((N : ℝ) * (quarticPsi_FIN066 !₂[-4, 0] - quarticPsi_FIN066 !₂[t, 0]))) ≤
        (particleLaw anisotropicQuarticSaddle N C).toReal
  calc
    _ = (1 / 2) * (c * (N : ℝ) ^ (1 / 4 : ℝ) * Real.exp
        (-((N : ℝ) * (quarticPsi_FIN066 !₂[-4, 0] - quarticPsi_FIN066 !₂[t, 0])))) := by ring
    _ ≤ (1 / 2) * ((imsEta (N : ℝ) quarticPsi_FIN066) (quarticRareRectangle (k * s))).toReal :=
      mul_le_mul_of_nonneg_left hMass (by norm_num)
    _ ≤ _ := hReal

end DGPS.FiniteN
