import DGPS.FiniteN.AnisotropicQuarticOccupationUpper
import DGPS.FiniteN.AnisotropicQuarticStripMass
import DGPS.FiniteN.AnisotropicQuarticAuxiliaryTransfer

/-! The actual canonical empirical support bound, from a positive conditional
posterior event and the genuine normalized latent-strip estimate. -/

open MeasureTheory Filter Topology Set
open DGPS.Models DGPS.FiniteN.QuarticSaddleGlobalFIN066
open DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.GaussianCoupling
open scoped ENNReal

namespace DGPS.FiniteN

private theorem quartic_posterior_noise_widths (L d : ℝ) (hd : 0 < d) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ N : ℝ, M ≤ N →
      (Real.sqrt N)⁻¹ * L ≤ d ∧ (Real.sqrt N)⁻¹ * L ≤ N ^ (-(1 / 4 : ℝ)) := by
  have hlong : Tendsto (fun N : ℝ => (Real.sqrt N)⁻¹ * L) atTop (𝓝 0) := by
    simpa only [zero_mul, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).mul_const L
  have htrans : Tendsto (fun N : ℝ => L * N ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul L
  have hEv : ∀ᶠ N : ℝ in atTop,
      (Real.sqrt N)⁻¹ * L ≤ d ∧ (Real.sqrt N)⁻¹ * L ≤ N ^ (-(1 / 4 : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), hlong.eventually (gt_mem_nhds hd),
      htrans.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hN hlong hsmall
    have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
    have hs : 0 ≤ N ^ (-(1 / 4 : ℝ)) := (Real.rpow_pos_of_pos hNp _).le
    have hs2 : (N ^ (-(1 / 4 : ℝ))) ^ 2 = (Real.sqrt N)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le, Real.sqrt_eq_rpow,
        ← Real.rpow_neg hNp.le]
      congr 1
      norm_num
    refine ⟨hlong.le, ?_⟩
    calc
      _ = N ^ (-(1 / 4 : ℝ)) * (L * N ^ (-(1 / 4 : ℝ))) := by rw [← hs2]; ring
      _ ≤ N ^ (-(1 / 4 : ℝ)) * 1 := mul_le_mul_of_nonneg_left hsmall.le hs
      _ = _ := mul_one _
  obtain ⟨M, hM⟩ := eventually_atTop.mp hEv
  exact ⟨max 1 M, le_max_left _ _, fun N hN => hM N ((le_max_right _ _).trans hN)⟩

private theorem quartic_fieldBox_auxiliary_mass (N : ℕ+) (δ s : ℝ) :
    auxLaw quarticHubbardD quarticHubbardField quarticHubbardU quarticHubbardFeature (DGPS.haar 1) N
      (quarticFieldBox δ s) =
        (imsEta (N : ℝ) quarticPsi_FIN066) (quarticRareStrip δ s) := by
  let e := MeasurableEquiv.toLp 2 (Fin 2 → ℝ)
  have hm : MeasurableSet (quarticRareStrip δ s) :=
    (quarticFieldBox_measurable δ s).preimage e.symm.measurable
  rw [← quartic_auxLaw_map N, Measure.map_apply e.measurable hm]
  rfl

/-- FIN072 actual canonical empirical support bound. The fixed positive posterior
event is multiplied into the particle probability; no unconditional tail is subtracted. -/
theorem quartic_empirical_support_rare_upper :
    ∃ t δ C M : ℝ, 1 < t ∧ 0 < δ ∧ 0 < C ∧ 1 ≤ M ∧
      (∀ w, quarticPsi_FIN066 !₂[t, 0] ≤ quarticPsi_FIN066 w) ∧
      (∀ w, quarticPsi_FIN066 w ≤ quarticPsi_FIN066 !₂[t, 0] → w = !₂[t, 0]) ∧
      0 < quarticPsi_FIN066 !₂[-4, 0] - quarticPsi_FIN066 !₂[t, 0] ∧
      ∀ N : ℕ+, M ≤ (N : ℝ) →
        (particleLaw anisotropicQuarticSaddle N).real
          ((posteriorCenter quarticHubbardD quarticHubbardField quarticHubbardFeature N) ⁻¹'
            quarticFieldBox δ (2 * (N : ℝ) ^ (-(1 / 4 : ℝ)))) ≤
          C * (N : ℝ) ^ (1 / 4 : ℝ) * Real.exp
            (-((N : ℝ) * (quarticPsi_FIN066 !₂[-4, 0] - quarticPsi_FIN066 !₂[t, 0]))) := by
  obtain ⟨t, d, ht, hd, hd1, hmin, huniq, hgap, hstrip⟩ := quartic_normalized_rare_strip_upper
  obtain ⟨C, M0, hC, hM0, hstrip⟩ := hstrip 3 (by norm_num)
  obtain ⟨L, hL, p, hp, hp1, hpost⟩ := quartic_empirical_box_posterior_upper
  let δ := d / 2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨M1, hM1, hwidth⟩ := quartic_posterior_noise_widths L (δ / 4) (by positivity)
  have hptop : p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp.ne' hptop
  refine ⟨t, δ, C / p.toReal, max M0 M1, ht, hδ, div_pos hC hpr,
    hM0.trans (le_max_left _ _), hmin, huniq, hgap, fun N hN => ?_⟩
  have hNp : 0 < (N : ℝ) := by exact_mod_cast N.pos
  let s := (N : ℝ) ^ (-(1 / 4 : ℝ))
  have hw := hwidth (N : ℝ) ((le_max_right _ _).trans hN)
  have hP := hpost N δ (2 * s) (δ / 4) s hw.1 hw.2
  have hsub : quarticFieldBox (δ + δ / 4) (2 * s + s) ⊆ quarticFieldBox d (3 * s) := by
    intro w hw
    change |w 0 + 4| ≤ d ∧ |w 1| ≤ 3 * s
    constructor
    · have h := hw.1
      dsimp only [δ] at h
      linarith
    · have h := hw.2
      linarith
  have hP' := hP.trans (measure_mono hsub)
  rw [quartic_fieldBox_auxiliary_mass] at hP'
  letI : IsProbabilityMeasure (imsEta (N : ℝ) quarticPsi_FIN066) :=
    quartic_imsEta_probability (N : ℝ) hNp
  have hR := ENNReal.toReal_mono
    (measure_ne_top (imsEta (N : ℝ) quarticPsi_FIN066) (quarticRareStrip d (3 * s))) hP'
  rw [ENNReal.toReal_mul] at hR
  have hbound := hR.trans (hstrip (N : ℝ) ((le_max_left _ _).trans hN))
  have hr : ((particleLaw anisotropicQuarticSaddle N)
      ((posteriorCenter quarticHubbardD quarticHubbardField quarticHubbardFeature N) ⁻¹'
        quarticFieldBox δ (2 * s))).toReal ≤
      (C * (N : ℝ) ^ (1 / 4 : ℝ) * Real.exp
        (-((N : ℝ) * (quarticPsi_FIN066 !₂[-4, 0] - quarticPsi_FIN066 !₂[t, 0])))) / p.toReal :=
    (le_div_iff₀ hpr).mpr (by simpa only [mul_comm] using hbound)
  change ((particleLaw anisotropicQuarticSaddle N)
    ((posteriorCenter quarticHubbardD quarticHubbardField quarticHubbardFeature N) ⁻¹'
      quarticFieldBox δ (2 * s))).toReal ≤ _
  refine hr.trans (le_of_eq ?_)
  ring

end DGPS.FiniteN
