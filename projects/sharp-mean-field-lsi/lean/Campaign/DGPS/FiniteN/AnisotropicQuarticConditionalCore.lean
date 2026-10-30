import DGPS.FiniteN.AnisotropicQuarticConditionalMoments
import DGPS.FiniteN.AnisotropicQuarticRareTest
import Mathlib.Probability.Moments.Variance

/-! Actual two-coordinate conditional concentration on a smaller quartic rare core.
The Chebyshev argument adapts the genuine FIN063 scalar proof to both coordinates. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open DGPS.Models DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.GaussianCoupling
open DGPS.FiniteN.Tools.AuxiliaryTransferTorus
open scoped ENNReal

namespace DGPS.FiniteN

private theorem quartic_bad_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZm : Measurable Z)
    (hZ : MemLp Z 2 P) (t ε : ℝ) (hε : 0 < ε)
    (hmean : |∫ x, Z x ∂P - t| ≤ ε / 2)
    (hvar : variance Z P / (ε / 2) ^ 2 ≤ 1 / 4) :
    P {x | |Z x - t| ≤ ε}ᶜ ≤ ENNReal.ofReal (1 / 4) := by
  have hsub : {x | |Z x - t| ≤ ε}ᶜ ⊆ {x | ε / 2 ≤ |Z x - ∫ y, Z y ∂P|} := by
    intro x hx
    have hbad : ε < |Z x - t| := lt_of_not_ge hx
    have ht := abs_sub_le (Z x) (∫ y, Z y ∂P) t
    change ε / 2 ≤ |Z x - ∫ y, Z y ∂P|
    linarith
  exact (measure_mono hsub).trans
    ((meas_ge_le_variance_div_sq hZ (c := ε / 2) (by positivity)).trans
      (ENNReal.ofReal_le_ofReal hvar))

private theorem quartic_rectangle_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z0 Z1 : Ω → ℝ)
    (hZm0 : Measurable Z0) (hZm1 : Measurable Z1) (hZ0 : MemLp Z0 2 P) (hZ1 : MemLp Z1 2 P)
    (t0 t1 ε0 ε1 : ℝ) (hε0 : 0 < ε0) (hε1 : 0 < ε1)
    (hm0 : |∫ x, Z0 x ∂P - t0| ≤ ε0 / 2) (hm1 : |∫ x, Z1 x ∂P - t1| ≤ ε1 / 2)
    (hv0 : variance Z0 P / (ε0 / 2) ^ 2 ≤ 1 / 4)
    (hv1 : variance Z1 P / (ε1 / 2) ^ 2 ≤ 1 / 4) :
    ENNReal.ofReal (1 / 2) ≤ P {x | |Z0 x - t0| ≤ ε0 ∧ |Z1 x - t1| ≤ ε1} := by
  let C0 := {x | |Z0 x - t0| ≤ ε0}
  let C1 := {x | |Z1 x - t1| ≤ ε1}
  have hC0 : MeasurableSet C0 := measurableSet_le (hZm0.sub measurable_const).abs measurable_const
  have hC1 : MeasurableSet C1 := measurableSet_le (hZm1.sub measurable_const).abs measurable_const
  have hb0 := quartic_bad_probability P Z0 hZm0 hZ0 t0 ε0 hε0 hm0 hv0
  have hb1 := quartic_bad_probability P Z1 hZm1 hZ1 t1 ε1 hε1 hm1 hv1
  have hbad : P (C0 ∩ C1)ᶜ ≤ ENNReal.ofReal (1 / 2) := by
    rw [compl_inter]
    refine (measure_union_le _ _).trans ((add_le_add hb0 hb1).trans_eq ?_)
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  have htotal := prob_add_prob_compl (μ := P) (hC0.inter hC1)
  change ENNReal.ofReal (1 / 2) ≤ P (C0 ∩ C1)
  apply ENNReal.le_of_add_le_add_right (measure_ne_top P (C0 ∩ C1)ᶜ)
  calc
    _ ≤ ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2) := add_le_add le_rfl hbad
    _ = 1 := by rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
    _ = _ := htotal.symm

private theorem quartic_posterior_coordinate_memLp (N : ℕ+) (w : Fin 2 → ℝ) (j : Fin 2) :
    MemLp (fun x : ParticleSpace 1 N => posteriorCenter quarticHubbardD quarticHubbardField
      quarticHubbardFeature N x j) 2
        (Measure.pi fun _ : Fin N => siteLaw quarticHubbardU quarticHubbardFeature (DGPS.haar 1) w) := by
  letI := isProbabilityMeasure_siteLaw quartic_hubbard_hyp (m := DGPS.haar 1) w
  have hs : IsSmoothPeriodicParticle (fun x : ParticleSpace 1 N =>
      posteriorCenter quarticHubbardD quarticHubbardField quarticHubbardFeature N x j) := by
    fin_cases j
    · have he : (fun x => posteriorCenter quarticHubbardD quarticHubbardField
          quarticHubbardFeature N x 0) = quarticEmpiricalCos N := by
        funext x
        rw [quartic_empirical_coordinates]
        rfl
      change IsSmoothPeriodicParticle (fun x => posteriorCenter quarticHubbardD
        quarticHubbardField quarticHubbardFeature N x (0 : Fin 2))
      rw [he]
      exact quartic_empirical_cos_smooth N
    · have he : (fun x => posteriorCenter quarticHubbardD quarticHubbardField
          quarticHubbardFeature N x 1) = quarticEmpiricalSin N := by
        funext x
        rw [quartic_empirical_coordinates]
        rfl
      change IsSmoothPeriodicParticle (fun x => posteriorCenter quarticHubbardD
        quarticHubbardField quarticHubbardFeature N x (1 : Fin 2))
      rw [he]
      exact quartic_empirical_sin_smooth N
  obtain ⟨hm, B, hB⟩ := measurable_bounded_of_smooth hs
  exact MemLp.of_bound hm.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)

private theorem quartic_variance_ratio (V N : ℝ) (hN : 0 < N) :
    (V / N) / (N ^ (-(1 / 4 : ℝ)) / 2) ^ 2 = 4 * V * N ^ (-(1 / 2 : ℝ)) := by
  have hs : 0 < N ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hN _
  have hs2 : (N ^ (-(1 / 4 : ℝ))) ^ 2 = N ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    congr 1
    norm_num
  have hp : N * N ^ (-(1 / 2 : ℝ)) = N ^ (1 / 2 : ℝ) := by
    calc
      _ = N ^ (1 : ℝ) * N ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
      _ = N ^ ((1 : ℝ) + -(1 / 2 : ℝ)) := (Real.rpow_add hN _ _).symm
      _ = _ := by norm_num
  calc
    _ = 4 * V / (N * (N ^ (-(1 / 4 : ℝ))) ^ 2) := by field_simp [hN.ne', hs.ne']; ring
    _ = _ := by rw [hs2, hp, div_eq_mul_inv, ← Real.rpow_neg hN.le]

/-- A single fixed smaller latent core has conditional canonical-core probability
at least one half for every sufficiently large N. Constants precede N and the field. -/
theorem quartic_conditional_core_probability :
    ∃ k : ℝ, 0 < k ∧ k ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → ∃ M : ℝ, 1 ≤ M ∧
      ∀ N : ℕ+, M ≤ (N : ℝ) → ∀ w : Fin 2 → ℝ,
        |w 0 + 4| ≤ (k * (N : ℝ) ^ (-(1 / 4 : ℝ))) ^ 2 →
        |w 1| ≤ k * (N : ℝ) ^ (-(1 / 4 : ℝ)) →
        ENNReal.ofReal (1 / 2) ≤
          (Measure.pi fun _ : Fin N => siteLaw quarticHubbardU quarticHubbardFeature (DGPS.haar 1) w)
            {x | |posteriorCenter quarticHubbardD quarticHubbardField quarticHubbardFeature N x 0 + 4| ≤ δ / 2 ∧
              |posteriorCenter quarticHubbardD quarticHubbardField quarticHubbardFeature N x 1| ≤
                (N : ℝ) ^ (-(1 / 4 : ℝ))} := by
  obtain ⟨r, C, hr, hC, hmean⟩ := quartic_conditional_mean_local_bound
  obtain ⟨V, hV, hmom⟩ := quartic_conditional_field_moments
  let k := min 1 (1 / (8 * (C + 1)))
  have hk : 0 < k := lt_min zero_lt_one (by positivity)
  have hk1 : k ≤ 1 := min_le_left _ _
  have hCk : C * k ≤ 1 / 8 := by
    have h := (le_div_iff₀ (by positivity : 0 < 8 * (C + 1))).mp (min_le_right 1 (1 / (8 * (C + 1))))
    change k * (8 * (C + 1)) ≤ 1 at h
    nlinarith [hk.le]
  refine ⟨k, hk, hk1, fun δ hδ => ?_⟩
  have hsLim := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  have hVxLim : Tendsto (fun N : ℝ => (V / N) / (δ / 4) ^ 2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, zero_mul] using
      (tendsto_inv_atTop_zero.const_mul V).div_const ((δ / 4) ^ 2)
  have hVyLim : Tendsto (fun N : ℝ => (V / N) / (N ^ (-(1 / 4 : ℝ)) / 2) ^ 2) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (4 * V)
    rw [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
    exact (quartic_variance_ratio V N (lt_of_lt_of_le zero_lt_one hN)).symm
  have hsmall : ∀ᶠ N : ℝ in atTop,
      N ^ (-(1 / 4 : ℝ)) ≤ min 1 (min r δ) ∧
      (V / N) / (δ / 4) ^ 2 ≤ 1 / 4 ∧
      (V / N) / (N ^ (-(1 / 4 : ℝ)) / 2) ^ 2 ≤ 1 / 4 := by
    filter_upwards [hsLim.eventually (gt_mem_nhds (lt_min zero_lt_one (lt_min hr hδ))),
      hVxLim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
      hVyLim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))] with N hs hx hy
    exact ⟨hs.le, hx.le, hy.le⟩
  obtain ⟨M, hM⟩ := eventually_atTop.mp hsmall
  refine ⟨max 1 M, le_max_left _ _, fun N hN w hw0 hw1 => ?_⟩
  have hNp : 0 < (N : ℝ) := by exact_mod_cast N.pos
  let s := (N : ℝ) ^ (-(1 / 4 : ℝ))
  have hs : 0 < s := Real.rpow_pos_of_pos hNp _
  have hbounds := hM (N : ℝ) ((le_max_right _ _).trans hN)
  have hs1 : s ≤ 1 := hbounds.1.trans (min_le_left _ _)
  have hsr : s ≤ r := hbounds.1.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsδ : s ≤ δ := hbounds.1.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hks : k * s ≤ s := mul_le_of_le_one_left hs.le hk1
  have hks2 : (k * s) ^ 2 ≤ k * s := by
    have hm := mul_nonneg (mul_nonneg hk.le hs.le) (sub_nonneg.mpr (hks.trans hs1))
    nlinarith only [hm]
  have hwNorm : ‖w - ![-4, 0]‖ ≤ k * s := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg hk.le hs.le)]
    intro j
    fin_cases j
    · simpa [Real.norm_eq_abs] using hw0.trans hks2
    · simpa [Real.norm_eq_abs, s] using hw1
  have hmNorm : ‖quarticConditionalFieldMean w - ![-4, 0]‖ ≤ s / 8 :=
    (hmean w (hwNorm.trans (hks.trans hsr))).trans
      ((mul_le_mul_of_nonneg_left hwNorm hC.le).trans (by nlinarith [mul_le_mul_of_nonneg_right hCk hs.le]))
  have hmcoord := (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ s / 8)).mp hmNorm
  let P := Measure.pi fun _ : Fin N => siteLaw quarticHubbardU quarticHubbardFeature (DGPS.haar 1) w
  letI := isProbabilityMeasure_siteLaw quartic_hubbard_hyp (m := DGPS.haar 1) w
  let Z0 := fun x : ParticleSpace 1 N => posteriorCenter quarticHubbardD quarticHubbardField quarticHubbardFeature N x 0
  let Z1 := fun x : ParticleSpace 1 N => posteriorCenter quarticHubbardD quarticHubbardField quarticHubbardFeature N x 1
  have hZm0 : Measurable Z0 := (measurable_pi_apply 0).comp (measurable_posteriorCenter quartic_hubbard_hyp quarticHubbardD quarticHubbardField N)
  have hZm1 : Measurable Z1 := (measurable_pi_apply 1).comp (measurable_posteriorCenter quartic_hubbard_hyp quarticHubbardD quarticHubbardField N)
  have hZ0 : MemLp Z0 2 P := quartic_posterior_coordinate_memLp N w 0
  have hZ1 : MemLp Z1 2 P := quartic_posterior_coordinate_memLp N w 1
  have hm0 : |∫ x, Z0 x ∂P - (-4)| ≤ (δ / 2) / 2 := by
    rw [(hmom N w 0).1]
    have h := hmcoord 0
    simp only [Pi.sub_apply, Matrix.cons_val_zero, Real.norm_eq_abs, sub_neg_eq_add] at h
    simp only [sub_neg_eq_add]
    linarith
  have hm1 : |∫ x, Z1 x ∂P - 0| ≤ s / 2 := by
    rw [(hmom N w 1).1]
    have h := hmcoord 1
    simp only [Pi.sub_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Real.norm_eq_abs, sub_zero] at h ⊢
    linarith
  have hv0 : variance Z0 P ≤ V / (N : ℝ) := by
    rw [variance_eq_integral hZ0.aestronglyMeasurable.aemeasurable, (hmom N w 0).1]
    exact (hmom N w 0).2
  have hv1 : variance Z1 P ≤ V / (N : ℝ) := by
    rw [variance_eq_integral hZ1.aestronglyMeasurable.aemeasurable, (hmom N w 1).1]
    exact (hmom N w 1).2
  have hprob := quartic_rectangle_probability P Z0 Z1 hZm0 hZm1 hZ0 hZ1 (-4) 0 (δ / 2) s
    (by positivity) hs hm0 hm1
    ((div_le_div_of_nonneg_right hv0 (sq_nonneg ((δ / 2) / 2))).trans
      (by convert hbounds.2.1 using 1 <;> ring))
    ((div_le_div_of_nonneg_right hv1 (sq_nonneg (s / 2))).trans hbounds.2.2)
  simpa only [Z0, Z1, P, s, sub_neg_eq_add, sub_zero] using hprob

end DGPS.FiniteN
