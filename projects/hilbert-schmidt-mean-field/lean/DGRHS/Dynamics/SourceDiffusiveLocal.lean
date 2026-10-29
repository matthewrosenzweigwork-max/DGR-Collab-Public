import DGRHS.Dynamics.SourceDiffusiveProperness

noncomputable section
open MeasureTheory Set Filter
open scoped Interval ENNReal
namespace DGRHS.Dynamics

theorem sourceB_integrable {a b : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T) (hb : IntervalIntegrable b volume 0 T) :
    IntervalIntegrable (fun t => Real.exp (∫ r in t..T, a r) * b t) volume 0 T := by
  have hI := ha.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  have hcont : ContinuousOn (fun t => Real.exp ((∫ r in 0..T, a r) -
      ∫ r in 0..t, a r)) (uIcc 0 T) :=
    Real.continuous_exp.comp_continuousOn (continuousOn_const.sub hI.continuousOn)
  apply (hb.continuousOn_mul hcont).congr
  intro t ht
  have htT : t ∈ Icc 0 T := by simpa [uIcc_of_le hT] using uIoc_subset_uIcc ht
  have hat : IntervalIntegrable a volume 0 t := ha.mono_set (by
    rw [uIcc_of_le htT.1, uIcc_of_le hT]
    exact Icc_subset_Icc le_rfl htT.2)
  dsimp only
  rw [intervalIntegral.integral_interval_sub_left ha hat]

theorem extendedSourceA_toReal {a : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T) (hna : ∀ᵐ t ∂volume, 0 ≤ a t) :
    (extendedSourceA a T).toReal = sourceA a T := by
  have hfinite : sourceExponent a T ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable ha.aestronglyMeasurable
      (ae_restrict_of_ae hna)).mpr ha.1
  rw [extendedSourceA, ite_eq_right hfinite, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  unfold sourceA sourceExponent
  rw [intervalIntegral.integral_of_le hT,
    integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hna) ha.aestronglyMeasurable]

theorem extendedSourceB_toReal {a b : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T) (hb : IntervalIntegrable b volume 0 T)
    (hnb : ∀ᵐ t ∂volume, 0 ≤ b t) :
    (extendedSourceB a b T).toReal = sourceB a b T := by
  have hi := sourceB_integrable hT ha hb
  have hn : ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      0 ≤ Real.exp (∫ r in t..T, a r) * b t := by
    filter_upwards [ae_restrict_of_ae hnb] with t ht
    exact mul_nonneg (Real.exp_pos _).le ht
  unfold extendedSourceB sourceB
  rw [intervalIntegral.integral_of_le hT,
    integral_eq_lintegral_of_nonneg_ae hn hi.aestronglyMeasurable]

/-- Finite-horizon exhaustion covers finite or infinite original lifespans. -/
theorem source_diffusive_gronwall_local {E a b J : ℝ → ℝ} {N : ℕ} {Tstar : ℝ≥0∞}
    (hN : 0 < N)
    (hE : ∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar → AbsolutelyContinuousOnInterval E 0 T)
    (hma : AEStronglyMeasurable a volume) (hmb : AEStronglyMeasurable b volume)
    (hna : ∀ᵐ t ∂volume, 0 ≤ a t) (hnb : ∀ᵐ t ∂volume, 0 ≤ b t)
    (hA : ∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar → extendedSourceA a T ≠ ∞)
    (hB : ∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar → extendedSourceB a b T ≠ ∞)
    (hd : ∀ᵐ t ∂volume, 0 < t → ENNReal.ofReal t < Tstar → deriv E t ≤ |J t| / N)
    (hc : ∀ᵐ t ∂volume, 0 < t → ENNReal.ofReal t < Tstar →
      |J t| ≤ a t * N * E t + b t) :
    ∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar →
      E T ≤ sourceA a T * E 0 + sourceB a b T / N := by
  intro T hT htstar
  apply source_diffusive_gronwall_finite hN hT (hE T hT htstar) hma hmb hna hnb
    (hA T hT htstar) (hB T hT htstar)
  · filter_upwards [hd] with t ht htt
    exact ht htt.1 (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal htt.2.le) htstar)
  · filter_upwards [hc] with t ht htt
    exact ht htt.1 (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal htt.2.le) htstar)

#print axioms sourceB_integrable
#print axioms extendedSourceA_toReal
#print axioms extendedSourceB_toReal
#print axioms source_diffusive_gronwall_local
#check @source_diffusive_gronwall_local
end DGRHS.Dynamics
