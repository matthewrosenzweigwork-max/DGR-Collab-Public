import DGRHS.Dynamics.SourceDiffusiveFactors

noncomputable section
open MeasureTheory Set Filter
open scoped Interval ENNReal
namespace DGRHS.Dynamics

/-- Nonnegative extended interpretation of the exponent in source A. -/
def sourceExponent (a : ℝ → ℝ) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioc 0 T, ENNReal.ofReal (a t)

/-- Extended exponential, with exp(infinity)=infinity, rather than a totalized integral. -/
def extendedSourceA (a : ℝ → ℝ) (T : ℝ) : ℝ≥0∞ :=
  if sourceExponent a T = ∞ then ∞ else
    ENNReal.ofReal (Real.exp (sourceExponent a T).toReal)

def extendedSourceB (a b : ℝ → ℝ) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioc 0 T, ENNReal.ofReal (Real.exp (∫ r in t..T, a r) * b t)

theorem extendedSourceA_finite_iff {a : ℝ → ℝ} {T : ℝ} :
    extendedSourceA a T ≠ ∞ ↔ sourceExponent a T ≠ ∞ := by
  unfold extendedSourceA
  split_ifs with h <;> simp [h]

/-- Source finiteness genuinely implies both coefficient integrability obligations. -/
theorem coefficients_integrable_of_finite_factors {a b : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hma : AEStronglyMeasurable a volume)
    (hmb : AEStronglyMeasurable b volume)
    (hna : ∀ᵐ t ∂volume, 0 ≤ a t) (hnb : ∀ᵐ t ∂volume, 0 ≤ b t)
    (hA : extendedSourceA a T ≠ ∞) (hB : extendedSourceB a b T ≠ ∞) :
    IntervalIntegrable a volume 0 T ∧ IntervalIntegrable b volume 0 T := by
  have hia : Integrable a (volume.restrict (Ioc 0 T)) :=
    (lintegral_ofReal_ne_top_iff_integrable hma.restrict
      (ae_restrict_of_ae hna)).mp (extendedSourceA_finite_iff.mp hA)
  have ha : IntervalIntegrable a volume 0 T := by
    rw [intervalIntegrable_iff, uIoc_of_le hT]
    exact hia
  have hle : (fun t => ENNReal.ofReal (b t)) ≤ᵐ[volume.restrict (Ioc 0 T)]
      (fun t => ENNReal.ofReal (Real.exp (∫ r in t..T, a r) * b t)) := by
    change ∀ᵐ t ∂volume.restrict (Ioc 0 T), _
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hnb] with t hbt ht
    have hw : 1 ≤ Real.exp (∫ r in t..T, a r) :=
      Real.one_le_exp_iff.mpr (intervalIntegral.integral_nonneg_of_ae ht.2 hna)
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  have hbfinite : (∫⁻ t in Ioc 0 T, ENNReal.ofReal (b t)) ≠ ∞ :=
    (lt_of_le_of_lt (lintegral_mono_ae hle) (lt_top_iff_ne_top.mpr hB)).ne
  have hib : Integrable b (volume.restrict (Ioc 0 T)) :=
    (lintegral_ofReal_ne_top_iff_integrable hmb.restrict
      (ae_restrict_of_ae hnb)).mp hbfinite
  refine ⟨ha, ?_⟩
  rw [intervalIntegrable_iff, uIoc_of_le hT]
  exact hib

/-- Proper extended factors discharge, rather than assume, the required coefficient L1 bounds. -/
theorem source_diffusive_gronwall_finite {E a b J : ℝ → ℝ} {T : ℝ} {N : ℕ}
    (hN : 0 < N) (hT : 0 ≤ T) (hE : AbsolutelyContinuousOnInterval E 0 T)
    (hma : AEStronglyMeasurable a volume) (hmb : AEStronglyMeasurable b volume)
    (hna : ∀ᵐ t ∂volume, 0 ≤ a t) (hnb : ∀ᵐ t ∂volume, 0 ≤ b t)
    (hA : extendedSourceA a T ≠ ∞) (hB : extendedSourceB a b T ≠ ∞)
    (hd : ∀ᵐ t ∂volume, t ∈ Ioo 0 T → deriv E t ≤ |J t| / N)
    (hc : ∀ᵐ t ∂volume, t ∈ Ioo 0 T → |J t| ≤ a t * N * E t + b t) :
    E T ≤ sourceA a T * E 0 + sourceB a b T / N := by
  obtain ⟨ha, hb⟩ := coefficients_integrable_of_finite_factors hT hma hmb hna hnb hA hB
  exact source_diffusive_gronwall hN hT hE ha hb hd hc

#print axioms extendedSourceA_finite_iff
#print axioms coefficients_integrable_of_finite_factors
#print axioms source_diffusive_gronwall_finite
end DGRHS.Dynamics
