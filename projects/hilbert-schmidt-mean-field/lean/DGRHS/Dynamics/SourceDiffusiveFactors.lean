import DGRHS.Dynamics.SourceDiffusiveGronwall

noncomputable section
open MeasureTheory Set Filter
open scoped Interval
namespace DGRHS.Dynamics

/-- Literal scalar factors in source eq:MFEGronwallFactors; properness is explicit below. -/
def sourceA (a : ℝ → ℝ) (t : ℝ) : ℝ := Real.exp (∫ r in 0..t, a r)
def sourceB (a b : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in 0..t, Real.exp (∫ r in s..t, a r) * b s

theorem sourceB_prefix {a b : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T) :
    sourceB a b T = sourceA a T *
      ∫ t in 0..T, b t * Real.exp (-(∫ r in 0..t, a r)) := by
  rw [sourceB, sourceA, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  filter_upwards with t ht
  have htT : t ∈ Icc 0 T := by
    exact uIoc_subset_uIcc ht |> (by simpa [uIcc_of_le hT] using ·)
  have hat : IntervalIntegrable a volume 0 t := ha.mono_set (by
    rw [uIcc_of_le htT.1, uIcc_of_le hT]
    exact Icc_subset_Icc le_rfl htT.2)
  rw [← intervalIntegral.integral_interval_sub_left ha hat,
    sub_eq_add_neg, Real.exp_add]
  ring

theorem variable_gronwall {E a b : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hE : AbsolutelyContinuousOnInterval E 0 T)
    (ha : IntervalIntegrable a volume 0 T) (hb : IntervalIntegrable b volume 0 T)
    (hd : ∀ᵐ t ∂volume, t ∈ Icc 0 T → deriv E t ≤ a t * E t + b t) :
    E T ≤ sourceA a T * E 0 + sourceB a b T := by
  rw [sourceB_prefix hT ha]
  exact variable_gronwall_prefix hT hE ha hb hd

/-- Endpoint-null passage preserves the source's open-time AE hypotheses. -/
theorem ae_closed_of_ae_open {P : ℝ → Prop} {T : ℝ}
    (h : ∀ᵐ t ∂volume, t ∈ Ioo 0 T → P t) :
    ∀ᵐ t ∂volume, t ∈ Icc 0 T → P t := by
  filter_upwards [h, (by simp [ae_iff] : ∀ᵐ (t : ℝ) ∂volume, t ≠ 0),
    (by simp [ae_iff] : ∀ᵐ (t : ℝ) ∂volume, t ≠ T)] with t ht ht0 htT htt
  exact ht ⟨lt_of_le_of_ne htt.1 (Ne.symm ht0), lt_of_le_of_ne htt.2 htT⟩

/-- Actual scalar dissipation plus actual entropic-commutator inequality, with source N. -/
theorem source_diffusive_gronwall {E a b J : ℝ → ℝ} {T : ℝ} {N : ℕ}
    (hN : 0 < N) (hT : 0 ≤ T) (hE : AbsolutelyContinuousOnInterval E 0 T)
    (ha : IntervalIntegrable a volume 0 T) (hb : IntervalIntegrable b volume 0 T)
    (hd : ∀ᵐ t ∂volume, t ∈ Ioo 0 T → deriv E t ≤ |J t| / N)
    (hc : ∀ᵐ t ∂volume, t ∈ Ioo 0 T → |J t| ≤ a t * N * E t + b t) :
    E T ≤ sourceA a T * E 0 + sourceB a b T / N := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hbn : IntervalIntegrable (fun t => b t / N) volume 0 T := by
    simpa [div_eq_mul_inv, mul_comm] using hb.const_mul ((N : ℝ)⁻¹)
  have hdiff : ∀ᵐ t ∂volume, t ∈ Icc 0 T →
      deriv E t ≤ a t * E t + b t / N := by
    apply ae_closed_of_ae_open
    filter_upwards [hd, hc] with t hdt hct ht
    calc
      deriv E t ≤ |J t| / N := hdt ht
      _ ≤ (a t * N * E t + b t) / N := div_le_div_of_nonneg_right (hct ht) hn.le
      _ = a t * E t + b t / N := by field_simp
  have H := variable_gronwall hT hE ha hbn hdiff
  simp only [sourceB] at H ⊢
  simp_rw [← mul_div_assoc] at H
  rw [intervalIntegral.integral_div] at H
  exact H

#print axioms sourceB_prefix
#print axioms variable_gronwall
#print axioms ae_closed_of_ae_open
#print axioms source_diffusive_gronwall
end DGRHS.Dynamics
