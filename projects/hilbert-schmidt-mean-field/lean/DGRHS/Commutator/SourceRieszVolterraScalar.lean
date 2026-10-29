import DGRHS.Dynamics.SourceDiffusiveGronwall

/-
DGR arXiv:2609.02743v1, source3971--3997, scalar Volterra comparison.
Source SHA256 6f52778d92aa534e2b5851ca0f6b0712dc56470259cb3efcb7146ac2384dac0c.
Analytic support only: the proper finite Ito identity must separately produce
absolute continuity and the AE differential equation. No stochastic identity,
terminal duality, characteristic factorization, or limit is assumed here.
Uses pinned Mathlib AC FTC through the unchanged checked variable Gronwall lemma.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Interval
namespace DGRHS.Commutator

/-- A proper real forced decay equation with a bounded nonnegative coefficient.
The derivative is only required AE; jump discontinuities of the coefficient are
allowed. The zero initial error yields an explicit L1 forcing bound. -/
theorem sourceRiesz_scalar_forced_decay_bound {e m f : ℝ → ℝ} {T C : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C)
    (he : AbsolutelyContinuousOnInterval e 0 T)
    (hm : IntervalIntegrable m volume 0 T)
    (hf : IntervalIntegrable f volume 0 T)
    (hmb : ∀ t ∈ Icc 0 T, 0 ≤ m t ∧ m t ≤ C)
    (hzero : e 0 = 0)
    (hd : ∀ᵐ t ∂volume, t ∈ Icc 0 T → deriv e t = -m t * e t + f t) :
    |e T| ≤ Real.exp (C * T) * ∫ t in 0..T, |f t| := by
  let I : ℝ → ℝ := fun t => ∫ r in 0..t, m r
  have hI : AbsolutelyContinuousOnInterval I 0 T :=
    hm.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hg : AbsolutelyContinuousOnInterval (fun t => Real.exp (I t)) 0 T :=
    DGRHS.Dynamics.absolutelyContinuous_exp hI
  have hw : IntervalIntegrable (fun t => |f t| * Real.exp (I t)) volume 0 T :=
    hf.abs.mul_continuousOn hg.continuousOn
  have hi : ∀ t ∈ Icc 0 T, 0 ≤ I t ∧ I t ≤ C * T := by
    intro t ht
    have hmt : IntervalIntegrable m volume 0 t := hm.mono_set (by
      rw [uIcc_of_le hT, uIcc_of_le ht.1]
      intro r hr
      exact ⟨hr.1, hr.2.trans ht.2⟩)
    have hn : 0 ≤ I t := intervalIntegral.integral_nonneg ht.1 (by
      intro r hr
      exact (hmb r ⟨hr.1, hr.2.trans ht.2⟩).1)
    have hu : I t ≤ C * t := by
      have hh := intervalIntegral.integral_mono_on ht.1 hmt
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume 0 t)
        (fun r hr => (hmb r ⟨hr.1, hr.2.trans ht.2⟩).2)
      simpa [I, intervalIntegral.integral_const, mul_comm] using hh
    exact ⟨hn, hu.trans (mul_le_mul_of_nonneg_left ht.2 hC)⟩
  have hwi : (∫ t in 0..T, |f t| * Real.exp (I t)) ≤
      Real.exp (C * T) * ∫ t in 0..T, |f t| := by
    have hh := intervalIntegral.integral_mono_on hT hw
      (hf.abs.const_mul (Real.exp (C * T))) (by
        intro t ht
        exact (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (hi t ht).2) (abs_nonneg (f t))).trans_eq (mul_comm _ _))
    simpa [intervalIntegral.integral_const_mul] using hh
  have hw0 : 0 ≤ ∫ t in 0..T, |f t| * Real.exp (I t) :=
    intervalIntegral.integral_nonneg hT (by
      intro t ht
      exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
  have hb : Real.exp (-I T) * (∫ t in 0..T, |f t| * Real.exp (I t)) ≤
      Real.exp (C * T) * ∫ t in 0..T, |f t| := by
    have hh : Real.exp (-I T) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (neg_nonpos.mpr (hi T ⟨hT, le_rfl⟩).1)
    exact (mul_le_of_le_one_left hw0 hh).trans hwi
  have hep : ∀ᵐ t ∂volume, t ∈ Icc 0 T →
      deriv e t ≤ (-m t) * e t + |f t| := by
    filter_upwards [hd] with t ht htT
    rw [ht htT]
    exact add_le_add le_rfl (le_abs_self (f t))
  have hen : ∀ᵐ t ∂volume, t ∈ Icc 0 T →
      deriv (fun r => -e r) t ≤ (-m t) * (-e t) + |f t| := by
    filter_upwards [hd, he.ae_differentiableAt] with t ht het htT
    have hder := (het (by simpa [uIcc_of_le hT] using htT)).hasDerivAt.neg.deriv
    change deriv (-e) t ≤ (-m t) * (-e t) + |f t|
    rw [hder, ht htT]
    have hh := neg_le_abs (f t)
    linarith
  have hp := DGRHS.Dynamics.variable_gronwall_prefix hT he hm.neg hf.abs hep
  have hn := DGRHS.Dynamics.variable_gronwall_prefix hT he.neg hm.neg hf.abs hen
  have hp' : e T ≤ Real.exp (C * T) * ∫ t in 0..T, |f t| := by
    apply le_trans _ hb
    simpa [intervalIntegral.integral_neg, hzero, I] using hp
  have hn' : -e T ≤ Real.exp (C * T) * ∫ t in 0..T, |f t| := by
    apply le_trans _ hb
    simpa [intervalIntegral.integral_neg, hzero, I] using hn
  exact abs_le.mpr ⟨by linarith, hp'⟩

#check sourceRiesz_scalar_forced_decay_bound
#print axioms sourceRiesz_scalar_forced_decay_bound
end DGRHS.Commutator
