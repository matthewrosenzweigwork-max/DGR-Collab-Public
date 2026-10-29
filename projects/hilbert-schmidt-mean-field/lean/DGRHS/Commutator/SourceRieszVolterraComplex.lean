import DGRHS.Commutator.SourceRieszVolterraComparison

/- DGR source3971--3997: complex finite Volterra comparison by real components.
Properness of each projected integral is proved. No stochastic exponential
identity, desired factorization, or limit appears among the hypotheses. -/
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace DGRHS.Commutator

theorem sourceRiesz_complex_volterra_comparison {chi f : ℝ → ℂ} {m : ℝ → ℝ}
    {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hm : IntervalIntegrable m volume 0 T)
    (hp : IntervalIntegrable (fun t => (m t : ℂ) * chi t) volume 0 T)
    (hf : IntervalIntegrable f volume 0 T)
    (hmb : ∀ t ∈ Icc 0 T, 0 ≤ m t ∧ m t ≤ C)
    (hchi : ∀ t ∈ Icc 0 T,
      chi t = chi 0 - ∫ r in 0..t, (m r : ℂ) * chi r + f r) :
    ‖chi T - chi 0 * (Real.exp (-(∫ t in 0..T, m t)) : ℂ)‖ ≤
      2 * Real.exp (C * T) * ∫ t in 0..T, ‖f t‖ := by
  have hpr : IntervalIntegrable (fun t => m t * (chi t).re) volume 0 T := by
    constructor
    · simpa [IntegrableOn] using Complex.reCLM.integrable_comp hp.1
    · simpa [IntegrableOn] using Complex.reCLM.integrable_comp hp.2
  have hpi : IntervalIntegrable (fun t => m t * (chi t).im) volume 0 T := by
    constructor
    · simpa [IntegrableOn] using Complex.imCLM.integrable_comp hp.1
    · simpa [IntegrableOn] using Complex.imCLM.integrable_comp hp.2
  have hfr : IntervalIntegrable (fun t => (f t).re) volume 0 T :=
    ⟨Complex.reCLM.integrable_comp hf.1, Complex.reCLM.integrable_comp hf.2⟩
  have hfi : IntervalIntegrable (fun t => (f t).im) volume 0 T :=
    ⟨Complex.imCLM.integrable_comp hf.1, Complex.imCLM.integrable_comp hf.2⟩
  have hqr : ∀ t ∈ Icc 0 T, (chi t).re = (chi 0).re -
      ∫ r in 0..t, m r * (chi r).re + (f r).re := by
    intro t ht
    have hpt : IntervalIntegrable (fun r => (m r : ℂ) * chi r + f r) volume 0 t := (hp.add hf).mono_set (by
      rw [uIcc_of_le hT, uIcc_of_le ht.1]
      intro r hr
      exact ⟨hr.1, hr.2.trans ht.2⟩)
    have hh := congrArg Complex.re (hchi t ht)
    simp only [Complex.sub_re] at hh
    have hhI : (∫ r in 0..t, (m r : ℂ) * chi r + f r).re =
        ∫ r in 0..t, m r * (chi r).re + (f r).re := by
      simpa using (Complex.reCLM.intervalIntegral_comp_comm hpt).symm
    rw [hhI] at hh
    exact hh
  have hqi : ∀ t ∈ Icc 0 T, (chi t).im = (chi 0).im -
      ∫ r in 0..t, m r * (chi r).im + (f r).im := by
    intro t ht
    have hpt : IntervalIntegrable (fun r => (m r : ℂ) * chi r + f r) volume 0 t := (hp.add hf).mono_set (by
      rw [uIcc_of_le hT, uIcc_of_le ht.1]
      intro r hr
      exact ⟨hr.1, hr.2.trans ht.2⟩)
    have hh := congrArg Complex.im (hchi t ht)
    simp only [Complex.sub_im] at hh
    have hhI : (∫ r in 0..t, (m r : ℂ) * chi r + f r).im =
        ∫ r in 0..t, m r * (chi r).im + (f r).im := by
      simpa using (Complex.imCLM.intervalIntegral_comp_comm hpt).symm
    rw [hhI] at hh
    exact hh
  have hr := sourceRiesz_real_volterra_comparison hT hC hm hpr hfr hmb hqr
  have hi := sourceRiesz_real_volterra_comparison hT hC hm hpi hfi hmb hqi
  have hbr : (∫ t in 0..T, |(f t).re|) ≤ ∫ t in 0..T, ‖f t‖ :=
    intervalIntegral.integral_mono_on hT hfr.abs hf.norm
      (fun t _ => Complex.abs_re_le_norm (f t))
  have hbi : (∫ t in 0..T, |(f t).im|) ≤ ∫ t in 0..T, ‖f t‖ :=
    intervalIntegral.integral_mono_on hT hfi.abs hf.norm
      (fun t _ => Complex.abs_im_le_norm (f t))
  let z := chi T - chi 0 * (Real.exp (-(∫ t in 0..T, m t)) : ℂ)
  have hr' : |z.re| ≤ Real.exp (C * T) * ∫ t in 0..T, ‖f t‖ := by
    have hh : |z.re| ≤ Real.exp (C * T) * ∫ t in 0..T, |(f t).re| := by simpa only [z, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using hr
    exact hh.trans
      (mul_le_mul_of_nonneg_left hbr (Real.exp_pos _).le)
  have hi' : |z.im| ≤ Real.exp (C * T) * ∫ t in 0..T, ‖f t‖ := by
    have hh : |z.im| ≤ Real.exp (C * T) * ∫ t in 0..T, |(f t).im| := by simpa only [z, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] using hi
    exact hh.trans
      (mul_le_mul_of_nonneg_left hbi (Real.exp_pos _).le)
  have hn : ‖z‖ ≤ |z.re| + |z.im| := by
    calc
      ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ := congrArg norm (Complex.re_add_im z).symm
      _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = _ := by simp [Real.norm_eq_abs]
  exact hn.trans ((add_le_add hr' hi').trans_eq (by ring))

#check sourceRiesz_complex_volterra_comparison
#print axioms sourceRiesz_complex_volterra_comparison
end DGRHS.Commutator
