import LeanResearch.PeriodicAttractiveLogGas.CenteredL2

/-! The supplied reverse-L2-triangle proof of source
`lem:entropy-one-site-crossing`, lines 2853–2872. All component moments are
actual finite integrals derived from L2 membership under the positive mixture. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PeriodicAttractiveLogGas.ConditionalNormCrossing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Reverse L2 triangle against a real constant, with literal second moments. -/
theorem reverse_norm_constant {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : MemLp f 2 μ) (c : ℝ) :
    abs (Real.sqrt (∫ x, f x ^ 2 ∂μ) - |c|) ≤
      Real.sqrt (∫ x, (f x - c) ^ 2 ∂μ) := by
  let u := hf.toLp f
  let v : Lp ℝ 2 μ := Lp.const 2 μ c
  have hu : ‖u‖ ^ 2 = ∫ x, f x ^ 2 ∂μ :=
    CenteredL2.norm_sq_eq_integral_sq_representative μ u hf.coeFn_toLp
  have hv : ‖v‖ ^ 2 = c ^ 2 := by
    simpa using CenteredL2.norm_sq_eq_integral_sq_representative μ v
      (Lp.coeFn_const 2 μ c)
  have huv : ‖u - v‖ ^ 2 = ∫ x, (f x - c) ^ 2 ∂μ := by
    apply CenteredL2.norm_sq_eq_integral_sq_representative
    filter_upwards [Lp.coeFn_sub u v, hf.coeFn_toLp, Lp.coeFn_const 2 μ c] with x hs hf' hc
    change (u - v) x = u x - v x at hs
    rw [hs, hf', hc]
    rfl
  have hvc : ‖v‖ = |c| := by
    nlinarith [norm_nonneg v, abs_nonneg c, sq_abs c]
  rw [← hu, ← huv, Real.sqrt_sq (norm_nonneg u), Real.sqrt_sq (norm_nonneg (u - v)), ← hvc]
  exact abs_norm_sub_norm_le u v

/-- The squared reverse comparison, useful before centering. -/
theorem reverse_norm_constant_sq {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : MemLp f 2 μ) (c : ℝ) :
    (Real.sqrt (∫ x, f x ^ 2 ∂μ) - |c|) ^ 2 ≤ ∫ x, (f x - c) ^ 2 ∂μ := by
  have hh := reverse_norm_constant hf c
  have hn : 0 ≤ ∫ x, (f x - c) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hh' := mul_self_le_mul_self (abs_nonneg _) hh
  simpa only [← sq, sq_abs, Real.sq_sqrt hn] using hh'

/-- Positive mixture weights supply the component L2 hypotheses. -/
theorem component_memLp {ν νa νb : Measure Ω} {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1)
    (hmix : ν = ENNReal.ofReal q • νa + ENNReal.ofReal (1 - q) • νb)
    {f : Ω → ℝ} (hf : MemLp f 2 ν) : MemLp f 2 νa ∧ MemLp f 2 νb := by
  rw [hmix] at hf
  have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  have hr0 : ENNReal.ofReal (1 - q) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (sub_pos.mpr hq1)).ne'
  constructor
  · have h := hf.left_of_add_measure.smul_measure
      (c := (ENNReal.ofReal q)⁻¹) (by simp [hq0])
    simpa only [smul_smul, ENNReal.inv_mul_cancel hq0 ENNReal.ofReal_ne_top,
      one_smul] using h
  · have h := hf.right_of_add_measure.smul_measure
      (c := (ENNReal.ofReal (1 - q))⁻¹) (by simp [hr0])
    simpa only [smul_smul, ENNReal.inv_mul_cancel hr0 ENNReal.ofReal_ne_top,
      one_smul] using h

/-- The literal convex mixture is itself a probability law. -/
theorem mixture_probability {ν νa νb : Measure Ω}
    [IsProbabilityMeasure νa] [IsProbabilityMeasure νb] {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hmix : ν = ENNReal.ofReal q • νa + ENNReal.ofReal (1 - q) • νb) :
    IsProbabilityMeasure ν := by
  constructor
  rw [hmix]
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hq (sub_nonneg.mpr hq1)]
  norm_num

/-- The actual mean and both component second moments are finite. -/
theorem mixture_integrability {ν νa νb : Measure Ω}
    [IsProbabilityMeasure νa] [IsProbabilityMeasure νb] {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1)
    (hmix : ν = ENNReal.ofReal q • νa + ENNReal.ofReal (1 - q) • νb)
    {f : Ω → ℝ} (hf : MemLp f 2 ν) :
    Integrable f ν ∧ Integrable (fun x => f x ^ 2) νa ∧
      Integrable (fun x => f x ^ 2) νb := by
  let := mixture_probability hq.le hq1.le hmix
  obtain ⟨ha, hb⟩ := component_memLp hq hq1 hmix hf
  exact ⟨hf.integrable (by norm_num), ha.integrable_sq, hb.integrable_sq⟩

/-- Actual mixture integrals, once component integrability has been derived. -/
theorem integral_mixture {ν νa νb : Measure Ω} {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hmix : ν = ENNReal.ofReal q • νa + ENNReal.ofReal (1 - q) • νb)
    {g : Ω → ℝ} (ha : Integrable g νa) (hb : Integrable g νb) :
    (∫ x, g x ∂ν) = q * (∫ x, g x ∂νa) + (1 - q) * (∫ x, g x ∂νb) := by
  rw [hmix, integral_add_measure (ha.smul_measure ENNReal.ofReal_ne_top)
    (hb.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal hq, ENNReal.toReal_ofReal (sub_nonneg.mpr hq1),
    smul_eq_mul, smul_eq_mul]

/-- The supplied comparison holds against every real constant, before choosing
that constant to be the actual mixture mean. -/
theorem crossing_le_centered_second_moment {ν νa νb : Measure Ω}
    [IsProbabilityMeasure νa] [IsProbabilityMeasure νb] {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1)
    (hmix : ν = ENNReal.ofReal q • νa + ENNReal.ofReal (1 - q) • νb)
    {f : Ω → ℝ} (hf : MemLp f 2 ν) (c : ℝ) :
    q * (1 - q) * (Real.sqrt (∫ x, f x ^ 2 ∂νa) -
      Real.sqrt (∫ x, f x ^ 2 ∂νb)) ^ 2 ≤ 2 * ∫ x, (f x - c) ^ 2 ∂ν := by
  obtain ⟨ha, hb⟩ := component_memLp hq hq1 hmix hf
  have ha' : Integrable (fun x => (f x - c) ^ 2) νa :=
    (ha.sub (memLp_const c)).integrable_sq
  have hb' : Integrable (fun x => (f x - c) ^ 2) νb :=
    (hb.sub (memLp_const c)).integrable_sq
  have hra := reverse_norm_constant_sq ha c
  have hrb := reverse_norm_constant_sq hb c
  have hA : 0 ≤ ∫ x, (f x - c) ^ 2 ∂νa := integral_nonneg fun x => sq_nonneg _
  have hB : 0 ≤ ∫ x, (f x - c) ^ 2 ∂νb := integral_nonneg fun x => sq_nonneg _
  have htwo : (Real.sqrt (∫ x, f x ^ 2 ∂νa) - Real.sqrt (∫ x, f x ^ 2 ∂νb)) ^ 2 ≤
      2 * ((∫ x, (f x - c) ^ 2 ∂νa) + ∫ x, (f x - c) ^ 2 ∂νb) := by
    nlinarith [sq_nonneg (Real.sqrt (∫ x, f x ^ 2 ∂νa) +
      Real.sqrt (∫ x, f x ^ 2 ∂νb) - 2 * |c|)]
  have hweighted := mul_le_mul_of_nonneg_left htwo
    (mul_nonneg hq.le (sub_nonneg.mpr hq1.le))
  rw [integral_mixture hq.le hq1.le hmix ha' hb']
  nlinarith [mul_nonneg (sq_nonneg q) hA, mul_nonneg (sq_nonneg (1 - q)) hB]

/-- Source `lem:entropy-one-site-crossing`: no separate component moment or
integrability assumptions are imposed. -/
theorem one_site_crossing {ν νa νb : Measure Ω}
    [IsProbabilityMeasure νa] [IsProbabilityMeasure νb] {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1)
    (hmix : ν = ENNReal.ofReal q • νa + ENNReal.ofReal (1 - q) • νb)
    {f : Ω → ℝ} (hf : MemLp f 2 ν) :
    q * (1 - q) * (Real.sqrt (∫ x, f x ^ 2 ∂νa) -
      Real.sqrt (∫ x, f x ^ 2 ∂νb)) ^ 2 ≤ 2 * ProbabilityTheory.variance f ν := by
  let := mixture_probability hq.le hq1.le hmix
  rw [ProbabilityTheory.variance_eq_integral hf.aemeasurable]
  exact crossing_le_centered_second_moment hq hq1 hmix hf (∫ x, f x ∂ν)

end PeriodicAttractiveLogGas.ConditionalNormCrossing
