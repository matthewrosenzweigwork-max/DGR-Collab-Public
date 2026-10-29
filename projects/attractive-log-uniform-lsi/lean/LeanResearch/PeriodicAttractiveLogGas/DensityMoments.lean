import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Density transfer for the Poincare and finite-moment part of source Lemma 3.2.

The measures, density, moments and energy below are actual objects.
Development evidence and separate semantic/protected statuses are recorded externally.
The only analytic input to the final transfer is the stated unweighted Sobolev
family. Rectangle instantiation, entropy, LSI and dilation are outside this file.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace PeriodicAttractiveLogGas.DensityMoments

variable {A : Type*} [MeasurableSpace A]
variable {μ ν : Measure A} {p f : A → ℝ} {c q K s : ℝ}

/-- A uniform real bound supplies genuine finite extended norms at every exponent. -/
theorem memLp_of_bounded [IsFiniteMeasure μ] (hf : Measurable f)
    (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) (r : ℝ≥0∞) : MemLp f r μ := by
  obtain ⟨M, hM⟩ := hb
  exact MemLp.of_bound hf.aestronglyMeasurable M
    (Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using hM x)

omit [MeasurableSpace A] in
theorem bounded_sub_const (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) (a : ℝ) :
    ∃ M : ℝ, ∀ x, |f x - a| ≤ M := by
  obtain ⟨M, hM⟩ := hb
  exact ⟨M + |a|, fun x ↦ (abs_sub _ _).trans (add_le_add (hM x) le_rfl)⟩

theorem memLp_norm_rpow_bounded [IsFiniteMeasure μ] (hf : Measurable f)
    (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) (hs : 0 ≤ s) (r : ℝ≥0∞) :
    MemLp (fun x ↦ ‖f x‖ ^ s) r μ := by
  obtain ⟨M, hM⟩ := hb
  apply MemLp.of_bound (hf.norm.pow_const s).aestronglyMeasurable ((max M 0) ^ s)
  exact Eventually.of_forall fun x ↦ by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    have hx : ‖f x‖ ≤ M := by simpa only [Real.norm_eq_abs] using hM x
    exact Real.rpow_le_rpow (norm_nonneg _) (hx.trans (le_max_left _ _)) hs

theorem integrable_norm_rpow_bounded [IsFiniteMeasure μ] (hf : Measurable f)
    (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) (hs : 0 ≤ s) :
    Integrable (fun x ↦ ‖f x‖ ^ s) μ :=
  (memLp_norm_rpow_bounded hf hb hs 1).integrable le_rfl

theorem lpNorm_ofReal_eq {E : Type*} [NormedAddCommGroup E]
    {μ : Measure A} {h : A → E} {r : ℝ} (hr : 0 < r)
    (hh : AEStronglyMeasurable h μ) :
    lpNorm h (ENNReal.ofReal r) μ = (∫ x, ‖h x‖ ^ r ∂μ) ^ (1 / r) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) ENNReal.ofReal_ne_top hh,
    ENNReal.toReal_ofReal hr.le, one_div]

theorem lpNorm_rpow_eq_integral {E : Type*} [NormedAddCommGroup E]
    {μ : Measure A} {h : A → E} {r : ℝ} (hr : 0 < r)
    (hh : AEStronglyMeasurable h μ) :
    lpNorm h (ENNReal.ofReal r) μ ^ r = ∫ x, ‖h x‖ ^ r ∂μ := by
  rw [lpNorm_ofReal_eq hr hh, one_div,
    Real.rpow_inv_rpow (integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _) hr.ne']

theorem lpNorm_norm_rpow {E : Type*} [NormedAddCommGroup E]
    {μ : Measure A} {h : A → E} {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (hh : AEStronglyMeasurable h μ) :
    lpNorm (fun x ↦ ‖h x‖ ^ t) (ENNReal.ofReal r) μ =
      lpNorm h (ENNReal.ofReal (t * r)) μ ^ t := by
  simp only [← toReal_eLpNorm]
  rw [eLpNorm_norm_rpow h hh ht, ← ENNReal.ofReal_mul hr.le,
    ENNReal.toReal_rpow, mul_comm r t]

/-- The actual Bochner integral under the actual density measure. Nonnegativity
is only almost everywhere; values on its exceptional null set are not changed. -/
theorem integral_density
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hp : Measurable p) (hp0 : ∀ᵐ x ∂μ, 0 ≤ p x) (h : A → ℝ) :
    ∫ x, h x ∂ν = ∫ x, p x * h x ∂μ := by
  rw [hν, integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hp0] with x hx
  simp only [ENNReal.toReal_ofReal hx, smul_eq_mul]

theorem integral_density_one [IsProbabilityMeasure ν]
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hp : Measurable p) (hp0 : ∀ᵐ x ∂μ, 0 ≤ p x) : ∫ x, p x ∂μ = 1 := by
  have h := integral_density hν hp hp0 (fun _ ↦ 1)
  simpa using h.symm

theorem lpNorm_mono_exponent [IsProbabilityMeasure μ]
    {E : Type*} [NormedAddCommGroup E] {h : A → E} {r t : ℝ≥0∞}
    (hh : MemLp h t μ) (hrt : r ≤ t) : lpNorm h r μ ≤ lpNorm h t μ := by
  exact ENNReal.toReal_mono hh.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hrt)

/-- In particular, the mean is controlled without assuming the function centered. -/
theorem norm_integral_le_lpNorm [IsProbabilityMeasure μ]
    {h : A → ℝ} {r : ℝ≥0∞} (hh : MemLp h r μ) (hr : 1 ≤ r) :
    |∫ x, h x ∂μ| ≤ lpNorm h r μ := by
  calc
    |∫ x, h x ∂μ| ≤ ∫ x, ‖h x‖ ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm h
    _ = lpNorm h 1 μ := (lpNorm_one_eq_integral_norm hh.aestronglyMeasurable).symm
    _ ≤ lpNorm h r μ := lpNorm_mono_exponent hh hr

/-- Probability normalization forces both source coefficient restrictions. -/
theorem density_constants [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hp : Measurable p) (hc : 0 < c) (hpc : ∀ᵐ x ∂μ, c ≤ p x)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) μ)
    (hK : lpNorm p (ENNReal.ofReal q) μ ≤ K) : c ≤ 1 ∧ 1 ≤ K := by
  have hp0 : ∀ᵐ x ∂μ, 0 ≤ p x := hpc.mono fun _ hx ↦ hc.le.trans hx
  have hmass := integral_density_one hν hp hp0
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq.le
  have hpi := hpq.integrable hq1
  constructor
  · have h := integral_mono_ae (integrable_const c) hpi hpc
    simpa only [integral_const, probReal_univ, one_smul, hmass] using h
  · have h := (norm_integral_le_lpNorm hpq hq1).trans hK
    simpa only [hmass, abs_one] using h

/-- The lower density bound is an actual inequality of measures. -/
theorem lower_measure
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hpc : ∀ᵐ x ∂μ, c ≤ p x) : (ENNReal.ofReal c) • μ ≤ ν := by
  rw [hν, ← withDensity_const]
  exact withDensity_mono (hpc.mono fun _ hx ↦ ENNReal.ofReal_le_ofReal hx)

theorem upper_reference_measure
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hc : 0 < c) (hpc : ∀ᵐ x ∂μ, c ≤ p x) :
    μ ≤ (ENNReal.ofReal c)⁻¹ • ν := by
  have hc0 : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hc)
  have h : (ENNReal.ofReal c)⁻¹ • ((ENNReal.ofReal c) • μ) ≤
      (ENNReal.ofReal c)⁻¹ • ν := by
    gcongr
    exact lower_measure hν hpc
  simpa only [smul_smul, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_smul] using h

theorem memLp_reference {E : Type*} [NormedAddCommGroup E] {G : A → E} {r : ℝ≥0∞}
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hc : 0 < c) (hpc : ∀ᵐ x ∂μ, c ≤ p x) (hG : MemLp G r ν) : MemLp G r μ := by
  exact hG.of_measure_le_smul
    (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hc)))
    (upper_reference_measure hν hc hpc)

/-- The inverse-c comparison is between actual integrable squared norms. -/
theorem energy_comparison {E : Type*} [NormedAddCommGroup E] {G : A → E}
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hc : 0 < c) (hpc : ∀ᵐ x ∂μ, c ≤ p x) (hG : MemLp G 2 ν) :
    Integrable (fun x ↦ ‖G x‖ ^ 2) μ ∧
      (∫ x, ‖G x‖ ^ 2 ∂μ) ≤ c⁻¹ * ∫ x, ‖G x‖ ^ 2 ∂ν := by
  have hGμ := memLp_reference hν hc hpc hG
  have hiν := (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG
  refine ⟨(memLp_two_iff_integrable_sq_norm hGμ.aestronglyMeasurable).mp hGμ, ?_⟩
  have h := integral_mono_measure (upper_reference_measure hν hc hpc)
    (Eventually.of_forall fun x ↦ sq_nonneg ‖G x‖)
    (hiν.smul_measure
      (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hc))))
  simpa only [integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hc.le, smul_eq_mul] using h

theorem lpNorm_two_eq {E : Type*} [NormedAddCommGroup E]
    {μ : Measure A} {G : A → E} (hG : AEStronglyMeasurable G μ) :
    lpNorm G 2 μ = (∫ x, ‖G x‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  simpa only [ENNReal.ofReal_ofNat, Real.rpow_two] using lpNorm_ofReal_eq (by norm_num : (0 : ℝ) < 2) hG

theorem lpNorm_two_sq {E : Type*} [NormedAddCommGroup E]
    {μ : Measure A} {G : A → E} (hG : MemLp G 2 μ) :
    lpNorm G 2 μ ^ 2 = ∫ x, ‖G x‖ ^ 2 ∂μ := by
  simpa only [ENNReal.ofReal_ofNat, Real.rpow_two] using
    lpNorm_rpow_eq_integral (by norm_num : (0 : ℝ) < 2) hG.aestronglyMeasurable

theorem lpNorm_energy_comparison {E : Type*} [NormedAddCommGroup E] {G : A → E}
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hc : 0 < c) (hpc : ∀ᵐ x ∂μ, c ≤ p x) (hG : MemLp G 2 ν) :
    lpNorm G 2 μ ≤ c ^ (-1 / 2 : ℝ) * lpNorm G 2 ν := by
  have hGμ := memLp_reference hν hc hpc hG
  rw [lpNorm_two_eq hGμ.aestronglyMeasurable, lpNorm_two_eq hG.aestronglyMeasurable]
  calc
    (∫ x, ‖G x‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤
        (c⁻¹ * ∫ x, ‖G x‖ ^ 2 ∂ν) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (integral_nonneg fun x ↦ sq_nonneg ‖G x‖)
        (energy_comparison hν hc hpc hG).2 (by norm_num)
    _ = c ^ (-1 / 2 : ℝ) * (∫ x, ‖G x‖ ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
      rw [Real.mul_rpow (inv_nonneg.mpr hc.le) (integral_nonneg fun x ↦ sq_nonneg ‖G x‖),
        ← Real.rpow_neg_eq_inv_rpow]
      congr 2; ring

/-- Holder for the actual weighted moment, before taking any root. -/
theorem integral_norm_rpow_density_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hp : Measurable p) (hp0 : ∀ᵐ x ∂μ, 0 ≤ p x)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) μ)
    (hf : Measurable f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) (hs : 0 < s) :
    (∫ x, ‖f x‖ ^ s ∂ν) ≤ lpNorm p (ENNReal.ofReal q) μ *
      lpNorm f (ENNReal.ofReal (s * (q / (q - 1)))) μ ^ s := by
  have hqq : q.HolderConjugate (q / (q - 1)) := Real.HolderConjugate.conjExponent hq
  have hpow := memLp_norm_rpow_bounded (μ := μ) hf hb hs.le (ENNReal.ofReal (q / (q - 1)))
  calc
    (∫ x, ‖f x‖ ^ s ∂ν) = ∫ x, ‖p x‖ * ‖‖f x‖ ^ s‖ ∂μ := by
      rw [integral_density hν hp hp0]
      apply integral_congr_ae
      filter_upwards [hp0] with x hx
      rw [Real.norm_of_nonneg hx, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    _ ≤ lpNorm p (ENNReal.ofReal q) μ *
        lpNorm (fun x ↦ ‖f x‖ ^ s) (ENNReal.ofReal (q / (q - 1))) μ := by
      simpa only [lpNorm_ofReal_eq hqq.pos hpq.aestronglyMeasurable,
        lpNorm_ofReal_eq hqq.symm.pos hpow.aestronglyMeasurable] using
        integral_mul_norm_le_Lp_mul_Lq hqq hpq hpow
    _ = _ := by rw [lpNorm_norm_rpow hqq.symm.pos hs hf.aestronglyMeasurable]

/-- Holder change of measure, with all finite-norm gates supplied by boundedness. -/
theorem lpNorm_density_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hp : Measurable p) (hp0 : ∀ᵐ x ∂μ, 0 ≤ p x)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) μ)
    (hK : lpNorm p (ENNReal.ofReal q) μ ≤ K)
    (hf : Measurable f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) (hs : 0 < s) :
    MemLp f (ENNReal.ofReal s) ν ∧
      lpNorm f (ENNReal.ofReal s) ν ≤ K ^ (1 / s) *
        lpNorm f (ENNReal.ofReal (s * (q / (q - 1)))) μ := by
  have hK0 : 0 ≤ K := lpNorm_nonneg.trans hK
  have hpow := (integral_norm_rpow_density_le hν hp hp0 hq hpq hf hb hs).trans
    (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg lpNorm_nonneg _))
  refine ⟨memLp_of_bounded hf hb _, ?_⟩
  rw [lpNorm_ofReal_eq hs hf.aestronglyMeasurable]
  calc
    (∫ x, ‖f x‖ ^ s ∂ν) ^ (1 / s) ≤
        (K * lpNorm f (ENNReal.ofReal (s * (q / (q - 1)))) μ ^ s) ^ (1 / s) :=
      Real.rpow_le_rpow (integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _) hpow
        (one_div_nonneg.mpr hs.le)
    _ = _ := by
      rw [Real.mul_rpow hK0 (Real.rpow_nonneg lpNorm_nonneg _), one_div,
        Real.rpow_rpow_inv lpNorm_nonneg hs.ne']

/-- Moving from an arbitrary center to the actual mean costs at most two. -/
theorem lpNorm_center_le_twice [IsProbabilityMeasure ν]
    (hf : Measurable f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (a : ℝ) (hs : 1 ≤ s) :
    lpNorm (fun x ↦ f x - ∫ y, f y ∂ν) (ENNReal.ofReal s) ν ≤
      2 * lpNorm (fun x ↦ f x - a) (ENNReal.ofReal s) ν := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hse : (1 : ℝ≥0∞) ≤ ENNReal.ofReal s := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hs
  have hfa := memLp_of_bounded (μ := ν) (hf.sub measurable_const) (bounded_sub_const hb a)
    (ENNReal.ofReal s)
  have hfi := (memLp_of_bounded (μ := ν) hf hb 1).integrable le_rfl
  have hmean : (∫ x, f x - a ∂ν) = (∫ x, f x ∂ν) - a := by
    rw [integral_sub hfi (integrable_const a)]
    simp
  have hi : |(∫ x, f x ∂ν) - a| ≤
      lpNorm (fun x ↦ f x - a) (ENNReal.ofReal s) ν := by
    rw [← hmean]
    exact norm_integral_le_lpNorm hfa hse
  have heq : (fun x ↦ f x - ∫ y, f y ∂ν) =
      (fun x ↦ f x - a) - (fun _ ↦ (∫ y, f y ∂ν) - a) := by
    ext x
    simp only [Pi.sub_apply]
    ring
  rw [heq]
  calc
    lpNorm ((fun x ↦ f x - a) - (fun _ ↦ (∫ y, f y ∂ν) - a)) (ENNReal.ofReal s) ν ≤
        lpNorm (fun x ↦ f x - a) (ENNReal.ofReal s) ν + |(∫ y, f y ∂ν) - a| := by
      simpa [lpNorm_const' (by positivity : ENNReal.ofReal s ≠ 0) ENNReal.ofReal_ne_top,
        Real.norm_eq_abs, Pi.sub_apply] using! lpNorm_sub_le hfa hse (g := fun _ ↦ (∫ y, f y ∂ν) - a)
    _ ≤ 2 * lpNorm (fun x ↦ f x - a) (ENNReal.ofReal s) ν := by linarith

/-- Variance is bounded by the squared distance from any chosen center. -/
theorem variance_le_integral_sub_sq [IsProbabilityMeasure ν]
    (hf : Measurable f) (a : ℝ) :
    ProbabilityTheory.variance f ν ≤ ∫ x, (f x - a) ^ 2 ∂ν := by
  rw [← ProbabilityTheory.variance_sub_const hf.aestronglyMeasurable a]
  exact ProbabilityTheory.variance_le_expectation_sq
    (hf.sub measurable_const).aestronglyMeasurable

/-- The generic Poincare transfer. The Sobolev premise is exactly the earlier
unweighted family; it does not contain a weighted conclusion. -/
theorem poincare [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Type*} [NormedAddCommGroup E] {G : A → E} {S : ℝ → ℝ}
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hp : Measurable p) (hc : 0 < c) (hpc : ∀ᵐ x ∂μ, c ≤ p x)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) μ)
    (hK : lpNorm p (ENNReal.ofReal q) μ ≤ K)
    (hf : Measurable f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) (hG : MemLp G 2 ν)
    (_hS : ∀ r : ℝ, 2 ≤ r → 0 ≤ S r)
    (hSob : ∀ r : ℝ, 2 ≤ r →
      lpNorm (fun x ↦ f x - ∫ y, f y ∂μ) (ENNReal.ofReal r) μ ≤
        S r * lpNorm G 2 μ) :
    ProbabilityTheory.variance f ν ≤
      (K * (S (2 * (q / (q - 1)))) ^ 2 / c) * ∫ x, ‖G x‖ ^ 2 ∂ν := by
  let a := ∫ y, f y ∂μ
  have hqq : q.HolderConjugate (q / (q - 1)) := Real.HolderConjugate.conjExponent hq
  have hr : 2 ≤ 2 * (q / (q - 1)) := by nlinarith [hqq.symm.lt]
  have hK0 : 0 ≤ K := lpNorm_nonneg.trans hK
  have hp0 : ∀ᵐ x ∂μ, 0 ≤ p x := hpc.mono fun _ hx ↦ hc.le.trans hx
  have hH := integral_norm_rpow_density_le hν hp hp0 hq hpq
    (hf.sub measurable_const) (bounded_sub_const hb a) (by norm_num : (0 : ℝ) < 2)
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs] at hH
  have hSob2 := hSob (2 * (q / (q - 1))) hr
  have hSq : lpNorm (fun x ↦ f x - a) (ENNReal.ofReal (2 * (q / (q - 1)))) μ ^ 2 ≤
      (S (2 * (q / (q - 1)))) ^ 2 * lpNorm G 2 μ ^ 2 := by
    calc
      _ ≤ (S (2 * (q / (q - 1))) * lpNorm G 2 μ) ^ 2 := by
        exact pow_le_pow_left₀ lpNorm_nonneg hSob2 2
      _ = _ := by ring
  have hGμ := memLp_reference hν hc hpc hG
  calc
    ProbabilityTheory.variance f ν ≤ ∫ x, (f x - a) ^ 2 ∂ν :=
      variance_le_integral_sub_sq hf a
    _ ≤ K * lpNorm (fun x ↦ f x - a)
        (ENNReal.ofReal (2 * (q / (q - 1)))) μ ^ 2 :=
      hH.trans (mul_le_mul_of_nonneg_right hK (sq_nonneg _))
    _ ≤ K * ((S (2 * (q / (q - 1)))) ^ 2 * lpNorm G 2 μ ^ 2) :=
      mul_le_mul_of_nonneg_left hSq hK0
    _ = (K * (S (2 * (q / (q - 1)))) ^ 2) * (∫ x, ‖G x‖ ^ 2 ∂μ) := by
      rw [lpNorm_two_sq hGμ]
      ring
    _ ≤ (K * (S (2 * (q / (q - 1)))) ^ 2) *
        (c⁻¹ * ∫ x, ‖G x‖ ^ 2 ∂ν) :=
      mul_le_mul_of_nonneg_left (energy_comparison hν hc hpc hG).2
        (mul_nonneg hK0 (sq_nonneg _))
    _ = _ := by ring

/-- The same Poincare conclusion expressed entirely as actual real integrals,
with the centered-square integrability gate included in the conclusion. -/
theorem poincare_integral [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Type*} [NormedAddCommGroup E] {G : A → E} {S : ℝ → ℝ}
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hp : Measurable p) (hc : 0 < c) (hpc : ∀ᵐ x ∂μ, c ≤ p x)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) μ)
    (hK : lpNorm p (ENNReal.ofReal q) μ ≤ K)
    (hf : Measurable f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) (hG : MemLp G 2 ν)
    (hS : ∀ r : ℝ, 2 ≤ r → 0 ≤ S r)
    (hSob : ∀ r : ℝ, 2 ≤ r →
      lpNorm (fun x ↦ f x - ∫ y, f y ∂μ) (ENNReal.ofReal r) μ ≤
        S r * lpNorm G 2 μ) :
    Integrable (fun x ↦ (f x - ∫ y, f y ∂ν) ^ 2) ν ∧
      (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤
        (K * (S (2 * (q / (q - 1)))) ^ 2 / c) * ∫ x, ‖G x‖ ^ 2 ∂ν := by
  refine ⟨(memLp_of_bounded (hf.sub measurable_const) (bounded_sub_const hb _) 2).integrable_sq, ?_⟩
  rw [← ProbabilityTheory.variance_eq_integral hf.aemeasurable]
  exact poincare hν hp hc hpc hq hpq hK hf hb hG hS hSob

/-- The generic moment transfer, at every real finite exponent s at least two. -/
theorem centered_moment [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Type*} [NormedAddCommGroup E] {G : A → E} {S : ℝ → ℝ}
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hp : Measurable p) (hc : 0 < c) (hpc : ∀ᵐ x ∂μ, c ≤ p x)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) μ)
    (hK : lpNorm p (ENNReal.ofReal q) μ ≤ K)
    (hf : Measurable f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) (hG : MemLp G 2 ν)
    (hS : ∀ r : ℝ, 2 ≤ r → 0 ≤ S r)
    (hSob : ∀ r : ℝ, 2 ≤ r →
      lpNorm (fun x ↦ f x - ∫ y, f y ∂μ) (ENNReal.ofReal r) μ ≤
        S r * lpNorm G 2 μ) (hs : 2 ≤ s) :
    MemLp (fun x ↦ f x - ∫ y, f y ∂ν) (ENNReal.ofReal s) ν ∧
      lpNorm (fun x ↦ f x - ∫ y, f y ∂ν) (ENNReal.ofReal s) ν ≤
        2 * K ^ (1 / s) * S (s * (q / (q - 1))) * c ^ (-1 / 2 : ℝ) * lpNorm G 2 ν := by
  let a := ∫ y, f y ∂μ
  have hs0 : 0 < s := by linarith
  have hqq : q.HolderConjugate (q / (q - 1)) := Real.HolderConjugate.conjExponent hq
  have hr : 2 ≤ s * (q / (q - 1)) := by
    calc
      2 ≤ s := hs
      _ = s * 1 := by ring
      _ ≤ s * (q / (q - 1)) := mul_le_mul_of_nonneg_left hqq.symm.lt.le hs0.le
  have hp0 : ∀ᵐ x ∂μ, 0 ≤ p x := hpc.mono fun _ hx ↦ hc.le.trans hx
  have hK0 : 0 ≤ K := lpNorm_nonneg.trans hK
  have hKpow : 0 ≤ K ^ (1 / s) := Real.rpow_nonneg hK0 _
  have hH := (lpNorm_density_le hν hp hp0 hq hpq hK
    (hf.sub measurable_const) (bounded_sub_const hb a) hs0).2
  refine ⟨memLp_of_bounded (hf.sub measurable_const) (bounded_sub_const hb _) _, ?_⟩
  calc
    lpNorm (fun x ↦ f x - ∫ y, f y ∂ν) (ENNReal.ofReal s) ν ≤
        2 * lpNorm (fun x ↦ f x - a) (ENNReal.ofReal s) ν :=
      lpNorm_center_le_twice hf hb a (by linarith)
    _ ≤ 2 * (K ^ (1 / s) * lpNorm (fun x ↦ f x - a)
        (ENNReal.ofReal (s * (q / (q - 1)))) μ) :=
      mul_le_mul_of_nonneg_left hH (by norm_num)
    _ ≤ 2 * (K ^ (1 / s) * (S (s * (q / (q - 1))) * lpNorm G 2 μ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hSob _ hr) hKpow) (by norm_num)
    _ ≤ 2 * (K ^ (1 / s) * (S (s * (q / (q - 1))) *
        (c ^ (-1 / 2 : ℝ) * lpNorm G 2 ν))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (lpNorm_energy_comparison hν hc hpc hG) (hS _ hr))
          hKpow) (by norm_num)
    _ = _ := by ring

/-- No positive-energy premise was needed above. Zero energy gives actual
almost-everywhere constancy, including zero centered functions. -/
theorem zero_energy_centered_ae [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Type*} [NormedAddCommGroup E] {G : A → E} {S : ℝ → ℝ}
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hp : Measurable p) (hc : 0 < c) (hpc : ∀ᵐ x ∂μ, c ≤ p x)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) μ)
    (hK : lpNorm p (ENNReal.ofReal q) μ ≤ K)
    (hf : Measurable f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) (hG : MemLp G 2 ν)
    (hS : ∀ r : ℝ, 2 ≤ r → 0 ≤ S r)
    (hSob : ∀ r : ℝ, 2 ≤ r →
      lpNorm (fun x ↦ f x - ∫ y, f y ∂μ) (ENNReal.ofReal r) μ ≤
        S r * lpNorm G 2 μ) (hzero : ∫ x, ‖G x‖ ^ 2 ∂ν = 0) :
    ∀ᵐ x ∂ν, f x = ∫ y, f y ∂ν := by
  have hg : lpNorm G 2 ν = 0 := by
    have h := lpNorm_two_sq hG
    rw [hzero] at h
    nlinarith [lpNorm_nonneg (f := G) (p := 2) (μ := ν)]
  have h := centered_moment hν hp hc hpc hq hpq hK hf hb hG hS hSob (s := 2) le_rfl
  have hz : lpNorm (fun x ↦ f x - ∫ y, f y ∂ν) (ENNReal.ofReal (2 : ℝ)) ν = 0 := by
    apply le_antisymm _ lpNorm_nonneg
    simpa only [hg, mul_zero] using h.2
  have hae := (lpNorm_eq_zero h.1 (by norm_num)).mp hz
  filter_upwards [hae] with x hx
  simpa only [Pi.zero_apply, sub_eq_zero] using hx

/-- The actual density measure is absolutely continuous even without positivity
or finiteness assumptions on the real density. -/
theorem density_absolutelyContinuous
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x))) : ν ≪ μ := by
  rw [hν]
  exact withDensity_absolutelyContinuous _ _

theorem memLp_of_ae_bounded [IsFiniteMeasure μ] (hf : AEMeasurable f μ)
    (hb : ∃ M : ℝ, ∀ᵐ x ∂μ, |f x| ≤ M) (r : ℝ≥0∞) : MemLp f r μ := by
  obtain ⟨M, hM⟩ := hb
  exact MemLp.of_bound hf.aestronglyMeasurable M
    (hM.mono fun x hx ↦ by simpa only [Real.norm_eq_abs] using hx)

/-- An AE bound under the reference measure gives a single bounded measurable
representative under both measures. No condition outside that full-measure set
is imposed on the original function. -/
theorem exists_bounded_representative
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hf : AEMeasurable f μ) (hb : ∃ M : ℝ, ∀ᵐ x ∂μ, |f x| ≤ M) :
    ∃ g : A → ℝ, Measurable g ∧ (∃ M : ℝ, ∀ x, |g x| ≤ M) ∧
      f =ᵐ[μ] g ∧ f =ᵐ[ν] g := by
  classical
  obtain ⟨M, hM⟩ := hb
  let g : A → ℝ := fun x ↦ if |hf.mk f x| ≤ max M 0 then hf.mk f x else 0
  have hg : Measurable g :=
    Measurable.ite (measurableSet_le (continuous_abs.measurable.comp hf.measurable_mk) measurable_const)
      hf.measurable_mk measurable_const
  have hgb : ∀ x, |g x| ≤ max M 0 := by
    intro x
    dsimp [g]
    split_ifs with hx
    · exact hx
    · simpa only [abs_zero] using le_max_right M 0
  have hfg : f =ᵐ[μ] g := by
    filter_upwards [hM, hf.ae_eq_mk] with x hx he
    simp only [g, ← he, hx.trans (le_max_left _ _), ite_true]
  exact ⟨g, hg, ⟨max M 0, hgb⟩, hfg, (density_absolutelyContinuous hν).ae_eq hfg⟩

theorem center_congr_ae {μ : Measure A} {g : A → ℝ} (hfg : f =ᵐ[μ] g) :
    (fun x ↦ f x - ∫ y, f y ∂μ) =ᵐ[μ] (fun x ↦ g x - ∫ y, g y ∂μ) := by
  filter_upwards [hfg] with x hx
  rw [hx, integral_congr_ae hfg]

theorem lpNorm_center_congr_ae {μ : Measure A} {g : A → ℝ}
    (hfg : f =ᵐ[μ] g) (r : ℝ≥0∞) :
    lpNorm (fun x ↦ f x - ∫ y, f y ∂μ) r μ =
      lpNorm (fun x ↦ g x - ∫ y, g y ∂μ) r μ := by
  exact congrArg ENNReal.toReal (eLpNorm_congr_ae (center_congr_ae hfg))

/-- AE-bounded version for functions specified only on the measured support. -/
theorem poincare_ae [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Type*} [NormedAddCommGroup E] {G : A → E} {S : ℝ → ℝ}
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hp : Measurable p) (hc : 0 < c) (hpc : ∀ᵐ x ∂μ, c ≤ p x)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) μ)
    (hK : lpNorm p (ENNReal.ofReal q) μ ≤ K)
    (hf : AEMeasurable f μ) (hb : ∃ M : ℝ, ∀ᵐ x ∂μ, |f x| ≤ M) (hG : MemLp G 2 ν)
    (hS : ∀ r : ℝ, 2 ≤ r → 0 ≤ S r)
    (hSob : ∀ r : ℝ, 2 ≤ r →
      lpNorm (fun x ↦ f x - ∫ y, f y ∂μ) (ENNReal.ofReal r) μ ≤
        S r * lpNorm G 2 μ) :
    MemLp f 2 ν ∧ ProbabilityTheory.variance f ν ≤
      (K * (S (2 * (q / (q - 1)))) ^ 2 / c) * ∫ x, ‖G x‖ ^ 2 ∂ν := by
  obtain ⟨g, hg, hgb, hfgμ, hfgν⟩ := exists_bounded_representative hν hf hb
  have hSobg : ∀ r : ℝ, 2 ≤ r →
      lpNorm (fun x ↦ g x - ∫ y, g y ∂μ) (ENNReal.ofReal r) μ ≤
        S r * lpNorm G 2 μ := by
    intro r hr
    rw [← lpNorm_center_congr_ae hfgμ]
    exact hSob r hr
  refine ⟨(memLp_congr_ae hfgν).mpr (memLp_of_bounded hg hgb 2), ?_⟩
  rw [ProbabilityTheory.variance_congr hfgν]
  exact poincare hν hp hc hpc hq hpq hK hg hgb hG hS hSobg

theorem poincare_integral_ae [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Type*} [NormedAddCommGroup E] {G : A → E} {S : ℝ → ℝ}
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hp : Measurable p) (hc : 0 < c) (hpc : ∀ᵐ x ∂μ, c ≤ p x)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) μ)
    (hK : lpNorm p (ENNReal.ofReal q) μ ≤ K)
    (hf : AEMeasurable f μ) (hb : ∃ M : ℝ, ∀ᵐ x ∂μ, |f x| ≤ M) (hG : MemLp G 2 ν)
    (hS : ∀ r : ℝ, 2 ≤ r → 0 ≤ S r)
    (hSob : ∀ r : ℝ, 2 ≤ r →
      lpNorm (fun x ↦ f x - ∫ y, f y ∂μ) (ENNReal.ofReal r) μ ≤
        S r * lpNorm G 2 μ) :
    Integrable (fun x ↦ (f x - ∫ y, f y ∂ν) ^ 2) ν ∧
      (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤
        (K * (S (2 * (q / (q - 1)))) ^ 2 / c) * ∫ x, ‖G x‖ ^ 2 ∂ν := by
  have h := poincare_ae hν hp hc hpc hq hpq hK hf hb hG hS hSob
  refine ⟨(h.1.sub (memLp_const _)).integrable_sq, ?_⟩
  rw [← ProbabilityTheory.variance_eq_integral h.1.aestronglyMeasurable.aemeasurable]
  exact h.2

/-- The same exact moment constant under an AE bound on the original function. -/
theorem centered_moment_ae [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Type*} [NormedAddCommGroup E] {G : A → E} {S : ℝ → ℝ}
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hp : Measurable p) (hc : 0 < c) (hpc : ∀ᵐ x ∂μ, c ≤ p x)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) μ)
    (hK : lpNorm p (ENNReal.ofReal q) μ ≤ K)
    (hf : AEMeasurable f μ) (hb : ∃ M : ℝ, ∀ᵐ x ∂μ, |f x| ≤ M) (hG : MemLp G 2 ν)
    (hS : ∀ r : ℝ, 2 ≤ r → 0 ≤ S r)
    (hSob : ∀ r : ℝ, 2 ≤ r →
      lpNorm (fun x ↦ f x - ∫ y, f y ∂μ) (ENNReal.ofReal r) μ ≤
        S r * lpNorm G 2 μ) (hs : 2 ≤ s) :
    MemLp (fun x ↦ f x - ∫ y, f y ∂ν) (ENNReal.ofReal s) ν ∧
      lpNorm (fun x ↦ f x - ∫ y, f y ∂ν) (ENNReal.ofReal s) ν ≤
        2 * K ^ (1 / s) * S (s * (q / (q - 1))) * c ^ (-1 / 2 : ℝ) * lpNorm G 2 ν := by
  obtain ⟨g, hg, hgb, hfgμ, hfgν⟩ := exists_bounded_representative hν hf hb
  have hSobg : ∀ r : ℝ, 2 ≤ r →
      lpNorm (fun x ↦ g x - ∫ y, g y ∂μ) (ENNReal.ofReal r) μ ≤
        S r * lpNorm G 2 μ := by
    intro r hr
    rw [← lpNorm_center_congr_ae hfgμ]
    exact hSob r hr
  have h := centered_moment hν hp hc hpc hq hpq hK hg hgb hG hS hSobg hs
  refine ⟨(memLp_congr_ae (center_congr_ae hfgν)).mpr h.1, ?_⟩
  rw [lpNorm_center_congr_ae hfgν]
  exact h.2

theorem zero_energy_centered_ae_of_ae_bounded [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Type*} [NormedAddCommGroup E] {G : A → E} {S : ℝ → ℝ}
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hp : Measurable p) (hc : 0 < c) (hpc : ∀ᵐ x ∂μ, c ≤ p x)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) μ)
    (hK : lpNorm p (ENNReal.ofReal q) μ ≤ K)
    (hf : AEMeasurable f μ) (hb : ∃ M : ℝ, ∀ᵐ x ∂μ, |f x| ≤ M) (hG : MemLp G 2 ν)
    (hS : ∀ r : ℝ, 2 ≤ r → 0 ≤ S r)
    (hSob : ∀ r : ℝ, 2 ≤ r →
      lpNorm (fun x ↦ f x - ∫ y, f y ∂μ) (ENNReal.ofReal r) μ ≤
        S r * lpNorm G 2 μ) (hzero : ∫ x, ‖G x‖ ^ 2 ∂ν = 0) :
    ∀ᵐ x ∂ν, f x = ∫ y, f y ∂ν := by
  have hg : lpNorm G 2 ν = 0 := by
    have h := lpNorm_two_sq hG
    rw [hzero] at h
    nlinarith [lpNorm_nonneg (f := G) (p := 2) (μ := ν)]
  have h := centered_moment_ae hν hp hc hpc hq hpq hK hf hb hG hS hSob (s := 2) le_rfl
  have hz : lpNorm (fun x ↦ f x - ∫ y, f y ∂ν) (ENNReal.ofReal (2 : ℝ)) ν = 0 := by
    apply le_antisymm _ lpNorm_nonneg
    simpa only [hg, mul_zero] using h.2
  have hae := (lpNorm_eq_zero h.1 (by norm_num)).mp hz
  filter_upwards [hae] with x hx
  simpa only [Pi.zero_apply, sub_eq_zero] using hx

/-- The logarithmic factor later used in source Lemma 3.2 is nonnegative.
This is coefficient algebra only, not an entropy or LSI theorem. -/
theorem logarithmic_coefficient_nonneg (hc : 0 < c) (hc1 : c ≤ 1) (hK1 : 1 ≤ K) :
    0 ≤ Real.log (K * c ^ (-3 / 2 : ℝ)) ∧
      0 ≤ 3 + 2 * Real.log (K * c ^ (-3 / 2 : ℝ)) ∧
      0 ≤ 5 + 2 * Real.log (K * c ^ (-3 / 2 : ℝ)) := by
  have hpow : 1 ≤ c ^ (-3 / 2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hc hc1 (by norm_num)
  have hlog : 0 ≤ Real.log (K * c ^ (-3 / 2 : ℝ)) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hK1 hpow)
  exact ⟨hlog, by linarith, by linarith⟩

theorem poincare_coefficient_nonneg {S : ℝ → ℝ}
    (hc : 0 < c) (hK : 0 ≤ K) : 0 ≤ K * (S (2 * (q / (q - 1)))) ^ 2 / c := by
  positivity

theorem moment_coefficient_nonneg {S : ℝ → ℝ}
    (hc : 0 < c) (hK : 0 ≤ K) (hS : 0 ≤ S (s * (q / (q - 1)))) :
    0 ≤ 2 * K ^ (1 / s) * S (s * (q / (q - 1))) * c ^ (-1 / 2 : ℝ) := by
  positivity

end PeriodicAttractiveLogGas.DensityMoments
