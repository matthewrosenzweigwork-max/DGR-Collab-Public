import LeanResearch.PeriodicAttractiveLogGas.Entropy
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.Bounded

/-! Source Lemma 3.2, `lem:rectangle-density`, lines 447--459: the normalized
entropy versus third moment and the defective entropy estimate.

The square-weighted measure is constructed and proved to be a probability.
The logarithm is integrable for that measure even when the original function
vanishes. Jensen's inequality is proved here from the logarithm's tangent-line
inequality; neither Jensen nor the desired entropy inequality is a premise.
Finite third moment supplies the actual square and entropy integrability.
The bounded measurable source case is then a corollary.

The normalized third-moment step is independent of the still-required
density-bound instantiation and homogeneity assembly.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PeriodicAttractiveLogGas
namespace EntropyMoment

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem sq_le_one_add_abs_cube (t : ℝ) : t ^ 2 ≤ 1 + |t| ^ 3 := by
  by_cases ht : |t| ≤ 1
  · have hs : t ^ 2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg t) ht 2
    linarith [pow_nonneg (abs_nonneg t) 3]
  · have hp := mul_nonneg (sq_nonneg |t|) (sub_nonneg.mpr (le_of_lt (lt_of_not_ge ht)))
    rw [← sq_abs t]
    nlinarith

theorem sq_mul_log_sq_eq (t : ℝ) :
    t ^ 2 * Real.log (t ^ 2) = 2 * (t ^ 2 * Real.log |t|) := by
  rw [Real.log_pow, Real.log_abs]
  norm_num; ring

/-- The two-sided bound handles zero and both tails of the entropy density.
In particular the negative logarithmic tail is not assumed integrable. -/
theorem abs_sq_mul_log_sq_le (t : ℝ) :
    |t ^ 2 * Real.log (t ^ 2)| ≤ 1 + 2 * |t| ^ 3 := by
  have hlo : -1 ≤ t ^ 2 * Real.log (t ^ 2) := by
    have h := Real.self_sub_one_le_mul_log (sq_nonneg t)
    linarith [sq_nonneg t]
  have hhi : t ^ 2 * Real.log (t ^ 2) ≤ 2 * |t| ^ 3 := by
    by_cases ht : t = 0
    · simp [ht]
    have hl := Real.log_le_sub_one_of_pos (abs_pos.mpr ht)
    have hm := mul_le_mul_of_nonneg_left hl (sq_nonneg |t|)
    rw [sq_mul_log_sq_eq, ← sq_abs t]
    nlinarith [sq_nonneg |t|]
  apply abs_le.mpr
  constructor <;> linarith [pow_nonneg (abs_nonneg t) 3]

theorem integrable_sq_of_integrable_abs_cube [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) (h3 : Integrable (fun x ↦ |f x| ^ 3) μ) :
    Integrable (fun x ↦ f x ^ 2) μ := by
  apply ((integrable_const 1).add h3).mono' (hf.pow_const 2).aestronglyMeasurable
  exact Eventually.of_forall fun x ↦ by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f x)), Pi.add_apply] using!
      sq_le_one_add_abs_cube (f x)

theorem integrable_sq_mul_log_sq_of_integrable_abs_cube [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f)
    (h3 : Integrable (fun x ↦ |f x| ^ 3) μ) :
    Integrable (fun x ↦ f x ^ 2 * Real.log (f x ^ 2)) μ := by
  apply ((integrable_const 1).add (h3.const_mul 2)).mono'
    (Real.continuous_mul_log.measurable.comp (hf.pow_const 2)).aestronglyMeasurable
  exact Eventually.of_forall fun x ↦ by
    simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply] using! abs_sq_mul_log_sq_le (f x)

theorem integrable_sq_mul_log_abs_of_integrable_abs_cube [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f)
    (h3 : Integrable (fun x ↦ |f x| ^ 3) μ) :
    Integrable (fun x ↦ f x ^ 2 * Real.log |f x|) μ := by
  apply ((integrable_sq_mul_log_sq_of_integrable_abs_cube hf h3).const_mul (1 / 2 : ℝ)).congr
  exact Eventually.of_forall fun x ↦ by
    change 1 / 2 * (f x ^ 2 * Real.log (f x ^ 2)) = f x ^ 2 * Real.log |f x|
    rw [sq_mul_log_sq_eq]
    ring

/-- The probability appearing in the source Jensen step. -/
def squareWeightedMeasure (μ : Measure α) (f : α → ℝ) : Measure α :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (f x ^ 2))

theorem squareWeightedMeasure_isProbability {f : α → ℝ}
    (h2 : Integrable (fun x ↦ f x ^ 2) μ) (hmass : ∫ x, f x ^ 2 ∂μ = 1) :
    IsProbabilityMeasure (squareWeightedMeasure μ f) := by
  constructor
  rw [squareWeightedMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal h2 (Eventually.of_forall fun x ↦ sq_nonneg (f x)),
    hmass, ENNReal.ofReal_one]

theorem integrable_squareWeightedMeasure_iff {f g : α → ℝ} (hf : Measurable f) :
    Integrable g (squareWeightedMeasure μ f) ↔ Integrable (fun x ↦ f x ^ 2 * g x) μ := by
  unfold squareWeightedMeasure
  rw [integrable_withDensity_iff_integrable_smul' (hf.pow_const 2).ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

theorem integral_squareWeightedMeasure {f : α → ℝ} (hf : Measurable f) (g : α → ℝ) :
    ∫ x, g x ∂squareWeightedMeasure μ f = ∫ x, f x ^ 2 * g x ∂μ := by
  unfold squareWeightedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (hf.pow_const 2).ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

theorem ae_abs_pos_squareWeightedMeasure {f : α → ℝ} (hf : Measurable f) :
    ∀ᵐ x ∂squareWeightedMeasure μ f, 0 < |f x| := by
  apply (ae_withDensity_iff (hf.pow_const 2).ennreal_ofReal).mpr
  exact Eventually.of_forall fun x hx ↦ abs_pos.mpr (by
    intro hz
    simp [hz] at hx)

theorem integrable_abs_squareWeightedMeasure {f : α → ℝ} (hf : Measurable f)
    (h3 : Integrable (fun x ↦ |f x| ^ 3) μ) :
    Integrable (fun x ↦ |f x|) (squareWeightedMeasure μ f) := by
  apply (integrable_squareWeightedMeasure_iff hf).mpr
  apply h3.congr
  exact Eventually.of_forall fun x ↦ by
    change |f x| ^ 3 = f x ^ 2 * |f x|
    rw [← sq_abs (f x)]
    ring

theorem integral_abs_squareWeightedMeasure {f : α → ℝ} (hf : Measurable f) :
    ∫ x, |f x| ∂squareWeightedMeasure μ f = ∫ x, |f x| ^ 3 ∂μ := by
  rw [integral_squareWeightedMeasure hf]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    change f x ^ 2 * |f x| = |f x| ^ 3
    rw [← sq_abs (f x)]
    ring

theorem integrable_log_abs_squareWeightedMeasure [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) (h3 : Integrable (fun x ↦ |f x| ^ 3) μ) :
    Integrable (fun x ↦ Real.log |f x|) (squareWeightedMeasure μ f) :=
  (integrable_squareWeightedMeasure_iff hf).mpr
    (integrable_sq_mul_log_abs_of_integrable_abs_cube hf h3)

theorem abs_cube_integral_pos_of_sq_integral_one {f : α → ℝ}
    (h3 : Integrable (fun x ↦ |f x| ^ 3) μ) (hmass : ∫ x, f x ^ 2 ∂μ = 1) :
    0 < ∫ x, |f x| ^ 3 ∂μ := by
  have hn : 0 ≤ ∫ x, |f x| ^ 3 ∂μ := integral_nonneg fun x ↦ pow_nonneg (abs_nonneg _) _
  apply lt_of_le_of_ne hn
  intro hz
  have ha := (integral_eq_zero_iff_of_nonneg
    (fun x ↦ pow_nonneg (abs_nonneg (f x)) 3) h3).mp hz.symm
  have hsq : ∫ x, f x ^ 2 ∂μ = 0 := by
    calc
      _ = ∫ x, (0 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ha] with x hx
        have habs : |f x| = 0 := (pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hx
        simp [abs_eq_zero.mp habs]
      _ = 0 := integral_zero _ _
  linarith

/-- Probability Jensen for the logarithm, proved from its tangent at the
strictly positive mean. The positivity is almost everywhere, so zero values
on null sets need no arbitrary positive replacement. -/
theorem integral_log_le_log_integral [IsProbabilityMeasure μ] {g : α → ℝ}
    (hg : Integrable g μ) (hlog : Integrable (fun x ↦ Real.log (g x)) μ)
    (hpos : ∀ᵐ x ∂μ, 0 < g x) (hmean : 0 < ∫ x, g x ∂μ) :
    ∫ x, Real.log (g x) ∂μ ≤ Real.log (∫ x, g x ∂μ) := by
  let A := ∫ x, g x ∂μ
  have hA : 0 < A := hmean
  have hr : Integrable (fun x ↦ Real.log A + g x / A - 1) μ :=
    ((integrable_const _).add (hg.div_const A)).sub (integrable_const _)
  have hp : ∀ᵐ x ∂μ, Real.log (g x) ≤ Real.log A + g x / A - 1 := by
    filter_upwards [hpos] with x hx
    have h := Real.log_le_sub_one_of_pos (div_pos hx hA)
    rw [Real.log_div hx.ne' hA.ne'] at h
    linarith
  have h := integral_mono_ae hlog hr hp
  have hsplit₁ := integral_sub ((integrable_const (Real.log A)).add (hg.div_const A))
    (integrable_const (1 : ℝ))
  have hsplit₂ := integral_add (integrable_const (Real.log A)) (hg.div_const A)
  dsimp only [Pi.add_apply] at hsplit₁
  rw [hsplit₁, hsplit₂, integral_div] at h
  simpa [A, hmean.ne'] using h

/-- Finite third moment is sufficient; finite entropy is a conclusion. This
general version even permits a finite base measure, because its square tilt
is the actual probability used in Jensen. -/
theorem entropy_sq_le_log_abs_cube [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) (h3 : Integrable (fun x ↦ |f x| ^ 3) μ)
    (hmass : ∫ x, f x ^ 2 ∂μ = 1) :
    entropy μ (fun x ↦ f x ^ 2) ≤
      ((2 * Real.log (∫ x, |f x| ^ 3 ∂μ) : ℝ) : EReal) := by
  have h2 := integrable_sq_of_integrable_abs_cube hf h3
  have hlog := integrable_sq_mul_log_sq_of_integrable_abs_cube hf h3
  let : IsProbabilityMeasure (squareWeightedMeasure μ f) :=
    squareWeightedMeasure_isProbability h2 hmass
  have hmean : 0 < ∫ x, |f x| ∂squareWeightedMeasure μ f := by
    rw [integral_abs_squareWeightedMeasure hf]
    exact abs_cube_integral_pos_of_sq_integral_one h3 hmass
  have hj := integral_log_le_log_integral
    (integrable_abs_squareWeightedMeasure hf h3)
    (integrable_log_abs_squareWeightedMeasure hf h3)
    (ae_abs_pos_squareWeightedMeasure hf) hmean
  rw [integral_abs_squareWeightedMeasure hf] at hj
  have hi : (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ) =
      2 * ∫ x, Real.log |f x| ∂squareWeightedMeasure μ f := by
    rw [integral_squareWeightedMeasure hf]
    calc
      _ = ∫ x, 2 * (f x ^ 2 * Real.log |f x|) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun x ↦ sq_mul_log_sq_eq (f x))
      _ = _ := integral_const_mul _ _
  rw [entropy_eq_integral (Eventually.of_forall fun x ↦ sq_nonneg (f x)) hlog,
    hmass, Real.log_one, mul_zero, sub_zero, hi]
  exact_mod_cast mul_le_mul_of_nonneg_left hj (by norm_num : (0 : ℝ) ≤ 2)

/-- A local compactness argument for bounded measurable scalar inputs. -/
theorem integrable_continuous_comp_bounded [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) {M : ℝ} (hb : ∀ x, |f x| ≤ M)
    {k : ℝ → ℝ} (hk : Continuous k) : Integrable (fun x ↦ k (f x)) μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-M) M)).exists_bound_of_continuousOn
    hk.continuousOn
  exact (integrable_const C).mono' (hk.measurable.comp hf).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ hC (f x) (abs_le.mp (hb x)))

theorem integrable_abs_cube_bounded [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) {M : ℝ} (hb : ∀ x, |f x| ≤ M) :
    Integrable (fun x ↦ |f x| ^ 3) μ :=
  integrable_continuous_comp_bounded hf hb (continuous_abs.pow 3)

/-- The exact normalized entropy-versus-third-moment step of Lemma 3.2. -/
theorem entropy_sq_le_log_abs_cube_bounded [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : Measurable f) {M : ℝ} (hb : ∀ x, |f x| ≤ M)
    (hmass : ∫ x, f x ^ 2 ∂μ = 1) :
    entropy μ (fun x ↦ f x ^ 2) ≤
      ((2 * Real.log (∫ x, |f x| ^ 3 ∂μ) : ℝ) : EReal) :=
  entropy_sq_le_log_abs_cube hf (integrable_abs_cube_bounded hf hb) hmass

theorem memLp_three_of_integrable_abs_cube {f : α → ℝ} (hf : Measurable f)
    (h3 : Integrable (fun x ↦ |f x| ^ 3) μ) : MemLp f 3 μ := by
  apply (integrable_norm_rpow_iff hf.aestronglyMeasurable
    (by norm_num : (3 : ℝ≥0∞) ≠ 0) (by norm_num : (3 : ℝ≥0∞) ≠ ∞)).mp
  simpa [Real.norm_eq_abs, Real.rpow_natCast] using h3

/-- This identity connects the finite real third moment to the actual L3
norm, with membership explicit so no infinity-to-real default is used. -/
theorem lpNorm_three_cubed {f : α → ℝ} (hf : MemLp f 3 μ) :
    lpNorm f 3 μ ^ 3 = ∫ x, |f x| ^ 3 ∂μ := by
  have he : lpNorm f 3 μ = (∫ x, |f x| ^ 3 ∂μ) ^ (1 / 3 : ℝ) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num : (3 : ℝ≥0∞) ≠ 0)
      (by norm_num : (3 : ℝ≥0∞) ≠ ∞) hf.aestronglyMeasurable]
    norm_num [Real.norm_eq_abs, Real.rpow_natCast]
  rw [he]
  simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow
    (integral_nonneg fun x ↦ pow_nonneg (abs_nonneg (f x)) 3) (by decide : (3 : ℕ) ≠ 0)

/-- The scalar step after Jensen, retaining the source constants. -/
theorem twice_log_moment_le_defect {A m S E : ℝ}
    (hA : 0 < A) (hm : 0 < m) (hS : 0 ≤ S) (hE : 0 ≤ E)
    (hbound : m ≤ A * (1 + S * Real.sqrt E) ^ 3) :
    2 * Real.log m ≤ 3 * S ^ 2 * E + 3 + 2 * Real.log A := by
  have ht : 0 ≤ S * Real.sqrt E := mul_nonneg hS (Real.sqrt_nonneg E)
  have hb : 0 < 1 + S * Real.sqrt E := by linarith
  have hlog := Real.log_le_log hm hbound
  rw [Real.log_mul hA.ne' (pow_ne_zero 3 hb.ne'), Real.log_pow] at hlog
  have hlin := Real.log_le_sub_one_of_pos hb
  have hquad := sq_nonneg (S * Real.sqrt E - 1)
  have hsquare : (S * Real.sqrt E) ^ 2 = S ^ 2 * E := by
    rw [mul_pow, Real.sq_sqrt hE]
  norm_num only [Nat.cast_ofNat] at hlog
  nlinarith [hsquare]

theorem densityMomentFactor_ge_one {K c : ℝ} (hK : 1 ≤ K) (hc : 0 < c) (hc1 : c ≤ 1) :
    1 ≤ K * c ^ (-(3 / 2 : ℝ)) := by
  have hp : 1 ≤ c ^ (-(3 / 2 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hc hc1 (by norm_num)
  simpa only [one_mul] using mul_le_mul hK hp zero_le_one (le_trans zero_le_one hK)

theorem densityDefectConstant_nonneg {K c : ℝ}
    (hK : 1 ≤ K) (hc : 0 < c) (hc1 : c ≤ 1) :
    0 ≤ 3 + 2 * Real.log (K * c ^ (-(3 / 2 : ℝ))) := by
  have h := Real.log_nonneg (densityMomentFactor_ge_one hK hc hc1)
  linarith

theorem cube_densityMomentNormFactor {K c S E : ℝ} (hK : 0 ≤ K) (hc : 0 < c) :
    (K ^ (1 / 3 : ℝ) * c ^ (-(1 / 2 : ℝ)) * (1 + S * Real.sqrt E)) ^ 3 =
      (K * c ^ (-(3 / 2 : ℝ))) * (1 + S * Real.sqrt E) ^ 3 := by
  have hKcube : (K ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = K := by
    simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow hK (by decide : (3 : ℕ) ≠ 0)
  have hccube : (c ^ (-(1 / 2 : ℝ))) ^ (3 : ℕ) = c ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_mul_natCast hc.le]
    congr 1
    norm_num
  rw [mul_pow, mul_pow, hKcube, hccube]

/-- The defective estimate from the source, under the supplied actual L3
bound. Its entropy finiteness and Jensen step are conclusions above. -/
theorem entropy_sq_defective_of_third_norm [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : Measurable f) (h3 : Integrable (fun x ↦ |f x| ^ 3) μ)
    (hmass : ∫ x, f x ^ 2 ∂μ = 1) {c K S E : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hK : 1 ≤ K) (hS : 0 ≤ S) (hE : 0 ≤ E)
    (hnorm : lpNorm f 3 μ ≤
      K ^ (1 / 3 : ℝ) * c ^ (-(1 / 2 : ℝ)) * (1 + S * Real.sqrt E)) :
    entropy μ (fun x ↦ f x ^ 2) ≤
      ((3 * S ^ 2 * E + 3 + 2 * Real.log (K * c ^ (-(3 / 2 : ℝ))) : ℝ) : EReal) := by
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hA : 0 < K * c ^ (-(3 / 2 : ℝ)) :=
    lt_of_lt_of_le zero_lt_one (densityMomentFactor_ge_one hK hc hc1)
  have hmoment : (∫ x, |f x| ^ 3 ∂μ) ≤
      (K * c ^ (-(3 / 2 : ℝ))) * (1 + S * Real.sqrt E) ^ 3 := by
    have hp := pow_le_pow_left₀ (lpNorm_nonneg (f := f) (p := 3) (μ := μ)) hnorm 3
    rw [lpNorm_three_cubed (memLp_three_of_integrable_abs_cube hf h3),
      cube_densityMomentNormFactor hK0 hc] at hp
    exact hp
  have hscalar := twice_log_moment_le_defect hA
    (abs_cube_integral_pos_of_sq_integral_one h3 hmass) hS hE hmoment
  exact (entropy_sq_le_log_abs_cube hf h3 hmass).trans (by exact_mod_cast hscalar)

theorem entropy_sq_defective_bounded [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : Measurable f) {M : ℝ} (hb : ∀ x, |f x| ≤ M)
    (hmass : ∫ x, f x ^ 2 ∂μ = 1) {c K S E : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hK : 1 ≤ K) (hS : 0 ≤ S) (hE : 0 ≤ E)
    (hnorm : lpNorm f 3 μ ≤
      K ^ (1 / 3 : ℝ) * c ^ (-(1 / 2 : ℝ)) * (1 + S * Real.sqrt E)) :
    entropy μ (fun x ↦ f x ^ 2) ≤
      ((3 * S ^ 2 * E + 3 + 2 * Real.log (K * c ^ (-(3 / 2 : ℝ))) : ℝ) : EReal) :=
  entropy_sq_defective_of_third_norm hf (integrable_abs_cube_bounded hf hb)
    hmass hc hc1 hK hS hE hnorm

end EntropyMoment
end PeriodicAttractiveLogGas
