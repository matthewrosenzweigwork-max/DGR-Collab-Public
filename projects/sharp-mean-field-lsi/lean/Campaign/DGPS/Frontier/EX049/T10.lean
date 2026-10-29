import DGPS.Circle.AngularNormalization
import DGPS.Foundations.Entropy

/-!
# EX049.10: Entropy finiteness, scalar upper bound and homogeneity

Task id: EX049.10 (node EX049, leaf formalization). Title: Entropy finiteness, scalar upper bound
and homogeneity.

Let `ν` be a probability measure on the angular circle `AngCircle`, `w` a measurable real function
and `S ≥ 0` a pointwise bound `w x ^ 2 ≤ S`. Put `M = ∫ w ^ 2 dν`. With the entropy
`Ent_ν f = ∫ f log f dν - (∫ f dν) log (∫ f dν)` of the specification, the square `w ^ 2` has
finite entropy, the entropy is `0` when `M = 0`, and `S > 0` and `Ent_ν (w ^ 2) ≤ M log (S / M)`
when `M > 0`. Moreover `Ent_ν ((c w) ^ 2) = c ^ 2 Ent_ν (w ^ 2)` for every real `c`.

## Provides

- `DGPS.Frontier.EX049.entEX04910`: the entropy `∫ f log f dν - (∫ f dν) log (∫ f dν)` of a real
  function on the circle, with `0 log 0 = 0` supplied by `Real.log 0 = 0`.
- `DGPS.Frontier.EX049.ex049_10_entropy_finiteness_scalar_upper_bound_homogeneity`: the full
  statement, a conjunction of three claims: (1) `w ^ 2` and `w ^ 2 log (w ^ 2)` are integrable
  (finiteness of the entropy); (2) `M = 0` gives entropy `0`, and `M > 0` gives `S > 0` together
  with `Ent_ν (w ^ 2) ≤ M log (S / M)`; (3) the homogeneity identity for every real `c`.
- `DGPS.Frontier.EX049.ex049_10_entropy_finiteness_scalar_upper_bound_homogeneity_homogeneousEntropy`:
  the entropy of the specification is the campaign entropy `homogeneousEntropy`, and the latter
  is finite, for the square `w ^ 2`.
- Helpers, each with full name `DGPS.Frontier.EX049.<name>`:
  - `mul_log_mul_EX04910`: the scalar identity `(k x) log (k x) = k (x log x) + k (log k) x`.
  - `norm_sq_le_EX04910`, `integrable_sq_EX04910`, `integrable_sq_mul_log_EX04910`: bounded
    measurable functions and the composition with `x log x` are integrable.
  - `integral_sq_le_EX04910`: the mass `M` is at most `S`.
  - `ent_eq_zero_EX04910`: the zero-mass case.
  - `integral_sq_mul_log_le_EX04910`: the pointwise bound `w ^ 2 log (w ^ 2) ≤ w ^ 2 log S`
    integrated.
  - `ent_le_EX04910`: the upper bound for positive mass.
  - `ent_smul_EX04910`: the homogeneity identity.

## R5 notes

- The circle is `AngCircle` and a probability measure on it is `ν : Measure AngCircle` with an
  `IsProbabilityMeasure ν` instance, with no relation to `angHaar` (the specification warns that
  `ν` is unrelated to Haar measure).
- Boundedness of `w` is not a separate hypothesis. The specification lists `w` bounded
  measurable together with `S ≥ 0` and `w x ^ 2 ≤ S` at every point. The latter says
  `|w x| ≤ √S` at every point, so a separate bound would be redundant and is not added. The
  hypotheses are `Measurable w`, `0 ≤ S` and the pointwise bound, and nothing else.
- The hypothesis `0 ≤ S` of the specification is kept for literal correspondence and is named
  `_hS0` in the main declaration because it is unused: it follows from the pointwise bound,
  since `0 ≤ w x ^ 2 ≤ S`. The helper lemmas do not take it.
- The entropy is the real number `entEX04910 ν f` of the specification, with `0 log 0 = 0` taken
  from `Real.log 0 = 0`. Finiteness of the entropy is read as integrability of the two integrands
  `f` and `f log f` for `f = w ^ 2`, so that both Bochner integrals are genuine and no junk value
  `0` of a non-integrable integral occurs. The corollary
  `..._homogeneousEntropy` connects this entropy with the campaign `homogeneousEntropy` valued in
  `ℝ≥0∞`, and shows that the latter is finite.
- The pointwise bound is used, never a Haar essential supremum. No hypothesis ties `ν` to
  `angHaar`, and `S` is not required to be the least bound. The case `S = 0` is allowed: it forces
  `w = 0`, hence `M = 0`.
- The case split of the specification is kept: the upper bound is stated only for `M > 0`,
  where `M log (S / M)` is the intended quantity. For `M = 0` the bound is not stated, since
  `Real.log (S / 0) = 0` in Lean and the entropy is `0` by the zero-mass clause.
- Homogeneity is stated for every real `c`, in the form
  `entEX04910 ν (fun x => (c * w x) ^ 2) = c ^ 2 * entEX04910 ν (fun x => w x ^ 2)`. The proof
  has no case split on `c`: the scalar identity `mul_log_mul_EX04910` holds for all `k` and `x`.
  The case `c = 0` therefore needs no separate zero-mass argument.
- No other campaign declaration is used besides `AngCircle` and `homogeneousEntropy`.
-/

namespace DGPS.Frontier.EX049

open MeasureTheory
open DGPS.Circle.AngularNormalization

/-- The entropy `∫ f log f dν - (∫ f dν) log (∫ f dν)` of a real function on the circle. The
convention `0 log 0 = 0` is `Real.log 0 = 0`. -/
noncomputable def entEX04910 (ν : Measure AngCircle) (f : AngCircle → ℝ) : ℝ :=
  ∫ x, f x * Real.log (f x) ∂ν - (∫ x, f x ∂ν) * Real.log (∫ x, f x ∂ν)

/-- The scalar identity `(k x) log (k x) = k (x log x) + k (log k) x`, valid for all reals. -/
theorem mul_log_mul_EX04910 (k x : ℝ) :
    k * x * Real.log (k * x) = k * (x * Real.log x) + k * Real.log k * x := by
  rcases eq_or_ne k 0 with hk | hk
  · simp [hk]
  rcases eq_or_ne x 0 with hx | hx
  · simp [hx]
  rw [Real.log_mul hk hx]
  ring

/-- A function bounded in square by `S` has a uniform bound on its norm. -/
theorem norm_sq_le_EX04910 {w : AngCircle → ℝ} {S : ℝ} (hS : ∀ x, w x ^ 2 ≤ S) (x : AngCircle) :
    ‖w x ^ 2‖ ≤ S := by
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact hS x

/-- The square of a measurable function with a pointwise bound is integrable. -/
theorem integrable_sq_EX04910 (ν : Measure AngCircle) [IsProbabilityMeasure ν] {w : AngCircle → ℝ}
    (hw : Measurable w) {S : ℝ} (hS : ∀ x, w x ^ 2 ≤ S) :
    Integrable (fun x => w x ^ 2) ν :=
  Integrable.of_bound (hw.pow_const 2).aestronglyMeasurable S
    (Filter.Eventually.of_forall (norm_sq_le_EX04910 hS))

/-- The composition of the square with `x log x` is integrable: `x log x` is continuous, hence
bounded on `[0, S]`, and `w ^ 2` takes values in `[0, S]`. -/
theorem integrable_sq_mul_log_EX04910 (ν : Measure AngCircle) [IsProbabilityMeasure ν]
    {w : AngCircle → ℝ} (hw : Measurable w) {S : ℝ} (hS : ∀ x, w x ^ 2 ≤ S) :
    Integrable (fun x => w x ^ 2 * Real.log (w x ^ 2)) ν := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := S)).exists_bound_of_continuousOn
    (Real.continuous_mul_log.continuousOn)
  refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun x => ?_)
  · exact (((hw.pow_const 2).mul (Real.measurable_log.comp (hw.pow_const 2)))).aestronglyMeasurable
  · exact hC (w x ^ 2) ⟨sq_nonneg _, hS x⟩

/-- The mass is at most the pointwise bound. -/
theorem integral_sq_le_EX04910 (ν : Measure AngCircle) [IsProbabilityMeasure ν]
    {w : AngCircle → ℝ} (hw : Measurable w) {S : ℝ} (hS : ∀ x, w x ^ 2 ≤ S) :
    ∫ x, w x ^ 2 ∂ν ≤ S := by
  have h := integral_mono (integrable_sq_EX04910 ν hw hS) (integrable_const S) hS
  simpa using h

/-- Zero mass gives zero entropy. -/
theorem ent_eq_zero_EX04910 (ν : Measure AngCircle) [IsProbabilityMeasure ν]
    {w : AngCircle → ℝ} (hw : Measurable w) {S : ℝ} (hS : ∀ x, w x ^ 2 ≤ S)
    (hM : ∫ x, w x ^ 2 ∂ν = 0) : entEX04910 ν (fun x => w x ^ 2) = 0 := by
  have hz : (fun x => w x ^ 2) =ᵐ[ν] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (w x))
      (integrable_sq_EX04910 ν hw hS)).mp hM
  have h1 : ∫ x, w x ^ 2 * Real.log (w x ^ 2) ∂ν = 0 := by
    rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
    · simp
    · filter_upwards [hz] with x hx
      simp only [Pi.zero_apply] at hx
      simp [hx]
  unfold entEX04910
  rw [hM, h1]
  simp

/-- The integrated pointwise bound `w ^ 2 log (w ^ 2) ≤ w ^ 2 log S`. -/
theorem integral_sq_mul_log_le_EX04910 (ν : Measure AngCircle) [IsProbabilityMeasure ν]
    {w : AngCircle → ℝ} (hw : Measurable w) {S : ℝ} (hS : ∀ x, w x ^ 2 ≤ S) :
    ∫ x, w x ^ 2 * Real.log (w x ^ 2) ∂ν ≤ (∫ x, w x ^ 2 ∂ν) * Real.log S := by
  rw [← integral_mul_const]
  refine integral_mono (integrable_sq_mul_log_EX04910 ν hw hS)
    ((integrable_sq_EX04910 ν hw hS).mul_const _) fun x => ?_
  rcases eq_or_ne (w x ^ 2) 0 with h | h
  · simp [h]
  · exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (lt_of_le_of_ne (sq_nonneg _) (Ne.symm h)) (hS x)) (sq_nonneg _)

/-- The upper bound `Ent_ν (w ^ 2) ≤ M log (S / M)` for positive mass, with `S > 0`. -/
theorem ent_le_EX04910 (ν : Measure AngCircle) [IsProbabilityMeasure ν]
    {w : AngCircle → ℝ} (hw : Measurable w) {S : ℝ} (hS : ∀ x, w x ^ 2 ≤ S)
    (hM : 0 < ∫ x, w x ^ 2 ∂ν) :
    0 < S ∧ entEX04910 ν (fun x => w x ^ 2)
      ≤ (∫ x, w x ^ 2 ∂ν) * Real.log (S / ∫ x, w x ^ 2 ∂ν) := by
  have hSpos : 0 < S := lt_of_lt_of_le hM (integral_sq_le_EX04910 ν hw hS)
  refine ⟨hSpos, ?_⟩
  rw [Real.log_div hSpos.ne' hM.ne']
  have h := integral_sq_mul_log_le_EX04910 ν hw hS
  unfold entEX04910
  nlinarith

/-- Homogeneity `Ent_ν ((c w) ^ 2) = c ^ 2 Ent_ν (w ^ 2)` for every real `c`. -/
theorem ent_smul_EX04910 (ν : Measure AngCircle) [IsProbabilityMeasure ν]
    {w : AngCircle → ℝ} (hw : Measurable w) {S : ℝ} (hS : ∀ x, w x ^ 2 ≤ S) (c : ℝ) :
    entEX04910 ν (fun x => (c * w x) ^ 2) = c ^ 2 * entEX04910 ν (fun x => w x ^ 2) := by
  have hpt : ∀ x, (c * w x) ^ 2 * Real.log ((c * w x) ^ 2)
      = c ^ 2 * (w x ^ 2 * Real.log (w x ^ 2)) + c ^ 2 * Real.log (c ^ 2) * w x ^ 2 := by
    intro x
    rw [mul_pow]
    exact mul_log_mul_EX04910 (c ^ 2) (w x ^ 2)
  have hI := integrable_sq_mul_log_EX04910 ν hw hS
  have hJ := integrable_sq_EX04910 ν hw hS
  have hm : ∫ x, (c * w x) ^ 2 ∂ν = c ^ 2 * ∫ x, w x ^ 2 ∂ν := by
    simp_rw [mul_pow]
    exact integral_const_mul _ _
  have hl : ∫ x, (c * w x) ^ 2 * Real.log ((c * w x) ^ 2) ∂ν
      = c ^ 2 * ∫ x, w x ^ 2 * Real.log (w x ^ 2) ∂ν
        + c ^ 2 * Real.log (c ^ 2) * ∫ x, w x ^ 2 ∂ν := by
    simp_rw [hpt]
    rw [integral_add (hI.const_mul _) (hJ.const_mul _), integral_const_mul, integral_const_mul]
  unfold entEX04910
  rw [hm, hl]
  have h2 := mul_log_mul_EX04910 (c ^ 2) (∫ x, w x ^ 2 ∂ν)
  rw [mul_assoc (c ^ 2)] at h2
  linarith

/-- The statement of EX049.10. For a probability measure `ν` on the circle, a measurable `w` and
a pointwise bound `w x ^ 2 ≤ S`: the entropy of `w ^ 2` is finite (both `w ^ 2` and
`w ^ 2 log (w ^ 2)` are integrable); it vanishes at zero mass; for positive mass `S > 0` and
`Ent_ν (w ^ 2) ≤ M log (S / M)`; and `Ent_ν ((c w) ^ 2) = c ^ 2 Ent_ν (w ^ 2)` for every real `c`. -/
theorem ex049_10_entropy_finiteness_scalar_upper_bound_homogeneity
    (ν : Measure AngCircle) [IsProbabilityMeasure ν] (w : AngCircle → ℝ) (hw : Measurable w)
    (S : ℝ) (_hS0 : 0 ≤ S) (hS : ∀ x, w x ^ 2 ≤ S) :
    (Integrable (fun x => w x ^ 2) ν ∧
      Integrable (fun x => w x ^ 2 * Real.log (w x ^ 2)) ν) ∧
    ((∫ x, w x ^ 2 ∂ν = 0 → entEX04910 ν (fun x => w x ^ 2) = 0) ∧
      (0 < ∫ x, w x ^ 2 ∂ν → 0 < S ∧ entEX04910 ν (fun x => w x ^ 2)
        ≤ (∫ x, w x ^ 2 ∂ν) * Real.log (S / ∫ x, w x ^ 2 ∂ν))) ∧
    ∀ c : ℝ, entEX04910 ν (fun x => (c * w x) ^ 2) = c ^ 2 * entEX04910 ν (fun x => w x ^ 2) :=
  ⟨⟨integrable_sq_EX04910 ν hw hS, integrable_sq_mul_log_EX04910 ν hw hS⟩,
    ⟨ent_eq_zero_EX04910 ν hw hS, ent_le_EX04910 ν hw hS⟩, ent_smul_EX04910 ν hw hS⟩

/-- The entropy of the specification is the campaign entropy `homogeneousEntropy`, which is
therefore finite, for the square `w ^ 2`. -/
theorem ex049_10_entropy_finiteness_scalar_upper_bound_homogeneity_homogeneousEntropy
    (ν : Measure AngCircle) [IsProbabilityMeasure ν] (w : AngCircle → ℝ) (hw : Measurable w)
    (S : ℝ) (hS : ∀ x, w x ^ 2 ≤ S) :
    DGPS.homogeneousEntropy ν (fun x => w x ^ 2) = ENNReal.ofReal (entEX04910 ν (fun x => w x ^ 2))
      ∧ DGPS.homogeneousEntropy ν (fun x => w x ^ 2) ≠ ⊤ := by
  have h : DGPS.homogeneousEntropy ν (fun x => w x ^ 2)
      = ENNReal.ofReal (entEX04910 ν (fun x => w x ^ 2)) :=
    DGPS.homogeneousEntropy_eq_formula (Filter.Eventually.of_forall fun x => sq_nonneg (w x))
      (integrable_sq_EX04910 ν hw hS) (integrable_sq_mul_log_EX04910 ν hw hS)
  exact ⟨h, by rw [h]; exact ENNReal.ofReal_ne_top⟩

end DGPS.Frontier.EX049
