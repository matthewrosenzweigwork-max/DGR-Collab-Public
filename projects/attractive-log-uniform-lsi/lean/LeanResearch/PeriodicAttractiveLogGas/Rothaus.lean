import LeanResearch.PeriodicAttractiveLogGas.Entropy
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! Bounded-function Rothaus inequality for source Lemma 3.2.

The argument follows the scaling-parameter proof of Bakry--Gentil--Ledoux,
Analysis and Geometry of Markov Diffusion Operators (2014), Lemma 5.1.4,
printed page 239. A positive delta is inserted before differentiating the
entropy density. The variational estimate, differentiation under the integral,
curvature comparison, and removal of delta are proved below. This file does
not attribute a theorem number or proof to the inaccessible original paper.

The bounded-function input here is explicit. The eventual density lemma must
discharge it on its actual finite-domain functions. Separate semantic review
and protected verification have independent statuses. -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace PeriodicAttractiveLogGas

namespace Rothaus

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem integrable_continuous_comp_bounded [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ x, |f x| ≤ M)
    {k : ℝ → ℝ} (hk : Continuous k) : Integrable (fun x ↦ k (f x)) μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-M) M)).exists_bound_of_continuousOn
    hk.continuousOn
  exact Integrable.of_bound (hk.measurable.comp hf).aestronglyMeasurable C
    (Eventually.of_forall fun x ↦ hC (f x) (abs_le.mp (hb x)))

/-- Compactness supplies the domination needed for differentiation with a
bounded measurable input; no derivative-integral interchange is assumed. -/
theorem hasDerivAt_integral_comp_bounded [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ x, |f x| ≤ M)
    {P D : ℝ × ℝ → ℝ} (hP : Continuous P) (hD : Continuous D)
    (hderiv : ∀ r t, HasDerivAt (fun s ↦ P (s, t)) (D (r, t)) r) (r : ℝ) :
    HasDerivAt (fun s ↦ ∫ x, P (s, f x) ∂μ) (∫ x, D (r, f x) ∂μ) r := by
  obtain ⟨C, hC⟩ :=
    ((isCompact_Icc : IsCompact (Icc (r - 1) (r + 1))).prod
      (isCompact_Icc : IsCompact (Icc (-M) M))).exists_bound_of_continuousOn hD.continuousOn
  have hPm (s : ℝ) : AEStronglyMeasurable (fun x ↦ P (s, f x)) μ :=
    (hP.measurable.comp (measurable_const.prodMk hf)).aestronglyMeasurable
  have hDm : AEStronglyMeasurable (fun x ↦ D (r, f x)) μ :=
    (hD.measurable.comp (measurable_const.prodMk hf)).aestronglyMeasurable
  have hPi : Integrable (fun x ↦ P (r, f x)) μ :=
    integrable_continuous_comp_bounded hf hb
      (hP.comp (continuous_const.prodMk continuous_id))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun s x ↦ P (s, f x)) (F' := fun s x ↦ D (s, f x))
    (bound := fun _ ↦ C) (s := Ioo (r - 1) (r + 1))
    (Ioo_mem_nhds (by linarith) (by linarith)) (Eventually.of_forall hPm) hPi hDm
    (Eventually.of_forall fun x s hs ↦ hC (s, f x)
      ⟨⟨hs.1.le, hs.2.le⟩, abs_le.mp (hb x)⟩)
    (integrable_const C) (Eventually.of_forall fun x s _ ↦ hderiv s (f x))).2

/-- The finite real expression, identified with the actual extended entropy
whenever the input is bounded and measurable. -/
def squareEntropy (μ : Measure α) (f : α → ℝ) : ℝ :=
  (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ) -
    (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ)

theorem entropy_sq_eq [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    {M : ℝ} (hb : ∀ x, |f x| ≤ M) :
    entropy μ (fun x ↦ f x ^ 2) = (squareEntropy μ f : EReal) := by
  apply entropy_eq_integral (Eventually.of_forall fun x ↦ sq_nonneg (f x))
  exact integrable_continuous_comp_bounded hf hb
    (Real.continuous_mul_log.comp (continuous_id.pow 2))

theorem log_variational_pointwise {u v A S : ℝ}
    (hu : 0 ≤ u) (hv : 0 < v) (hA : 0 < A) (hS : 0 < S) :
    u * Real.log v - u * Real.log S ≤
      u * Real.log u - u * Real.log A + (A / S) * v - u := by
  rcases eq_or_lt_of_le hu with rfl | hu
  · simp only [zero_mul, sub_zero, zero_add]
    positivity
  have ht : 0 < A * v / (S * u) := div_pos (mul_pos hA hv) (mul_pos hS hu)
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos ht) hu.le
  rw [Real.log_div (mul_ne_zero hA.ne' hv.ne') (mul_ne_zero hS.ne' hu.ne'),
    Real.log_mul hA.ne' hv.ne', Real.log_mul hS.ne' hu.ne'] at h
  have he : u * (A * v / (S * u) - 1) = (A / S) * v - u := by
    field_simp [hS.ne', hu.ne']
  rw [he] at h
  nlinarith only [h]

/-- The variational inequality needed in the curvature calculation, proved
from the scalar logarithm inequality and actual integrability hypotheses. -/
theorem integral_log_variational [IsFiniteMeasure μ] {U V : α → ℝ}
    (hU : ∀ x, 0 ≤ U x) (hV : ∀ x, 0 < V x)
    (hUi : Integrable U μ) (hVi : Integrable V μ)
    (hUlog : Integrable (fun x ↦ U x * Real.log (U x)) μ)
    (hUVlog : Integrable (fun x ↦ U x * Real.log (V x)) μ)
    (hS : 0 < ∫ x, V x ∂μ) :
    (∫ x, U x * Real.log (V x) ∂μ) -
        (∫ x, U x ∂μ) * Real.log (∫ x, V x ∂μ) ≤
      (∫ x, U x * Real.log (U x) ∂μ) -
        (∫ x, U x ∂μ) * Real.log (∫ x, U x ∂μ) := by
  let A := ∫ x, U x ∂μ
  let S := ∫ x, V x ∂μ
  have hA : 0 ≤ A := integral_nonneg hU
  by_cases hA0 : A = 0
  · have hz : U =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hU hUi).mp hA0
    have hz₁ : (∫ x, U x * Real.log (V x) ∂μ) = 0 := by
      calc
        _ = ∫ x, (0 : ℝ) ∂μ := integral_congr_ae (hz.mono fun x hx ↦ by simp [hx])
        _ = 0 := integral_zero _ _
    have hz₂ : (∫ x, U x * Real.log (U x) ∂μ) = 0 := by
      calc
        _ = ∫ x, (0 : ℝ) ∂μ := integral_congr_ae (hz.mono fun x hx ↦ by simp [hx])
        _ = 0 := integral_zero _ _
    change _ - A * Real.log S ≤ _ - A * Real.log A
    simp [hA0, hz₁, hz₂]
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  have hLi : Integrable (fun x ↦ U x * Real.log (V x) - U x * Real.log S) μ :=
    hUVlog.sub (hUi.mul_const _)
  have hRi : Integrable (fun x ↦ U x * Real.log (U x) - U x * Real.log A +
      (A / S) * V x - U x) μ :=
    ((hUlog.sub (hUi.mul_const _)).add (hVi.const_mul _)).sub hUi
  have h := integral_mono hLi hRi
    (fun x ↦ log_variational_pointwise (hU x) (hV x) hAp hS)
  have hR₁ := integral_sub
    ((hUlog.sub (hUi.mul_const (Real.log A))).add (hVi.const_mul (A / S))) hUi
  have hR₂ := integral_add (hUlog.sub (hUi.mul_const (Real.log A)))
    (hVi.const_mul (A / S))
  have hR₃ := integral_sub hUlog (hUi.mul_const (Real.log A))
  dsimp only [Pi.sub_apply, Pi.add_apply] at hR₁ hR₂ hR₃
  rw [integral_sub hUVlog (hUi.mul_const _), hR₁, hR₂, hR₃,
    integral_mul_const, integral_mul_const, integral_const_mul] at h
  have he : (A / S) * S = A := div_mul_cancel₀ A hS.ne'
  change _ - A * Real.log S ≤ _ - A * Real.log A
  change _ - A * Real.log S ≤ _ - A * Real.log A + (A / S) * S - A at h
  linarith

/-- An upper second-derivative bound with zero value and slope at zero. -/
theorem curvature_bound {H D E : ℝ → ℝ} {C : ℝ}
    (hH : ∀ r, HasDerivAt H (D r) r) (hD : ∀ r, HasDerivAt D (E r) r)
    (hE : ∀ r, E r ≤ 2 * C) (h0 : H 0 = 0) (hD0 : D 0 = 0) : H 1 ≤ C := by
  let Q : ℝ → ℝ := fun r ↦ H r - C * r ^ 2
  let Q' : ℝ → ℝ := fun r ↦ D r - 2 * C * r
  have hQ (r : ℝ) : HasDerivAt Q (Q' r) r := by
    convert (hH r).sub (((hasDerivAt_id r).pow 2).const_mul C) using 1 <;>
      first | rfl | (try dsimp [Q, Q']; ring)
  have hQ' (r : ℝ) : HasDerivAt Q' (E r - 2 * C) r := by
    convert (hD r).sub ((hasDerivAt_id r).const_mul (2 * C)) using 1 <;>
      first | rfl | ring
  have hanti : Antitone Q' := antitone_of_hasDerivAt_nonpos hQ' (fun r ↦ by
    change E r - 2 * C ≤ 0
    linarith [hE r])
  have hQ0 : Q' 0 = 0 := by simp [Q', hD0]
  have hnonpos : ∀ r ∈ interior (Ici (0 : ℝ)), Q' r ≤ 0 := by
    intro r hr
    rw [← hQ0]
    exact hanti (interior_subset hr)
  have hantiQ : AntitoneOn Q (Ici (0 : ℝ)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun r _ ↦ (hQ r).continuousAt.continuousWithinAt)
      (fun r _ ↦ (hQ r).hasDerivWithinAt) hnonpos
  have h := hantiQ (by simp : (0 : ℝ) ∈ Ici 0) (by simp : (1 : ℝ) ∈ Ici 0) zero_le_one
  dsimp [Q] at h
  norm_num [h0] at h
  linarith

def value (a δ : ℝ) (z : ℝ × ℝ) : ℝ := (z.1 * z.2 + a) ^ 2 + δ
def valueFirst (a : ℝ) (z : ℝ × ℝ) : ℝ := 2 * z.2 * (z.1 * z.2 + a)
def pointEntropy (a δ : ℝ) (z : ℝ × ℝ) : ℝ :=
  value a δ z * Real.log (value a δ z)
def pointFirst (a δ : ℝ) (z : ℝ × ℝ) : ℝ :=
  valueFirst a z * (Real.log (value a δ z) + 1)
def pointSecond (a δ : ℝ) (z : ℝ × ℝ) : ℝ :=
  2 * z.2 ^ 2 * (Real.log (value a δ z) + 1) +
    4 * z.2 ^ 2 * (z.1 * z.2 + a) ^ 2 / value a δ z

theorem value_pos (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (z : ℝ × ℝ) :
    0 < value a δ z := by
  dsimp [value]
  positivity

theorem continuous_value (a δ : ℝ) : Continuous (value a δ) := by
  unfold value
  fun_prop

theorem continuous_valueFirst (a : ℝ) : Continuous (valueFirst a) := by
  unfold valueFirst
  fun_prop

theorem continuous_pointEntropy (a δ : ℝ) : Continuous (pointEntropy a δ) :=
  Real.continuous_mul_log.comp (continuous_value a δ)

theorem continuous_pointFirst (a : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (pointFirst a δ) :=
  (continuous_valueFirst a).mul
    (((continuous_value a δ).log (fun z ↦ (value_pos a hδ z).ne')).add continuous_const)

theorem continuous_pointSecond (a : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (pointSecond a δ) := by
  have hlog := (continuous_value a δ).log (fun z ↦ (value_pos a hδ z).ne')
  unfold pointSecond
  exact ((continuous_const.mul (continuous_snd.pow 2)).mul
    (hlog.add continuous_const)).add
      (((continuous_const.mul (continuous_snd.pow 2)).mul
        ((continuous_fst.mul continuous_snd).add continuous_const |>.pow 2)).div
          (continuous_value a δ) (fun z ↦ (value_pos a hδ z).ne'))

theorem hasDerivAt_value (a δ r t : ℝ) :
    HasDerivAt (fun s ↦ value a δ (s, t)) (valueFirst a (r, t)) r := by
  convert ((((hasDerivAt_id r).mul_const t).add_const a).pow 2).add_const δ using 1 <;>
    first | rfl | (try dsimp [value, valueFirst]; ring)

theorem hasDerivAt_valueFirst (a r t : ℝ) :
    HasDerivAt (fun s ↦ valueFirst a (s, t)) (2 * t ^ 2) r := by
  convert (((hasDerivAt_id r).mul_const t).add_const a).const_mul (2 * t) using 1 <;>
    first | rfl | ring

theorem hasDerivAt_pointEntropy (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (r t : ℝ) :
    HasDerivAt (fun s ↦ pointEntropy a δ (s, t)) (pointFirst a δ (r, t)) r := by
  convert (Real.hasDerivAt_mul_log (value_pos a hδ (r, t)).ne').comp r
    (hasDerivAt_value a δ r t) using 1 <;>
    first | rfl | (try dsimp [pointEntropy, pointFirst]; ring)

theorem hasDerivAt_pointFirst (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (r t : ℝ) :
    HasDerivAt (fun s ↦ pointFirst a δ (s, t)) (pointSecond a δ (r, t)) r := by
  have hv := hasDerivAt_value a δ r t
  have hd := (hasDerivAt_valueFirst a r t).mul
    ((hv.log (value_pos a hδ (r, t)).ne').add_const 1)
  convert hd using 1 <;> first | rfl |
    (try dsimp [pointSecond, pointFirst, valueFirst]
     field_simp [(value_pos a hδ (r, t)).ne']
     ring)

def mass (μ : Measure α) (f : α → ℝ) (a δ r : ℝ) : ℝ :=
  ∫ x, value a δ (r, f x) ∂μ
def massFirst (μ : Measure α) (f : α → ℝ) (a r : ℝ) : ℝ :=
  ∫ x, valueFirst a (r, f x) ∂μ
def curve (μ : Measure α) (f : α → ℝ) (a δ r : ℝ) : ℝ :=
  (∫ x, pointEntropy a δ (r, f x) ∂μ) -
    mass μ f a δ r * Real.log (mass μ f a δ r)
def curveFirst (μ : Measure α) (f : α → ℝ) (a δ r : ℝ) : ℝ :=
  (∫ x, pointFirst a δ (r, f x) ∂μ) -
    massFirst μ f a r * (Real.log (mass μ f a δ r) + 1)
def curveSecond (μ : Measure α) (f : α → ℝ) (a δ r : ℝ) : ℝ :=
  (∫ x, pointSecond a δ (r, f x) ∂μ) -
    (2 * (∫ x, f x ^ 2 ∂μ) * (Real.log (mass μ f a δ r) + 1) +
      massFirst μ f a r ^ 2 / mass μ f a δ r)

section Probability

variable [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Measurable f)
  {M : ℝ} (hb : ∀ x, |f x| ≤ M)

include hf hb

theorem integrable_value (a δ r : ℝ) : Integrable (fun x ↦ value a δ (r, f x)) μ :=
  integrable_continuous_comp_bounded hf hb
    ((continuous_value a δ).comp (continuous_const.prodMk continuous_id))

theorem mass_pos (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (r : ℝ) : 0 < mass μ f a δ r := by
  have h : δ ≤ mass μ f a δ r := by
    calc
      δ = ∫ x, δ ∂μ := by simp
      _ ≤ ∫ x, value a δ (r, f x) ∂μ :=
        integral_mono (integrable_const _) (integrable_value hf hb a δ r)
          (fun x ↦ by dsimp [value]; nlinarith [sq_nonneg (r * f x + a)])
  exact hδ.trans_le h

theorem hasDerivAt_mass (a δ r : ℝ) :
    HasDerivAt (mass μ f a δ) (massFirst μ f a r) r :=
  hasDerivAt_integral_comp_bounded hf hb (continuous_value a δ) (continuous_valueFirst a)
    (hasDerivAt_value a δ) r

theorem hasDerivAt_massFirst (a r : ℝ) :
    HasDerivAt (massFirst μ f a) (2 * ∫ x, f x ^ 2 ∂μ) r := by
  have h := hasDerivAt_integral_comp_bounded (μ := μ) hf hb (continuous_valueFirst a)
    (show Continuous (fun z : ℝ × ℝ ↦ 2 * z.2 ^ 2) by fun_prop)
    (hasDerivAt_valueFirst a) r
  simpa only [massFirst, integral_const_mul] using! h

theorem hasDerivAt_curve (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    HasDerivAt (curve μ f a δ) (curveFirst μ f a δ r) r := by
  have h₁ := hasDerivAt_integral_comp_bounded (μ := μ) hf hb (continuous_pointEntropy a δ)
    (continuous_pointFirst a hδ) (hasDerivAt_pointEntropy a hδ) r
  have h₂ := (Real.hasDerivAt_mul_log (mass_pos (μ := μ) hf hb a hδ r).ne').comp r
    (hasDerivAt_mass hf hb a δ r)
  convert h₁.sub h₂ using 1 <;> first | rfl | (try dsimp [curve, curveFirst]; ring)

theorem hasDerivAt_curveFirst (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    HasDerivAt (curveFirst μ f a δ) (curveSecond μ f a δ r) r := by
  have h₁ := hasDerivAt_integral_comp_bounded (μ := μ) hf hb (continuous_pointFirst a hδ)
    (continuous_pointSecond a hδ) (hasDerivAt_pointFirst a hδ) r
  have h₂ := (hasDerivAt_massFirst (μ := μ) hf hb a r).mul
    (((hasDerivAt_mass hf hb a δ r).log (mass_pos (μ := μ) hf hb a hδ r).ne').add_const 1)
  convert h₁.sub h₂ using 1 <;> first | rfl |
    (try dsimp [curveSecond, curveFirst]
     field_simp [(mass_pos (μ := μ) hf hb a hδ r).ne'])

theorem curveSecond_le (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    curveSecond μ f a δ r ≤ 2 * (squareEntropy μ f + 2 * ∫ x, f x ^ 2 ∂μ) := by
  have hsq : Integrable (fun x ↦ f x ^ 2) μ :=
    integrable_continuous_comp_bounded hf hb (continuous_id.pow 2)
  have hsqlog : Integrable (fun x ↦ f x ^ 2 * Real.log (f x ^ 2)) μ :=
    integrable_continuous_comp_bounded hf hb
      (Real.continuous_mul_log.comp (continuous_id.pow 2))
  have hlogcont : Continuous (fun t ↦ t ^ 2 * Real.log (value a δ (r, t))) :=
    (continuous_id.pow 2).mul
      (((continuous_value a δ).comp (continuous_const.prodMk continuous_id)).log
        (fun t ↦ (value_pos a hδ (r, t)).ne'))
  have hsqlogV : Integrable (fun x ↦ f x ^ 2 * Real.log (value a δ (r, f x))) μ :=
    integrable_continuous_comp_bounded hf hb hlogcont
  have hvar := integral_log_variational (fun x ↦ sq_nonneg (f x))
    (fun x ↦ value_pos a hδ (r, f x)) hsq (integrable_value hf hb a δ r)
    hsqlog hsqlogV (mass_pos (μ := μ) hf hb a hδ r)
  have hp₂ : Integrable (fun x ↦ pointSecond a δ (r, f x)) μ :=
    integrable_continuous_comp_bounded hf hb
      ((continuous_pointSecond a hδ).comp (continuous_const.prodMk continuous_id))
  have hpoint (t : ℝ) : pointSecond a δ (r, t) ≤
      2 * (t ^ 2 * Real.log (value a δ (r, t))) + 6 * t ^ 2 := by
    have hratio : (r * t + a) ^ 2 / value a δ (r, t) ≤ 1 := by
      apply (div_le_iff₀ (value_pos a hδ (r, t))).2
      dsimp [value]
      linarith
    have hmul := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 4 * t ^ 2)
    dsimp [pointSecond]
    rw [← mul_div_assoc] at hmul
    nlinarith
  have hI := integral_mono hp₂ ((hsqlogV.const_mul 2).add (hsq.const_mul 6))
    (fun x ↦ hpoint (f x))
  dsimp only [Pi.add_apply] at hI
  have hsplit := integral_add (hsqlogV.const_mul 2) (hsq.const_mul 6)
  try dsimp only [Pi.add_apply] at hsplit
  rw [hsplit,
    integral_const_mul, integral_const_mul] at hI
  have hlast : 0 ≤ massFirst μ f a r ^ 2 / mass μ f a δ r :=
    div_nonneg (sq_nonneg _) (mass_pos (μ := μ) hf hb a hδ r).le
  change _ - (∫ x, f x ^ 2 ∂μ) * Real.log (mass μ f a δ r) ≤ squareEntropy μ f at hvar
  dsimp [curveSecond]
  nlinarith

omit hf hb in
theorem mass_zero (a δ : ℝ) : mass μ f a δ 0 = a ^ 2 + δ := by
  simp [mass, value]

omit hf hb in
theorem curve_zero (a δ : ℝ) : curve μ f a δ 0 = 0 := by
  simp [curve, pointEntropy, mass, value]

omit hf hb in
theorem curveFirst_zero (a δ : ℝ) : curveFirst μ f a δ 0 = 0 := by
  simp only [curveFirst, pointFirst, valueFirst, value, zero_mul, zero_add,
    mass_zero, massFirst]
  rw [integral_mul_const]
  ring

/-- The regularized Rothaus estimate. The actual entropy, rather than a
formal integral expression, appears in the conclusion. -/
theorem regularized_shift_le (a : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    entropy μ (fun x ↦ (f x + a) ^ 2 + δ) ≤
      ((squareEntropy μ f + 2 * ∫ x, f x ^ 2 ∂μ : ℝ) : EReal) := by
  have h := curvature_bound (hasDerivAt_curve hf hb a hδ)
    (hasDerivAt_curveFirst hf hb a hδ) (curveSecond_le hf hb a hδ)
    (curve_zero (μ := μ) (f := f) a δ) (curveFirst_zero (μ := μ) (f := f) a δ)
  have hi : Integrable (fun x ↦ ((f x + a) ^ 2 + δ) *
      Real.log ((f x + a) ^ 2 + δ)) μ :=
    integrable_continuous_comp_bounded hf hb
      (Real.continuous_mul_log.comp ((continuous_id.add continuous_const).pow 2 |>.add continuous_const))
  rw [entropy_eq_integral (Eventually.of_forall fun x ↦ by positivity) hi]
  exact_mod_cast (show (∫ x, ((f x + a) ^ 2 + δ) * Real.log ((f x + a) ^ 2 + δ) ∂μ) -
    (∫ x, (f x + a) ^ 2 + δ ∂μ) * Real.log (∫ x, (f x + a) ^ 2 + δ ∂μ) ≤
      squareEntropy μ f + 2 * ∫ x, f x ^ 2 ∂μ from by simpa [curve, mass, pointEntropy, value] using h)

end Probability

/-- Full bounded Rothaus shift inequality for the existing extended entropy.
The input need not have mean zero, and the shift is any real number. -/
theorem shift_le [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Measurable f)
    (hbounded : ∃ M : ℝ, ∀ x, |f x| ≤ M) (a : ℝ) :
    entropy μ (fun x ↦ (f x + a) ^ 2) ≤
      entropy μ (fun x ↦ f x ^ 2) + ((2 * ∫ x, f x ^ 2 ∂μ : ℝ) : EReal) := by
  obtain ⟨M, hb⟩ := hbounded
  let δ : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hsq : Integrable (fun x ↦ (f x + a) ^ 2) μ :=
    integrable_continuous_comp_bounded hf hb ((continuous_id.add continuous_const).pow 2)
  let C : ℝ := squareEntropy μ f + 2 * ∫ x, f x ^ 2 ∂μ
  have hmass (n : ℕ) : (∫ x, (f x + a) ^ 2 + δ n ∂μ) =
      (∫ x, (f x + a) ^ 2 ∂μ) + δ n := by
    rw [integral_add hsq (integrable_const _)]
    simp
  have hmasses : Tendsto (fun n ↦ ∫ x, (f x + a) ^ 2 + δ n ∂μ) atTop
      (𝓝 (∫ x, (f x + a) ^ 2 ∂μ)) := by
    simp_rw [hmass]
    simpa using tendsto_const_nhds.add hδlim
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ (f x + a) ^ 2 + δ n) atTop
      (𝓝 ((f x + a) ^ 2)) := by
    exact Eventually.of_forall fun x ↦ by simpa using tendsto_const_nhds.add hδlim
  have h := entropy_le_of_ae_tendsto
    (μ := μ) (F := fun n x ↦ (f x + a) ^ 2 + δ n)
    (f := fun x ↦ (f x + a) ^ 2) (b := fun _ ↦ C)
    (fun n ↦ (((hf.add measurable_const).pow_const 2).add measurable_const).aemeasurable)
    hlim hmasses tendsto_const_nhds (fun n ↦ regularized_shift_le hf hb a (hδ n))
  rw [entropy_sq_eq hf hb, ← EReal.coe_add]
  exact h

/-- Explicit zero-second-moment case, including every shift. No positivity
of the second moment is required in `shift_le`. -/
theorem entropy_sq_and_shift_zero [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : Measurable f) (hbounded : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (hzero : (∫ x, f x ^ 2 ∂μ) = 0) :
    entropy μ (fun x ↦ f x ^ 2) = 0 ∧
      ∀ a : ℝ, entropy μ (fun x ↦ (f x + a) ^ 2) = 0 := by
  obtain ⟨M, hb⟩ := hbounded
  have hi : Integrable (fun x ↦ f x ^ 2) μ :=
    integrable_continuous_comp_bounded hf hb (continuous_id.pow 2)
  have hz : (fun x ↦ f x ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg (f x)) hi).mp hzero
  have hfz : f =ᵐ[μ] 0 := hz.mono fun x hx ↦ sq_eq_zero_iff.mp hx
  constructor
  · exact (entropy_congr_ae hz).trans (entropy_zero μ)
  · intro a
    have he : (fun x ↦ (f x + a) ^ 2) =ᵐ[μ] fun _ ↦ a ^ 2 :=
      hfz.mono fun x hx ↦ by simp [hx]
    exact (entropy_congr_ae he).trans (entropy_const μ (sq_nonneg a))

end Rothaus

/-- An almost-everywhere bounded measurable class has a genuinely bounded
measurable representative, without any condition outside the measure's support. -/
theorem exists_bounded_measurable_ae_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : AEMeasurable f μ) {M : ℝ} (hb : ∀ᵐ x ∂μ, |f x| ≤ M) :
    ∃ g : α → ℝ, Measurable g ∧ (∀ x, |g x| ≤ max M 0) ∧ f =ᵐ[μ] g := by
  let g : α → ℝ := fun x ↦ if |hf.mk f x| ≤ max M 0 then hf.mk f x else 0
  refine ⟨g, ?_, ?_, ?_⟩
  · exact Measurable.ite (measurableSet_le (continuous_abs.measurable.comp hf.measurable_mk)
      measurable_const)
      hf.measurable_mk measurable_const
  · intro x
    dsimp only [g]
    split_ifs with hx
    · exact hx
    · simp only [abs_zero, le_max_iff, le_refl, or_true]
  · filter_upwards [hf.ae_eq_mk, hb] with x hx hbx
    dsimp only [g]
    simp only [← hx, hbx.trans (le_max_left M 0), ite_true]

/-- The precise centering inequality used in source Lemma 3.2, with the
ordinary mean and variance, for any bounded measurable real function. -/
theorem rothaus_centering {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Measurable f)
    (hbounded : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    entropy μ (fun x ↦ f x ^ 2) ≤
      entropy μ (fun x ↦ (f x - ∫ y, f y ∂μ) ^ 2) +
        ((2 * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ : ℝ) : EReal) := by
  obtain ⟨M, hb⟩ := hbounded
  have hc : ∃ B : ℝ, ∀ x, |f x - ∫ y, f y ∂μ| ≤ B := by
    refine ⟨M + |∫ y, f y ∂μ|, fun x ↦ ?_⟩
    exact (abs_sub (f x) _).trans (add_le_add (hb x) le_rfl)
  simpa only [Pi.sub_apply, sub_add_cancel] using
    (Rothaus.shift_le (μ := μ) (hf.sub measurable_const) hc (∫ y, f y ∂μ))

/-- Degenerate centered input is covered by actual AE equality to a constant. -/
theorem rothaus_centering_zero_variance {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Measurable f)
    (hbounded : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (hzero : (∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ) = 0) :
    entropy μ (fun x ↦ f x ^ 2) = 0 := by
  obtain ⟨M, hb⟩ := hbounded
  have hc : ∃ B : ℝ, ∀ x, |f x - ∫ y, f y ∂μ| ≤ B := by
    exact ⟨M + |∫ y, f y ∂μ|, fun x ↦
      (abs_sub (f x) _).trans (add_le_add (hb x) le_rfl)⟩
  simpa only [Pi.sub_apply, sub_add_cancel] using
    (Rothaus.entropy_sq_and_shift_zero (hf.sub measurable_const) hc hzero).2 (∫ y, f y ∂μ)

/-- The same centering inequality for an almost-everywhere bounded measurable
class, which is the form needed on restricted rectangle measures. -/
theorem rothaus_centering_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : AEMeasurable f μ)
    (hbounded : ∃ M : ℝ, ∀ᵐ x ∂μ, |f x| ≤ M) :
    entropy μ (fun x ↦ f x ^ 2) ≤
      entropy μ (fun x ↦ (f x - ∫ y, f y ∂μ) ^ 2) +
        ((2 * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ : ℝ) : EReal) := by
  obtain ⟨M, hb⟩ := hbounded
  obtain ⟨g, hg, hgb, heq⟩ := exists_bounded_measurable_ae_eq hf hb
  have hm : (∫ x, f x ∂μ) = ∫ x, g x ∂μ := integral_congr_ae heq
  have hs : (fun x ↦ f x ^ 2) =ᵐ[μ] fun x ↦ g x ^ 2 :=
    heq.mono fun x hx ↦ congrArg (fun t : ℝ ↦ t ^ 2) hx
  have hc : (fun x ↦ (f x - ∫ y, f y ∂μ) ^ 2) =ᵐ[μ]
      fun x ↦ (g x - ∫ y, g y ∂μ) ^ 2 := heq.mono fun x hx ↦ by
    simpa only [hm] using congrArg (fun t : ℝ ↦ (t - ∫ y, g y ∂μ) ^ 2) hx
  rw [entropy_congr_ae hs, entropy_congr_ae hc, integral_congr_ae hc]
  exact rothaus_centering hg ⟨max M 0, hgb⟩

end PeriodicAttractiveLogGas
