import DGPS.Frontier.EX012.T36

/-!
# EX012.16: Admissible normalized variation

Task id: EX012.16 (node EX012, leaf formalization).
Title: Admissible normalized variation.

For a positive smooth one-periodic `u` of unit `L²` mass on `[0,1]` and a smooth one-periodic real
`ξ`, put `v_t = u + tξ`, `N_t = (∫₀¹ v_t²)^(1/2)`, `u_t = v_t / N_t`. With `m = min u`,
`M = max u`, `Q = ‖ξ‖∞`, `B = M + Q` and `δ = min(1, m / (2 max(1,Q)))`, for `|t| < δ` each `u_t`
is admissible (`IsAdmSmooth_EX01236`: smooth, one-periodic, positive, mass one), and
`(d/dt) u_t |₀ = η := ξ - u ∫ uξ`. The uniform bounds recorded in the specification's proof
(`m/2 ≤ v_t ≤ B`, `m/2 ≤ N_t ≤ B`, `m/(2B) ≤ u_t ≤ 2B/m`, `|∂_t u_t| ≤ 2Q/m + 8B²Q/m³`) are
part of the conclusion, because the consumers (EX012.18, EX012.19) use them.

## Provides

* `DGPS.Frontier.EX012.ex012_16_admissible_normalized_variation`: for admissible `u`, smooth
  periodic `ξ`, and `m = min u`, `M = max u`, `Q = ‖ξ‖∞`: `0 < m`, `0 < δ`; for `|t| < δ` the
  function `u_t` is admissible, with the bounds above and `HasDerivAt (fun s => u_s x) (∂_t u_t x) t`
  for every `x`; moreover `u_0 = u` and `HasDerivAt (fun s => u_s x) (η x) 0` and
  `deriv (fun s => u_s x) 0 = η x`.
* `DGPS.Frontier.EX012.vcurve_EX01216`, `massSq_EX01216`, `normCurve_EX01216`, `ucurve_EX01216`,
  `delta_EX01216`, `eta_EX01216`, `dcurve_EX01216`: the objects `v_t x`, `∫ v_t²`, `N_t`, `u_t x`,
  `δ`, `η x`, and the explicit derivative `∂_t u_t x = ξ x / N_t - v_t x (∫ v_t ξ) / N_t³`.
* Helper lemmas, all with the suffix `_EX01216`: the exact expansion of `∫ v_t²` and `∫ v_t ξ`
  as polynomials in `t`, its derivative, the bound lemmas, and the pieces of the main theorem
  (`setup_*_EX01216`, stated for the bundle `Setup_EX01216`).

## R5 notes

* Domains. `u ξ : ℝ → ℝ` are one-periodic functions on the line (the form consumed by EX012.36's
  `IsAdmSmooth_EX01236` and `smoothDensity_EX01236`), integrals are `∫ x in (0:ℝ)..1`. "Positive
  smooth normalized" is read as `IsAdmSmooth_EX01236 u`; "real smooth periodic `ξ`" as
  `ContDiff ℝ ∞ ξ` and `Function.Periodic ξ 1`. "Admissible positive smooth normalized square
  roots" is read as `IsAdmSmooth_EX01236 (u_t)`.
* `m = min u`, `M = max u`, `Q = ‖ξ‖∞` are not computed: they enter as variables with
  `IsLeast (Set.range u) m`, `IsGreatest (Set.range u) M`,
  `IsLUB (Set.range fun x => |ξ x|) Q`. These are exactly the defining properties (existence is
  by compactness of the period and is not needed). `0 < m` is derived from positivity of `u`,
  not assumed. The proof uses only the inequalities `m ≤ u ≤ M`, `|ξ| ≤ Q`.
* The derivative `(d/dt) u_t |₀` is pointwise in `x` (`HasDerivAt` of `s ↦ u_s x` at `0`), not a
  derivative in a function space; no Banach-space norm is attached. The same pointwise derivative
  with explicit value is given at every `|t| < δ` (needed by EX012.18).
* The finite parameter integral of the polynomial `v_t²` is not differentiated under the integral
  sign: `∫ v_t²` and `∫ v_t ξ` are expanded exactly in `t`, so `N'` comes from the derivative of a
  quadratic polynomial composed with the square root (`N_t² > 0` for `|t| < δ`).
* The bound `|∂_t u_t| ≤ 2Q/m + 8B²Q/m³` is stated with `B = M + Q` written out.
* Only EX012.36 (via `IsAdmSmooth_EX01236`) is imported; EX012.13 is not needed.
-/

open MeasureTheory
open scoped ContDiff

namespace DGPS.Frontier.EX012

/-- `v_t = u + tξ`. -/
def vcurve_EX01216 (u ξ : ℝ → ℝ) (t x : ℝ) : ℝ := u x + t * ξ x

/-- `∫ v_t²`. -/
noncomputable def massSq_EX01216 (u ξ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..1, vcurve_EX01216 u ξ t x ^ 2

/-- `N_t`. -/
noncomputable def normCurve_EX01216 (u ξ : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (massSq_EX01216 u ξ t)

/-- `u_t`. -/
noncomputable def ucurve_EX01216 (u ξ : ℝ → ℝ) (t x : ℝ) : ℝ :=
  vcurve_EX01216 u ξ t x / normCurve_EX01216 u ξ t

/-- `δ`. -/
noncomputable def delta_EX01216 (m Q : ℝ) : ℝ := min 1 (m / (2 * max 1 Q))

/-- `η`. -/
noncomputable def eta_EX01216 (u ξ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ξ x - u x * ∫ y in (0:ℝ)..1, u y * ξ y

/-- `∂_t u_t`. -/
noncomputable def dcurve_EX01216 (u ξ : ℝ → ℝ) (t x : ℝ) : ℝ :=
  ξ x / normCurve_EX01216 u ξ t
    - vcurve_EX01216 u ξ t x * (∫ y in (0:ℝ)..1, vcurve_EX01216 u ξ t y * ξ y)
      / normCurve_EX01216 u ξ t ^ 3

theorem massSq_expand_EX01216 {u ξ : ℝ → ℝ} (hu : Continuous u) (hξ : Continuous ξ) (t : ℝ) :
    massSq_EX01216 u ξ t = (∫ x in (0:ℝ)..1, u x ^ 2) + 2 * t * (∫ x in (0:ℝ)..1, u x * ξ x)
      + t ^ 2 * ∫ x in (0:ℝ)..1, ξ x ^ 2 := by
  unfold massSq_EX01216 vcurve_EX01216
  have h1 : IntervalIntegrable (fun x => u x ^ 2) MeasureTheory.volume 0 1 :=
    (hu.pow 2).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x => 2 * t * (u x * ξ x)) MeasureTheory.volume 0 1 :=
    (continuous_const.mul (hu.mul hξ)).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun x => t ^ 2 * ξ x ^ 2) MeasureTheory.volume 0 1 :=
    (continuous_const.mul (hξ.pow 2)).intervalIntegrable _ _
  have : ∀ x, (u x + t * ξ x) ^ 2 = u x ^ 2 + 2 * t * (u x * ξ x) + t ^ 2 * ξ x ^ 2 := fun x => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem cross_expand_EX01216 {u ξ : ℝ → ℝ} (hu : Continuous u) (hξ : Continuous ξ) (t : ℝ) :
    (∫ x in (0:ℝ)..1, vcurve_EX01216 u ξ t x * ξ x) = (∫ x in (0:ℝ)..1, u x * ξ x)
      + t * ∫ x in (0:ℝ)..1, ξ x ^ 2 := by
  unfold vcurve_EX01216
  have h2 : IntervalIntegrable (fun x => u x * ξ x) MeasureTheory.volume 0 1 :=
    (hu.mul hξ).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun x => t * ξ x ^ 2) MeasureTheory.volume 0 1 :=
    (continuous_const.mul (hξ.pow 2)).intervalIntegrable _ _
  have : ∀ x, (u x + t * ξ x) * ξ x = u x * ξ x + t * ξ x ^ 2 := fun x => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_add h2 h3, intervalIntegral.integral_const_mul]

theorem hasDerivAt_massSq_EX01216 {u ξ : ℝ → ℝ} (hu : Continuous u) (hξ : Continuous ξ) (t : ℝ) :
    HasDerivAt (massSq_EX01216 u ξ) (2 * ∫ x in (0:ℝ)..1, vcurve_EX01216 u ξ t x * ξ x) t := by
  have e : massSq_EX01216 u ξ = fun t => (∫ x in (0:ℝ)..1, u x ^ 2) + 2 * t * (∫ x in (0:ℝ)..1, u x * ξ x)
      + t ^ 2 * ∫ x in (0:ℝ)..1, ξ x ^ 2 := funext (massSq_expand_EX01216 hu hξ)
  rw [e, cross_expand_EX01216 hu hξ]
  have := (((hasDerivAt_id t).const_mul 2).mul_const (∫ x in (0:ℝ)..1, u x * ξ x)).const_add (∫ x in (0:ℝ)..1, u x ^ 2)
  have h2 := ((hasDerivAt_pow 2 t).mul_const (∫ x in (0:ℝ)..1, ξ x ^ 2))
  refine HasDerivAt.congr_deriv (this.add h2) ?_
  simp
  ring


theorem delta_bound_EX01216 {m Q t : ℝ} (hm : 0 < m) (hQ : 0 ≤ Q) (ht : |t| < delta_EX01216 m Q) :
    |t| < 1 ∧ |t| * Q ≤ m / 2 := by
  unfold delta_EX01216 at ht
  have h1 : |t| < 1 := lt_of_lt_of_le ht (min_le_left _ _)
  have h2 : |t| < m / (2 * max 1 Q) := lt_of_lt_of_le ht (min_le_right _ _)
  refine ⟨h1, ?_⟩
  have hpos : 0 < max 1 Q := lt_of_lt_of_le one_pos (le_max_left _ _)
  rw [lt_div_iff₀ (by positivity)] at h2
  have : Q ≤ max 1 Q := le_max_right _ _
  nlinarith [abs_nonneg t]

theorem v_bounds_EX01216 {u ξ : ℝ → ℝ} {m M Q t : ℝ} (hm : ∀ x, m ≤ u x) (hM : ∀ x, u x ≤ M)
    (hQ : ∀ x, |ξ x| ≤ Q) (ht1 : |t| < 1) (ht2 : |t| * Q ≤ m / 2) (x : ℝ) :
    m / 2 ≤ vcurve_EX01216 u ξ t x ∧ vcurve_EX01216 u ξ t x ≤ M + Q := by
  have hQ0 : 0 ≤ Q := (abs_nonneg _).trans (hQ 0)
  have h3 : |t * ξ x| ≤ |t| * Q := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hQ x) (abs_nonneg _)
  have h4 : |t| * Q ≤ Q := by nlinarith [abs_nonneg t]
  have := abs_le.1 h3
  unfold vcurve_EX01216
  have := hm x
  have := hM x
  constructor <;> linarith [this]

theorem massSq_bounds_EX01216 {u ξ : ℝ → ℝ} (hu : Continuous u) (hξ : Continuous ξ)
    {m B t : ℝ} (hlo : ∀ x, m / 2 ≤ vcurve_EX01216 u ξ t x)
    (hhi : ∀ x, vcurve_EX01216 u ξ t x ≤ B) (hm : 0 < m) :
    (m / 2) ^ 2 ≤ massSq_EX01216 u ξ t ∧ massSq_EX01216 u ξ t ≤ B ^ 2 := by
  have hc : Continuous fun x => vcurve_EX01216 u ξ t x ^ 2 :=
    ((hu.add (continuous_const.mul hξ)).pow 2)
  have hi : IntervalIntegrable (fun x => vcurve_EX01216 u ξ t x ^ 2) MeasureTheory.volume 0 1 :=
    hc.intervalIntegrable _ _
  have hci : ∀ c : ℝ, IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume 0 1 :=
    fun c => intervalIntegrable_const
  constructor
  · have := intervalIntegral.integral_mono_on (zero_le_one' ℝ) (hci ((m / 2) ^ 2)) hi
      (fun x _ => pow_le_pow_left₀ (by positivity) (hlo x) 2)
    simpa [massSq_EX01216] using this
  · have := intervalIntegral.integral_mono_on (zero_le_one' ℝ) hi (hci (B ^ 2))
      (fun x _ => pow_le_pow_left₀ (by linarith [hlo x, hm]) (hhi x) 2)
    simpa [massSq_EX01216] using this


/-- The data of the specification with `m`, `M`, `Q` replaced by their defining inequalities. -/
structure Setup_EX01216 (u ξ : ℝ → ℝ) (m M Q : ℝ) : Prop where
  adm : IsAdmSmooth_EX01236 u
  smooth : ContDiff ℝ ∞ ξ
  periodic : Function.Periodic ξ 1
  m_pos : 0 < m
  lower : ∀ x, m ≤ u x
  upper : ∀ x, u x ≤ M
  bound : ∀ x, |ξ x| ≤ Q

theorem setup_Q_nonneg_EX01216 {u ξ : ℝ → ℝ} {m M Q : ℝ} (h : Setup_EX01216 u ξ m M Q) :
    0 ≤ Q := (abs_nonneg _).trans (h.bound 0)

theorem setup_m_le_M_EX01216 {u ξ : ℝ → ℝ} {m M Q : ℝ} (h : Setup_EX01216 u ξ m M Q) :
    m ≤ M := (h.lower 0).trans (h.upper 0)

theorem setup_v_bounds_EX01216 {u ξ : ℝ → ℝ} {m M Q t : ℝ} (h : Setup_EX01216 u ξ m M Q)
    (ht : |t| < delta_EX01216 m Q) (x : ℝ) :
    m / 2 ≤ vcurve_EX01216 u ξ t x ∧ vcurve_EX01216 u ξ t x ≤ M + Q :=
  v_bounds_EX01216 h.lower h.upper h.bound
    (delta_bound_EX01216 h.m_pos (setup_Q_nonneg_EX01216 h) ht).1
    (delta_bound_EX01216 h.m_pos (setup_Q_nonneg_EX01216 h) ht).2 x

theorem setup_N_bounds_EX01216 {u ξ : ℝ → ℝ} {m M Q t : ℝ} (h : Setup_EX01216 u ξ m M Q)
    (ht : |t| < delta_EX01216 m Q) :
    m / 2 ≤ normCurve_EX01216 u ξ t ∧ normCurve_EX01216 u ξ t ≤ M + Q := by
  have hb := massSq_bounds_EX01216 h.adm.smooth.continuous h.smooth.continuous
    (fun x => (setup_v_bounds_EX01216 h ht x).1) (fun x => (setup_v_bounds_EX01216 h ht x).2)
    h.m_pos
  have hB : 0 ≤ M + Q := by linarith [h.m_pos, setup_m_le_M_EX01216 h, setup_Q_nonneg_EX01216 h]
  unfold normCurve_EX01216
  constructor
  · calc m / 2 = Real.sqrt ((m / 2) ^ 2) := (Real.sqrt_sq (by linarith [h.m_pos])).symm
      _ ≤ _ := Real.sqrt_le_sqrt hb.1
  · calc _ ≤ Real.sqrt ((M + Q) ^ 2) := Real.sqrt_le_sqrt hb.2
      _ = M + Q := Real.sqrt_sq hB

theorem setup_N_pos_EX01216 {u ξ : ℝ → ℝ} {m M Q t : ℝ} (h : Setup_EX01216 u ξ m M Q)
    (ht : |t| < delta_EX01216 m Q) : 0 < normCurve_EX01216 u ξ t := by
  linarith [(setup_N_bounds_EX01216 h ht).1, h.m_pos]

theorem setup_massSq_pos_EX01216 {u ξ : ℝ → ℝ} {m M Q t : ℝ} (h : Setup_EX01216 u ξ m M Q)
    (ht : |t| < delta_EX01216 m Q) : 0 < massSq_EX01216 u ξ t := by
  have := setup_N_pos_EX01216 h ht
  unfold normCurve_EX01216 at this
  exact Real.sqrt_pos.1 this

theorem setup_admissible_EX01216 {u ξ : ℝ → ℝ} {m M Q t : ℝ} (h : Setup_EX01216 u ξ m M Q)
    (ht : |t| < delta_EX01216 m Q) : IsAdmSmooth_EX01236 (ucurve_EX01216 u ξ t) := by
  have hN := setup_N_pos_EX01216 h ht
  have hS := setup_massSq_pos_EX01216 h ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold ucurve_EX01216 vcurve_EX01216
    exact (h.adm.smooth.add (contDiff_const.mul h.smooth)).div_const _
  · intro x
    unfold ucurve_EX01216 vcurve_EX01216
    rw [h.adm.periodic x, h.periodic x]
  · intro x
    unfold ucurve_EX01216
    exact div_pos (by linarith [(setup_v_bounds_EX01216 h ht x).1, h.m_pos]) hN
  · have e : ∀ x, ucurve_EX01216 u ξ t x ^ 2 = vcurve_EX01216 u ξ t x ^ 2 / massSq_EX01216 u ξ t := by
      intro x
      unfold ucurve_EX01216 normCurve_EX01216
      rw [div_pow, Real.sq_sqrt hS.le]
    simp_rw [e]
    rw [intervalIntegral.integral_div]
    exact div_self hS.ne'


theorem setup_ucurve_bounds_EX01216 {u ξ : ℝ → ℝ} {m M Q t : ℝ} (h : Setup_EX01216 u ξ m M Q)
    (ht : |t| < delta_EX01216 m Q) (x : ℝ) :
    m / (2 * (M + Q)) ≤ ucurve_EX01216 u ξ t x ∧ ucurve_EX01216 u ξ t x ≤ 2 * (M + Q) / m := by
  have hN := setup_N_pos_EX01216 h ht
  have hNb := setup_N_bounds_EX01216 h ht
  have hv := setup_v_bounds_EX01216 h ht x
  have hm := h.m_pos
  have hB : 0 < M + Q := by linarith [setup_m_le_M_EX01216 h, setup_Q_nonneg_EX01216 h]
  unfold ucurve_EX01216
  constructor
  · calc m / (2 * (M + Q)) = (m / 2) / (M + Q) := by field_simp
      _ ≤ _ := div_le_div₀ (by linarith) hv.1 hN hNb.2
  · calc _ ≤ (M + Q) / (m / 2) :=
          div_le_div₀ hB.le hv.2 (by linarith) hNb.1
      _ = _ := by field_simp

theorem setup_cross_bound_EX01216 {u ξ : ℝ → ℝ} {m M Q t : ℝ} (h : Setup_EX01216 u ξ m M Q)
    (ht : |t| < delta_EX01216 m Q) :
    |∫ y in (0:ℝ)..1, vcurve_EX01216 u ξ t y * ξ y| ≤ (M + Q) * Q := by
  have hm := h.m_pos
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (f := fun y => vcurve_EX01216 u ξ t y * ξ y) (C := (M + Q) * Q) (by
      intro y _
      rw [Real.norm_eq_abs, abs_mul]
      have hv := setup_v_bounds_EX01216 h ht y
      have : |vcurve_EX01216 u ξ t y| ≤ M + Q := by
        rw [abs_of_nonneg (by linarith [hv.1])]; exact hv.2
      exact mul_le_mul this (h.bound y) (abs_nonneg _)
        (by linarith [setup_m_le_M_EX01216 h, setup_Q_nonneg_EX01216 h]))
  simpa using this

theorem setup_hasDerivAt_ucurve_EX01216 {u ξ : ℝ → ℝ} {m M Q t : ℝ} (h : Setup_EX01216 u ξ m M Q)
    (ht : |t| < delta_EX01216 m Q) (x : ℝ) :
    HasDerivAt (fun s => ucurve_EX01216 u ξ s x) (dcurve_EX01216 u ξ t x) t := by
  have hN := setup_N_pos_EX01216 h ht
  have hS := setup_massSq_pos_EX01216 h ht
  have hSd := hasDerivAt_massSq_EX01216 h.adm.smooth.continuous h.smooth.continuous t
  have hNd : HasDerivAt (normCurve_EX01216 u ξ)
      ((2 * ∫ y in (0:ℝ)..1, vcurve_EX01216 u ξ t y * ξ y) / (2 * normCurve_EX01216 u ξ t)) t :=
    hSd.sqrt hS.ne'
  have hvd : HasDerivAt (fun s => vcurve_EX01216 u ξ s x) (ξ x) t := by
    unfold vcurve_EX01216
    simpa using ((hasDerivAt_id t).mul_const (ξ x)).const_add (u x)
  have hq := hvd.div hNd hN.ne'
  refine HasDerivAt.congr_deriv hq ?_
  unfold dcurve_EX01216
  field_simp

theorem setup_dcurve_bound_EX01216 {u ξ : ℝ → ℝ} {m M Q t : ℝ} (h : Setup_EX01216 u ξ m M Q)
    (ht : |t| < delta_EX01216 m Q) (x : ℝ) :
    |dcurve_EX01216 u ξ t x| ≤ 2 * Q / m + 8 * (M + Q) ^ 2 * Q / m ^ 3 := by
  have hN := setup_N_pos_EX01216 h ht
  have hNb := setup_N_bounds_EX01216 h ht
  have hv := setup_v_bounds_EX01216 h ht x
  have hm := h.m_pos
  have hQ := setup_Q_nonneg_EX01216 h
  have hB : 0 < M + Q := by linarith [setup_m_le_M_EX01216 h, setup_Q_nonneg_EX01216 h]
  have hI := setup_cross_bound_EX01216 h ht
  unfold dcurve_EX01216
  have t1 : |ξ x / normCurve_EX01216 u ξ t| ≤ 2 * Q / m := by
    rw [abs_div, abs_of_pos hN]
    calc _ ≤ Q / (m / 2) := div_le_div₀ hQ (h.bound x) (by linarith) hNb.1
      _ = _ := by field_simp
  have t2 : |vcurve_EX01216 u ξ t x * (∫ y in (0:ℝ)..1, vcurve_EX01216 u ξ t y * ξ y)
      / normCurve_EX01216 u ξ t ^ 3| ≤ 8 * (M + Q) ^ 2 * Q / m ^ 3 := by
    rw [abs_div, abs_mul, abs_of_nonneg (by linarith [hv.1] : 0 ≤ vcurve_EX01216 u ξ t x),
      abs_of_pos (pow_pos hN 3)]
    calc _ ≤ ((M + Q) * ((M + Q) * Q)) / (m / 2) ^ 3 := by
          refine div_le_div₀ (by positivity) ?_ (by positivity) ?_
          · exact mul_le_mul hv.2 hI (abs_nonneg _) hB.le
          · exact pow_le_pow_left₀ (by linarith) hNb.1 3
      _ = _ := by field_simp; norm_num
  exact (abs_sub _ _).trans (add_le_add t1 t2)


theorem delta_pos_EX01216 {m Q : ℝ} (hm : 0 < m) : 0 < delta_EX01216 m Q := by
  unfold delta_EX01216
  exact lt_min one_pos (div_pos hm (by positivity))

theorem normCurve_zero_EX01216 {u ξ : ℝ → ℝ} (hu : IsAdmSmooth_EX01236 u) :
    normCurve_EX01216 u ξ 0 = 1 := by
  unfold normCurve_EX01216 massSq_EX01216 vcurve_EX01216
  simp only [zero_mul, add_zero]
  rw [hu.mass, Real.sqrt_one]

theorem ucurve_zero_EX01216 {u ξ : ℝ → ℝ} (hu : IsAdmSmooth_EX01236 u) (x : ℝ) :
    ucurve_EX01216 u ξ 0 x = u x := by
  unfold ucurve_EX01216 vcurve_EX01216
  rw [normCurve_zero_EX01216 hu]
  simp

theorem dcurve_zero_EX01216 {u ξ : ℝ → ℝ} (hu : IsAdmSmooth_EX01236 u) (x : ℝ) :
    dcurve_EX01216 u ξ 0 x = eta_EX01216 u ξ x := by
  unfold dcurve_EX01216 eta_EX01216 vcurve_EX01216
  rw [normCurve_zero_EX01216 hu]
  simp

theorem ex012_16_admissible_normalized_variation {u ξ : ℝ → ℝ}
    (hu : IsAdmSmooth_EX01236 u) (hξ : ContDiff ℝ ∞ ξ) (hξp : Function.Periodic ξ 1)
    {m M Q : ℝ} (hm : IsLeast (Set.range u) m) (hM : IsGreatest (Set.range u) M)
    (hQ : IsLUB (Set.range fun x => |ξ x|) Q) :
    0 < m ∧ 0 < delta_EX01216 m Q ∧
    (∀ t : ℝ, |t| < delta_EX01216 m Q →
      IsAdmSmooth_EX01236 (ucurve_EX01216 u ξ t) ∧
      (∀ x, m / 2 ≤ vcurve_EX01216 u ξ t x ∧ vcurve_EX01216 u ξ t x ≤ M + Q) ∧
      (m / 2 ≤ normCurve_EX01216 u ξ t ∧ normCurve_EX01216 u ξ t ≤ M + Q) ∧
      (∀ x, m / (2 * (M + Q)) ≤ ucurve_EX01216 u ξ t x ∧
        ucurve_EX01216 u ξ t x ≤ 2 * (M + Q) / m) ∧
      (∀ x, HasDerivAt (fun s => ucurve_EX01216 u ξ s x) (dcurve_EX01216 u ξ t x) t) ∧
      (∀ x, |dcurve_EX01216 u ξ t x| ≤ 2 * Q / m + 8 * (M + Q) ^ 2 * Q / m ^ 3)) ∧
    (∀ x, ucurve_EX01216 u ξ 0 x = u x) ∧
    (∀ x, HasDerivAt (fun s => ucurve_EX01216 u ξ s x) (eta_EX01216 u ξ x) 0) ∧
    (∀ x, deriv (fun s => ucurve_EX01216 u ξ s x) 0 = eta_EX01216 u ξ x) := by
  have hS : Setup_EX01216 u ξ m M Q :=
    { adm := hu
      smooth := hξ
      periodic := hξp
      m_pos := by
        obtain ⟨x, hx⟩ := hm.1
        rw [← hx]; exact hu.pos x
      lower := fun x => hm.2 ⟨x, rfl⟩
      upper := fun x => hM.2 ⟨x, rfl⟩
      bound := fun x => hQ.1 ⟨x, rfl⟩ }
  have hd := delta_pos_EX01216 (Q := Q) hS.m_pos
  have h0 : |(0:ℝ)| < delta_EX01216 m Q := by simpa using hd
  have hder : ∀ x, HasDerivAt (fun s => ucurve_EX01216 u ξ s x) (eta_EX01216 u ξ x) 0 := fun x => by
    have := setup_hasDerivAt_ucurve_EX01216 hS h0 x
    rwa [dcurve_zero_EX01216 hu] at this
  exact ⟨hS.m_pos, hd, fun t ht => ⟨setup_admissible_EX01216 hS ht, setup_v_bounds_EX01216 hS ht,
    setup_N_bounds_EX01216 hS ht, setup_ucurve_bounds_EX01216 hS ht,
    setup_hasDerivAt_ucurve_EX01216 hS ht, setup_dcurve_bound_EX01216 hS ht⟩,
    ucurve_zero_EX01216 hu, hder, fun x => (hder x).deriv⟩

end DGPS.Frontier.EX012
