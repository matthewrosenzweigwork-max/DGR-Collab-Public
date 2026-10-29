import DGPS.Frontier.EX012.T16

/-!
# EX012.18: Entropic first variation

Task id: EX012.18 (node EX012, leaf formalization).
Title: Entropic first variation.

For the curve `u_t` of EX012.16 (`u_t = (u + tξ) / ‖u + tξ‖₂`, admissible for `|t| < δ`), prove
`(d/dt) ∫₀¹ u_t² log u_t |₀ = ∫₀¹ (2 u log u + u) η`, with `η = ξ - u ∫ uξ`. The scalar derivative
is `(2 z log z + z) z'`; the parameter-integral derivative theorem is applied on `|t| < δ` with the
constant dominator `U (2H + 1) T`, `ℓ = m/(2B)`, `U = 2B/m`, `T = 2Q/m + 8B²Q/m³`,
`H = max |log ℓ| |log U|`, `B = M + Q`.

## Provides

* `DGPS.Frontier.EX012.ex012_18_entropic_first_variation`: under the hypotheses of
  `ex012_16_admissible_normalized_variation`, with `m = min u`, `M = max u`, `Q = ‖ξ‖∞`, the function
  `t ↦ ∫ x in 0..1, u_t x ^ 2 * log (u_t x)` has derivative
  `∫ x in 0..1, (2 * u x * log (u x) + u x) * η x` at `0`.
* `DGPS.Frontier.EX012.ex012_18_entropic_first_variation_deriv`: the same statement as an
  equation `deriv (fun t => ∫ x in 0..1, u_t x ^ 2 * log (u_t x)) 0 = ∫ x in 0..1, (2 * u x * log (u x) + u x) * η x`.
* `DGPS.Frontier.EX012.entropy_EX01218`, `entropyDeriv_EX01218`, `dominator_EX01218`: the entropy
  `t ↦ ∫ u_t² log u_t`, the pointwise derivative integrand `(2 u_t log u_t + u_t) ∂_t u_t`,
  and the constant dominator `U (2H + 1) T`.
* Helper lemmas, all with the suffix `_EX01218`.

## R5 notes

* The hypotheses and the objects `u_t` (`ucurve_EX01216`), `η` (`eta_EX01216`), `m`, `M`, `Q` are
  exactly those of EX012.16 (`IsLeast`, `IsGreatest`, `IsLUB` for `m`, `M`, `Q`); no further
  hypothesis is added. The derivative is the ordinary real derivative in `t` of a real-valued
  function, stated as `HasDerivAt` at `0` (and as `deriv` in the second declaration).
* `log` is `Real.log`; it is only evaluated on positive values (`u_t > 0`), where it is the true
  logarithm.
* The Haar-probability integral is read as `∫ x in (0:ℝ)..1`, the form used by EX012.16 and
  EX012.36. Internally the integral is converted to the Bochner integral over the finite measure
  `volume.restrict (Set.Ioc 0 1)`.
* The dominator `U (2H + 1) T` is a constant, hence integrable on the finite measure. It is
  applied on the ball `|t| < δ` of EX012.16.
-/

open MeasureTheory Metric
open scoped ContDiff

namespace DGPS.Frontier.EX012

/-- The entropy `t ↦ ∫ u_t² log u_t`. -/
noncomputable def entropy_EX01218 (u ξ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..1, ucurve_EX01216 u ξ t x ^ 2 * Real.log (ucurve_EX01216 u ξ t x)

/-- The pointwise derivative `(2 u_t log u_t + u_t) ∂_t u_t`. -/
noncomputable def entropyDeriv_EX01218 (u ξ : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (2 * ucurve_EX01216 u ξ t x * Real.log (ucurve_EX01216 u ξ t x) + ucurve_EX01216 u ξ t x)
    * dcurve_EX01216 u ξ t x

/-- The constant dominator `U (2H + 1) T`. -/
noncomputable def dominator_EX01218 (m M Q : ℝ) : ℝ :=
  (2 * (M + Q) / m) *
    (2 * max |Real.log (m / (2 * (M + Q)))| |Real.log (2 * (M + Q) / m)| + 1) *
    (2 * Q / m + 8 * (M + Q) ^ 2 * Q / m ^ 3)

theorem ucurve_pos_EX01218 {u ξ : ℝ → ℝ} {m M Q t : ℝ} (h : Setup_EX01216 u ξ m M Q)
    (ht : |t| < delta_EX01216 m Q) (x : ℝ) : 0 < ucurve_EX01216 u ξ t x :=
  (setup_admissible_EX01216 h ht).pos x

theorem continuous_ucurve_EX01218 {u ξ : ℝ → ℝ} {m M Q t : ℝ} (h : Setup_EX01216 u ξ m M Q)
    (ht : |t| < delta_EX01216 m Q) : Continuous (ucurve_EX01216 u ξ t) :=
  (setup_admissible_EX01216 h ht).smooth.continuous

theorem continuous_dcurve_EX01218 {u ξ : ℝ → ℝ} {m M Q : ℝ} (h : Setup_EX01216 u ξ m M Q) (t : ℝ) :
    Continuous (dcurve_EX01216 u ξ t) := by
  have hu := h.adm.smooth.continuous
  have hξ := h.smooth.continuous
  have hv : Continuous (vcurve_EX01216 u ξ t) :=
    hu.add (continuous_const.mul hξ)
  unfold dcurve_EX01216
  exact (hξ.div_const _).sub ((hv.mul continuous_const).div_const _)

theorem continuous_entropy_integrand_EX01218 {u ξ : ℝ → ℝ} {m M Q t : ℝ}
    (h : Setup_EX01216 u ξ m M Q) (ht : |t| < delta_EX01216 m Q) :
    Continuous fun x => ucurve_EX01216 u ξ t x ^ 2 * Real.log (ucurve_EX01216 u ξ t x) :=
  ((continuous_ucurve_EX01218 h ht).pow 2).mul
    ((continuous_ucurve_EX01218 h ht).log fun x => (ucurve_pos_EX01218 h ht x).ne')

theorem continuous_entropyDeriv_EX01218 {u ξ : ℝ → ℝ} {m M Q t : ℝ}
    (h : Setup_EX01216 u ξ m M Q) (ht : |t| < delta_EX01216 m Q) :
    Continuous (entropyDeriv_EX01218 u ξ t) := by
  have hc := continuous_ucurve_EX01218 h ht
  unfold entropyDeriv_EX01218
  exact (((continuous_const.mul hc).mul
    (hc.log fun x => (ucurve_pos_EX01218 h ht x).ne')).add hc).mul (continuous_dcurve_EX01218 h t)

theorem hasDerivAt_entropy_integrand_EX01218 {u ξ : ℝ → ℝ} {m M Q t : ℝ}
    (h : Setup_EX01216 u ξ m M Q) (ht : |t| < delta_EX01216 m Q) (x : ℝ) :
    HasDerivAt (fun s => ucurve_EX01216 u ξ s x ^ 2 * Real.log (ucurve_EX01216 u ξ s x))
      (entropyDeriv_EX01218 u ξ t x) t := by
  have hz := setup_hasDerivAt_ucurve_EX01216 h ht x
  have hpos := (ucurve_pos_EX01218 h ht x).ne'
  have := (hz.pow 2).mul (hz.log hpos)
  refine HasDerivAt.congr_deriv this ?_
  unfold entropyDeriv_EX01218
  simp only [Pi.pow_apply]
  field_simp
  ring

theorem entropyDeriv_bound_EX01218 {u ξ : ℝ → ℝ} {m M Q t : ℝ}
    (h : Setup_EX01216 u ξ m M Q) (ht : |t| < delta_EX01216 m Q) (x : ℝ) :
    ‖entropyDeriv_EX01218 u ξ t x‖ ≤ dominator_EX01218 m M Q := by
  have hm := h.m_pos
  have hB : 0 < M + Q := by linarith [setup_m_le_M_EX01216 h, setup_Q_nonneg_EX01216 h]
  have hz := ucurve_pos_EX01218 h ht x
  obtain ⟨hlo, hhi⟩ := setup_ucurve_bounds_EX01216 h ht x
  have hl : 0 < m / (2 * (M + Q)) := by positivity
  set z := ucurve_EX01216 u ξ t x with hzdef
  set H := max |Real.log (m / (2 * (M + Q)))| |Real.log (2 * (M + Q) / m)| with hH
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (le_max_left _ _)
  have hlog : |Real.log z| ≤ H := by
    have h1 : Real.log (m / (2 * (M + Q))) ≤ Real.log z := Real.log_le_log hl hlo
    have h2 : Real.log z ≤ Real.log (2 * (M + Q) / m) := Real.log_le_log hz hhi
    have h3 := le_max_left |Real.log (m / (2 * (M + Q)))| |Real.log (2 * (M + Q) / m)|
    have h4 := le_max_right |Real.log (m / (2 * (M + Q)))| |Real.log (2 * (M + Q) / m)|
    rw [← hH] at h3 h4
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log (m / (2 * (M + Q))))]
    · linarith [le_abs_self (Real.log (2 * (M + Q) / m))]
  have hd := setup_dcurve_bound_EX01216 h ht x
  have hUpos : 0 < 2 * (M + Q) / m := by positivity
  have hfac : |2 * z * Real.log z + z| ≤ (2 * (M + Q) / m) * (2 * H + 1) := by
    calc |2 * z * Real.log z + z| ≤ |2 * z * Real.log z| + |z| := abs_add_le _ _
      _ = 2 * z * |Real.log z| + z := by
          rw [abs_mul, abs_mul, abs_of_pos hz, abs_two]
      _ ≤ 2 * (2 * (M + Q) / m) * H + 2 * (M + Q) / m := by
          have : z * |Real.log z| ≤ (2 * (M + Q) / m) * H :=
            mul_le_mul hhi hlog (abs_nonneg _) hUpos.le
          nlinarith
      _ = _ := by ring
  unfold entropyDeriv_EX01218 dominator_EX01218
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul hfac hd (abs_nonneg _) (by positivity)

theorem setup_entropy_hasDerivAt_EX01218 {u ξ : ℝ → ℝ} {m M Q : ℝ} (h : Setup_EX01216 u ξ m M Q) :
    HasDerivAt (entropy_EX01218 u ξ)
      (∫ x in (0:ℝ)..1, entropyDeriv_EX01218 u ξ 0 x) 0 := by
  have hd := delta_pos_EX01216 (Q := Q) h.m_pos
  have h0 : |(0:ℝ)| < delta_EX01216 m Q := by simpa using hd
  have hball : ∀ s ∈ ball (0:ℝ) (delta_EX01216 m Q), |s| < delta_EX01216 m Q := fun s hs => by
    simpa [Real.dist_eq] using hs
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioc (0:ℝ) 1))
    (F := fun s x => ucurve_EX01216 u ξ s x ^ 2 * Real.log (ucurve_EX01216 u ξ s x))
    (F' := entropyDeriv_EX01218 u ξ) (x₀ := 0) (bound := fun _ => dominator_EX01218 m M Q)
    (ball_mem_nhds _ hd)
    (Filter.eventually_of_mem (ball_mem_nhds _ hd) fun s hs =>
      (continuous_entropy_integrand_EX01218 h (hball s hs)).aestronglyMeasurable)
    ((continuous_entropy_integrand_EX01218 h h0).integrableOn_Ioc)
    (continuous_entropyDeriv_EX01218 h h0).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x s hs => entropyDeriv_bound_EX01218 h (hball s hs) x)
    (integrable_const _)
    (Filter.Eventually.of_forall fun x s hs =>
      hasDerivAt_entropy_integrand_EX01218 h (hball s hs) x)
  have := key.2
  have e : entropy_EX01218 u ξ = fun n => ∫ a in Set.Ioc (0:ℝ) 1,
      ucurve_EX01216 u ξ n a ^ 2 * Real.log (ucurve_EX01216 u ξ n a) := funext fun n => by
    unfold entropy_EX01218
    exact intervalIntegral.integral_of_le (zero_le_one' ℝ)
  rw [e, intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  exact this

theorem ex012_18_entropic_first_variation {u ξ : ℝ → ℝ}
    (hu : IsAdmSmooth_EX01236 u) (hξ : ContDiff ℝ ∞ ξ) (hξp : Function.Periodic ξ 1)
    {m M Q : ℝ} (hm : IsLeast (Set.range u) m) (hM : IsGreatest (Set.range u) M)
    (hQ : IsLUB (Set.range fun x => |ξ x|) Q) :
    HasDerivAt (fun t => ∫ x in (0:ℝ)..1,
        ucurve_EX01216 u ξ t x ^ 2 * Real.log (ucurve_EX01216 u ξ t x))
      (∫ x in (0:ℝ)..1, (2 * u x * Real.log (u x) + u x) * eta_EX01216 u ξ x) 0 := by
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
  have := setup_entropy_hasDerivAt_EX01218 hS
  have e : ∀ x, entropyDeriv_EX01218 u ξ 0 x
      = (2 * u x * Real.log (u x) + u x) * eta_EX01216 u ξ x := fun x => by
    unfold entropyDeriv_EX01218
    rw [ucurve_zero_EX01216 hu, dcurve_zero_EX01216 hu]
  simp_rw [e] at this
  exact this

theorem ex012_18_entropic_first_variation_deriv {u ξ : ℝ → ℝ}
    (hu : IsAdmSmooth_EX01236 u) (hξ : ContDiff ℝ ∞ ξ) (hξp : Function.Periodic ξ 1)
    {m M Q : ℝ} (hm : IsLeast (Set.range u) m) (hM : IsGreatest (Set.range u) M)
    (hQ : IsLUB (Set.range fun x => |ξ x|) Q) :
    deriv (fun t => ∫ x in (0:ℝ)..1,
        ucurve_EX01216 u ξ t x ^ 2 * Real.log (ucurve_EX01216 u ξ t x)) 0
      = ∫ x in (0:ℝ)..1, (2 * u x * Real.log (u x) + u x) * eta_EX01216 u ξ x :=
  (ex012_18_entropic_first_variation hu hξ hξp hm hM hQ).deriv

end DGPS.Frontier.EX012
