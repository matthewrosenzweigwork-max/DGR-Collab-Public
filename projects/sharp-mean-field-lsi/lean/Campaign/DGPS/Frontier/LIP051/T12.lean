import Mathlib
import DGPS.Frontier.LIP051.T11

/-!
# LIP051.12: L1 law of large numbers by truncation

Task id: LIP051.12 (node LIP051, joint Gaussian and quadratic fluctuation limit).
Title: L1 law of large numbers by truncation.

Provides:
* `DGPS.Frontier.LIP051.lip051_12_l1_law_large_numbers_truncation`: for a probability measure `μ`,
  a measurable `μ`-integrable real `g`, the following two clauses. (1) For every `M > 0` and `N ≥ 1`,
  under `Q_N = Measure.pi (fun _ : Fin N => μ)`, the expected absolute deviation of the empirical
  average `(1/N) ∑ g(x l)` from `μ(g)` is at most `2 ‖g - g_M‖_{L¹(μ)} + M / √N`, where
  `g_M = max (-M) (min M g)`. (2) That expected absolute deviation tends to `0` as `N → ∞`.
* Helper `DGPS.Frontier.LIP051.truncation_error_le_LIP05112`: the clipping error is dominated by `|g|`.
* Helper `DGPS.Frontier.LIP051.truncation_tendsto_LIP05112`: the L¹ truncation tail
  `∫ |g - g_M| dμ` tends to `0` along `M = n + 1` (dominated convergence).
* Helper `DGPS.Frontier.LIP051.clip_measurable_LIP05112`: the clipped function `g_M` is measurable.
* Helper `DGPS.Frontier.LIP051.clip_bound_LIP05112`: the clipped function satisfies `|g_M| ≤ M`.
* Helper `DGPS.Frontier.LIP051.empirical_integral_LIP05112`: the expected empirical average of `h`
  composed with the coordinates equals `∫ h dμ`, for `N ≥ 1`.
* Helper `DGPS.Frontier.LIP051.deviation_bound_LIP05112`: the quantitative clause (1).

Dependencies: LIP051.11 (`DGPS.Frontier.LIP051.T11`, `lip051_11_bounded_empirical_average_estimate`
and `marginal_integral_LIP05111`, `marginal_integrable_LIP05111`, `integrable_of_bound_LIP05111`).

R5 notes:
* Ambient spaces. As in LIP051.11, `E` is an arbitrary measurable space and `μ` an arbitrary
  probability measure on it; `Torus d` with its Borel structure is one instance. The sample space is
  `Fin N → E` with `Q_N = Measure.pi (fun _ => μ)` and coordinate maps `X_l x = x l`. No object of
  the campaign (`Spec`, `KData`, `Hw`, the Gaussian law, the kernel `K`) is used or identified here.
* "Measurable `g` in L1". Read as `Measurable g` together with `Integrable g μ`.
* The clipping. `g_M x = max (-M) (min M (g x))`, displayed literally in the statement as a function of
  `g x`, with `M : ℝ` and `0 < M`.
* Norms and expectations. `‖g - g_M‖_{L¹(μ)}` is the Bochner integral `∫ x, |g x - g_M x| ∂μ`, and
  "E|…|" is `∫ x, |…| ∂Q_N`. The empirical average is `(1/N) * ∑ l, g (x l)` with the Lean cast
  `N : ℝ`, and `μ(g)` is `∫ y, g y ∂μ`; both are displayed literally.
* Range of N. The quantitative clause is stated for `1 ≤ N`, as in the specification. The clause
  "in particular the left side tends to zero" is `Tendsto` along `Filter.atTop` on `ℕ`, which ignores
  any finite set of values of `N`.
* Conjunction. The specification's two sentences are the two conjuncts of one theorem; neither is
  weakened and no hypothesis is added beyond those of the first sentence.
* Order of choices in the limit. Given `ε`, first `M` (a natural number plus one) with the truncation
  tail below `ε/4`, then `N` large with `M/√N < ε/2`; no fourth moment or boundedness of `g` is used.
* Mode indexing (FD-002). This unit involves no Gaussian object, no Fourier or Hilbert-basis mode,
  no binder `Spec` or `KData`, no mode-zero convention, and no index of positive modes; the
  binder, mode-zero and index conventions of the node are therefore not touched here. The
  positive-mode reading of the node (coordinates `1, …, m`, with mode zero excluded) is neither
  adopted nor contradicted, and the original pointwise diagonal of the kernel plays no role.
* Use of LIP051.11. The bounded estimate is applied to the clipped function `g_M`, which is
  measurable and bounded by `M` pointwise; only its second conjunct chain
  `E|…| ≤ √Var / √N ≤ M / √N` is used, as `E|…| ≤ M / √N`.
-/

namespace DGPS.Frontier.LIP051

open MeasureTheory ProbabilityTheory Filter Topology

/-- The clipping error is dominated by `|g|`, for every clipping level `M ≥ 0`. -/
lemma truncation_error_le_LIP05112 (M : ℝ) (hM : 0 ≤ M) (a : ℝ) :
    |a - max (-M) (min M a)| ≤ |a| := by
  rcases le_total a M with h1 | h1
  · rw [min_eq_right h1]
    rcases le_total (-M) a with h2 | h2
    · rw [max_eq_right h2]; simp
    · rw [max_eq_left h2, abs_le]
      constructor <;> cases abs_cases a <;> linarith
  · rw [min_eq_left h1, max_eq_right (by linarith), abs_le]
    constructor <;> cases abs_cases a <;> linarith

/-- The clipped function is measurable. -/
lemma clip_measurable_LIP05112 {E : Type*} [MeasurableSpace E] {g : E → ℝ} (hg : Measurable g)
    (M : ℝ) : Measurable fun x => max (-M) (min M (g x)) :=
  measurable_const.max (measurable_const.min hg)

/-- The clipped function is bounded by `M`. -/
lemma clip_bound_LIP05112 {M : ℝ} (hM : 0 ≤ M) (a : ℝ) : |max (-M) (min M a)| ≤ M := by
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

/-- The L¹ truncation tail tends to zero along `M = n + 1`, by dominated convergence. -/
lemma truncation_tendsto_LIP05112 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (g : E → ℝ) (hg : Measurable g) (hgi : Integrable g μ) :
    Tendsto (fun n : ℕ => ∫ x, |g x - max (-((n : ℝ) + 1)) (min ((n : ℝ) + 1) (g x))| ∂μ)
      atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun (n : ℕ) x => |g x - max (-((n : ℝ) + 1)) (min ((n : ℝ) + 1) (g x))|)
    (f := fun _ => (0 : ℝ)) (fun x => |g x|)
    (fun n => (hg.sub (clip_measurable_LIP05112 hg _)).abs.aestronglyMeasurable)
    hgi.abs
    (fun n => ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_abs]
      exact truncation_error_le_LIP05112 _ (by positivity) _)
    (ae_of_all _ fun x => by
      refine tendsto_const_nhds.congr' ?_
      obtain ⟨n₀, hn₀⟩ := exists_nat_ge |g x|
      filter_upwards [eventually_ge_atTop n₀] with n hn
      have hn' : |g x| ≤ (n : ℝ) + 1 := by
        have : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      obtain ⟨h1, h2⟩ := abs_le.1 hn'
      rw [min_eq_right h2, max_eq_right h1]
      simp)
  simpa using h

/-- The expected empirical average of `h` equals `∫ h dμ`, for `N ≥ 1`. -/
lemma empirical_integral_LIP05112 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {h : E → ℝ} (hm : Measurable h) (hi : Integrable h μ)
    (N : ℕ) (hN : 1 ≤ N) :
    ∫ x, (1 / (N : ℝ)) * (∑ l : Fin N, h (x l)) ∂(Measure.pi fun _ : Fin N => μ)
      = ∫ y, h y ∂μ := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  rw [integral_const_mul, integral_finsetSum _ (fun l _ => marginal_integrable_LIP05111 μ l hi)]
  rw [Finset.sum_congr rfl (fun l _ => marginal_integral_LIP05111 μ l hm)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The quantitative clause: for every `M > 0` and `N ≥ 1`, the expected deviation is at most
`2 ‖g - g_M‖₁ + M / √N`. -/
lemma deviation_bound_LIP05112 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] (g : E → ℝ) (hg : Measurable g) (hgi : Integrable g μ)
    (M : ℝ) (hM : 0 < M) (N : ℕ) (hN : 1 ≤ N) :
    ∫ x, |(1 / (N : ℝ)) * (∑ l : Fin N, g (x l)) - ∫ y, g y ∂μ|
        ∂(Measure.pi fun _ : Fin N => μ)
      ≤ 2 * ∫ x, |g x - max (-M) (min M (g x))| ∂μ + M / Real.sqrt (N : ℝ) := by
  set Q : Measure (Fin N → E) := Measure.pi fun _ : Fin N => μ with hQ
  set b : E → ℝ := fun x => max (-M) (min M (g x)) with hb
  have hbm : Measurable b := clip_measurable_LIP05112 hg M
  have hbbd : ∀ x, |b x| ≤ M := fun x => clip_bound_LIP05112 hM.le _
  have hbi : Integrable b μ := integrable_of_bound_LIP05111 hbm hbbd
  have hhm : Measurable fun x => |g x - b x| := (hg.sub hbm).abs
  have hhi : Integrable (fun x => |g x - b x|) μ := (hgi.sub hbi).abs
  set c : ℝ := ∫ x, |g x - b x| ∂μ with hc
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hT11 := lip051_11_bounded_empirical_average_estimate μ b M hM.le hbm hbbd N hN
  have hT := hT11.1.trans hT11.2
  -- pointwise decomposition
  have hpt : ∀ x : Fin N → E,
      |(1 / (N : ℝ)) * (∑ l : Fin N, g (x l)) - ∫ y, g y ∂μ|
        ≤ |(1 / (N : ℝ)) * (∑ l : Fin N, b (x l)) - ∫ y, b y ∂μ|
          + (1 / (N : ℝ)) * (∑ l : Fin N, |g (x l) - b (x l)|) + c := by
    intro x
    have hsplit : (1 / (N : ℝ)) * (∑ l : Fin N, g (x l)) - ∫ y, g y ∂μ
        = ((1 / (N : ℝ)) * (∑ l : Fin N, b (x l)) - ∫ y, b y ∂μ)
          + ((1 / (N : ℝ)) * (∑ l : Fin N, (g (x l) - b (x l))) - ∫ y, (g y - b y) ∂μ) := by
      rw [integral_sub hgi hbi, Finset.sum_sub_distrib]
      ring
    have h1 : |(1 / (N : ℝ)) * (∑ l : Fin N, (g (x l) - b (x l)))|
        ≤ (1 / (N : ℝ)) * (∑ l : Fin N, |g (x l) - b (x l)|) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    have h2 : |∫ y, (g y - b y) ∂μ| ≤ c := by
      have := abs_integral_le_integral_abs (μ := μ) (f := fun y => g y - b y)
      exact this
    rw [hsplit]
    calc _ ≤ |(1 / (N : ℝ)) * (∑ l : Fin N, b (x l)) - ∫ y, b y ∂μ|
          + |(1 / (N : ℝ)) * (∑ l : Fin N, (g (x l) - b (x l))) - ∫ y, (g y - b y) ∂μ| :=
          abs_add_le _ _
      _ ≤ _ := by
          have := abs_sub (((1 / (N : ℝ)) * (∑ l : Fin N, (g (x l) - b (x l)))))
            (∫ y, (g y - b y) ∂μ)
          linarith
  -- integrability of the three right-hand terms
  have hmeasb : ∀ l : Fin N, Measurable fun x : Fin N → E => b (x l) :=
    fun l => hbm.comp (measurable_pi_apply l)
  have hI1 : Integrable (fun x : Fin N → E =>
      |(1 / (N : ℝ)) * (∑ l : Fin N, b (x l)) - ∫ y, b y ∂μ|) Q := by
    refine integrable_of_bound_LIP05111 (C := M + M) ?_ fun x => ?_
    · exact (measurable_const.mul (Finset.measurable_sum _ fun l _ => hmeasb l)).sub
        measurable_const |>.abs
    · rw [abs_abs]
      have hs : |∑ l : Fin N, b (x l)| ≤ (N : ℝ) * M := by
        calc |∑ l : Fin N, b (x l)| ≤ ∑ l : Fin N, |b (x l)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _l : Fin N, M := Finset.sum_le_sum fun l _ => hbbd _
          _ = (N : ℝ) * M := by simp
      have hint : |∫ y, b y ∂μ| ≤ M := by
        have h := norm_integral_le_of_norm_le_const (μ := μ) (f := b) (C := M)
          (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hbbd x)
        simpa [Real.norm_eq_abs] using h
      have havg : |(1 / (N : ℝ)) * ∑ l : Fin N, b (x l)| ≤ M := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
        calc 1 / (N : ℝ) * |∑ l : Fin N, b (x l)| ≤ 1 / (N : ℝ) * ((N : ℝ) * M) := by
              gcongr
          _ = M := by field_simp
      calc _ ≤ |(1 / (N : ℝ)) * ∑ l : Fin N, b (x l)| + |∫ y, b y ∂μ| := abs_sub _ _
        _ ≤ M + M := add_le_add havg hint
  have hI2 : Integrable (fun x : Fin N → E =>
      (1 / (N : ℝ)) * (∑ l : Fin N, |g (x l) - b (x l)|)) Q :=
    (integrable_finsetSum _ fun l _ => marginal_integrable_LIP05111 μ l hhi).const_mul _
  have hI12 : Integrable (fun x : Fin N → E =>
      |(1 / (N : ℝ)) * (∑ l : Fin N, b (x l)) - ∫ y, b y ∂μ|
        + (1 / (N : ℝ)) * (∑ l : Fin N, |g (x l) - b (x l)|)) Q := hI1.add hI2
  have hRHS : Integrable (fun x : Fin N → E =>
      |(1 / (N : ℝ)) * (∑ l : Fin N, b (x l)) - ∫ y, b y ∂μ|
        + (1 / (N : ℝ)) * (∑ l : Fin N, |g (x l) - b (x l)|) + c) Q :=
    hI12.add (integrable_const (μ := Q) c)
  have hE2 : ∫ x, (1 / (N : ℝ)) * (∑ l : Fin N, |g (x l) - b (x l)|) ∂Q = c :=
    empirical_integral_LIP05112 μ hhm hhi N hN
  calc ∫ x, |(1 / (N : ℝ)) * (∑ l : Fin N, g (x l)) - ∫ y, g y ∂μ| ∂Q
      ≤ ∫ x, (|(1 / (N : ℝ)) * (∑ l : Fin N, b (x l)) - ∫ y, b y ∂μ|
          + (1 / (N : ℝ)) * (∑ l : Fin N, |g (x l) - b (x l)|) + c) ∂Q :=
        integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _) hRHS (ae_of_all _ hpt)
    _ = ∫ x, |(1 / (N : ℝ)) * (∑ l : Fin N, b (x l)) - ∫ y, b y ∂μ| ∂Q + c + c := by
        rw [integral_add hI12 (integrable_const c), integral_add hI1 hI2, hE2]
        simp
    _ ≤ M / Real.sqrt (N : ℝ) + c + c := by gcongr
    _ = 2 * c + M / Real.sqrt (N : ℝ) := by ring

/-- **LIP051.12.** L¹ law of large numbers by truncation. For a probability measure `μ` and a
measurable `μ`-integrable real `g`: (1) for every `M > 0` and `N ≥ 1`, under `Q_N = μ^N`,
`E |(1/N) ∑ g(X_l) - μ(g)| ≤ 2 ‖g - g_M‖_{L¹(μ)} + M / √N` with `g_M = max (-M) (min M g)`;
(2) the left side tends to zero as `N → ∞`. -/
theorem lip051_12_l1_law_large_numbers_truncation
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (g : E → ℝ) (hg : Measurable g) (hgi : Integrable g μ) :
    (∀ M : ℝ, 0 < M → ∀ N : ℕ, 1 ≤ N →
      ∫ x, |(1 / (N : ℝ)) * (∑ l : Fin N, g (x l)) - ∫ y, g y ∂μ|
          ∂(Measure.pi fun _ : Fin N => μ)
        ≤ 2 * ∫ x, |g x - max (-M) (min M (g x))| ∂μ + M / Real.sqrt (N : ℝ)) ∧
    Tendsto (fun N : ℕ => ∫ x, |(1 / (N : ℝ)) * (∑ l : Fin N, g (x l)) - ∫ y, g y ∂μ|
        ∂(Measure.pi fun _ : Fin N => μ)) atTop (𝓝 0) := by
  refine ⟨fun M hM N hN => deviation_bound_LIP05112 μ g hg hgi M hM N hN, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have htail := truncation_tendsto_LIP05112 μ g hg hgi
  rw [Metric.tendsto_atTop] at htail
  obtain ⟨n, hn⟩ := htail (ε / 4) (by positivity)
  set M : ℝ := (n : ℝ) + 1 with hMdef
  have hM : 0 < M := by positivity
  have htailM := hn n le_rfl
  rw [Real.dist_eq, sub_zero] at htailM
  have hc4 : ∫ x, |g x - max (-M) (min M (g x))| ∂μ < ε / 4 := by
    have h := lt_of_le_of_lt (le_abs_self _) htailM
    exact h
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((2 * M / ε) ^ 2)
  refine ⟨N₀ + 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hbound := deviation_bound_LIP05112 μ g hg hgi M hM N hN1
  have hNgt : (2 * M / ε) ^ 2 < (N : ℝ) := by
    have : (N₀ : ℝ) ≤ N := by exact_mod_cast (by omega : N₀ ≤ N)
    linarith
  have hsq : 2 * M / ε < Real.sqrt (N : ℝ) :=
    Real.lt_sqrt (by positivity) |>.2 hNgt
  have hsqpos : 0 < Real.sqrt (N : ℝ) := lt_of_le_of_lt (by positivity) hsq
  have hMN : M / Real.sqrt (N : ℝ) < ε / 2 := by
    rw [div_lt_iff₀ hsqpos]
    rw [div_lt_iff₀ hε] at hsq
    linarith
  have hnn : 0 ≤ ∫ x, |(1 / (N : ℝ)) * (∑ l : Fin N, g (x l)) - ∫ y, g y ∂μ|
      ∂(Measure.pi fun _ : Fin N => μ) := integral_nonneg fun x => abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith

end DGPS.Frontier.LIP051
