import DGPS.Frontier.STR029.T05
import DGPS.Frontier.STR029.T43

/-!
# STR029.08: Vanishing-entropy endpoint

Task id: STR029.08. Title: Vanishing-entropy endpoint (node STR029, size S).

Provides:
* `DGPS.Frontier.STR029.str029_08_vanishing_entropy_endpoint`: for `|h| ≤ 1/1000` and periodic `H¹` functions
  `g n` with weak derivatives `dg n`, normalized by `∫ (g n)² q_h dm = 1`, converging uniformly to `1`, and with
  `H(g n) > 0`, the `EReal` liminf of `4 ∫ (dg n)² q_h dm / (2 H(g n))` is at least `1 - h²`.
* `DGPS.Frontier.STR029.wmeas_STR02908`: the probability measure `q_h m` on `(0, 2π]`, with density `(2π)⁻¹ q_h`.
* `DGPS.Frontier.STR029.Hent_STR02908`: the angular entropy `H(g) = ∫ g² log(g²) q_h dm`.
* `DGPS.Frontier.STR029.sq_range_STR02908`: `9/16 ≤ y² ≤ 25/16` when `|y - 1| ≤ 1/4`.
* `DGPS.Frontier.STR029.abs_sq_log_STR02908`: `|y² log y²| ≤ 2` when `|y - 1| ≤ 1/4`.
* `DGPS.Frontier.STR029.measurable_dens_STR02908`: the density of `q_h m` is measurable.
* `DGPS.Frontier.STR029.integral_wmeas_STR02908`: `∫ F d(q_h m) = ∫ F q_h dm`.
* `DGPS.Frontier.STR029.isProbabilityMeasure_wmeas_STR02908`: `q_h m` is a probability measure.
* `DGPS.Frontier.STR029.ae_wmeas_STR02908`: almost-everywhere statements transfer from `dm` to `q_h m`.
* `DGPS.Frontier.STR029.normInt_congr_STR02908`, `DGPS.Frontier.STR029.varQ_congr_STR02908`: congruence of
  `normInt` and `varQ` under almost-everywhere equality.
* `DGPS.Frontier.STR029.varQ_eq_variance_STR02908`: `varQ_h F = Var_{q_h m}(F)` for `F ∈ L²(q_h m)`.
* `DGPS.Frontier.STR029.quot_bound_STR02908`: the per-index bound
  `(1 - h²)/(1 + 2δ) ≤ 4 ∫ (dg)² q_h dm / (2 H(g))` when `|g - 1| ≤ δ` almost everywhere.

R5 notes:
* Hypotheses. The hypotheses are those of the specification: `|h| ≤ 1/1000`, the periodic `H¹` predicate
  `IsPeriodicWeakDerivative_STR02933 (g n) (dg n)` (so `dg n` is the weak derivative of `g n`, and the statement
  holds for every such weak derivative), the normalization `∫ (g n)² q_h dm = 1`, the positivity `0 < H(g n)`, and
  the uniform convergence `g n → 1`. No hypothesis is added.
* Nonnegativity. The hypothesis `0 ≤ g n` is stated almost everywhere on `(0, 2π]`. It is passed to STR029.43 and
  is otherwise not needed, because `H` and the normalization involve only `g²`.
* Uniform convergence. It is read as an essential supremum on `(0, 2π]` with respect to `dt`: for every `δ > 0`,
  eventually `|g n t - 1| ≤ δ` for almost every `t`. A pointwise sup-norm hypothesis would imply this, so the
  formal hypothesis is weaker and the theorem is at least as strong as the specification.
* Liminf in `EReal`. The conclusion is `((1 - h²) : EReal) ≤ Filter.liminf (...) atTop` with values in `EReal`.
  The real-valued `Filter.liminf` returns the junk value `0` for a sequence tending to `+∞`, so the literal real
  reading is not the mathematical content when the quotients are unbounded above. The `EReal` reading is the
  faithful one and is the only change of carrier in the statement. The quotient is well defined since `H(g n) > 0`.
* Measure and domain. Integrals are normalized over the period `(0, 2π]` (`normInt_STR02933`, factor `(2π)⁻¹`).
  The specification writes `[0, 2π)`; the endpoint is a null set. The angular variable is `t = 2πx`, as in
  STR029.05 and STR029.43.
* Entropy. `H(g) = ∫ g² log(g²) q_h dm` is defined directly as a normalized integral (`Hent_STR02908`). It is
  identified with `DGPS.homogeneousEntropy` on the probability space `(q_h m)` inside the proof, via
  `homogeneousEntropy_eq_formula`. The Fisher-type term is `∫ (dg)² q_h dm`, with no further normalization.
* Weight. The weight is `q_h = qT_STR02904 h`, the reference density of STR029.04, normalized by
  `normInt_qT_STR02935`. The bridge measure `q_h m` is the `withDensity` of `(2π)⁻¹ q_h` on `(0, 2π]`.
* Measurable representatives. STR029.43 needs measurable functions on a probability space. Each `g n` is only
  `L²` on the period, so the proof replaces it by a measurable representative `G` that agrees with `g n` almost
  everywhere. This changes no integral, since all integrals are almost-everywhere invariant.
* Variance. `varQ_STR02935 h (g - ∫ g dm)` in STR029.05 equals the variance of `G` under `q_h m`, by the bridge lemma
  and shift invariance of the variance. The proof uses no further variance convention.
* Proof route. The entropy expansion is STR029.43 (`str029_43_entropy_expansion_relative_variance`), applied with
  `ε = δ ≤ 1/4`. The Poincaré bound is STR029.05 (`str029_05_poincare_bound_sufficient_attainment`). The liminf is
  taken by the sequence of per-index bounds: for each `δ ∈ (0, 1/4)`, eventually the quotient is at least
  `(1 - h²)/(1 + 2δ)`, and the limit `δ → 0+` gives the claim.
* Not used by this unit. The optimizer-chart predicate, the `AbsoluteDensity` domain, the Euler range map and the
  rate normalization are not used. The sufficient-attainment bound and the entropy expansion carry the proof.
-/

open MeasureTheory Set Real Filter ProbabilityTheory Topology

namespace DGPS.Frontier.STR029

/-- The probability measure `q_h m` on the period `(0, 2π]`: the measure with density `(2π)⁻¹ q_h` against
Lebesgue measure restricted to `(0, 2π]`. -/
noncomputable def wmeas_STR02908 (h : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc 0 (2 * π))).withDensity
    (fun t => ENNReal.ofReal ((2 * π)⁻¹ * qT_STR02904 h t))

/-- The angular entropy `H(g) = ∫ g² log(g²) q_h dm` of a periodic function `g`. -/
noncomputable def Hent_STR02908 (h : ℝ) (g : ℝ → ℝ) : ℝ :=
  normInt_STR02933 (fun t => g t ^ 2 * Real.log (g t ^ 2) * qT_STR02904 h t)

/-- For `|y - 1| ≤ 1/4`, the square satisfies `9/16 ≤ y² ≤ 25/16`. -/
theorem sq_range_STR02908 {y : ℝ} (hy : |y - 1| ≤ 1 / 4) : 9 / 16 ≤ y ^ 2 ∧ y ^ 2 ≤ 25 / 16 := by
  obtain ⟨h1, h2⟩ := abs_le.mp hy
  have hy3 : 3 / 4 ≤ y := by linarith
  have hy5 : y ≤ 5 / 4 := by linarith
  constructor
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y - 3 / 4) (by linarith : (0 : ℝ) ≤ y + 3 / 4)]
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 5 / 4 - y) (by linarith : (0 : ℝ) ≤ 5 / 4 + y)]

/-- For `|y - 1| ≤ 1/4`, `|y² log y²| ≤ 2`. -/
theorem abs_sq_log_STR02908 {y : ℝ} (hy : |y - 1| ≤ 1 / 4) :
    |y ^ 2 * Real.log (y ^ 2)| ≤ 2 := by
  obtain ⟨hs2, hs1⟩ := sq_range_STR02908 hy
  have hs0 : 0 < y ^ 2 := by linarith
  have hl1 : Real.log (y ^ 2) ≤ y ^ 2 - 1 := Real.log_le_sub_one_of_pos hs0
  have hl2 : 1 - (y ^ 2)⁻¹ ≤ Real.log (y ^ 2) := Real.one_sub_inv_le_log_of_pos hs0
  have hinv : (y ^ 2)⁻¹ ≤ 16 / 9 := by
    rw [inv_eq_one_div, div_le_iff₀ hs0]
    linarith
  have hL : |Real.log (y ^ 2)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [abs_mul, abs_of_pos hs0]
  nlinarith [mul_le_mul_of_nonneg_left hL hs0.le]

/-- The density `ofReal((2π)⁻¹ q_h)` is measurable. -/
theorem measurable_dens_STR02908 (h : ℝ) :
    Measurable (fun t => ENNReal.ofReal ((2 * π)⁻¹ * qT_STR02904 h t)) :=
  (measurable_const.mul (continuous_qT_STR02904 h).measurable).ennreal_ofReal

/-- Integrals against `q_h m` are normalized integrals against `q_h`: `∫ F d(q_h m) = ∫ F q_h dm`. -/
theorem integral_wmeas_STR02908 (h : ℝ) (F : ℝ → ℝ) :
    ∫ x, F x ∂(wmeas_STR02908 h) = normInt_STR02933 (fun t => F t * qT_STR02904 h t) := by
  have hdens : ∀ x, 0 ≤ (2 * π)⁻¹ * qT_STR02904 h x :=
    fun x => (mul_pos (by positivity) (qT_pos_STR02904 h x)).le
  unfold wmeas_STR02908 normInt_STR02933
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_dens_STR02908 h)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (hdens x)]
  ring

/-- `q_h m` is a probability measure, since `∫ q_h dm = 1` (`normInt_qT_STR02935`). -/
theorem isProbabilityMeasure_wmeas_STR02908 (h : ℝ) : IsProbabilityMeasure (wmeas_STR02908 h) := by
  have e : ∫ _x, (1 : ℝ) ∂(wmeas_STR02908 h) = normInt_STR02933 (fun t => 1 * qT_STR02904 h t) :=
    integral_wmeas_STR02908 h (fun _ => 1)
  simp only [one_mul] at e
  rw [normInt_qT_STR02935 h, integral_const, smul_eq_mul, mul_one] at e
  exact ⟨(ENNReal.toReal_eq_one_iff _).mp e⟩

/-- Almost-everywhere statements for `dm` transfer to `q_h m`, which is absolutely continuous with respect to `dm`. -/
theorem ae_wmeas_STR02908 {h : ℝ} {P : ℝ → Prop}
    (hP : ∀ᵐ t ∂(volume.restrict (Ioc 0 (2 * π))), P t) : ∀ᵐ t ∂(wmeas_STR02908 h), P t :=
  (withDensity_absolutelyContinuous _ _).ae_le hP

/-- `normInt` respects almost-everywhere equality. -/
theorem normInt_congr_STR02908 {f f' : ℝ → ℝ}
    (hf : f =ᵐ[volume.restrict (Ioc 0 (2 * π))] f') :
    normInt_STR02933 f = normInt_STR02933 f' := by
  unfold normInt_STR02933
  rw [integral_congr_ae hf]

/-- `varQ_STR02935 h` respects almost-everywhere equality. -/
theorem varQ_congr_STR02908 (h : ℝ) {F F' : ℝ → ℝ}
    (hF : F =ᵐ[volume.restrict (Ioc 0 (2 * π))] F') :
    varQ_STR02935 h F = varQ_STR02935 h F' := by
  have h1 : (fun t => F t ^ 2 * qT_STR02904 h t) =ᵐ[volume.restrict (Ioc 0 (2 * π))]
      (fun t => F' t ^ 2 * qT_STR02904 h t) := by
    filter_upwards [hF] with t ht
    simp only [ht]
  have h2 : (fun t => F t * qT_STR02904 h t) =ᵐ[volume.restrict (Ioc 0 (2 * π))]
      (fun t => F' t * qT_STR02904 h t) := by
    filter_upwards [hF] with t ht
    simp only [ht]
  unfold varQ_STR02935
  rw [normInt_congr_STR02908 h1, normInt_congr_STR02908 h2]

/-- For `F ∈ L²(q_h m)`, the weighted variance `varQ_STR02935 h F` is the variance of `F` under `q_h m`. -/
theorem varQ_eq_variance_STR02908 (h : ℝ) {F : ℝ → ℝ} (hF : MemLp F 2 (wmeas_STR02908 h)) :
    varQ_STR02935 h F = variance F (wmeas_STR02908 h) := by
  have := isProbabilityMeasure_wmeas_STR02908 h
  have e1 : ∫ x, (F ^ 2) x ∂(wmeas_STR02908 h)
      = normInt_STR02933 (fun t => F t ^ 2 * qT_STR02904 h t) :=
    integral_wmeas_STR02908 h (fun t => F t ^ 2)
  have e2 : ∫ x, F x ∂(wmeas_STR02908 h)
      = normInt_STR02933 (fun t => F t * qT_STR02904 h t) :=
    integral_wmeas_STR02908 h F
  unfold varQ_STR02935
  rw [variance_eq_sub hF, ← e1, ← e2]

/-- Per-index bound: if `g` is a periodic `H¹` function with weak derivative `dg`, `∫ g² q_h dm = 1`,
`H(g) > 0`, and `|g - 1| ≤ δ ≤ 1/4` almost everywhere, then `(1 - h²)/(1 + 2δ) ≤ 4 ∫ (dg)² q_h dm / (2 H(g))`. -/
theorem quot_bound_STR02908 {h : ℝ} (hh : |h| ≤ 1 / 1000) {g dg : ℝ → ℝ}
    (hfg : IsPeriodicWeakDerivative_STR02933 g dg)
    (hg0 : 0 ≤ᵐ[volume.restrict (Ioc 0 (2 * π))] g)
    (hnorm : normInt_STR02933 (fun t => g t ^ 2 * qT_STR02904 h t) = 1)
    (hpos : 0 < Hent_STR02908 h g) {δ : ℝ} (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    (hae : ∀ᵐ t ∂(volume.restrict (Ioc 0 (2 * π))), |g t - 1| ≤ δ) :
    (1 - h ^ 2) / (1 + 2 * δ)
      ≤ 4 * normInt_STR02933 (fun t => dg t ^ 2 * qT_STR02904 h t) / (2 * Hent_STR02908 h g) := by
  have := isProbabilityMeasure_wmeas_STR02908 h
  have hg0e : ∀ᵐ t ∂(volume.restrict (Ioc 0 (2 * π))), 0 ≤ g t := hg0
  obtain ⟨G, hGsm, hGae⟩ := hfg.1.2.aestronglyMeasurable
  have hGm : Measurable G := hGsm.measurable
  have hb : ∀ᵐ t ∂(volume.restrict (Ioc 0 (2 * π))), |G t - 1| ≤ δ := by
    filter_upwards [hae, hGae] with t h1 h2
    rw [← h2]
    exact h1
  have hg0G : ∀ᵐ t ∂(volume.restrict (Ioc 0 (2 * π))), 0 ≤ G t := by
    filter_upwards [hg0e, hGae] with t h1 h2
    rw [← h2]
    exact h1
  have hb' : ∀ᵐ t ∂(wmeas_STR02908 h), |G t - 1| ≤ δ := ae_wmeas_STR02908 hb
  have hg0' : ∀ᵐ t ∂(wmeas_STR02908 h), 0 ≤ G t := ae_wmeas_STR02908 hg0G
  have hbg : ∀ᵐ t ∂(wmeas_STR02908 h), ‖G t‖ ≤ 5 / 4 := by
    filter_upwards [hb'] with t ht
    rw [Real.norm_eq_abs, abs_le]
    have ht' := abs_le.mp ht
    constructor <;> linarith [ht'.1, ht'.2]
  have hGmem : MemLp G 2 (wmeas_STR02908 h) :=
    MemLp.of_bound hGm.aestronglyMeasurable (5 / 4) hbg
  have hGmemF : MemLp (fun t => G t - normInt_STR02933 g) 2 (wmeas_STR02908 h) :=
    hGmem.sub (memLp_const (normInt_STR02933 g))
  have hGsq : ∀ᵐ t ∂(wmeas_STR02908 h), |G t ^ 2| ≤ 25 / 16 := by
    filter_upwards [hb'] with t ht
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_range_STR02908 (ht.trans hδ4)).2
  have hI2 : Integrable (fun t => G t ^ 2) (wmeas_STR02908 h) :=
    integrable_of_abs_le_STR02943 (hGm.pow_const 2) hGsq
  have hLogb : ∀ᵐ t ∂(wmeas_STR02908 h), |G t ^ 2 * Real.log (G t ^ 2)| ≤ 2 := by
    filter_upwards [hb'] with t ht
    exact abs_sq_log_STR02908 (ht.trans hδ4)
  have hLogI : Integrable (fun t => G t ^ 2 * Real.log (G t ^ 2)) (wmeas_STR02908 h) :=
    integrable_of_abs_le_STR02943 (by fun_prop) hLogb
  have hcongr1 : normInt_STR02933 (fun t => G t ^ 2 * qT_STR02904 h t)
      = normInt_STR02933 (fun t => g t ^ 2 * qT_STR02904 h t) :=
    normInt_congr_STR02908 (by filter_upwards [hGae] with t ht; simp only [ht])
  have hnormG : ∫ x, G x ^ 2 ∂(wmeas_STR02908 h) = 1 := by
    have e : ∫ x, G x ^ 2 ∂(wmeas_STR02908 h)
        = normInt_STR02933 (fun t => G t ^ 2 * qT_STR02904 h t) :=
      integral_wmeas_STR02908 h (fun t => G t ^ 2)
    rw [e, hcongr1, hnorm]
  have hHG : ∫ x, G x ^ 2 * Real.log (G x ^ 2) ∂(wmeas_STR02908 h) = Hent_STR02908 h g := by
    have e : ∫ x, G x ^ 2 * Real.log (G x ^ 2) ∂(wmeas_STR02908 h)
        = normInt_STR02933 (fun t => G t ^ 2 * Real.log (G t ^ 2) * qT_STR02904 h t) :=
      integral_wmeas_STR02908 h (fun t => G t ^ 2 * Real.log (G t ^ 2))
    have hc : normInt_STR02933 (fun t => G t ^ 2 * Real.log (G t ^ 2) * qT_STR02904 h t)
        = normInt_STR02933 (fun t => g t ^ 2 * Real.log (g t ^ 2) * qT_STR02904 h t) :=
      normInt_congr_STR02908 (by filter_upwards [hGae] with t ht; simp only [ht])
    unfold Hent_STR02908
    rw [e, hc]
  have hv0 : 0 ≤ᵐ[wmeas_STR02908 h] fun t => G t ^ 2 :=
    Eventually.of_forall fun t => sq_nonneg (G t)
  have hEntF : DGPS.homogeneousEntropy (wmeas_STR02908 h) (fun t => G t ^ 2)
      = ENNReal.ofReal (∫ x, G x ^ 2 * Real.log (G x ^ 2) ∂(wmeas_STR02908 h)) := by
    rw [DGPS.homogeneousEntropy_eq_formula hv0 hI2 hLogI, hnormG, Real.log_one, mul_zero, sub_zero]
  have hposG : 0 < ∫ x, G x ^ 2 * Real.log (G x ^ 2) ∂(wmeas_STR02908 h) := by
    rw [hHG]
    exact hpos
  have hT := str029_43_entropy_expansion_relative_variance (wmeas_STR02908 h) G hGm hg0' hnormG hb' hδ4
  rw [hEntF, ENNReal.toReal_ofReal hposG.le, hHG] at hT
  have hHV : Hent_STR02908 h g ≤ 2 * (1 + 2 * δ) * variance G (wmeas_STR02908 h) := by
    have := (abs_le.mp hT).2
    linarith
  have hvarQ : varQ_STR02935 h (fun t => g t - normInt_STR02933 g)
      = variance G (wmeas_STR02908 h) := by
    have hcongrF : varQ_STR02935 h (fun t => g t - normInt_STR02933 g)
        = varQ_STR02935 h (fun t => G t - normInt_STR02933 g) :=
      varQ_congr_STR02908 h (by filter_upwards [hGae] with t ht; simp only [ht])
    rw [hcongrF, varQ_eq_variance_STR02908 h hGmemF]
    have hfun : (fun t => G t - normInt_STR02933 g) = (fun t => G t + -normInt_STR02933 g) := by
      funext t
      ring
    rw [hfun]
    exact variance_add_const hGm.aestronglyMeasurable (-normInt_STR02933 g)
  have hD := str029_05_poincare_bound_sufficient_attainment h hh g dg hfg
  rw [hvarQ] at hD
  have hk : 0 ≤ 1 - h ^ 2 := by
    obtain ⟨h1, h2⟩ := abs_le.mp hh
    nlinarith
  have hp1 : 0 < 1 + 2 * δ := by linarith
  have hp2 : 0 < 2 * Hent_STR02908 h g := by linarith
  have k1 := mul_le_mul_of_nonneg_left hHV hk
  have k2 := mul_le_mul_of_nonneg_left hD hp1.le
  rw [div_le_div_iff₀ hp1 hp2]
  nlinarith [k1, k2]

/-- STR029.08, vanishing-entropy endpoint. For `|h| ≤ 1/1000` and periodic `H¹` functions `g n` with weak
derivatives `dg n`, nonnegative, normalized by `∫ (g n)² q_h dm = 1`, converging uniformly to `1`, and with
`H(g n) > 0`, the `EReal` liminf of `4 ∫ (dg n)² q_h dm / (2 H(g n))` is at least `1 - h²`. -/
theorem str029_08_vanishing_entropy_endpoint {h : ℝ} (hh : |h| ≤ 1 / 1000)
    (g dg : ℕ → ℝ → ℝ) (hfg : ∀ n, IsPeriodicWeakDerivative_STR02933 (g n) (dg n))
    (hg0 : ∀ n, 0 ≤ᵐ[volume.restrict (Ioc 0 (2 * π))] g n)
    (hnorm : ∀ n, normInt_STR02933 (fun t => g n t ^ 2 * qT_STR02904 h t) = 1)
    (hpos : ∀ n, 0 < Hent_STR02908 h (g n))
    (hconv : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop, ∀ᵐ t ∂(volume.restrict (Ioc 0 (2 * π))), |g n t - 1| ≤ δ) :
    ((1 - h ^ 2 : ℝ) : EReal) ≤
      Filter.liminf (fun n => ((4 * normInt_STR02933 (fun t => dg n t ^ 2 * qT_STR02904 h t)
        / (2 * Hent_STR02908 h (g n)) : ℝ) : EReal)) atTop := by
  have hlow : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
      (((1 - h ^ 2) / (1 + 2 * δ) : ℝ) : EReal) ≤
        Filter.liminf (fun n => ((4 * normInt_STR02933 (fun t => dg n t ^ 2 * qT_STR02904 h t)
          / (2 * Hent_STR02908 h (g n)) : ℝ) : EReal)) atTop := by
    intro δ hδ0 hδ4
    refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [hconv δ hδ0] with n hn
    exact EReal.coe_le_coe_iff.mpr
      (quot_bound_STR02908 hh (hfg n) (hg0 n) (hnorm n) (hpos n) hδ0 hδ4 hn)
  have hcont : ContinuousAt (fun δ : ℝ => (1 - h ^ 2) / (1 + 2 * δ)) 0 := by
    refine ContinuousAt.div continuousAt_const ?_ ?_
    · fun_prop
    · norm_num
  have h0 : Tendsto (fun δ : ℝ => (1 - h ^ 2) / (1 + 2 * δ)) (𝓝[>] 0)
      (𝓝 ((1 - h ^ 2) / (1 + 2 * 0))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  rw [mul_zero, add_zero, div_one] at h0
  have hlim : Tendsto (fun δ : ℝ => (((1 - h ^ 2) / (1 + 2 * δ) : ℝ) : EReal)) (𝓝[>] 0)
      (𝓝 ((1 - h ^ 2 : ℝ) : EReal)) :=
    EReal.tendsto_coe.mpr h0
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with δ hδ
  exact hlow δ hδ.1 hδ.2.le

end DGPS.Frontier.STR029
