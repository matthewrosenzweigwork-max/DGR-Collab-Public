import DGPS.Frontier.STR029.T44
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# STR029.45: Information coefficients before trigonometric evaluation

Task id: STR029.45. Title: Information coefficients before trigonometric evaluation (node STR029, size L).

Provides:
* `DGPS.Frontier.STR029.str029_45_information_coefficients_before_trigonometric_evaluation`: for every `R`
  there are `h0 > 0` and `K ≥ 0` such that for all `|A|, …, |F| ≤ R` and `|h| ≤ h0`, with `u = h p + h² q`,
  the Fisher information `∫ u'² ρ(h,u) dm` of the logarithmic chart density equals `I₂ h² + 0·h³ + I₄ h⁴` and
  the relative entropy `∫ g² log (g²) q_h dm` (`g² = ρ(h,u)/q_h`) equals `H₂ h² + 0·h³ + H₄ h⁴`, each up to
  `K |h|⁵`.
* `DGPS.Frontier.STR029.I2_STR02945`, `H2_STR02945`: the quadratic coefficients `⟨p'²⟩` and `⟨p²⟩/2`.
* `DGPS.Frontier.STR029.I4_STR02945`, `H4_STR02945`: the fourth coefficients
  `⟨q'²⟩ + 2⟨p'q'v⟩ + ⟨p'²q⟩ + ½⟨p'²v²⟩ - ½⟨p'²⟩⟨v²⟩` and
  `½⟨q²⟩ + ⟨pbq⟩ + ⟨p²q⟩ + ¼(⟨p²b²⟩ - ⟨p²⟩⟨b²⟩) + ⅓⟨p³b⟩ + ⅛⟨p⁴⟩ - ⅜⟨p²⟩²`.
* `DGPS.Frontier.STR029.bFun_STR02945`, `pFun_STR02945`, `qFun_STR02945`, `vFun_STR02945`, `uFun_STR02945`:
  `b = cos 3t`, `p = A cos t + B sin t`, `q = C cos 2t + D sin 2t + E cos 4t + F sin 4t`, `v = b + p`,
  and `u = h p + h² q`.
* `DGPS.Frontier.STR029.refNorm_STR02945`, `refDensity_STR02945`: the normalizer `∫ e^{h cos 3s} dm` and the
  density `q_h` of the reference measure.
* `DGPS.Frontier.STR029.chartNorm_STR02945`, `chartDensity_STR02945`, `chartRatio_STR02945`: the normalizer
  and the density `ρ(h,u)` of the logarithmic chart, and `g² = ρ(h,u)/q_h`.
* `DGPS.Frontier.STR029.chartFisher_STR02945`, `chartEntropy_STR02945`: `∫ u'² ρ(h,u) dm` and
  `∫ g² log (g²) q_h dm`.
* `DGPS.Frontier.STR029.chartNorm_uFun_STR02945`, `refNorm_eq_STR02945`: the chart normalizers are the
  normalizers `Z(h)` of .44 for `(v, q)` and for `(b, 0)`.
* `DGPS.Frontier.STR029.chartFisher_eq_STR02945`, `chartEntropy_eq_STR02945`: closed forms
  `⟨(h p' + h² q')² e^{h v + h² q}⟩ / Z` and
  `⟨(h p + h² q) e^{h v + h² q}⟩ / Z - log Z + log Z_b` of the two chart quantities.
* `DGPS.Frontier.STR029.fisher_expansion_STR02945`, `entropy_expansion_STR02945`: the two halves of the main
  statement with their own `h0` and `K`.
* `DGPS.Frontier.STR029.fisher_generic_STR02945`, `entropy_generic_STR02945`,
  `entropy_full_generic_STR02945`: uniform degree-four expansions of `⟨(h a + h² c)² e^{x_h}⟩ / Z` and of
  the entropy functional for arbitrary admissible `v, q, p` and bounded continuous `a, c`, with explicit
  coefficients before any trigonometric evaluation (definitions `fk0_STR02945`, `fk1_STR02945`,
  `fk2_STR02945`, `ftail_STR02945`, `ek2_STR02945`, `ek3_STR02945`, `ek4_STR02945`, `etail_STR02945`,
  `entC2_STR02945`, `entC3_STR02945`, `entC4_STR02945`).
* `DGPS.Frontier.STR029.fisher_n1_STR02945`, `fisher_n2_STR02945`: the cubic Fisher coefficient vanishes
  (odd/even symmetry under `t ↦ t + π`), and the fourth Fisher coefficient equals the displayed formula.
* `DGPS.Frontier.STR029.ent_a2_STR02945`, `ent_z2_STR02945`, `ent_zb2_STR02945`, `ent_c2_STR02945`,
  `ent_c3_STR02945`, `ent_c4_STR02945`: the quadratic entropy coefficient `⟨p²⟩/2`, the vanishing cubic
  coefficient, and the fourth entropy coefficient in the displayed form.
* `DGPS.Frontier.STR029.pb_mode_STR02945`, `normInt_pFun_mul_bFun_STR02945`: `p b` is a sum of modes of
  frequencies two and four, so `⟨p b⟩ = 0`.
* `DGPS.Frontier.STR029.pFun_shift_STR02945`, `bFun_shift_STR02945`, `vFun_shift_STR02945`,
  `qFun_shift_STR02945`, `deriv_pFun_shift_STR02945`, `deriv_qFun_shift_STR02945`: `p, b, v, p'` change sign
  and `q, q'` are unchanged under `t ↦ t + π`.
* `DGPS.Frontier.STR029.pFun_cont_STR02945`, `qFun_cont_STR02945`, `bFun_cont_STR02945`,
  `vFun_cont_STR02945`, `deriv_pFun_cont_STR02945`, `deriv_qFun_cont_STR02945`, `deriv_uFun_STR02945`:
  continuity of the carriers and their derivatives, and `u' = h p' + h² q'`.
* `DGPS.Frontier.STR029.mode1_STR02945`, `mode2_STR02945` with `mode1_cont_STR02945`, `mode2_cont_STR02945`,
  `mode1_hasDerivAt_STR02945`, `mode2_hasDerivAt_STR02945`, `mode2_deriv_STR02945`, `mode1_abs_le_STR02945`,
  `mode2_abs_le_STR02945`, `normInt_mode1_STR02945`, `normInt_mode2_STR02945`, `mode1_shift_STR02945`,
  `mode2_shift_odd_STR02945`, `mode2_shift_even_STR02945`, `mode1_periodic_STR02945`,
  `mode2_admissible_STR02945`: one- and two-mode trigonometric sums, their derivatives, bounds, vanishing
  means, symmetry under `t ↦ t + π`, and admissibility in the sense of .44.
* `DGPS.Frontier.STR029.Mbound_STR02945`, `pFun_eq_STR02945`, `qFun_eq_STR02945`, `bFun_eq_STR02945`,
  `vFun_eq_STR02945`, `zero_eq_STR02945`, `deriv_pFun_STR02945`, `deriv_qFun_STR02945`,
  `pFun_admissible_STR02945`, `qFun_admissible_STR02945`, `bFun_admissible_STR02945`,
  `vFun_admissible_STR02945`, `zero_admissible_STR02945`, `admissible_deriv_bound_STR02945`: the carriers as
  mode sums, their derivatives, and admissibility with the single bound `M = 13 + 56 max(R, 0)` on the box.
* `DGPS.Frontier.STR029.normInt_antiperiodic_STR02945`, `normInt_cos_nat_STR02945`, `normInt_sin_nat_STR02945`,
  `normInt_congr_STR02945`, `normInt_addmul_STR02945`, `normInt_lin2_STR02945`, …, `normInt_lin6_STR02945`:
  normalized-integral algebra (vanishing for `f(t+π) = -f(t)`, vanishing of `cos nt`, `sin nt`, congruence,
  linearity for two to six summands).
* `DGPS.Frontier.STR029.bound5_STR02945`, `absmul_le_STR02945`, `abs_split4_STR02945`,
  `assemble_STR02945`, `fisher_poly_id_STR02945`, `entropy_poly_id_STR02945`: a compactness bound for a
  continuous function of five bounded reals, two absolute-value utilities, the scalar assembly of a numerator
  and an inverse normalizer expansion, and the two polynomial identities.

R5 notes:
* Carriers: concrete functions `ℝ → ℝ` (as in .44 and T33), `⟨f⟩ = normInt_STR02933 f = (2π)⁻¹ ∫_{(0,2π]} f`.
  The derivatives `p'`, `q'`, `u'` are `deriv` of the concrete functions; they are shown to exist and to be the
  displayed trigonometric sums.
* Reading of the data: `b = cos 3t`, `p = A cos t + B sin t`, `q = C cos 2t + D sin 2t + E cos 4t + F sin 4t`
  (the form of `q` printed in .09), `v = b + p`, `u = h p + h² q`, so that `h cos 3t + u = h v + h² q`.
* Chart quantities: the preamble defines `ρ(h,u)` and `q_h` and states that in the logarithmic chart
  `I_h(ρ(h,u)) = ∫ u'² ρ(h,u) dm` and `H_h(ρ) = ∫ g² log (g²) q_h dm` with `g² = ρ/q_h`. The definitions
  `chartFisher_STR02945` and `chartEntropy_STR02945` are exactly these two integrals; no identification with
  `4 ∫ g'² q_h dm` is attempted here (that identification belongs to .01). `Real.log 0 = 0` realizes the
  convention `z log z = 0` at `z = 0` (not needed, since all densities are positive for `|h| ≤ h0`).
  The chart definitions accept any `u : ℝ → ℝ`; no mean-zero requirement is imposed (the function
  `u = h p + h² q` used in the statement has mean zero, but this is not needed).
* Uniformity: the statement is uniform over the box `|A|, …, |F| ≤ R` (a strengthening of the fixed-coefficient
  reading). The constants `h0` and `K` depend only on `R`, through the `C²` bound `M = 13 + 56 max(R, 0)` of .44
  that dominates `p, q, v, b, 0` and `p', q'`. The restriction is `|h| ≤ h0`, so negative `h` is included.
  `h0` is the minimum of the constants of the two expansions and of the `h0` of .44 (which also gives
  `Z(h) ≥ 1/2` and hence positivity of both normalizers).
* The cubic coefficients are stated as the literal `0 * h ^ 3`. The vanishing is proved, not assumed, from the
  symmetry `t ↦ t + π` (`p, b, v, p'` odd; `q, q'` even): the whole cubic coefficient is the normalized
  integral of an antiperiodic function. This replaces, and does not separately state, the individual relations
  `⟨bp⟩ = ⟨pq⟩ = ⟨p²b⟩ = ⟨p³⟩ = 0` and the frequency count for cubic products of odd frequencies that the
  specification lists for the cubic cancellation.
* Besides `⟨q⟩ = 0` (part of admissibility in the sense of .44) the only orthogonality relation used at the
  quadratic and quartic order is `⟨p b⟩ = 0`, proved from the product-to-sum formulas for frequencies `1 ± 3`.
* The fifth remainder is the uniform one of .44, applied to `(v, q)` and `(b, 0)`; the numerator remainder is
  controlled by a compactness bound on the explicit polynomial tails (`bound5_STR02945`), so the final
  constant `K` is existential and not explicit.
* No hypothesis is added to the specification; `R` is the radius of the coefficient box and `h0`, `K` are
  existentially quantified.
-/

open MeasureTheory Set Real

namespace DGPS.Frontier.STR029

/-- The first-harmonic-free profile `b(t) = cos 3t`. -/
noncomputable def bFun_STR02945 (t : ℝ) : ℝ := Real.cos (3 * t)

/-- The first harmonic `p(t) = A cos t + B sin t`. -/
noncomputable def pFun_STR02945 (A B t : ℝ) : ℝ := A * Real.cos t + B * Real.sin t

/-- The second-order profile `q(t) = C cos 2t + D sin 2t + E cos 4t + F sin 4t`. -/
noncomputable def qFun_STR02945 (C D E F t : ℝ) : ℝ :=
  C * Real.cos (2 * t) + D * Real.sin (2 * t) + E * Real.cos (4 * t) + F * Real.sin (4 * t)

/-- The exponent profile `v = b + p`. -/
noncomputable def vFun_STR02945 (A B t : ℝ) : ℝ := bFun_STR02945 t + pFun_STR02945 A B t

/-- The logarithmic-chart argument `u = h p + h² q`. -/
noncomputable def uFun_STR02945 (A B C D E F h t : ℝ) : ℝ :=
  h * pFun_STR02945 A B t + h ^ 2 * qFun_STR02945 C D E F t

theorem bound5_STR02945 (N : ℝ) (f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hf : Continuous (fun x : Fin 5 → ℝ => f (x 0) (x 1) (x 2) (x 3) (x 4))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x0 x1 x2 x3 x4 : ℝ, |x0| ≤ N → |x1| ≤ N → |x2| ≤ N → |x3| ≤ N →
      |x4| ≤ N → |f x0 x1 x2 x3 x4| ≤ K := by
  have hc : IsCompact (Set.pi Set.univ (fun _ : Fin 5 => Set.Icc (-N) N)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨K, hK⟩ := hc.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max K 0, le_max_right _ _, fun x0 x1 x2 x3 x4 h0 h1 h2 h3 h4 => ?_⟩
  have hmem : (![x0, x1, x2, x3, x4] : Fin 5 → ℝ) ∈
      Set.pi Set.univ (fun _ : Fin 5 => Set.Icc (-N) N) := by
    intro i _
    fin_cases i <;> simp [abs_le.mp h0, abs_le.mp h1, abs_le.mp h2, abs_le.mp h3, abs_le.mp h4]
  have := hK _ hmem
  simp at this
  exact this.trans (le_max_left _ _)

theorem normInt_antiperiodic_STR02945 {f : ℝ → ℝ} (hc : Continuous f)
    (hanti : ∀ t, f (t + π) = - f t) : normInt_STR02933 f = 0 := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  unfold normInt_STR02933
  have h1 : ∫ t in Ioc 0 (2 * π), f t = ∫ t in (0:ℝ)..(2 * π), f t :=
    (intervalIntegral.integral_of_le (by positivity)).symm
  have h2 : ∫ t in (0:ℝ)..(2 * π), f t = (∫ t in (0:ℝ)..π, f t) + ∫ t in π..(2 * π), f t :=
    (intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)).symm.trans (by rw [two_mul])
  have h3 : ∫ t in π..(2 * π), f t = - ∫ t in (0:ℝ)..π, f t := by
    have := intervalIntegral.integral_comp_add_right f π (a := 0) (b := π)
    rw [zero_add, ← two_mul] at this
    rw [← this]
    simp only [hanti]
    rw [intervalIntegral.integral_neg]
  rw [h1, h2, h3]
  ring

theorem normInt_cos_nat_STR02945 {n : ℕ} (hn : 1 ≤ n) :
    normInt_STR02933 (fun t => Real.cos (n * t)) = 0 := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hn' : (n:ℝ) ≠ 0 := by positivity
  unfold normInt_STR02933
  rw [(intervalIntegral.integral_of_le (by positivity)).symm]
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hn', integral_cos]
  have : Real.sin (n * (2 * π)) = 0 := by
    rw [show (n:ℝ) * (2 * π) = ((2 * n : ℕ) : ℝ) * π by push_cast; ring]
    exact Real.sin_nat_mul_pi _
  simp [this]

theorem normInt_sin_nat_STR02945 {n : ℕ} (hn : 1 ≤ n) :
    normInt_STR02933 (fun t => Real.sin (n * t)) = 0 := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hn' : (n:ℝ) ≠ 0 := by positivity
  unfold normInt_STR02933
  rw [(intervalIntegral.integral_of_le (by positivity)).symm]
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hn', integral_sin]
  have : Real.cos (n * (2 * π)) = 1 := by
    exact Real.cos_nat_mul_two_pi n
  simp [this]

theorem normInt_congr_STR02945 {f g : ℝ → ℝ} (h : ∀ t, f t = g t) :
    normInt_STR02933 f = normInt_STR02933 g := by
  have : f = g := funext h
  rw [this]

theorem normInt_addmul_STR02945 {g f : ℝ → ℝ} (c : ℝ) (hg : Continuous g) (hf : Continuous f) :
    normInt_STR02933 (fun t => g t + c * f t) = normInt_STR02933 g + c * normInt_STR02933 f := by
  have hcf : Continuous (fun t => c * f t) := by fun_prop
  rw [normInt_add_STR02944 hg hcf, normInt_mul_const_STR02933]

theorem normInt_lin2_STR02945 {f1 f2 : ℝ → ℝ} (c1 c2 : ℝ) (h1 : Continuous f1)
    (h2 : Continuous f2) :
    normInt_STR02933 (fun t => c1 * f1 t + c2 * f2 t) =
      c1 * normInt_STR02933 f1 + c2 * normInt_STR02933 f2 := by
  have hc1 : Continuous (fun t => c1 * f1 t) := by fun_prop
  rw [normInt_addmul_STR02945 c2 hc1 h2, normInt_mul_const_STR02933]

theorem normInt_lin3_STR02945 {f1 f2 f3 : ℝ → ℝ} (c1 c2 c3 : ℝ) (h1 : Continuous f1)
    (h2 : Continuous f2) (h3 : Continuous f3) :
    normInt_STR02933 (fun t => c1 * f1 t + c2 * f2 t + c3 * f3 t) =
      c1 * normInt_STR02933 f1 + c2 * normInt_STR02933 f2 + c3 * normInt_STR02933 f3 := by
  have hc : Continuous (fun t => c1 * f1 t + c2 * f2 t) := by fun_prop
  rw [normInt_addmul_STR02945 c3 hc h3, normInt_lin2_STR02945 c1 c2 h1 h2]

theorem normInt_lin4_STR02945 {f1 f2 f3 f4 : ℝ → ℝ} (c1 c2 c3 c4 : ℝ) (h1 : Continuous f1)
    (h2 : Continuous f2) (h3 : Continuous f3) (h4 : Continuous f4) :
    normInt_STR02933 (fun t => c1 * f1 t + c2 * f2 t + c3 * f3 t + c4 * f4 t) =
      c1 * normInt_STR02933 f1 + c2 * normInt_STR02933 f2 + c3 * normInt_STR02933 f3 +
        c4 * normInt_STR02933 f4 := by
  have hc : Continuous (fun t => c1 * f1 t + c2 * f2 t + c3 * f3 t) := by fun_prop
  rw [normInt_addmul_STR02945 c4 hc h4, normInt_lin3_STR02945 c1 c2 c3 h1 h2 h3]

theorem normInt_lin5_STR02945 {f1 f2 f3 f4 f5 : ℝ → ℝ} (c1 c2 c3 c4 c5 : ℝ) (h1 : Continuous f1)
    (h2 : Continuous f2) (h3 : Continuous f3) (h4 : Continuous f4) (h5 : Continuous f5) :
    normInt_STR02933 (fun t => c1 * f1 t + c2 * f2 t + c3 * f3 t + c4 * f4 t + c5 * f5 t) =
      c1 * normInt_STR02933 f1 + c2 * normInt_STR02933 f2 + c3 * normInt_STR02933 f3 +
        c4 * normInt_STR02933 f4 + c5 * normInt_STR02933 f5 := by
  have hc : Continuous (fun t => c1 * f1 t + c2 * f2 t + c3 * f3 t + c4 * f4 t) := by fun_prop
  rw [normInt_addmul_STR02945 c5 hc h5, normInt_lin4_STR02945 c1 c2 c3 c4 h1 h2 h3 h4]

theorem normInt_lin6_STR02945 {f1 f2 f3 f4 f5 f6 : ℝ → ℝ} (c1 c2 c3 c4 c5 c6 : ℝ)
    (h1 : Continuous f1) (h2 : Continuous f2) (h3 : Continuous f3) (h4 : Continuous f4)
    (h5 : Continuous f5) (h6 : Continuous f6) :
    normInt_STR02933
        (fun t => c1 * f1 t + c2 * f2 t + c3 * f3 t + c4 * f4 t + c5 * f5 t + c6 * f6 t) =
      c1 * normInt_STR02933 f1 + c2 * normInt_STR02933 f2 + c3 * normInt_STR02933 f3 +
        c4 * normInt_STR02933 f4 + c5 * normInt_STR02933 f5 + c6 * normInt_STR02933 f6 := by
  have hc : Continuous (fun t => c1 * f1 t + c2 * f2 t + c3 * f3 t + c4 * f4 t + c5 * f5 t) := by
    fun_prop
  rw [normInt_addmul_STR02945 c6 hc h6, normInt_lin5_STR02945 c1 c2 c3 c4 c5 h1 h2 h3 h4 h5]

/-- A single trigonometric mode `a cos (n t) + b sin (n t)`. -/
noncomputable def mode1_STR02945 (a b : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  a * Real.cos (n * t) + b * Real.sin (n * t)

/-- A sum of two trigonometric modes. -/
noncomputable def mode2_STR02945 (a1 b1 : ℝ) (n1 : ℕ) (a2 b2 : ℝ) (n2 : ℕ) (t : ℝ) : ℝ :=
  mode1_STR02945 a1 b1 n1 t + mode1_STR02945 a2 b2 n2 t

theorem mode1_cont_STR02945 (a b : ℝ) (n : ℕ) : Continuous (mode1_STR02945 a b n) := by
  unfold mode1_STR02945; fun_prop

theorem mode2_cont_STR02945 (a1 b1 : ℝ) (n1 : ℕ) (a2 b2 : ℝ) (n2 : ℕ) :
    Continuous (mode2_STR02945 a1 b1 n1 a2 b2 n2) := by
  unfold mode2_STR02945; exact (mode1_cont_STR02945 _ _ _).add (mode1_cont_STR02945 _ _ _)

theorem mode1_hasDerivAt_STR02945 (a b : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (mode1_STR02945 a b n) (mode1_STR02945 (n * b) (-(n * a)) n t) t := by
  have hl : HasDerivAt (fun t : ℝ => (n : ℝ) * t) (n : ℝ) t := by
    simpa using (hasDerivAt_id t).const_mul (n : ℝ)
  have h := (hl.cos.const_mul a).add (hl.sin.const_mul b)
  have e : mode1_STR02945 (n * b) (-(n * a)) n t =
      a * (-Real.sin (n * t) * n) + b * (Real.cos (n * t) * n) := by
    unfold mode1_STR02945; ring
  rw [e]; exact h

theorem mode2_hasDerivAt_STR02945 (a1 b1 : ℝ) (n1 : ℕ) (a2 b2 : ℝ) (n2 : ℕ) (t : ℝ) :
    HasDerivAt (mode2_STR02945 a1 b1 n1 a2 b2 n2)
      (mode2_STR02945 (n1 * b1) (-(n1 * a1)) n1 (n2 * b2) (-(n2 * a2)) n2 t) t :=
  (mode1_hasDerivAt_STR02945 a1 b1 n1 t).add (mode1_hasDerivAt_STR02945 a2 b2 n2 t)

theorem mode2_deriv_STR02945 (a1 b1 : ℝ) (n1 : ℕ) (a2 b2 : ℝ) (n2 : ℕ) :
    deriv (mode2_STR02945 a1 b1 n1 a2 b2 n2) =
      mode2_STR02945 (n1 * b1) (-(n1 * a1)) n1 (n2 * b2) (-(n2 * a2)) n2 :=
  funext fun t => (mode2_hasDerivAt_STR02945 a1 b1 n1 a2 b2 n2 t).deriv

theorem mode1_abs_le_STR02945 (a b : ℝ) (n : ℕ) (t : ℝ) :
    |mode1_STR02945 a b n t| ≤ |a| + |b| := by
  unfold mode1_STR02945
  calc |a * Real.cos (n * t) + b * Real.sin (n * t)|
      ≤ |a * Real.cos (n * t)| + |b * Real.sin (n * t)| := abs_add_le _ _
    _ ≤ |a| + |b| := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
        (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))

theorem mode2_abs_le_STR02945 (a1 b1 : ℝ) (n1 : ℕ) (a2 b2 : ℝ) (n2 : ℕ) (t : ℝ) :
    |mode2_STR02945 a1 b1 n1 a2 b2 n2 t| ≤ (|a1| + |b1|) + (|a2| + |b2|) := by
  unfold mode2_STR02945
  exact (abs_add_le _ _).trans (add_le_add (mode1_abs_le_STR02945 _ _ _ _)
    (mode1_abs_le_STR02945 _ _ _ _))

theorem normInt_mode1_STR02945 (a b : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    normInt_STR02933 (mode1_STR02945 a b n) = 0 := by
  have h := normInt_lin2_STR02945 a b (f1 := fun t => Real.cos (n * t))
    (f2 := fun t => Real.sin (n * t)) (by fun_prop) (by fun_prop)
  show normInt_STR02933 (fun t => a * Real.cos (n * t) + b * Real.sin (n * t)) = 0
  rw [h, normInt_cos_nat_STR02945 hn, normInt_sin_nat_STR02945 hn]; ring

theorem normInt_mode2_STR02945 (a1 b1 : ℝ) {n1 : ℕ} (a2 b2 : ℝ) {n2 : ℕ} (h1 : 1 ≤ n1)
    (h2 : 1 ≤ n2) : normInt_STR02933 (mode2_STR02945 a1 b1 n1 a2 b2 n2) = 0 := by
  show normInt_STR02933 (fun t => mode1_STR02945 a1 b1 n1 t + mode1_STR02945 a2 b2 n2 t) = 0
  rw [normInt_add_STR02944 (mode1_cont_STR02945 _ _ _) (mode1_cont_STR02945 _ _ _),
    normInt_mode1_STR02945 _ _ h1, normInt_mode1_STR02945 _ _ h2]
  ring

theorem mode1_shift_STR02945 (a b : ℝ) (n : ℕ) (t : ℝ) :
    mode1_STR02945 a b n (t + π) = (-1) ^ n * mode1_STR02945 a b n t := by
  unfold mode1_STR02945
  rw [show (n : ℝ) * (t + π) = n * t + n * π by ring, Real.cos_add_nat_mul_pi,
    Real.sin_add_nat_mul_pi]
  ring

theorem mode2_shift_odd_STR02945 (a1 b1 : ℝ) {n1 : ℕ} (a2 b2 : ℝ) {n2 : ℕ} (h1 : Odd n1)
    (h2 : Odd n2) (t : ℝ) :
    mode2_STR02945 a1 b1 n1 a2 b2 n2 (t + π) = - mode2_STR02945 a1 b1 n1 a2 b2 n2 t := by
  unfold mode2_STR02945
  rw [mode1_shift_STR02945, mode1_shift_STR02945, h1.neg_one_pow, h2.neg_one_pow]
  ring

theorem mode2_shift_even_STR02945 (a1 b1 : ℝ) {n1 : ℕ} (a2 b2 : ℝ) {n2 : ℕ} (h1 : Even n1)
    (h2 : Even n2) (t : ℝ) :
    mode2_STR02945 a1 b1 n1 a2 b2 n2 (t + π) = mode2_STR02945 a1 b1 n1 a2 b2 n2 t := by
  unfold mode2_STR02945
  rw [mode1_shift_STR02945, mode1_shift_STR02945, h1.neg_one_pow, h2.neg_one_pow]
  ring

theorem mode1_periodic_STR02945 (a b : ℝ) (n : ℕ) (t : ℝ) :
    mode1_STR02945 a b n (t + 2 * π) = mode1_STR02945 a b n t := by
  unfold mode1_STR02945
  rw [show (n : ℝ) * (t + 2 * π) = n * t + n * (2 * π) by ring, Real.cos_add_nat_mul_two_pi,
    Real.sin_add_nat_mul_two_pi]

theorem mode2_admissible_STR02945 (M a1 b1 a2 b2 : ℝ) {n1 n2 : ℕ} (h1 : 1 ≤ n1) (h2 : 1 ≤ n2)
    (hM : (|a1| + |b1|) * (1 + n1 + n1 ^ 2) + (|a2| + |b2|) * (1 + n2 + n2 ^ 2) ≤ M) :
    IsAdmissible_STR02944 M (mode2_STR02945 a1 b1 n1 a2 b2 n2) := by
  refine ⟨?_, normInt_mode2_STR02945 a1 b1 a2 b2 h1 h2, ?_, ?_⟩
  · intro t
    unfold mode2_STR02945
    rw [mode1_periodic_STR02945, mode1_periodic_STR02945]
  · unfold mode2_STR02945 mode1_STR02945; fun_prop
  · have hn1 : (0 : ℝ) ≤ n1 := Nat.cast_nonneg _
    have hn2 : (0 : ℝ) ≤ n2 := Nat.cast_nonneg _
    refine ⟨(|a1| + |b1|) + (|a2| + |b2|), n1 * (|a1| + |b1|) + n2 * (|a2| + |b2|),
      n1 ^ 2 * (|a1| + |b1|) + n2 ^ 2 * (|a2| + |b2|), by nlinarith,
      fun t => mode2_abs_le_STR02945 _ _ _ _ _ _ t, fun t => ?_, fun t => ?_⟩
    · rw [mode2_deriv_STR02945]
      refine (mode2_abs_le_STR02945 _ _ _ _ _ _ t).trans (le_of_eq ?_)
      simp only [abs_mul, abs_neg, Nat.abs_cast]
      ring
    · rw [mode2_deriv_STR02945, mode2_deriv_STR02945]
      refine (mode2_abs_le_STR02945 _ _ _ _ _ _ t).trans (le_of_eq ?_)
      simp only [abs_mul, abs_neg, Nat.abs_cast]
      ring

/-- The admissibility bound used for the whole box `|A|, …, |F| ≤ R`. -/
noncomputable def Mbound_STR02945 (R : ℝ) : ℝ := 13 + 56 * max R 0

theorem pFun_eq_STR02945 (A B : ℝ) : pFun_STR02945 A B = mode2_STR02945 A B 1 0 0 1 := by
  funext t; simp [pFun_STR02945, mode2_STR02945, mode1_STR02945]

theorem qFun_eq_STR02945 (C D E F : ℝ) :
    qFun_STR02945 C D E F = mode2_STR02945 C D 2 E F 4 := by
  funext t; simp [qFun_STR02945, mode2_STR02945, mode1_STR02945]; ring

theorem bFun_eq_STR02945 : bFun_STR02945 = mode2_STR02945 1 0 3 0 0 3 := by
  funext t; simp [bFun_STR02945, mode2_STR02945, mode1_STR02945]

theorem vFun_eq_STR02945 (A B : ℝ) : vFun_STR02945 A B = mode2_STR02945 A B 1 1 0 3 := by
  funext t; simp [vFun_STR02945, bFun_STR02945, pFun_STR02945, mode2_STR02945, mode1_STR02945]
  ring

theorem zero_eq_STR02945 : (fun _ : ℝ => (0 : ℝ)) = mode2_STR02945 0 0 1 0 0 1 := by
  funext t; simp [mode2_STR02945, mode1_STR02945]

theorem deriv_pFun_STR02945 (A B : ℝ) :
    deriv (pFun_STR02945 A B) = mode2_STR02945 B (-A) 1 0 0 1 := by
  rw [pFun_eq_STR02945, mode2_deriv_STR02945]; simp

theorem deriv_qFun_STR02945 (C D E F : ℝ) :
    deriv (qFun_STR02945 C D E F) = mode2_STR02945 (2 * D) (-(2 * C)) 2 (4 * F) (-(4 * E)) 4 := by
  rw [qFun_eq_STR02945, mode2_deriv_STR02945]; norm_num

theorem pFun_admissible_STR02945 (R : ℝ) {A B : ℝ} (hA : |A| ≤ R) (hB : |B| ≤ R) :
    IsAdmissible_STR02944 (Mbound_STR02945 R) (pFun_STR02945 A B) := by
  rw [pFun_eq_STR02945]
  refine mode2_admissible_STR02945 _ _ _ _ _ le_rfl le_rfl ?_
  have h1 := hA.trans (le_max_left R 0)
  have h2 := hB.trans (le_max_left R 0)
  have h3 := le_max_right R 0
  unfold Mbound_STR02945
  norm_num
  linarith

theorem qFun_admissible_STR02945 (R : ℝ) {C D E F : ℝ} (hC : |C| ≤ R) (hD : |D| ≤ R)
    (hE : |E| ≤ R) (hF : |F| ≤ R) :
    IsAdmissible_STR02944 (Mbound_STR02945 R) (qFun_STR02945 C D E F) := by
  rw [qFun_eq_STR02945]
  refine mode2_admissible_STR02945 _ _ _ _ _ (by norm_num) (by norm_num) ?_
  have h1 := hC.trans (le_max_left R 0)
  have h2 := hD.trans (le_max_left R 0)
  have h3 := hE.trans (le_max_left R 0)
  have h4 := hF.trans (le_max_left R 0)
  unfold Mbound_STR02945
  norm_num
  linarith

theorem bFun_admissible_STR02945 (R : ℝ) :
    IsAdmissible_STR02944 (Mbound_STR02945 R) bFun_STR02945 := by
  rw [bFun_eq_STR02945]
  refine mode2_admissible_STR02945 _ _ _ _ _ (by norm_num) (by norm_num) ?_
  unfold Mbound_STR02945
  norm_num

theorem vFun_admissible_STR02945 (R : ℝ) {A B : ℝ} (hA : |A| ≤ R) (hB : |B| ≤ R) :
    IsAdmissible_STR02944 (Mbound_STR02945 R) (vFun_STR02945 A B) := by
  rw [vFun_eq_STR02945]
  refine mode2_admissible_STR02945 _ _ _ _ _ le_rfl (by norm_num) ?_
  have h1 := hA.trans (le_max_left R 0)
  have h2 := hB.trans (le_max_left R 0)
  have h3 := le_max_right R 0
  unfold Mbound_STR02945
  norm_num
  linarith

theorem zero_admissible_STR02945 (R : ℝ) :
    IsAdmissible_STR02944 (Mbound_STR02945 R) (fun _ : ℝ => (0 : ℝ)) := by
  rw [zero_eq_STR02945]
  refine mode2_admissible_STR02945 _ _ _ _ _ le_rfl le_rfl ?_
  have h3 := le_max_right R 0
  unfold Mbound_STR02945
  norm_num
  linarith

theorem admissible_deriv_bound_STR02945 {M : ℝ} {f : ℝ → ℝ} (hf : IsAdmissible_STR02944 M f)
    (t : ℝ) : |deriv f t| ≤ M := by
  obtain ⟨_, _, _, A, B, C, hsum, hA, hB, hC⟩ := hf
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  linarith [hB t]

theorem absmul_le_STR02945 {a x B S : ℝ} (ha : |a| ≤ B) (hx : |x| ≤ S) : |a * x| ≤ B * S := by
  rw [abs_mul]
  exact mul_le_mul ha hx (abs_nonneg _) ((abs_nonneg _).trans ha)

/-- Scalar assembly: multiplying a degree-four numerator by a degree-four inverse expansion. -/
theorem assemble_STR02945 {h Num Zinv a2 a3 a4 R z2 z3 y4 r5 B C K1 K2 : ℝ}
    (hh : |h| ≤ 1) (hB : 0 ≤ B) (hC : 0 ≤ C) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hNum : Num = a2 * h ^ 2 + a3 * h ^ 3 + a4 * h ^ 4 + R) (hR : |R| ≤ K1 * |h| ^ 5)
    (ha2 : |a2| ≤ B) (ha3 : |a3| ≤ B) (ha4 : |a4| ≤ B)
    (hZ : Zinv = 1 - z2 * h ^ 2 - z3 * h ^ 3 + y4 * h ^ 4 + r5) (hr5 : |r5| ≤ K2 * |h| ^ 5)
    (hz2 : |z2| ≤ C) (hz3 : |z3| ≤ C) (hy4 : |y4| ≤ C) :
    |Num * Zinv - (a2 * h ^ 2 + a3 * h ^ 3 + (a4 - a2 * z2) * h ^ 4)| ≤
      (K1 + B * (2 * C + K2) + (2 * B + K1) * (3 * C + K2)) * |h| ^ 5 := by
  have hid : Num * Zinv - (a2 * h ^ 2 + a3 * h ^ 3 + (a4 - a2 * z2) * h ^ 4) =
      R + a2 * h ^ 2 * (-(z3 * h ^ 3) + y4 * h ^ 4 + r5) +
        (a3 * h ^ 3 + a4 * h ^ 4 + R) * (-(z2 * h ^ 2) - z3 * h ^ 3 + y4 * h ^ 4 + r5) := by
    rw [hNum, hZ]; ring
  rw [hid]
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = |h| := ⟨_, rfl⟩
  rw [← hs] at hh hR hr5 ⊢
  have hs0 : 0 ≤ s := hs ▸ abs_nonneg h
  have hp : ∀ k : ℕ, |h ^ k| = s ^ k := fun k => by rw [abs_pow, hs]
  have h43 : s ^ 4 ≤ s ^ 3 := pow_le_pow_of_le_one hs0 hh (by norm_num)
  have h53 : s ^ 5 ≤ s ^ 3 := pow_le_pow_of_le_one hs0 hh (by norm_num)
  have h32 : s ^ 3 ≤ s ^ 2 := pow_le_pow_of_le_one hs0 hh (by norm_num)
  have h42 : s ^ 4 ≤ s ^ 2 := pow_le_pow_of_le_one hs0 hh (by norm_num)
  have h52 : s ^ 5 ≤ s ^ 2 := pow_le_pow_of_le_one hs0 hh (by norm_num)
  have h65 : s ^ 6 ≤ s ^ 5 := pow_le_pow_of_le_one hs0 hh (by norm_num)
  have h75 : s ^ 7 ≤ s ^ 5 := pow_le_pow_of_le_one hs0 hh (by norm_num)
  -- bound for the first correction
  have hX1 : |-(z3 * h ^ 3) + y4 * h ^ 4 + r5| ≤ C * s ^ 3 + C * s ^ 4 + K2 * s ^ 5 := by
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) hr5)
    · rw [abs_neg]; simpa [hp] using absmul_le_STR02945 hz3 (le_of_eq (hp 3))
    · simpa [hp] using absmul_le_STR02945 hy4 (le_of_eq (hp 4))
  have hX2 : |-(z2 * h ^ 2) - z3 * h ^ 3 + y4 * h ^ 4 + r5| ≤
      C * s ^ 2 + C * s ^ 3 + C * s ^ 4 + K2 * s ^ 5 := by
    have e1 := absmul_le_STR02945 hz2 (le_of_eq (hp 2))
    have e2 := absmul_le_STR02945 hz3 (le_of_eq (hp 3))
    have e3 := absmul_le_STR02945 hy4 (le_of_eq (hp 4))
    calc |-(z2 * h ^ 2) - z3 * h ^ 3 + y4 * h ^ 4 + r5|
        = |(-(z2 * h ^ 2)) + (-(z3 * h ^ 3)) + y4 * h ^ 4 + r5| := by ring_nf
      _ ≤ |z2 * h ^ 2| + |z3 * h ^ 3| + |y4 * h ^ 4| + |r5| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
          (add_le_add ((abs_add_le _ _).trans (add_le_add (le_of_eq (abs_neg _))
            (le_of_eq (abs_neg _)))) le_rfl)) le_rfl)
      _ ≤ C * s ^ 2 + C * s ^ 3 + C * s ^ 4 + K2 * s ^ 5 := by linarith
  have hY : |a3 * h ^ 3 + a4 * h ^ 4 + R| ≤ B * s ^ 3 + B * s ^ 4 + K1 * s ^ 5 := by
    have e1 := absmul_le_STR02945 ha3 (le_of_eq (hp 3))
    have e2 := absmul_le_STR02945 ha4 (le_of_eq (hp 4))
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add e1 e2)) hR)
  have hA : |a2 * h ^ 2| ≤ B * s ^ 2 := absmul_le_STR02945 ha2 (le_of_eq (hp 2))
  have hT1 : |a2 * h ^ 2 * (-(z3 * h ^ 3) + y4 * h ^ 4 + r5)| ≤
      B * s ^ 2 * (C * s ^ 3 + C * s ^ 4 + K2 * s ^ 5) := by
    exact (abs_mul _ _).le.trans (mul_le_mul hA hX1 (abs_nonneg _) (by positivity))
  have hT2 : |(a3 * h ^ 3 + a4 * h ^ 4 + R) * (-(z2 * h ^ 2) - z3 * h ^ 3 + y4 * h ^ 4 + r5)| ≤
      (B * s ^ 3 + B * s ^ 4 + K1 * s ^ 5) *
        (C * s ^ 2 + C * s ^ 3 + C * s ^ 4 + K2 * s ^ 5) := by
    exact (abs_mul _ _).le.trans (mul_le_mul hY hX2 (abs_nonneg _) (by positivity))
  have k1 : B * s ^ 2 * (C * s ^ 3 + C * s ^ 4 + K2 * s ^ 5) ≤ B * (2 * C + K2) * s ^ 5 := by
    linarith only [mul_nonneg (mul_nonneg hB hC) (sub_nonneg.2 h65),
      mul_nonneg (mul_nonneg hB hK2) (sub_nonneg.2 h75)]
  have k2a : B * s ^ 3 + B * s ^ 4 + K1 * s ^ 5 ≤ (2 * B + K1) * s ^ 3 := by
    linarith only [mul_nonneg hB (sub_nonneg.2 h43), mul_nonneg hK1 (sub_nonneg.2 h53)]
  have k2b : C * s ^ 2 + C * s ^ 3 + C * s ^ 4 + K2 * s ^ 5 ≤ (3 * C + K2) * s ^ 2 := by
    linarith only [mul_nonneg hC (sub_nonneg.2 h32), mul_nonneg hC (sub_nonneg.2 h42),
      mul_nonneg hK2 (sub_nonneg.2 h52)]
  have k2 : (B * s ^ 3 + B * s ^ 4 + K1 * s ^ 5) *
      (C * s ^ 2 + C * s ^ 3 + C * s ^ 4 + K2 * s ^ 5) ≤ (2 * B + K1) * (3 * C + K2) * s ^ 5 := by
    calc (B * s ^ 3 + B * s ^ 4 + K1 * s ^ 5) * (C * s ^ 2 + C * s ^ 3 + C * s ^ 4 + K2 * s ^ 5)
        ≤ ((2 * B + K1) * s ^ 3) * ((3 * C + K2) * s ^ 2) :=
          mul_le_mul k2a k2b (by positivity) (by positivity)
      _ = (2 * B + K1) * (3 * C + K2) * s ^ 5 := by ring
  have hR' : |R| ≤ K1 * s ^ 5 := hR
  have tri := abs_add_le (R + a2 * h ^ 2 * (-(z3 * h ^ 3) + y4 * h ^ 4 + r5))
    ((a3 * h ^ 3 + a4 * h ^ 4 + R) * (-(z2 * h ^ 2) - z3 * h ^ 3 + y4 * h ^ 4 + r5))
  have tri2 := abs_add_le R (a2 * h ^ 2 * (-(z3 * h ^ 3) + y4 * h ^ 4 + r5))
  calc _ ≤ |R| + |a2 * h ^ 2 * (-(z3 * h ^ 3) + y4 * h ^ 4 + r5)| +
        |(a3 * h ^ 3 + a4 * h ^ 4 + R) * (-(z2 * h ^ 2) - z3 * h ^ 3 + y4 * h ^ 4 + r5)| :=
        tri.trans (by linarith only [tri2])
    _ ≤ K1 * s ^ 5 + B * (2 * C + K2) * s ^ 5 + (2 * B + K1) * (3 * C + K2) * s ^ 5 :=
        add_le_add (add_le_add hR' (hT1.trans k1)) (hT2.trans k2)
    _ = _ := by ring

/-- Coefficient of `h⁰` in `(a + h c)² · expPoly` (pointwise scalars). -/
noncomputable def fk0_STR02945 (a _c _v _q : ℝ) : ℝ := a ^ 2

/-- Coefficient of `h¹` in `(a + h c)² · expPoly`. -/
noncomputable def fk1_STR02945 (a c v _q : ℝ) : ℝ := a ^ 2 * v + 2 * a * c

/-- Coefficient of `h²` in `(a + h c)² · expPoly`. -/
noncomputable def fk2_STR02945 (a c v q : ℝ) : ℝ := a ^ 2 * (q + v ^ 2 / 2) + 2 * a * c * v + c ^ 2

/-- The tail `k₃ + h k₄ + h² k₅ + h³ k₆` of `(a + h c)² · expPoly`. -/
noncomputable def ftail_STR02945 (a c v q h : ℝ) : ℝ :=
  (a ^ 2 * (v * q + v ^ 3 / 6) + 2 * a * c * (q + v ^ 2 / 2) + c ^ 2 * v) +
    h * (a ^ 2 * (q ^ 2 / 2 + v ^ 2 * q / 2 + v ^ 4 / 24) + 2 * a * c * (v * q + v ^ 3 / 6) +
      c ^ 2 * (q + v ^ 2 / 2)) +
    h ^ 2 * (2 * a * c * (q ^ 2 / 2 + v ^ 2 * q / 2 + v ^ 4 / 24) + c ^ 2 * (v * q + v ^ 3 / 6)) +
    h ^ 3 * (c ^ 2 * (q ^ 2 / 2 + v ^ 2 * q / 2 + v ^ 4 / 24))

theorem fisher_poly_id_STR02945 (a c v q h : ℝ) :
    (a + h * c) ^ 2 * (1 + h * v + h ^ 2 * (q + v ^ 2 / 2) + h ^ 3 * (v * q + v ^ 3 / 6) +
      h ^ 4 * (q ^ 2 / 2 + v ^ 2 * q / 2 + v ^ 4 / 24)) =
    1 * fk0_STR02945 a c v q + h * fk1_STR02945 a c v q + h ^ 2 * fk2_STR02945 a c v q +
      h ^ 3 * ftail_STR02945 a c v q h := by
  unfold fk0_STR02945 fk1_STR02945 fk2_STR02945 ftail_STR02945; ring

theorem abs_split4_STR02945 {x0 x1 x2 x3 K : ℝ}
    (h : |(|x0| + |x1| + |x2| + |x3|)| ≤ K) :
    |x0| ≤ K ∧ |x1| ≤ K ∧ |x2| ≤ K ∧ |x3| ≤ K := by
  have h1 := (le_abs_self _).trans h
  have n0 := abs_nonneg x0
  have n1 := abs_nonneg x1
  have n2 := abs_nonneg x2
  have n3 := abs_nonneg x3
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem fisher_generic_STR02945 (M : ℝ) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ v q a c : ℝ → ℝ, IsAdmissible_STR02944 M v → IsAdmissible_STR02944 M q →
        Continuous a → Continuous c → (∀ t, |a t| ≤ M) → (∀ t, |c t| ≤ M) →
        ∀ h : ℝ, |h| ≤ h0 →
          |normInt_STR02933 (fun t => (h * a t + h ^ 2 * c t) ^ 2 *
              Real.exp (expArg_STR02944 v q h t)) / normalizer_STR02944 v q h -
            (normInt_STR02933 (fun t => fk0_STR02945 (a t) (c t) (v t) (q t)) * h ^ 2 +
              normInt_STR02933 (fun t => fk1_STR02945 (a t) (c t) (v t) (q t)) * h ^ 3 +
              (normInt_STR02933 (fun t => fk2_STR02945 (a t) (c t) (v t) (q t)) -
                normInt_STR02933 (fun t => fk0_STR02945 (a t) (c t) (v t) (q t)) *
                  z2_STR02944 v q) * h ^ 4)| ≤ K * |h| ^ 5 := by
  obtain ⟨h0', hpos, C, hC, hT⟩ := str029_44_uniform_exponential_normalizer_expansions M
  obtain ⟨K0, hK0, hbd⟩ := bound5_STR02945 (max M 1)
    (fun x0 x1 x2 x3 x4 => |fk0_STR02945 x0 x1 x2 x3| + |fk1_STR02945 x0 x1 x2 x3| +
      |fk2_STR02945 x0 x1 x2 x3| + |ftail_STR02945 x0 x1 x2 x3 x4|)
    (by unfold fk0_STR02945 fk1_STR02945 fk2_STR02945 ftail_STR02945; fun_prop)
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, K1 = 4 * (max M 1) ^ 2 * C + K0 := ⟨_, rfl⟩
  have hK1' : 0 ≤ K1 := by rw [hK1]; positivity
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = C ^ 2 + C := ⟨_, rfl⟩
  have hCm' : 0 ≤ Cm := by rw [hCm]; positivity
  refine ⟨min h0' 1, lt_min hpos one_pos,
    K1 + K0 * (2 * Cm + C) + (2 * K0 + K1) * (3 * Cm + C), by positivity, ?_⟩
  intro v q a c hv hq hac hcc hab hcb h hh
  have hh1 : |h| ≤ 1 := hh.trans (min_le_right _ _)
  have hh0 : |h| ≤ h0' := hh.trans (min_le_left _ _)
  obtain ⟨hexp, hZ5, -, -, hinv, -, hz2, hz3, hz4⟩ := hT v q hv hq h hh0
  obtain ⟨hvc, -, hvb⟩ := admissible_bounds_STR02944 hv
  obtain ⟨hqc, -, hqb⟩ := admissible_bounds_STR02944 hq
  have hN1 : (1 : ℝ) ≤ max M 1 := le_max_right _ _
  have hEc : Continuous (fun t => Real.exp (expArg_STR02944 v q h t)) := by
    unfold expArg_STR02944; fun_prop
  have hkb : ∀ t, |fk0_STR02945 (a t) (c t) (v t) (q t)| ≤ K0 ∧
      |fk1_STR02945 (a t) (c t) (v t) (q t)| ≤ K0 ∧
      |fk2_STR02945 (a t) (c t) (v t) (q t)| ≤ K0 ∧
      |ftail_STR02945 (a t) (c t) (v t) (q t) h| ≤ K0 := fun t =>
    abs_split4_STR02945 (hbd _ _ _ _ _ ((hab t).trans (le_max_left _ _))
      ((hcb t).trans (le_max_left _ _))
      ((hvb t).trans (max_le_max le_rfl zero_le_one)) ((hqb t).trans (max_le_max le_rfl zero_le_one))
      (hh1.trans hN1))
  have hc0 : Continuous (fun t => fk0_STR02945 (a t) (c t) (v t) (q t)) := by
    unfold fk0_STR02945; fun_prop
  have hc1 : Continuous (fun t => fk1_STR02945 (a t) (c t) (v t) (q t)) := by
    unfold fk1_STR02945; fun_prop
  have hc2 : Continuous (fun t => fk2_STR02945 (a t) (c t) (v t) (q t)) := by
    unfold fk2_STR02945; fun_prop
  have hb0 : |normInt_STR02933 (fun t => fk0_STR02945 (a t) (c t) (v t) (q t))| ≤ K0 :=
    abs_normInt_le_STR02944 (fun t => (hkb t).1)
  have hb1 : |normInt_STR02933 (fun t => fk1_STR02945 (a t) (c t) (v t) (q t))| ≤ K0 :=
    abs_normInt_le_STR02944 (fun t => (hkb t).2.1)
  have hb2 : |normInt_STR02933 (fun t => fk2_STR02945 (a t) (c t) (v t) (q t))| ≤ K0 :=
    abs_normInt_le_STR02944 (fun t => (hkb t).2.2.1)
  -- the integral of `(a + h c)² E`
  have hDc : Continuous (fun t => (a t + h * c t) ^ 2 * Real.exp (expArg_STR02944 v q h t)) := by
    fun_prop
  have hlin := normInt_lin3_STR02945 1 h (h ^ 2) hc0 hc1 hc2
  rw [one_mul] at hlin
  have hGc : Continuous (fun t => 1 * fk0_STR02945 (a t) (c t) (v t) (q t) +
      h * fk1_STR02945 (a t) (c t) (v t) (q t) + h ^ 2 * fk2_STR02945 (a t) (c t) (v t) (q t)) := by
    fun_prop
  have hpt : ∀ t, |(a t + h * c t) ^ 2 * Real.exp (expArg_STR02944 v q h t) -
      (1 * fk0_STR02945 (a t) (c t) (v t) (q t) + h * fk1_STR02945 (a t) (c t) (v t) (q t) +
        h ^ 2 * fk2_STR02945 (a t) (c t) (v t) (q t))| ≤ K1 * |h| ^ 3 := by
    intro t
    have hid := fisher_poly_id_STR02945 (a t) (c t) (v t) (q t) h
    have hexp' := hexp t
    have htail : |ftail_STR02945 (a t) (c t) (v t) (q t) h| ≤ K0 := (hkb t).2.2.2
    have hat : |a t + h * c t| ≤ 2 * max M 1 := by
      have h1 : |a t| ≤ max M 1 := (hab t).trans (le_max_left _ _)
      have h2 : |h * c t| ≤ max M 1 := by
        rw [abs_mul]
        calc |h| * |c t| ≤ 1 * max M 1 :=
              mul_le_mul hh1 ((hcb t).trans (le_max_left _ _)) (abs_nonneg _) zero_le_one
          _ = max M 1 := one_mul _
      linarith [abs_add_le (a t) (h * c t)]
    have hdiff : (a t + h * c t) ^ 2 * Real.exp (expArg_STR02944 v q h t) -
        (1 * fk0_STR02945 (a t) (c t) (v t) (q t) + h * fk1_STR02945 (a t) (c t) (v t) (q t) +
          h ^ 2 * fk2_STR02945 (a t) (c t) (v t) (q t)) =
        (a t + h * c t) ^ 2 * (Real.exp (expArg_STR02944 v q h t) - expPoly_STR02944 v q h t) +
          h ^ 3 * ftail_STR02945 (a t) (c t) (v t) (q t) h := by
      have : expPoly_STR02944 v q h t = 1 + h * v t + h ^ 2 * (q t + v t ^ 2 / 2) +
          h ^ 3 * (v t * q t + v t ^ 3 / 6) +
          h ^ 4 * (q t ^ 2 / 2 + v t ^ 2 * q t / 2 + v t ^ 4 / 24) := rfl
      rw [this]
      linear_combination hid
    rw [hdiff]
    have hs0 : 0 ≤ |h| := abs_nonneg h
    have h53 : |h| ^ 5 ≤ |h| ^ 3 := pow_le_pow_of_le_one hs0 hh1 (by norm_num)
    have e1 : |(a t + h * c t) ^ 2 * (Real.exp (expArg_STR02944 v q h t) -
        expPoly_STR02944 v q h t)| ≤ 4 * (max M 1) ^ 2 * C * |h| ^ 3 := by
      rw [abs_mul, abs_pow]
      calc |a t + h * c t| ^ 2 * |Real.exp (expArg_STR02944 v q h t) - expPoly_STR02944 v q h t|
          ≤ (2 * max M 1) ^ 2 * (C * |h| ^ 5) :=
            mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hat 2) hexp' (abs_nonneg _) (by positivity)
        _ ≤ (2 * max M 1) ^ 2 * (C * |h| ^ 3) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h53 hC) (by positivity)
        _ = 4 * (max M 1) ^ 2 * C * |h| ^ 3 := by ring
    have e2 : |h ^ 3 * ftail_STR02945 (a t) (c t) (v t) (q t) h| ≤ K0 * |h| ^ 3 := by
      rw [abs_mul, abs_pow]
      calc |h| ^ 3 * |ftail_STR02945 (a t) (c t) (v t) (q t) h| ≤ |h| ^ 3 * K0 :=
            mul_le_mul_of_nonneg_left htail (by positivity)
        _ = K0 * |h| ^ 3 := by ring
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ 4 * (max M 1) ^ 2 * C * |h| ^ 3 + K0 * |h| ^ 3 := add_le_add e1 e2
      _ = K1 * |h| ^ 3 := by rw [hK1]; ring
  have hD : |normInt_STR02933 (fun t => (a t + h * c t) ^ 2 * Real.exp (expArg_STR02944 v q h t)) -
      (normInt_STR02933 (fun t => fk0_STR02945 (a t) (c t) (v t) (q t)) +
        h * normInt_STR02933 (fun t => fk1_STR02945 (a t) (c t) (v t) (q t)) +
        h ^ 2 * normInt_STR02933 (fun t => fk2_STR02945 (a t) (c t) (v t) (q t)))| ≤
      K1 * |h| ^ 3 := by
    rw [← hlin, ← normInt_sub_STR02944 hDc hGc]
    exact abs_normInt_le_STR02944 hpt
  have hNumEq : normInt_STR02933 (fun t => (h * a t + h ^ 2 * c t) ^ 2 *
      Real.exp (expArg_STR02944 v q h t)) =
      h ^ 2 * normInt_STR02933 (fun t => (a t + h * c t) ^ 2 * Real.exp (expArg_STR02944 v q h t)) := by
    rw [← normInt_mul_const_STR02933]
    exact normInt_congr_STR02945 (fun t => by ring)
  have hy4 : |z2_STR02944 v q ^ 2 - z4_STR02944 v q| ≤ Cm := by
    have e1 : |z2_STR02944 v q ^ 2| ≤ C ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hz2 2
    calc |z2_STR02944 v q ^ 2 - z4_STR02944 v q| ≤ |z2_STR02944 v q ^ 2| + |z4_STR02944 v q| :=
          abs_sub _ _
      _ ≤ C ^ 2 + C := add_le_add e1 hz4
      _ = Cm := hCm.symm
  have hRb : |h ^ 2 * (normInt_STR02933 (fun t => (a t + h * c t) ^ 2 * Real.exp (expArg_STR02944 v q h t)) -
      (normInt_STR02933 (fun t => fk0_STR02945 (a t) (c t) (v t) (q t)) +
        h * normInt_STR02933 (fun t => fk1_STR02945 (a t) (c t) (v t) (q t)) +
        h ^ 2 * normInt_STR02933 (fun t => fk2_STR02945 (a t) (c t) (v t) (q t))))| ≤
      K1 * |h| ^ 5 := by
    rw [abs_mul, abs_pow]
    calc |h| ^ 2 * |_| ≤ |h| ^ 2 * (K1 * |h| ^ 3) :=
          mul_le_mul_of_nonneg_left hD (by positivity)
      _ = K1 * |h| ^ 5 := by ring
  rw [div_eq_mul_inv, hNumEq]
  exact assemble_STR02945 (h := h) hh1 hK0 hCm' hK1' hC (by ring) hRb hb0 hb1 hb2
    (r5 := (normalizer_STR02944 v q h)⁻¹ - (1 - z2_STR02944 v q * h ^ 2 - z3_STR02944 v q * h ^ 3 +
      (z2_STR02944 v q ^ 2 - z4_STR02944 v q) * h ^ 4)) (by ring) hinv
    (hz2.trans (by nlinarith [sq_nonneg C])) (hz3.trans (by nlinarith [sq_nonneg C])) hy4

/-- Coefficient of `h²` in `(h p + h² q) · expPoly`. -/
noncomputable def ek2_STR02945 (p q v : ℝ) : ℝ := p * v + q

/-- Coefficient of `h³` in `(h p + h² q) · expPoly`. -/
noncomputable def ek3_STR02945 (p q v : ℝ) : ℝ := p * (q + v ^ 2 / 2) + q * v

/-- Coefficient of `h⁴` in `(h p + h² q) · expPoly`. -/
noncomputable def ek4_STR02945 (p q v : ℝ) : ℝ := p * (v * q + v ^ 3 / 6) + q * (q + v ^ 2 / 2)

/-- The tail `k₅ + h k₆` of `(h p + h² q) · expPoly`. -/
noncomputable def etail_STR02945 (p q v h : ℝ) : ℝ :=
  (p * (q ^ 2 / 2 + v ^ 2 * q / 2 + v ^ 4 / 24) + q * (v * q + v ^ 3 / 6)) +
    h * (q * (q ^ 2 / 2 + v ^ 2 * q / 2 + v ^ 4 / 24))

theorem entropy_poly_id_STR02945 (p q v h : ℝ) :
    (h * p + h ^ 2 * q) * (1 + h * v + h ^ 2 * (q + v ^ 2 / 2) + h ^ 3 * (v * q + v ^ 3 / 6) +
      h ^ 4 * (q ^ 2 / 2 + v ^ 2 * q / 2 + v ^ 4 / 24)) =
    h * p + h ^ 2 * ek2_STR02945 p q v + h ^ 3 * ek3_STR02945 p q v +
      h ^ 4 * ek4_STR02945 p q v + h ^ 5 * etail_STR02945 p q v h := by
  unfold ek2_STR02945 ek3_STR02945 ek4_STR02945 etail_STR02945; ring

theorem entropy_generic_STR02945 (M : ℝ) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ v p q : ℝ → ℝ, IsAdmissible_STR02944 M v → IsAdmissible_STR02944 M p →
        IsAdmissible_STR02944 M q → ∀ h : ℝ, |h| ≤ h0 →
          |normInt_STR02933 (fun t => (h * p t + h ^ 2 * q t) *
              Real.exp (expArg_STR02944 v q h t)) / normalizer_STR02944 v q h -
            (normInt_STR02933 (fun t => ek2_STR02945 (p t) (q t) (v t)) * h ^ 2 +
              normInt_STR02933 (fun t => ek3_STR02945 (p t) (q t) (v t)) * h ^ 3 +
              (normInt_STR02933 (fun t => ek4_STR02945 (p t) (q t) (v t)) -
                normInt_STR02933 (fun t => ek2_STR02945 (p t) (q t) (v t)) *
                  z2_STR02944 v q) * h ^ 4)| ≤ K * |h| ^ 5 := by
  obtain ⟨h0', hpos, C, hC, hT⟩ := str029_44_uniform_exponential_normalizer_expansions M
  obtain ⟨K0, hK0, hbd⟩ := bound5_STR02945 (max M 1)
    (fun x0 x1 x2 x3 _ => |ek2_STR02945 x0 x1 x2| + |ek3_STR02945 x0 x1 x2| +
      |ek4_STR02945 x0 x1 x2| + |etail_STR02945 x0 x1 x2 x3|)
    (by unfold ek2_STR02945 ek3_STR02945 ek4_STR02945 etail_STR02945; fun_prop)
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, K1 = 2 * max M 1 * C + K0 := ⟨_, rfl⟩
  have hK1' : 0 ≤ K1 := by rw [hK1]; positivity
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = C ^ 2 + C := ⟨_, rfl⟩
  have hCm' : 0 ≤ Cm := by rw [hCm]; positivity
  refine ⟨min h0' 1, lt_min hpos one_pos,
    K1 + K0 * (2 * Cm + C) + (2 * K0 + K1) * (3 * Cm + C), by positivity, ?_⟩
  intro v p q hv hp hq h hh
  have hh1 : |h| ≤ 1 := hh.trans (min_le_right _ _)
  have hh0 : |h| ≤ h0' := hh.trans (min_le_left _ _)
  obtain ⟨hexp, hZ5, -, -, hinv, -, hz2, hz3, hz4⟩ := hT v q hv hq h hh0
  obtain ⟨hvc, -, hvb⟩ := admissible_bounds_STR02944 hv
  obtain ⟨hpc, hp0, hpb⟩ := admissible_bounds_STR02944 hp
  obtain ⟨hqc, -, hqb⟩ := admissible_bounds_STR02944 hq
  have hN1 : (1 : ℝ) ≤ max M 1 := le_max_right _ _
  have hMN : M ≤ max M 1 := le_max_left _ _
  have hM0 : max M 0 ≤ max M 1 := max_le_max le_rfl zero_le_one
  have hEc : Continuous (fun t => Real.exp (expArg_STR02944 v q h t)) := by
    unfold expArg_STR02944; fun_prop
  have hkb : ∀ t, |ek2_STR02945 (p t) (q t) (v t)| ≤ K0 ∧
      |ek3_STR02945 (p t) (q t) (v t)| ≤ K0 ∧
      |ek4_STR02945 (p t) (q t) (v t)| ≤ K0 ∧
      |etail_STR02945 (p t) (q t) (v t) h| ≤ K0 := fun t =>
    abs_split4_STR02945 (hbd _ _ _ _ _ ((hpb t).trans hM0) ((hqb t).trans hM0)
      ((hvb t).trans hM0) (hh1.trans hN1) (hh1.trans hN1))
  have hc2 : Continuous (fun t => ek2_STR02945 (p t) (q t) (v t)) := by
    unfold ek2_STR02945; fun_prop
  have hc3 : Continuous (fun t => ek3_STR02945 (p t) (q t) (v t)) := by
    unfold ek3_STR02945; fun_prop
  have hc4 : Continuous (fun t => ek4_STR02945 (p t) (q t) (v t)) := by
    unfold ek4_STR02945; fun_prop
  have hb2 : |normInt_STR02933 (fun t => ek2_STR02945 (p t) (q t) (v t))| ≤ K0 :=
    abs_normInt_le_STR02944 (fun t => (hkb t).1)
  have hb3 : |normInt_STR02933 (fun t => ek3_STR02945 (p t) (q t) (v t))| ≤ K0 :=
    abs_normInt_le_STR02944 (fun t => (hkb t).2.1)
  have hb4 : |normInt_STR02933 (fun t => ek4_STR02945 (p t) (q t) (v t))| ≤ K0 :=
    abs_normInt_le_STR02944 (fun t => (hkb t).2.2.1)
  have hFc : Continuous (fun t => (h * p t + h ^ 2 * q t) * Real.exp (expArg_STR02944 v q h t)) := by
    fun_prop
  have hlin := normInt_lin4_STR02945 h (h ^ 2) (h ^ 3) (h ^ 4) hpc hc2 hc3 hc4
  rw [hp0, mul_zero, zero_add] at hlin
  have hGc : Continuous (fun t => h * p t + h ^ 2 * ek2_STR02945 (p t) (q t) (v t) +
      h ^ 3 * ek3_STR02945 (p t) (q t) (v t) + h ^ 4 * ek4_STR02945 (p t) (q t) (v t)) := by
    fun_prop
  have hpt : ∀ t, |(h * p t + h ^ 2 * q t) * Real.exp (expArg_STR02944 v q h t) -
      (h * p t + h ^ 2 * ek2_STR02945 (p t) (q t) (v t) +
        h ^ 3 * ek3_STR02945 (p t) (q t) (v t) + h ^ 4 * ek4_STR02945 (p t) (q t) (v t))| ≤
      K1 * |h| ^ 5 := by
    intro t
    have hid := entropy_poly_id_STR02945 (p t) (q t) (v t) h
    have hexp' := hexp t
    have htail : |etail_STR02945 (p t) (q t) (v t) h| ≤ K0 := (hkb t).2.2.2
    have hat : |h * p t + h ^ 2 * q t| ≤ 2 * max M 1 * |h| := by
      have h1 : |h * p t| ≤ max M 1 * |h| := by
        rw [abs_mul]
        calc |h| * |p t| ≤ |h| * max M 1 :=
              mul_le_mul_of_nonneg_left ((hpb t).trans hM0) (abs_nonneg _)
          _ = max M 1 * |h| := mul_comm _ _
      have h2 : |h ^ 2 * q t| ≤ max M 1 * |h| := by
        rw [abs_mul, abs_pow]
        calc |h| ^ 2 * |q t| ≤ |h| ^ 2 * max M 1 :=
              mul_le_mul_of_nonneg_left ((hqb t).trans hM0) (by positivity)
          _ ≤ |h| * max M 1 := by
              have : |h| ^ 2 ≤ |h| := pow_le_of_le_one (abs_nonneg h) hh1 two_ne_zero
              exact mul_le_mul_of_nonneg_right this (by linarith only [hN1])
          _ = max M 1 * |h| := mul_comm _ _
      linarith only [abs_add_le (h * p t) (h ^ 2 * q t), h1, h2]
    have hdiff : (h * p t + h ^ 2 * q t) * Real.exp (expArg_STR02944 v q h t) -
        (h * p t + h ^ 2 * ek2_STR02945 (p t) (q t) (v t) +
          h ^ 3 * ek3_STR02945 (p t) (q t) (v t) + h ^ 4 * ek4_STR02945 (p t) (q t) (v t)) =
        (h * p t + h ^ 2 * q t) * (Real.exp (expArg_STR02944 v q h t) - expPoly_STR02944 v q h t) +
          h ^ 5 * etail_STR02945 (p t) (q t) (v t) h := by
      have : expPoly_STR02944 v q h t = 1 + h * v t + h ^ 2 * (q t + v t ^ 2 / 2) +
          h ^ 3 * (v t * q t + v t ^ 3 / 6) +
          h ^ 4 * (q t ^ 2 / 2 + v t ^ 2 * q t / 2 + v t ^ 4 / 24) := rfl
      rw [this]
      linear_combination hid
    rw [hdiff]
    have hs0 : 0 ≤ |h| := abs_nonneg h
    have e1 : |(h * p t + h ^ 2 * q t) * (Real.exp (expArg_STR02944 v q h t) -
        expPoly_STR02944 v q h t)| ≤ 2 * max M 1 * C * |h| ^ 5 := by
      rw [abs_mul]
      have h65 : |h| * |h| ^ 5 ≤ |h| ^ 5 := mul_le_of_le_one_left (by positivity) hh1
      calc |h * p t + h ^ 2 * q t| * |Real.exp (expArg_STR02944 v q h t) - expPoly_STR02944 v q h t|
          ≤ (2 * max M 1 * |h|) * (C * |h| ^ 5) :=
            mul_le_mul hat hexp' (abs_nonneg _) (by positivity)
        _ = 2 * max M 1 * C * (|h| * |h| ^ 5) := by ring
        _ ≤ 2 * max M 1 * C * |h| ^ 5 :=
            mul_le_mul_of_nonneg_left h65 (by positivity)
    have e2 : |h ^ 5 * etail_STR02945 (p t) (q t) (v t) h| ≤ K0 * |h| ^ 5 := by
      rw [abs_mul, abs_pow]
      calc |h| ^ 5 * |etail_STR02945 (p t) (q t) (v t) h| ≤ |h| ^ 5 * K0 :=
            mul_le_mul_of_nonneg_left htail (by positivity)
        _ = K0 * |h| ^ 5 := by ring
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ 2 * max M 1 * C * |h| ^ 5 + K0 * |h| ^ 5 := add_le_add e1 e2
      _ = K1 * |h| ^ 5 := by rw [hK1]; ring
  have hR : |normInt_STR02933 (fun t => (h * p t + h ^ 2 * q t) *
        Real.exp (expArg_STR02944 v q h t)) -
      (normInt_STR02933 (fun t => ek2_STR02945 (p t) (q t) (v t)) * h ^ 2 +
        normInt_STR02933 (fun t => ek3_STR02945 (p t) (q t) (v t)) * h ^ 3 +
        normInt_STR02933 (fun t => ek4_STR02945 (p t) (q t) (v t)) * h ^ 4)| ≤
      K1 * |h| ^ 5 := by
    have e : normInt_STR02933 (fun t => (h * p t + h ^ 2 * q t) *
        Real.exp (expArg_STR02944 v q h t)) -
      (normInt_STR02933 (fun t => ek2_STR02945 (p t) (q t) (v t)) * h ^ 2 +
        normInt_STR02933 (fun t => ek3_STR02945 (p t) (q t) (v t)) * h ^ 3 +
        normInt_STR02933 (fun t => ek4_STR02945 (p t) (q t) (v t)) * h ^ 4) =
      normInt_STR02933 (fun t => (h * p t + h ^ 2 * q t) * Real.exp (expArg_STR02944 v q h t)) -
      normInt_STR02933 (fun t => h * p t + h ^ 2 * ek2_STR02945 (p t) (q t) (v t) +
        h ^ 3 * ek3_STR02945 (p t) (q t) (v t) + h ^ 4 * ek4_STR02945 (p t) (q t) (v t)) := by
      rw [hlin]; ring
    rw [e, ← normInt_sub_STR02944 hFc hGc]
    exact abs_normInt_le_STR02944 hpt
  have hy4 : |z2_STR02944 v q ^ 2 - z4_STR02944 v q| ≤ Cm := by
    have e1 : |z2_STR02944 v q ^ 2| ≤ C ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hz2 2
    calc |z2_STR02944 v q ^ 2 - z4_STR02944 v q| ≤ |z2_STR02944 v q ^ 2| + |z4_STR02944 v q| :=
          abs_sub _ _
      _ ≤ C ^ 2 + C := add_le_add e1 hz4
      _ = Cm := hCm.symm
  rw [div_eq_mul_inv]
  exact assemble_STR02945 (h := h) hh1 hK0 hCm' hK1' hC (by ring) hR hb2 hb3 hb4
    (r5 := (normalizer_STR02944 v q h)⁻¹ - (1 - z2_STR02944 v q * h ^ 2 - z3_STR02944 v q * h ^ 3 +
      (z2_STR02944 v q ^ 2 - z4_STR02944 v q) * h ^ 4)) (by ring) hinv
    (hz2.trans (by linarith only [sq_nonneg C, hCm])) (hz3.trans (by linarith only [sq_nonneg C, hCm])) hy4

/-- The `h²` coefficient of the entropy expansion before trigonometric evaluation. -/
noncomputable def entC2_STR02945 (b v p q : ℝ → ℝ) : ℝ :=
  normInt_STR02933 (fun t => ek2_STR02945 (p t) (q t) (v t)) - z2_STR02944 v q +
    z2_STR02944 b (fun _ => 0)

/-- The `h³` coefficient of the entropy expansion before trigonometric evaluation. -/
noncomputable def entC3_STR02945 (b v p q : ℝ → ℝ) : ℝ :=
  normInt_STR02933 (fun t => ek3_STR02945 (p t) (q t) (v t)) - z3_STR02944 v q +
    z3_STR02944 b (fun _ => 0)

/-- The `h⁴` coefficient of the entropy expansion before trigonometric evaluation. -/
noncomputable def entC4_STR02945 (b v p q : ℝ → ℝ) : ℝ :=
  (normInt_STR02933 (fun t => ek4_STR02945 (p t) (q t) (v t)) -
      normInt_STR02933 (fun t => ek2_STR02945 (p t) (q t) (v t)) * z2_STR02944 v q) -
    (z4_STR02944 v q - z2_STR02944 v q ^ 2 / 2) +
    (z4_STR02944 b (fun _ => 0) - z2_STR02944 b (fun _ => 0) ^ 2 / 2)

theorem entropy_full_generic_STR02945 (M : ℝ)
    (hz0 : IsAdmissible_STR02944 M (fun _ : ℝ => (0 : ℝ))) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ b v p q : ℝ → ℝ, IsAdmissible_STR02944 M b → IsAdmissible_STR02944 M v →
        IsAdmissible_STR02944 M p → IsAdmissible_STR02944 M q → ∀ h : ℝ, |h| ≤ h0 →
          |(normInt_STR02933 (fun t => (h * p t + h ^ 2 * q t) *
              Real.exp (expArg_STR02944 v q h t)) / normalizer_STR02944 v q h -
            Real.log (normalizer_STR02944 v q h) +
            Real.log (normalizer_STR02944 b (fun _ => 0) h)) -
            (entC2_STR02945 b v p q * h ^ 2 + entC3_STR02945 b v p q * h ^ 3 +
              entC4_STR02945 b v p q * h ^ 4)| ≤ K * |h| ^ 5 := by
  obtain ⟨hE, hEpos, KE, hKE, hEnt⟩ := entropy_generic_STR02945 M
  obtain ⟨hT, hTpos, C, hC, hTT⟩ := str029_44_uniform_exponential_normalizer_expansions M
  refine ⟨min hE hT, lt_min hEpos hTpos, KE + C + C, by positivity, ?_⟩
  intro b v p q hb hv hp hq h hh
  have hhE : |h| ≤ hE := hh.trans (min_le_left _ _)
  have hhT : |h| ≤ hT := hh.trans (min_le_right _ _)
  have h1 := hEnt v p q hv hp hq h hhE
  obtain ⟨-, -, -, -, -, hlog, -⟩ := hTT v q hv hq h hhT
  obtain ⟨-, -, -, -, -, hlogb, -⟩ := hTT b (fun _ => 0) hb hz0 h hhT
  unfold entC2_STR02945 entC3_STR02945 entC4_STR02945
  have key : ∀ x L Lb Px PL PLb : ℝ, |x - Px| ≤ KE * |h| ^ 5 → |L - PL| ≤ C * |h| ^ 5 →
      |Lb - PLb| ≤ C * |h| ^ 5 → |(x - L + Lb) - (Px - PL + PLb)| ≤ (KE + C + C) * |h| ^ 5 := by
    intro x L Lb Px PL PLb hx hL hLb
    have e : (x - L + Lb) - (Px - PL + PLb) = (x - Px) - (L - PL) + (Lb - PLb) := by ring
    rw [e]
    calc |(x - Px) - (L - PL) + (Lb - PLb)| ≤ |(x - Px) - (L - PL)| + |Lb - PLb| := abs_add_le _ _
      _ ≤ (|x - Px| + |L - PL|) + |Lb - PLb| := by gcongr; exact abs_sub _ _
      _ ≤ (KE * |h| ^ 5 + C * |h| ^ 5) + C * |h| ^ 5 := by gcongr
      _ = (KE + C + C) * |h| ^ 5 := by ring
  have := key _ _ _ _ _ _ h1 hlog hlogb
  convert this using 2
  ring

theorem fisher_n1_STR02945 {a c v q : ℝ → ℝ} (hac : Continuous a) (hcc : Continuous c)
    (hvc : Continuous v)
    (ha : ∀ t, a (t + π) = - a t) (hc : ∀ t, c (t + π) = c t) (hv : ∀ t, v (t + π) = - v t) :
    normInt_STR02933 (fun t => fk1_STR02945 (a t) (c t) (v t) (q t)) = 0 := by
  refine normInt_antiperiodic_STR02945 ?_ (fun t => ?_)
  · unfold fk1_STR02945; fun_prop
  · simp only [fk1_STR02945, ha, hc, hv]; ring

theorem fisher_n2_STR02945 {a c v q : ℝ → ℝ} (hac : Continuous a) (hcc : Continuous c)
    (hvc : Continuous v) (hqc : Continuous q) (hq0 : normInt_STR02933 q = 0) :
    normInt_STR02933 (fun t => fk2_STR02945 (a t) (c t) (v t) (q t)) -
      normInt_STR02933 (fun t => fk0_STR02945 (a t) (c t) (v t) (q t)) * z2_STR02944 v q =
    normInt_STR02933 (fun t => c t ^ 2) +
      2 * normInt_STR02933 (fun t => a t * c t * v t) +
      normInt_STR02933 (fun t => a t ^ 2 * q t) +
      (1 / 2) * normInt_STR02933 (fun t => a t ^ 2 * v t ^ 2) -
      (1 / 2) * normInt_STR02933 (fun t => a t ^ 2) * normInt_STR02933 (fun t => v t ^ 2) := by
  have e2 : normInt_STR02933 (fun t => fk2_STR02945 (a t) (c t) (v t) (q t)) =
      1 * normInt_STR02933 (fun t => a t ^ 2 * q t) +
        (1 / 2) * normInt_STR02933 (fun t => a t ^ 2 * v t ^ 2) +
        2 * normInt_STR02933 (fun t => a t * c t * v t) +
        1 * normInt_STR02933 (fun t => c t ^ 2) := by
    rw [← normInt_lin4_STR02945 (f1 := fun t => a t ^ 2 * q t) (f2 := fun t => a t ^ 2 * v t ^ 2)
      (f3 := fun t => a t * c t * v t) (f4 := fun t => c t ^ 2) 1 (1 / 2) 2 1
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)]
    exact normInt_congr_STR02945 (fun t => by unfold fk2_STR02945; ring)
  have e0 : normInt_STR02933 (fun t => fk0_STR02945 (a t) (c t) (v t) (q t)) =
      normInt_STR02933 (fun t => a t ^ 2) := rfl
  have ez : z2_STR02944 v q = (1 / 2) * normInt_STR02933 (fun t => v t ^ 2) := by
    unfold z2_STR02944
    have := normInt_addmul_STR02945 (g := q) (f := fun t => v t ^ 2) (1 / 2) hqc (by fun_prop)
    rw [hq0, zero_add] at this
    rw [← this]
    exact normInt_congr_STR02945 (fun t => by ring)
  rw [e2, e0, ez]; ring

theorem ent_a2_STR02945 {b p q : ℝ → ℝ} (hbc : Continuous b) (hpc : Continuous p)
    (hqc : Continuous q) (hq0 : normInt_STR02933 q = 0)
    (hpb : normInt_STR02933 (fun t => p t * b t) = 0) :
    normInt_STR02933 (fun t => ek2_STR02945 (p t) (q t) (b t + p t)) =
      normInt_STR02933 (fun t => p t ^ 2) := by
  rw [normInt_congr_STR02945 (g := fun t => 1 * (p t * b t) + 1 * p t ^ 2 + 1 * q t)
    (fun t => by unfold ek2_STR02945; ring),
    normInt_lin3_STR02945 (f1 := fun t => p t * b t) (f2 := fun t => p t ^ 2) (f3 := q)
      1 1 1 (by fun_prop) (by fun_prop) hqc, hpb, hq0]
  ring

theorem ent_z2_STR02945 {b p q : ℝ → ℝ} (hbc : Continuous b) (hpc : Continuous p)
    (hqc : Continuous q) (hq0 : normInt_STR02933 q = 0)
    (hpb : normInt_STR02933 (fun t => p t * b t) = 0) :
    z2_STR02944 (fun t => b t + p t) q =
      (1 / 2) * normInt_STR02933 (fun t => b t ^ 2) +
        (1 / 2) * normInt_STR02933 (fun t => p t ^ 2) := by
  unfold z2_STR02944
  rw [normInt_congr_STR02945
      (g := fun t => 1 * q t + (1 / 2) * b t ^ 2 + 1 * (p t * b t) + (1 / 2) * p t ^ 2)
      (fun t => by ring),
    normInt_lin4_STR02945 (f1 := q) (f2 := fun t => b t ^ 2) (f3 := fun t => p t * b t)
      (f4 := fun t => p t ^ 2) 1 (1 / 2) 1 (1 / 2) hqc (by fun_prop) (by fun_prop) (by fun_prop),
    hpb, hq0]
  ring

theorem ent_zb2_STR02945 {b : ℝ → ℝ} :
    z2_STR02944 b (fun _ => 0) = (1 / 2) * normInt_STR02933 (fun t => b t ^ 2) := by
  unfold z2_STR02944
  rw [← normInt_mul_const_STR02933]
  exact normInt_congr_STR02945 (fun t => by ring)

theorem ent_c2_STR02945 {b p q : ℝ → ℝ} (hbc : Continuous b) (hpc : Continuous p)
    (hqc : Continuous q) (hq0 : normInt_STR02933 q = 0)
    (hpb : normInt_STR02933 (fun t => p t * b t) = 0) :
    entC2_STR02945 b (fun t => b t + p t) p q = (1 / 2) * normInt_STR02933 (fun t => p t ^ 2) := by
  unfold entC2_STR02945
  rw [ent_a2_STR02945 hbc hpc hqc hq0 hpb, ent_z2_STR02945 hbc hpc hqc hq0 hpb,
    ent_zb2_STR02945]
  ring

theorem ent_c3_STR02945 {b p q : ℝ → ℝ} (hbc : Continuous b) (hpc : Continuous p)
    (hqc : Continuous q) (hbA : ∀ t, b (t + π) = - b t) (hpA : ∀ t, p (t + π) = - p t)
    (hqS : ∀ t, q (t + π) = q t) :
    entC3_STR02945 b (fun t => b t + p t) p q = 0 := by
  unfold entC3_STR02945 z3_STR02944
  rw [normInt_antiperiodic_STR02945 (f := fun t => ek3_STR02945 (p t) (q t) (b t + p t))
      (by unfold ek3_STR02945; fun_prop) (fun t => by simp only [ek3_STR02945, hbA, hpA, hqS]; ring),
    normInt_antiperiodic_STR02945
      (f := fun t => (b t + p t) * q t + (b t + p t) ^ 3 / 6)
      (by fun_prop) (fun t => by simp only [hbA, hpA, hqS]; ring),
    normInt_antiperiodic_STR02945 (f := fun t => b t * (fun _ : ℝ => (0 : ℝ)) t + b t ^ 3 / 6)
      (by fun_prop) (fun t => by simp only [hbA]; ring)]
  ring

theorem ent_c4_STR02945 {b p q : ℝ → ℝ} (hbc : Continuous b) (hpc : Continuous p)
    (hqc : Continuous q) (hq0 : normInt_STR02933 q = 0)
    (hpb : normInt_STR02933 (fun t => p t * b t) = 0) :
    entC4_STR02945 b (fun t => b t + p t) p q =
      (1 / 2) * normInt_STR02933 (fun t => q t ^ 2) +
        normInt_STR02933 (fun t => p t * b t * q t) +
        normInt_STR02933 (fun t => p t ^ 2 * q t) +
        (1 / 4) * (normInt_STR02933 (fun t => p t ^ 2 * b t ^ 2) -
          normInt_STR02933 (fun t => p t ^ 2) * normInt_STR02933 (fun t => b t ^ 2)) +
        (1 / 3) * normInt_STR02933 (fun t => p t ^ 3 * b t) +
        (1 / 8) * normInt_STR02933 (fun t => p t ^ 4) -
        (3 / 8) * normInt_STR02933 (fun t => p t ^ 2) ^ 2 := by
  have hF : normInt_STR02933 (fun t => ek4_STR02945 (p t) (q t) (b t + p t)) -
      normInt_STR02933 (fun t => q t ^ 2 / 2 + (b t + p t) ^ 2 * q t / 2 + (b t + p t) ^ 4 / 24) +
      normInt_STR02933 (fun t => (0 : ℝ) ^ 2 / 2 + b t ^ 2 * 0 / 2 + b t ^ 4 / 24) =
      (1 / 2) * normInt_STR02933 (fun t => q t ^ 2) +
        1 * normInt_STR02933 (fun t => p t * b t * q t) +
        1 * normInt_STR02933 (fun t => p t ^ 2 * q t) +
        (1 / 4) * normInt_STR02933 (fun t => p t ^ 2 * b t ^ 2) +
        (1 / 3) * normInt_STR02933 (fun t => p t ^ 3 * b t) +
        (1 / 8) * normInt_STR02933 (fun t => p t ^ 4) := by
    have h1 := normInt_lin3_STR02945
      (f1 := fun t => ek4_STR02945 (p t) (q t) (b t + p t))
      (f2 := fun t => q t ^ 2 / 2 + (b t + p t) ^ 2 * q t / 2 + (b t + p t) ^ 4 / 24)
      (f3 := fun t => (0 : ℝ) ^ 2 / 2 + b t ^ 2 * 0 / 2 + b t ^ 4 / 24) 1 (-1) 1
      (by unfold ek4_STR02945; fun_prop) (by fun_prop) (by fun_prop)
    have h2 := normInt_lin6_STR02945 (f1 := fun t => q t ^ 2) (f2 := fun t => p t * b t * q t)
      (f3 := fun t => p t ^ 2 * q t) (f4 := fun t => p t ^ 2 * b t ^ 2)
      (f5 := fun t => p t ^ 3 * b t) (f6 := fun t => p t ^ 4) (1 / 2) 1 1 (1 / 4) (1 / 3) (1 / 8)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    have h3 := normInt_congr_STR02945
      (f := fun t => 1 * ek4_STR02945 (p t) (q t) (b t + p t) +
        (-1) * (q t ^ 2 / 2 + (b t + p t) ^ 2 * q t / 2 + (b t + p t) ^ 4 / 24) +
        1 * ((0 : ℝ) ^ 2 / 2 + b t ^ 2 * 0 / 2 + b t ^ 4 / 24))
      (g := fun t => (1 / 2) * q t ^ 2 + 1 * (p t * b t * q t) + 1 * (p t ^ 2 * q t) +
        (1 / 4) * (p t ^ 2 * b t ^ 2) + (1 / 3) * (p t ^ 3 * b t) + (1 / 8) * p t ^ 4)
      (fun t => by unfold ek4_STR02945; ring)
    linarith only [h1, h2, h3]
  have ea2 := ent_a2_STR02945 hbc hpc hqc hq0 hpb
  have ez2 := ent_z2_STR02945 hbc hpc hqc hq0 hpb
  have ezb2 := ent_zb2_STR02945 (b := b)
  have e4 : z4_STR02944 (fun t => b t + p t) q =
      normInt_STR02933 (fun t => q t ^ 2 / 2 + (b t + p t) ^ 2 * q t / 2 + (b t + p t) ^ 4 / 24) :=
    rfl
  have eb4 : z4_STR02944 b (fun _ => 0) =
      normInt_STR02933 (fun t => (0 : ℝ) ^ 2 / 2 + b t ^ 2 * 0 / 2 + b t ^ 4 / 24) := rfl
  unfold entC4_STR02945
  rw [ea2, ez2, ezb2, e4, eb4]
  linear_combination hF

theorem pb_mode_STR02945 (A B : ℝ) :
    (fun t => pFun_STR02945 A B t * bFun_STR02945 t) =
      mode2_STR02945 (A / 2) (-(B / 2)) 2 (A / 2) (B / 2) 4 := by
  funext t
  have h4 : Real.cos (4 * t) = Real.cos (3 * t) * Real.cos t - Real.sin (3 * t) * Real.sin t := by
    rw [← Real.cos_add]; ring_nf
  have h2 : Real.cos (2 * t) = Real.cos (3 * t) * Real.cos t + Real.sin (3 * t) * Real.sin t := by
    rw [← Real.cos_sub]; ring_nf
  have s4 : Real.sin (4 * t) = Real.sin (3 * t) * Real.cos t + Real.cos (3 * t) * Real.sin t := by
    rw [← Real.sin_add]; ring_nf
  have s2 : Real.sin (2 * t) = Real.sin (3 * t) * Real.cos t - Real.cos (3 * t) * Real.sin t := by
    rw [← Real.sin_sub]; ring_nf
  simp only [pFun_STR02945, bFun_STR02945, mode2_STR02945, mode1_STR02945, Nat.cast_ofNat]
  rw [h4, h2, s4, s2]; ring

theorem normInt_pFun_mul_bFun_STR02945 (A B : ℝ) :
    normInt_STR02933 (fun t => pFun_STR02945 A B t * bFun_STR02945 t) = 0 :=
  (congrArg normInt_STR02933 (pb_mode_STR02945 A B)).trans
    (normInt_mode2_STR02945 _ _ _ _ (by norm_num) (by norm_num))

theorem pFun_shift_STR02945 (A B t : ℝ) :
    pFun_STR02945 A B (t + π) = - pFun_STR02945 A B t := by
  rw [pFun_eq_STR02945]
  exact mode2_shift_odd_STR02945 _ _ _ _ (by decide) (by decide) t

theorem bFun_shift_STR02945 (t : ℝ) : bFun_STR02945 (t + π) = - bFun_STR02945 t := by
  rw [bFun_eq_STR02945]
  exact mode2_shift_odd_STR02945 _ _ _ _ (by decide) (by decide) t

theorem vFun_shift_STR02945 (A B t : ℝ) :
    vFun_STR02945 A B (t + π) = - vFun_STR02945 A B t := by
  rw [vFun_eq_STR02945]
  exact mode2_shift_odd_STR02945 _ _ _ _ (by decide) (by decide) t

theorem qFun_shift_STR02945 (C D E F t : ℝ) :
    qFun_STR02945 C D E F (t + π) = qFun_STR02945 C D E F t := by
  rw [qFun_eq_STR02945]
  exact mode2_shift_even_STR02945 _ _ _ _ (by decide) (by decide) t

theorem deriv_pFun_shift_STR02945 (A B t : ℝ) :
    deriv (pFun_STR02945 A B) (t + π) = - deriv (pFun_STR02945 A B) t := by
  rw [deriv_pFun_STR02945]
  exact mode2_shift_odd_STR02945 _ _ _ _ (by decide) (by decide) t

theorem deriv_qFun_shift_STR02945 (C D E F t : ℝ) :
    deriv (qFun_STR02945 C D E F) (t + π) = deriv (qFun_STR02945 C D E F) t := by
  rw [deriv_qFun_STR02945]
  exact mode2_shift_even_STR02945 _ _ _ _ (by decide) (by decide) t

theorem pFun_cont_STR02945 (A B : ℝ) : Continuous (pFun_STR02945 A B) := by
  rw [pFun_eq_STR02945]; exact mode2_cont_STR02945 _ _ _ _ _ _

theorem qFun_cont_STR02945 (C D E F : ℝ) : Continuous (qFun_STR02945 C D E F) := by
  rw [qFun_eq_STR02945]; exact mode2_cont_STR02945 _ _ _ _ _ _

theorem bFun_cont_STR02945 : Continuous bFun_STR02945 := by
  rw [bFun_eq_STR02945]; exact mode2_cont_STR02945 _ _ _ _ _ _

theorem vFun_cont_STR02945 (A B : ℝ) : Continuous (vFun_STR02945 A B) := by
  rw [vFun_eq_STR02945]; exact mode2_cont_STR02945 _ _ _ _ _ _

theorem deriv_pFun_cont_STR02945 (A B : ℝ) : Continuous (deriv (pFun_STR02945 A B)) := by
  rw [deriv_pFun_STR02945]; exact mode2_cont_STR02945 _ _ _ _ _ _

theorem deriv_qFun_cont_STR02945 (C D E F : ℝ) : Continuous (deriv (qFun_STR02945 C D E F)) := by
  rw [deriv_qFun_STR02945]; exact mode2_cont_STR02945 _ _ _ _ _ _

theorem deriv_uFun_STR02945 (A B C D E F h t : ℝ) :
    deriv (uFun_STR02945 A B C D E F h) t =
      h * deriv (pFun_STR02945 A B) t + h ^ 2 * deriv (qFun_STR02945 C D E F) t := by
  have hpd : DifferentiableAt ℝ (pFun_STR02945 A B) t := by
    rw [pFun_eq_STR02945]; exact (mode2_hasDerivAt_STR02945 _ _ _ _ _ _ t).differentiableAt
  have hqd : DifferentiableAt ℝ (qFun_STR02945 C D E F) t := by
    rw [qFun_eq_STR02945]; exact (mode2_hasDerivAt_STR02945 _ _ _ _ _ _ t).differentiableAt
  have := (hpd.hasDerivAt.const_mul h).add (hqd.hasDerivAt.const_mul (h ^ 2))
  exact this.deriv

/-- Quadratic Fisher coefficient `⟨p'²⟩`. -/
noncomputable def I2_STR02945 (A B : ℝ) : ℝ :=
  normInt_STR02933 (fun t => deriv (pFun_STR02945 A B) t ^ 2)

/-- Quadratic entropy coefficient `⟨p²⟩ / 2`. -/
noncomputable def H2_STR02945 (A B : ℝ) : ℝ :=
  (1 / 2) * normInt_STR02933 (fun t => pFun_STR02945 A B t ^ 2)

/-- Fourth Fisher coefficient
`⟨q'²⟩ + 2⟨p'q'v⟩ + ⟨p'²q⟩ + ½⟨p'²v²⟩ − ½⟨p'²⟩⟨v²⟩`, with `v = b + p`. -/
noncomputable def I4_STR02945 (A B C D E F : ℝ) : ℝ :=
  normInt_STR02933 (fun t => deriv (qFun_STR02945 C D E F) t ^ 2) +
    2 * normInt_STR02933 (fun t => deriv (pFun_STR02945 A B) t * deriv (qFun_STR02945 C D E F) t *
      vFun_STR02945 A B t) +
    normInt_STR02933 (fun t => deriv (pFun_STR02945 A B) t ^ 2 * qFun_STR02945 C D E F t) +
    (1 / 2) * normInt_STR02933 (fun t => deriv (pFun_STR02945 A B) t ^ 2 *
      vFun_STR02945 A B t ^ 2) -
    (1 / 2) * normInt_STR02933 (fun t => deriv (pFun_STR02945 A B) t ^ 2) *
      normInt_STR02933 (fun t => vFun_STR02945 A B t ^ 2)

/-- Fourth entropy coefficient
`½⟨q²⟩ + ⟨pbq⟩ + ⟨p²q⟩ + ¼(⟨p²b²⟩ − ⟨p²⟩⟨b²⟩) + ⅓⟨p³b⟩ + ⅛⟨p⁴⟩ − ⅜⟨p²⟩²`. -/
noncomputable def H4_STR02945 (A B C D E F : ℝ) : ℝ :=
  (1 / 2) * normInt_STR02933 (fun t => qFun_STR02945 C D E F t ^ 2) +
    normInt_STR02933 (fun t => pFun_STR02945 A B t * bFun_STR02945 t * qFun_STR02945 C D E F t) +
    normInt_STR02933 (fun t => pFun_STR02945 A B t ^ 2 * qFun_STR02945 C D E F t) +
    (1 / 4) * (normInt_STR02933 (fun t => pFun_STR02945 A B t ^ 2 * bFun_STR02945 t ^ 2) -
      normInt_STR02933 (fun t => pFun_STR02945 A B t ^ 2) *
        normInt_STR02933 (fun t => bFun_STR02945 t ^ 2)) +
    (1 / 3) * normInt_STR02933 (fun t => pFun_STR02945 A B t ^ 3 * bFun_STR02945 t) +
    (1 / 8) * normInt_STR02933 (fun t => pFun_STR02945 A B t ^ 4) -
    (3 / 8) * normInt_STR02933 (fun t => pFun_STR02945 A B t ^ 2) ^ 2

/-- Normalizer `∫ e^{h cos 3s} dm` of the reference density `q_h`. -/
noncomputable def refNorm_STR02945 (h : ℝ) : ℝ :=
  normInt_STR02933 (fun s => Real.exp (h * Real.cos (3 * s)))

/-- The reference density `q_h(t) = e^{h cos 3t} / ∫ e^{h cos 3s} dm`. -/
noncomputable def refDensity_STR02945 (h t : ℝ) : ℝ :=
  Real.exp (h * Real.cos (3 * t)) / refNorm_STR02945 h

/-- Normalizer `∫ e^{h cos 3s + u s} dm` of the logarithmic chart. -/
noncomputable def chartNorm_STR02945 (h : ℝ) (u : ℝ → ℝ) : ℝ :=
  normInt_STR02933 (fun s => Real.exp (h * Real.cos (3 * s) + u s))

/-- The chart density `ρ(h,u)(t) = e^{h cos 3t + u t} / ∫ e^{h cos 3s + u s} dm`. -/
noncomputable def chartDensity_STR02945 (h : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (h * Real.cos (3 * t) + u t) / chartNorm_STR02945 h u

/-- The squared amplitude `g² = ρ(h,u) / q_h`. -/
noncomputable def chartRatio_STR02945 (h : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  chartDensity_STR02945 h u t / refDensity_STR02945 h t

/-- Fisher information of the chart density in the logarithmic chart, `∫ u'² ρ(h,u) dm`. -/
noncomputable def chartFisher_STR02945 (h : ℝ) (u : ℝ → ℝ) : ℝ :=
  normInt_STR02933 (fun t => deriv u t ^ 2 * chartDensity_STR02945 h u t)

/-- Entropy of the chart density relative to `q_h`, `∫ g² log (g²) q_h dm`. -/
noncomputable def chartEntropy_STR02945 (h : ℝ) (u : ℝ → ℝ) : ℝ :=
  normInt_STR02933 (fun t => chartRatio_STR02945 h u t * Real.log (chartRatio_STR02945 h u t) *
    refDensity_STR02945 h t)

theorem chartNorm_uFun_STR02945 (A B C D E F h : ℝ) :
    chartNorm_STR02945 h (uFun_STR02945 A B C D E F h) =
      normalizer_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h := by
  unfold chartNorm_STR02945 normalizer_STR02944
  refine normInt_congr_STR02945 (fun t => ?_)
  congr 1
  simp only [uFun_STR02945, expArg_STR02944, vFun_STR02945, bFun_STR02945]
  ring

theorem refNorm_eq_STR02945 (h : ℝ) :
    refNorm_STR02945 h = normalizer_STR02944 bFun_STR02945 (fun _ => 0) h := by
  unfold refNorm_STR02945 normalizer_STR02944
  refine normInt_congr_STR02945 (fun t => ?_)
  congr 1
  simp only [expArg_STR02944, bFun_STR02945]
  ring

theorem chartFisher_eq_STR02945 (A B C D E F h : ℝ) :
    chartFisher_STR02945 h (uFun_STR02945 A B C D E F h) =
      normInt_STR02933 (fun t => (h * deriv (pFun_STR02945 A B) t +
          h ^ 2 * deriv (qFun_STR02945 C D E F) t) ^ 2 *
          Real.exp (expArg_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h t)) /
        normalizer_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h := by
  unfold chartFisher_STR02945
  have key : ∀ t, deriv (uFun_STR02945 A B C D E F h) t ^ 2 *
      chartDensity_STR02945 h (uFun_STR02945 A B C D E F h) t =
      (normalizer_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h)⁻¹ *
        ((h * deriv (pFun_STR02945 A B) t + h ^ 2 * deriv (qFun_STR02945 C D E F) t) ^ 2 *
          Real.exp (expArg_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h t)) := by
    intro t
    have harg : h * Real.cos (3 * t) + uFun_STR02945 A B C D E F h t =
        expArg_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h t := by
      simp only [uFun_STR02945, expArg_STR02944, vFun_STR02945, bFun_STR02945]
      ring
    unfold chartDensity_STR02945
    rw [chartNorm_uFun_STR02945, harg, deriv_uFun_STR02945]
    ring
  rw [normInt_congr_STR02945 key, normInt_mul_const_STR02933, div_eq_inv_mul]

theorem chartEntropy_eq_STR02945 (A B C D E F h : ℝ)
    (hZ : 0 < normalizer_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h)
    (hZb : 0 < normalizer_STR02944 bFun_STR02945 (fun _ => 0) h) :
    chartEntropy_STR02945 h (uFun_STR02945 A B C D E F h) =
      normInt_STR02933 (fun t => (h * pFun_STR02945 A B t + h ^ 2 * qFun_STR02945 C D E F t) *
          Real.exp (expArg_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h t)) /
        normalizer_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h -
      Real.log (normalizer_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h) +
      Real.log (normalizer_STR02944 bFun_STR02945 (fun _ => 0) h) := by
  obtain ⟨Z, hZdef⟩ : ∃ Z, Z = normalizer_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h :=
    ⟨_, rfl⟩
  obtain ⟨Zb, hZbdef⟩ : ∃ Zb, Zb = normalizer_STR02944 bFun_STR02945 (fun _ => 0) h := ⟨_, rfl⟩
  rw [← hZdef] at hZ ⊢
  rw [← hZbdef] at hZb ⊢
  have hcn : chartNorm_STR02945 h (uFun_STR02945 A B C D E F h) = Z := by
    rw [chartNorm_uFun_STR02945, hZdef]
  have hrn : refNorm_STR02945 h = Zb := by rw [refNorm_eq_STR02945, hZbdef]
  have key : ∀ t, chartRatio_STR02945 h (uFun_STR02945 A B C D E F h) t *
      Real.log (chartRatio_STR02945 h (uFun_STR02945 A B C D E F h) t) * refDensity_STR02945 h t =
      Z⁻¹ * ((h * pFun_STR02945 A B t + h ^ 2 * qFun_STR02945 C D E F t) *
          Real.exp (expArg_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h t)) +
        ((Real.log Zb - Real.log Z) * Z⁻¹) *
          Real.exp (expArg_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h t) := by
    intro t
    have harg : h * Real.cos (3 * t) + uFun_STR02945 A B C D E F h t =
        expArg_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h t := by
      simp only [uFun_STR02945, expArg_STR02944, vFun_STR02945, bFun_STR02945]
      ring
    have hu : uFun_STR02945 A B C D E F h t = h * pFun_STR02945 A B t + h ^ 2 * qFun_STR02945 C D E F t :=
      rfl
    have hE := Real.exp_pos (expArg_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h t)
    have hEb := Real.exp_pos (h * Real.cos (3 * t))
    have hx : chartDensity_STR02945 h (uFun_STR02945 A B C D E F h) t =
        Real.exp (expArg_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h t) / Z := by
      unfold chartDensity_STR02945; rw [hcn, harg]
    have hy : refDensity_STR02945 h t = Real.exp (h * Real.cos (3 * t)) / Zb := by
      unfold refDensity_STR02945; rw [hrn]
    have hxpos := div_pos hE hZ
    have hypos := div_pos hEb hZb
    unfold chartRatio_STR02945
    rw [hx, hy]
    have e1 : Real.exp (expArg_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h t) / Z /
        (Real.exp (h * Real.cos (3 * t)) / Zb) * (Real.exp (h * Real.cos (3 * t)) / Zb) =
        Real.exp (expArg_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h t) / Z :=
      div_mul_cancel₀ _ (ne_of_gt hypos)
    have hlog : Real.log (Real.exp (expArg_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h t) /
        Z / (Real.exp (h * Real.cos (3 * t)) / Zb)) =
        (h * pFun_STR02945 A B t + h ^ 2 * qFun_STR02945 C D E F t) - Real.log Z + Real.log Zb := by
      rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hypos), Real.log_div (ne_of_gt hE) (ne_of_gt hZ),
        Real.log_div (ne_of_gt hEb) (ne_of_gt hZb), Real.log_exp, Real.log_exp, ← hu]
      have : expArg_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h t =
          h * Real.cos (3 * t) + uFun_STR02945 A B C D E F h t := harg.symm
      rw [this]; ring
    calc _ = (Real.exp (expArg_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h t) / Z /
          (Real.exp (h * Real.cos (3 * t)) / Zb) * (Real.exp (h * Real.cos (3 * t)) / Zb)) *
          Real.log (Real.exp (expArg_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h t) /
            Z / (Real.exp (h * Real.cos (3 * t)) / Zb)) := by ring
      _ = _ := by rw [e1, hlog]; ring
  have hc1 : Continuous (fun t => (h * pFun_STR02945 A B t + h ^ 2 * qFun_STR02945 C D E F t) *
      Real.exp (expArg_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h t)) := by
    have := pFun_cont_STR02945 A B
    have := qFun_cont_STR02945 C D E F
    have := vFun_cont_STR02945 A B
    unfold expArg_STR02944; fun_prop
  have hc2 : Continuous (fun t => Real.exp (expArg_STR02944 (vFun_STR02945 A B)
      (qFun_STR02945 C D E F) h t)) := by
    have := qFun_cont_STR02945 C D E F
    have := vFun_cont_STR02945 A B
    unfold expArg_STR02944; fun_prop
  have hZeq : normInt_STR02933 (fun t => Real.exp (expArg_STR02944 (vFun_STR02945 A B)
      (qFun_STR02945 C D E F) h t)) = Z := by rw [hZdef]; rfl
  unfold chartEntropy_STR02945
  rw [normInt_congr_STR02945 key, normInt_lin2_STR02945 _ _ hc1 hc2, hZeq]
  field_simp
  ring

theorem fisher_expansion_STR02945 (R : ℝ) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ A B C D E F : ℝ, |A| ≤ R → |B| ≤ R → |C| ≤ R → |D| ≤ R → |E| ≤ R → |F| ≤ R →
        ∀ h : ℝ, |h| ≤ h0 →
          |chartFisher_STR02945 h (uFun_STR02945 A B C D E F h) -
            (I2_STR02945 A B * h ^ 2 + 0 * h ^ 3 + I4_STR02945 A B C D E F * h ^ 4)| ≤
            K * |h| ^ 5 := by
  obtain ⟨h0, hpos, K, hK, hbd⟩ := fisher_generic_STR02945 (Mbound_STR02945 R)
  refine ⟨h0, hpos, K, hK, ?_⟩
  intro A B C D E F hA hB hC hD hE hF h hh
  have hp := pFun_admissible_STR02945 R hA hB
  have hq := qFun_admissible_STR02945 R hC hD hE hF
  have hv := vFun_admissible_STR02945 R hA hB
  have h1 := hbd (vFun_STR02945 A B) (qFun_STR02945 C D E F) (deriv (pFun_STR02945 A B))
    (deriv (qFun_STR02945 C D E F)) hv hq (deriv_pFun_cont_STR02945 A B)
    (deriv_qFun_cont_STR02945 C D E F) (fun t => admissible_deriv_bound_STR02945 hp t)
    (fun t => admissible_deriv_bound_STR02945 hq t) h hh
  have hn1 := fisher_n1_STR02945 (q := qFun_STR02945 C D E F) (deriv_pFun_cont_STR02945 A B)
    (deriv_qFun_cont_STR02945 C D E F) (vFun_cont_STR02945 A B) (deriv_pFun_shift_STR02945 A B)
    (deriv_qFun_shift_STR02945 C D E F) (vFun_shift_STR02945 A B)
  have hn2 := fisher_n2_STR02945 (deriv_pFun_cont_STR02945 A B) (deriv_qFun_cont_STR02945 C D E F)
    (vFun_cont_STR02945 A B) (qFun_cont_STR02945 C D E F) hq.2.1
  have hn0 : normInt_STR02933 (fun t => fk0_STR02945 (deriv (pFun_STR02945 A B) t)
      (deriv (qFun_STR02945 C D E F) t) (vFun_STR02945 A B t) (qFun_STR02945 C D E F t)) =
      I2_STR02945 A B := rfl
  rw [chartFisher_eq_STR02945]
  rw [hn2, hn1, hn0] at h1
  exact h1

theorem entropy_expansion_STR02945 (R : ℝ) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ A B C D E F : ℝ, |A| ≤ R → |B| ≤ R → |C| ≤ R → |D| ≤ R → |E| ≤ R → |F| ≤ R →
        ∀ h : ℝ, |h| ≤ h0 →
          |chartEntropy_STR02945 h (uFun_STR02945 A B C D E F h) -
            (H2_STR02945 A B * h ^ 2 + 0 * h ^ 3 + H4_STR02945 A B C D E F * h ^ 4)| ≤
            K * |h| ^ 5 := by
  obtain ⟨h1', hpos1, K, hK, hbd⟩ :=
    entropy_full_generic_STR02945 (Mbound_STR02945 R) (zero_admissible_STR02945 R)
  obtain ⟨hT, hTpos, Cc, hCc, hTT⟩ :=
    str029_44_uniform_exponential_normalizer_expansions (Mbound_STR02945 R)
  refine ⟨min h1' hT, lt_min hpos1 hTpos, K, hK, ?_⟩
  intro A B C D E F hA hB hC hD hE hF h hh
  have hhE : |h| ≤ h1' := hh.trans (min_le_left _ _)
  have hhT : |h| ≤ hT := hh.trans (min_le_right _ _)
  have hp := pFun_admissible_STR02945 R hA hB
  have hq := qFun_admissible_STR02945 R hC hD hE hF
  have hv := vFun_admissible_STR02945 R hA hB
  have hb := bFun_admissible_STR02945 R
  have hZ : 0 < normalizer_STR02944 (vFun_STR02945 A B) (qFun_STR02945 C D E F) h := by
    obtain ⟨-, -, -, h4, -⟩ := hTT _ _ hv hq h hhT
    have := (abs_le.mp h4).1
    linarith
  have hZb : 0 < normalizer_STR02944 bFun_STR02945 (fun _ => 0) h := by
    obtain ⟨-, -, -, h4, -⟩ := hTT _ _ hb (zero_admissible_STR02945 R) h hhT
    have := (abs_le.mp h4).1
    linarith
  have h1 := hbd bFun_STR02945 (vFun_STR02945 A B) (pFun_STR02945 A B) (qFun_STR02945 C D E F)
    hb hv hp hq h hhE
  have hq0 := hq.2.1
  have hpb := normInt_pFun_mul_bFun_STR02945 A B
  have hc2 := ent_c2_STR02945 (b := bFun_STR02945) (p := pFun_STR02945 A B)
    (q := qFun_STR02945 C D E F) bFun_cont_STR02945 (pFun_cont_STR02945 A B)
    (qFun_cont_STR02945 C D E F) hq0 hpb
  have hc3 := ent_c3_STR02945 (b := bFun_STR02945) (p := pFun_STR02945 A B)
    (q := qFun_STR02945 C D E F) bFun_cont_STR02945 (pFun_cont_STR02945 A B)
    (qFun_cont_STR02945 C D E F) bFun_shift_STR02945 (pFun_shift_STR02945 A B)
    (qFun_shift_STR02945 C D E F)
  have hc4 := ent_c4_STR02945 (b := bFun_STR02945) (p := pFun_STR02945 A B)
    (q := qFun_STR02945 C D E F) bFun_cont_STR02945 (pFun_cont_STR02945 A B)
    (qFun_cont_STR02945 C D E F) hq0 hpb
  rw [chartEntropy_eq_STR02945 A B C D E F h hZ hZb]
  have e2 : entC2_STR02945 bFun_STR02945 (vFun_STR02945 A B) (pFun_STR02945 A B)
      (qFun_STR02945 C D E F) = H2_STR02945 A B := hc2
  have e3 : entC3_STR02945 bFun_STR02945 (vFun_STR02945 A B) (pFun_STR02945 A B)
      (qFun_STR02945 C D E F) = 0 := hc3
  have e4 : entC4_STR02945 bFun_STR02945 (vFun_STR02945 A B) (pFun_STR02945 A B)
      (qFun_STR02945 C D E F) = H4_STR02945 A B C D E F := hc4
  rw [e2, e3, e4] at h1
  exact h1

/-- Information coefficients before trigonometric evaluation: uniformly for the coefficients
`|A|, …, |F| ≤ R` and `|h| ≤ h0`, the Fisher information and the relative entropy of the chart
density `ρ(h, u)` with `u = h p + h² q` equal `I₂ h² + 0 h³ + I₄ h⁴` and `H₂ h² + 0 h³ + H₄ h⁴`
up to an error `K |h|⁵`. -/
theorem str029_45_information_coefficients_before_trigonometric_evaluation (R : ℝ) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ A B C D E F : ℝ, |A| ≤ R → |B| ≤ R → |C| ≤ R → |D| ≤ R → |E| ≤ R → |F| ≤ R →
        ∀ h : ℝ, |h| ≤ h0 →
          |chartFisher_STR02945 h (uFun_STR02945 A B C D E F h) -
              (I2_STR02945 A B * h ^ 2 + 0 * h ^ 3 + I4_STR02945 A B C D E F * h ^ 4)| ≤
              K * |h| ^ 5 ∧
          |chartEntropy_STR02945 h (uFun_STR02945 A B C D E F h) -
              (H2_STR02945 A B * h ^ 2 + 0 * h ^ 3 + H4_STR02945 A B C D E F * h ^ 4)| ≤
              K * |h| ^ 5 := by
  obtain ⟨h1, hpos1, K1, hK1, hF⟩ := fisher_expansion_STR02945 R
  obtain ⟨h2, hpos2, K2, hK2, hH⟩ := entropy_expansion_STR02945 R
  refine ⟨min h1 h2, lt_min hpos1 hpos2, K1 + K2, add_nonneg hK1 hK2, ?_⟩
  intro A B C D E F hA hB hC hD hE hF' h hh
  have hh1 : |h| ≤ h1 := hh.trans (min_le_left _ _)
  have hh2 : |h| ≤ h2 := hh.trans (min_le_right _ _)
  have hpow : 0 ≤ |h| ^ 5 := pow_nonneg (abs_nonneg h) 5
  refine ⟨(hF A B C D E F hA hB hC hD hE hF' h hh1).trans ?_,
    (hH A B C D E F hA hB hC hD hE hF' h hh2).trans ?_⟩
  · nlinarith [mul_nonneg hK2 hpow]
  · nlinarith [mul_nonneg hK1 hpow]

end DGPS.Frontier.STR029
