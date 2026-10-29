import DGPS.Frontier.STR029.T45
import DGPS.Frontier.STR029.T46
import DGPS.Frontier.STR029.T47
import DGPS.Frontier.STR029.T49
import DGPS.Frontier.STR029.T50

/-!
# STR029.09: Fourth-order coefficient of the explicit information functional

Task id: STR029.09. Title: Fourth-order coefficient of the explicit information functional.
Prerequisites: STR029.44, STR029.45, STR029.46, STR029.47 (and the chart functionals of
STR029.49 and STR029.50).

Provides:
* `str029_09_fourth_order_coefficient_explicit_information_functional`: for every real bound `R`
  there are `h0 > 0` and `K ≥ 0` such that, for `|A|, …, |F| ≤ R` and `|h| ≤ h0`, the functional
  `J(h,0,u)` at `u = h p + h² q` equals `h⁴ 𝒥₄ + O(h⁵)`, the entropy equals
  `h² (A² + B²)/4 + O(h³)`, and for every remainder family `r` as in the R5 notes the functional at
  `u + h³ r(h)` equals `h⁴ 𝒥₄ + O(h⁵)` with the same `K`.
* `Jzero_STR02909 h u`: the functional `J(h,0,u) = I_h(ρ(h,u)) - 2 H_h(ρ(h,u))`.
* `J4_STR02909 A B C D E F`: the explicit fourth-order coefficient `𝒥₄` of the statement.
* `H4_closed_STR02909 A B C D E F`: the closed form of the fourth entropy coefficient (STR029.46).
* `normInt_pos_STR02909`: a normalized integral of a positive continuous function is positive.
* `meanT_eq_normInt_STR02909`: the periodic mean equals the normalized integral over `(0, 2π]`.
* `refNorm_pos_STR02909`, `chartNorm_pos_STR02909`: positivity of the two normalizers.
* `chartDensity_cont_STR02909`, `normInt_chartDensity_STR02909`: continuity and unit mass of the
  chart density `ρ(h,u)`.
* `chartRatio_log_STR02909`: the pointwise identity behind `g² log(g²) q_h = ρ (u + log Z_h - log Z)`.
* `rhoT_eq_chartDensity_STR02909`, `chartFisher_eq_fisherChart_STR02909`,
  `chartEntropy_eq_entropyChart_STR02909`, `Jzero_eq_Jchart_STR02909`: identification of the
  STR029.45 chart quantities with the STR029.49 and STR029.50 chart functionals.
* `uFun_cont_STR02909`, `pT_eq_pFun_STR02909`, `qT_eq_qFun_STR02909`: continuity of
  `u = h p + h² q` and identification of the STR029.47 trigonometric polynomials.
* `I2_eq_STR02909`, `H2_eq_STR02909`, `I2_eq_two_H2_STR02909`, `H4_eq_closed_STR02909`,
  `J4_identity_STR02909`: the quadratic coefficients and the identity `I4 - 2 H4 = 𝒥₄`.
* `H4_box_bound_STR02909`: a bound on the fourth entropy coefficient over the box `|·| ≤ R`.
* `pow_le_STR02909`: comparison of the powers `|h|³`, `|h|⁴`, `|h|⁵` for `|h| ≤ 1`.

R5 notes:
1. Reading of `J`. `J(h,0,u)` is `Jzero_STR02909 h u = I - 2H`, where `I` is the chart Fisher term
  `∫ u'² ρ dm` and `H` is `∫ g² log(g²) q_h dm` with `g² = ρ / q_h`, both as defined in STR029.45.
  The identity `I_h(ρ(h,u)) = ∫ u'² ρ dm` is used as the definition of the Fisher term. The
  amplitude `g = exp((u - log Z + log Z_h)/2)` and the factor `4 ∫ g'² q_h dm` are not formalized
  here; the brief assigns that identification to STR029.01.
2. Integrals. The normalized integral is `(2π)⁻¹ ∫_{(0,2π]}` (`normInt_STR02933`), and the periodic
  mean `meanT_STR02901` is shown to coincide with it.
3. Parameter domain. The bounded parameter sets are read as the box `|A|, …, |F| ≤ R` for an
  arbitrary real `R`. The constants `h0` and `K` depend on `R` only.
4. Range of h. The specification's `0 < h < h0` is replaced by `|h| ≤ h0`, which includes `h = 0`
  and negative `h`. This is a stronger conclusion.
5. Remainder family. The clause uses `r : ℝ → ℝ → ℝ` with: (a) each `r s` in the class
  `IsC2Alpha_STR02901 (1/2)`, periodic and `C²`, read as the specification's `C²` in the fixed
  exponent `α = 1/2` of the brief; (b) `meanT (r s) = 0`, which is passed to STR029.47 and not
  otherwise used; (c) a uniform bound `c2Norm (1/2) (r s) ≤ R` for every `s ∈ ℝ`, not only on the
  chosen interval. The specification's requirement that `r` be smooth in the parameter with its
  first five parameter derivatives bounded is not assumed and is not used. Items (a) and (c) are
  non-literal readings that STR029.47 requires.
6. The entropy clause `H_h(ρ(h,u)) = h²(A² + B²)/4 + O(h³)` has a constant `K` that is uniform over
  the box. The bound on the fourth entropy coefficient comes from compactness of the box
  (`H4_box_bound_STR02909`), so that constant is existential and not given explicitly.
7. The `O(h⁵)` for `J` and the `O(h³)` for `H` are derived from the STR029.45 expansions and the
  STR029.47 insensitivity bound; the constants are combined as `K = 3 K₁ + K₂ + |M|`.
8. No mean-zero hypothesis is imposed on `u = h p + h² q` beyond what the chart needs; the
  trigonometric polynomials `p` and `q` are used exactly as in the specification.
9. Library facts: no declaration from the implicit-function library and no EX049 periodic-Hölder
  declaration is used directly by this unit; the analytic input comes from STR029.44–47 and
  STR029.49–50.
-/

namespace DGPS.Frontier.STR029

/-- The functional `J(h,0,u) = I_h(ρ(h,u)) - 2 H_h(ρ(h,u))` in the logarithmic chart. -/
noncomputable def Jzero_STR02909 (h : ℝ) (u : ℝ → ℝ) : ℝ :=
  chartFisher_STR02945 h u - 2 * chartEntropy_STR02945 h u

/-- The explicit fourth-order coefficient `𝒥₄` of the statement. -/
noncomputable def J4_STR02909 (A B C D E F : ℝ) : ℝ :=
  3 / 2 * (C ^ 2 + D ^ 2) + 15 / 2 * (E ^ 2 + F ^ 2) +
    C * ((A ^ 2 - B ^ 2) / 4 - 3 * A / 2) + D * (A * B / 2 + 3 * B / 2) +
    3 / 2 * (A * E + B * F) + (A ^ 2 + B ^ 2) ^ 2 / 32 - 5 * (A ^ 3 - 3 * A * B ^ 2) / 24

/-- The closed form of the fourth entropy coefficient, as established in STR029.46. -/
noncomputable def H4_closed_STR02909 (A B C D E F : ℝ) : ℝ :=
  (C ^ 2 + D ^ 2 + E ^ 2 + F ^ 2) / 4 + (A * (C + E) + B * (F - D)) / 4 +
    ((A ^ 2 - B ^ 2) * C + 2 * A * B * D) / 4 + (A ^ 3 - 3 * A * B ^ 2) / 24 -
    3 * (A ^ 2 + B ^ 2) ^ 2 / 64

theorem H4_eq_closed_STR02909 (A B C D E F : ℝ) :
    H4_STR02945 A B C D E F = H4_closed_STR02909 A B C D E F :=
  (str029_46_exact_trigonometric_information_coefficients A B C D E F).1

theorem J4_identity_STR02909 (A B C D E F : ℝ) :
    I4_STR02945 A B C D E F - 2 * H4_STR02945 A B C D E F = J4_STR02909 A B C D E F := by
  rw [(str029_46_exact_trigonometric_information_coefficients A B C D E F).1,
    (str029_46_exact_trigonometric_information_coefficients A B C D E F).2]
  unfold J4_STR02909
  ring

theorem I2_eq_STR02909 (A B : ℝ) :
    I2_STR02945 A B = (1 / 2) * B ^ 2 + (1 / 2) * A ^ 2 :=
  mom_pd2_STR02946 A B

theorem H2_eq_STR02909 (A B : ℝ) : H2_STR02945 A B = (A ^ 2 + B ^ 2) / 4 := by
  unfold H2_STR02945
  rw [mom_p2_STR02946]
  ring

theorem I2_eq_two_H2_STR02909 (A B : ℝ) : I2_STR02945 A B = 2 * H2_STR02945 A B := by
  rw [I2_eq_STR02909, H2_eq_STR02909]
  ring

/-- A uniform bound on the closed-form fourth entropy coefficient over the box `|·| ≤ R`. -/
theorem H4_box_bound_STR02909 (R : ℝ) :
    ∃ M : ℝ, ∀ A B C D E F : ℝ, |A| ≤ R → |B| ≤ R → |C| ≤ R → |D| ≤ R → |E| ≤ R → |F| ≤ R →
      |H4_closed_STR02909 A B C D E F| ≤ M := by
  have hS : IsCompact (Set.Icc (-R) R ×ˢ (Set.Icc (-R) R ×ˢ (Set.Icc (-R) R ×ˢ
      (Set.Icc (-R) R ×ˢ (Set.Icc (-R) R ×ˢ Set.Icc (-R) R))))) :=
    isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod
      (isCompact_Icc.prod isCompact_Icc))))
  have hg : ContinuousOn (fun x : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ =>
      H4_closed_STR02909 x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
      (Set.Icc (-R) R ×ˢ (Set.Icc (-R) R ×ˢ (Set.Icc (-R) R ×ˢ
        (Set.Icc (-R) R ×ˢ (Set.Icc (-R) R ×ˢ Set.Icc (-R) R))))) := by
    apply Continuous.continuousOn
    unfold H4_closed_STR02909
    fun_prop
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hg
  refine ⟨M, fun A B C D E F hA hB hC hD hE hF => ?_⟩
  have hmem : ((A, B, C, D, E, F) : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) ∈
      (Set.Icc (-R) R ×ˢ (Set.Icc (-R) R ×ˢ (Set.Icc (-R) R ×ˢ
        (Set.Icc (-R) R ×ˢ (Set.Icc (-R) R ×ˢ Set.Icc (-R) R))))) :=
    ⟨abs_le.mp hA, abs_le.mp hB, abs_le.mp hC, abs_le.mp hD, abs_le.mp hE, abs_le.mp hF⟩
  have hb := hM _ hmem
  rw [Real.norm_eq_abs] at hb
  exact hb

/-- Power comparison for `|h| ≤ 1`. -/
theorem pow_le_STR02909 (h : ℝ) (hh : |h| ≤ 1) : |h| ^ 4 ≤ |h| ^ 3 ∧ |h| ^ 5 ≤ |h| ^ 3 := by
  have h3 : 0 ≤ |h| ^ 3 := pow_nonneg (abs_nonneg h) 3
  have h4 : 0 ≤ |h| ^ 4 := pow_nonneg (abs_nonneg h) 4
  have e4 : |h| ^ 4 ≤ |h| ^ 3 := by
    calc |h| ^ 4 = |h| ^ 3 * |h| := by ring
      _ ≤ |h| ^ 3 * 1 := mul_le_mul_of_nonneg_left hh h3
      _ = |h| ^ 3 := mul_one _
  refine ⟨e4, ?_⟩
  calc |h| ^ 5 = |h| ^ 4 * |h| := by ring
    _ ≤ |h| ^ 4 * 1 := mul_le_mul_of_nonneg_left hh h4
    _ = |h| ^ 4 := mul_one _
    _ ≤ |h| ^ 3 := e4

/-! ### Normalized integrals and the chart densities -/

/-- A normalized integral of a positive continuous function is positive. -/
theorem normInt_pos_STR02909 {f : ℝ → ℝ} (hf : Continuous f) (hpos : ∀ t, 0 < f t) :
    0 < normInt_STR02933 f := by
  unfold normInt_STR02933
  rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity)]
  exact mul_pos (by positivity)
    (intervalIntegral.intervalIntegral_pos_of_pos (hf.intervalIntegrable _ _) hpos
      (by positivity))

/-- The periodic mean over one period equals the normalized integral over `(0, 2π]`. -/
theorem meanT_eq_normInt_STR02909 (f : ℝ → ℝ) :
    meanT_STR02901 f = normInt_STR02933 f := by
  unfold meanT_STR02901 normInt_STR02933
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity)]

theorem refNorm_pos_STR02909 (h : ℝ) : 0 < refNorm_STR02945 h := by
  unfold refNorm_STR02945
  exact normInt_pos_STR02909 (by fun_prop) (fun t => Real.exp_pos _)

theorem chartNorm_pos_STR02909 (h : ℝ) {u : ℝ → ℝ} (hu : Continuous u) :
    0 < chartNorm_STR02945 h u := by
  unfold chartNorm_STR02945
  exact normInt_pos_STR02909 (by fun_prop) (fun t => Real.exp_pos _)

theorem chartDensity_cont_STR02909 (h : ℝ) {u : ℝ → ℝ} (hu : Continuous u) :
    Continuous (chartDensity_STR02945 h u) := by
  unfold chartDensity_STR02945
  fun_prop

theorem normInt_chartDensity_STR02909 (h : ℝ) {u : ℝ → ℝ} (hu : Continuous u) :
    normInt_STR02933 (chartDensity_STR02945 h u) = 1 := by
  have hZ : chartNorm_STR02945 h u ≠ 0 := (chartNorm_pos_STR02909 h hu).ne'
  have e : chartDensity_STR02945 h u = fun t =>
      (chartNorm_STR02945 h u)⁻¹ * Real.exp (h * Real.cos (3 * t) + u t) := by
    funext t
    unfold chartDensity_STR02945
    ring
  rw [e, normInt_mul_const_STR02933]
  exact inv_mul_cancel₀ hZ

/-- The pointwise identity `g² log(g²) q_h = ρ (u + log Z_h - log Z)` in the chart. -/
theorem chartRatio_log_STR02909 (h : ℝ) {u : ℝ → ℝ} (hu : Continuous u) (t : ℝ) :
    chartRatio_STR02945 h u t * Real.log (chartRatio_STR02945 h u t) * refDensity_STR02945 h t =
      chartDensity_STR02945 h u t * u t +
        (Real.log (refNorm_STR02945 h) - Real.log (chartNorm_STR02945 h u)) *
          chartDensity_STR02945 h u t := by
  have hZb : refNorm_STR02945 h ≠ 0 := (refNorm_pos_STR02909 h).ne'
  have hZu : chartNorm_STR02945 h u ≠ 0 := (chartNorm_pos_STR02909 h hu).ne'
  have hratio : chartRatio_STR02945 h u t =
      Real.exp (u t) * (refNorm_STR02945 h / chartNorm_STR02945 h u) := by
    unfold chartRatio_STR02945 chartDensity_STR02945 refDensity_STR02945
    rw [Real.exp_add]
    field_simp
  have hlog : Real.log (chartRatio_STR02945 h u t) =
      u t + (Real.log (refNorm_STR02945 h) - Real.log (chartNorm_STR02945 h u)) := by
    rw [hratio, Real.log_mul (Real.exp_ne_zero _) (div_ne_zero hZb hZu), Real.log_exp,
      Real.log_div hZb hZu]
  rw [hlog, hratio]
  unfold chartDensity_STR02945 refDensity_STR02945
  rw [Real.exp_add]
  field_simp

/-! ### Identification with the STR029.49 and STR029.50 chart functionals -/

theorem rhoT_eq_chartDensity_STR02909 (h : ℝ) (u : ℝ → ℝ) (t : ℝ) :
    rhoT_STR02901 h u t = chartDensity_STR02945 h u t := by
  unfold rhoT_STR02901 chartDensity_STR02945 chartNorm_STR02945
  rw [meanT_eq_normInt_STR02909]

theorem chartFisher_eq_fisherChart_STR02909 (h : ℝ) (u : ℝ → ℝ) :
    chartFisher_STR02945 h u = fisherChart_STR02949 h u := by
  unfold chartFisher_STR02945 fisherChart_STR02949
  rw [meanT_eq_normInt_STR02909]
  exact normInt_congr_STR02945 (fun t => by rw [rhoT_eq_chartDensity_STR02909])

theorem chartEntropy_eq_entropyChart_STR02909 (h : ℝ) {u : ℝ → ℝ} (hu : Continuous u) :
    chartEntropy_STR02945 h u = entropyChart_STR02949 h u := by
  have hfc : Continuous (chartDensity_STR02945 h u) := chartDensity_cont_STR02909 h hu
  have hgc : Continuous (fun t => chartDensity_STR02945 h u t * u t) := hfc.mul hu
  have hZu : meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u s)) =
      chartNorm_STR02945 h u := meanT_eq_normInt_STR02909 _
  have hZb : meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s))) =
      refNorm_STR02945 h := meanT_eq_normInt_STR02909 _
  have hm : meanT_STR02901 (fun t => u t * rhoT_STR02901 h u t) =
      normInt_STR02933 (fun t => chartDensity_STR02945 h u t * u t) := by
    rw [meanT_eq_normInt_STR02909]
    exact normInt_congr_STR02945 (fun t => by rw [rhoT_eq_chartDensity_STR02909]; ring)
  unfold chartEntropy_STR02945 entropyChart_STR02949
  rw [normInt_congr_STR02945 (chartRatio_log_STR02909 h hu),
    normInt_addmul_STR02945 _ hgc hfc, normInt_chartDensity_STR02909 h hu, hm, hZu, hZb]
  ring

theorem Jzero_eq_Jchart_STR02909 (h : ℝ) {u : ℝ → ℝ} (hu : Continuous u) :
    Jzero_STR02909 h u = Jchart_STR02950 h 0 u := by
  unfold Jzero_STR02909 Jchart_STR02950
  rw [chartFisher_eq_fisherChart_STR02909, chartEntropy_eq_entropyChart_STR02909 h hu]
  ring

/-! ### Trigonometric carriers -/

theorem uFun_cont_STR02909 (A B C D E F h : ℝ) :
    Continuous (uFun_STR02945 A B C D E F h) := by
  unfold uFun_STR02945
  exact (continuous_const.mul (pFun_cont_STR02945 A B)).add
    (continuous_const.mul (qFun_cont_STR02945 C D E F))

theorem pT_eq_pFun_STR02909 (A B t : ℝ) : pT_STR02947 A B t = pFun_STR02945 A B t := by
  simp only [pT_STR02947, trigN_STR02947, pFun_STR02945, Nat.cast_one, one_mul]

theorem qT_eq_qFun_STR02909 (C D E F t : ℝ) :
    qT_STR02947 C D E F t = qFun_STR02945 C D E F t := by
  simp only [qT_STR02947, trigN_STR02947, qFun_STR02945, Nat.cast_ofNat]
  ring

/-! ### Main statement -/

/-- STR029.09. For every bound `R` there are `h0 > 0` and `K ≥ 0` such that, for the box
`|A|, …, |F| ≤ R` and `|h| ≤ h0`: the functional at `u = h p + h² q` is `h⁴ 𝒥₄ + O(h⁵)`, the
entropy is `h² (A²+B²)/4 + O(h³)`, and adding `h³ r(h)` for a remainder family `r` changes the
fourth-order behavior only by `O(h⁵)` with the same constant `K`. -/
theorem str029_09_fourth_order_coefficient_explicit_information_functional (R : ℝ) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ A B C D E F : ℝ, |A| ≤ R → |B| ≤ R → |C| ≤ R → |D| ≤ R → |E| ≤ R → |F| ≤ R →
        ∀ h : ℝ, |h| ≤ h0 →
          |Jzero_STR02909 h (uFun_STR02945 A B C D E F h) - h ^ 4 * J4_STR02909 A B C D E F|
              ≤ K * |h| ^ 5 ∧
          |chartEntropy_STR02945 h (uFun_STR02945 A B C D E F h) -
              h ^ 2 * ((A ^ 2 + B ^ 2) / 4)| ≤ K * |h| ^ 3 ∧
          ∀ r : ℝ → ℝ → ℝ, (∀ s : ℝ, IsC2Alpha_STR02901 (1 / 2) (r s)) →
            (∀ s : ℝ, meanT_STR02901 (r s) = 0) →
            (∀ s : ℝ, c2Norm_STR02901 (1 / 2) (r s) ≤ R) →
              |Jzero_STR02909 h (fun t => h * pFun_STR02945 A B t +
                  h ^ 2 * qFun_STR02945 C D E F t + h ^ 3 * r h t) -
                  h ^ 4 * J4_STR02909 A B C D E F| ≤ K * |h| ^ 5 := by
  obtain ⟨h1, hpos1, K1, hK1, hT45⟩ :=
    str029_45_information_coefficients_before_trigonometric_evaluation R
  obtain ⟨h2, hpos2, K2, hK2, hT47⟩ :=
    str029_47_insensitivity_quartic_coefficient_cubic_logarithmic_remainder R
  obtain ⟨M, hM⟩ := H4_box_bound_STR02909 R
  have hM0 : 0 ≤ |M| := abs_nonneg M
  refine ⟨min (min h1 h2) 1, lt_min (lt_min hpos1 hpos2) one_pos,
    3 * K1 + K2 + |M|, by linarith, ?_⟩
  intro A B C D E F hA hB hC hD hE hF h hh
  have hh1 : |h| ≤ h1 := hh.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hh2 : |h| ≤ h2 := hh.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hh3 : |h| ≤ 1 := hh.trans (min_le_right _ _)
  obtain ⟨hf, he⟩ := hT45 A B C D E F hA hB hC hD hE hF h hh1
  obtain ⟨hpow4, hpow5⟩ := pow_le_STR02909 h hh3
  have hK5 : 0 ≤ |h| ^ 5 := by positivity
  have hH4 : |H4_STR02945 A B C D E F| ≤ |M| := by
    rw [H4_eq_closed_STR02909]
    exact (hM A B C D E F hA hB hC hD hE hF).trans (le_abs_self M)
  -- Algebra: J - h⁴ 𝒥₄ = (Fisher remainder) - 2 (entropy remainder), using I₂ = 2 H₂ and I₄ - 2 H₄ = 𝒥₄.
  have hkey : Jzero_STR02909 h (uFun_STR02945 A B C D E F h) - h ^ 4 * J4_STR02909 A B C D E F =
      (chartFisher_STR02945 h (uFun_STR02945 A B C D E F h) -
          (I2_STR02945 A B * h ^ 2 + 0 * h ^ 3 + I4_STR02945 A B C D E F * h ^ 4)) -
        2 * (chartEntropy_STR02945 h (uFun_STR02945 A B C D E F h) -
          (H2_STR02945 A B * h ^ 2 + 0 * h ^ 3 + H4_STR02945 A B C D E F * h ^ 4)) := by
    unfold Jzero_STR02909
    linear_combination h ^ 2 * I2_eq_two_H2_STR02909 A B +
      h ^ 4 * J4_identity_STR02909 A B C D E F
  -- Clause 1 with the sharper constant 3 K₁.
  have hc1 : |Jzero_STR02909 h (uFun_STR02945 A B C D E F h) - h ^ 4 * J4_STR02909 A B C D E F|
      ≤ 3 * K1 * |h| ^ 5 := by
    rw [hkey, abs_le]
    have hX := abs_le.mp hf
    have hY := abs_le.mp he
    constructor <;> linarith [hX.1, hX.2, hY.1, hY.2]
  have hcl1 : |Jzero_STR02909 h (uFun_STR02945 A B C D E F h) - h ^ 4 * J4_STR02909 A B C D E F|
      ≤ (3 * K1 + K2 + |M|) * |h| ^ 5 := by
    have h2nn : 0 ≤ K2 * |h| ^ 5 := mul_nonneg hK2 hK5
    have hMnn : 0 ≤ |M| * |h| ^ 5 := mul_nonneg hM0 hK5
    linarith [hc1, h2nn, hMnn]
  -- Clause 2: the fourth entropy term is O(h⁴) and is absorbed into O(h³).
  have hH4term : |H4_STR02945 A B C D E F * h ^ 4| ≤ |M| * |h| ^ 3 := by
    rw [abs_mul, abs_pow]
    calc |H4_STR02945 A B C D E F| * |h| ^ 4 ≤ |M| * |h| ^ 4 :=
          mul_le_mul_of_nonneg_right hH4 (by positivity)
      _ ≤ |M| * |h| ^ 3 := mul_le_mul_of_nonneg_left hpow4 hM0
  have hcl2 : |chartEntropy_STR02945 h (uFun_STR02945 A B C D E F h) -
      h ^ 2 * ((A ^ 2 + B ^ 2) / 4)| ≤ (3 * K1 + K2 + |M|) * |h| ^ 3 := by
    have hdiff : chartEntropy_STR02945 h (uFun_STR02945 A B C D E F h) -
        h ^ 2 * ((A ^ 2 + B ^ 2) / 4) =
        (chartEntropy_STR02945 h (uFun_STR02945 A B C D E F h) -
          (H2_STR02945 A B * h ^ 2 + 0 * h ^ 3 + H4_STR02945 A B C D E F * h ^ 4)) +
          H4_STR02945 A B C D E F * h ^ 4 := by
      rw [H2_eq_STR02909]
      ring
    rw [hdiff, abs_le]
    have hY := abs_le.mp he
    have hT := abs_le.mp hH4term
    have hK13 : K1 * |h| ^ 5 ≤ K1 * |h| ^ 3 := mul_le_mul_of_nonneg_left hpow5 hK1
    have hA3 : 0 ≤ K1 * |h| ^ 3 := mul_nonneg hK1 (by positivity)
    have hB3 : 0 ≤ K2 * |h| ^ 3 := mul_nonneg hK2 (by positivity)
    have hC3 : 0 ≤ |M| * |h| ^ 3 := mul_nonneg hM0 (by positivity)
    constructor <;> linarith [hY.1, hY.2, hT.1, hT.2, hK13, hA3, hB3, hC3]
  refine ⟨hcl1, hcl2, ?_⟩
  -- Clause 3: the cubic logarithmic remainder, via STR029.47 on the same chart functional.
  intro r hr hm hrn
  have hT47' := hT47 A B C D E F hA hB hC hD hE hF r hr hm hrn h hh2
  have e0 : (fun t => h * pT_STR02947 A B t + h ^ 2 * qT_STR02947 C D E F t) =
      uFun_STR02945 A B C D E F h := by
    funext t
    simp only [pT_eq_pFun_STR02909, qT_eq_qFun_STR02909, uFun_STR02945]
  have e1 : (fun t => h * pT_STR02947 A B t + h ^ 2 * qT_STR02947 C D E F t + h ^ 3 * r h t) =
      (fun t => h * pFun_STR02945 A B t + h ^ 2 * qFun_STR02945 C D E F t + h ^ 3 * r h t) := by
    funext t
    simp only [pT_eq_pFun_STR02909, qT_eq_qFun_STR02909]
  rw [e1, e0] at hT47'
  have hcontR : Continuous (fun t => h * pFun_STR02945 A B t +
      h ^ 2 * qFun_STR02945 C D E F t + h ^ 3 * r h t) := by
    have hrc : Continuous (r h) := (hr h).2.1.continuous
    exact ((continuous_const.mul (pFun_cont_STR02945 A B)).add
      (continuous_const.mul (qFun_cont_STR02945 C D E F))).add (continuous_const.mul hrc)
  rw [← Jzero_eq_Jchart_STR02909 h hcontR,
    ← Jzero_eq_Jchart_STR02909 h (uFun_cont_STR02909 A B C D E F h)] at hT47'
  have hA1 := abs_le.mp hT47'
  have hA2 := abs_le.mp hc1
  have hM5 : 0 ≤ |M| * |h| ^ 5 := mul_nonneg hM0 hK5
  rw [abs_le]
  constructor <;> linarith [hA1.1, hA1.2, hA2.1, hA2.2, hM5]

end DGPS.Frontier.STR029
