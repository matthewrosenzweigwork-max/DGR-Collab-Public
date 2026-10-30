import DGPS.Lipschitz.T01TiltScore

/-!
# Exact tilt dissipation integrals and their limit

The limiting numerator is the integral of the actual gradient norm. Uniform
Lipschitz bounds supply domination only; they do not replace that integral.
-/

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- The sharp scaled dissipation integrand of the equilibrium tilt. -/
noncomputable def t01TiltEnergy (h : Torus d → ℝ) (G B : Torus d → Tangent d)
    (t : ℝ) (x : Torus d) : ℝ :=
  ‖G x + (t * h x) • B x‖ ^ 2 / (1 + t * h x)

/-- Dominated convergence for the exact scaled dissipation. The vector fields may
be merely measurable and essentially bounded. -/
theorem tendsto_t01_tilt_energy (μ : Measure (Torus d)) [IsFiniteMeasure μ]
    (h : Torus d → ℝ) (hh : Measurable h) (G B : Torus d → Tangent d)
    (hG : Measurable G) (hB : Measurable B) {M Lg Lb : ℝ}
    (hM : 0 ≤ M) (hLg : 0 ≤ Lg) (hLb : 0 ≤ Lb)
    (hbound : ∀ x, |h x| ≤ M)
    (hg : ∀ᵐ x ∂μ, ‖G x‖ ≤ Lg) (hb : ∀ᵐ x ∂μ, ‖B x‖ ≤ Lb) :
    Tendsto (fun t => ∫ x, t01TiltEnergy h G B t x ∂μ) (𝓝 0)
      (𝓝 (∫ x, ‖G x‖ ^ 2 ∂μ)) := by
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| ≤ 1 ∧ |t| * M ≤ 1 / 2 := by
    have h1 : ∀ᶠ t : ℝ in 𝓝 0, |t| ≤ 1 :=
      (continuous_abs.tendsto' 0 0 (by simp)).eventually (ge_mem_nhds (by norm_num))
    have h2 : ∀ᶠ t : ℝ in 𝓝 0, |t| * M ≤ 1 / 2 :=
      ((continuous_abs.mul continuous_const).tendsto' 0 0 (by simp)).eventually
        (ge_mem_nhds (by norm_num))
    exact h1.and h2
  have hmeas : ∀ t, Measurable (t01TiltEnergy h G B t) := fun t =>
    ((hG.add ((measurable_const.mul hh).smul hB)).norm.pow_const 2).div
      (measurable_const.add (measurable_const.mul hh))
  have hlim : ∀ x, Tendsto (fun t => t01TiltEnergy h G B t x) (𝓝 0)
      (𝓝 (‖G x‖ ^ 2)) := by
    intro x
    have hc : ContinuousAt (fun t => t01TiltEnergy h G B t x) 0 := by
      unfold t01TiltEnergy
      exact ((continuous_const.add ((continuous_id.mul continuous_const).smul
        continuous_const)).norm.pow 2).continuousAt.div
          (continuous_const.add (continuous_id.mul continuous_const)).continuousAt (by simp)
    simpa only [t01TiltEnergy, zero_mul, zero_smul, add_zero, add_zero, zero_add, div_one]
      using hc.tendsto
  refine tendsto_integral_filter_of_dominated_convergence
    (fun _ => 2 * (Lg + M * Lb) ^ 2) ?_ ?_ (integrable_const _) (Eventually.of_forall hlim)
  · exact Eventually.of_forall fun t => (hmeas t).aestronglyMeasurable
  · filter_upwards [hsmall] with t ht
    filter_upwards [hg, hb] with x hxg hxb
    have hth : |t * h x| ≤ 1 / 2 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hbound x) (abs_nonneg _)).trans ht.2
    have ha : 1 / 2 ≤ 1 + t * h x := by linarith [(abs_le.mp hth).1]
    have hnorm : ‖G x + (t * h x) • B x‖ ≤ Lg + M * Lb := by
      refine (norm_add_le _ _).trans (add_le_add hxg ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_mul]
      calc |t| * |h x| * ‖B x‖ ≤ 1 * M * Lb :=
            mul_le_mul (mul_le_mul ht.1 (hbound x) (abs_nonneg _) (by norm_num))
              hxb (norm_nonneg _) (by positivity)
        _ = M * Lb := by ring
    have hn0 : 0 ≤ ‖G x + (t * h x) • B x‖ ^ 2 := sq_nonneg _
    have hn : ‖G x + (t * h x) • B x‖ ^ 2 ≤ (Lg + M * Lb) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    unfold t01TiltEnergy
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hn0 (by linarith))]
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg (Lg + M * Lb)]

/-- The same domination also proves finite real integrability on the safe tilt interval. -/
theorem t01_tilt_energy_integrable (μ : Measure (Torus d)) [IsFiniteMeasure μ]
    (h : Torus d → ℝ) (hh : Measurable h) (G B : Torus d → Tangent d)
    (hG : Measurable G) (hB : Measurable B) {M Lg Lb t : ℝ}
    (hM : 0 ≤ M) (hLg : 0 ≤ Lg) (hLb : 0 ≤ Lb)
    (hbound : ∀ x, |h x| ≤ M)
    (hg : ∀ᵐ x ∂μ, ‖G x‖ ≤ Lg) (hb : ∀ᵐ x ∂μ, ‖B x‖ ≤ Lb)
    (ht : |t| ≤ 1) (htM : |t| * M ≤ 1 / 2) :
    Integrable (t01TiltEnergy h G B t) μ := by
  have hm : Measurable (t01TiltEnergy h G B t) :=
    ((hG.add ((measurable_const.mul hh).smul hB)).norm.pow_const 2).div
      (measurable_const.add (measurable_const.mul hh))
  refine Integrable.of_bound hm.aestronglyMeasurable (2 * (Lg + M * Lb) ^ 2) ?_
  filter_upwards [hg, hb] with x hxg hxb
  have hth : |t * h x| ≤ 1 / 2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hbound x) (abs_nonneg _)).trans htM
  have ha : 1 / 2 ≤ 1 + t * h x := by linarith [(abs_le.mp hth).1]
  have hnorm : ‖G x + (t * h x) • B x‖ ≤ Lg + M * Lb := by
    refine (norm_add_le _ _).trans (add_le_add hxg ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
    calc |t| * |h x| * ‖B x‖ ≤ 1 * M * Lb :=
          mul_le_mul (mul_le_mul ht (hbound x) (abs_nonneg _) (by norm_num))
            hxb (norm_nonneg _) (by positivity)
      _ = M * Lb := by ring
  have hn0 : 0 ≤ ‖G x + (t * h x) • B x‖ ^ 2 := sq_nonneg _
  have hn : ‖G x + (t * h x) • B x‖ ^ 2 ≤ (Lg + M * Lb) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  unfold t01TiltEnergy
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hn0 (by linarith)),
    div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg (Lg + M * Lb)]

private theorem t01_tilt_score_integrand (a t : ℝ) (ha : 0 < a) (z : Tangent d) :
    a * ‖t • (a⁻¹ • z)‖ ^ 2 = t ^ 2 * (‖z‖ ^ 2 / a) := by
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow,
    sq_abs, sq_abs]
  field_simp [ha.ne']
  <;> ring

/-- Exact dissipation of the same absolute density, under its actual relative score.
Finiteness is supplied by the real integrability input, not assumed for the density. -/
theorem t01_tilt_dissipation_eq (A : InteractionData d) (b : AbsoluteDrift A)
    (ρ : AbsoluteDensity d) (μ : Measure (Torus d))
    (h : Torus d → ℝ) (hh : Measurable h) (G B : Torus d → Tangent d)
    (hG : Measurable G) (hB : Measurable B) (t : ℝ)
    (hpos : ∀ x, 0 < 1 + t * h x)
    (hρ : (densityMeasure ρ : Measure (Torus d)) =
      perturb μ (fun x => 1 + t * h x))
    (hscore : scalarScore A b ρ =ᵐ[haar d] fun x => ρ.sqrt x •
      (t • ((1 + t * h x)⁻¹ • (G x + (t * h x) • B x))))
    (hint : Integrable (t01TiltEnergy h G B t) μ) :
    scalarDissipation A b ρ =
      ENNReal.ofReal (t ^ 2 * ∫ x, t01TiltEnergy h G B t x ∂μ) := by
  have hm : Measurable (fun x => t • ((1 + t * h x)⁻¹ •
      (G x + (t * h x) • B x))) := by
    exact (((measurable_const.add (measurable_const.mul hh)).inv.smul
      (hG.add ((measurable_const.mul hh).smul hB))).const_smul t)
  have he := scalarDissipation_eq_reference_score A b ρ μ
    (fun x => 1 + t * h x) (measurable_const.add (measurable_const.mul hh))
    (fun x => (hpos x).le) _ hm hρ hscore
  rw [he]
  have hp : ∀ x, 0 ≤ t01TiltEnergy h G B t x := fun x =>
    div_nonneg (sq_nonneg _) (hpos x).le
  calc (∫⁻ x, ENNReal.ofReal ((1 + t * h x) *
        ‖t • ((1 + t * h x)⁻¹ • (G x + (t * h x) • B x))‖ ^ 2) ∂μ)
      = ∫⁻ x, ENNReal.ofReal (t ^ 2 * t01TiltEnergy h G B t x) ∂μ := by
          refine lintegral_congr fun x => ?_
          rw [t01_tilt_score_integrand _ _ (hpos x)]
          rfl
    _ = ENNReal.ofReal (∫ x, t ^ 2 * t01TiltEnergy h G B t x ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal (hint.const_mul _) (Eventually.of_forall
        fun x => mul_nonneg (sq_nonneg _) (hp x))).symm
    _ = _ := by rw [integral_const_mul]

end DGPS.Lipschitz
