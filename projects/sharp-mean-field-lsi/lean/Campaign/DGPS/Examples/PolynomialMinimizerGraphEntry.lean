import DGPS.Examples.PolynomialProjectedCriticality
import DGPS.Examples.PolynomialProviderIndependence
import DGPS.Examples.PolynomialSpeciesRangeCommon

/-! Original-domain minimizers enter the SAME existing interacting range graph.
The amplitude/complement decomposition and every neighborhood condition are
derived from actual centered C2 capture and the actual coarse rate limit. -/

noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ENNReal
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization
open DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

private def cosineCoefficient : PeriodicC2_STR02969 →L[ℝ] ℝ :=
  (2 : ℝ) • c2Data_STR02969.pairCLM Real.cos Real.continuous_cos Real.abs_cos_le_one

private def sineCoefficient : PeriodicC2_STR02969 →L[ℝ] ℝ :=
  (2 : ℝ) • c2Data_STR02969.pairCLM Real.sin Real.continuous_sin Real.abs_sin_le_one

private def complementRaw (u : PeriodicC2_STR02969) : PeriodicC2_STR02969 :=
  u - cosineCoefficient u • cosC2_STR02915 - sineCoefficient u • sinC2_STR02915

private theorem complement_mem (u : PeriodicC2_STR02969) (hm : meanT_STR02901 u.val = 0) :
    complementRaw u ∈ E_STR02969 := by
  apply (str029_69_completeness_closed_complements_range_spaces_E.1 _).2
  have he : (complementRaw u).val = projP_STR02953 u.val := by
    funext t
    change u.val t - (2 * pair_STR02953 Real.cos u.val) * Real.cos t -
      (2 * pair_STR02953 Real.sin u.val) * Real.sin t = projP_STR02953 u.val t
    rw [projP_STR02953, hm]
    ring
  rw [he]
  exact projP_inE_STR02955 u.isC2.2.1.continuous

private def complement (u : PeriodicC2_STR02969) (hm : meanT_STR02901 u.val = 0) : E_STR02969 :=
  ⟨complementRaw u, complement_mem u hm⟩

private theorem decomposition (u : PeriodicC2_STR02969) (hm : meanT_STR02901 u.val = 0) :
    cosineCoefficient u • cosC2_STR02915 + sineCoefficient u • sinC2_STR02915 +
      (complement u hm : PeriodicC2_STR02969) = u := by
  change cosineCoefficient u • cosC2_STR02915 + sineCoefficient u • sinC2_STR02915 +
    (u - cosineCoefficient u • cosC2_STR02915 - sineCoefficient u • sinC2_STR02915) = u
  module

private theorem complementRaw_continuous : Continuous complementRaw :=
  (continuous_id.sub (cosineCoefficient.continuous.smul continuous_const)).sub
    (sineCoefficient.continuous.smul continuous_const)

/-- Any retained actual range graph accepts a subsequence of EVERY original
minimizer sequence at vanishing fields. No chart or neighborhood entry premise
is assumed for the competitors. The graph witness is supplied once and retained. -/
theorem polynomial_scalarMinimizer_sequence_graph_entry
    (U : Set PolynomialRangeParameters) (N : Set E_STR02969)
    (ψ : PolynomialRangeParameters → E_STR02969)
    (hU : IsOpen U) (h0U : (0 : PolynomialRangeParameters) ∈ U)
    (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (b : ∀ n, AbsoluteDrift (canonical_elementary_polynomial_model (h n)))
    (ρ : ℕ → AbsoluteDensity 1)
    (hG : ∀ n, 0 < scalarGap (canonical_elementary_polynomial_model (h n)) (ρ n))
    (hmin : ∀ n, scalarQuotient (canonical_elementary_polynomial_model (h n)) (b n) (ρ n) =
      scalarRate (canonical_elementary_polynomial_model (h n)) (b n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᶠ n in atTop,
      ∃ a b' : ℝ, ∃ w : E_STR02969,
        let γ := (scalarRate (canonical_elementary_polynomial_model (h (φ n))) (b (φ n))).toReal / a0 - 1
        let p : PolynomialRangeParameters := (a, b', (h (φ n), root_EX054 (h (φ n))), γ)
        p ∈ U ∧ w ∈ N ∧ ψ p = w ∧
        (ρ (φ n)).density =ᵐ[haar 1]
          (polynomialChartAbsolute (h (φ n))
            (a • cosC2_STR02915 + b' • sinC2_STR02915 + (w : PeriodicC2_STR02969))).density := by
  obtain ⟨φ, u, hφ, hm, hd, hn, hEuler⟩ :=
    polynomial_scalarMinimizer_projected_chart_capture h hh b ρ hG hmin
  have hu : Tendsto u atTop (𝓝 (0 : PeriodicC2_STR02969)) := tendsto_zero_iff_norm_tendsto_zero.mpr hn
  let a := fun n => cosineCoefficient (u n)
  let b' := fun n => sineCoefficient (u n)
  let w := fun n => complement (u n) (hm n)
  let r := fun n => (scalarRate (canonical_elementary_polynomial_model (h (φ n))) (b (φ n))).toReal
  let γ := fun n => r n / a0 - 1
  let p := fun n => ((a n, b' n, (h (φ n), root_EX054 (h (φ n))), γ n) : PolynomialRangeParameters)
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [a, Function.comp_def, map_zero] using (cosineCoefficient.continuous.tendsto 0).comp hu
  have hb : Tendsto b' atTop (𝓝 0) := by
    simpa only [b', Function.comp_def, map_zero] using (sineCoefficient.continuous.tendsto 0).comp hu
  have hw : Tendsto w atTop (𝓝 (0 : E_STR02969)) := by
    apply tendsto_subtype_rng.mpr
    have ht := (complementRaw_continuous.tendsto 0).comp hu
    simpa [w, complement, complementRaw, Function.comp_def] using ht
  have hhs : Tendsto (fun n => h (φ n)) atTop (𝓝 0) := hh.comp hφ.tendsto_atTop
  have hr : Tendsto r atTop (𝓝 a0) := by
    have ht := (polynomial_sequence_rates_at_origin h hh b).2.comp hφ.tendsto_atTop
    have htr := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp ht
    simpa only [r, Function.comp_def, ENNReal.toReal_ofReal a0_pos.le] using htr
  have hγ : Tendsto γ atTop (𝓝 0) := by
    simpa only [γ, div_self a0_pos.ne', sub_self] using (hr.div_const a0).sub_const 1
  have hp : Tendsto p atTop (𝓝 0) :=
    polynomial_selected_parameters_tendsto.comp (ha.prodMk_nhds (hb.prodMk_nhds (hhs.prodMk_nhds hγ)))
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hp.eventually (hU.mem_nhds h0U), hw.eventually (hN.mem_nhds h0N)] with n hpn hwn
  refine ⟨a n, b' n, w n, hpn, hwn, ?_, ?_⟩
  · apply (hgraph (p n) hpn (w n) hwn).1
    have hrate : a0 * (1 + γ n) = r n := by
      dsimp only [γ]
      field_simp [show a0 ≠ 0 from a0_pos.ne']
      ring
    change PY_STR02955 (polynomialRangeEuler (h (φ n), root_EX054 (h (φ n)))
      (a0 * (1 + γ n)) (a n • cosC2_STR02915 + b' n • sinC2_STR02915 + (w n : PeriodicC2_STR02969))) = 0
    rw [hrate]
    change PY_STR02955 (polynomialRangeEuler (h (φ n), root_EX054 (h (φ n))) (r n)
      (cosineCoefficient (u n) • cosC2_STR02915 + sineCoefficient (u n) • sinC2_STR02915 +
        (complement (u n) (hm n) : PeriodicC2_STR02969))) = 0
    rw [decomposition]
    exact hEuler n
  · change (ρ (φ n)).density =ᵐ[haar 1] (polynomialChartAbsolute (h (φ n))
      (cosineCoefficient (u n) • cosC2_STR02915 + sineCoefficient (u n) • sinC2_STR02915 +
        (complement (u n) (hm n) : PeriodicC2_STR02969))).density
    rw [decomposition]
    exact hd n

/-- Every sufficiently small positive field and EVERY actual original-domain
minimizer enter the supplied SAME actual graph. The field threshold precedes
the drift and competitor; no bound or regularity assumption is added. -/
theorem polynomial_scalarMinimizer_graph_entry
    (U : Set PolynomialRangeParameters) (N : Set E_STR02969)
    (ψ : PolynomialRangeParameters → E_STR02969)
    (hU : IsOpen U) (h0U : (0 : PolynomialRangeParameters) ∈ U)
    (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h),
      ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (canonical_elementary_polynomial_model h) ρ →
      scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
        scalarRate (canonical_elementary_polynomial_model h) b →
      ∃ a b' : ℝ, ∃ w : E_STR02969,
        let γ := (scalarRate (canonical_elementary_polynomial_model h) b).toReal / a0 - 1
        let p : PolynomialRangeParameters := (a, b', (h, root_EX054 h), γ)
        p ∈ U ∧ w ∈ N ∧ ψ p = w ∧
        ρ.density =ᵐ[haar 1] (polynomialChartAbsolute h
          (a • cosC2_STR02915 + b' • sinC2_STR02915 + (w : PeriodicC2_STR02969))).density := by
  classical
  by_contra hc
  push_neg at hc
  have hbad : ∀ n : ℕ, ∃ h : ℝ, 0 < h ∧ h < 1 / (n + 1 : ℝ) ∧
      ∃ b : AbsoluteDrift (canonical_elementary_polynomial_model h), ∃ ρ : AbsoluteDensity 1,
      0 < scalarGap (canonical_elementary_polynomial_model h) ρ ∧
      scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
        scalarRate (canonical_elementary_polynomial_model h) b ∧
      ¬ ∃ a b' : ℝ, ∃ w : E_STR02969,
        let γ := (scalarRate (canonical_elementary_polynomial_model h) b).toReal / a0 - 1
        let p : PolynomialRangeParameters := (a, b', (h, root_EX054 h), γ)
        p ∈ U ∧ w ∈ N ∧ ψ p = w ∧
        ρ.density =ᵐ[haar 1] (polynomialChartAbsolute h
          (a • cosC2_STR02915 + b' • sinC2_STR02915 + (w : PeriodicC2_STR02969))).density := by
    intro n
    obtain ⟨h, hh, hδ, b, ρ, hG, hmin, hfail⟩ := hc (1 / (n + 1 : ℝ)) (by positivity)
    exact ⟨h, hh, hδ, b, ρ, hG, hmin, by simpa only [not_exists] using hfail⟩
  choose h hh hsmall b ρ hG hmin hfail using hbad
  have hlim : Tendsto h atTop (𝓝 0) :=
    squeeze_zero (fun n => (hh n).le) (fun n => (hsmall n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨φ, hφ, he⟩ := polynomial_scalarMinimizer_sequence_graph_entry U N ψ hU h0U hN h0N hgraph
    h hlim b ρ hG hmin
  obtain ⟨n, hn⟩ := he.exists
  exact hfail (φ n) hn

end DGPS.Examples.PolynomialSpecies
