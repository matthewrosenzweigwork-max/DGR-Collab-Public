import DGPS.Examples.PolynomialSpeciesFactorImplicitBranches
import DGPS.Examples.PolynomialChartCriticality
import DGPS.Examples.PolynomialSpeciesScaledQuarticCapture

/-! Actual original-domain minimizers satisfy the scaled three-equation system.
The proof uses the genuine global variational deficit inequality and the local
fourth-power identity. No differentiated value remainder, stationarity premise,
or assertion about optimizer capture is assumed. -/
noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ContDiff ENNReal
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium
open DGPS.Circle.AngularNormalization

namespace DGPS.Examples.PolynomialSpecies

/-- On the open domain of the genuine fourth factor, every original minimizer
represented by the supplied graph is a zero of its actual critical system.
The selected reference enters only through a pointwise coordinate equality;
there is no differentiation of `root_EX054`. -/
theorem polynomial_scalarMinimizer_scaled_critical
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0) (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0) :
    ∃ O : Set (ℝ × PolynomialScaledCoefficients), IsOpen O ∧
      (∀ c, ((0 : ℝ), c) ∈ O) ∧ O ⊆ polynomialScaledParameters ⁻¹' U ∧
      ∀ (h σ : ℝ) (z : PolynomialFactorUnknowns)
        (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (ρ : AbsoluteDensity 1),
      h ≠ 0 → (h, (z.1.1, z.1.2, z.2, σ)) ∈ O →
      h ^ 4 * σ = root_EX054 h →
      a0 * (1 + h ^ 2 * z.2) = (scalarRate (canonical_elementary_polynomial_model h) b).toReal →
      0 < scalarGap (canonical_elementary_polynomial_model h) ρ →
      scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
        scalarRate (canonical_elementary_polynomial_model h) b →
      ρ.density =ᵐ[haar 1] (polynomialChartAbsolute h
        ((h * z.1.1) • cosC2_STR02915 + (h * z.1.2) • sinC2_STR02915 +
          (ψ (polynomialScaledParameters (h, (z.1.1, z.1.2, z.2, σ))) : PeriodicC2_STR02969))).density →
      polynomialFactorCriticalSystem ψ ((h, σ), z) = 0 := by
  obtain ⟨O, hO, h0O, hOU, _hC, hfactor, _hz, _hlim⟩ :=
    polynomialScaledDeficitFactor_identified hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst
  refine ⟨O, hO, h0O, hOU, ?_⟩
  intro h σ z b ρ hh hp hs hr hG hmin hρ
  let r := (scalarRate (canonical_elementary_polynomial_model h) b).toReal
  let c := fun x : ℝ × ℝ => (x.1, x.2, z.2, σ)
  let L := fun x : ℝ × ℝ =>
    (h * x.1) • cosC2_STR02915 + (h * x.2) • sinC2_STR02915 +
      (ψ (polynomialScaledParameters (h, c x)) : PeriodicC2_STR02969)
  let F := fun x : ℝ × ℝ => polynomialScaledDeficitFactor ψ (h, c x)
  have hfour : 0 < h ^ 4 := by
    have hsq := sq_pos_of_ne_zero hh
    nlinarith only [sq_pos_of_pos hsq]
  have hactual (x : ℝ × ℝ) : polynomialScaledDeficit ψ (h, c x) =
      polynomialChartDeficit h r (L x) := by
    change polynomialRangeDeficit (h, h ^ 4 * σ) (a0 * (1 + h ^ 2 * z.2)) (L x) = _
    rw [hs, hr, polynomialRangeDeficit_actual]
  obtain ⟨hz, hn⟩ := polynomial_minimizer_deficit_zero_and_nonnegative h b ρ hG hmin
  have hμ : (densityMeasure (polynomialChartAbsolute h (L z.1)) : Measure (Torus 1)) =
      (densityMeasure ρ : Measure (Torus 1)) :=
    (densityMeasure_eq_iff_STR02901 _ _).2 hρ.symm
  have hvar : polynomialVariationalDeficit h r (polynomialChartAbsolute h (L z.1)) =
      polynomialVariationalDeficit h r ρ := by
    unfold polynomialVariationalDeficit
    rw [hμ]
  have hDz : polynomialChartDeficit h r (L z.1) = 0 := by
    rw [← polynomialChartAbsolute_deficit h r b (L z.1),
      ← polynomialVariationalDeficit_eq h r b (polynomialChartAbsolute h (L z.1)),
      hvar, polynomialVariationalDeficit_eq h r b ρ]
    exact hz
  have hFz : F z.1 = 0 := by
    have he := hfactor h (c z.1) hp
    rw [hactual, hDz] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hfour.ne'
  have hmem : ∀ᶠ x in 𝓝 z.1, (h, c x) ∈ O :=
    (show ContinuousAt (fun x : ℝ × ℝ => (h, c x)) z.1 by
      dsimp only [c]; fun_prop).tendsto.eventually (hO.mem_nhds hp)
  have hloc : IsLocalMin F z.1 := by
    filter_upwards [hmem] with x hx
    rw [hFz]
    have hnon : 0 ≤ polynomialChartDeficit h r (L x) := by
      rw [← polynomialChartAbsolute_deficit h r b (L x)]
      exact hn (polynomialChartAbsolute h (L x))
    rw [← hactual x, hfactor h (c x) hx] at hnon
    exact (mul_le_mul_iff_right₀ hfour).1 (by simpa only [mul_zero] using hnon)
  have hD : fderiv ℝ F z.1 = 0 := hloc.fderiv_eq_zero
  change ((fderiv ℝ F z.1 (1, 0), fderiv ℝ F z.1 (0, 1)), F z.1) = 0
  rw [hD, hFz]
  rfl

/-- Actual all-competitor nonnegativity, including zero-gap competitors. -/
theorem polynomial_scalarMinimizer_scaled_factor_nonnegative
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0) (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0) :
    ∃ O : Set (ℝ × PolynomialScaledCoefficients), IsOpen O ∧
      (∀ c, ((0 : ℝ), c) ∈ O) ∧ O ⊆ polynomialScaledParameters ⁻¹' U ∧
      ∀ (h σ α : ℝ)
        (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (ρ : AbsoluteDensity 1),
      h ≠ 0 → h ^ 4 * σ = root_EX054 h →
      a0 * (1 + h ^ 2 * α) = (scalarRate (canonical_elementary_polynomial_model h) b).toReal →
      0 < scalarGap (canonical_elementary_polynomial_model h) ρ →
      scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
        scalarRate (canonical_elementary_polynomial_model h) b →
      ∀ a b' : ℝ, (h, (a, b', α, σ)) ∈ O →
        0 ≤ polynomialScaledDeficitFactor ψ (h, (a, b', α, σ)) := by
  obtain ⟨O, hO, h0O, hOU, _hC, hfactor, _hz, _hlim⟩ :=
    polynomialScaledDeficitFactor_identified hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst
  refine ⟨O, hO, h0O, hOU, ?_⟩
  intro h σ α b ρ hh hs hr hG hmin a b' hp
  let r := (scalarRate (canonical_elementary_polynomial_model h) b).toReal
  let u := (h * a) • cosC2_STR02915 + (h * b') • sinC2_STR02915 +
    (ψ (polynomialScaledParameters (h, (a, b', α, σ))) : PeriodicC2_STR02969)
  have hfour : 0 < h ^ 4 := by
    have hsq := sq_pos_of_ne_zero hh
    nlinarith only [sq_pos_of_pos hsq]
  have hactual : polynomialScaledDeficit ψ (h, (a, b', α, σ)) =
      polynomialChartDeficit h r u := by
    change polynomialRangeDeficit (h, h ^ 4 * σ) (a0 * (1 + h ^ 2 * α)) u = _
    rw [hs, hr, polynomialRangeDeficit_actual]
  have hn := (polynomial_minimizer_deficit_zero_and_nonnegative h b ρ hG hmin).2
  have hnon : 0 ≤ polynomialChartDeficit h r u := by
    rw [← polynomialChartAbsolute_deficit h r b u]
    exact hn (polynomialChartAbsolute h u)
  rw [← hactual, hfactor h (a, b', α, σ) hp] at hnon
  exact (mul_le_mul_iff_right₀ hfour).1 (by simpa only [mul_zero] using hnon)

/-- Every limiting polynomial inherits all-competitor nonnegativity from the actual original minimizers. -/
theorem polynomial_scalarMinimizer_limiting_factor_nonnegative
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0) (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (h α σ : ℕ → ℝ) (α₀ σ₀ : ℝ)
    (hh : Tendsto h atTop (𝓝 0)) (hα : Tendsto α atTop (𝓝 α₀))
    (hσ : Tendsto σ atTop (𝓝 σ₀))
    (b : ∀ n, AbsoluteDrift (canonical_elementary_polynomial_model (h n)))
    (ρ : ℕ → AbsoluteDensity 1)
    (hne : ∀ n, h n ≠ 0) (hs : ∀ n, (h n) ^ 4 * σ n = root_EX054 (h n))
    (hr : ∀ n, a0 * (1 + (h n) ^ 2 * α n) =
      (scalarRate (canonical_elementary_polynomial_model (h n)) (b n)).toReal)
    (hG : ∀ n, 0 < scalarGap (canonical_elementary_polynomial_model (h n)) (ρ n))
    (hmin : ∀ n, scalarQuotient (canonical_elementary_polynomial_model (h n)) (b n) (ρ n) =
      scalarRate (canonical_elementary_polynomial_model (h n)) (b n)) :
    ∀ a b' : ℝ, 0 ≤ polynomialScaledQuartic (a, b', α₀, σ₀) := by
  obtain ⟨O, hO, h0O, _hOU, hnon⟩ :=
    polynomial_scalarMinimizer_scaled_factor_nonnegative hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst
  obtain ⟨V, hV, h0V, _hVU, hC, _hfactor, hz, _hlim⟩ :=
    polynomialScaledDeficitFactor_identified hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst
  intro a b'
  let c : PolynomialScaledCoefficients := (a, b', α₀, σ₀)
  have hq : Tendsto (fun n => (h n, (a, b', α n, σ n))) atTop (𝓝 (0, c)) :=
    hh.prodMk_nhds (tendsto_const_nhds.prodMk_nhds (tendsto_const_nhds.prodMk_nhds (hα.prodMk_nhds hσ)))
  have hmem : ∀ᶠ n in atTop, (h n, (a, b', α n, σ n)) ∈ O :=
    hq.eventually (hO.mem_nhds (h0O c))
  have hnon' : ∀ᶠ n in atTop, 0 ≤ polynomialScaledDeficitFactor ψ (h n, (a, b', α n, σ n)) := by
    filter_upwards [hmem] with n hn
    exact hnon (h n) (σ n) (α n) (b n) (ρ n) (hne n) (hs n) (hr n) (hG n) (hmin n) a b' hn
  have hF := ((hC.contDiffAt (hV.mem_nhds (h0V c))).continuousAt.tendsto).comp hq
  rw [hz c] at hF
  exact ge_of_tendsto hF hnon'

/-- Actual annular subsequence capture. The nonzero limiting amplitude is stated explicitly; uniform exclusion of the origin is a separate obligation. -/
theorem polynomial_scalarMinimizer_annular_limit_capture
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0) (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (h A B α σ : ℕ → ℝ) (A₀ B₀ α₀ σ₀ : ℝ)
    (hh : Tendsto h atTop (𝓝 0)) (hA : Tendsto A atTop (𝓝 A₀))
    (hB : Tendsto B atTop (𝓝 B₀)) (hα : Tendsto α atTop (𝓝 α₀))
    (hσ : Tendsto σ atTop (𝓝 σ₀)) (hAnn : 0 < A₀ ^ 2 + B₀ ^ 2)
    (b : ∀ n, AbsoluteDrift (canonical_elementary_polynomial_model (h n)))
    (ρ : ℕ → AbsoluteDensity 1)
    (hne : ∀ n, h n ≠ 0) (hs : ∀ n, (h n) ^ 4 * σ n = root_EX054 (h n))
    (hr : ∀ n, a0 * (1 + (h n) ^ 2 * α n) =
      (scalarRate (canonical_elementary_polynomial_model (h n)) (b n)).toReal)
    (hG : ∀ n, 0 < scalarGap (canonical_elementary_polynomial_model (h n)) (ρ n))
    (hmin : ∀ n, scalarQuotient (canonical_elementary_polynomial_model (h n)) (b n) (ρ n) =
      scalarRate (canonical_elementary_polynomial_model (h n)) (b n))
    (hρ : ∀ n, (ρ n).density =ᵐ[haar 1] (polynomialChartAbsolute (h n)
      ((h n * A n) • cosC2_STR02915 + (h n * B n) • sinC2_STR02915 +
        (ψ (polynomialScaledParameters (h n, (A n, B n, α n, σ n))) : PeriodicC2_STR02969))).density) :
    α₀ = (3 - Real.sqrt 2) / 24 ∧
      A₀ = -(1 + Real.sqrt 2) / 2 ∧ B₀ ^ 2 = (1 + Real.sqrt 2) / 4 := by
  have hnon := polynomial_scalarMinimizer_limiting_factor_nonnegative
    hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst
    h α σ α₀ σ₀ hh hα hσ b ρ hne hs hr hG hmin
  obtain ⟨O, hO, h0O, _hOU, hcritical⟩ :=
    polynomial_scalarMinimizer_scaled_critical hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst
  obtain ⟨V, hV, h0V, _hVU, hC, _hfactor, hz, _hlim⟩ :=
    polynomialScaledDeficitFactor_identified hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst
  let c : PolynomialScaledCoefficients := (A₀, B₀, α₀, σ₀)
  have hq : Tendsto (fun n => (h n, (A n, B n, α n, σ n))) atTop (𝓝 (0, c)) :=
    hh.prodMk_nhds (hA.prodMk_nhds (hB.prodMk_nhds (hα.prodMk_nhds hσ)))
  have hmem : ∀ᶠ n in atTop, (h n, (A n, B n, α n, σ n)) ∈ O :=
    hq.eventually (hO.mem_nhds (h0O c))
  have he : ∀ᶠ n in atTop, polynomialScaledDeficitFactor ψ (h n, (A n, B n, α n, σ n)) = 0 := by
    filter_upwards [hmem] with n hn
    have heq := hcritical (h n) (σ n) ((A n, B n), α n) (b n) (ρ n)
      (hne n) hn (hs n) (hr n) (hG n) (hmin n) (hρ n)
    exact congrArg Prod.snd heq
  have hF := ((hC.contDiffAt (hV.mem_nhds (h0V c))).continuousAt.tendsto).comp hq
  rw [hz c] at hF
  have hFzero : Tendsto (fun n => polynomialScaledDeficitFactor ψ (h n, (A n, B n, α n, σ n)))
      atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds.congr' (he.mono (fun n hn => hn.symm))
  have hval : polynomialScaledQuartic c = 0 := tendsto_nhds_unique hF hFzero
  exact polynomialScaledQuartic_variational_capture A₀ B₀ α₀ σ₀ hAnn hval hnon

/-- Exact zero-amplitude value and gradient for the actual factor at every nonzero field in its domain. -/
theorem polynomialScaledDeficitFactor_amplitude_origin
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0) (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0) :
    ∃ O : Set (ℝ × PolynomialScaledCoefficients), IsOpen O ∧
      (∀ c, ((0 : ℝ), c) ∈ O) ∧
      ∀ h α σ : ℝ, h ≠ 0 → (h, (0, 0, α, σ)) ∈ O →
      polynomialScaledDeficitFactor ψ (h, (0, 0, α, σ)) = 0 ∧
      fderiv ℝ (fun x : ℝ × ℝ => polynomialScaledDeficitFactor ψ (h, (x.1, x.2, α, σ))) 0 = 0 := by
  obtain ⟨O, hO, h0O, hOU, hC, hfactor, _hz, _hlim⟩ :=
    polynomialScaledDeficitFactor_identified hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst
  refine ⟨O, hO, h0O, ?_⟩
  intro h α σ hh hp
  let θ : (ℝ × ℝ) × ℝ := ((h, h ^ 4 * σ), h ^ 2 * α)
  let f := fun x : ℝ × ℝ => polynomialReducedDeficit ψ (polynomialGapSlice θ x)
  let F := fun x : ℝ × ℝ => polynomialScaledDeficitFactor ψ (h, (x.1, x.2, α, σ))
  let D := fun x : ℝ × ℝ => polynomialScaledDeficit ψ (h, (x.1, x.2, α, σ))
  have hp0 : polynomialGapSlice θ 0 ∈ U := by
    simpa [polynomialScaledParameters, polynomialGapSlice, θ] using hOU hp
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, polynomialGapSlice θ (t • (0 : ℝ × ℝ)) ∈ U := by
    intro t ht
    simpa only [smul_zero] using hp0
  obtain ⟨hf0, hdf0, _hTaylor⟩ := polynomialReducedDeficit_quadratic_factor hU hψ hzero θ 0 hseg
  change f 0 = 0 at hf0
  change fderiv ℝ f 0 = 0 at hdf0
  have hq : ContDiff ℝ ∞ (polynomialGapSlice θ) := by unfold polynomialGapSlice; fun_prop
  have hf : DifferentiableAt ℝ f 0 :=
    (((polynomialReducedDeficit_smooth hψ).contDiffAt (hU.mem_nhds hp0)).comp 0 hq.contDiffAt).differentiableAt (by simp)
  have hscale : DifferentiableAt ℝ (fun x : ℝ × ℝ => h • x) 0 := by fun_prop
  have hD : D = f ∘ (fun x : ℝ × ℝ => h • x) := rfl
  have hD0 : D 0 = 0 := by rw [hD, Function.comp_apply, smul_zero, hf0]
  have hDd : fderiv ℝ D 0 = 0 := by
    rw [hD, fderiv_comp 0 (by simpa only [smul_zero] using hf) hscale, smul_zero, hdf0]
    exact ContinuousLinearMap.zero_comp _
  have hfour : h ^ 4 ≠ 0 := pow_ne_zero _ hh
  have hvalue := hfactor h (0, 0, α, σ) hp
  change D 0 = h ^ 4 * F 0 at hvalue
  have hF0 : F 0 = 0 := (mul_eq_zero.mp (hvalue.symm.trans hD0)).resolve_left hfour
  have hc : ContDiff ℝ ∞ (fun x : ℝ × ℝ => (h, (x.1, x.2, α, σ))) := by fun_prop
  have hFC : ContDiffAt ℝ ∞ (polynomialScaledDeficitFactor ψ) (h, (0, 0, α, σ)) := hC.contDiffAt (hO.mem_nhds hp)
  have hF : DifferentiableAt ℝ F 0 := by
    exact (hFC.comp (f := fun x : ℝ × ℝ => (h, (x.1, x.2, α, σ))) (0 : ℝ × ℝ) hc.contDiffAt).differentiableAt (by simp)
  have hmem : ∀ᶠ x : ℝ × ℝ in 𝓝 0, (h, (x.1, x.2, α, σ)) ∈ O :=
    hc.continuous.continuousAt.tendsto.eventually (hO.mem_nhds hp)
  have he : D =ᶠ[𝓝 (0 : ℝ × ℝ)] fun x => h ^ 4 * F x := by
    filter_upwards [hmem] with x hx
    exact hfactor h (x.1, x.2, α, σ) hx
  have hder : fderiv ℝ D 0 = h ^ 4 • fderiv ℝ F 0 :=
    he.fderiv_eq.trans (hF.hasFDerivAt.const_mul (h ^ 4)).fderiv
  have hFd : fderiv ℝ F 0 = 0 := by
    have hsm : h ^ 4 • fderiv ℝ F 0 = 0 := hder.symm.trans hDd
    exact (smul_eq_zero.mp hsm).resolve_left hfour
  exact ⟨hF0, hFd⟩

end DGPS.Examples.PolynomialSpecies
