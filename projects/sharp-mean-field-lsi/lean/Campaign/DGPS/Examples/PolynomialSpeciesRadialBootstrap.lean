import DGPS.Examples.PolynomialSpeciesRateRadialControl
import DGPS.Examples.PolynomialSpeciesOriginRadialLower
import DGPS.Examples.PolynomialSpeciesFieldRadialControl
import DGPS.Examples.PolynomialHaarTrialBounds
import DGPS.Examples.PolynomialMinimizerGraphEntry

/-! Simultaneous actual amplitude and rate scaling on ONE retained graph.
The numerical inequality is derived from actual origin/field/rate radial
producers and the original-domain Haar trial. Every-minimizer box entry and
stationarity are derived from their genuine variational producers. -/

noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ENNReal ContDiff
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium
open DGPS.Circle.AngularNormalization

namespace DGPS.Examples.PolynomialSpecies

/-- One numerical constant controls amplitude and negative rate shift
SIMULTANEOUSLY. The inequality is an explicit numerical input; this does not
assert that the actual model satisfies it without its analytic producers. -/
theorem polynomial_radial_scale_absorption {c d C K : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hK : 0 ≤ K) :
    ∃ M : ℝ, 0 < M ∧ ∀ h R g : ℝ, 0 < h → 0 ≤ R → 0 ≤ g →
      c * R ^ 2 + d * g ≤ C * h * R + K * h ^ 2 →
        R ≤ M * h ∧ g ≤ M * h ^ 2 := by
  let B := K + C ^ 2 / (2 * c) + 1
  let N := 2 * B / c
  let Q := B / d
  let M := N + Q + 1
  have hB : 0 < B := by
    dsimp only [B]
    have he := div_nonneg (sq_nonneg C) (mul_pos (by norm_num : (0 : ℝ) < 2) hc).le
    linarith
  have hN : 0 ≤ N := div_nonneg (mul_nonneg (by norm_num) hB.le) hc.le
  have hQ : 0 ≤ Q := div_nonneg hB.le hd.le
  have hM1 : 1 ≤ M := by dsimp only [M]; linarith
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  refine ⟨M, hM, fun h R g hh hR hg hineq => ?_⟩
  have hyoung : C * h * R ≤ c / 2 * R ^ 2 + C ^ 2 / (2 * c) * h ^ 2 := by
    have he : c ^ 2 * R ^ 2 + C ^ 2 * h ^ 2 =
        (2 * c) * (c / 2 * R ^ 2 + C ^ 2 / (2 * c) * h ^ 2) := by
      field_simp [hc.ne']
      <;> ring
    have hm : (2 * c) * (C * h * R) ≤
        (2 * c) * (c / 2 * R ^ 2 + C ^ 2 / (2 * c) * h ^ 2) := by
      rw [← he]
      nlinarith only [sq_nonneg (c * R - C * h)]
    exact (mul_le_mul_iff_right₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hc)).1 hm
  have hbudget : c / 2 * R ^ 2 + d * g ≤ B * h ^ 2 := by
    have he : c / 2 * R ^ 2 + d * g ≤ (K + C ^ 2 / (2 * c)) * h ^ 2 := by
      nlinarith only [hineq, hyoung]
    have hb : K + C ^ 2 / (2 * c) ≤ B := by dsimp only [B]; linarith
    exact he.trans (mul_le_mul_of_nonneg_right hb (sq_nonneg h))
  have hR2 : R ^ 2 ≤ N * h ^ 2 := by
    have hm : R ^ 2 * c ≤ 2 * B * h ^ 2 := by
      nlinarith only [hbudget, mul_nonneg hd.le hg]
    calc
      R ^ 2 ≤ (2 * B * h ^ 2) / c := (le_div_iff₀ hc).2 hm
      _ = _ := by dsimp only [N]; ring
  have hg2 : g ≤ Q * h ^ 2 := by
    have hm : g * d ≤ B * h ^ 2 := by
      nlinarith only [hbudget, mul_nonneg (div_nonneg hc.le (by norm_num : (0 : ℝ) ≤ 2)) (sq_nonneg R)]
    calc
      g ≤ (B * h ^ 2) / d := (le_div_iff₀ hd).2 hm
      _ = _ := by dsimp only [Q]; ring
  have hNM : N ≤ M := by dsimp only [M]; linarith
  have hQM : Q ≤ M := by dsimp only [M]; linarith
  have hMM : M ≤ M ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hM1 hM.le
    nlinarith only [hm]
  have hbound := hR2.trans (mul_le_mul_of_nonneg_right (hNM.trans hMM) (sq_nonneg h))
  refine ⟨?_, hg2.trans (mul_le_mul_of_nonneg_right hQM (sq_nonneg h))⟩
  apply (sq_le_sq₀ hR (mul_nonneg hM.le hh.le)).mp
  nlinarith only [hbound]


/-- The actual stationary-chart bridge. Origin/field/rate radial estimates are
proved by their producers; none is assumed as a numerical model hypothesis. -/
theorem polynomial_scalar_stationary_graph_scale
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hamp : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (henv : ∀ a b h γ : ℝ,
      ((a, b, (h, root_EX054 h), γ) : PolynomialRangeParameters) ∈ U →
      HasDerivAt (fun τ : ℝ => polynomialChartDeficit h (a0 * (1 + τ))
        (a • cosC2_STR02915 + b • sinC2_STR02915 +
          (ψ (a, b, (h, root_EX054 h), τ) : PeriodicC2_STR02969)))
        (-2 * a0 * polynomialChartGap h
          (a • cosC2_STR02915 + b • sinC2_STR02915 +
            (ψ (a, b, (h, root_EX054 h), γ) : PeriodicC2_STR02969))) γ) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧ ∀ (h : ℝ)
      (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (x : ℝ × ℝ),
      0 < h → h < δ →
      let γ := (scalarRate (canonical_elementary_polynomial_model h) b).toReal / a0 - 1
      ‖(((h, root_EX054 h), γ), x)‖ < δ →
      ((x.1, x.2, (h, root_EX054 h), γ) : PolynomialRangeParameters) ∈ U →
      0 < scalarGap (canonical_elementary_polynomial_model h)
        (polynomialChartAbsolute h (polynomialGapLift ψ ((h, root_EX054 h), γ) x)) →
      polynomialReducedDeficitRadial ψ ((h, root_EX054 h), γ) x = 0 →
      Real.sqrt (x.1 ^ 2 + x.2 ^ 2) ≤ M * h ∧ |γ| ≤ M * h ^ 2 := by
  have hψ0 : ψ (0 : PolynomialRangeParameters) = 0 := hzero 0 0 0 h0U
  obtain ⟨δO, hδO, hOrigin⟩ := polynomial_origin_same_graph_radial_quartic_lower
    hU h0U hN h0N hψ hψN hgraph hzero hamp
  obtain ⟨δF, C, hδF, hC, hField⟩ := polynomialReducedDeficitRadial_field_lower
    hU h0U hN h0N hψ hψ0 hψN hgraph hzero
  obtain ⟨δR, hδR, hRate⟩ := polynomialSelectedDeficit_radial_rate_control
    hU h0U hψ hzero hamp henv
  obtain ⟨Cs, δs, hCs, hδs, hroot⟩ := abs_root_le_sixth_EX054
  obtain ⟨δT, hδT, hTrial⟩ := polynomial_haar_trial_strict_upper
  let c := a0 / 768
  let d := a0 / 2
  let Cg : ℝ := 5 / 48
  let K := C * (1 + Cs) + (3 * a0 / 2) * Cg
  have hc : 0 < c := div_pos a0_pos (by norm_num)
  have hd : 0 < d := div_pos a0_pos (by norm_num)
  have hCg : 0 < Cg := by norm_num [Cg]
  have ha0 : 0 < a0 := a0_pos
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  obtain ⟨M0, hM0, hAbsorb⟩ := polynomial_radial_scale_absorption (C := C) hc hd hK
  let M := M0 + Cg + 1
  have hM : 0 < M := by dsimp only [M]; positivity
  let δ := min 1 (min δO (min δF (min δR (min δs δT))))
  have hδ : 0 < δ := lt_min one_pos (lt_min hδO (lt_min hδF (lt_min hδR (lt_min hδs hδT))))
  refine ⟨δ, M, hδ, hM, fun h b x hh hsmall => ?_⟩
  let γ := (scalarRate (canonical_elementary_polynomial_model h) b).toReal / a0 - 1
  dsimp only
  intro hbox hp hGap hE
  change ‖(((h, root_EX054 h), γ), x)‖ < δ at hbox
  change ((x.1, x.2, (h, root_EX054 h), γ) : PolynomialRangeParameters) ∈ U at hp
  change 0 < scalarGap (canonical_elementary_polynomial_model h)
    (polynomialChartAbsolute h (polynomialGapLift ψ ((h, root_EX054 h), γ) x)) at hGap
  change polynomialReducedDeficitRadial ψ ((h, root_EX054 h), γ) x = 0 at hE
  change Real.sqrt (x.1 ^ 2 + x.2 ^ 2) ≤ M * h ∧ |γ| ≤ M * h ^ 2
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδO' : δ ≤ δO := (min_le_right _ _).trans (min_le_left _ _)
  have hδF' : δ ≤ δF := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδR' : δ ≤ δR := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδs' : δ ≤ δs := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hδT' : δ ≤ δT := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hh1 : h ≤ 1 := hsmall.le.trans hδ1
  have hnormx : ‖x‖ ≤ ‖(((h, root_EX054 h), γ), x)‖ := by
    rw [Prod.norm_def]
    exact le_max_right _ _
  have hnorm0 : ‖(((h, root_EX054 h), (0 : ℝ)), x)‖ ≤ ‖(((h, root_EX054 h), γ), x)‖ := by
    simp only [Prod.norm_def]
    exact max_le_max (max_le_max le_rfl (by simp)) le_rfl
  let R := Real.sqrt (x.1 ^ 2 + x.2 ^ 2)
  have hR2 : R ^ 2 = x.1 ^ 2 + x.2 ^ 2 := Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hRp : 0 < R := Real.sqrt_pos.2 (polynomialSelectedGap_positive_amplitude hzero h γ x b hp hGap)
  have hO := hOrigin x (hnormx.trans_lt (hbox.trans_le hδO'))
  have hF := hField h (root_EX054 h) x (hnorm0.trans_lt (hbox.trans_le hδF'))
  have hR := hRate h γ x (hbox.trans_le hδR')
  dsimp only at hF
  change polynomialReducedDeficitRadial ψ ((0, 0), 0) x - C * |h| * R ^ 3 -
    C * (h ^ 2 + |root_EX054 h|) * R ^ 2 ≤ polynomialReducedDeficitRadial ψ ((h, root_EX054 h), 0) x at hF
  rw [abs_of_pos hh] at hF
  rw [← hR2] at hO hR
  change c * (R ^ 2) ^ 2 ≤ polynomialReducedDeficitRadial ψ ((0, 0), 0) x at hO
  have hs0 := hroot h (by rw [abs_of_pos hh]; exact hsmall.le.trans hδs')
  have hh4 : h ^ 4 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hh.le hh1 4
  have hh6 : h ^ 6 ≤ h ^ 2 := by
    have he := mul_le_mul_of_nonneg_right hh4 (sq_nonneg h)
    nlinarith only [he]
  have hs2 : |root_EX054 h| ≤ Cs * h ^ 2 :=
    hs0.trans (mul_le_mul_of_nonneg_left hh6 hCs.le)
  obtain ⟨hTG, hTQ⟩ := hTrial h hh (hsmall.le.trans hδT') b
  have hrate : scalarRate (canonical_elementary_polynomial_model h) b ≤
      ENNReal.ofReal (a0 * (1 + 5 * h ^ 2 / 48)) :=
    ((scalarRate_le_quotient _ _ _ hTG).trans_lt hTQ).le
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hrate
  have hreal := ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg a0_pos.le (by positivity : 0 ≤ 1 + 5 * h ^ 2 / 48)) hrate
  have hγ : γ ≤ Cg * h ^ 2 := by
    have he : (scalarRate (canonical_elementary_polynomial_model h) b).toReal / a0 ≤
        1 + 5 * h ^ 2 / 48 := (div_le_iff₀ a0_pos).2 (by nlinarith only [hreal])
    dsimp only [γ, Cg]
    nlinarith only [he]
  have hgp : max γ 0 ≤ Cg * h ^ 2 := max_le hγ (mul_nonneg hCg.le (sq_nonneg h))
  have hS : C * (h ^ 2 + |root_EX054 h|) * R ^ 2 ≤ C * (1 + Cs) * h ^ 2 * R ^ 2 := by
    have he : h ^ 2 + |root_EX054 h| ≤ (1 + Cs) * h ^ 2 := by nlinarith only [hs2]
    have hm := mul_le_mul_of_nonneg_left he (mul_nonneg hC.le (sq_nonneg R))
    nlinarith only [hm]
  have hP : (3 * a0 / 2) * max γ 0 * R ^ 2 ≤ (3 * a0 / 2) * Cg * h ^ 2 * R ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hgp
      (show 0 ≤ (3 * a0 / 2) * R ^ 2 by positivity)
    nlinarith only [hm]
  have hcoerc : c * R ^ 4 + d * max (-γ) 0 * R ^ 2 ≤ C * h * R ^ 3 + K * h ^ 2 * R ^ 2 := by
    dsimp only [d, K]
    nlinarith only [hO, hF, hR, hE, hS, hP]
  have hmul : (c * R ^ 2 + d * max (-γ) 0) * R ^ 2 ≤ (C * h * R + K * h ^ 2) * R ^ 2 := by
    nlinarith only [hcoerc]
  have hclear := (mul_le_mul_iff_left₀ (sq_pos_of_pos hRp)).1 hmul
  obtain ⟨hAmp, hNeg⟩ := hAbsorb h R (max (-γ) 0) hh hRp.le (le_max_right _ _) hclear
  have hM0 : M0 ≤ M := by dsimp only [M]; linarith
  have hMCg : Cg ≤ M := by dsimp only [M]; linarith
  refine ⟨hAmp.trans (mul_le_mul_of_nonneg_right hM0 hh.le), ?_⟩
  rcases le_total (0 : ℝ) γ with hg | hg
  · rw [abs_of_nonneg hg]
    exact hγ.trans (mul_le_mul_of_nonneg_right hMCg (sq_nonneg h))
  · rw [abs_of_nonpos hg]
    have hn : -γ ≤ M0 * h ^ 2 := by
      simpa only [max_eq_left (neg_nonneg.mpr hg)] using hNeg
    exact hn.trans (mul_le_mul_of_nonneg_right hM0 (sq_nonneg h))

private theorem same_measure_gap (A : InteractionData 1) (ρ σ : AbsoluteDensity 1)
    (hμ : (densityMeasure ρ : Measure (Torus 1)) = densityMeasure σ) :
    scalarGap A ρ = scalarGap A σ := by
  have hprob : densityMeasure ρ = densityMeasure σ := Subtype.ext hμ
  apply NNReal.coe_injective
  change densityFreeEnergy A ρ - freeEnergyMinimumReal A = densityFreeEnergy A σ - freeEnergyMinimumReal A
  congr 1
  apply EReal.coe_injective
  rw [coe_densityFreeEnergy, coe_densityFreeEnergy, hprob]

private theorem gapLift_differentiable_at {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (θ : (ℝ × ℝ) × ℝ) (x : ℝ × ℝ)
    (hp : polynomialGapSlice θ x ∈ U) :
    DifferentiableAt ℝ (polynomialGapLift ψ θ) x := by
  have hs : ContDiff ℝ ∞ (polynomialGapSlice θ) := by
    unfold polynomialGapSlice
    fun_prop
  have hΦ := ((hψ.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).comp x
    (hs.differentiable (by simp) x)
  have hE : DifferentiableAt ℝ (fun y : ℝ × ℝ =>
      (ψ (polynomialGapSlice θ y) : PeriodicC2_STR02969)) x :=
    E_STR02969.subtypeL.differentiableAt.comp x hΦ
  have hlin : DifferentiableAt ℝ (fun y : ℝ × ℝ =>
      y.1 • cosC2_STR02915 + y.2 • sinC2_STR02915) x := by fun_prop
  have hL : DifferentiableAt ℝ (polynomialGapLift ψ θ) x := hlin.add hE
  exact hL

private theorem chartDeficit_smooth_fixed (h r : ℝ) :
    ContDiff ℝ ∞ (polynomialChartDeficit h r) := by
  let P : PeriodicC2_STR02969 → PolynomialEulerInput := fun v => ((h, root_EX054 h), r, v)
  have hP : ContDiff ℝ ∞ P := by
    exact contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have hsm := polynomialRangeDeficit_smooth.comp hP
  have hactual : (fun v : PeriodicC2_STR02969 => polynomialRangeDeficit (h, root_EX054 h) r v) =
      polynomialChartDeficit h r := funext fun v => polynomialRangeDeficit_actual h r v
  change ContDiff ℝ ∞ (fun v : PeriodicC2_STR02969 => polynomialRangeDeficit (h, root_EX054 h) r v) at hsm
  rw [hactual] at hsm
  exact hsm

private theorem minimizer_radial_zero {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (ρ : AbsoluteDensity 1)
    (hG : 0 < scalarGap (canonical_elementary_polynomial_model h) ρ)
    (hmin : scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
      scalarRate (canonical_elementary_polynomial_model h) b) (x : ℝ × ℝ) :
    let γ := (scalarRate (canonical_elementary_polynomial_model h) b).toReal / a0 - 1
    ((x.1, x.2, (h, root_EX054 h), γ) : PolynomialRangeParameters) ∈ U →
    ρ.density =ᵐ[haar 1]
      (polynomialChartAbsolute h (polynomialGapLift ψ ((h, root_EX054 h), γ) x)).density →
    polynomialReducedDeficitRadial ψ ((h, root_EX054 h), γ) x = 0 := by
  let r := (scalarRate (canonical_elementary_polynomial_model h) b).toReal
  let γ := r / a0 - 1
  let θ : (ℝ × ℝ) × ℝ := ((h, root_EX054 h), γ)
  let u := polynomialGapLift ψ θ x
  dsimp only
  intro hp hu
  change polynomialGapSlice θ x ∈ U at hp
  change ρ.density =ᵐ[haar 1] (polynomialChartAbsolute h u).density at hu
  change polynomialReducedDeficitRadial ψ θ x = 0
  have hcrit := polynomial_scalarMinimizer_chart_fderiv_zero h b ρ hG hmin u hu
  change fderiv ℝ (polynomialChartDeficit h r) u = 0 at hcrit
  have hL := gapLift_differentiable_at hU hψ θ x hp
  have hsm := chartDeficit_smooth_fixed h r
  have hphys : a0 * (1 + γ) = r := by
    dsimp only [γ]
    field_simp [a0_pos.ne']
    <;> ring
  have hfun : (fun y : ℝ × ℝ => polynomialRangeDeficit θ.1 (a0 * (1 + θ.2))
      (polynomialGapLift ψ θ y)) = polynomialChartDeficit h r ∘ polynomialGapLift ψ θ := by
    funext y
    change polynomialRangeDeficit (h, root_EX054 h) (a0 * (1 + γ)) _ = _
    rw [polynomialRangeDeficit_actual, hphys]
    rfl
  unfold polynomialReducedDeficitRadial
  change (fderiv ℝ (fun y : ℝ × ℝ => polynomialRangeDeficit θ.1 (a0 * (1 + θ.2)) (polynomialGapLift ψ θ y)) x) x = 0
  rw [hfun, fderiv_comp x (hsm.differentiable (by simp) u) hL, hcrit]
  simp

/-- Every sufficiently small positive field and EVERY original absolute-domain
scalar minimizer have a SAME-graph amplitude of order h and rate shift of order
h squared. Small-box entry and stationarity are conclusions of their actual
variational producers, rather than hypotheses of this final scale factory. -/
theorem polynomial_scalarMinimizer_same_graph_scale
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hamp : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (henv : ∀ a b h γ : ℝ,
      ((a, b, (h, root_EX054 h), γ) : PolynomialRangeParameters) ∈ U →
      HasDerivAt (fun τ : ℝ => polynomialChartDeficit h (a0 * (1 + τ))
        (a • cosC2_STR02915 + b • sinC2_STR02915 +
          (ψ (a, b, (h, root_EX054 h), τ) : PeriodicC2_STR02969)))
        (-2 * a0 * polynomialChartGap h
          (a • cosC2_STR02915 + b • sinC2_STR02915 +
            (ψ (a, b, (h, root_EX054 h), γ) : PeriodicC2_STR02969))) γ) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h),
      ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (canonical_elementary_polynomial_model h) ρ →
      scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
        scalarRate (canonical_elementary_polynomial_model h) b →
      ∃ x : ℝ × ℝ,
        let γ := (scalarRate (canonical_elementary_polynomial_model h) b).toReal / a0 - 1
        ((x.1, x.2, (h, root_EX054 h), γ) : PolynomialRangeParameters) ∈ U ∧
        ρ.density =ᵐ[haar 1]
          (polynomialChartAbsolute h (polynomialGapLift ψ ((h, root_EX054 h), γ) x)).density ∧
        Real.sqrt (x.1 ^ 2 + x.2 ^ 2) ≤ M * h ∧ |γ| ≤ M * h ^ 2 := by
  obtain ⟨δS, M, hδS, hM, hscale⟩ := polynomial_scalar_stationary_graph_scale
    hU h0U hN h0N hψ hψN hgraph hzero hamp henv
  let V := U ∩ Metric.ball (0 : PolynomialRangeParameters) δS
  have hV : IsOpen V := hU.inter Metric.isOpen_ball
  have h0V : (0 : PolynomialRangeParameters) ∈ V :=
    ⟨h0U, by simpa only [Metric.mem_ball, dist_self] using hδS⟩
  have hgraphV : ∀ p ∈ V, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w :=
    fun p hp w hw => hgraph p hp.1 w hw
  obtain ⟨δE, hδE, hentry⟩ := polynomial_scalarMinimizer_graph_entry V N ψ hV h0V hN h0N hgraphV
  refine ⟨min δS δE, M, lt_min hδS hδE, hM, fun h hh hsmall b ρ hG hmin => ?_⟩
  obtain ⟨a, b', w, hp, hw, hψw, hρ⟩ := hentry h hh (hsmall.trans_le (min_le_right _ _)) b ρ hG hmin
  let x : ℝ × ℝ := (a, b')
  let γ := (scalarRate (canonical_elementary_polynomial_model h) b).toReal / a0 - 1
  let p : PolynomialRangeParameters := (a, b', (h, root_EX054 h), γ)
  change p ∈ V at hp
  change ψ p = w at hψw
  have hu : ρ.density =ᵐ[haar 1]
      (polynomialChartAbsolute h (polynomialGapLift ψ ((h, root_EX054 h), γ) x)).density := by
    change ρ.density =ᵐ[haar 1]
      (polynomialChartAbsolute h (a • cosC2_STR02915 + b' • sinC2_STR02915 +
        (ψ p : PeriodicC2_STR02969))).density
    rw [hψw]
    exact hρ
  have hpn : ‖p‖ < δS := by
    simpa only [Metric.mem_ball, dist_zero_right] using hp.2
  have hnorm : ‖(((h, root_EX054 h), γ), x)‖ < δS := by
    have he : ‖(((h, root_EX054 h), γ), x)‖ = ‖p‖ := by
      dsimp only [p, x]
      simp only [Prod.norm_def]
      ac_rfl
    rw [he]
    exact hpn
  have hμ : (densityMeasure ρ : Measure (Torus 1)) =
      densityMeasure (polynomialChartAbsolute h (polynomialGapLift ψ ((h, root_EX054 h), γ) x)) :=
    (densityMeasure_eq_iff_STR02901 _ _).2 hu
  have hGc : 0 < scalarGap (canonical_elementary_polynomial_model h)
      (polynomialChartAbsolute h (polynomialGapLift ψ ((h, root_EX054 h), γ) x)) := by
    rw [← same_measure_gap _ _ _ hμ]
    exact hG
  have hstationary := minimizer_radial_zero hU hψ h b ρ hG hmin x hp.1 hu
  obtain ⟨hAmp, hRate⟩ := hscale h b x hh (hsmall.trans_le (min_le_left _ _)) hnorm hp.1 hGc hstationary
  exact ⟨x, hp.1, hu, hAmp, hRate⟩

end DGPS.Examples.PolynomialSpecies
