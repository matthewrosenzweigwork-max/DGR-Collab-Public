import DGPS.Structural.FrozenGibbsIdentities
import DGPS.Structural.FrozenGibbsInformation
import DGPS.Variational.SpeciesGap
import DGPS.Variational.WeightedScoreInformation
import DGPS.Variational.SpeciesInclusion
import DGPS.Foundations.RateArithmetic

/-!
# Harmonic-mean scalar/species comparison (STR012)

For direct Lipschitz data `A` (`LipschitzData A`), `0 < d`, and `0 < r_* < ∞` with
`r_* = scalarRate A b`, let `ℓ = frozenLSRateInf A` (STR001: `0 < ℓ < ∞`).  Then

* `speciesDissipation_ge_harmonicMean_mul_gap`: every family `F` with `G_θ > 0` obeys
  `D_θ ≥ 2 (r_* ℓ / (r_* + ℓ)) G_θ`;
* `speciesRate_ge_harmonicMean_frozenLS`: `r_* ℓ / (r_* + ℓ) ≤ r_ms ≤ r_*`.

Proof: with `g = G(ρ̄)` and `S = ∑ θ_s H(ρ_s | ρ̄)` one has `G_θ = g + S` (DEF014),
`D_θ ≥ D(ρ̄) ≥ 2 r_* g` (DEF015 and the scalar rate), and, by STR002 and the frozen
logarithmic Sobolev inequality for `P = P(ρ̄ m)`,
`D_θ = ∑ θ_s I(ρ_s m | P) ≥ 2 ℓ ∑ θ_s H(ρ_s m | P) ≥ 2 ℓ S`, the last step by the real-level
chain rule `H(ρ_s | P) = H(ρ_s | m) - ∫ ρ_s log p` for the bounded reference `P = p m`.  Adding
`ℓ · (2 r_* g ≤ D_θ)` and `r_* · (2 ℓ S ≤ D_θ)` gives `2 r_* ℓ G_θ ≤ (r_* + ℓ) D_θ`.  The
inequality `r_ms ≤ r_*` is DEF030 (one species).  Neither equilibrium uniqueness nor Hessian
coercivity is used.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace DGPS.Structural

variable {d : ℕ}

/-! ### The frozen logarithmic Sobolev inequality in entropy-information form -/

/-- For `ν ≪ P`, the logarithmic Sobolev rate of `P` bounds the relative Fisher information below:
`2 r_LS(P) H(ν | P) ≤ I(ν | P)`. -/
theorem two_mul_lsRate_mul_relativeEntropy_le (P : BoundedPositiveReference d)
    (ν : Measure (Torus d)) (hν : ν ≪ P.measure) :
    2 * ordinaryLSRate P * relativeEntropy ν P.measure ≤ ordinaryRelativeFisher ν P := by
  by_cases hmem : relativeSqrt ν P ∈ WeightedH1 P
  swap
  · rw [ordinaryRelativeFisher_of_not_mem hmem]; exact le_top
  have hent : homogeneousEntropy P.measure (fun x => relativeSqrt ν P x ^ 2) =
      relativeEntropy ν P.measure := by
    rw [relativeEntropy_of_absolutelyContinuous hν]
    congr 1
    funext x
    exact Real.sq_sqrt ENNReal.toReal_nonneg
  have hfish : ordinaryRelativeFisher ν P =
      4 * ∫⁻ x, ‖weightedGradient P (relativeSqrt ν P) hmem x‖ₑ ^ 2 ∂P.measure := by
    unfold ordinaryRelativeFisher
    rw [dite_eq_left_of_eq_true (eq_true ⟨hν, hmem⟩)]
  rw [hfish]
  set E := ∫⁻ x, ‖weightedGradient P (relativeSqrt ν P) hmem x‖ₑ ^ 2 ∂P.measure with hE
  set H := relativeEntropy ν P.measure with hH
  by_cases h0 : H = 0
  · rw [h0]; simp
  have hle : ordinaryLSRate P ≤ 2 * E / H := by
    unfold ordinaryLSRate
    have hpos : 0 < homogeneousEntropy P.measure (fun x => relativeSqrt ν P x ^ 2) := by
      rw [hent]; exact pos_iff_ne_zero.2 h0
    refine (iInf_le _ ⟨relativeSqrt ν P, hmem, hpos⟩).trans (le_of_eq ?_)
    simp only [hent]
    rfl
  by_cases htop : H = ⊤
  · rw [htop, ENNReal.div_top, nonpos_iff_eq_zero] at hle
    rw [hle, htop]; simp
  have h1 : ordinaryLSRate P * H ≤ 2 * E := by
    calc ordinaryLSRate P * H ≤ 2 * E / H * H :=
          mul_le_mul' hle le_rfl
      _ = 2 * E := ENNReal.div_mul_cancel h0 htop
  calc 2 * ordinaryLSRate P * H = 2 * (ordinaryLSRate P * H) := by rw [mul_assoc]
    _ ≤ 2 * (2 * E) := mul_le_mul' le_rfl h1
    _ = 4 * E := by rw [← mul_assoc]; norm_num

/-- The frozen LSI for the densities `ρ m`, with respect to any frozen Gibbs reference. -/
theorem two_mul_frozenLSRateInf_mul_relativeEntropy_le (A : InteractionData d)
    (σ : ProbabilityMeasure (Torus d)) (ρ : AbsoluteDensity d) :
    2 * frozenLSRateInf A *
        relativeEntropy (densityMeasure ρ : Measure (Torus d)) (frozenGibbs A σ).measure ≤
      ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus d)) (frozenGibbs A σ) := by
  have hν : (densityMeasure ρ : Measure (Torus d)) ≪ (frozenGibbs A σ).measure := by
    refine Measure.AbsolutelyContinuous.trans ?_ (frozenGibbs A σ).haar_ac_measure
    rw [densityMeasure_coe]
    exact withDensity_absolutelyContinuous _ _
  exact (mul_le_mul' (mul_le_mul' le_rfl (frozenLSRateInf_le A σ)) le_rfl).trans
    (two_mul_lsRate_mul_relativeEntropy_le _ _ hν)

/-! ### Relative entropy with respect to a bounded reference -/

theorem exists_abs_log_density_le (P : BoundedPositiveReference d) :
    ∃ C : ℝ, ∀ᵐ x ∂haar d, |Real.log (P.density x)| ≤ C := by
  refine ⟨|Real.log P.lower| + |Real.log P.upper|, ?_⟩
  filter_upwards [P.lower_le, P.le_upper] with x h1 h2
  have hp := lt_of_lt_of_le P.lower_pos h1
  have a1 := Real.log_le_log P.lower_pos h1
  have a2 := Real.log_le_log hp h2
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log P.lower), abs_nonneg (Real.log P.upper)]
  · linarith [le_abs_self (Real.log P.upper), abs_nonneg (Real.log P.lower)]

theorem integrable_density_mul_log_reference (P : BoundedPositiveReference d)
    (ρ : AbsoluteDensity d) :
    Integrable (fun x => ρ.density x * Real.log (P.density x)) (haar d) := by
  obtain ⟨C, hC⟩ := exists_abs_log_density_le P
  refine Integrable.mono' (ρ.integrable_density.mul_const C) ?_ ?_
  · exact ρ.integrable_density.aestronglyMeasurable.mul
      P.measurable_density.log.aestronglyMeasurable
  · filter_upwards [hC] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ρ.density_nonneg x)]
    exact mul_le_mul_of_nonneg_left hx (ρ.density_nonneg x)

theorem pointwise_reference_kernel {ρ p : ℝ} (hρ : 0 ≤ ρ) (hp : 0 < p) :
    p * ((ρ / p) * Real.log (ρ / p) - ρ / p + 1) = ρ * Real.log ρ - ρ * Real.log p - ρ + p := by
  rcases hρ.eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · rw [Real.log_div h0.ne' hp.ne']
    field_simp

/-- For a bounded positive reference `P = p m` and an absolute density `ρ`, the relative entropy
`H(ρ m | P)` is finite and equals `H(ρ m | m) - ∫ ρ log p` (real form). -/
theorem relativeEntropy_reference (P : BoundedPositiveReference d) (ρ : AbsoluteDensity d) :
    relativeEntropy (densityMeasure ρ : Measure (Torus d)) P.measure ≠ ⊤ ∧
    (relativeEntropy (densityMeasure ρ : Measure (Torus d)) P.measure).toReal =
      (relativeEntropy (densityMeasure ρ : Measure (Torus d)) (haar d)).toReal
        - ∫ x, ρ.density x * Real.log (P.density x) ∂haar d := by
  set ν : Measure (Torus d) := (densityMeasure ρ : Measure (Torus d)) with hν
  have hνm : ν ≪ haar d := by
    rw [hν, densityMeasure_coe]; exact withDensity_absolutelyContinuous _ _
  have hν' : ν ≪ P.measure := hνm.trans P.haar_ac_measure
  have hρm : AEMeasurable ρ.density (haar d) := ρ.integrable_density.aemeasurable
  set v : Torus d → ℝ := fun x => ρ.density x / P.density x with hv
  have hvm : AEMeasurable v (haar d) := hρm.div P.measurable_density.aemeasurable
  have hrn : (fun x => (ν.rnDeriv P.measure x).toReal) =ᵐ[P.measure] v := by
    have h1 := Measure.rnDeriv_withDensity_right ν (haar d)
      (f := fun x => ENNReal.ofReal (P.density x)) P.measurable_ofReal_density.aemeasurable
      (by filter_upwards [P.ae_pos] with x hx; exact (ENNReal.ofReal_pos.2 hx).ne')
      (by filter_upwards with x; exact ENNReal.ofReal_ne_top)
    have h2 : ν.rnDeriv (haar d) =ᵐ[haar d] fun x => ENNReal.ofReal (ρ.density x) := by
      rw [hν, densityMeasure_coe]
      exact Measure.rnDeriv_withDensity₀ (haar d)
        (f := fun x => ENNReal.ofReal (ρ.sqrt x ^ 2))
        ((ρ.memLp_sqrt.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal)
    refine P.measure_ac_haar.ae_le ?_
    filter_upwards [h1, h2, P.ae_pos] with x hx1 hx2 hp
    have hx1' : ν.rnDeriv P.measure x =
        (ENNReal.ofReal (P.density x))⁻¹ * ν.rnDeriv (haar d) x := hx1
    simp only [hx1', hx2, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le,
      ENNReal.toReal_ofReal (ρ.density_nonneg x), hv]
    ring
  have hH : relativeEntropy ν P.measure = homogeneousEntropy P.measure v := by
    rw [relativeEntropy_of_absolutelyContinuous hν']
    exact homogeneousEntropy_congr_ae hrn
  have hmass : ∫ x, v x ∂P.measure = 1 := by
    show ∫ x, v x ∂(haar d).withDensity (fun x => ENNReal.ofReal (P.density x)) = 1
    rw [integral_withDensity_eq_integral_toReal_smul₀ P.measurable_ofReal_density.aemeasurable
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    have : ∀ᵐ x ∂haar d, (ENNReal.ofReal (P.density x)).toReal • v x = ρ.density x := by
      filter_upwards [P.ae_pos] with x hp
      rw [ENNReal.toReal_ofReal hp.le, smul_eq_mul]
      simp only [hv]
      field_simp
    rw [integral_congr_ae this]
    exact ρ.integral_density
  have h1 := absoluteDensity_entropy_finite ρ
  have h2 := integrable_density_mul_log_reference P ρ
  have hKint : Integrable (fun x => ρ.density x * Real.log (ρ.density x)
      - ρ.density x * Real.log (P.density x) - ρ.density x + P.density x) (haar d) :=
    ((h1.1.sub h2).sub ρ.integrable_density).add P.integrable_density
  have hKnn : 0 ≤ᵐ[haar d] fun x => ρ.density x * Real.log (ρ.density x)
      - ρ.density x * Real.log (P.density x) - ρ.density x + P.density x := by
    filter_upwards [P.ae_pos] with x hp
    rw [← pointwise_reference_kernel (ρ.density_nonneg x) hp]
    exact mul_nonneg hp.le (self_mul_log_sub_add_one_nonneg
      (div_nonneg (ρ.density_nonneg x) hp.le))
  have hlint : homogeneousEntropy P.measure v = ENNReal.ofReal (∫ x, ρ.density x *
      Real.log (ρ.density x) - ρ.density x * Real.log (P.density x) - ρ.density x
        + P.density x ∂haar d) := by
    rw [entropy_mass_one hmass]
    show ∫⁻ x, _ ∂(haar d).withDensity (fun x => ENNReal.ofReal (P.density x)) = _
    rw [lintegral_withDensity_eq_lintegral_mul₀ P.measurable_ofReal_density.aemeasurable
      (by
        have : AEMeasurable (fun x => ENNReal.ofReal (v x * Real.log (v x) - v x + 1)) (haar d) :=
          ENNReal.measurable_ofReal.comp_aemeasurable ((hvm.mul hvm.log).sub hvm |>.add_const 1)
        exact this),
      ofReal_integral_eq_lintegral_ofReal hKint hKnn]
    refine lintegral_congr_ae ?_
    filter_upwards [P.ae_pos] with x hp
    show ENNReal.ofReal (P.density x) * ENNReal.ofReal _ = _
    rw [← ENNReal.ofReal_mul hp.le]
    congr 1
    exact pointwise_reference_kernel (ρ.density_nonneg x) hp
  have hint : ∫ x, ρ.density x * Real.log (ρ.density x) - ρ.density x * Real.log (P.density x)
        - ρ.density x + P.density x ∂haar d =
      (relativeEntropy ν (haar d)).toReal - ∫ x, ρ.density x * Real.log (P.density x) ∂haar d := by
    have i1 : Integrable (fun x => ρ.density x * Real.log (ρ.density x)
        - ρ.density x * Real.log (P.density x)) (haar d) := h1.1.sub h2
    have i2 : Integrable (fun x => ρ.density x * Real.log (ρ.density x)
        - ρ.density x * Real.log (P.density x) - ρ.density x) (haar d) := i1.sub ρ.integrable_density
    have e1 := integral_add (μ := haar d) i2 P.integrable_density
    have e2 := integral_sub (μ := haar d) i1 ρ.integrable_density
    have e3 := integral_sub (μ := haar d) h1.1 h2
    rw [e1, e2, e3, ρ.integral_density, P.mass_one, h1.2.2.2]
    ring
  have hnn : 0 ≤ ∫ x, ρ.density x * Real.log (ρ.density x) - ρ.density x * Real.log (P.density x)
        - ρ.density x + P.density x ∂haar d := integral_nonneg_of_ae hKnn
  refine ⟨?_, ?_⟩
  · rw [hH, hlint]; exact ENNReal.ofReal_ne_top
  · rw [hH, hlint, ENNReal.toReal_ofReal hnn, hint]

/-- Species entropies relative to the barycenter are dominated by the species entropies relative
to any bounded reference: `∑ θ_s H(ρ_s | ρ̄) ≤ ∑ θ_s H(ρ_s | P)` (real form). -/
theorem sum_relativeEntropy_barycenter_le_reference (F : SpeciesFamily d)
    (P : BoundedPositiveReference d) :
    ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
        (densityMeasure (barycenter F) : Measure (Torus d))).toReal ≤
      ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
        P.measure).toReal := by
  have hA : ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
        (densityMeasure (barycenter F) : Measure (Torus d))).toReal =
      ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
        (haar d)).toReal -
      (relativeEntropy (densityMeasure (barycenter F) : Measure (Torus d)) (haar d)).toReal := by
    rw [← F.sum_weight_integral_density_mul_log, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [(F.relativeEntropy_species s).2.2]; ring
  have hI : ∑ s, F.weight s * ∫ x, (F.density s).density x * Real.log (P.density x) ∂haar d =
      ∫ x, (barycenter F).density x * Real.log (P.density x) ∂haar d := by
    have hint : ∀ s, Integrable (fun x => F.weight s *
        ((F.density s).density x * Real.log (P.density x))) (haar d) :=
      fun s => (integrable_density_mul_log_reference P (F.density s)).const_mul _
    have h1 : ∑ s, F.weight s * ∫ x, (F.density s).density x * Real.log (P.density x) ∂haar d =
        ∫ x, ∑ s, F.weight s * ((F.density s).density x * Real.log (P.density x)) ∂haar d := by
      rw [integral_finsetSum _ fun s _ => hint s]
      exact Finset.sum_congr rfl fun s _ => (integral_const_mul _ _).symm
    rw [h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show _ = (barycenter F).density x * Real.log (P.density x)
    calc ∑ s, F.weight s * ((F.density s).density x * Real.log (P.density x))
        = (∑ s, F.weight s * (F.density s).density x) * Real.log (P.density x) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun s _ => by ring
      _ = _ := by rw [← F.barycenter_density_eq_sum x]
  have hB : ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
        P.measure).toReal =
      ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
        (haar d)).toReal -
      ∫ x, (barycenter F).density x * Real.log (P.density x) ∂haar d := by
    rw [← hI, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [(relativeEntropy_reference P (F.density s)).2]; ring
  have hC : 0 ≤ (relativeEntropy (densityMeasure (barycenter F) : Measure (Torus d))
      (haar d)).toReal - ∫ x, (barycenter F).density x * Real.log (P.density x) ∂haar d := by
    rw [← (relativeEntropy_reference P (barycenter F)).2]
    exact ENNReal.toReal_nonneg
  linarith

/-! ### The comparison -/

/-- **STR012 (dissipation form).**  For direct Lipschitz data with `0 < d`, `0 < r_* < ∞` and
`ℓ = frozenLSRateInf A`: every family with positive gap obeys
`D_θ ≥ 2 (r_* ℓ / (r_* + ℓ)) G_θ`. -/
theorem speciesDissipation_ge_harmonicMean_mul_gap (hd : 0 < d) (A : InteractionData d)
    (hLip : LipschitzData A) (b : AbsoluteDrift A)
    (hr : 0 < scalarRate A b) (hrf : scalarRate A b ≠ ⊤)
    (F : SpeciesFamily d) (hG : 0 < speciesGap A F) :
    ENNReal.ofReal (2 * ((scalarRate A b).toReal * (frozenLSRateInf A).toReal /
        ((scalarRate A b).toReal + (frozenLSRateInf A).toReal)) * (speciesGap A F : ℝ)) ≤
      speciesDissipation A b F := by
  obtain ⟨hl0, hlle, hltop⟩ := frozenLSRateInf_ge_lowerBound hd A
  have hℓpos : 0 < (frozenLSRateInf A).toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hl0) hlle)) hltop.ne
  have hrpos : 0 < (scalarRate A b).toReal := ENNReal.toReal_pos hr.ne' hrf
  set r := (scalarRate A b).toReal with hrdef
  set ℓ := (frozenLSRateInf A).toReal with hℓdef
  by_cases hDtop : speciesDissipation A b F = ⊤
  · rw [hDtop]; exact le_top
  set Dr := (speciesDissipation A b F).toReal with hDr
  have hGpos : 0 < (speciesGap A F : ℝ) := by exact_mod_cast hG
  -- the scalar estimate `2 r_* g ≤ D_θ`
  have ha : 2 * r * (scalarGap A (barycenter F) : ℝ) ≤ Dr := by
    have hdec := (speciesDissipation_decomposition A b F).2
    have hle : scalarDissipation A b (barycenter F) ≤ speciesDissipation A b F := by
      rw [hdec]; exact le_self_add
    by_cases hg : 0 < scalarGap A (barycenter F)
    · have h1 := scalarRate_le_quotient A b (barycenter F) hg
      unfold scalarQuotient at h1
      have h2 : scalarRate A b * (2 * (scalarGap A (barycenter F) : ℝ≥0∞)) ≤
          scalarDissipation A b (barycenter F) :=
        (ENNReal.le_div_iff_mul_le (Or.inl (two_mul_gap_ne_zero hg))
          (Or.inl (two_mul_gap_ne_top _))).1 h1
      have h3 := ENNReal.toReal_mono hDtop (h2.trans hle)
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at h3
      simp only [ENNReal.toReal_ofNat, ENNReal.coe_toReal] at h3
      rw [hDr]; linarith
    · have : (scalarGap A (barycenter F) : ℝ) = 0 := by
        have := nonpos_iff_eq_zero.1 (not_lt.1 hg)
        rw [this]; rfl
      rw [this, mul_zero]; exact ENNReal.toReal_nonneg
  -- the frozen LSI estimate `2 ℓ S ≤ D_θ`
  have hb : 2 * ℓ * ∑ s, F.weight s *
      (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
        (densityMeasure (barycenter F) : Measure (Torus d))).toReal ≤ Dr := by
    set P := frozenGibbs A (densityMeasure (barycenter F)) with hP
    set Hr : Fin F.count → ℝ := fun s => (relativeEntropy
      (densityMeasure (F.density s) : Measure (Torus d)) P.measure).toReal with hHr
    have hfin : ∀ s, relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
        P.measure ≠ ⊤ := fun s => (relativeEntropy_reference P (F.density s)).1
    have hterm : ∀ s, ENNReal.ofReal (F.weight s * (2 * ℓ * Hr s)) =
        ENNReal.ofReal (F.weight s) * (2 * frozenLSRateInf A *
          relativeEntropy (densityMeasure (F.density s) : Measure (Torus d)) P.measure) := by
      intro s
      have hH0 : 0 ≤ Hr s := ENNReal.toReal_nonneg
      rw [ENNReal.ofReal_mul (F.weight_nonneg s), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat, hℓdef,
        ENNReal.ofReal_toReal hltop.ne, hHr, ENNReal.ofReal_toReal (hfin s)]
    have hsum : ENNReal.ofReal (∑ s, F.weight s * (2 * ℓ * Hr s)) ≤ speciesDissipation A b F := by
      rw [ENNReal.ofReal_sum_of_nonneg fun s _ =>
        mul_nonneg (F.weight_nonneg s) (mul_nonneg (by positivity) ENNReal.toReal_nonneg)]
      rw [speciesDissipation_eq_frozenInformation A hLip b F]
      refine Finset.sum_le_sum fun s _ => ?_
      rw [hterm s]
      exact mul_le_mul' le_rfl (two_mul_frozenLSRateInf_mul_relativeEntropy_le A _ (F.density s))
    have hreal : ∑ s, F.weight s * (2 * ℓ * Hr s) ≤ Dr :=
      (ENNReal.ofReal_le_iff_le_toReal hDtop).1 hsum
    have hK := sum_relativeEntropy_barycenter_le_reference F P
    have hrewrite : ∑ s, F.weight s * (2 * ℓ * Hr s) = 2 * ℓ * ∑ s, F.weight s * Hr s := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [hrewrite] at hreal
    refine le_trans ?_ hreal
    exact mul_le_mul_of_nonneg_left hK (by positivity)
  have hdecomp := F.speciesGap_decomposition A
  set g : ℝ := (scalarGap A (barycenter F) : ℝ) with hgdef
  set S : ℝ := ∑ s, F.weight s *
      (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
        (densityMeasure (barycenter F) : Measure (Torus d))).toReal with hSdef
  rw [(ENNReal.ofReal_le_iff_le_toReal hDtop)]
  rw [← hDr]
  have hrℓ : 0 < r + ℓ := by positivity
  have e : 2 * (r * ℓ / (r + ℓ)) * (speciesGap A F : ℝ) =
      2 * r * ℓ * (speciesGap A F : ℝ) / (r + ℓ) := by
    field_simp
  rw [e, div_le_iff₀ hrℓ, hdecomp]
  have h1 : ℓ * (2 * r * g) ≤ ℓ * Dr := mul_le_mul_of_nonneg_left ha hℓpos.le
  have h2 : r * (2 * ℓ * S) ≤ r * Dr := mul_le_mul_of_nonneg_left hb hrpos.le
  nlinarith [h1, h2]

/-- **STR012.**  For direct Lipschitz data with `0 < d` and `0 < r_* < ∞`, with
`ℓ = frozenLSRateInf A` the actual frozen LSI infimum:
`r_* ℓ / (r_* + ℓ) ≤ r_ms ≤ r_*`. -/
theorem speciesRate_ge_harmonicMean_frozenLS (hd : 0 < d) (A : InteractionData d)
    (hLip : LipschitzData A) (b : AbsoluteDrift A)
    (hr : 0 < scalarRate A b) (hrf : scalarRate A b ≠ ⊤) :
    ENNReal.ofReal ((scalarRate A b).toReal * (frozenLSRateInf A).toReal /
        ((scalarRate A b).toReal + (frozenLSRateInf A).toReal)) ≤ speciesRate A b ∧
      speciesRate A b ≤ scalarRate A b := by
  refine ⟨?_, speciesRate_le_scalarRate A b⟩
  refine le_iInf fun F => ?_
  have hG : 0 < speciesGap A F.1 := F.2
  have hmain := speciesDissipation_ge_harmonicMean_mul_gap hd A hLip b hr hrf F.1 hG
  unfold speciesQuotient
  rw [ENNReal.le_div_iff_mul_le (Or.inl (two_mul_gap_ne_zero hG))
    (Or.inl (two_mul_gap_ne_top _))]
  have hh : 0 ≤ (scalarRate A b).toReal * (frozenLSRateInf A).toReal /
      ((scalarRate A b).toReal + (frozenLSRateInf A).toReal) := by
    positivity
  have e : ENNReal.ofReal ((scalarRate A b).toReal * (frozenLSRateInf A).toReal /
        ((scalarRate A b).toReal + (frozenLSRateInf A).toReal)) * (2 * (speciesGap A F.1 : ℝ≥0∞)) =
      ENNReal.ofReal (2 * ((scalarRate A b).toReal * (frozenLSRateInf A).toReal /
        ((scalarRate A b).toReal + (frozenLSRateInf A).toReal)) * (speciesGap A F.1 : ℝ)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
    ring
  rw [e]
  exact hmain

end DGPS.Structural
