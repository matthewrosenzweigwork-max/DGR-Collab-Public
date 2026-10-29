import DGPS.Structural.CircleDensityRatio
import DGPS.Analysis.WeightedRateComparison
import DGPS.Variational.ScoreDecomposition

/-!
# Ordinary LSI for the positive `H¹` barycenter and its species scores (STR020)

On the circle, let `ρ̄ = barycenter F` satisfy `CircleDensityRatio A b ρ̄` (STR019): a continuous
`w` with `1/4 < w² < 9/4` and `ρ̄ = w² p` a.e., where `p = P(ρ̄ m)` is the frozen Gibbs density.
Then, for any bounded positive reference `Q` whose density agrees a.e. with `ρ̄`:

* `barycenterLSRate_ge_frozen_ninth`: `r_LS(Q) ≥ r_LS(p m) / 9 ≥ ℓ / 9` (bounded-density
  comparison with oscillation `log 9`; no spatial derivative of `ρ̄` is used);
* `positiveH1Circle_reference_information_eq_score`: `√(ρ_s / ρ̄) ∈ H¹(Q)` and its ordinary
  relative Fisher information equals the DEF015 score information `I_s`.

R5 notes. Route: self-contained (the alternate route allowed by the spec). Statements are
quantified over an arbitrary reference `Q` with `Q.density =ᵐ ρ̄.density` (the barycenter density is
only a.e. equal to the continuous `w² p`); `circleDensityRatio_exists_reference` supplies such a
`Q`. The Lipschitz hypothesis of `positiveReference_absolute_identity` is not used: the continuous
`H¹` representative `H = w √p` of `√ρ̄` is bounded below, so `H⁻¹ ∈ H¹` and the product/reciprocal
rules give `∇(u_s / H) = (1/(2H)) (2∇u_s - u_s σ)`.
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS.Structural

variable {A : InteractionData 1} {b : AbsoluteDrift A} {ρ : AbsoluteDensity 1}

/-- A continuous, positively bounded below representative of `√ρ` from the density ratio. -/
theorem circleDensityRatio_sqrt_rep (hR : CircleDensityRatio A b ρ) :
    ∃ H : Torus 1 → ℝ, Continuous H ∧ (∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ H x) ∧
      ρ.sqrt =ᵐ[haar 1] H ∧ ρ.density =ᵐ[haar 1] fun x => H x ^ 2 := by
  obtain ⟨w, g, hwc, -, -, -, -, -, -, -, hrange, hρ, -⟩ := hR
  set ν : ProbabilityMeasure (Torus 1) := densityMeasure ρ with hν
  have hpc : Continuous (frozenDensity A (ν : Measure (Torus 1))) := frozenDensity_continuous A _
  have hpb := fun x => frozenDensity_bounds A (ν : Measure (Torus 1)) x
  have hp0 : ∀ x, 0 < frozenDensity A (ν : Measure (Torus 1)) x := fun x =>
    lt_of_lt_of_le (Real.exp_pos _) (hpb x).1
  have hdens : ∀ x, (frozenGibbs A ν).density x = frozenDensity A (ν : Measure (Torus 1)) x :=
    fun _ => rfl
  refine ⟨fun x => w x * Real.sqrt (frozenDensity A (ν : Measure (Torus 1)) x),
    hwc.mul (hpc.sqrt), ⟨1 / 2 * Real.sqrt (Real.exp (-(2 * frozenSupBound A))), ?_, ?_⟩, ?_, ?_⟩
  · positivity
  · intro x
    have h1 : Real.sqrt (Real.exp (-(2 * frozenSupBound A))) ≤
        Real.sqrt (frozenDensity A (ν : Measure (Torus 1)) x) :=
      Real.sqrt_le_sqrt (hpb x).1
    have h2 := (hrange x).1
    have h3 : 0 ≤ Real.sqrt (Real.exp (-(2 * frozenSupBound A))) := Real.sqrt_nonneg _
    nlinarith
  · have hsq : ∀ x, (w x * Real.sqrt (frozenDensity A (ν : Measure (Torus 1)) x)) ^ 2 =
        w x ^ 2 * frozenDensity A (ν : Measure (Torus 1)) x := by
      intro x
      rw [mul_pow, Real.sq_sqrt (hp0 x).le]
    filter_upwards [hρ, ρ.sqrt_nonneg] with x hx hx0
    have hH0 : 0 ≤ w x * Real.sqrt (frozenDensity A (ν : Measure (Torus 1)) x) :=
      mul_nonneg (by linarith [(hrange x).1]) (Real.sqrt_nonneg _)
    refine (pow_left_inj₀ hx0 hH0 two_ne_zero).1 ?_
    rw [hsq, ← hdens, ← hx]
    rfl
  · filter_upwards [hρ] with x hx
    rw [hx, mul_pow, Real.sq_sqrt (hp0 x).le]
    rfl

/-- A bounded positive reference with the density `w² p` of the density-ratio representation. -/
theorem circleDensityRatio_exists_reference (hR : CircleDensityRatio A b ρ) :
    ∃ Q : BoundedPositiveReference 1, Q.density =ᵐ[haar 1] ρ.density := by
  obtain ⟨w, g, hwc, -, -, -, hmass, -, -, -, hrange, hρ, hsq⟩ := hR
  set ν : ProbabilityMeasure (Torus 1) := densityMeasure ρ with hν
  have hpc : Continuous (frozenDensity A (ν : Measure (Torus 1))) := frozenDensity_continuous A _
  have hpb := fun x => frozenDensity_bounds A (ν : Measure (Torus 1)) x
  refine ⟨⟨fun x => w x ^ 2 * frozenDensity A (ν : Measure (Torus 1)) x,
    ((hwc.pow 2).mul hpc).measurable, 1 / 4 * Real.exp (-(2 * frozenSupBound A)),
    9 / 4 * Real.exp (2 * frozenSupBound A), by positivity, ?_, ?_, hmass⟩, hρ.symm⟩
  · refine Filter.Eventually.of_forall fun x => ?_
    have h1 := (hsq x).1
    have h2 := (hpb x).1
    have h3 := Real.exp_pos (-(2 * frozenSupBound A))
    show _ ≤ w x ^ 2 * frozenDensity A (ν : Measure (Torus 1)) x
    nlinarith
  · refine Filter.Eventually.of_forall fun x => ?_
    have h1 := (hsq x).2
    have h2 := (hpb x).2
    have h3 := (hpb x).1
    have h4 := Real.exp_pos (-(2 * frozenSupBound A))
    have h5 : 0 < w x ^ 2 := by linarith [(hsq x).1]
    show w x ^ 2 * frozenDensity A (ν : Measure (Torus 1)) x ≤ _
    nlinarith [Real.exp_pos (2 * frozenSupBound A)]

/-- **STR020 (rate, generic form).** `r_LS(Q) ≥ r_LS(P(ρ m)) / 9` for any bounded positive
reference `Q` a.e. equal to `ρ`, when `ρ` has the density-ratio representation. -/
theorem circleDensityRatio_lsRate_ge_ninth (hR : CircleDensityRatio A b ρ)
    (Q : BoundedPositiveReference 1) (hQ : Q.density =ᵐ[haar 1] ρ.density) :
    ENNReal.ofReal (1 / 9) * ordinaryLSRate (frozenGibbs A (densityMeasure ρ)) ≤
      ordinaryLSRate Q := by
  obtain ⟨w, g, hwc, -, -, -, -, -, -, -, hrange, hρ, hsq⟩ := hR
  have hQw : Q.density =ᵐ[haar 1]
      fun x => w x ^ 2 * (frozenGibbs A (densityMeasure ρ)).density x := hQ.trans hρ
  have hosc : ∀ᵐ x ∂haar 1, ∀ᵐ y ∂haar 1,
      Real.log (Q.density x / (frozenGibbs A (densityMeasure ρ)).density x) -
        Real.log (Q.density y / (frozenGibbs A (densityMeasure ρ)).density y) ≤ Real.log 9 := by
    have hp0 : ∀ x, 0 < (frozenGibbs A (densityMeasure ρ)).density x := fun x =>
      lt_of_lt_of_le (Real.exp_pos _) (frozenDensity_bounds A _ x).1
    filter_upwards [hQw] with x hx
    filter_upwards [hQw] with y hy
    rw [hx, hy, mul_div_cancel_right₀ _ (hp0 x).ne', mul_div_cancel_right₀ _ (hp0 y).ne']
    have ha : 0 < w x ^ 2 := by linarith [(hsq x).1]
    have hb : 0 < w y ^ 2 := by linarith [(hsq y).1]
    rw [← Real.log_div ha.ne' hb.ne']
    refine Real.log_le_log (div_pos ha hb) ?_
    rw [div_le_iff₀ hb]
    linarith [(hsq x).2, (hsq y).1]
  have h := (Examples.ordinary_lsi_bounded_density_comparison (frozenGibbs A (densityMeasure ρ)) Q
    (Real.log 9) hosc).1.1
  have he : Real.exp (-Real.log 9) = 1 / 9 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  rwa [he] at h

/-- **STR020 (rate).** For the barycenter of a species family on the circle whose density ratio
against the frozen Gibbs reference is controlled (STR019), any bounded positive reference `Q`
a.e. equal to `ρ̄` has ordinary LS rate at least `1/9` of the frozen infimum `ℓ`, hence at least
`a₀ e^{-M} / 9`. -/
theorem barycenterLSRate_ge_frozen_ninth (F : SpeciesFamily 1)
    (hR : CircleDensityRatio A b (barycenter F))
    (Q : BoundedPositiveReference 1) (hQ : Q.density =ᵐ[haar 1] (barycenter F).density) :
    ENNReal.ofReal (1 / 9) * frozenLSRateInf A ≤ ordinaryLSRate Q ∧
      ENNReal.ofReal (a0 * Real.exp (-totalOscillation A) / 9) ≤ ordinaryLSRate Q := by
  have h1 : ENNReal.ofReal (1 / 9) * frozenLSRateInf A ≤ ordinaryLSRate Q :=
    le_trans (by gcongr; exact iInf_le _ _) (circleDensityRatio_lsRate_ge_ninth hR Q hQ)
  refine ⟨h1, ?_⟩
  refine le_trans ?_ h1
  rw [show a0 * Real.exp (-totalOscillation A) / 9 = 1 / 9 * (a0 * Real.exp (-totalOscillation A))
    by ring, ENNReal.ofReal_mul (by norm_num)]
  gcongr
  exact frozenLSRateInf_lower_bound 1 one_pos A

/-- Pointwise form of the score identity: with `h = H > 0`,
`2 ∇u_s - u_s σ = 2 H ∇(u_s / H)`. -/
theorem scoreDifference_eq_smul (F : SpeciesFamily 1) (s : Fin F.count) (x : Torus 1) (H : ℝ)
    (hH : 0 < H) (hh : (barycenter F).sqrt x = H) :
    F.scoreDifference s x = (2 * H) •
      (H⁻¹ • F.sqrtGradient s x +
        (F.density s).sqrt x • ((-(H ^ 2)⁻¹) • F.barycenterWeakGrad x)) := by
  rw [SpeciesFamily.scoreDifference, F.score_eq x, hh]
  ext j
  simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  field_simp
  ring

/-- **STR020 (score identity).** For `ρ̄ = barycenter F` with the density-ratio representation and
a bounded positive reference `Q` a.e. equal to `ρ̄`, the species relative square root
`√(ρ_s / ρ̄)` lies in `H¹(Q)` and its ordinary relative Fisher information equals the weighted
score information `I_s = ∫ |2 ∇u_s - u_s σ|² dm` of DEF015. -/
theorem positiveH1Circle_reference_information_eq_score (F : SpeciesFamily 1)
    (hR : CircleDensityRatio A b (barycenter F))
    (Q : BoundedPositiveReference 1) (hQ : Q.density =ᵐ[haar 1] (barycenter F).density)
    (s : Fin F.count) :
    relativeSqrt (densityMeasure (F.density s) : Measure (Torus 1)) Q ∈ WeightedH1 Q ∧
      ordinaryRelativeFisher (densityMeasure (F.density s) : Measure (Torus 1)) Q =
        F.scoreInformation s := by
  obtain ⟨H, hHc, ⟨c, hc, hcH⟩, hsq_ae, hden⟩ := circleDensityRatio_sqrt_rep hR
  set ν : Measure (Torus 1) := (densityMeasure (F.density s) : Measure (Torus 1)) with hν
  have hνac : ν ≪ Q.measure :=
    (withDensity_absolutelyContinuous _ _).trans Q.haar_ac_measure
  have hHpos : ∀ x, 0 < H x := fun x => lt_of_lt_of_le hc (hcH x)
  have habs : (fun x => Real.sqrt (ν.rnDeriv (haar 1) x).toReal) =ᵐ[haar 1] (F.density s).sqrt := by
    have h := Measure.rnDeriv_withDensity₀ (haar 1)
      (f := fun x => ENNReal.ofReal ((F.density s).sqrt x ^ 2))
      (by exact (((F.density s).memLp_sqrt.aestronglyMeasurable.aemeasurable.pow_const 2)).ennreal_ofReal)
    filter_upwards [h, (F.density s).sqrt_nonneg] with x hx hx0
    rw [hν, densityMeasure_coe, hx, ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq hx0]
  have hHG : IsWeakGradient H F.barycenterWeakGrad :=
    F.isWeakGradient_barycenterWeakGrad.congr_ae hsq_ae (Filter.EventuallyEq.refl _ _)
  have hinv := hHG.inv_of_pos hHc hc hcH
  have hmul := (F.isWeakGradient_sqrtGradient s).mul_one_dim hinv
  have hQH : ∀ᵐ x ∂haar 1, Q.density x = H x ^ 2 := hQ.trans hden
  have hrel : relativeSqrt ν Q =ᵐ[haar 1] fun x => (F.density s).sqrt x * (H x)⁻¹ := by
    filter_upwards [RelativeFisher.relativeSqrt_ae_eq Q ν, habs, hQH] with x h1 h2 h3
    rw [h1, h2, h3, Real.rpow_neg (sq_nonneg _), ← Real.sqrt_eq_rpow, Real.sqrt_sq (hHpos x).le]
  have hws := hmul.congr_ae hrel.symm (Filter.EventuallyEq.refl _ _)
  refine ⟨(mem_weightedH1_iff Q).2 ⟨_, hws⟩, ?_⟩
  rw [ordinaryRelativeFisher_eq hνac hws, SpeciesFamily.scoreInformation]
  have hmeas := hmul.memLp_grad.aestronglyMeasurable.aemeasurable.enorm.pow_const 2
  rw [show Q.measure = (haar 1).withDensity fun x => ENNReal.ofReal (Q.density x) from rfl,
    lintegral_withDensity_eq_lintegral_mul₀ Q.measurable_ofReal_density.aemeasurable hmeas,
    ← lintegral_const_mul' _ _ (by norm_num)]
  refine lintegral_congr_ae ?_
  filter_upwards [hQH, hsq_ae] with x hx hx2
  simp only [Pi.mul_apply]
  rw [hx]
  have hsd := scoreDifference_eq_smul F s x (H x) (hHpos x) hx2
  have e : ‖F.scoreDifference s x‖ₑ ^ 2 = ENNReal.ofReal (‖F.scoreDifference s x‖ ^ 2) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [← e]
  have := RelativeFisher.enorm_aux
    ((H x)⁻¹ • F.sqrtGradient s x + (F.density s).sqrt x • ((-(H x ^ 2)⁻¹) • F.barycenterWeakGrad x))
    (F.scoreDifference s x) (H x ^ 2) (sq_nonneg _) (by
      rw [hsd, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (by have := hHpos x; positivity)]
      ring)
  exact this

end DGPS.Structural
