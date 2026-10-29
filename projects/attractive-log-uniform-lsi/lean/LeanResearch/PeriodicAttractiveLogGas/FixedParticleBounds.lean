import LeanResearch.PeriodicAttractiveLogGas.FixedGibbsDensityComparison

/-! Appendix A, the two fixed-particle estimates for the actual canonical
Green Gibbs law. The constants are selected before the coupling. The source
bounded-perturbation factors are preserved; the previously recorded A1
majorant is used in place of the source's smaller displayed cube constant. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace PeriodicAttractiveLogGas.FixedParticleBounds
open FixedGibbsDensityComparison

def poincareConstant (N : ℕ) (β₀ C₀ : ℝ) : ℝ :=
  factor N β₀ C₀ * FixedWeightFunctionalInequalities.poincareConstant N β₀

def energyConstant (N : ℕ) (β₀ C₀ : ℝ) : ℝ :=
  factor N β₀ C₀ ^ 2 * (2 * N * FixedWeightFunctionalInequalities.firstConstant N β₀ ^ 2)

def massConstant (N : ℕ) (β₀ C₀ : ℝ) : ℝ :=
  factor N β₀ C₀ ^ 2 * (N * (2 * FixedParticleAOne.normalizationBound N β₀ ^ 2 - 1))

lemma weight_mass_coefficient_nonneg (N : ℕ) (β₀ : ℝ) :
    0 ≤ (N : ℝ) * (2 * FixedParticleAOne.normalizationBound N β₀ ^ 2 - 1) := by
  have hZ := FixedParticleAOne.normalizationBound_ge_one N β₀
  apply mul_nonneg (Nat.cast_nonneg N)
  nlinarith only [hZ, sq_nonneg (FixedParticleAOne.normalizationBound N β₀ - 1)]

lemma constants_nonneg (N : ℕ) (β₀ C₀ : ℝ) :
    0 ≤ poincareConstant N β₀ C₀ ∧ 0 ≤ energyConstant N β₀ C₀ ∧ 0 ≤ massConstant N β₀ C₀ := by
  have hF : 0 ≤ factor N β₀ C₀ := (Real.exp_pos _).le
  have hC := FixedWeightFunctionalInequalities.constants_nonneg N β₀
  exact ⟨mul_nonneg hF hC.1, mul_nonneg (sq_nonneg _) (by positivity),
    mul_nonneg (sq_nonneg _) (weight_mass_coefficient_nonneg N β₀)⟩

/-- Source fixed-particle PI and defective entropy, proved for the actual
law. No fixed-particle functional inequality is a premise. -/
theorem bounds {N : ℕ} (hN : 2 ≤ N) {β₀ C₀ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (hC₀ : 0 ≤ C₀)
    (hbound : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    {β : ℝ} (hβ : 0 ≤ β) (hle : β ≤ β₀) (s : SmoothPair N) :
    variance s.value (gibbsMeasure greenRealRepresentative N β) ≤
        poincareConstant N β₀ C₀ * ∫ X, ‖s.gradient X‖ ^ 2 ∂gibbsMeasure greenRealRepresentative N β ∧
      entropy (gibbsMeasure greenRealRepresentative N β) (fun X => s.value X ^ 2) ≤
        ((energyConstant N β₀ C₀ * (∫ X, ‖s.gradient X‖ ^ 2 ∂gibbsMeasure greenRealRepresentative N β) +
          massConstant N β₀ C₀ * (∫ X, s.value X ^ 2 ∂gibbsMeasure greenRealRepresentative N β) : ℝ) : EReal) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha : 0 ≤ β / (N : ℝ) := div_nonneg hβ hn.le
  have haa : β / (N : ℝ) ≤ FixedWeightConstants.exponent N β₀ :=
    div_le_div_of_nonneg_right hle hn.le
  let μ := gibbsMeasure greenRealRepresentative N β
  let ν := FixedWeightProbability.law N (β / N)
  let M := factor N β₀ C₀
  let : IsProbabilityMeasure μ := isProbabilityMeasure_greenGibbs N hN hβ (hle.trans_lt hsub)
  let : IsProbabilityMeasure ν := FixedWeightProbability.law_probability hN hβ₀ hsub ha haa
  have hM : 0 ≤ M := (Real.exp_pos _).le
  obtain ⟨u, v, hu, hv, huv, huM, hvM, hμν, hνμ⟩ :=
    comparison_factors hN hβ₀ hsub hC₀ hbound hβ hle
  have hμνM : μ ≤ ENNReal.ofReal M • ν := hμν.trans (by
    intro S
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal huM) zero_le)
  have hνμM : ν ≤ ENNReal.ofReal M • μ := hνμ.trans (by
    intro S
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hvM) zero_le)
  have hsb : ∀ X, |s.value X| ≤ ‖s.value‖ := fun X => by
    simpa only [Real.norm_eq_abs] using s.value.norm_coe_le_norm X
  have hp := BoundedPerturbation.poincare_comparison hu.le hv.le
    (FixedWeightFunctionalInequalities.constants_nonneg N β₀).1 hμν hνμ
    s.value.continuous.measurable ⟨‖s.value‖, hsb⟩
    (fun X => sq_nonneg ‖s.gradient X‖) (s.finite_energy μ)
    (FixedWeightFunctionalInequalities.poincare hN hβ₀ hsub ha haa s)
  rw [huv] at hp
  have hd := BoundedPerturbation.defective_comparison hM (by positivity)
    (weight_mass_coefficient_nonneg N β₀) hμνM hνμM s.value.continuous.measurable
    ⟨‖s.value‖, hsb⟩ (fun X => sq_nonneg ‖s.gradient X‖) (s.finite_energy μ)
    (FixedWeightFunctionalInequalities.defective_entropy hN hβ₀ hsub ha haa s)
  refine ⟨hp, ?_⟩
  rw [Rothaus.entropy_sq_eq s.value.continuous.measurable hsb]
  exact EReal.coe_le_coe_iff.mpr hd

/-- The fixed particle number and enclosing coupling interval are the
only parameters in the three constants. Both zero endpoints are included. -/
theorem exists_fixed_particle_bounds (N : ℕ) (hN : 2 ≤ N) {β₀ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) :
    ∃ Cpi A B : ℝ, 0 ≤ Cpi ∧ 0 ≤ A ∧ 0 ≤ B ∧
      ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → ∀ s : SmoothPair N,
        variance s.value (gibbsMeasure greenRealRepresentative N β) ≤
            Cpi * ∫ X, ‖s.gradient X‖ ^ 2 ∂gibbsMeasure greenRealRepresentative N β ∧
          entropy (gibbsMeasure greenRealRepresentative N β) (fun X => s.value X ^ 2) ≤
            ((A * (∫ X, ‖s.gradient X‖ ^ 2 ∂gibbsMeasure greenRealRepresentative N β) +
              B * (∫ X, s.value X ^ 2 ∂gibbsMeasure greenRealRepresentative N β) : ℝ) : EReal) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_regularGreenRepresentative_bounds
  have hc := constants_nonneg N β₀ C₀
  exact ⟨poincareConstant N β₀ C₀, energyConstant N β₀ C₀, massConstant N β₀ C₀,
    hc.1, hc.2.1, hc.2.2, fun β hβ hle s => bounds hN hβ₀ hsub hC₀.le
      (fun z hz => (hb z hz).1) hβ hle s⟩

end PeriodicAttractiveLogGas.FixedParticleBounds
