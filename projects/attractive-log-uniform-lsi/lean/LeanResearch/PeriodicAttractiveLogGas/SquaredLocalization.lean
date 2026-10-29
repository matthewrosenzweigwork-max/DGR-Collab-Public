import LeanResearch.PeriodicAttractiveLogGas.FiniteEntropyCalculus
import LeanResearch.PeriodicAttractiveLogGas.RelativeEntropyVariational
import LeanResearch.PeriodicAttractiveLogGas.HeavyLocalization

/-! Squared localization and entropy, manuscript Lemma 7.4.
The two products and their gradients are the actual physical functions.
The logarithmic formula is used only after proving its integrability. -/
noncomputable section
open MeasureTheory Filter Set InnerProductSpace
open scoped ENNReal NNReal BigOperators Topology
namespace PeriodicAttractiveLogGas.SquaredLocalization

section Entropy
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem entropy_log_form {F : Ω → ℝ} (hn : 0 ≤ᵐ[μ] F)
    (hi : Integrable F μ) (hl : Integrable (fun x => F x * Real.log (F x)) μ) :
    entropy μ F = ((∫ x, F x * (Real.log (F x) - Real.log (∫ y, F y ∂μ)) ∂μ : ℝ) : EReal) := by
  rw [entropy_eq_integral hn hl]
  simp_rw [mul_sub]
  rw [integral_sub hl (hi.mul_const _), integral_mul_const]

/-- Log-sum subadditivity, including zero means and exceptional null sets. -/
theorem entropy_add_le {F G : Ω → ℝ} (hF : Measurable F) (hG : Measurable G)
    {K L : ℝ} (hbF : ∀ᵐ x ∂μ, 0 ≤ F x ∧ F x ≤ K)
    (hbG : ∀ᵐ x ∂μ, 0 ≤ G x ∧ G x ≤ L) :
    entropy μ (fun x => F x + G x) ≤ entropy μ F + entropy μ G := by
  obtain ⟨hiF, hlF⟩ := RelativeEntropyVariational.bounded_density_integrable hF hbF
  obtain ⟨hiG, hlG⟩ := RelativeEntropyVariational.bounded_density_integrable hG hbG
  have hnF : 0 ≤ᵐ[μ] F := hbF.mono fun _ h => h.1
  have hnG : 0 ≤ᵐ[μ] G := hbG.mono fun _ h => h.1
  by_cases hA : (∫ x, F x ∂μ) = 0
  · have hz : F =ᵐ[μ] (fun _ => 0) := by
      filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnF hiF).mp hA] with x hx
      simpa only [Pi.zero_apply] using hx
    have hs : (fun x => F x + G x) =ᵐ[μ] G :=
      hz.mono fun x hx => by simp only [hx, zero_add]
    rw [entropy_congr_ae hs, entropy_congr_ae hz, entropy_zero, zero_add]
  by_cases hB : (∫ x, G x ∂μ) = 0
  · have hz : G =ᵐ[μ] (fun _ => 0) := by
      filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnG hiG).mp hB] with x hx
      simpa only [Pi.zero_apply] using hx
    have hs : (fun x => F x + G x) =ᵐ[μ] F :=
      hz.mono fun x hx => by simp only [hx, add_zero]
    rw [entropy_congr_ae hs, entropy_congr_ae hz, entropy_zero, add_zero]
  have hAp : 0 < ∫ x, F x ∂μ :=
    lt_of_le_of_ne (integral_nonneg_of_ae hnF) (Ne.symm hA)
  have hBp : 0 < ∫ x, G x ∂μ :=
    lt_of_le_of_ne (integral_nonneg_of_ae hnG) (Ne.symm hB)
  have hbS : ∀ᵐ x ∂μ, 0 ≤ F x + G x ∧ F x + G x ≤ K + L := by
    filter_upwards [hbF, hbG] with x hx hy
    exact ⟨add_nonneg hx.1 hy.1, add_le_add hx.2 hy.2⟩
  obtain ⟨hiS, hlS⟩ := RelativeEntropyVariational.bounded_density_integrable (hF.add hG) hbS
  have hnS := hbS.mono fun _ h => h.1
  have hi1 : Integrable (fun x => F x * (Real.log (F x) - Real.log (∫ y, F y ∂μ))) μ := by
    simp_rw [mul_sub]
    exact hlF.sub (hiF.mul_const _)
  have hi2 : Integrable (fun x => G x * (Real.log (G x) - Real.log (∫ y, G y ∂μ))) μ := by
    simp_rw [mul_sub]
    exact hlG.sub (hiG.mul_const _)
  have hi3 : Integrable (fun x => (F x + G x) *
      (Real.log (F x + G x) - Real.log ((∫ y, F y ∂μ) + ∫ y, G y ∂μ))) μ := by
    simp_rw [mul_sub]
    exact hlS.sub (hiS.mul_const _)
  have hh := integral_mono_ae hi3 (hi1.add hi2) (by
    filter_upwards [hnF, hnG] with x hx hy
    exact FiniteEntropyCalculus.two_term_log_sum hx hy hAp hBp)
  simp only [Pi.add_apply] at hh
  rw [integral_add hi1 hi2] at hh
  rw [entropy_log_form hnS hiS hlS, entropy_log_form hnF hiF hlF,
    entropy_log_form hnG hiG hlG, ← EReal.coe_add, integral_add hiF hiG]
  exact EReal.coe_le_coe_iff.mpr hh
end Entropy

section Physical
variable {N : ℕ}

def cosMap (θ : C(Configuration N, ℝ)) : C(Configuration N, ℝ) :=
  ⟨fun X => Real.cos (θ X), Real.continuous_cos.comp θ.continuous⟩

def sinMap (θ : C(Configuration N, ℝ)) : C(Configuration N, ℝ) :=
  ⟨fun X => Real.sin (θ X), Real.continuous_sin.comp θ.continuous⟩

@[simp] theorem cosMap_apply (θ : C(Configuration N, ℝ)) (X : Configuration N) :
    cosMap θ X = Real.cos (θ X) := rfl
@[simp] theorem sinMap_apply (θ : C(Configuration N, ℝ)) (X : Configuration N) :
    sinMap θ X = Real.sin (θ X) := rfl

theorem cosMap_lipschitz (θ : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hθ : LipschitzWith L (fun y => θ (configurationQuotient N y))) :
    LipschitzWith L (fun y => cosMap θ (configurationQuotient N y)) := by
  simpa only [one_mul, Function.comp_def, cosMap_apply] using Real.lipschitzWith_cos.comp hθ

theorem sinMap_lipschitz (θ : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hθ : LipschitzWith L (fun y => θ (configurationQuotient N y))) :
    LipschitzWith L (fun y => sinMap θ (configurationQuotient N y)) := by
  simpa only [one_mul, Function.comp_def, sinMap_apply] using Real.lipschitzWith_sin.comp hθ

private theorem innerSL_injective_real {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v w : E} (h : innerSL ℝ v = innerSL ℝ w) : v = w := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  calc
    ‖v - w‖ = ‖innerSL ℝ (v - w)‖ := (innerSL_apply_norm ℝ (v - w)).symm
    _ = 0 := by rw [map_sub, h, sub_self, norm_zero]

/-- Scalar chain rule for the actual descended Riesz gradient. -/
theorem ae_scalar_chain_rule (μ : Measure (Configuration N)) (hμ : μ ≪ referenceMeasure N)
    (θ : C(Configuration N, ℝ)) {K L : ℝ≥0} {φ φ' : ℝ → ℝ}
    (hθ : LipschitzWith K (fun y => θ (configurationQuotient N y)))
    (hφ : LipschitzWith L φ) (hdφ : ∀ z, HasDerivAt φ (φ' z) z) :
    ∀ᵐ X ∂μ, descendedLiftGradient ⟨fun X => φ (θ X), hφ.continuous.comp θ.continuous⟩ X =
      φ' (θ X) • descendedLiftGradient θ X := by
  let ψ : C(Configuration N, ℝ) :=
    ⟨fun X => φ (θ X), hφ.continuous.comp θ.continuous⟩
  have hψ : LipschitzWith (L * K) (fun y => ψ (configurationQuotient N y)) := hφ.comp hθ
  change ∀ᵐ X ∂μ, descendedLiftGradient ψ X = φ' (θ X) • descendedLiftGradient θ X
  filter_upwards [ae_hasFDerivAt_configurationLift_of_absolutelyContinuous θ hθ hμ,
    ae_hasFDerivAt_configurationLift_of_absolutelyContinuous ψ hψ hμ] with X hdθ hdψ
  let y := configurationCenteredLift X
  have hy : configurationQuotient N y = X := configurationQuotient_centeredLift X
  have he := (hdψ y hy).unique
    (HasDerivAt.comp_hasFDerivAt y (hdφ _) (hdθ y hy))
  apply innerSL_injective_real
  calc
    _ = φ' (θ X) • innerSL ℝ (descendedLiftGradient θ X) := by
      simpa only [hy] using he
    _ = _ := by
      ext v
      simp only [smul_apply, innerSL_apply_apply, inner_smul_left, conj_trivial, smul_eq_mul]

theorem ae_cosMap_gradient (μ : Measure (Configuration N)) (hμ : μ ≪ referenceMeasure N)
    (θ : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hθ : LipschitzWith L (fun y => θ (configurationQuotient N y))) :
    ∀ᵐ X ∂μ, descendedLiftGradient (cosMap θ) X =
      (-Real.sin (θ X)) • descendedLiftGradient θ X := by
  simpa only [cosMap] using
    ae_scalar_chain_rule μ hμ θ hθ Real.lipschitzWith_cos Real.hasDerivAt_cos

theorem ae_sinMap_gradient (μ : Measure (Configuration N)) (hμ : μ ≪ referenceMeasure N)
    (θ : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hθ : LipschitzWith L (fun y => θ (configurationQuotient N y))) :
    ∀ᵐ X ∂μ, descendedLiftGradient (sinMap θ) X =
      Real.cos (θ X) • descendedLiftGradient θ X := by
  simpa only [sinMap] using
    ae_scalar_chain_rule μ hμ θ hθ Real.lipschitzWith_sin Real.hasDerivAt_sin

theorem ae_cutoff_gradient_sum (μ : Measure (Configuration N)) (hμ : μ ≪ referenceMeasure N)
    (θ : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hθ : LipschitzWith L (fun y => θ (configurationQuotient N y))) :
    ∀ᵐ X ∂μ, ‖descendedLiftGradient (cosMap θ) X‖ ^ 2 +
      ‖descendedLiftGradient (sinMap θ) X‖ ^ 2 = ‖descendedLiftGradient θ X‖ ^ 2 := by
  filter_upwards [ae_cosMap_gradient μ hμ θ hθ, ae_sinMap_gradient μ hμ θ hθ] with X hc hs
  rw [hc, hs]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq]
  rw [← add_mul, add_comm (Real.sin (θ X) ^ 2), Real.cos_sq_add_sin_sq, one_mul]

theorem square_partition (F θ : C(Configuration N, ℝ)) (X : Configuration N) :
    (cosMap θ * F) X ^ 2 + (sinMap θ * F) X ^ 2 = F X ^ 2 := by
  change (Real.cos (θ X) * F X) ^ 2 + (Real.sin (θ X) * F X) ^ 2 = _
  calc
    _ = (Real.cos (θ X) ^ 2 + Real.sin (θ X) ^ 2) * F X ^ 2 := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq, one_mul]

/-- The mixed gradient terms cancel on an actual full-measure set. -/
theorem ae_squared_localization (μ : Measure (Configuration N)) (hμ : μ ≪ referenceMeasure N)
    (F θ : C(Configuration N, ℝ)) {K L : ℝ≥0}
    (hF : LipschitzWith K (fun y => F (configurationQuotient N y)))
    (hθ : LipschitzWith L (fun y => θ (configurationQuotient N y))) :
    ∀ᵐ X ∂μ, ‖descendedLiftGradient (cosMap θ * F) X‖ ^ 2 +
      ‖descendedLiftGradient (sinMap θ * F) X‖ ^ 2 =
      ‖descendedLiftGradient F X‖ ^ 2 + F X ^ 2 * ‖descendedLiftGradient θ X‖ ^ 2 := by
  let u : Fin 2 → C(Configuration N, ℝ) := ![cosMap θ, sinMap θ]
  have hu : ∀ i, LipschitzWith L (fun y => u i (configurationQuotient N y)) := by
    intro i
    fin_cases i
    · exact cosMap_lipschitz θ hθ
    · exact sinMap_lipschitz θ hθ
  have hp : ∀ X, F X ≠ 0 → (∑ i, u i X ^ 2) = 1 := by
    intro X _
    rw [Fin.sum_univ_two]
    exact Real.cos_sq_add_sin_sq (θ X)
  filter_upwards [HeavyLocalization.ae_finite_ims μ hμ F u hF hu hp,
    ae_cutoff_gradient_sum μ hμ θ hθ] with X hi hs
  simp only [Fin.sum_univ_two] at hi
  change ‖descendedLiftGradient (cosMap θ * F) X‖ ^ 2 +
      ‖descendedLiftGradient (sinMap θ * F) X‖ ^ 2 =
      ‖descendedLiftGradient F X‖ ^ 2 + F X ^ 2 *
        (‖descendedLiftGradient (cosMap θ) X‖ ^ 2 + ‖descendedLiftGradient (sinMap θ) X‖ ^ 2) at hi
  exact hi.trans (by rw [hs])

theorem squared_localization_integral (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (hμ : μ ≪ referenceMeasure N) (F θ : C(Configuration N, ℝ)) {K L : ℝ≥0}
    (hF : LipschitzWith K (fun y => F (configurationQuotient N y)))
    (hθ : LipschitzWith L (fun y => θ (configurationQuotient N y))) :
    (∫ X, ‖descendedLiftGradient (cosMap θ * F) X‖ ^ 2 ∂μ) +
      (∫ X, ‖descendedLiftGradient (sinMap θ * F) X‖ ^ 2 ∂μ) =
      (∫ X, ‖descendedLiftGradient F X‖ ^ 2 ∂μ) +
        ∫ X, F X ^ 2 * ‖descendedLiftGradient θ X‖ ^ 2 ∂μ := by
  have hc := integrable_sq_norm_descendedLiftGradient μ (cosMap θ * F)
    (HeavyLocalization.lipschitz_lift_mul _ _ (cosMap_lipschitz θ hθ) hF)
  have hs := integrable_sq_norm_descendedLiftGradient μ (sinMap θ * F)
    (HeavyLocalization.lipschitz_lift_mul _ _ (sinMap_lipschitz θ hθ) hF)
  have hcost : Integrable (fun X => F X ^ 2 * ‖descendedLiftGradient θ X‖ ^ 2) μ := by
    apply (integrable_sq_norm_descendedLiftGradient μ θ hθ).bdd_mul
      (F.continuous.measurable.pow_const 2).aestronglyMeasurable
    filter_upwards [] with X
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (F.norm_coe_le_norm X) 2
  rw [← integral_add hc hs,
    integral_congr_ae (ae_squared_localization μ hμ F θ hF hθ),
    integral_add (integrable_sq_norm_descendedLiftGradient μ F hF) hcost]

theorem continuous_square_bound (F : C(Configuration N, ℝ)) (X : Configuration N) :
    0 ≤ F X ^ 2 ∧ F X ^ 2 ≤ ‖F‖ ^ 2 := by
  refine ⟨sq_nonneg _, ?_⟩
  simpa only [Real.norm_eq_abs, sq_abs] using
    pow_le_pow_left₀ (norm_nonneg _) (F.norm_coe_le_norm X) 2

theorem entropy_square_split (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (F θ : C(Configuration N, ℝ)) :
    entropy μ (fun X => F X ^ 2) ≤
      entropy μ (fun X => (cosMap θ * F) X ^ 2) +
        entropy μ (fun X => (sinMap θ * F) X ^ 2) := by
  have h := entropy_add_le ((cosMap θ * F).continuous.measurable.pow_const 2)
    ((sinMap θ * F).continuous.measurable.pow_const 2)
    (Eventually.of_forall (continuous_square_bound (cosMap θ * F)))
    (Eventually.of_forall (continuous_square_bound (sinMap θ * F))) (μ := μ)
  simpa only [square_partition] using h
end Physical
end PeriodicAttractiveLogGas.SquaredLocalization
