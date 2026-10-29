import DGPS.Examples.RoughBoundary.FeatureRough
import DGPS.Examples.RoughBoundary.FreeEnergy
import DGPS.Examples.RoughBoundary.Nonlinear
import DGPS.Examples.RoughBoundary.SpikesNowhereL2
import DGPS.Model.ScalarRate

/-!
# Finite scalar dissipation exactly means zero feature mean (RUF032)

Source: `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 4.2.

For the rough product model `W_{L,ε}(x,y) = κ (1 - U(x)·U(y))` with `ε ≠ 0`, every
absolute-admissible `ρ = u²` and every weak-drift provider `b`, the scalar dissipation
`D(ρ) = ∫⁻ |2u' + u b_ρ|²` is finite exactly when the feature mean `M(ρ) = ∫ U ρ dm` vanishes.
On that class `D(ρ) = 4 ∫ |u'|²` and (under the exact free-energy decomposition of RUF027)
`G(ρ) = H(ρ m | m)`. If `M ≠ 0` and `G > 0` the quotient `D/(2G)` is `⊤`, with finite positive
denominator `2G`.

Design choices (R5 notes).
* `ε ≠ 0` is assumed (needed for the directional roughness of RUF007); `L > 0` is arbitrary.
* The identification `G = H(ρ m | m)` uses `FreeEnergyDecomposition L ε` (RUF027) as hypothesis,
  since `F_* = κ/2` is only proved for the selected parameters.
* The statement is for every weak-drift provider `b`; they all agree with the explicit force.
-/

open MeasureTheory Filter Set
open scoped ENNReal NNReal Real

namespace DGPS.Examples.RoughBoundary.Nonlinear

open DGPS.Examples.RoughBoundary.Feature DGPS.Examples.RoughBoundary.Model
open DGPS.Examples.RoughBoundary.Spikes (pt measurable_pt integral_haar_eq)
open DGPS.Examples.RoughBoundary.FreeEnergy (FreeEnergyDecomposition meanFeature)

lemma enorm_sq_eq_ofReal (r : ℝ) : ‖r‖ₑ ^ 2 = ENNReal.ofReal (r ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg r), Real.norm_eq_abs, sq_abs]

/-- Local roughness on the torus: a continuous normalized `w` times `M·U'` is not in `L²`. -/
lemma false_of_finite_weighted_directional {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : ε ≠ 0)
    {w : Torus 1 → ℝ} (hw : Continuous w) (hmass : ∫ x, w x ^ 2 ∂haar 1 = 1)
    {M : EuclideanSpace ℝ (Fin 2)} (hM : M ≠ 0)
    (hfin : ∫⁻ x, ‖w x * inner ℝ M (Uprime L ε x)‖ₑ ^ 2 ∂haar 1 < ⊤) : False := by
  -- a point of `(0,1)` where `w ∘ pt` is nonzero
  have hcφ : Continuous fun t : ℝ => w (pt t) := hw.comp (SharpLSI.continuous_liftT.comp (continuous_pi fun _ => continuous_id))
  obtain ⟨t0, ht0, hne⟩ : ∃ t0 ∈ Ioo (0 : ℝ) 1, w (pt t0) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 : ∫ x, w x ^ 2 ∂haar 1 = ∫ t in Ioc (0 : ℝ) 1, w (pt t) ^ 2 :=
      integral_haar_eq (F := fun x => w x ^ 2) (hw.pow 2).aestronglyMeasurable
    rw [integral_Ioc_eq_integral_Ioo] at h1
    have h2 : ∫ t in Ioo (0 : ℝ) 1, w (pt t) ^ 2 = 0 := by
      rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ))
        (fun t ht => by simp [hcon t ht])]
      simp
    rw [h2] at h1
    rw [hmass] at h1
    exact one_ne_zero h1
  set d : ℝ := |w (pt t0)| / 2 with hd
  have hdpos : 0 < d := by rw [hd]; have := abs_pos.2 hne; linarith
  set J : Set ℝ := Ioo 0 1 ∩ {t | d < |w (pt t)|} with hJ
  have hJo : IsOpen J :=
    isOpen_Ioo.inter (isOpen_lt continuous_const (continuous_abs.comp hcφ))
  have hJne : J.Nonempty := ⟨t0, ht0, by
    show d < |w (pt t0)|
    rw [hd]; have := abs_pos.2 hne; linarith⟩
  have hMne := every_nonzero_direction_is_rough hL hε hJo hJne hM
  refine hMne.2.2 ?_
  have hmeasU : Measurable fun t : ℝ => inner ℝ M (Uprime L ε (pt t)) :=
    (measurable_const.inner (measurable_Uprime_vec hL ε)).comp measurable_pt
  have hmeasF : Measurable fun x : Torus 1 => ‖w x * inner ℝ M (Uprime L ε x)‖ₑ ^ 2 :=
    (((hw.measurable.mul (measurable_const.inner (measurable_Uprime_vec hL ε))).enorm)).pow_const 2
  have hbound : ∫⁻ t in J, ‖inner ℝ M (Uprime L ε (pt t))‖ₑ ^ 2 ≤
      (‖d⁻¹‖ₑ ^ 2) * ∫⁻ x, ‖w x * inner ℝ M (Uprime L ε x)‖ₑ ^ 2 ∂haar 1 := by
    have h1 : ∫⁻ t in J, ‖inner ℝ M (Uprime L ε (pt t))‖ₑ ^ 2 ≤
        ∫⁻ t in J, (‖d⁻¹‖ₑ ^ 2) * ‖w (pt t) * inner ℝ M (Uprime L ε (pt t))‖ₑ ^ 2 := by
      refine setLIntegral_mono' hJo.measurableSet fun t ht => ?_
      have hdt : d < |w (pt t)| := ht.2
      have : ‖inner ℝ M (Uprime L ε (pt t))‖ₑ ≤
          ‖d⁻¹‖ₑ * ‖w (pt t) * inner ℝ M (Uprime L ε (pt t))‖ₑ := by
        rw [← enorm_mul]
        refine enorm_le_iff_norm_le.2 ?_
        rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos hdpos]
        have h0 : 0 ≤ ‖inner ℝ M (Uprime L ε (pt t))‖ := norm_nonneg _
        have : d⁻¹ * (|w (pt t)| * ‖inner ℝ M (Uprime L ε (pt t))‖) ≥
            d⁻¹ * (d * ‖inner ℝ M (Uprime L ε (pt t))‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdt.le h0)
            (inv_nonneg.2 hdpos.le)
        rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hdpos.ne', one_mul] at this
        rw [← mul_assoc]
        exact this
      calc ‖inner ℝ M (Uprime L ε (pt t))‖ₑ ^ 2
          ≤ (‖d⁻¹‖ₑ * ‖w (pt t) * inner ℝ M (Uprime L ε (pt t))‖ₑ) ^ 2 := by gcongr
        _ = _ := by rw [mul_pow]
    refine h1.trans ?_
    rw [lintegral_const_mul' _ _ (by
      have : ‖d⁻¹‖ₑ ≠ ⊤ := enorm_ne_top
      exact ENNReal.pow_ne_top this)]
    refine mul_le_mul_right ?_ _
    calc ∫⁻ t in J, ‖w (pt t) * inner ℝ M (Uprime L ε (pt t))‖ₑ ^ 2
        ≤ ∫⁻ t in Ioo (0 : ℝ) 1, ‖w (pt t) * inner ℝ M (Uprime L ε (pt t))‖ₑ ^ 2 :=
          lintegral_mono_set inter_subset_left
      _ = ∫⁻ x in pt '' Ioo (0 : ℝ) 1, ‖w x * inner ℝ M (Uprime L ε x)‖ₑ ^ 2 ∂haar 1 :=
          (DGPS.Examples.RoughBoundary.Spikes.nl_lintegral_pt (a := 0) (b := 1) (by norm_num)
            _ hmeasF).symm
      _ ≤ _ := setLIntegral_le_lintegral _ _
  have hlt : ∫⁻ t in J, ‖inner ℝ M (Uprime L ε (pt t))‖ₑ ^ 2 < ⊤ :=
    lt_of_le_of_lt hbound (ENNReal.mul_lt_top (by
      have : ‖d⁻¹‖ₑ ≠ ⊤ := enorm_ne_top
      exact ENNReal.pow_lt_top (lt_top_iff_ne_top.2 this)) hfin)
  -- translate to `MemLp` on `J`
  have e : (fun t : ℝ => inner ℝ M ((2 * π * dtheta L ε t) • Jrot (Ureal L ε t))) =
      fun t => inner ℝ M (Uprime L ε (pt t)) := funext fun t => by rw [Uprime_pt hL]
  rw [e]
  rw [MemLp, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by simp)]
  · simpa using hlt
  · exact hmeasU.aestronglyMeasurable


lemma norm_tangent_one (v : Tangent 1) : ‖v‖ ^ 2 = v 0 ^ 2 := by
  simp [EuclideanSpace.norm_eq, Real.sq_sqrt (sq_nonneg _)]

/-- The provider's force equals the explicit force a.e. -/
lemma force_ae_eq {L : ℝ} (hL : 0 < L) (ε : ℝ) (b : AbsoluteDrift (modelData hL ε))
    (ρ : AbsoluteDensity 1) : b.force ρ =ᵐ[haar 1] forceVec L ε (featureMean L ε ρ) := by
  have h1 := isWeakGradientLp_potential hL ε ρ (p := 1) le_rfl one_lt_two
  rw [ENNReal.ofReal_one] at h1
  exact b.ae_eq_of_isWeakGradient ρ h1

/-- The scalar dissipation is the extended integral of the explicit score. -/
lemma scalarDissipation_eq {L : ℝ} (hL : 0 < L) (ε : ℝ) (b : AbsoluteDrift (modelData hL ε))
    (ρ : AbsoluteDensity 1) :
    scalarDissipation (modelData hL ε) b ρ =
      ∫⁻ x, ‖forceScore L ε ρ (weakGradient ρ.sqrt ρ.sqrt_mem) x‖ₑ ^ 2 ∂haar 1 := by
  unfold scalarDissipation
  refine lintegral_congr_ae ?_
  filter_upwards [force_ae_eq hL ε b ρ] with x hx
  rw [enorm_sq_eq_ofReal, norm_tangent_one]
  congr 2
  simp only [scalarScore, forceScore, hx, forceVec]
  simp
  ring

lemma memLp_two_of_lintegral_lt_top {f : Torus 1 → ℝ} (hf : AEStronglyMeasurable f (haar 1))
    (h : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂haar 1 < ⊤) : MemLp f 2 (haar 1) := by
  rw [MemLp, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by simp)]
  · simpa using h
  · exact hf

lemma lintegral_lt_top_of_memLp_two {f : Torus 1 → ℝ} (h : MemLp f 2 (haar 1)) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂haar 1 < ⊤ := by
  have := h.eLpNorm_lt_top
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by simp)
    h.aestronglyMeasurable] at this
  simpa using this

/-- Finite dissipation forces `M = 0`. -/
lemma featureMean_eq_zero_of_finite {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : ε ≠ 0)
    (b : AbsoluteDrift (modelData hL ε)) (ρ : AbsoluteDensity 1)
    (hD : scalarDissipation (modelData hL ε) b ρ < ⊤) : featureMean L ε ρ = 0 := by
  by_contra hM
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  set g := weakGradient ρ.sqrt ρ.sqrt_mem with hg
  rw [scalarDissipation_eq hL ε b ρ] at hD
  have hS : MemLp (forceScore L ε ρ g) 2 (haar 1) := by
    refine memLp_two_of_lintegral_lt_top ?_ hD
    have := memLp_forceScore hL ε ρ hw (p := 1) le_rfl one_lt_two
    exact this.aestronglyMeasurable
  have hg0 : MemLp (fun x => g x 0) 2 (haar 1) := memLp_coord_of_memLp hw.memLp_grad 0
  have hK : MemLp (fun x => kappa * (ρ.sqrt x * inner ℝ (featureMean L ε ρ) (Uprime L ε x))) 2
      (haar 1) := by
    have e : (fun x => kappa * (ρ.sqrt x * inner ℝ (featureMean L ε ρ) (Uprime L ε x))) =
        (fun x => 2 * g x 0) - forceScore L ε ρ g := by
      funext x; simp only [Pi.sub_apply, forceScore]; ring
    rw [e]
    exact (hg0.const_mul 2).sub hS
  obtain ⟨w, hwc, hwae, -, -⟩ := exists_continuous_rep_one hw
  have hmass : ∫ x, w x ^ 2 ∂haar 1 = 1 := by
    exact (integral_congr_ae (hwae.mono fun x hx => by simp [hx])).trans ρ.mass_one
  refine false_of_finite_weighted_directional hL hε hwc hmass hM ?_
  have hk0 : kappa ≠ 0 := by unfold kappa; norm_num
  have hlt := lintegral_lt_top_of_memLp_two hK
  have h1 : ∫⁻ x, ‖w x * inner ℝ (featureMean L ε ρ) (Uprime L ε x)‖ₑ ^ 2 ∂haar 1 =
      ‖kappa⁻¹‖ₑ ^ 2 * ∫⁻ x, ‖kappa * (ρ.sqrt x *
        inner ℝ (featureMean L ε ρ) (Uprime L ε x))‖ₑ ^ 2 ∂haar 1 := by
    rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top)]
    refine lintegral_congr_ae (hwae.mono fun x hx => ?_)
    simp only
    rw [← hx, ← mul_pow, ← enorm_mul, ← mul_assoc, inv_mul_cancel₀ hk0, one_mul]
  rw [h1]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top enorm_lt_top) hlt

lemma meanFeature_densityMeasure (L ε : ℝ) (ρ : AbsoluteDensity 1) :
    meanFeature L ε (densityMeasure ρ : Measure (Torus 1)) = featureMean L ε ρ := by
  rw [meanFeature, densityMeasure_coe, featureMean]
  rw [integral_withDensity_eq_integral_toReal_smul₀ (f := fun x => ENNReal.ofReal (ρ.sqrt x ^ 2))
    (ENNReal.measurable_ofReal.comp_aemeasurable (ρ.memLp_sqrt.aestronglyMeasurable.aemeasurable.pow_const 2))
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), AbsoluteDensity.density]

/-- On `M = 0` the dissipation is `4 ∫ |u'|²`. -/
lemma scalarDissipation_eq_of_zero {L : ℝ} (hL : 0 < L) (ε : ℝ)
    (b : AbsoluteDrift (modelData hL ε)) (ρ : AbsoluteDensity 1)
    (hM : featureMean L ε ρ = 0) :
    scalarDissipation (modelData hL ε) b ρ =
      ENNReal.ofReal (4 * ∫ x, ‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2 ∂haar 1) := by
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  have hint : Integrable (fun x => ‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2) (haar 1) :=
    hw.memLp_grad.norm.integrable_sq
  rw [scalarDissipation_eq hL ε b ρ, ← integral_const_mul,
    ofReal_integral_eq_lintegral_ofReal (hint.const_mul 4)
      (Filter.Eventually.of_forall fun x => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [enorm_sq_eq_ofReal]
  congr 1
  simp only [forceScore, hM, inner_zero_left, mul_zero, sub_zero]
  rw [norm_tangent_one]
  ring

/-- Under the exact decomposition and `M = 0`, the gap is `H(ρ m | m)`. -/
lemma scalarGap_eq_of_zero {L : ℝ} (hL : 0 < L) {ε : ℝ} (hdec : FreeEnergyDecomposition L ε)
    (ρ : AbsoluteDensity 1) (hM : featureMean L ε ρ = 0) :
    (scalarGap (modelData hL ε) ρ : ℝ≥0∞) =
      relativeEntropy (densityMeasure ρ : Measure (Torus 1)) (haar 1) := by
  obtain ⟨h1, -, -, hmin, -⟩ := hdec hL
  have hF := (h1 (densityMeasure ρ)).2
  rw [meanFeature_densityMeasure, hM] at hF
  have hc := coe_densityFreeEnergy (modelData hL ε) ρ
  have hm := coe_freeEnergyMinimumReal (modelData hL ε)
  rw [hmin] at hm
  have hm' : freeEnergyMinimumReal (modelData hL ε) = kappa / 2 := EReal.coe_eq_coe_iff.1 hm
  rw [hF] at hc
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    EReal.coe_zero, add_zero] at hc
  have hne : relativeEntropy (densityMeasure ρ : Measure (Torus 1)) (haar 1) ≠ ⊤ := by
    intro htop
    rw [htop] at hc
    simp at hc
  lift relativeEntropy (densityMeasure ρ : Measure (Torus 1)) (haar 1) to ℝ≥0 using hne with h hh
  rw [ENNReal.coe_inj]
  apply NNReal.eq
  rw [coe_scalarGap, hm']
  have h2 : ((h : ℝ≥0∞) : EReal) = ((h : ℝ) : EReal) := rfl
  rw [h2, ← EReal.coe_add, EReal.coe_eq_coe_iff] at hc
  linarith

/-- **RUF032.** For every absolute-admissible `ρ` (and every weak-drift provider `b`), the scalar
dissipation is finite iff the feature mean vanishes. On that class `D = 4 ∫ |(√ρ)'|²` and
`G = H(ρ m | m)`; if `M ≠ 0` and `G > 0` then `D/(2G) = ⊤` with `0 < 2G < ⊤`. -/
theorem finite_scalar_dissipation_exactly_means_zero_feature_mean {L : ℝ} (hL : 0 < L) {ε : ℝ}
    (hε : ε ≠ 0) (hdec : FreeEnergyDecomposition L ε) (b : AbsoluteDrift (modelData hL ε))
    (ρ : AbsoluteDensity 1) :
    (scalarDissipation (modelData hL ε) b ρ < ⊤ ↔ featureMean L ε ρ = 0) ∧
    (featureMean L ε ρ = 0 →
      scalarDissipation (modelData hL ε) b ρ =
          ENNReal.ofReal (4 * ∫ x, ‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2 ∂haar 1) ∧
        (scalarGap (modelData hL ε) ρ : ℝ≥0∞) =
          relativeEntropy (densityMeasure ρ : Measure (Torus 1)) (haar 1)) ∧
    (featureMean L ε ρ ≠ 0 → 0 < scalarGap (modelData hL ε) ρ →
      scalarQuotient (modelData hL ε) b ρ = ⊤ ∧
        0 < 2 * (scalarGap (modelData hL ε) ρ : ℝ≥0∞) ∧
        2 * (scalarGap (modelData hL ε) ρ : ℝ≥0∞) < ⊤) := by
  have hiff : scalarDissipation (modelData hL ε) b ρ < ⊤ ↔ featureMean L ε ρ = 0 :=
    ⟨featureMean_eq_zero_of_finite hL hε b ρ, fun hM => by
      rw [scalarDissipation_eq_of_zero hL ε b ρ hM]; exact ENNReal.ofReal_lt_top⟩
  refine ⟨hiff, fun hM => ⟨scalarDissipation_eq_of_zero hL ε b ρ hM,
    scalarGap_eq_of_zero hL hdec ρ hM⟩, fun hM hG => ?_⟩
  have hD : scalarDissipation (modelData hL ε) b ρ = ⊤ :=
    top_le_iff.1 (not_lt.1 fun h => hM (hiff.1 h))
  have h0 : 0 < 2 * (scalarGap (modelData hL ε) ρ : ℝ≥0∞) := by
    simpa using hG
  have h1 : 2 * (scalarGap (modelData hL ε) ρ : ℝ≥0∞) < ⊤ :=
    ENNReal.mul_lt_top (by simp) ENNReal.coe_lt_top
  refine ⟨?_, h0, h1⟩
  unfold scalarQuotient
  rw [hD, ENNReal.top_div_of_ne_top h1.ne]

end DGPS.Examples.RoughBoundary.Nonlinear
