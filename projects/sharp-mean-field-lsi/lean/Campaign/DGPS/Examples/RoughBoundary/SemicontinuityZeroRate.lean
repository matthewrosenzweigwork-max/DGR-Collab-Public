import DGPS.Examples.RoughBoundary.FreeEnergy
import DGPS.Examples.RoughBoundary.SemicontinuityPersistence
import DGPS.Variational.ZeroDissipation
import DGPS.Variational.SpeciesInclusion
import DGPS.Foundations.SobolevEmbedding

/-!
# SEM010: a smooth positive-gap Gibbs competitor forces both rates to zero

For a smooth unit-norm feature `U` with the landscape certificate and a critical point `t` of
`Ψ_U` with `Ψ_U t > 0`, the Gibbs competitor `q = exp(⟨t, U⟩ - Λ_U t)` is a frozen-Gibbs fixed point
(self-consistency `t = κ M(q)`), hence has `√q ∈ H¹`, zero score and zero dissipation, and gap
`Ψ_U t > 0`; so `r_* = r_ms = 0`.
-/

open MeasureTheory InformationTheory
open scoped ENNReal NNReal

namespace DGPS.Examples.RoughBoundary.Semicontinuity

open DGPS.Examples.RoughBoundary.Landscape
open DGPS.Examples.RoughBoundary.Model (kappa)
open DGPS.Examples.RoughBoundary.FreeEnergy (klDiv_tilted_right coe_eq_toReal kappa_eq kappa_pos
  pd_expPhi)

/-- The model interaction `W_U(x,y) = κ (1 - ⟪U x, U y⟫)` of a feature `U`. -/
noncomputable def featureW (U : Torus 1 → E2) (x y : Torus 1) : ℝ :=
  kappa * (1 - inner ℝ (U x) (U y))

lemma continuous_featureW {U : Torus 1 → E2} (hc : Continuous U) :
    Continuous (fun q : Torus 1 × Torus 1 => featureW U q.1 q.2) := by
  unfold featureW
  exact continuous_const.mul (continuous_const.sub
    ((hc.comp continuous_fst).inner (hc.comp continuous_snd)))

/-- The interaction data `V = 0`, `W = κ (1 - ⟪U x, U y⟫)` of a continuous unit-norm feature. -/
noncomputable def featureData {U : Torus 1 → E2} (hc : Continuous U) (hn : ∀ y, ‖U y‖ = 1) :
    InteractionData 1 where
  V := fun _ => 0
  W := featureW U
  V_continuous := continuous_const
  W_continuous := continuous_featureW hc
  W_symm := fun x y => by unfold featureW; rw [real_inner_comm]
  W_diag := fun x => by
    unfold featureW; rw [real_inner_self_eq_norm_sq, hn]; norm_num

/-- The mean feature `M(ν) = ∫ U dν`. -/
noncomputable def featMean (U : Torus 1 → E2) (ν : Measure (Torus 1)) : E2 := ∫ y, U y ∂ν

/-- The Gibbs tilt `q_t m` of Haar measure, `q_t = exp (⟪t, U⟫ - Λ(t))`. -/
noncomputable def featGibbs (U : Torus 1 → E2) (t : E2) : Measure (Torus 1) :=
  (DGPS.haar 1).tilted fun y => inner ℝ t (U y)

/-- The Gibbs density `q_t(y) = exp (⟪t, U y⟫ - Λ(t))` with respect to Haar measure. -/
noncomputable def featGibbsDensity (U : Torus 1 → E2) (t : E2) (y : Torus 1) : ℝ :=
  Real.exp (inner ℝ t (U y) - featureLogPartition U t)

lemma integrable_featU {U : Torus 1 → E2} (hc : Continuous U) (ν : Measure (Torus 1))
    [IsFiniteMeasure ν] : Integrable U ν :=
  hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma integrable_inner_featU {U : Torus 1 → E2} (hc : Continuous U) (ν : Measure (Torus 1))
    [IsFiniteMeasure ν] (c : E2) : Integrable (fun y => inner ℝ (U y) c) ν :=
  (hc.inner continuous_const).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma integral_inner_featU {U : Torus 1 → E2} (hc : Continuous U) (ν : Measure (Torus 1))
    [IsFiniteMeasure ν] (c : E2) : ∫ y, inner ℝ (U y) c ∂ν = inner ℝ (featMean U ν) c := by
  simp_rw [real_inner_comm c]
  exact integral_inner (integrable_featU hc ν) c

lemma featInteractionEnergy {U : Torus 1 → E2} (hc : Continuous U) (hn : ∀ y, ‖U y‖ = 1)
    (ν : ProbabilityMeasure (Torus 1)) :
    interactionEnergy (featureData hc hn) ν =
      kappa * (1 - ‖featMean U (ν : Measure (Torus 1))‖ ^ 2) := by
  rw [interactionEnergy_eq_iterated]
  have h1 : ∀ y, ∫ x, (featureData hc hn).W x y ∂(ν : Measure (Torus 1)) =
      kappa * (1 - inner ℝ (featMean U (ν : Measure (Torus 1))) (U y)) := by
    intro y
    show ∫ x, featureW U x y ∂(ν : Measure (Torus 1)) = _
    unfold featureW
    rw [integral_const_mul, integral_sub (integrable_const _) (integrable_inner_featU hc _ _),
      integral_inner_featU hc]
    simp
  simp_rw [h1]
  rw [integral_const_mul, integral_sub (integrable_const _)]
  · have := integral_inner_featU hc (ν : Measure (Torus 1))
      (featMean U (ν : Measure (Torus 1)))
    simp_rw [real_inner_comm (featMean U (ν : Measure (Torus 1)))] at this
    rw [this]
    simp
  · exact ((integrable_inner_featU hc (ν : Measure (Torus 1))
      (featMean U (ν : Measure (Torus 1)))).congr
      (Filter.Eventually.of_forall fun y => real_inner_comm _ _))

lemma integrable_exp_featTilt {U : Torus 1 → E2} (hc : Continuous U) (t : E2) :
    Integrable (fun y => Real.exp (inner ℝ t (U y))) (DGPS.haar 1) :=
  (Real.continuous_exp.comp (continuous_const.inner hc)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma isProbabilityMeasure_featGibbs {U : Torus 1 → E2} (hc : Continuous U) (t : E2) :
    IsProbabilityMeasure (featGibbs U t) :=
  isProbabilityMeasure_tilted (integrable_exp_featTilt hc t)

/-- The Gibbs tilt as a probability measure. -/
noncomputable def featGibbsProb {U : Torus 1 → E2} (hc : Continuous U) (t : E2) :
    ProbabilityMeasure (Torus 1) :=
  ⟨featGibbs U t, isProbabilityMeasure_featGibbs hc t⟩

lemma freeEnergy_feature {U : Torus 1 → E2} (hc : Continuous U) (hn : ∀ y, ‖U y‖ = 1)
    (ν : ProbabilityMeasure (Torus 1)) :
    freeEnergy (featureData hc hn) ν =
      ((relativeEntropy (ν : Measure (Torus 1)) (DGPS.haar 1) : ℝ≥0∞) : EReal) +
        ((kappa / 2 * (1 - ‖featMean U (ν : Measure (Torus 1))‖ ^ 2) : ℝ) : EReal) := by
  unfold freeEnergy
  rw [featInteractionEnergy hc hn ν, add_assoc, ← EReal.coe_add]
  congr 2
  simp [potentialEnergy, featureData]
  ring

lemma freeEnergy_feature_eq_gibbs {U : Torus 1 → E2} (hc : Continuous U) (hn : ∀ y, ‖U y‖ = 1)
    (ν : ProbabilityMeasure (Torus 1)) :
    freeEnergy (featureData hc hn) ν =
      ((kappa / 2 : ℝ) : EReal) +
        (((relativeEntropy (ν : Measure (Torus 1))
          (featGibbs U (kappa • featMean U (ν : Measure (Torus 1)))) : ℝ≥0∞) : EReal) +
        ((featurePotential kappa0 U
          (kappa • featMean U (ν : Measure (Torus 1))) : ℝ) : EReal)) := by
  set M := featMean U (ν : Measure (Torus 1)) with hM
  have := isProbabilityMeasure_featGibbs hc (kappa • M)
  rw [freeEnergy_feature hc hn, Analysis.relativeEntropy_eq_klDiv,
    Analysis.relativeEntropy_eq_klDiv]
  have hf : Integrable (fun y => inner ℝ (kappa • M) (U y)) (ν : Measure (Torus 1)) :=
    (integrable_inner_featU hc _ (kappa • M)).congr
      (Filter.Eventually.of_forall fun y => real_inner_comm _ _)
  have h := klDiv_tilted_right (m := DGPS.haar 1) (ν := (ν : Measure (Torus 1)))
    (integrable_exp_featTilt hc (kappa • M)) hf
  have hint : ∫ y, inner ℝ (kappa • M) (U y) ∂(ν : Measure (Torus 1)) =
      kappa * ‖M‖ ^ 2 := by
    have := integral_inner_featU hc (ν : Measure (Torus 1)) (kappa • M)
    simp_rw [real_inner_comm (kappa • M)] at this
    rw [this]
    rw [← hM, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hΛ : Real.log (∫ y, Real.exp (inner ℝ (kappa • M) (U y)) ∂(DGPS.haar 1)) =
      featureLogPartition U (kappa • M) := rfl
  unfold featGibbs
  rw [h, hΛ, hint, add_assoc (_ : EReal) ((_ : ℝ) : EReal), ← EReal.coe_add, add_left_comm,
    ← EReal.coe_add]
  congr 2
  unfold featurePotential
  rw [norm_smul, kappa_eq]
  have hk : (0 : ℝ) < kappa0 := kappa_eq ▸ kappa_pos
  simp only [Real.norm_eq_abs, abs_of_pos hk, mul_pow]
  rw [hM]
  field_simp
  ring

/-- Gibbs variational inequality at Haar measure: `⟪t, ∫ U dm⟫ ≤ Λ(t)`. -/
lemma inner_featMean_haar_le {U : Torus 1 → E2} (hc : Continuous U) (t : E2) :
    inner ℝ (featMean U (DGPS.haar 1)) t ≤ featureLogPartition U t := by
  have hf : Integrable (fun y => inner ℝ t (U y)) (DGPS.haar 1) :=
    (integrable_inner_featU hc _ t).congr (Filter.Eventually.of_forall fun y => real_inner_comm _ _)
  have h := klDiv_tilted_right (m := DGPS.haar 1) (ν := DGPS.haar 1)
    (integrable_exp_featTilt hc t) hf
  have hint : ∫ y, inner ℝ t (U y) ∂(DGPS.haar 1) =
      inner ℝ (featMean U (DGPS.haar 1)) t := by
    have := integral_inner_featU hc (DGPS.haar 1) t
    simp_rw [real_inner_comm t] at this
    rw [this, real_inner_comm]
  rw [klDiv_self, EReal.coe_ennreal_zero, zero_add] at h
  have h0 : (0 : EReal) ≤ _ := h ▸ EReal.coe_ennreal_nonneg _
  have h1 := EReal.coe_nonneg.mp h0
  rw [hint] at h1
  exact sub_nonneg.mp h1

lemma featMean_haar_eq_zero {U : Torus 1 → E2} (hc : Continuous U)
    (hnn : ∀ t, 0 ≤ featurePotential kappa0 U t) : featMean U (DGPS.haar 1) = 0 := by
  set M0 := featMean U (DGPS.haar 1) with hM0
  have h1 := inner_featMean_haar_le hc (kappa • M0)
  have h2 := hnn (kappa • M0)
  unfold featurePotential at h2
  have hk : (0 : ℝ) < kappa := kappa_pos
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq] at h1
  rw [norm_smul, ← kappa_eq, Real.norm_eq_abs, abs_of_pos hk] at h2
  have h3 : kappa * ‖M0‖ ^ 2 ≤ kappa * ‖M0‖ ^ 2 / 2 := by
    have : (kappa * ‖M0‖) ^ 2 / (2 * kappa) = kappa * ‖M0‖ ^ 2 / 2 := by
      field_simp
    linarith
  have h4 : ‖M0‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖M0‖]
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg M0, sq_nonneg ‖M0‖])

lemma freeEnergy_feature_haar {U : Torus 1 → E2} (hc : Continuous U) (hn : ∀ y, ‖U y‖ = 1)
    (hnn : ∀ t, 0 ≤ featurePotential kappa0 U t) :
    freeEnergy (featureData hc hn) (haarProbability 1) = ((kappa / 2 : ℝ) : EReal) := by
  rw [freeEnergy_feature]
  have hm : ((haarProbability 1 : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)) = DGPS.haar 1 :=
    rfl
  rw [hm, featMean_haar_eq_zero hc hnn, relativeEntropy_zero_iff.mpr rfl]
  simp

lemma freeEnergy_feature_ge {U : Torus 1 → E2} (hc : Continuous U) (hn : ∀ y, ‖U y‖ = 1)
    (hnn : ∀ t, 0 ≤ featurePotential kappa0 U t) (ν : ProbabilityMeasure (Torus 1)) :
    ((kappa / 2 : ℝ) : EReal) ≤ freeEnergy (featureData hc hn) ν := by
  rw [freeEnergy_feature_eq_gibbs hc hn ν]
  exact le_add_of_nonneg_right (add_nonneg (EReal.coe_ennreal_nonneg _)
    (EReal.coe_nonneg.mpr (hnn _)))

lemma freeEnergyMinimum_feature {U : Torus 1 → E2} (hc : Continuous U) (hn : ∀ y, ‖U y‖ = 1)
    (hnn : ∀ t, 0 ≤ featurePotential kappa0 U t) :
    freeEnergyMinimum (featureData hc hn) = ((kappa / 2 : ℝ) : EReal) :=
  le_antisymm (freeEnergy_feature_haar hc hn hnn ▸ iInf_le _ _)
    (le_iInf (freeEnergy_feature_ge hc hn hnn))

lemma hasFDerivAt_featureLogPartition' {U : Torus 1 → E2} (hc : Continuous U)
    (hn : ∀ y, ‖U y‖ = 1) (t : E2) :
    ∃ D : E2 →L[ℝ] ℝ, HasFDerivAt (featureLogPartition U) D t ∧
      ∀ v, D v = ∫ y, inner ℝ v (U y) ∂(featGibbs U t) := by
  have hV := hc.measurable
  have hb : ∀ᵐ y ∂(DGPS.haar 1), ‖U y‖ ≤ 1 := Filter.Eventually.of_forall fun y => (hn y).le
  have hP := hasFDerivAt_pint (μ := DGPS.haar 1) contDiff_expPhi hV hb t
  have hpos : 0 < pint (DGPS.haar 1) U expPhi t :=
    lt_of_lt_of_le (Real.exp_pos _) (exp_neg_norm_le_pint hV hb t)
  have hlog := hP.log hpos.ne'
  refine ⟨_, hlog, fun v => ?_⟩
  have hcont : Continuous (pd expPhi) := (contDiff_pd contDiff_expPhi).continuous
  have hint := integrable_pint hcont hV hb t
  have e1 : pint (DGPS.haar 1) U (pd expPhi) t v =
      ∫ y, Real.exp (inner ℝ t (U y)) * inner ℝ v (U y) ∂(DGPS.haar 1) := by
    unfold pint
    rw [ContinuousLinearMap.integral_apply hint v]
    simp_rw [pd_expPhi]
  have e2 : pint (DGPS.haar 1) U expPhi t =
      ∫ y, Real.exp (inner ℝ t (U y)) ∂(DGPS.haar 1) := rfl
  simp only [smul_apply, smul_eq_mul]
  rw [e1, e2, featGibbs, integral_tilted]
  simp_rw [smul_eq_mul, div_eq_inv_mul, mul_assoc]
  rw [integral_const_mul]

lemma critical_selfconsistent' {U : Torus 1 → E2} (hc : Continuous U) (hn : ∀ y, ‖U y‖ = 1)
    {t : E2} (hcrit : fderiv ℝ (featurePotential kappa0 U) t = 0) :
    t = kappa • featMean U (featGibbs U t) := by
  have := isProbabilityMeasure_featGibbs hc t
  obtain ⟨D, hD, hDv⟩ := hasFDerivAt_featureLogPartition' hc hn t
  have hq := (hasFDerivAt_id t).norm_sq.mul_const (2 * kappa0)⁻¹
  have hΨ := hq.sub hD
  have e : featurePotential kappa0 U =
      (fun y : E2 => ‖id y‖ ^ 2 * (2 * kappa0)⁻¹) - featureLogPartition U := by
    funext x; simp [featurePotential, div_eq_mul_inv]
  rw [e, hΨ.fderiv] at hcrit
  have hk : (0 : ℝ) < kappa := kappa_pos
  refine ext_inner_right ℝ fun v => ?_
  have h1 := congrArg (fun A : E2 →L[ℝ] ℝ => A v) hcrit
  simp only [smul_apply, sub_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, id_eq,
    zero_apply, smul_eq_mul, nsmul_eq_mul, ContinuousLinearMap.id_apply, Nat.cast_ofNat] at h1
  rw [hDv v] at h1
  have h2 := integral_inner_featU hc (featGibbs U t) v
  simp_rw [real_inner_comm v] at h2
  rw [h2] at h1
  rw [real_inner_smul_left, real_inner_comm v (featMean U (featGibbs U t))]
  rw [← kappa_eq] at h1
  field_simp at h1
  nlinarith [h1]

lemma freeEnergy_gibbs_of_selfconsistent' {U : Torus 1 → E2} (hc : Continuous U)
    (hn : ∀ y, ‖U y‖ = 1) {t : E2} (hself : t = kappa • featMean U (featGibbs U t)) :
    freeEnergy (featureData hc hn) (featGibbsProb hc t) =
      ((kappa / 2 : ℝ) : EReal) + ((featurePotential kappa0 U t : ℝ) : EReal) := by
  have := isProbabilityMeasure_featGibbs hc t
  rw [freeEnergy_feature_eq_gibbs hc hn]
  show _ + (((relativeEntropy (featGibbs U t)
    (featGibbs U (kappa • featMean U (featGibbs U t))) : ℝ≥0∞) : EReal) +
    ((featurePotential kappa0 U (kappa • featMean U (featGibbs U t)) : ℝ) : EReal)) = _
  rw [← hself, Analysis.relativeEntropy_eq_klDiv, klDiv_self]
  simp

lemma lipschitzData_feature {U : Torus 1 → E2} (hc : Continuous U) (hn : ∀ y, ‖U y‖ = 1)
    {C : ℝ} (hC : ∀ x y, ‖U x - U y‖ ≤ C * torusDist x y) :
    LipschitzData (featureData hc hn) := by
  refine ⟨⟨0, fun x y => by simp [featureData]⟩, ?_⟩
  rw [LipschitzData.W_lipschitz_sum_iff]
  refine ⟨kappa * |C|, fun x y x' y' => ?_⟩
  have hk : (0 : ℝ) < kappa := kappa_pos
  have hd : ∀ x y : Torus 1, 0 ≤ torusDist x y := fun x y => Real.sqrt_nonneg _
  have hCx : ‖U x - U x'‖ ≤ |C| * torusDist x x' :=
    (hC x x').trans (mul_le_mul_of_nonneg_right (le_abs_self C) (hd _ _))
  have hCy : ‖U y - U y'‖ ≤ |C| * torusDist y y' :=
    (hC y y').trans (mul_le_mul_of_nonneg_right (le_abs_self C) (hd _ _))
  have e : (featureData hc hn).W x y - (featureData hc hn).W x' y' =
      kappa * (inner ℝ (U x') (U y') - inner ℝ (U x) (U y)) := by
    show featureW U x y - featureW U x' y' = _
    unfold featureW; ring
  have e2 : inner ℝ (U x') (U y') - inner ℝ (U x) (U y) =
      -(inner ℝ (U x - U x') (U y') + inner ℝ (U x) (U y - U y')) := by
    simp only [inner_sub_left, inner_sub_right]; ring
  have b1 : |inner ℝ (U x - U x') (U y')| ≤ ‖U x - U x'‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hn, mul_one]
  have b2 : |inner ℝ (U x) (U y - U y')| ≤ ‖U y - U y'‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hn, one_mul]
  rw [e, e2, abs_mul, abs_of_pos hk, abs_neg]
  have := abs_add_le (inner ℝ (U x - U x') (U y')) (inner ℝ (U x) (U y - U y'))
  calc kappa * |inner ℝ (U x - U x') (U y') + inner ℝ (U x) (U y - U y')|
      ≤ kappa * (|C| * torusDist x x' + |C| * torusDist y y') := by
        gcongr
        linarith
    _ = kappa * |C| * (torusDist x x' + torusDist y y') := by ring

lemma frozenPotential_feature {U : Torus 1 → E2} (hc : Continuous U) (hn : ∀ y, ‖U y‖ = 1)
    (ν : Measure (Torus 1)) [IsProbabilityMeasure ν] (x : Torus 1) :
    frozenPotential (featureData hc hn) ν x =
      kappa - inner ℝ (kappa • featMean U ν) (U x) := by
  show (0 : ℝ) + ∫ y, featureW U x y ∂ν = _
  unfold featureW
  have hi : ∫ y, inner ℝ (U x) (U y) ∂ν = inner ℝ (featMean U ν) (U x) := by
    rw [← integral_inner_featU hc ν (U x)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => real_inner_comm _ _)
  have hint : Integrable (fun y => inner ℝ (U x) (U y)) ν :=
    (integrable_inner_featU hc ν (U x)).congr
      (Filter.Eventually.of_forall fun y => real_inner_comm _ _)
  rw [integral_const_mul, integral_sub (integrable_const _) hint, hi, real_inner_smul_left]
  simp
  ring

lemma featGibbs_eq_frozen {U : Torus 1 → E2} (hc : Continuous U) (hn : ∀ y, ‖U y‖ = 1)
    {t : E2} (hself : t = kappa • featMean U (featGibbs U t)) :
    (featGibbsProb hc t : Measure (Torus 1)) =
      (frozenGibbs (featureData hc hn) (featGibbsProb hc t)).measure := by
  have := isProbabilityMeasure_featGibbs hc t
  show featGibbs U t = (DGPS.haar 1).withDensity _
  have hfp : ∀ x, frozenPotential (featureData hc hn) (featGibbsProb hc t : Measure (Torus 1)) x =
      kappa - inner ℝ t (U x) := by
    intro x
    rw [frozenPotential_feature hc hn]
    show kappa - inner ℝ (kappa • featMean U (featGibbs U t)) (U x) = _
    rw [← hself]
  have hden : ∀ x, frozenDensity (featureData hc hn) (featGibbsProb hc t : Measure (Torus 1)) x =
      Real.exp (inner ℝ t (U x)) / ∫ y, Real.exp (inner ℝ t (U y)) ∂(DGPS.haar 1) := by
    intro x
    have hpart : frozenPartition (featureData hc hn) (featGibbsProb hc t : Measure (Torus 1)) =
        Real.exp (-kappa) * ∫ y, Real.exp (inner ℝ t (U y)) ∂(DGPS.haar 1) := by
      unfold frozenPartition
      rw [← integral_const_mul]
      congr 1
      funext y
      rw [hfp y, ← Real.exp_add]
      congr 1; ring
    unfold frozenDensity
    rw [hpart, hfp x]
    have hpos : 0 < ∫ y, Real.exp (inner ℝ t (U y)) ∂(DGPS.haar 1) := by
      refine integral_exp_pos ?_
      exact integrable_exp_featTilt hc t
    rw [show -(kappa - inner ℝ t (U x)) = -kappa + inner ℝ t (U x) by ring, Real.exp_add]
    field_simp
  unfold featGibbs Measure.tilted
  show _ = (DGPS.haar 1).withDensity fun x => ENNReal.ofReal (frozenDensity _ _ x)
  simp_rw [hden]

lemma lipschitz_of_isSmoothPeriodic {φ : Torus 1 → ℝ} (hφ : IsSmoothPeriodic φ) :
    ∃ C : ℝ, ∀ x y, |φ x - φ y| ≤ C * torusDist x y := by
  have hc : Continuous (coordPartial 0 φ) := hφ.continuous_coordPartial 0
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨B, fun x y => ?_⟩
  obtain ⟨a, b, rfl, rfl, hab, -⟩ := exists_lifts_one x y
  rw [← hab]
  have hc' : Continuous (fun t : ℝ => coordPartial 0 φ (torusLift (fun _ : Fin 1 => t))) :=
    hc.comp (SharpLSI.continuous_liftT.comp (continuous_pi fun _ => continuous_id))
  have hftc : ∫ t in a..b, coordPartial 0 φ (torusLift (fun _ : Fin 1 => t)) =
      φ (torusLift (fun _ => b)) - φ (torusLift (fun _ => a)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_smooth_one hφ t)
      (hc'.intervalIntegrable _ _)
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := B)
    (f := fun t : ℝ => coordPartial 0 φ (torusLift (fun _ : Fin 1 => t)))
    (fun t _ => by simpa using hB _ (Set.mem_univ _))
  rw [hftc, Real.norm_eq_abs, abs_sub_comm] at h1
  rwa [abs_sub_comm a b]

lemma lipschitz_of_smoothCoords {U : Torus 1 → E2} (hs : ∀ j : Fin 2, IsSmoothPeriodic fun y => U y j) :
    ∃ C : ℝ, ∀ x y, ‖U x - U y‖ ≤ C * torusDist x y := by
  obtain ⟨C0, h0⟩ := lipschitz_of_isSmoothPeriodic (hs 0)
  obtain ⟨C1, h1⟩ := lipschitz_of_isSmoothPeriodic (hs 1)
  refine ⟨C0 + C1, fun x y => ?_⟩
  have hn : ∀ v : E2, ‖v‖ ≤ |v 0| + |v 1| := fun v => by
    have h := EuclideanSpace.real_norm_sq_eq v
    rw [Fin.sum_univ_two] at h
    apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
    nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), sq_abs (v 0), sq_abs (v 1)]
  calc ‖U x - U y‖ ≤ |(U x - U y) 0| + |(U x - U y) 1| := hn _
    _ = |U x 0 - U y 0| + |U x 1 - U y 1| := by simp
    _ ≤ C0 * torusDist x y + C1 * torusDist x y := add_le_add (h0 x y) (h1 x y)
    _ = (C0 + C1) * torusDist x y := by ring

lemma continuous_of_smoothCoords {U : Torus 1 → E2} (hs : ∀ j : Fin 2, IsSmoothPeriodic fun y => U y j) :
    Continuous U := by
  have : Continuous fun y => (WithLp.toLp 2 (fun j => U y j) : E2) :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => (hs j).continuous_torus)
  simpa using this

lemma featGibbs_eq_withDensity {U : Torus 1 → E2} (hc : Continuous U) (t : E2) :
    featGibbs U t = (DGPS.haar 1).withDensity fun x => ENNReal.ofReal (featGibbsDensity U t x) := by
  unfold featGibbs Measure.tilted featGibbsDensity
  congr 1
  funext x
  congr 1
  have hpos : 0 < ∫ y, Real.exp (inner ℝ t (U y)) ∂(DGPS.haar 1) :=
    integral_exp_pos (integrable_exp_featTilt hc t)
  rw [Real.exp_sub]
  show _ / _ = _ / Real.exp (Real.log (∫ y, Real.exp (inner ℝ t (U y)) ∂(DGPS.haar 1)))
  rw [Real.exp_log hpos]

lemma gap_feature {U : Torus 1 → E2} (hc : Continuous U) (hn : ∀ y, ‖U y‖ = 1)
    (hnn : ∀ t, 0 ≤ featurePotential kappa0 U t) {t : E2}
    (hself : t = kappa • featMean U (featGibbs U t)) (ρ : AbsoluteDensity 1)
    (hρ : densityMeasure ρ = featGibbsProb hc t) :
    ((scalarGap (featureData hc hn) ρ : ℝ≥0) : ℝ) = featurePotential kappa0 U t := by
  rw [coe_scalarGap]
  have h1 := coe_densityFreeEnergy (featureData hc hn) ρ
  rw [hρ, freeEnergy_gibbs_of_selfconsistent' hc hn hself] at h1
  have h2 := coe_freeEnergyMinimumReal (featureData hc hn)
  rw [freeEnergyMinimum_feature hc hn hnn] at h2
  rw [← EReal.coe_add] at h1
  have h1' := EReal.coe_eq_coe_iff.mp h1
  have h2' := EReal.coe_eq_coe_iff.mp h2
  rw [h1', h2']
  ring

/-- **SEM010.**  Let `U` be a smooth (coordinatewise smooth periodic) unit-norm feature carrying the
landscape certificate, and let `t` be a critical point of `Ψ_U` with `Ψ_U t > 0`.  Then the Gibbs
competitor `q = exp(⟨t, U⟩ - Λ_U(t))` is smooth-positive and defines an absolute-admissible density
`ρ = (√q)²` (so `√q ∈ H¹`), whose gap is `G(q) = Ψ_U(t) > 0`, whose score
`2 (√q)' + √q b_ρ` vanishes a.e. (hence zero dissipation), and `r_* = r_ms = r_1 = 0`. -/
theorem smooth_positive_gap_gibbs_competitor_forces_both_rates_zero
    {U : Torus 1 → E2} (hs : ∀ j : Fin 2, IsSmoothPeriodic fun y => U y j)
    (hn : ∀ y, ‖U y‖ = 1) (hU : RoughLandscapeCertificate U) {t : E2}
    (hcrit : fderiv ℝ (featurePotential kappa0 U) t = 0) (hpos : 0 < featurePotential kappa0 U t)
    (b : AbsoluteDrift (featureData (continuous_of_smoothCoords hs) hn)) :
    (∀ y, 0 < featGibbsDensity U t y) ∧ Continuous (featGibbsDensity U t) ∧
    (∃ ρ : AbsoluteDensity 1,
      densityMeasure ρ = featGibbsProb (continuous_of_smoothCoords hs) t ∧
      (∀ᵐ x ∂DGPS.haar 1, ρ.sqrt x ^ 2 = featGibbsDensity U t x) ∧
      ((scalarGap (featureData (continuous_of_smoothCoords hs) hn) ρ : ℝ≥0) : ℝ) =
        featurePotential kappa0 U t ∧
      0 < scalarGap (featureData (continuous_of_smoothCoords hs) hn) ρ ∧
      (∀ᵐ x ∂DGPS.haar 1,
        scalarScore (featureData (continuous_of_smoothCoords hs) hn) b ρ x = 0) ∧
      scalarDissipation (featureData (continuous_of_smoothCoords hs) hn) b ρ = 0) ∧
    scalarRate (featureData (continuous_of_smoothCoords hs) hn) b = 0 ∧
    speciesRate (featureData (continuous_of_smoothCoords hs) hn) b = 0 ∧
    speciesRateAtMost (featureData (continuous_of_smoothCoords hs) hn) b 1 = 0 := by
  have hc := continuous_of_smoothCoords hs
  obtain ⟨-, -, hnn, -⟩ := hU
  have hself := critical_selfconsistent' hc hn hcrit
  obtain ⟨C, hC⟩ := lipschitz_of_smoothCoords hs
  have hLip := lipschitzData_feature hc hn hC
  have hfix := featGibbs_eq_frozen hc hn hself
  obtain ⟨-, ρ, hρ, hD⟩ :=
    (zeroDissipation_iff_frozenFixedPoint (featureData hc hn) hLip b).2 (featGibbsProb hc t) hfix
  have hgap := gap_feature hc hn hnn hself ρ hρ
  have hgap0 : 0 < scalarGap (featureData hc hn) ρ := by
    rw [← NNReal.coe_pos, hgap]; exact hpos
  have hq0 : ∀ y, 0 < featGibbsDensity U t y := fun y => Real.exp_pos _
  have hscalar : scalarRate (featureData hc hn) b = 0 := by
    refine le_antisymm ?_ bot_le
    refine (scalarRate_le_quotient _ b ρ hgap0).trans ?_
    unfold scalarQuotient
    rw [hD]
    simp
  have hcq : Continuous (featGibbsDensity U t) := by
    unfold featGibbsDensity
    exact Real.continuous_exp.comp ((continuous_const.inner hc).sub continuous_const)
  refine ⟨hq0, hcq,
    ⟨ρ, hρ, ?_, hgap, hgap0, ?_, hD⟩, hscalar, ?_, ?_⟩
  · have h1 : (DGPS.haar 1).withDensity (fun x => ENNReal.ofReal (ρ.sqrt x ^ 2)) =
        (DGPS.haar 1).withDensity (fun x => ENNReal.ofReal (featGibbsDensity U t x)) := by
      rw [← featGibbs_eq_withDensity hc t, ← densityMeasure_coe, hρ]
      rfl
    rw [withDensity_eq_iff_of_sigmaFinite
      ((ρ.memLp_sqrt.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal)
      (hcq.measurable.ennreal_ofReal.aemeasurable)] at h1
    filter_upwards [h1] with x hx
    exact (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (hq0 x).le).1 hx
  · have hg := isWeakGradient_weakGradient ρ.sqrt_mem
    have h1 : AEStronglyMeasurable
        (fun x => scalarScore (featureData hc hn) b ρ x) (DGPS.haar 1) :=
      (hg.memLp_grad.aestronglyMeasurable.const_smul (2 : ℝ)).add
        (ρ.memLp_sqrt.aestronglyMeasurable.smul (b.measurable_force ρ).aestronglyMeasurable)
    have hmeas : AEMeasurable
        (fun x => ENNReal.ofReal (‖scalarScore (featureData hc hn) b ρ x‖ ^ 2)) (DGPS.haar 1) :=
      (h1.norm.aemeasurable.pow_const 2).ennreal_ofReal
    have hD' := hD
    unfold scalarDissipation at hD'
    rw [lintegral_eq_zero_iff' hmeas] at hD'
    filter_upwards [hD'] with x hx
    have h0 : ‖scalarScore (featureData hc hn) b ρ x‖ ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.1 hx
    exact norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h0 (by positivity)))
  · exact le_antisymm (hscalar ▸ speciesRate_le_scalarRate _ b) bot_le
  · rw [speciesRateAtMost_one]; exact hscalar

end DGPS.Examples.RoughBoundary.Semicontinuity
