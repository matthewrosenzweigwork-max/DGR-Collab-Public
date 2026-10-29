import DGPS.Examples.RoughBoundary.LandscapeSelection
import DGPS.Examples.RoughBoundary.Model
import DGPS.Model.FreeEnergy
import DGPS.Measure.EntropyChain

/-!
# RUF027: exact free energy decomposition and unique Haar minimizer

For the selected feature `U = U_{L,ε}`, `M(ν) = ∫ U dν`, `κ = 11/6` and `q_t = exp(⟪t,U⟫ - Λ(t))`:
`F(ν) = F_* + H(ν | q_{κM} m) + Ψ(κM) = F_* + H(ν | m) - κ ‖M‖² / 2` with `F_* = κ/2`, extended
entropy (`EReal`). Haar measure is the unique global minimizer, and every critical point `t_*` of
`Ψ` is self-consistent, `t_* = κ ∫ U q_{t_*} dm`, with gap `F(q_{t_*} m) - F(m) = Ψ(t_*)`.

Design choices (R5 notes).
* The statement is packaged as the predicate `FreeEnergyDecomposition L ε`, proved for every
  feature carrying `RoughLandscapeCertificate`, and the main theorem transports it along the
  parameter selection of RUF026 (`common_finite_parameter_selection`).
* Identities are stated additively over `F_* = κ/2` in `EReal`, which avoids `∞ - ∞`.
* The entropy tilt identity `H(ν | m.tilted f) = H(ν | m) + log ∫ e^f - ∫ f ν` is proved at
  infinite entropy by cases (`klDiv_tilted_right`), using only boundedness of the log tilt.
* The Haar mean `∫ U dm = 0` is derived from the certificate (`Ψ ≥ 0` with Jensen), and
  `∇Λ(t) = ∫ U q_t dm` from `hasFDerivAt_pint`.
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace DGPS.Examples.RoughBoundary.FreeEnergy

open DGPS.Examples.RoughBoundary.Feature DGPS.Examples.RoughBoundary.Landscape
open DGPS.Examples.RoughBoundary.Model (modelData modelW kappa continuous_modelW)
open DGPS.Examples.RoughBoundary.Semicontinuity (featureLogPartition featurePotential)

lemma coe_eq_toReal {x : ℝ≥0∞} (h : x ≠ ⊤) : (x : EReal) = ((x.toReal : ℝ) : EReal) := by
  lift x to NNReal using h
  rw [ENNReal.coe_toReal]
  rfl

/-- Entropy tilt identity on a probability space, for a bounded (integrable) log tilt `f`. -/
lemma klDiv_tilted_right {α : Type*} [MeasurableSpace α] {m ν : Measure α}
    [IsProbabilityMeasure m] [IsProbabilityMeasure ν] {f : α → ℝ}
    (hfm : Integrable (fun x => Real.exp (f x)) m) (hfν : Integrable f ν) :
    ((klDiv ν (m.tilted f) : ℝ≥0∞) : EReal) =
      ((klDiv ν m : ℝ≥0∞) : EReal) + ((Real.log (∫ x, Real.exp (f x) ∂m) - ∫ x, f x ∂ν : ℝ) : EReal) := by
  have : IsProbabilityMeasure (m.tilted f) := isProbabilityMeasure_tilted hfm
  by_cases hac : ν ≪ m
  · have hac' : ν ≪ m.tilted f := hac.trans (absolutelyContinuous_tilted hfm)
    by_cases hint : Integrable (llr ν m) ν
    · have hint' : Integrable (llr ν (m.tilted f)) ν :=
        integrable_llr_tilted_right hac hfν hint hfm
      have h1 := toReal_klDiv_of_measure_eq hac' (by simp)
      have h2 := toReal_klDiv_of_measure_eq hac (by simp)
      have h3 := integral_llr_tilted_right hac hfν hfm hint
      have n1 : klDiv ν (m.tilted f) ≠ ⊤ := klDiv_ne_top hac' hint'
      have n2 : klDiv ν m ≠ ⊤ := klDiv_ne_top hac hint
      rw [coe_eq_toReal n1, coe_eq_toReal n2, ← EReal.coe_add, h1, h2, h3]
      congr 1; ring
    · have hint' : ¬ Integrable (llr ν (m.tilted f)) ν := fun h => by
        apply hint
        have := llr_tilted_right hac hfm
        rw [integrable_congr this] at h
        have h' : Integrable (fun x => -f x + Real.log (∫ z, Real.exp (f z) ∂m)) ν :=
          hfν.neg.add (integrable_const _)
        exact (h.sub h').congr (Filter.Eventually.of_forall fun x => by simp)
      rw [klDiv_of_not_integrable hint, klDiv_of_not_integrable hint', EReal.coe_ennreal_top,
        EReal.top_add_coe]
  · have hac' : ¬ ν ≪ m.tilted f := fun h => hac (h.trans (tilted_absolutelyContinuous m f))
    rw [klDiv_of_not_ac hac, klDiv_of_not_ac hac', EReal.coe_ennreal_top, EReal.top_add_coe]

/-- The mean feature `M(ν) = ∫ U dν`. -/
noncomputable def meanFeature (L ε : ℝ) (ν : Measure (Torus 1)) : E2 := ∫ y, Ufeat L ε y ∂ν

lemma integrable_U {L : ℝ} (hL : 0 < L) (ε : ℝ) (ν : Measure (Torus 1)) [IsFiniteMeasure ν] :
    Integrable (Ufeat L ε) ν :=
  (continuous_Ufeat hL ε).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma integrable_inner_U {L : ℝ} (hL : 0 < L) (ε : ℝ) (ν : Measure (Torus 1)) [IsFiniteMeasure ν]
    (c : E2) : Integrable (fun y => inner ℝ (Ufeat L ε y) c) ν :=
  (continuous_Ufeat hL ε).inner continuous_const |>.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma integral_inner_U {L : ℝ} (hL : 0 < L) (ε : ℝ) (ν : Measure (Torus 1)) [IsFiniteMeasure ν]
    (c : E2) : ∫ y, inner ℝ (Ufeat L ε y) c ∂ν = inner ℝ (meanFeature L ε ν) c := by
  simp_rw [real_inner_comm c]
  exact integral_inner (integrable_U hL ε ν) c

lemma interactionEnergy_model {L : ℝ} (hL : 0 < L) (ε : ℝ) (ν : ProbabilityMeasure (Torus 1)) :
    interactionEnergy (modelData hL ε) ν =
      kappa * (1 - ‖meanFeature L ε (ν : Measure (Torus 1))‖ ^ 2) := by
  rw [interactionEnergy_eq_iterated]
  have h1 : ∀ y, ∫ x, (modelData hL ε).W x y ∂(ν : Measure (Torus 1)) =
      kappa * (1 - inner ℝ (meanFeature L ε (ν : Measure (Torus 1))) (Ufeat L ε y)) := by
    intro y
    show ∫ x, modelW L ε x y ∂(ν : Measure (Torus 1)) = _
    unfold modelW
    rw [integral_const_mul, integral_sub (integrable_const _) (integrable_inner_U hL ε _ _),
      integral_inner_U hL ε]
    simp
  simp_rw [h1]
  rw [integral_const_mul, integral_sub (integrable_const _)]
  · have := integral_inner_U hL ε (ν : Measure (Torus 1)) (meanFeature L ε (ν : Measure (Torus 1)))
    simp_rw [real_inner_comm (meanFeature L ε (ν : Measure (Torus 1)))] at this
    rw [this]
    simp
  · exact ((integrable_inner_U hL ε (ν : Measure (Torus 1))
      (meanFeature L ε (ν : Measure (Torus 1)))).congr
      (Filter.Eventually.of_forall fun y => real_inner_comm _ _))

/-- The Gibbs tilt `q_t m` of Haar measure, `q_t = exp (⟪t, U⟫ - Λ(t))`. -/
noncomputable def gibbsMeasure (L ε : ℝ) (t : E2) : Measure (Torus 1) :=
  (DGPS.haar 1).tilted fun y => inner ℝ t (Ufeat L ε y)

/-- The Gibbs density `q_t(y) = exp (⟪t, U y⟫ - Λ(t))` with respect to Haar measure. -/
noncomputable def gibbsDensity (L ε : ℝ) (t : E2) (y : Torus 1) : ℝ :=
  Real.exp (inner ℝ t (Ufeat L ε y) - featureLogPartition (Ufeat L ε) t)

lemma integrable_exp_tilt {L : ℝ} (hL : 0 < L) (ε : ℝ) (t : E2) :
    Integrable (fun y => Real.exp (inner ℝ t (Ufeat L ε y))) (DGPS.haar 1) :=
  (Real.continuous_exp.comp (continuous_const.inner (continuous_Ufeat hL ε))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma isProbabilityMeasure_gibbs {L : ℝ} (hL : 0 < L) (ε : ℝ) (t : E2) :
    IsProbabilityMeasure (gibbsMeasure L ε t) :=
  isProbabilityMeasure_tilted (integrable_exp_tilt hL ε t)

/-- The Gibbs tilt as a probability measure. -/
noncomputable def gibbsProbability {L : ℝ} (hL : 0 < L) (ε : ℝ) (t : E2) :
    ProbabilityMeasure (Torus 1) :=
  ⟨gibbsMeasure L ε t, isProbabilityMeasure_gibbs hL ε t⟩

lemma kappa_eq : kappa = kappa0 := rfl

lemma kappa_pos : 0 < kappa := by unfold kappa; norm_num

lemma freeEnergy_model {L : ℝ} (hL : 0 < L) (ε : ℝ) (ν : ProbabilityMeasure (Torus 1)) :
    freeEnergy (modelData hL ε) ν =
      ((relativeEntropy (ν : Measure (Torus 1)) (DGPS.haar 1) : ℝ≥0∞) : EReal) +
        ((kappa / 2 * (1 - ‖meanFeature L ε (ν : Measure (Torus 1))‖ ^ 2) : ℝ) : EReal) := by
  unfold freeEnergy
  rw [interactionEnergy_model hL ε ν, add_assoc, ← EReal.coe_add]
  congr 2
  simp [potentialEnergy, modelData]
  ring

lemma freeEnergy_eq_gibbs {L : ℝ} (hL : 0 < L) (ε : ℝ) (ν : ProbabilityMeasure (Torus 1)) :
    freeEnergy (modelData hL ε) ν =
      ((relativeEntropy (ν : Measure (Torus 1))
        (gibbsMeasure L ε (kappa • meanFeature L ε (ν : Measure (Torus 1)))) : ℝ≥0∞) : EReal) +
      ((featurePotential kappa0 (Ufeat L ε)
        (kappa • meanFeature L ε (ν : Measure (Torus 1))) : ℝ) : EReal) +
      ((kappa / 2 : ℝ) : EReal) := by
  set M := meanFeature L ε (ν : Measure (Torus 1)) with hM
  have := isProbabilityMeasure_gibbs hL ε (kappa • M)
  rw [freeEnergy_model, Analysis.relativeEntropy_eq_klDiv, Analysis.relativeEntropy_eq_klDiv]
  have hf : Integrable (fun y => inner ℝ (kappa • M) (Ufeat L ε y)) (ν : Measure (Torus 1)) :=
    (integrable_inner_U hL ε _ (kappa • M)).congr
      (Filter.Eventually.of_forall fun y => real_inner_comm _ _)
  have h := klDiv_tilted_right (m := DGPS.haar 1) (ν := (ν : Measure (Torus 1)))
    (integrable_exp_tilt hL ε (kappa • M)) hf
  have hint : ∫ y, inner ℝ (kappa • M) (Ufeat L ε y) ∂(ν : Measure (Torus 1)) =
      kappa * ‖M‖ ^ 2 := by
    have := integral_inner_U hL ε (ν : Measure (Torus 1)) (kappa • M)
    simp_rw [real_inner_comm (kappa • M)] at this
    rw [this]
    rw [← hM, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hΛ : Real.log (∫ y, Real.exp (inner ℝ (kappa • M) (Ufeat L ε y)) ∂(DGPS.haar 1)) =
      featureLogPartition (Ufeat L ε) (kappa • M) := rfl
  unfold gibbsMeasure
  rw [h, hΛ, hint, add_assoc _ ((_ : ℝ) : EReal), ← EReal.coe_add, add_assoc, ← EReal.coe_add]
  congr 2
  unfold featurePotential
  rw [norm_smul, kappa_eq]
  have hk : (0 : ℝ) < kappa0 := kappa_eq ▸ kappa_pos
  simp only [Real.norm_eq_abs, abs_of_pos hk, mul_pow]
  field_simp
  ring

lemma freeEnergy_eq_gibbs' {L : ℝ} (hL : 0 < L) (ε : ℝ) (ν : ProbabilityMeasure (Torus 1)) :
    freeEnergy (modelData hL ε) ν =
      ((kappa / 2 : ℝ) : EReal) +
        (((relativeEntropy (ν : Measure (Torus 1))
          (gibbsMeasure L ε (kappa • meanFeature L ε (ν : Measure (Torus 1)))) : ℝ≥0∞) : EReal) +
        ((featurePotential kappa0 (Ufeat L ε)
          (kappa • meanFeature L ε (ν : Measure (Torus 1))) : ℝ) : EReal)) := by
  rw [freeEnergy_eq_gibbs hL ε ν, add_comm]

lemma freeEnergy_eq_entropy_sub {L : ℝ} (hL : 0 < L) (ε : ℝ) (ν : ProbabilityMeasure (Torus 1)) :
    freeEnergy (modelData hL ε) ν =
      ((kappa / 2 : ℝ) : EReal) +
        (((relativeEntropy (ν : Measure (Torus 1)) (DGPS.haar 1) : ℝ≥0∞) : EReal) +
        ((-(kappa / 2) * ‖meanFeature L ε (ν : Measure (Torus 1))‖ ^ 2 : ℝ) : EReal)) := by
  rw [freeEnergy_model, add_left_comm, ← EReal.coe_add]
  congr 2
  ring

lemma gibbsMeasure_zero (L ε : ℝ) : gibbsMeasure L ε 0 = DGPS.haar 1 := by
  unfold gibbsMeasure
  simp only [inner_zero_left]
  exact tilted_zero _

/-- Gibbs variational inequality at Haar measure: `⟪t, ∫ U dm⟫ ≤ Λ(t)`. -/
lemma inner_meanFeature_haar_le {L : ℝ} (hL : 0 < L) (ε : ℝ) (t : E2) :
    inner ℝ (meanFeature L ε (DGPS.haar 1)) t ≤ featureLogPartition (Ufeat L ε) t := by
  have hf : Integrable (fun y => inner ℝ t (Ufeat L ε y)) (DGPS.haar 1) :=
    (integrable_inner_U hL ε _ t).congr (Filter.Eventually.of_forall fun y => real_inner_comm _ _)
  have h := klDiv_tilted_right (m := DGPS.haar 1) (ν := DGPS.haar 1)
    (integrable_exp_tilt hL ε t) hf
  have hint : ∫ y, inner ℝ t (Ufeat L ε y) ∂(DGPS.haar 1) =
      inner ℝ (meanFeature L ε (DGPS.haar 1)) t := by
    have := integral_inner_U hL ε (DGPS.haar 1) t
    simp_rw [real_inner_comm t] at this
    rw [this, real_inner_comm]
  rw [klDiv_self, EReal.coe_ennreal_zero, zero_add] at h
  have h0 : (0 : EReal) ≤ _ := h ▸ EReal.coe_ennreal_nonneg _
  have h1 := EReal.coe_nonneg.mp h0
  rw [hint] at h1
  exact sub_nonneg.mp h1

lemma meanFeature_haar_eq_zero {L : ℝ} (hL : 0 < L) (ε : ℝ)
    (hnn : ∀ t, 0 ≤ featurePotential kappa0 (Ufeat L ε) t) :
    meanFeature L ε (DGPS.haar 1) = 0 := by
  set M0 := meanFeature L ε (DGPS.haar 1) with hM0
  have h1 := inner_meanFeature_haar_le hL ε (kappa • M0)
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

lemma freeEnergy_haar {L : ℝ} (hL : 0 < L) (ε : ℝ)
    (hnn : ∀ t, 0 ≤ featurePotential kappa0 (Ufeat L ε) t) :
    freeEnergy (modelData hL ε) (haarProbability 1) = ((kappa / 2 : ℝ) : EReal) := by
  rw [freeEnergy_model]
  have hm : ((haarProbability 1 : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)) = DGPS.haar 1 :=
    rfl
  rw [hm, meanFeature_haar_eq_zero hL ε hnn,
    relativeEntropy_zero_iff.mpr rfl]
  simp

lemma freeEnergy_ge {L : ℝ} (hL : 0 < L) (ε : ℝ)
    (hnn : ∀ t, 0 ≤ featurePotential kappa0 (Ufeat L ε) t) (ν : ProbabilityMeasure (Torus 1)) :
    ((kappa / 2 : ℝ) : EReal) ≤ freeEnergy (modelData hL ε) ν := by
  rw [freeEnergy_eq_gibbs' hL ε ν]
  exact le_add_of_nonneg_right (add_nonneg (EReal.coe_ennreal_nonneg _)
    (EReal.coe_nonneg.mpr (hnn _)))

lemma eq_haar_of_freeEnergy_eq {L : ℝ} (hL : 0 < L) (ε : ℝ)
    (hnn : ∀ t, 0 ≤ featurePotential kappa0 (Ufeat L ε) t)
    (hzero : ∀ t, featurePotential kappa0 (Ufeat L ε) t = 0 ↔ t = 0)
    (ν : ProbabilityMeasure (Torus 1))
    (h : freeEnergy (modelData hL ε) ν = ((kappa / 2 : ℝ) : EReal)) :
    ν = haarProbability 1 := by
  rw [freeEnergy_eq_gibbs' hL ε ν] at h
  set M := meanFeature L ε (ν : Measure (Torus 1)) with hM
  set H := relativeEntropy (ν : Measure (Torus 1)) (gibbsMeasure L ε (kappa • M)) with hH
  have := isProbabilityMeasure_gibbs hL ε (kappa • M)
  have hHtop : H ≠ ⊤ := by
    intro htop
    rw [htop, EReal.coe_ennreal_top, EReal.top_add_coe, EReal.coe_add_top] at h
    exact EReal.coe_ne_top _ h.symm
  rw [coe_eq_toReal hHtop, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_eq_coe_iff] at h
  have hH0 : 0 ≤ H.toReal := ENNReal.toReal_nonneg
  have hΨ := hnn (kappa • M)
  have hH1 : H.toReal = 0 := by linarith
  have hΨ1 : featurePotential kappa0 (Ufeat L ε) (kappa • M) = 0 := by linarith
  have hHz : H = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).mp hH1 with h' | h'
    · exact h'
    · exact absurd h' hHtop
  have hν : (ν : Measure (Torus 1)) = gibbsMeasure L ε (kappa • M) :=
    relativeEntropy_zero_iff.mp hHz
  have hκM : kappa • M = 0 := (hzero _).mp hΨ1
  rw [hκM, gibbsMeasure_zero] at hν
  exact Subtype.ext hν

lemma pd_expPhi (u t v : E2) : pd expPhi (u, t) v = Real.exp (inner ℝ t u) * inner ℝ v u := by
  have h1 := hasFDerivAt_pd (contDiff_expPhi.differentiable (by simp)) u t
  have h2 : HasFDerivAt (fun s : E2 => expPhi (u, s))
      (Real.exp (inner ℝ t u) • innerSL ℝ u) t := by
    have h3 : HasFDerivAt (fun s : E2 => inner ℝ s u) (innerSL ℝ u) t := by
      refine ((innerSL ℝ u).hasFDerivAt (x := t)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => ?_)
      simp [real_inner_comm]
    exact h3.exp
  have := h1.unique h2
  rw [this]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [real_inner_comm v u]

lemma hasFDerivAt_featureLogPartition {L : ℝ} (hL : 0 < L) (ε : ℝ) (t : E2) :
    ∃ D : E2 →L[ℝ] ℝ, HasFDerivAt (featureLogPartition (Ufeat L ε)) D t ∧
      ∀ v, D v = ∫ y, inner ℝ v (Ufeat L ε y) ∂(gibbsMeasure L ε t) := by
  have hV := measurable_Ufeat hL ε
  have hb := ae_norm_Ufeat L ε
  have hP := hasFDerivAt_pint (μ := DGPS.haar 1) contDiff_expPhi hV hb t
  have hpos : 0 < pint (DGPS.haar 1) (Ufeat L ε) expPhi t :=
    lt_of_lt_of_le (Real.exp_pos _) (exp_neg_norm_le_pint hV hb t)
  have hlog := hP.log hpos.ne'
  refine ⟨_, hlog, fun v => ?_⟩
  have hcont : Continuous (pd expPhi) := (contDiff_pd contDiff_expPhi).continuous
  have hint := integrable_pint hcont hV hb t
  have e1 : pint (DGPS.haar 1) (Ufeat L ε) (pd expPhi) t v =
      ∫ y, Real.exp (inner ℝ t (Ufeat L ε y)) * inner ℝ v (Ufeat L ε y) ∂(DGPS.haar 1) := by
    unfold pint
    rw [ContinuousLinearMap.integral_apply hint v]
    simp_rw [pd_expPhi]
  have e2 : pint (DGPS.haar 1) (Ufeat L ε) expPhi t =
      ∫ y, Real.exp (inner ℝ t (Ufeat L ε y)) ∂(DGPS.haar 1) := rfl
  simp only [smul_apply, smul_eq_mul]
  rw [e1, e2, gibbsMeasure, integral_tilted]
  simp_rw [smul_eq_mul, div_eq_inv_mul, mul_assoc]
  rw [integral_const_mul]

/-- At a critical point `t` of the feature potential, the Gibbs density `q_t` is self-consistent:
`t = κ ∫ U q_t dm`. -/
lemma critical_selfconsistent {L : ℝ} (hL : 0 < L) (ε : ℝ) (t : E2)
    (hcrit : fderiv ℝ (featurePotential kappa0 (Ufeat L ε)) t = 0) :
    t = kappa • meanFeature L ε (gibbsMeasure L ε t) := by
  have := isProbabilityMeasure_gibbs hL ε t
  obtain ⟨D, hD, hDv⟩ := hasFDerivAt_featureLogPartition hL ε t
  have hq := (hasFDerivAt_id t).norm_sq.mul_const (2 * kappa0)⁻¹
  have hΨ := hq.sub hD
  have e : featurePotential kappa0 (Ufeat L ε) =
      (fun y : E2 => ‖id y‖ ^ 2 * (2 * kappa0)⁻¹) - featureLogPartition (Ufeat L ε) := by
    funext x; simp [featurePotential, div_eq_mul_inv]
  rw [e, hΨ.fderiv] at hcrit
  have hk : (0 : ℝ) < kappa := kappa_pos
  refine ext_inner_right ℝ fun v => ?_
  have h1 := congrArg (fun A : E2 →L[ℝ] ℝ => A v) hcrit
  simp only [smul_apply, sub_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    id_eq, zero_apply, smul_eq_mul, nsmul_eq_mul, ContinuousLinearMap.id_apply,
    Nat.cast_ofNat] at h1
  rw [hDv v] at h1
  have h2 := integral_inner_U hL ε (gibbsMeasure L ε t) v
  simp_rw [real_inner_comm v] at h2
  rw [h2] at h1
  rw [real_inner_smul_left, real_inner_comm v (meanFeature L ε (gibbsMeasure L ε t))]
  rw [← kappa_eq] at h1
  field_simp at h1
  nlinarith [h1]

lemma freeEnergy_gibbs_of_selfconsistent {L : ℝ} (hL : 0 < L) (ε : ℝ) (t : E2)
    (hself : t = kappa • meanFeature L ε (gibbsMeasure L ε t)) :
    freeEnergy (modelData hL ε) (gibbsProbability hL ε t) =
      ((kappa / 2 : ℝ) : EReal) + ((featurePotential kappa0 (Ufeat L ε) t : ℝ) : EReal) := by
  have := isProbabilityMeasure_gibbs hL ε t
  rw [freeEnergy_eq_gibbs' hL ε]
  show _ + (((relativeEntropy (gibbsMeasure L ε t)
    (gibbsMeasure L ε (kappa • meanFeature L ε (gibbsMeasure L ε t))) : ℝ≥0∞) : EReal) +
      ((featurePotential kappa0 (Ufeat L ε) (kappa • meanFeature L ε (gibbsMeasure L ε t)) : ℝ) :
        EReal)) = _
  rw [← hself, relativeEntropy_zero_iff.mpr rfl]
  simp

/-- RUF027 (packet statement for one feature `U_{L,ε}`): the exact free energy decomposition, the
unique Haar minimizer with `F_* = κ/2`, and self-consistency of the Gibbs densities at critical
points, written additively over `F_* = κ/2`. -/
def FreeEnergyDecomposition (L ε : ℝ) : Prop :=
  ∀ hL : 0 < L,
    (∀ ν : ProbabilityMeasure (Torus 1),
      freeEnergy (modelData hL ε) ν =
        ((kappa / 2 : ℝ) : EReal) +
          (((relativeEntropy (ν : Measure (Torus 1))
            (gibbsMeasure L ε (kappa • meanFeature L ε (ν : Measure (Torus 1)))) : ℝ≥0∞) : EReal) +
          ((featurePotential kappa0 (Ufeat L ε)
            (kappa • meanFeature L ε (ν : Measure (Torus 1))) : ℝ) : EReal)) ∧
      freeEnergy (modelData hL ε) ν =
        ((kappa / 2 : ℝ) : EReal) +
          (((relativeEntropy (ν : Measure (Torus 1)) (DGPS.haar 1) : ℝ≥0∞) : EReal) +
          ((-(kappa / 2) * ‖meanFeature L ε (ν : Measure (Torus 1))‖ ^ 2 : ℝ) : EReal))) ∧
    freeEnergy (modelData hL ε) (haarProbability 1) = ((kappa / 2 : ℝ) : EReal) ∧
    (∀ ν : ProbabilityMeasure (Torus 1),
      ((kappa / 2 : ℝ) : EReal) ≤ freeEnergy (modelData hL ε) ν ∧
        (freeEnergy (modelData hL ε) ν = ((kappa / 2 : ℝ) : EReal) ↔ ν = haarProbability 1)) ∧
    freeEnergyMinimum (modelData hL ε) = ((kappa / 2 : ℝ) : EReal) ∧
    (∀ μ : ProbabilityMeasure (Torus 1),
      freeEnergy (modelData hL ε) μ = freeEnergyMinimum (modelData hL ε) → μ = haarProbability 1) ∧
    (∀ t : E2, fderiv ℝ (featurePotential kappa0 (Ufeat L ε)) t = 0 →
      t = kappa • meanFeature L ε (gibbsMeasure L ε t) ∧
        freeEnergy (modelData hL ε) (gibbsProbability hL ε t) =
          ((kappa / 2 : ℝ) : EReal) + ((featurePotential kappa0 (Ufeat L ε) t : ℝ) : EReal))

lemma freeEnergyDecomposition_of_certificate {L : ℝ} (ε : ℝ)
    (hcert : RoughLandscapeCertificate (Ufeat L ε)) : FreeEnergyDecomposition L ε := by
  intro hL
  obtain ⟨-, -, hnn, hzero, -⟩ := hcert
  have hF := freeEnergy_haar hL ε hnn
  have hge := freeEnergy_ge hL ε hnn
  have hmin : freeEnergyMinimum (modelData hL ε) = ((kappa / 2 : ℝ) : EReal) :=
    le_antisymm (hF ▸ iInf_le _ _) (le_iInf hge)
  refine ⟨fun ν => ⟨freeEnergy_eq_gibbs' hL ε ν, freeEnergy_eq_entropy_sub hL ε ν⟩, hF,
    fun ν => ⟨hge ν, ⟨eq_haar_of_freeEnergy_eq hL ε hnn hzero ν, fun h => h ▸ hF⟩⟩, hmin,
    fun μ hμ => eq_haar_of_freeEnergy_eq hL ε hnn hzero μ (hμ.trans hmin), fun t ht => ?_⟩
  have hs := critical_selfconsistent hL ε t ht
  exact ⟨hs, freeEnergy_gibbs_of_selfconsistent hL ε t hs⟩

/-- **RUF027.** For the selected rough-boundary features `U_{L,ε}`: for every probability density
`ρ`, `F(ρ m) - F(m) = H(ρ m | q_{κM} m) + Ψ(κM) = H(ρ m | m) - κ ‖M‖² / 2` (extended entropy),
Haar measure is the unique global minimizer with `F_* = κ/2`, and every critical `t_*` of `Ψ` gives
a self-consistent Gibbs density `q_{t_*}` with free-energy gap `Ψ(t_*)`. -/
theorem exact_free_energy_decomposition_and_unique_haar_minimizer :
    ∃ ε₀ L₀ : ℝ, 0 < ε₀ ∧ 1 ≤ L₀ ∧ 1 / ε₀ ≤ L₀ ∧
      (∀ L : ℝ, L₀ ≤ L → ∀ ε : ℝ, |ε| ≤ ε₀ → FreeEnergyDecomposition L ε) ∧
      ∃ L_fixed : ℝ, L₀ ≤ L_fixed ∧ 1 / L_fixed ≤ ε₀ ∧
        FreeEnergyDecomposition L_fixed (1 / L_fixed) := by
  obtain ⟨ε₀, L₀, h1, h2, h3, h4, L, h5, h6, h7⟩ := common_finite_parameter_selection
  exact ⟨ε₀, L₀, h1, h2, h3, fun L hL ε hε =>
    freeEnergyDecomposition_of_certificate ε (h4 L hL ε hε), L, h5, h6,
    freeEnergyDecomposition_of_certificate _ h7⟩

end DGPS.Examples.RoughBoundary.FreeEnergy
