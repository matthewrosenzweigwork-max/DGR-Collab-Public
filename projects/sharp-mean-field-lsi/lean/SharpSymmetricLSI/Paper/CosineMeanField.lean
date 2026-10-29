import SharpSymmetricLSI.Paper.CosineTest
import SharpSymmetricLSI.Paper.R37Rescaling
import SharpSymmetricLSI.Infra.Pinsker

/-!
# Section 3.4: the mean-field cosine model, (3.4) (Phase 3, lane C)

`W_κ(μ,μ) = κ(Q(μ) - 1)` for probability measures (`interE_cos`), `F_* = -κ/2`, the unique
minimizer `m`, `G_κ(ρ) = H(ρ|m) + (κ/2)Q(ρ)` and the dissipation formula.
-/

open MeasureTheory InformationTheory Set Filter
open scoped ENNReal Real

namespace SharpLSI

/-! ### The first mode -/

/-- `sin(2πx)`. -/
noncomputable def sCos (x : Torus 1) : ℝ := (expT x).im

theorem continuous_sCos : Continuous sCos := Complex.continuous_im.comp continuous_expT

theorem exists_coe (x : Torus 1) : ∃ s : ℝ, x 0 = (s : UnitAddCircle) :=
  let ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (x 0); ⟨a, ha.symm⟩

theorem gCos_sub (x y : Torus 1) : gCos (x - y) = gCos x * gCos y + sCos x * sCos y := by
  obtain ⟨s, hs⟩ := exists_coe x
  obtain ⟨t, ht⟩ := exists_coe y
  have hst : (x - y) 0 = ((s - t : ℝ) : UnitAddCircle) := by
    simp only [Pi.sub_apply, hs, ht, AddCircle.coe_sub]
  rw [gCos_coe _ _ hst, gCos_coe _ _ hs, gCos_coe _ _ ht, sCos, sCos, expT_im_coe _ _ hs,
    expT_im_coe _ _ ht, show 2 * π * (s - t) = 2 * π * s - 2 * π * t by ring, Real.cos_sub]

theorem abs_sCos_le (y : Torus 1) : |sCos y| ≤ 1 := by
  have h1 : ‖expT y‖ = 1 := by simp [expT, fourier_apply]
  calc |sCos y| = |(expT y).im| := rfl
    _ ≤ ‖expT y‖ := Complex.abs_im_le_norm _
    _ = 1 := h1

theorem integrable_bdd {μ : Measure (Torus 1)} [IsFiniteMeasure μ] {F : Torus 1 → ℝ}
    (hF : Continuous F) : Integrable F μ :=
  (BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩).integrable _

/-- `Q(μ) = (∫ cos)² + (∫ sin)²`. -/
noncomputable def firstModeM (μ : Measure (Torus 1)) : ℝ :=
  (∫ x, gCos x ∂μ) ^ 2 + (∫ x, sCos x ∂μ) ^ 2

theorem firstModeM_nonneg (μ : Measure (Torus 1)) : 0 ≤ firstModeM μ := by
  unfold firstModeM; positivity

/-- `W_κ(μ,μ) = κ(Q(μ) - 1)`. -/
theorem interE_cos (κ : ℝ) (μ : Measure (Torus 1)) [IsProbabilityMeasure μ] :
    interE (cosW κ) μ μ = κ * (firstModeM μ - 1) := by
  unfold interE cosW firstModeM
  simp_rw [gCos_sub]
  have ic : Integrable gCos μ := integrable_bdd continuous_gCos
  have is : Integrable sCos μ := integrable_bdd continuous_sCos
  have inner : ∀ y, ∫ x, κ * (gCos x * gCos y + sCos x * sCos y - 1) ∂μ =
      κ * ((∫ x, gCos x ∂μ) * gCos y + (∫ x, sCos x ∂μ) * sCos y - 1) := by
    intro y
    rw [integral_const_mul, integral_sub (f := fun x => gCos x * gCos y + sCos x * sCos y)
      (g := fun _ => (1 : ℝ)) ((ic.mul_const _).add (is.mul_const _)) (integrable_const _),
      integral_add (f := fun x => gCos x * gCos y) (g := fun x => sCos x * sCos y)
        (ic.mul_const _) (is.mul_const _), integral_mul_const, integral_mul_const]
    simp
  simp_rw [inner]
  rw [integral_const_mul, integral_sub (f := fun a => (∫ x, gCos x ∂μ) * gCos a +
      (∫ x, sCos x ∂μ) * sCos a) (g := fun _ => (1 : ℝ)) ((ic.const_mul _).add (is.const_mul _))
    (integrable_const _), integral_add (f := fun a => (∫ x, gCos x ∂μ) * gCos a)
      (g := fun a => (∫ x, sCos x ∂μ) * sCos a) (ic.const_mul _) (is.const_mul _),
    integral_const_mul, integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  ring

/-! ### Densities -/

theorem integrable_of_integral_eq_one {ρ : Torus 1 → ℝ} (hρ1 : ∫ x, ρ x ∂haar 1 = 1) :
    Integrable ρ (haar 1) := by
  by_contra h
  rw [integral_undef h] at hρ1
  exact zero_ne_one hρ1

theorem isProbabilityMeasure_densMeasure {ρ : Torus 1 → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar 1 = 1) : IsProbabilityMeasure (densMeasure ρ) := by
  refine ⟨?_⟩
  rw [densMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_of_integral_eq_one hρ1)
      (Eventually.of_forall hρ0), hρ1, ENNReal.ofReal_one]

theorem integral_densMeasure {ρ : Torus 1 → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar 1 = 1) (F : Torus 1 → ℝ) :
    ∫ x, F x ∂densMeasure ρ = ∫ x, ρ x * F x ∂haar 1 := by
  have hm : AEMeasurable (fun x => ENNReal.ofReal (ρ x)) (haar 1) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (integrable_of_integral_eq_one hρ1).aestronglyMeasurable.aemeasurable
  rw [densMeasure, integral_withDensity_eq_integral_toReal_smul₀ hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hρ0 _), smul_eq_mul]

theorem firstModeM_densMeasure {ρ : Torus 1 → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar 1 = 1) : firstModeM (densMeasure ρ) = firstMode ρ := by
  have hi := integrable_of_integral_eq_one hρ1
  have hie : Integrable (fun x => expT x * (ρ x : ℂ)) (haar 1) := by
    refine Integrable.mono' hi.norm (continuous_expT.aestronglyMeasurable.mul
      hi.ofReal.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    have h1 : ‖expT x‖ = 1 := by simp [expT, fourier_apply]
    rw [norm_mul, h1, one_mul, Complex.norm_real]
  rw [firstModeM, firstMode, integral_densMeasure hρ0 hρ1, integral_densMeasure hρ0 hρ1,
    Complex.normSq_apply]
  have hr := integral_re hie
  have hm := integral_im hie
  simp only [RCLike.re_to_complex, RCLike.im_to_complex] at hr hm
  rw [← hr, ← hm]
  simp only [RCLike.re_to_complex, RCLike.im_to_complex, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, add_zero, gCos, sCos]
  have e1 : ∀ x, ρ x * (expT x).re = (expT x).re * ρ x := fun x => mul_comm _ _
  have e2 : ∀ x, ρ x * (expT x).im = (expT x).im * ρ x := fun x => mul_comm _ _
  simp_rw [e1, e2]
  ring

/-! ### Free energy, minimizer, gap -/

theorem integral_sCos : ∫ y, sCos y ∂haar 1 = 0 := by
  have := integral_fun_expT_im (fun s => s)
  rw [show (∫ y, sCos y ∂haar 1) = ∫ y : Torus 1, (expT y).im from rfl, this,
    intervalIntegral.integral_comp_mul_left (fun s => Real.sin s) (by positivity), integral_sin]
  simp

theorem firstModeM_haar : firstModeM (haar 1) = 0 := by
  simp [firstModeM, integral_gCos, integral_sCos]

theorem freeEnergy_cos (κ : ℝ) (μ : Measure (Torus 1)) [IsProbabilityMeasure μ] :
    freeEnergy cosV (cosW κ) μ =
      ((klDiv μ (haar 1) : ℝ≥0∞) : EReal) + ((κ * (firstModeM μ - 1) / 2 : ℝ) : EReal) := by
  unfold freeEnergy
  rw [interE_cos]
  simp [potE, cosV]

theorem freeEnergy_cos_haar (κ : ℝ) :
    freeEnergy cosV (cosW κ) (haar 1) = ((-κ / 2 : ℝ) : EReal) := by
  rw [freeEnergy_cos, klDiv_self, firstModeM_haar]
  simp only [EReal.coe_ennreal_zero, zero_add]
  congr 1; ring

theorem Fstar_cos {κ : ℝ} (hκ : 0 < κ) : Fstar cosV (cosW κ) = ((-κ / 2 : ℝ) : EReal) := by
  apply le_antisymm
  · exact (iInf_le (fun ρ : ProbabilityMeasure (Torus 1) => freeEnergy cosV (cosW κ) ρ)
      ⟨haar 1, inferInstance⟩).trans (freeEnergy_cos_haar κ).le
  · refine le_iInf fun μ => ?_
    rw [freeEnergy_cos]
    have hQ := firstModeM_nonneg (μ : Measure (Torus 1))
    calc ((-κ / 2 : ℝ) : EReal) ≤ ((κ * (firstModeM μ - 1) / 2 : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.mpr (by nlinarith)
      _ = 0 + ((κ * (firstModeM μ - 1) / 2 : ℝ) : EReal) := (zero_add _).symm
      _ ≤ _ := add_le_add (EReal.coe_ennreal_nonneg _) le_rfl

theorem isMinimizer_cos_iff {κ : ℝ} (hκ : 0 < κ) (μ : ProbabilityMeasure (Torus 1)) :
    IsMinimizer cosV (cosW κ) μ ↔ (μ : Measure (Torus 1)) = haar 1 := by
  unfold IsMinimizer
  rw [Fstar_cos hκ, freeEnergy_cos]
  constructor
  · intro h
    have hK : klDiv (μ : Measure (Torus 1)) (haar 1) ≠ ⊤ := by
      intro hK; rw [hK] at h; simp at h
    rw [← EReal.coe_ennreal_toReal hK, ← EReal.coe_add, EReal.coe_eq_coe_iff] at h
    have hQ := firstModeM_nonneg (μ : Measure (Torus 1))
    have hk0 := ENNReal.toReal_nonneg (a := klDiv (μ : Measure (Torus 1)) (haar 1))
    have hk : (klDiv (μ : Measure (Torus 1)) (haar 1)).toReal = 0 := by nlinarith
    have : klDiv (μ : Measure (Torus 1)) (haar 1) = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).mp hk with h0 | h0
      · exact h0
      · exact absurd h0 hK
    exact (klDiv_eq_zero_iff).mp this
  · intro h
    rw [h, klDiv_self, firstModeM_haar]
    simp only [EReal.coe_ennreal_zero, zero_add]
    congr 1; ring

theorem gap_cos {κ : ℝ} (hκ : 0 < κ) (μ : Measure (Torus 1)) [IsProbabilityMeasure μ] :
    gap cosV (cosW κ) μ =
      ((klDiv μ (haar 1) : ℝ≥0∞) : EReal) + ((κ / 2 * firstModeM μ : ℝ) : EReal) := by
  unfold gap
  rw [freeEnergy_cos, Fstar_cos hκ]
  by_cases hK : klDiv μ (haar 1) = ⊤
  · rw [hK, EReal.coe_ennreal_top, EReal.top_add_coe, EReal.top_sub_coe, EReal.top_add_coe]
  · rw [← EReal.coe_ennreal_toReal hK, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_add]
    congr 1; ring

/-! ### The convolution and the dissipation -/

theorem integrable_mul_bdd {ρ : Torus 1 → ℝ} (hi : Integrable ρ (haar 1)) {F : Torus 1 → ℝ}
    (hF : Continuous F) (hFb : ∀ y, |F y| ≤ 1) : Integrable (fun y => F y * ρ y) (haar 1) :=
  Integrable.mono' hi.norm (hF.aestronglyMeasurable.mul hi.aestronglyMeasurable)
    (Eventually.of_forall fun y => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (abs_nonneg _) (hFb y))

/-- `(g*ρ)(x) = A cos(2πx) + B sin(2πx)`. -/
theorem gConv_eq {ρ : Torus 1 → ℝ} (hρ1 : ∫ x, ρ x ∂haar 1 = 1) (x : Torus 1) :
    gConv ρ x = gCos x * (∫ y, gCos y * ρ y ∂haar 1) + sCos x * (∫ y, sCos y * ρ y ∂haar 1) := by
  have hi := integrable_of_integral_eq_one hρ1
  have i1 := integrable_mul_bdd hi continuous_gCos abs_gCos_le
  have i2 := integrable_mul_bdd hi continuous_sCos abs_sCos_le
  unfold gConv
  simp_rw [gCos_sub]
  have e : ∀ y, (gCos x * gCos y + sCos x * sCos y) * ρ y =
      gCos x * (gCos y * ρ y) + sCos x * (sCos y * ρ y) := fun y => by ring
  simp_rw [e]
  rw [integral_add (f := fun y => gCos x * (gCos y * ρ y)) (g := fun y => sCos x * (sCos y * ρ y))
    (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]

theorem convDens_cos (κ : ℝ) {ρ : Torus 1 → ℝ} (hρ1 : ∫ x, ρ x ∂haar 1 = 1) (x : Torus 1) :
    convDens (cosW κ) ρ x = κ * (gConv ρ x - 1) := by
  have hi := integrable_of_integral_eq_one hρ1
  have i1 := integrable_mul_bdd hi (continuous_gCos.comp (continuous_const.sub continuous_id))
    (fun y => abs_gCos_le (x - y))
  unfold convDens cosW gConv
  have e : ∀ y, κ * (gCos (x - y) - 1) * ρ y = κ * (gCos (x - y) * ρ y - ρ y) := fun y => by ring
  simp_rw [e]
  rw [integral_const_mul, integral_sub (f := fun y => gCos (x - y) * ρ y) i1 hi, hρ1]

theorem gConv_lift {ρ : Torus 1 → ℝ} (hρ1 : ∫ x, ρ x ∂haar 1 = 1) :
    gConv ρ ∘ liftT = fun z : Fin 1 → ℝ =>
      Real.cos (2 * π * z 0) * (∫ y, gCos y * ρ y ∂haar 1) +
        Real.sin (2 * π * z 0) * (∫ y, sCos y * ρ y ∂haar 1) := by
  funext z
  simp only [Function.comp_apply, gConv_eq hρ1]
  rw [gCos_coe (liftT z) (z 0) rfl, sCos, expT_im_coe (liftT z) (z 0) rfl]

theorem contDiff_gConv_lift {ρ : Torus 1 → ℝ} (hρ1 : ∫ x, ρ x ∂haar 1 = 1) :
    ContDiff ℝ ⊤ (gConv ρ ∘ liftT) := by
  rw [gConv_lift hρ1]
  exact ((Real.contDiff_cos.comp (contDiff_const.mul (contDiff_apply ℝ ℝ 0))).mul
    contDiff_const).add ((Real.contDiff_sin.comp (contDiff_const.mul (contDiff_apply ℝ ℝ 0))).mul
    contDiff_const)

/-- The dissipation of the cosine model, (3.4). -/
theorem dissipation_cos (κ : ℝ) {ρ : Torus 1 → ℝ} (hρ1 : ∫ x, ρ x ∂haar 1 = 1)
    (hH1 : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    dissipation cosV (cosW κ) ρ =
      ∫⁻ x, ENNReal.ofReal ((2 * weakGrad (fun y => Real.sqrt (ρ y)) x 0 +
        κ * Real.sqrt (ρ x) * weakGrad (gConv ρ) x 0) ^ 2) ∂haar 1 := by
  have hf1 : (fun x => cosV x + convDens (cosW κ) ρ x) = fun x => κ * (gConv ρ x - 1) := by
    funext x; simp [cosV, convDens_cos κ hρ1]
  have hG : ContDiff ℝ 1 (gConv ρ ∘ liftT) := (contDiff_gConv_lift hρ1).of_le le_top
  have hF : ContDiff ℝ 1 ((fun x => κ * (gConv ρ x - 1)) ∘ liftT) :=
    contDiff_const.mul (hG.sub contDiff_const)
  unfold dissipation
  rw [hf1, if_pos ⟨hH1, ⟨_, isWeakGrad_of_contDiff hF⟩⟩]
  refine lintegral_congr_ae ?_
  filter_upwards [weakGrad_ae_eq_of_contDiff hF, weakGrad_ae_eq_of_contDiff hG] with x h1 h2
  rw [Fin.sum_univ_one, h1, h2]
  have hd : fderiv ℝ ((fun x => κ * (gConv ρ x - 1)) ∘ liftT) (secT x) (Pi.single 0 1) =
      κ * fderiv ℝ (gConv ρ ∘ liftT) (secT x) (Pi.single 0 1) := by
    rw [show ((fun x => κ * (gConv ρ x - 1)) ∘ liftT) =
      fun z => κ * ((gConv ρ ∘ liftT) z - 1) from rfl, fderiv_const_mul
      ((hG.differentiable one_ne_zero (secT x)).sub_const 1), fderiv_sub_const]
    rfl
  simp only [hd]
  ring_nf

/-- (3.4). -/
theorem cosine_free_energy_aux {κ : ℝ} (hκ : 0 < κ) :
    (∀ ρ : Torus 1 → ℝ, (∀ x, 0 ≤ ρ x) → ∫ x, ρ x ∂haar 1 = 1 →
      interE (cosW κ) (densMeasure ρ) (densMeasure ρ) = κ * (firstMode ρ - 1)) ∧
    Fstar cosV (cosW κ) = ((-κ / 2 : ℝ) : EReal) ∧
    (∀ μ : ProbabilityMeasure (Torus 1),
      IsMinimizer cosV (cosW κ) μ ↔ (μ : Measure (Torus 1)) = haar 1) ∧
    (∀ ρ : Torus 1 → ℝ, (∀ x, 0 ≤ ρ x) → ∫ x, ρ x ∂haar 1 = 1 →
      gap cosV (cosW κ) (densMeasure ρ) =
        ((klDiv (densMeasure ρ) (haar 1) : ENNReal) : EReal) + ((κ / 2 * firstMode ρ : ℝ) : EReal)) ∧
    (∀ ρ : Torus 1 → ℝ, (∀ x, 0 ≤ ρ x) → ∫ x, ρ x ∂haar 1 = 1 →
      MemH1 (haar 1) (fun x => Real.sqrt (ρ x)) →
      dissipation cosV (cosW κ) ρ =
        ∫⁻ x, ENNReal.ofReal ((2 * weakGrad (fun y => Real.sqrt (ρ y)) x 0 +
          κ * Real.sqrt (ρ x) * weakGrad (gConv ρ) x 0) ^ 2) ∂haar 1) := by
  refine ⟨fun ρ hρ0 hρ1 => ?_, Fstar_cos hκ, isMinimizer_cos_iff hκ, fun ρ hρ0 hρ1 => ?_,
    fun ρ _ hρ1 hH1 => dissipation_cos κ hρ1 hH1⟩
  · have := isProbabilityMeasure_densMeasure hρ0 hρ1
    rw [interE_cos, firstModeM_densMeasure hρ0 hρ1]
  · have := isProbabilityMeasure_densMeasure hρ0 hρ1
    rw [gap_cos hκ, firstModeM_densMeasure hρ0 hρ1]

/-! ### (3.20): Pinsker and the entropy comparisons -/

theorem klDiv_densMeasure {ρ : Torus 1 → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar 1 = 1) :
    klDiv (densMeasure ρ) (haar 1) = ∫⁻ x, ENNReal.ofReal (klFun (ρ x)) ∂haar 1 := by
  have := isProbabilityMeasure_densMeasure hρ0 hρ1
  have hm : AEMeasurable (fun x => ENNReal.ofReal (ρ x)) (haar 1) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (integrable_of_integral_eq_one hρ1).aestronglyMeasurable.aemeasurable
  rw [klDiv_eq_lintegral_klFun_of_ac (μ := densMeasure ρ) (ν := haar 1)
    (withDensity_absolutelyContinuous _ _)]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_withDensity₀ (haar 1) hm] with x hx
  rw [densMeasure, hx, ENNReal.toReal_ofReal (hρ0 x)]

theorem integral_expT : ∫ x, expT x ∂haar 1 = 0 := by
  have hi : Integrable expT (haar 1) :=
    (BoundedContinuousFunction.mkOfCompact ⟨expT, continuous_expT⟩).integrable _
  apply Complex.ext
  · have := integral_re hi
    simp only [RCLike.re_to_complex] at this
    rw [← this]; exact integral_gCos
  · have := integral_im hi
    simp only [RCLike.im_to_complex] at this
    rw [← this]; exact integral_sCos

theorem firstMode_le {ρ : Torus 1 → ℝ} (hρ1 : ∫ x, ρ x ∂haar 1 = 1) :
    ENNReal.ofReal (firstMode ρ) ≤ (∫⁻ x, ‖ρ x - 1‖ₑ ∂haar 1) ^ 2 := by
  have hi := integrable_of_integral_eq_one hρ1
  have hie : ∀ {f : Torus 1 → ℝ}, Integrable f (haar 1) →
      Integrable (fun x => expT x * (f x : ℂ)) (haar 1) := fun {f} hf => by
    refine Integrable.mono' hf.norm (continuous_expT.aestronglyMeasurable.mul
      hf.ofReal.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    have h1 : ‖expT x‖ = 1 := by simp [expT, fourier_apply]
    rw [norm_mul, h1, one_mul, Complex.norm_real]
  have hi1 : Integrable (fun x => ρ x - 1) (haar 1) := hi.sub (integrable_const 1)
  have hz : ∫ x, expT x * (ρ x : ℂ) ∂haar 1 = ∫ x, expT x * ((ρ x - 1 : ℝ) : ℂ) ∂haar 1 := by
    have e : ∀ x, expT x * (ρ x : ℂ) = expT x * ((ρ x - 1 : ℝ) : ℂ) + expT x := fun x => by
      push_cast; ring
    simp_rw [e]
    rw [integral_add (f := fun x => expT x * ((ρ x - 1 : ℝ) : ℂ)) (g := expT) (hie hi1)
      ((BoundedContinuousFunction.mkOfCompact ⟨expT, continuous_expT⟩).integrable _),
      integral_expT, add_zero]
  have hn : ‖∫ x, expT x * ((ρ x - 1 : ℝ) : ℂ) ∂haar 1‖ ≤ ∫ x, ‖ρ x - 1‖ ∂haar 1 := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
      (Eventually.of_forall fun x => ?_)))
    have h1 : ‖expT x‖ = 1 := by simp [expT, fourier_apply]
    simp only [norm_mul, h1, one_mul, Complex.norm_real]
  rw [firstMode, hz, Complex.normSq_eq_norm_sq, ← ofReal_integral_norm_eq_lintegral_enorm hi1,
    ← ENNReal.ofReal_pow (integral_nonneg fun x => norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hn 2)

/-- (3.20). -/
theorem cosine_entropy_comparison_aux {κ : ℝ} (hκ : 0 < κ) {ρ : Torus 1 → ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar 1 = 1) :
    ENNReal.ofReal (firstMode ρ) ≤ eLpNorm (fun x => ρ x - 1) 1 (haar 1) ^ 2 ∧
    eLpNorm (fun x => ρ x - 1) 1 (haar 1) ^ 2 ≤ 2 * klDiv (densMeasure ρ) (haar 1) ∧
    ((klDiv (densMeasure ρ) (haar 1) : ENNReal) : EReal) ≤ gap cosV (cosW κ) (densMeasure ρ) ∧
    gap cosV (cosW κ) (densMeasure ρ) ≤
      ((1 + κ : ℝ) : EReal) * ((klDiv (densMeasure ρ) (haar 1) : ENNReal) : EReal) := by
  have hi := integrable_of_integral_eq_one hρ1
  have hL : eLpNorm (fun x => ρ x - 1) 1 (haar 1) = ∫⁻ x, ‖ρ x - 1‖ₑ ∂haar 1 :=
    eLpNorm_one_eq_lintegral_enorm (hi.sub (integrable_const 1)).aestronglyMeasurable
  have h1 : ENNReal.ofReal (firstMode ρ) ≤ eLpNorm (fun x => ρ x - 1) 1 (haar 1) ^ 2 := by
    rw [hL]; exact firstMode_le hρ1
  have h2 : eLpNorm (fun x => ρ x - 1) 1 (haar 1) ^ 2 ≤ 2 * klDiv (densMeasure ρ) (haar 1) := by
    rw [hL, klDiv_densMeasure hρ0 hρ1]; exact pinsker_lintegral hρ0 hi hρ1
  have hgap := (cosine_free_energy_aux hκ).2.2.2.1 ρ hρ0 hρ1
  have hQ : 0 ≤ firstMode ρ := Complex.normSq_nonneg _
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [hgap]
    exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr (by positivity))
  · rw [hgap]
    by_cases hK : klDiv (densMeasure ρ) (haar 1) = ⊤
    · rw [hK, EReal.coe_ennreal_top, EReal.coe_mul_top_of_pos (by linarith)]
      exact le_top
    · have hQk : firstMode ρ ≤ 2 * (klDiv (densMeasure ρ) (haar 1)).toReal := by
        have h12 := h1.trans h2
        rw [← ENNReal.ofReal_toReal hK, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul
          (by norm_num), ENNReal.ofReal_le_ofReal_iff (by positivity)] at h12
        exact h12
      rw [← EReal.coe_ennreal_toReal hK, ← EReal.coe_add, ← EReal.coe_mul, EReal.coe_le_coe_iff]
      nlinarith

end SharpLSI
