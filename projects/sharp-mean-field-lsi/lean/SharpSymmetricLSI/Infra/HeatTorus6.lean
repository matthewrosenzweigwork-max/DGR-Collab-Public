import SharpSymmetricLSI.Infra.HeatTorus5

/-!
# The periodic heat kernel on `𝕋^ι` (I4, part 6): the divergence kernel

`∂ₖG_t(y) = -G_t(y) yₖ/(2t)` and `∫|∂ₖG_t| = (πt)^{-1/2}`. Consequently
`|∇·e^{tΔ}F| ≤ |ι| (πt)^{-1/2} M` if `|Fₖ| ≤ M`, and
`∫|∇·e^{tΔ}F| ≤ (πt)^{-1/2} ∑ₖ ∫|Fₖ|` (`lintegral_divHeatT_le`).
-/

open MeasureTheory Set Filter Topology
open scoped Real ContDiff ENNReal

namespace SharpLSI

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem differentiable_heatKernel (t : ℝ) : Differentiable ℝ (heatKernel (ι := ι) t) := by
  unfold heatKernel; fun_prop

theorem hasDerivAt_gauss1 (t r : ℝ) : HasDerivAt (gauss1 t) (-(r / (2 * t)) * gauss1 t r) r := by
  unfold gauss1
  have h := ((((hasDerivAt_pow 2 r).neg).div_const (4 * t)).exp).const_mul
    ((4 * π * t) ^ (-(1 : ℝ) / 2))
  convert h using 1
  simp only [Pi.neg_apply, Nat.cast_ofNat]
  rcases eq_or_ne t 0 with ht | ht
  · subst ht; simp
  · field_simp; ring

theorem fderiv_heatKernel_single {t : ℝ} (ht : 0 < t) (y : ι → ℝ) (k : ι) :
    fderiv ℝ (heatKernel t) y (Pi.single k 1) = -(heatKernel t y * y k / (2 * t)) := by
  -- restrict to the line `s ↦ y + s eₖ`
  have hline : HasDerivAt (fun s : ℝ => y + s • (Pi.single k 1 : ι → ℝ)) (Pi.single k 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single k (1 : ℝ) : ι → ℝ)).const_add y
  have h1 := ((differentiable_heatKernel t (y + (0 : ℝ) • (Pi.single k 1 : ι → ℝ))).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hline)
  have hprod : ∀ s : ℝ, heatKernel t (y + s • (Pi.single k 1 : ι → ℝ)) =
      gauss1 t (y k + s) * ∏ j ∈ Finset.univ.erase k, gauss1 t (y j) := by
    intro s
    rw [heatKernel_eq_prod ht, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun j hj => ?_
      simp [Finset.ne_of_mem_erase hj]
  have h2 : HasDerivAt (fun s : ℝ => heatKernel t (y + s • (Pi.single k 1 : ι → ℝ)))
      ((-((y k + 0) / (2 * t)) * gauss1 t (y k + 0)) * ∏ j ∈ Finset.univ.erase k, gauss1 t (y j))
      0 := by
    simp_rw [hprod]
    exact ((hasDerivAt_gauss1 t (y k + 0)).comp (0 : ℝ) ((hasDerivAt_id 0).const_add (y k))
      |>.congr_deriv (by simp)).mul_const _
  have e := h1.unique h2
  simp only [zero_smul, add_zero] at e
  rw [e, heatKernel_eq_prod ht, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  ring

/-- `∫ |r| e^{-r²/(4t)} dr = 4t`. -/
theorem integral_abs_mul_gauss {t : ℝ} (ht : 0 < t) :
    ∫ r : ℝ, |r| * Real.exp (-r ^ 2 / (4 * t)) = 4 * t := by
  have h := integral_comp_abs (f := fun r : ℝ => r * Real.exp (-r ^ 2 / (4 * t)))
  simp only [sq_abs] at h
  rw [h]
  have hc := integral_mul_cexp_neg_mul_sq (b := ((1 / (4 * t) : ℝ) : ℂ)) (by
    simp only [Complex.ofReal_re]; positivity)
  have hre : ∫ r in Ioi (0 : ℝ), r * Real.exp (-r ^ 2 / (4 * t)) = 2 * t := by
    have e : ∀ r : ℝ, (r : ℂ) * Complex.exp (-((1 / (4 * t) : ℝ) : ℂ) * (r : ℂ) ^ 2) =
        ((r * Real.exp (-r ^ 2 / (4 * t)) : ℝ) : ℂ) := by
      intro r; push_cast; congr 2; ring
    simp_rw [e, integral_complex_ofReal] at hc
    have : ((2 * ((1 / (4 * t) : ℝ) : ℂ))⁻¹ : ℂ) = ((2 * t : ℝ) : ℂ) := by
      push_cast; field_simp; ring
    rw [this] at hc
    exact_mod_cast hc
  rw [hre]; ring

/-- `∫|r| g_t(r) dr = (4πt)^{-1/2} 4t`. -/
theorem integral_abs_mul_gauss1 {t : ℝ} (ht : 0 < t) :
    ∫ r : ℝ, |r| * gauss1 t r = (4 * π * t) ^ (-(1 : ℝ) / 2) * (4 * t) := by
  unfold gauss1
  simp_rw [show ∀ r : ℝ, |r| * ((4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (-r ^ 2 / (4 * t))) =
    (4 * π * t) ^ (-(1 : ℝ) / 2) * (|r| * Real.exp (-r ^ 2 / (4 * t))) from fun r => by ring]
  rw [integral_const_mul, integral_abs_mul_gauss ht]

theorem integrable_abs_mul_gauss1 {t : ℝ} (ht : 0 < t) : Integrable fun r : ℝ => |r| * gauss1 t r := by
  by_contra h
  have := integral_abs_mul_gauss1 ht
  rw [integral_undef h] at this
  have hp : 0 < (4 * π * t) ^ (-(1 : ℝ) / 2) * (4 * t) := by positivity
  linarith

theorem integral_gauss1 {t : ℝ} (ht : 0 < t) : ∫ r : ℝ, gauss1 t r = 1 := by
  unfold gauss1
  rw [integral_const_mul]
  have := integral_gaussian (1 / (4 * t))
  simp_rw [show ∀ r : ℝ, -r ^ 2 / (4 * t) = -(1 / (4 * t)) * r ^ 2 from fun r => by ring]
  rw [this, show π / (1 / (4 * t)) = 4 * π * t by field_simp, Real.sqrt_eq_rpow,
    ← Real.rpow_add (by positivity)]
  norm_num

/-- **`∫|∂ₖG_t| = (4πt)^{-1/2} · 2`.** -/
theorem integral_abs_fderiv_heatKernel {t : ℝ} (ht : 0 < t) (k : ι) :
    ∫ y : ι → ℝ, |fderiv ℝ (heatKernel t) y (Pi.single k 1)| =
      1 / (2 * t) * ((4 * π * t) ^ (-(1 : ℝ) / 2) * (4 * t)) := by
  set h : ι → ℝ → ℝ := fun j r => (if j = k then |r| else 1) * gauss1 t r
  have hy : ∀ y : ι → ℝ, |fderiv ℝ (heatKernel t) y (Pi.single k 1)| =
      1 / (2 * t) * ∏ j, h j (y j) := by
    intro y
    rw [fderiv_heatKernel_single ht, abs_neg, heatKernel_eq_prod ht, abs_div,
      abs_of_pos (by positivity : 0 < 2 * t), abs_mul, abs_of_pos
        (Finset.prod_pos fun i _ => gauss1_pos ht _)]
    simp only [h, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    ring
  simp_rw [hy]
  rw [integral_const_mul, volume_pi, integral_fintype_prod_eq_prod (μ := fun _ => volume) h]
  congr 1
  rw [Finset.prod_eq_single k]
  · simp only [h, ite_true]
    exact integral_abs_mul_gauss1 ht
  · intro j _ hj
    simp only [h, hj, ite_false, one_mul]
    exact integral_gauss1 ht
  · simp

theorem integrable_fderiv_heatKernel {t : ℝ} (ht : 0 < t) (k : ι) :
    Integrable fun y : ι → ℝ => fderiv ℝ (heatKernel t) y (Pi.single k 1) := by
  have hm : AEStronglyMeasurable (fun y : ι → ℝ => fderiv ℝ (heatKernel t) y (Pi.single k 1))
      volume := by
    simp_rw [fderiv_heatKernel_single ht]
    exact ((measurable_heatKernel t).mul (measurable_pi_apply k)).div_const _ |>.neg
      |>.aestronglyMeasurable
  by_contra h
  have h' : ¬ Integrable fun y : ι → ℝ => |fderiv ℝ (heatKernel t) y (Pi.single k 1)| := by
    intro hi; exact h ((integrable_norm_iff hm).1 (by simpa [Real.norm_eq_abs] using hi))
  have := integral_abs_fderiv_heatKernel (ι := ι) ht k
  rw [integral_undef h'] at this
  have hp : 0 < 1 / (2 * t) * ((4 * π * t) ^ (-(1 : ℝ) / 2) * (4 * t)) := by positivity
  linarith

/-- The constant `‖∂ₖG_t‖_{L¹}`. -/
noncomputable def divConst (t : ℝ) : ℝ := 1 / (2 * t) * ((4 * π * t) ^ (-(1 : ℝ) / 2) * (4 * t))

theorem divConst_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ divConst t := by unfold divConst; positivity

omit [DecidableEq ι] in
theorem qmp_sub_liftT (x : UnitAddTorus ι) :
    Measure.QuasiMeasurePreserving (fun y : ι → ℝ => x - liftT y) volume volume :=
  (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.comp quasiMeasurePreserving_liftT

/-- **Pointwise bound** for `∇·e^{tΔ}F`. -/
theorem abs_divHeatT_le {t : ℝ} (ht : 0 < t) {F : UnitAddTorus ι → ι → ℝ} {M : ℝ}
    (hM : ∀ k, ∀ᵐ z, |F z k| ≤ M) (x : UnitAddTorus ι) :
    |divHeatT t F x| ≤ Fintype.card ι * divConst t * M := by
  unfold divHeatT
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hk : ∀ k, |∫ y : ι → ℝ, fderiv ℝ (heatKernel t) y (Pi.single k 1) * F (x - liftT y) k| ≤
      divConst t * M := by
    intro k
    rw [← Real.norm_eq_abs]
    have hb := (integrable_fderiv_heatKernel ht k).abs.mul_const M
    refine (norm_integral_le_of_norm_le hb ?_).trans (le_of_eq ?_)
    · filter_upwards [(qmp_sub_liftT x).ae (hM k)] with y hy
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
    · rw [integral_mul_const, integral_abs_fderiv_heatKernel ht k, divConst]
  calc ∑ k, |∫ y : ι → ℝ, fderiv ℝ (heatKernel t) y (Pi.single k 1) * F (x - liftT y) k|
      ≤ ∑ _k : ι, divConst t * M := Finset.sum_le_sum fun k _ => hk k
    _ = Fintype.card ι * divConst t * M := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- **`L¹` bound** for `∇·e^{tΔ}F`. -/
theorem lintegral_divHeatT_le {t : ℝ} (ht : 0 < t) {F : UnitAddTorus ι → ι → ℝ}
    (hF : ∀ k, AEStronglyMeasurable (fun z => F z k) volume) :
    ∫⁻ x, ‖divHeatT t F x‖ₑ ≤ ENNReal.ofReal (divConst t) * ∑ k, ∫⁻ z, ‖F z k‖ₑ := by
  have hpt : ∀ x, ‖divHeatT t F x‖ₑ ≤ ∑ k, ∫⁻ y : ι → ℝ,
      ‖fderiv ℝ (heatKernel t) y (Pi.single k 1)‖ₑ * ‖F (x - liftT y) k‖ₑ := by
    intro x
    unfold divHeatT
    refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    simp_rw [enorm_mul]
  have hmeas : ∀ k, AEMeasurable (fun p : UnitAddTorus ι × (ι → ℝ) =>
      ‖fderiv ℝ (heatKernel t) p.2 (Pi.single k 1)‖ₑ * ‖F (p.1 - liftT p.2) k‖ₑ)
      (volume.prod volume) := by
    intro k
    have hd : Measurable fun y : ι → ℝ => fderiv ℝ (heatKernel t) y (Pi.single k 1) := by
      simp_rw [fderiv_heatKernel_single ht]
      exact ((measurable_heatKernel t).mul (measurable_pi_apply k)).div_const _ |>.neg
    have h1 : AEMeasurable (fun p : UnitAddTorus ι × (ι → ℝ) =>
        ‖fderiv ℝ (heatKernel t) p.2 (Pi.single k 1)‖ₑ) (volume.prod volume) :=
      (hd.comp measurable_snd).enorm.aemeasurable
    have hq : Measure.QuasiMeasurePreserving (fun p : UnitAddTorus ι × (ι → ℝ) => p.1 - liftT p.2)
        (volume.prod volume) volume := by
      refine MeasureTheory.QuasiMeasurePreserving.prod_of_left
        (measurable_fst.sub (measurable_liftT.comp measurable_snd))
        (Eventually.of_forall fun y => ?_)
      exact (measurePreserving_sub_right (volume : Measure (UnitAddTorus ι))
        (liftT y)).quasiMeasurePreserving
    have h2 : AEMeasurable (fun p : UnitAddTorus ι × (ι → ℝ) => ‖F (p.1 - liftT p.2) k‖ₑ)
        (volume.prod volume) :=
      (hF k).enorm.comp_quasiMeasurePreserving hq
    exact h1.mul h2
  calc ∫⁻ x, ‖divHeatT t F x‖ₑ
      ≤ ∫⁻ x, ∑ k, ∫⁻ y : ι → ℝ,
          ‖fderiv ℝ (heatKernel t) y (Pi.single k 1)‖ₑ * ‖F (x - liftT y) k‖ₑ :=
        lintegral_mono hpt
    _ = ∑ k, ∫⁻ x, ∫⁻ y : ι → ℝ,
          ‖fderiv ℝ (heatKernel t) y (Pi.single k 1)‖ₑ * ‖F (x - liftT y) k‖ₑ := by
        rw [lintegral_finsetSum' _ fun k _ => (hmeas k).lintegral_prod_right']
    _ = ∑ k, ∫⁻ y : ι → ℝ, ∫⁻ x,
          ‖fderiv ℝ (heatKernel t) y (Pi.single k 1)‖ₑ * ‖F (x - liftT y) k‖ₑ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        exact lintegral_lintegral_swap (hmeas k)
    _ = ∑ k, ∫⁻ y : ι → ℝ, ‖fderiv ℝ (heatKernel t) y (Pi.single k 1)‖ₑ * ∫⁻ z, ‖F z k‖ₑ := by
        refine Finset.sum_congr rfl fun k _ => lintegral_congr fun y => ?_
        have hm : AEMeasurable (fun x : UnitAddTorus ι => ‖F (x - liftT y) k‖ₑ) volume :=
          (hF k).enorm.comp_quasiMeasurePreserving
            (measurePreserving_sub_right (volume : Measure (UnitAddTorus ι))
              (liftT y)).quasiMeasurePreserving
        rw [lintegral_const_mul'' (‖fderiv ℝ (heatKernel t) y (Pi.single k 1)‖ₑ) hm]
        congr 1
        exact lintegral_sub_right_eq_self (fun z => ‖F z k‖ₑ) (liftT y)
    _ = ∑ k, ENNReal.ofReal (divConst t) * ∫⁻ z, ‖F z k‖ₑ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [lintegral_mul_const'' _ (integrable_fderiv_heatKernel ht k).aestronglyMeasurable.enorm]
        congr 1
        rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_fderiv_heatKernel ht k)]
        simp_rw [Real.norm_eq_abs]
        rw [integral_abs_fderiv_heatKernel ht k, divConst]
    _ = ENNReal.ofReal (divConst t) * ∑ k, ∫⁻ z, ‖F z k‖ₑ := by rw [Finset.mul_sum]

end SharpLSI
