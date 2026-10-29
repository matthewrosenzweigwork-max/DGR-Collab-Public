import SharpSymmetricLSI.Infra.HeatTorus7

/-!
# The periodic heat kernel on `𝕋^ι` (I4, part 8): `e^{tΔ} f → f` in `L¹` as `t ↓ 0`

Rescaling `y = √t z`: `e^{tΔ}g (x) = ∫ g(x - π(√t z)) G₁(z) dz`; for continuous `g` this tends
to `g(x)` by dominated convergence, and the `L¹` statement for integrable `f` follows from the
density of continuous functions and the `L¹` contraction (`tendsto_heatT_L1`).
-/

open MeasureTheory Set Filter Topology
open scoped Real ContDiff ENNReal

namespace SharpLSI

variable {ι : Type*} [Fintype ι]

theorem heatKernel_smul {t : ℝ} (ht : 0 < t) (z : ι → ℝ) :
    heatKernel t (Real.sqrt t • z) = (Real.sqrt t ^ Fintype.card ι)⁻¹ * heatKernel 1 z := by
  unfold heatKernel
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have e1 : (-∑ k, (Real.sqrt t • z) k ^ 2) / (4 * t) = (-∑ k, z k ^ 2) / (4 * 1) := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, hs, ← Finset.mul_sum]
    field_simp
  rw [e1]
  have e2 : (4 * π * t) ^ (-(Fintype.card ι : ℝ) / 2) =
      (Real.sqrt t ^ Fintype.card ι)⁻¹ * (4 * π * 1) ^ (-(Fintype.card ι : ℝ) / 2) := by
    rw [mul_one, Real.mul_rpow (by positivity) ht.le]
    rw [show t ^ (-(Fintype.card ι : ℝ) / 2) = (Real.sqrt t ^ Fintype.card ι)⁻¹ by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_neg ht.le]
      ring_nf]
    ring
  rw [e2]; ring

/-- `e^{tΔ}g (x) = ∫ g(x - π(√t z)) G₁(z) dz`. -/
theorem heatT_rescale {t : ℝ} (ht : 0 < t) (g : UnitAddTorus ι → ℝ) (x : UnitAddTorus ι) :
    heatT t g x = ∫ z, g (x - liftT (Real.sqrt t • z)) * heatKernel 1 z := by
  rw [heatT]
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have h := Measure.integral_comp_smul (μ := (volume : Measure (ι → ℝ)))
    (fun y => g (x - liftT y) * heatKernel t y) (Real.sqrt t)
  simp only [Module.finrank_fintype_fun_eq_card] at h
  simp_rw [heatKernel_smul ht] at h
  have hc : 0 < (Real.sqrt t ^ Fintype.card ι)⁻¹ := by positivity
  rw [abs_of_pos hc, smul_eq_mul] at h
  have h' : ∫ z, g (x - liftT (Real.sqrt t • z)) * ((Real.sqrt t ^ Fintype.card ι)⁻¹ *
      heatKernel 1 z) = (Real.sqrt t ^ Fintype.card ι)⁻¹ *
        ∫ z, g (x - liftT (Real.sqrt t • z)) * heatKernel 1 z := by
    rw [← integral_const_mul]; congr 1; funext z; ring
  rw [h'] at h
  exact (mul_left_cancel₀ hc.ne' h).symm

theorem heatT_sub {t : ℝ} (ht : 0 < t) {f g : UnitAddTorus ι → ℝ} (hf : Integrable f)
    (hg : Integrable g) (x : UnitAddTorus ι) :
    heatT t f x - heatT t g x = heatT t (fun y => f y - g y) x := by
  obtain ⟨M, hM⟩ := heatP_bdd (ι := ι) ht
  have hi : ∀ h : UnitAddTorus ι → ℝ, Integrable h → Integrable fun w => heatP t w * h (x - w) :=
    fun h hh => (hh.comp_sub_left x).bdd_mul (c := M) (measurable_heatP ht).aestronglyMeasurable
      (Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hM w)
  rw [heatT_eq ht hf.aestronglyMeasurable, heatT_eq ht hg.aestronglyMeasurable,
    heatT_eq ht (f := fun y => f y - g y) (hf.sub hg).aestronglyMeasurable]
  refine (integral_sub (hi f hf) (hi g hg)).symm.trans ?_
  congr 1; funext z; ring

/-- **Pointwise convergence for continuous data.** -/
theorem tendsto_heatT_of_continuous {g : UnitAddTorus ι → ℝ} (hg : Continuous g)
    (x : UnitAddTorus ι) : Tendsto (fun t => heatT t g x) (𝓝[>] 0) (𝓝 (g x)) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), heatT t g x =
      ∫ z, g (x - liftT (Real.sqrt t • z)) * heatKernel 1 z :=
    eventually_nhdsWithin_of_forall fun t ht => heatT_rescale ht g x
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  have hlim : ∫ z : ι → ℝ, g x * heatKernel 1 z = g x := by
    rw [integral_const_mul, integral_heatKernel one_pos, mul_one]
  rw [← hlim]
  refine tendsto_integral_filter_of_dominated_convergence (bound := fun z => C * heatKernel 1 z)
    (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ?_)
    ((integrable_heatKernel one_pos).const_mul C) ?_
  · have hcz : Continuous fun z : ι → ℝ => g (x - liftT (Real.sqrt t • z)) :=
      hg.comp ((continuous_const (y := x)).sub (continuous_liftT.comp
        (continuous_id.const_smul (Real.sqrt t))))
    exact (hcz.mul (differentiable_heatKernel (ι := ι) 1).continuous).aestronglyMeasurable
  · refine Eventually.of_forall fun z => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (heatKernel_pos one_pos z)]
    exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hC _ (mem_univ _))
      (heatKernel_pos one_pos z).le
  · refine Eventually.of_forall fun z => ?_
    refine Tendsto.mul_const _ ?_
    have h1 : Tendsto (fun t : ℝ => Real.sqrt t • z) (𝓝[>] 0) (𝓝 0) := by
      have := ((Real.continuous_sqrt.tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).smul_const z
      simpa using this
    have h2 := ((hg.comp ((continuous_const (y := x)).sub continuous_liftT)).tendsto
      (0 : ι → ℝ)).comp h1
    have e : liftT (0 : ι → ℝ) = 0 := by funext i; simp [liftT]
    simpa [Function.comp_def, e] using h2

theorem continuous_heatT {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ} (hf : Integrable f) :
    Continuous (heatT t f) := by
  have hq : Topology.IsQuotientMap (liftT (ι := ι)) :=
    IsOpenQuotientMap.isQuotientMap
      (IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk)
  exact hq.continuous_iff.2 (isSmoothT_heatT ht hf).continuous

theorem lintegral_enorm_heatT_le {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ}
    (hf : Integrable f) : ∫⁻ x, ‖heatT t f x‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_heatT ht hf),
    ← ofReal_integral_norm_eq_lintegral_enorm hf]
  refine ENNReal.ofReal_le_ofReal ?_
  simp_rw [Real.norm_eq_abs]
  exact integral_abs_heatT_le ht hf

/-- **`e^{tΔ} f → f` in `L¹`.** -/
theorem tendsto_heatT_L1 {f : UnitAddTorus ι → ℝ} (hf : Integrable f) :
    Tendsto (fun t => ∫⁻ x, ‖heatT t f x - f x‖ₑ) (𝓝[>] 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : ε / 3 ≠ 0 := by simpa using hε.ne'
  obtain ⟨g, hgε, hgi⟩ := hf.exists_boundedContinuous_lintegral_sub_le hε3
  have hgc : Continuous g := g.continuous
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hgc.continuousOn
  have hC' : ∀ x, |g x| ≤ C := fun x => by simpa [Real.norm_eq_abs] using hC x (mem_univ x)
  -- the continuous part
  have hcont : Tendsto (fun t => ∫⁻ x, ‖heatT t g x - g x‖ₑ) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
      (μ := (volume : Measure (UnitAddTorus ι))) (bound := fun _ => ENNReal.ofReal (2 * C))
      (F := fun t x => ‖heatT t g x - g x‖ₑ) (f := fun _ => 0) ?_ ?_ ?_ ?_
    · simpa using h
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact ((continuous_heatT ht hgi).sub hgc).measurable.enorm
    · filter_upwards [self_mem_nhdsWithin] with t ht
      refine Eventually.of_forall fun x => ?_
      rw [← ofReal_norm, Real.norm_eq_abs]
      refine ENNReal.ofReal_le_ofReal ((abs_sub _ _).trans ?_)
      have := abs_heatT_le ht hgc.aestronglyMeasurable (Eventually.of_forall hC') x
      linarith [hC' x]
    · simp only [lintegral_const, measure_univ, mul_one]
      exact ENNReal.ofReal_ne_top
    · refine Eventually.of_forall fun x => ?_
      have := ((tendsto_heatT_of_continuous hgc x).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => g x) (𝓝[>] 0) (𝓝 (g x)))).enorm
      rwa [sub_self, enorm_zero] at this
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hcont) (ε / 3)
      (ENNReal.div_pos hε.ne' (by norm_num)),
    self_mem_nhdsWithin] with t ht ht0
  have hpt : ∀ x, ‖heatT t f x - f x‖ₑ ≤
      ‖heatT t (fun y => f y - g y) x‖ₑ + ‖heatT t g x - g x‖ₑ + ‖f x - g x‖ₑ := by
    intro x
    have e : heatT t f x - f x =
        heatT t (fun y => f y - g y) x + (heatT t g x - g x) - (f x - g x) := by
      rw [← heatT_sub ht0 hf hgi]; ring
    rw [e]
    exact (enorm_sub_le).trans (add_le_add (enorm_add_le _ _) le_rfl)
  have hm1 : AEMeasurable (fun x => ‖heatT t (fun y => f y - g y) x‖ₑ) :=
    (integrable_heatT ht0 (hf.sub hgi)).aestronglyMeasurable.enorm
  have hm2 : AEMeasurable (fun x => ‖heatT t g x - g x‖ₑ) :=
    ((continuous_heatT ht0 hgi).sub hgc).measurable.enorm.aemeasurable
  calc ∫⁻ x, ‖heatT t f x - f x‖ₑ
      ≤ ∫⁻ x, (‖heatT t (fun y => f y - g y) x‖ₑ + ‖heatT t g x - g x‖ₑ + ‖f x - g x‖ₑ) :=
        lintegral_mono hpt
    _ = (∫⁻ x, ‖heatT t (fun y => f y - g y) x‖ₑ) + (∫⁻ x, ‖heatT t g x - g x‖ₑ) +
          ∫⁻ x, ‖f x - g x‖ₑ := by
        rw [lintegral_add_left' (f := fun x => ‖heatT t (fun y => f y - g y) x‖ₑ +
          ‖heatT t g x - g x‖ₑ) (hm1.add hm2), lintegral_add_left' hm1]
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        exact (lintegral_enorm_heatT_le ht0 (hf.sub hgi)).trans hgε
    _ = ε := ENNReal.add_thirds ε

end SharpLSI
