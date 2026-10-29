import SharpSymmetricLSI.Paper.LyapSchmidt12

/-!
# Proposition 2.1 (lane s42; R02): the second variation at a minimizer

For a minimizer `μ = p m` and a bounded measurable `h` with `μ(h) = 0`, and `|t| ‖h‖_∞ ≤ 1/2`,
`G(μ(1+th)) = ∫ klFun(1+th) dμ + (t²/2) ⟨h, T h⟩_{L²(μ)}` exactly (`gap_pert_toReal`, from
R17 `G = H(·|μ) + J`), and `|klFun(1+u) - u²/2| ≤ 4|u|³` for `|u| ≤ 1/2`. Hence
`G(μ(1+th))/t² → ½⟨h,(I+T)h⟩` (`tendsto_gap_pert`).
-/

open MeasureTheory Filter Topology InformationTheory Set

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `|klFun(1+u) - u²/2| ≤ 4|u|³` for `|u| ≤ 1/2`. -/
theorem abs_klFun_one_add_sub_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |klFun (1 + u) - u ^ 2 / 2| ≤ 4 * |u| ^ 3 := by
  have hu' : |(-u)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hu' 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at h
  set E := Real.log (1 + u) - u + u ^ 2 / 2 with hE
  have hE' : |E| ≤ 2 * |u| ^ 3 := by
    have e : (0 : ℝ) + (-u) ^ (0 + 1) / ((0 : ℕ) + 1 : ℝ) + (-u) ^ (1 + 1) / ((1 : ℕ) + 1 : ℝ) +
        Real.log (1 + u) = E := by
      rw [hE]; push_cast; ring
    rw [e] at h
    have h1 : 0 < 1 - |u| := by linarith
    refine h.trans ?_
    rw [div_le_iff₀ h1, show (2 : ℕ) + 1 = 3 from rfl]
    have := pow_nonneg (abs_nonneg u) 3
    nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 * (1 - |u|) by linarith) this]
  have hk : klFun (1 + u) - u ^ 2 / 2 = -(u ^ 3) / 2 + (1 + u) * E := by
    rw [klFun_apply, hE]; ring
  rw [hk]
  have h1u : |1 + u| ≤ 3 / 2 := by
    rw [abs_le]; constructor <;> linarith [abs_le.mp hu |>.1, abs_le.mp hu |>.2]
  calc |-(u ^ 3) / 2 + (1 + u) * E| ≤ |-(u ^ 3) / 2| + |(1 + u) * E| := abs_add_le _ _
    _ = |u| ^ 3 / 2 + |1 + u| * |E| := by rw [abs_div, abs_neg, abs_pow, abs_mul]; norm_num
    _ ≤ |u| ^ 3 / 2 + 3 / 2 * (2 * |u| ^ 3) := by
        gcongr
    _ ≤ 4 * |u| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg u) 3]

theorem klFun_one_add_le {u : ℝ} (hu : -1 < u) : klFun (1 + u) ≤ u ^ 2 := by
  rw [klFun_apply]
  have h1 : 0 < 1 + u := by linarith
  have := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos h1) h1.le
  nlinarith

section pert
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
include hyp hμ

/-- The perturbed density `p (1 + t h)`. -/
theorem pert_props {h : Torus d → ℝ} (hm : Measurable h) {B : ℝ} (hb : ∀ x, |h x| ≤ B)
    (hh0 : ∫ x, h x ∂(μ : Measure (Torus d)) = 0) {t : ℝ} (ht : |t| * B ≤ 1 / 2) :
    (∀ x, 0 ≤ elDens V W (μ : Measure (Torus d)) x * (1 + t * h x)) ∧
      ∫ x, elDens V W (μ : Measure (Torus d)) x * (1 + t * h x) ∂haar d = 1 ∧
      densMeasure (fun x => elDens V W (μ : Measure (Torus d)) x * (1 + t * h x)) =
        (μ : Measure (Torus d)).withDensity fun x => ENNReal.ofReal (1 + t * h x) := by
  set p := elDens V W (μ : Measure (Torus d)) with hp
  obtain ⟨hpm, hp0, hp1⟩ := elDensity_props hyp (μ : Measure (Torus d))
  have hμp : (μ : Measure (Torus d)) = densMeasure p := minimizer_eq_elDensity hyp hμ
  have hth : ∀ x, |t * h x| ≤ 1 / 2 := fun x => by
    rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (hb x) (abs_nonneg t)).trans ht
  have hpos : ∀ x, 0 < 1 + t * h x := fun x => by
    have := (abs_le.mp (hth x)).1; linarith
  refine ⟨fun x => mul_nonneg (hp0 x).le (hpos x).le, ?_, ?_⟩
  · have := integral_densMeasure' (fun x => (hp0 x).le) hp1 (fun x => 1 + t * h x)
    rw [← hμp] at this
    rw [← this]
    haveI : IsProbabilityMeasure (μ : Measure (Torus d)) := inferInstance
    have hi : Integrable h (μ : Measure (Torus d)) :=
      Integrable.of_bound hm.aestronglyMeasurable B
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)
    rw [integral_add (integrable_const _) (hi.const_mul t), integral_const_mul, hh0]
    simp
  · have hf : Measurable fun x => ENNReal.ofReal (p x) := ENNReal.measurable_ofReal.comp hpm
    have hg : Measurable fun x => ENNReal.ofReal (1 + t * h x) :=
      ENNReal.measurable_ofReal.comp (measurable_const.add (hm.const_mul t))
    have e : (fun x => ENNReal.ofReal (p x * (1 + t * h x))) =
        (fun x => ENNReal.ofReal (p x)) * fun x => ENNReal.ofReal (1 + t * h x) := by
      funext x
      simp only [Pi.mul_apply]
      rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ p x from (hp0 x).le)]
    conv_rhs => rw [hμp]
    unfold densMeasure
    rw [e, withDensity_mul _ hf hg]

/-- **`G(μ(1+th)) = ∫ klFun(1+th) dμ + (t²/2)⟨h, Th⟩`.** -/
theorem gap_pert_toReal {h : Torus d → ℝ} (hm : Measurable h) {B : ℝ} (hb : ∀ x, |h x| ≤ B)
    (hh0 : ∫ x, h x ∂(μ : Measure (Torus d)) = 0) {t : ℝ} (ht : |t| * B ≤ 1 / 2) :
    (gap V W (densMeasure fun x => elDens V W (μ : Measure (Torus d)) x * (1 + t * h x))).toReal =
      ∫ x, klFun (1 + t * h x) ∂(μ : Measure (Torus d)) +
        t ^ 2 / 2 * ∫ x, h x * Top W (μ : Measure (Torus d)) h x ∂(μ : Measure (Torus d)) := by
  set μm := (μ : Measure (Torus d))
  set p := elDens V W μm with hp
  obtain ⟨hpm, hp0, hp1⟩ := elDensity_props hyp μm
  have hμp : μm = densMeasure p := minimizer_eq_elDensity hyp hμ
  obtain ⟨h0, h1, hρw⟩ := pert_props hyp hμ hm hb hh0 ht
  haveI hρp := isProbabilityMeasure_densMeasure' h0 h1
  set ρ : ProbabilityMeasure (Torus d) := ⟨densMeasure fun x => p x * (1 + t * h x), hρp⟩
  have hgap := gap_eq_aux hyp hμ ρ
  have hth : ∀ x, |t * h x| ≤ 1 / 2 := fun x => by
    rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (hb x) (abs_nonneg t)).trans ht
  have hpos : ∀ x, 0 < 1 + t * h x := fun x => by
    have := (abs_le.mp (hth x)).1; linarith
  have hi : Integrable h μm :=
    Integrable.of_bound hm.aestronglyMeasurable B
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)
  have hmeas1 : Measurable fun x => 1 + t * h x := measurable_const.add (hm.const_mul t)
  -- integration against `ρ`
  have hintρ : ∀ F : Torus d → ℝ, ∫ x, F x ∂(ρ : Measure (Torus d)) =
      ∫ x, (1 + t * h x) * F x ∂μm := fun F => by
    show ∫ x, F x ∂(densMeasure _) = _
    rw [integral_densMeasure' h0 h1, hμp, integral_densMeasure' (fun x => (hp0 x).le) hp1]
    congr 1; funext x; ring
  -- the relative entropy
  have hint : Integrable (fun x => klFun (1 + t * h x)) μm := by
    refine Integrable.of_bound (continuous_klFun.measurable.comp hmeas1).aestronglyMeasurable 1
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg (hpos x).le)]
    refine (klFun_one_add_le (by linarith [(abs_le.mp (hth x)).1])).trans ?_
    have := hth x
    nlinarith [abs_nonneg (t * h x), sq_abs (t * h x)]
  have hkl : klDiv (ρ : Measure (Torus d)) μm = ENNReal.ofReal (∫ x, klFun (1 + t * h x) ∂μm) := by
    have hρ : (ρ : Measure (Torus d)) = μm.withDensity fun x => ENNReal.ofReal (1 + t * h x) := hρw
    have hm' : AEMeasurable (fun x => ENNReal.ofReal (1 + t * h x)) μm :=
      (ENNReal.measurable_ofReal.comp hmeas1).aemeasurable
    haveI : IsFiniteMeasure (μm.withDensity fun x => ENNReal.ofReal (1 + t * h x)) := by
      rw [← hρ]; infer_instance
    rw [hρ, klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous _ _)]
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun x => klFun_nonneg (hpos x).le)]
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_withDensity₀ μm hm'] with x hx
    rw [hx, ENNReal.toReal_ofReal (hpos x).le]
  -- the interaction
  have hL20 : MemL20 μm h := ⟨MemLp.of_bound hm.aestronglyMeasurable B
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x), hh0⟩
  obtain ⟨CT0, hCT⟩ := Top_W1inf hyp μm
  obtain ⟨hTb, hTL⟩ := hCT h hL20
  have hTm : Measurable (Top W μm h) := hTL.continuous.measurable
  have hTi : Integrable (Top W μm h) μm :=
    Integrable.of_bound hTm.aestronglyMeasurable _
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hTb x)
  have hhTi : Integrable (fun x => h x * Top W μm h x) μm := by
    refine Integrable.of_bound (hm.mul hTm).aestronglyMeasurable
      (B * (CT0 * Real.sqrt (∫ y, h y ^ 2 ∂μm))) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hb x) (hTb x) (abs_nonneg _) ((abs_nonneg _).trans (hb x))
  have hJ : Jfun W μm ρ = t ^ 2 / 2 * ∫ x, h x * Top W μm h x ∂μm := by
    have hK := continuous_centeredKernel hyp μm
    unfold Jfun interE
    have hin : ∀ y, ∫ x, centeredKernel W μm x y ∂(ρ : Measure (Torus d)) =
        t * Top W μm h y := fun y => by
      rw [hintρ, Top_eq_integral hyp μm hL20 y]
      have i1 : Integrable (fun x => centeredKernel W μm x y) μm :=
        integrable_of_continuous (cont_left hK y)
      obtain ⟨BK, hBK⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hK
      have i2 : Integrable (fun x => h x * centeredKernel W μm x y) μm :=
        Integrable.of_bound (hm.mul (cont_left hK y).measurable).aestronglyMeasurable (B * BK)
          (Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul (hb x) (hBK (x, y)) (abs_nonneg _) ((abs_nonneg _).trans (hb x)))
      have e : (fun x => (1 + t * h x) * centeredKernel W μm x y) =
          fun x => centeredKernel W μm x y + t * (h x * centeredKernel W μm x y) := by
        funext x; ring
      rw [e, integral_add i1 (i2.const_mul t), integral_const_mul]
      have h0' : ∫ x, centeredKernel W μm x y ∂μm = 0 := by
        simp_rw [centeredKernel_symm_coerc hyp μm _ y]; exact integral_centeredKernel hyp μm y
      rw [h0', zero_add]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show h x * centeredKernel W μm x y = centeredKernel W μm y x * h x
      rw [centeredKernel_symm_coerc hyp μm x y, mul_comm]
    simp_rw [hin]
    rw [hintρ]
    have e : (fun y => (1 + t * h y) * (t * Top W μm h y)) =
        fun y => t * Top W μm h y + t ^ 2 * (h y * Top W μm h y) := by funext y; ring
    rw [e, integral_add (hTi.const_mul t) (hhTi.const_mul _), integral_const_mul,
      integral_const_mul, integral_Top hyp μm hi]
    ring
  have hnn : 0 ≤ ∫ x, klFun (1 + t * h x) ∂μm := integral_nonneg fun x => klFun_nonneg (hpos x).le
  show (gap V W (ρ : Measure (Torus d))).toReal = _
  rw [hgap, hkl, EReal.coe_ennreal_ofReal, max_eq_left hnn, ← EReal.coe_add, EReal.toReal_coe, hJ]

/-- **The second variation**: `G(μ(1+th))/t² → ½⟨h,(I+T)h⟩` as `t → 0`. -/
theorem tendsto_gap_pert {h : Torus d → ℝ} (hm : Measurable h) (hb : ∃ B, ∀ x, |h x| ≤ B)
    (hh0 : ∫ x, h x ∂(μ : Measure (Torus d)) = 0) :
    Tendsto (fun t : ℝ => (gap V W (densMeasure fun x =>
        elDens V W (μ : Measure (Torus d)) x * (1 + t * h x))).toReal / t ^ 2)
      (𝓝[≠] 0) (𝓝 (secondVar W (μ : Measure (Torus d)) h / 2)) := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨B, hB⟩ := hb
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hi : Integrable h μm :=
    Integrable.of_bound hm.aestronglyMeasurable B
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
  have hL20 : MemL20 μm h := ⟨MemLp.of_bound hm.aestronglyMeasurable B
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x), hh0⟩
  obtain ⟨CT0, hCT⟩ := Top_W1inf hyp μm
  obtain ⟨hTb, hTL⟩ := hCT h hL20
  have hTm : Measurable (Top W μm h) := hTL.continuous.measurable
  have hhTi : Integrable (fun x => h x * Top W μm h x) μm := by
    refine Integrable.of_bound (hm.mul hTm).aestronglyMeasurable
      (B * (CT0 * Real.sqrt (∫ y, h y ^ 2 ∂μm))) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hB x) (hTb x) (abs_nonneg _) hB0
  have hh2 : Integrable (fun x => h x ^ 2) μm :=
    Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable (B ^ 2)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2)
  -- the target
  have hsv : secondVar W μm h / 2 = (1 / 2) * ∫ x, h x ^ 2 ∂μm +
      (1 / 2) * ∫ x, h x * Top W μm h x ∂μm := by
    unfold secondVar
    have e : (fun x => h x * (h x + Top W μm h x)) = fun x => h x ^ 2 + h x * Top W μm h x := by
      funext x; ring
    rw [e, integral_add hh2 hhTi]; ring
  rw [hsv]
  -- small `t`
  set δ : ℝ := 1 / (2 * B + 1)
  have hδ : 0 < δ := by positivity
  have hsmall : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 ∧ |t| * B ≤ 1 / 2 := by
    have h1 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ∈ Metric.ball (0 : ℝ) δ :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hδ)
    filter_upwards [h1, self_mem_nhdsWithin] with t ht ht0
    refine ⟨ht0, ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    have : |t| * (2 * B + 1) ≤ 1 := by
      have := mul_lt_mul_of_pos_right ht (by positivity : (0 : ℝ) < 2 * B + 1)
      rw [show δ * (2 * B + 1) = 1 from one_div_mul_cancel (by positivity)] at this
      exact this.le
    nlinarith [abs_nonneg t]
  -- the main estimate
  have hbound : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      |(gap V W (densMeasure fun x => elDens V W μm x * (1 + t * h x))).toReal / t ^ 2 -
        ((1 / 2) * ∫ x, h x ^ 2 ∂μm + (1 / 2) * ∫ x, h x * Top W μm h x ∂μm)| ≤
        4 * B ^ 3 * |t| := by
    filter_upwards [hsmall] with t ⟨ht0, ht⟩
    rw [gap_pert_toReal hyp hμ hm hB hh0 ht]
    have ht2 : 0 < t ^ 2 := by positivity
    have hth : ∀ x, |t * h x| ≤ 1 / 2 := fun x => by
      rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (hB x) (abs_nonneg t)).trans ht
    have hpos : ∀ x, 0 < 1 + t * h x := fun x => by
      have := (abs_le.mp (hth x)).1; linarith
    have hint : Integrable (fun x => klFun (1 + t * h x)) μm := by
      refine Integrable.of_bound
        (continuous_klFun.measurable.comp (measurable_const.add (hm.const_mul t))).aestronglyMeasurable
        1 (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg (hpos x).le)]
      refine (klFun_one_add_le (by linarith [(abs_le.mp (hth x)).1])).trans ?_
      have := hth x
      nlinarith [abs_nonneg (t * h x), sq_abs (t * h x)]
    have e : (∫ x, klFun (1 + t * h x) ∂μm + t ^ 2 / 2 * ∫ x, h x * Top W μm h x ∂μm) / t ^ 2 -
        ((1 / 2) * ∫ x, h x ^ 2 ∂μm + (1 / 2) * ∫ x, h x * Top W μm h x ∂μm) =
        (∫ x, (klFun (1 + t * h x) - (t * h x) ^ 2 / 2) ∂μm) / t ^ 2 := by
      rw [integral_sub hint (hh2.const_mul (t ^ 2 / 2) |>.congr
        (Eventually.of_forall fun x => by simp only; ring))]
      have : ∫ x, (t * h x) ^ 2 / 2 ∂μm = t ^ 2 / 2 * ∫ x, h x ^ 2 ∂μm := by
        rw [← integral_const_mul]; congr 1; funext x; ring
      rw [this]
      field_simp
      ring
    rw [e, abs_div, abs_of_pos ht2, div_le_iff₀ ht2]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ x, |klFun (1 + t * h x) - (t * h x) ^ 2 / 2| ∂μm ≤ ∫ _x, 4 * (|t| * B) ^ 3 ∂μm := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
            (integrable_const _) (Eventually.of_forall fun x => ?_)
          refine (abs_klFun_one_add_sub_le (hth x)).trans ?_
          have h1 : |t * h x| ≤ |t| * B := by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB x) (abs_nonneg t)
          have := pow_le_pow_left₀ (abs_nonneg _) h1 3
          linarith
      _ = 4 * (|t| * B) ^ 3 := by simp
      _ = 4 * B ^ 3 * |t| * t ^ 2 := by rw [mul_pow, ← sq_abs t]; ring
  -- conclude
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun t : ℝ => 4 * B ^ 3 * |t|)
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [hbound] with t ht
    rw [Real.norm_eq_abs]; exact ht
  · have : Tendsto (fun t : ℝ => 4 * B ^ 3 * |t|) (𝓝 0) (𝓝 (4 * B ^ 3 * |0|)) :=
      (continuous_const.mul continuous_abs).tendsto 0
    rw [abs_zero, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds

end pert

end SharpLSI
