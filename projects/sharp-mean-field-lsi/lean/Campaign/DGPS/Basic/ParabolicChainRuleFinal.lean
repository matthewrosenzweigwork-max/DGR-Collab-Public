import DGPS.Basic.ParabolicChainRule
import DGPS.Basic.ParabolicChainRuleTime
import DGPS.Foundations.WeakContractions
import DGPS.Foundations.SobolevCalculus

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff RealInnerProductSpace

namespace DGPS.Lipschitz

open DGPS DGPS.Lipschitz.ParabolicChainRule

variable {d : ℕ}

theorem lip026c_inner_eq (a b : Tangent d) : ⟪a, b⟫ = ∑ j, a j * b j := by
  simp [PiLp.inner_apply, mul_comm]

theorem lip026c_abs_heatOp_le {ε M : ℝ} (hε : 0 < ε) {f : Torus d → ℝ}
    (hf : ∀ᵐ x ∂haar d, |f x| ≤ M) (y : Torus d) : |heatOp ε f y| ≤ M := by
  have hM : 0 ≤ M := by
    obtain ⟨x, hx⟩ := hf.exists
    exact (abs_nonneg _).trans hx
  have hae : f =ᵐ[haar d] fun x => max (-M) (min (f x) M) := by
    filter_upwards [hf] with x hx
    have h1 := abs_le.1 hx
    rw [min_eq_left h1.2, max_eq_right h1.1]
  have h1 : heatOp ε f = heatOp ε (fun x => max (-M) (min (f x) M)) :=
    torusConv_congr_ae _ hae
  rw [h1]
  refine abs_torusConv_le (continuous_heatKernelT hε) (fun z => (heatKernelT_pos hε z).le)
    (integral_heatKernelT hε) (fun x => ?_) y
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

theorem lip026c_measurable_heatOp {ε : ℝ} (hε : 0 < ε) {f : ℝ → Torus d → ℝ}
    (hf : Measurable (fun p : ℝ × Torus d => f p.1 p.2)) :
    Measurable (fun p : ℝ × Torus d => heatOp ε (f p.1) p.2) := by
  have hK : Measurable (heatKernelT (d := d) ε) := (continuous_heatKernelT hε).measurable
  have h : Measurable (fun q : (ℝ × Torus d) × Torus d =>
      heatKernelT ε (q.1.2 - q.2) * f q.1.1 q.2) :=
    (hK.comp ((measurable_snd.comp measurable_fst).sub measurable_snd)).mul
      (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem lip026c_integral_sq_heatOp_le {ε : ℝ} (hε : 0 < ε) {f : Torus d → ℝ}
    (hf : MemLp f 2 (haar d)) :
    ∫ x, (heatOp ε f x) ^ 2 ∂haar d ≤ ∫ x, f x ^ 2 ∂haar d := by
  have hH := memLp_heatOp hε one_le_two (by simp) hf
  have h := eLpNorm_heatOp_le hε one_le_two (by simp) hf
  rw [hH.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp),
    hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)] at h
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at h
  have h0 : 0 ≤ ∫ x, (heatOp ε f x) ^ 2 ∂haar d := integral_nonneg fun x => sq_nonneg _
  have h0' : 0 ≤ ∫ x, f x ^ 2 ∂haar d := integral_nonneg fun x => sq_nonneg _
  rw [ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg h0' _)] at h
  exact (Real.rpow_le_rpow_iff h0 h0' (by norm_num)).1 h

theorem lip026c_integral_norm_sq_eq {g : Torus d → Tangent d} (hg : MemLp g 2 (haar d)) :
    ∫ x, ‖g x‖ ^ 2 ∂haar d = ∑ j, ∫ x, g x j ^ 2 ∂haar d := by
  simp_rw [tangent_norm_sq]
  exact integral_finsetSum _ fun j _ => (memLp_coord hg j).integrable_sq

theorem lip026c_integral_norm_sq_heatGrad_le {ε : ℝ} (hε : 0 < ε) {g : Torus d → Tangent d}
    (hg : MemLp g 2 (haar d)) :
    ∫ x, ‖heatGrad ε g x‖ ^ 2 ∂haar d ≤ ∫ x, ‖g x‖ ^ 2 ∂haar d := by
  rw [lip026c_integral_norm_sq_eq hg, lip026c_integral_norm_sq_eq (memLp_heatGrad hε hg)]
  exact Finset.sum_le_sum fun j _ => lip026c_integral_sq_heatOp_le hε (memLp_coord hg j)


/-! ### Hölder convergence of products along a filter -/

theorem lip026c_eLpNorm_mul_le {a b : Torus d → ℝ} (ha : MemLp a 2 (haar d))
    (hb : MemLp b 2 (haar d)) :
    eLpNorm (fun x => a x * b x) 1 (haar d)
      ≤ eLpNorm a 2 (haar d) * eLpNorm b 2 (haar d) :=
  DGPS.eLpNorm_mul_le_two ha hb

theorem lip026c_tendsto_eLpNorm_mul_sub {ι : Type*} {l : Filter ι} {P Q : ι → Torus d → ℝ}
    {p q : Torus d → ℝ}
    (hQ : ∀ᶠ i in l, MemLp (Q i) 2 (haar d)) (hP : ∀ᶠ i in l, MemLp (P i) 2 (haar d))
    (hp : MemLp p 2 (haar d)) (hq : MemLp q 2 (haar d))
    (hPc : Tendsto (fun i => eLpNorm (fun x => P i x - p x) 2 (haar d)) l (𝓝 0))
    (hQc : Tendsto (fun i => eLpNorm (fun x => Q i x - q x) 2 (haar d)) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (fun y => P i y * Q i y - p y * q y) 1 (haar d)) l (𝓝 0) := by
  have key : ∀ᶠ i in l, eLpNorm (fun y => P i y * Q i y - p y * q y) 1 (haar d) ≤
      eLpNorm (fun x => P i x - p x) 2 (haar d) *
        (eLpNorm q 2 (haar d) + eLpNorm (fun x => Q i x - q x) 2 (haar d))
      + eLpNorm p 2 (haar d) * eLpNorm (fun x => Q i x - q x) 2 (haar d) := by
    filter_upwards [hP, hQ] with i hPi hQi
    have hPp : MemLp (fun x => P i x - p x) 2 (haar d) := hPi.sub hp
    have hQq : MemLp (fun x => Q i x - q x) 2 (haar d) := hQi.sub hq
    have e : (fun y => P i y * Q i y - p y * q y)
        = (fun y => (P i y - p y) * Q i y) + (fun y => p y * (Q i y - q y)) := by
      funext y; simp only [Pi.add_apply]; ring
    rw [e]
    refine le_trans (eLpNorm_add_le le_rfl) ?_
    refine add_le_add ((lip026c_eLpNorm_mul_le hPp hQi).trans ?_)
      (lip026c_eLpNorm_mul_le hp hQq)
    gcongr
    have e2 : Q i = (fun x => q x) + (fun x => Q i x - q x) := by funext x; simp
    calc eLpNorm (Q i) 2 (haar d)
        = eLpNorm ((fun x => q x) + (fun x => Q i x - q x)) 2 (haar d) := by rw [← e2]
      _ ≤ _ := eLpNorm_add_le one_le_two
  have hb : Tendsto (fun i => eLpNorm q 2 (haar d) + eLpNorm (fun x => Q i x - q x) 2 (haar d))
      l (𝓝 (eLpNorm q 2 (haar d) + 0)) := tendsto_const_nhds.add hQc
  have h1 := ENNReal.Tendsto.mul hPc (Or.inr (by simpa using hq.eLpNorm_ne_top)) hb
    (Or.inr ENNReal.zero_ne_top)
  have h2 := ENNReal.Tendsto.const_mul hQc (Or.inr hp.eLpNorm_ne_top)
  have := h1.add h2
  simp only [zero_mul, mul_zero, add_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this
    (Eventually.of_forall fun n => zero_le) key

/-! ### Passage to the limit for continuous multipliers -/

theorem lip026c_tendsto_integral_comp_mul {a : ℝ → ℝ} (ha : Continuous a) {M : ℝ}
    {f : Torus d → ℝ} (hf : MemLp f 2 (haar d)) (hfM : ∀ᵐ x ∂haar d, |f x| ≤ M)
    {w : Torus d → ℝ} (hw : Integrable w (haar d)) :
    Tendsto (fun ε : ℝ => ∫ x, a (heatOp ε f x) * w x ∂haar d) (𝓝[>] 0)
      (𝓝 (∫ x, a (f x) * w x ∂haar d)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -M) (b := M)).exists_bound_of_continuousOn
    ha.continuousOn
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hpos : ∀ᶠ n in atTop, 0 < ns n := hns.eventually self_mem_nhdsWithin
  have hconv : Tendsto (fun n => eLpNorm (fun y => heatOp (ns n) f y - f y) 2 (haar d)) atTop
      (𝓝 0) := (tendsto_eLpNorm_two_heatOp_sub hf).comp hns
  have hmeas : TendstoInMeasure (haar d) (fun n => heatOp (ns n) f) atTop f :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hconv
  obtain ⟨ms, hms, hae⟩ := hmeas.exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hpos' : ∀ᶠ n in atTop, 0 < ns (ms n) := hms.tendsto_atTop.eventually hpos
  refine tendsto_integral_filter_of_dominated_convergence (fun x => C * ‖w x‖) ?_ ?_
    (hw.norm.const_mul C) ?_
  · filter_upwards [hpos'] with n hn
    exact (ha.comp (isC1Periodic_heatOp hn (hf.integrable one_le_two)).continuous_torus
      ).aestronglyMeasurable.mul hw.aestronglyMeasurable
  · filter_upwards [hpos'] with n hn
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right (hC _ ?_) (norm_nonneg _)
    exact abs_le.1 (lip026c_abs_heatOp_le hn hfM x)
  · filter_upwards [hae] with x hx
    exact (ha.continuousAt.tendsto.comp hx).mul_const _

theorem lip026c_integrable_comp_mul {a : ℝ → ℝ} (ha : Continuous a) {M : ℝ} {f : Torus d → ℝ}
    (hf : AEStronglyMeasurable f (haar d)) (hfM : ∀ᵐ x ∂haar d, |f x| ≤ M)
    {w : Torus d → ℝ} (hw : Integrable w (haar d)) :
    Integrable (fun x => a (f x) * w x) (haar d) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -M) (b := M)).exists_bound_of_continuousOn
    ha.continuousOn
  refine hw.bdd_mul (c := C) (ha.comp_aestronglyMeasurable hf) ?_
  filter_upwards [hfM] with x hx
  exact hC _ (abs_le.1 hx)

theorem lip026c_tendsto_comp_mul_prod {a : ℝ → ℝ} (ha : Continuous a) {M : ℝ}
    {f : Torus d → ℝ} (hf : MemLp f 2 (haar d)) (hfM : ∀ᵐ x ∂haar d, |f x| ≤ M)
    {p q : Torus d → ℝ} (hp : MemLp p 2 (haar d)) (hq : MemLp q 2 (haar d)) :
    Tendsto (fun ε : ℝ => ∫ x, a (heatOp ε f x) * (heatOp ε p x * heatOp ε q x) ∂haar d)
      (𝓝[>] 0) (𝓝 (∫ x, a (f x) * (p x * q x) ∂haar d)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -M) (b := M)).exists_bound_of_continuousOn
    ha.continuousOn
  have hpq : Integrable (fun x => p x * q x) (haar d) := hp.integrable_mul hq
  have hG := lip026c_tendsto_integral_comp_mul ha hf hfM hpq
  have hmem : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hD : Tendsto (fun ε : ℝ => eLpNorm (fun y => heatOp ε p y * heatOp ε q y - p y * q y) 1
      (haar d)) (𝓝[>] 0) (𝓝 0) :=
    lip026c_tendsto_eLpNorm_mul_sub (P := fun ε => heatOp ε p) (Q := fun ε => heatOp ε q)
      (by filter_upwards [hmem] with ε hε using memLp_heatOp hε one_le_two (by simp) hq)
      (by filter_upwards [hmem] with ε hε using memLp_heatOp hε one_le_two (by simp) hp)
      hp hq (tendsto_eLpNorm_two_heatOp_sub hp) (tendsto_eLpNorm_two_heatOp_sub hq)
  have hb : Tendsto (fun ε : ℝ => C * (eLpNorm (fun y => heatOp ε p y * heatOp ε q y - p y * q y)
      1 (haar d)).toReal) (𝓝[>] 0) (𝓝 0) := by
    have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hD).const_mul C
    simpa using this
  have hX : Tendsto (fun ε : ℝ => ∫ x, a (heatOp ε f x) * (heatOp ε p x * heatOp ε q x) ∂haar d
      - ∫ x, a (heatOp ε f x) * (p x * q x) ∂haar d) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hmem] with ε hε
    have hfe : ∀ x, |heatOp ε f x| ≤ M := lip026c_abs_heatOp_le hε hfM
    have hcont : AEStronglyMeasurable (heatOp ε f) (haar d) :=
      (isC1Periodic_heatOp hε (hf.integrable one_le_two)).continuous_torus.aestronglyMeasurable
    have hi1 : Integrable (fun x => a (heatOp ε f x) * (heatOp ε p x * heatOp ε q x)) (haar d) :=
      lip026c_integrable_comp_mul ha hcont (Eventually.of_forall hfe)
        ((memLp_heatOp hε one_le_two (by simp) hp).integrable_mul
          (memLp_heatOp hε one_le_two (by simp) hq))
    have hi2 : Integrable (fun x => a (heatOp ε f x) * (p x * q x)) (haar d) :=
      lip026c_integrable_comp_mul ha hcont (Eventually.of_forall hfe) hpq
    have hD1 : Integrable (fun y => heatOp ε p y * heatOp ε q y - p y * q y) (haar d) :=
      ((memLp_heatOp hε one_le_two (by simp) hp).integrable_mul
          (memLp_heatOp hε one_le_two (by simp) hq)).sub hpq
    rw [← integral_sub hi1 hi2]
    have e : (fun x => a (heatOp ε f x) * (heatOp ε p x * heatOp ε q x)
        - a (heatOp ε f x) * (p x * q x)) =
        fun x => a (heatOp ε f x) * (heatOp ε p x * heatOp ε q x - p x * q x) := by
      funext x; ring
    simp_rw [e]
    calc ‖∫ x, a (heatOp ε f x) * (heatOp ε p x * heatOp ε q x - p x * q x) ∂haar d‖
        ≤ ∫ x, C * ‖heatOp ε p x * heatOp ε q x - p x * q x‖ ∂haar d := by
          refine norm_integral_le_of_norm_le (hD1.norm.const_mul C) (Eventually.of_forall fun x => ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hC _ (abs_le.1 (hfe x))) (norm_nonneg _)
      _ = C * ∫ x, ‖heatOp ε p x * heatOp ε q x - p x * q x‖ ∂haar d := integral_const_mul _ _
      _ = C * (eLpNorm (fun y => heatOp ε p y * heatOp ε q y - p y * q y) 1 (haar d)).toReal := by
          rw [integral_norm_eq_lintegral_enorm hD1.aestronglyMeasurable,
            eLpNorm_one_eq_lintegral_enorm hD1.aestronglyMeasurable]
  have := hX.add hG
  simp only [zero_add, sub_add_cancel] at this
  exact this

theorem lip026c_inner_heatGrad (ε : ℝ) (g V : Torus d → Tangent d) (x : Torus d) :
    ⟪heatGrad ε g x, heatGrad ε V x⟫ =
      ∑ j, heatOp ε (fun z => g z j) x * heatOp ε (fun z => V z j) x := by
  rw [lip026c_inner_eq]; rfl

/-- **Slice convergence.**  The regularised integrand converges to the unregularised one. -/
theorem lip026c_tendsto_slice {a : ℝ → ℝ} (ha : Continuous a) {M : ℝ}
    {f : Torus d → ℝ} (hf : MemLp f 2 (haar d)) (hfM : ∀ᵐ x ∂haar d, |f x| ≤ M)
    {g V : Torus d → Tangent d} (hg : MemLp g 2 (haar d)) (hV : MemLp V 2 (haar d)) :
    Tendsto (fun ε : ℝ => ∫ x, a (heatOp ε f x) * ⟪heatGrad ε g x, heatGrad ε V x⟫ ∂haar d)
      (𝓝[>] 0) (𝓝 (∫ x, a (f x) * ⟪g x, V x⟫ ∂haar d)) := by
  have hmem : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hlim : ∫ x, a (f x) * ⟪g x, V x⟫ ∂haar d =
      ∑ j, ∫ x, a (f x) * (g x j * V x j) ∂haar d := by
    simp_rw [lip026c_inner_eq, Finset.mul_sum]
    exact integral_finsetSum _ fun j _ => lip026c_integrable_comp_mul ha hf.aestronglyMeasurable hfM
      ((memLp_coord hg j).integrable_mul (memLp_coord hV j))
  rw [hlim]
  refine Tendsto.congr' ?_ (tendsto_finsetSum _ fun j _ =>
    lip026c_tendsto_comp_mul_prod ha hf hfM (memLp_coord hg j) (memLp_coord hV j))
  filter_upwards [hmem] with ε hε
  have hfe : ∀ x, |heatOp ε f x| ≤ M := lip026c_abs_heatOp_le hε hfM
  have hcont : AEStronglyMeasurable (heatOp ε f) (haar d) :=
    (isC1Periodic_heatOp hε (hf.integrable one_le_two)).continuous_torus.aestronglyMeasurable
  symm
  simp_rw [lip026c_inner_heatGrad, Finset.mul_sum]
  exact integral_finsetSum _ fun j _ => lip026c_integrable_comp_mul ha hcont
    (Eventually.of_forall hfe)
    ((memLp_heatOp hε one_le_two (by simp) (memLp_coord hg j)).integrable_mul
      (memLp_heatOp hε one_le_two (by simp) (memLp_coord hV j)))

/-! ### The slice bound and the structure of hypotheses -/

theorem lip026c_slice_bound {ε : ℝ} (hε : 0 < ε) {a : ℝ → ℝ} {A M : ℝ} (hA : 0 ≤ A)
    (haA : ∀ y, |y| ≤ M → |a y| ≤ A) {f : Torus d → ℝ} (hfM : ∀ᵐ x ∂haar d, |f x| ≤ M)
    {g V : Torus d → Tangent d} (hg : MemLp g 2 (haar d)) (hV : MemLp V 2 (haar d)) :
    |∫ x, a (heatOp ε f x) * ⟪heatGrad ε g x, heatGrad ε V x⟫ ∂haar d| ≤
      A / 2 * (∫ x, ‖g x‖ ^ 2 ∂haar d + ∫ x, ‖V x‖ ^ 2 ∂haar d) := by
  have hGm := memLp_heatGrad hε hg
  have hWm := memLp_heatGrad hε hV
  have hGi : Integrable (fun x => ‖heatGrad ε g x‖ ^ 2) (haar d) :=
    (memLp_two_iff_integrable_sq_norm hGm.aestronglyMeasurable).1 hGm
  have hWi : Integrable (fun x => ‖heatGrad ε V x‖ ^ 2) (haar d) :=
    (memLp_two_iff_integrable_sq_norm hWm.aestronglyMeasurable).1 hWm
  have hb : Integrable (fun x => A / 2 * (‖heatGrad ε g x‖ ^ 2 + ‖heatGrad ε V x‖ ^ 2))
      (haar d) := (hGi.add hWi).const_mul _
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun x => ?_)).trans ?_
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := haA _ (lip026c_abs_heatOp_le hε hfM x)
    have h2 : |⟪heatGrad ε g x, heatGrad ε V x⟫| ≤ ‖heatGrad ε g x‖ * ‖heatGrad ε V x‖ :=
      abs_real_inner_le_norm _ _
    calc |a (heatOp ε f x)| * |⟪heatGrad ε g x, heatGrad ε V x⟫|
        ≤ A * (‖heatGrad ε g x‖ * ‖heatGrad ε V x‖) :=
          mul_le_mul h1 h2 (abs_nonneg _) hA
      _ ≤ _ := by nlinarith [sq_nonneg (‖heatGrad ε g x‖ - ‖heatGrad ε V x‖)]
  · rw [integral_const_mul, integral_add hGi hWi]
    exact mul_le_mul_of_nonneg_left (add_le_add (lip026c_integral_norm_sq_heatGrad_le hε hg)
      (lip026c_integral_norm_sq_heatGrad_le hε hV)) (by positivity)

/-- The standing hypotheses on the data `(u, ∇u, J)`. -/
structure lip026c_Setting (T : ℝ) (u : ℝ → Torus d → ℝ) (g J : ℝ → Torus d → Tangent d) :
    Prop where
  div : IsWeakTimeDivergence T u J
  bdd : ∃ M : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂haar d, |u t x| ≤ M
  grad : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), IsWeakGradient (u r) (g r)
  meas_g : Measurable (fun p : ℝ × Torus d => g p.1 p.2)
  int_g : Integrable (fun p : ℝ × Torus d => ‖g p.1 p.2‖ ^ 2)
    ((volume.restrict (Icc (0 : ℝ) T)).prod (haar d))
  int_J : Integrable (fun p : ℝ × Torus d => ‖J p.1 p.2‖ ^ 2)
    ((volume.restrict (Icc (0 : ℝ) T)).prod (haar d))

theorem lip026c_measurable_inner_heatGrad {ε : ℝ} (hε : 0 < ε) {g J : ℝ → Torus d → Tangent d}
    (hg : Measurable (fun p : ℝ × Torus d => g p.1 p.2))
    (hJ : Measurable (fun p : ℝ × Torus d => J p.1 p.2)) :
    Measurable (fun p : ℝ × Torus d => ⟪heatGrad ε (g p.1) p.2, heatGrad ε (J p.1) p.2⟫) := by
  have e : (fun p : ℝ × Torus d => ⟪heatGrad ε (g p.1) p.2, heatGrad ε (J p.1) p.2⟫) =
      fun p => ∑ j, heatOp ε (fun z => g p.1 z j) p.2 * heatOp ε (fun z => J p.1 z j) p.2 :=
    funext fun p => lip026c_inner_heatGrad ε (g p.1) (J p.1) p.2
  rw [e]
  refine Finset.measurable_sum _ fun j _ => ?_
  have hproj : Measurable (fun v : Tangent d => v j) :=
    (EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).continuous.measurable
  exact (lip026c_measurable_heatOp hε (f := fun r z => g r z j) (hproj.comp hg)).mul
    (lip026c_measurable_heatOp hε (f := fun r z => J r z j) (hproj.comp hJ))

/-! ### Part A: the C² chain rule -/

theorem lip026c_reg_identity {T : ℝ} {u : ℝ → Torus d → ℝ} {g J : ℝ → Torus d → Tangent d}
    (S : lip026c_Setting T u g J) {ε : ℝ} (hε : 0 < ε) {H : ℝ → ℝ} (hH : ContDiff ℝ 2 H)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    ∫ x, H (heatOp ε (u t) x) ∂haar d - ∫ x, H (heatOp ε (u s) x) ∂haar d =
      -∫ r in s..t, ∫ x, deriv (deriv H) (heatOp ε (u r) x) *
          ⟪heatGrad ε (g r) x, heatGrad ε (J r) x⟫ ∂haar d := by
  rw [heatOp_chain_rule_integrated hε S.div hH hs hst ht]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  have hgr := (ae_restrict_iff' measurableSet_Icc).1 S.grad
  filter_upwards [hgr] with r hr hrI
  rw [Set.uIoc_of_le hst] at hrI
  have hw := hr ⟨hs.trans hrI.1.le, hrI.2.trans ht⟩
  have h1 : IsWeakGradient (heatOp ε (u r)) (heatOpGrad ε (u r)) :=
    (heatOp_isWeakGradient_of_memL2 hε hw.memLp).2.1
  have h2 := IsWeakGradient.heatOp hε hw
  have h3 := h1.ae_eq h2
  refine integral_congr_ae ?_
  filter_upwards [h3] with x hx
  rw [hx]

theorem lip026c_aesm_Phi {T : ℝ} {u : ℝ → Torus d → ℝ} {g J : ℝ → Torus d → Tangent d}
    (S : lip026c_Setting T u g J) {ε : ℝ} (hε : 0 < ε) {a : ℝ → ℝ} (ha : Continuous a)
    (hT : 0 ≤ T) :
    AEStronglyMeasurable (fun r => ∫ x, a (heatOp ε (u r) x) *
      ⟪heatGrad ε (g r) x, heatGrad ε (J r) x⟫ ∂haar d) (volume.restrict (Icc (0 : ℝ) T)) := by
  have hU := lip026b_measurable_U hε hT S.div
  have hΘ : Measurable (fun p : ℝ × Torus d => a (heatOp ε (u (lip026b_clamp T p.1)) p.2) *
      ⟪heatGrad ε (g p.1) p.2, heatGrad ε (J p.1) p.2⟫) :=
    (ha.measurable.comp hU).mul
      (lip026c_measurable_inner_heatGrad hε S.meas_g S.div.measurable_J)
  have h1 := hΘ.stronglyMeasurable.integral_prod_right' (ν := haar d)
  refine h1.aestronglyMeasurable.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  simp only [lip026b_clamp_of_mem hr]

theorem lip026c_tendsto_int_Phi {T : ℝ} {u : ℝ → Torus d → ℝ} {g J : ℝ → Torus d → Tangent d}
    (S : lip026c_Setting T u g J) {a : ℝ → ℝ} (ha : Continuous a) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t ≤ T) :
    Tendsto (fun ε : ℝ => ∫ r in s..t, ∫ x, a (heatOp ε (u r) x) *
      ⟪heatGrad ε (g r) x, heatGrad ε (J r) x⟫ ∂haar d) (𝓝[>] 0)
      (𝓝 (∫ r in s..t, ∫ x, a (u r x) * ⟪g r x, J r x⟫ ∂haar d)) := by
  have hT : 0 ≤ T := hs.trans (hst.trans ht)
  obtain ⟨M, hM⟩ := S.bdd
  obtain ⟨A0, hA0⟩ := (isCompact_Icc (a := -M) (b := M)).exists_bound_of_continuousOn
    ha.continuousOn
  have hA : 0 ≤ max A0 0 := le_max_right _ _
  have haA : ∀ y, |y| ≤ M → |a y| ≤ max A0 0 := fun y hy => by
    have := hA0 y (abs_le.1 hy)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  set A := max A0 0 with hAdef
  have hsub : Ioc s t ⊆ Icc 0 T := fun r hr => ⟨hs.trans hr.1.le, hr.2.trans ht⟩
  have hJ2 : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), MemLp (J r) 2 (haar d) := by
    filter_upwards [S.int_J.prod_right_ae] with r hr
    exact (memLp_two_iff_integrable_sq_norm
      (lip026b_measurable_slice S.div.measurable_J r).aestronglyMeasurable).2 hr
  have hfacts : ∀ᵐ r ∂(volume.restrict (Ioc s t)),
      IsWeakGradient (u r) (g r) ∧ MemLp (J r) 2 (haar d) ∧ r ∈ Icc (0 : ℝ) T := by
    have h1 := ae_restrict_of_ae_restrict_of_subset hsub (S.grad.and hJ2)
    filter_upwards [h1, ae_restrict_mem measurableSet_Ioc] with r hr hrm
    exact ⟨hr.1, hr.2, hsub hrm⟩
  have hfacts' := (ae_restrict_iff' measurableSet_Ioc).1 hfacts
  have hGi : Integrable (fun r => ∫ x, ‖g r x‖ ^ 2 ∂haar d)
      (volume.restrict (Icc (0 : ℝ) T)) := S.int_g.integral_prod_left
  have hKi : Integrable (fun r => ∫ x, ‖J r x‖ ^ 2 ∂haar d)
      (volume.restrict (Icc (0 : ℝ) T)) := S.int_J.integral_prod_left
  have hbint : IntervalIntegrable (fun r => A / 2 * (∫ x, ‖g r x‖ ^ 2 ∂haar d +
      ∫ x, ‖J r x‖ ^ 2 ∂haar d)) volume s t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
    exact ((hGi.add hKi).const_mul _).mono_measure (Measure.restrict_mono hsub le_rfl)
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hbint ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [Set.uIoc_of_le hst]
    exact (lip026c_aesm_Phi S hε ha hT).mono_measure (Measure.restrict_mono hsub le_rfl)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [hfacts'] with r hr hrI
    rw [Set.uIoc_of_le hst] at hrI
    obtain ⟨hw, hJr, hrT⟩ := hr hrI
    rw [Real.norm_eq_abs]
    exact lip026c_slice_bound hε hA haA (hM r hrT) hw.memLp_grad hJr
  · filter_upwards [hfacts'] with r hr hrI
    rw [Set.uIoc_of_le hst] at hrI
    obtain ⟨hw, hJr, hrT⟩ := hr hrI
    exact lip026c_tendsto_slice ha hw.memLp (hM r hrT) hw.memLp_grad hJr

theorem lip026c_memLp_slice {T : ℝ} {u : ℝ → Torus d → ℝ} {g J : ℝ → Torus d → Tangent d}
    (S : lip026c_Setting T u g J) {M : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂haar d, |u t x| ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : MemLp (u t) 2 (haar d) :=
  MemLp.of_bound (S.div.integrable_u t ht).aestronglyMeasurable M
    ((hM t ht).mono fun x hx => by rwa [Real.norm_eq_abs])

theorem lip026c_chain_rule_C2 {T : ℝ} {u : ℝ → Torus d → ℝ} {g J : ℝ → Torus d → Tangent d}
    (S : lip026c_Setting T u g J) {H : ℝ → ℝ} (hH : ContDiff ℝ 2 H)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    ∫ x, H (u t x) ∂haar d - ∫ x, H (u s x) ∂haar d =
      -∫ r in s..t, ∫ x, deriv (deriv H) (u r x) * ⟪g r x, J r x⟫ ∂haar d := by
  obtain ⟨M, hM⟩ := S.bdd
  have hHc : Continuous H := hH.continuous
  have hH2 : Continuous (deriv (deriv H)) :=
    (lip026b_deriv_contDiff hH).continuous_deriv le_rfl
  have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs, hst.trans ht⟩
  have htI : t ∈ Icc (0 : ℝ) T := ⟨hs.trans hst, ht⟩
  have hL : ∀ r ∈ Icc (0 : ℝ) T, Tendsto (fun ε : ℝ => ∫ x, H (heatOp ε (u r) x) ∂haar d)
      (𝓝[>] 0) (𝓝 (∫ x, H (u r x) ∂haar d)) := fun r hr => by
    have := lip026c_tendsto_integral_comp_mul hHc (lip026c_memLp_slice S hM hr) (hM r hr)
      (w := fun _ => (1 : ℝ)) (integrable_const _)
    simpa using this
  have hR := (lip026c_tendsto_int_Phi S hH2 hs hst ht).neg
  have hlim := ((hL t htI).sub (hL s hsI))
  refine tendsto_nhds_unique hlim (hR.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (lip026c_reg_identity S hε hH hs hst ht).symm

/-! ### Smooth approximants of the negative-part energy -/

noncomputable def lip026c_S (δ y : ℝ) : ℝ := Real.sqrt (y ^ 2 + δ ^ 2)

noncomputable def lip026c_hd (δ y : ℝ) : ℝ := ((lip026c_S δ y - y) / 2) ^ 2 / 2

noncomputable def lip026c_hd2 (δ y : ℝ) : ℝ :=
  ((y / lip026c_S δ y - 1) / 2) ^ 2 + (lip026c_S δ y - y) / 2 * (δ ^ 2 / (2 * lip026c_S δ y ^ 3))

theorem lip026c_S_pos {δ : ℝ} (hδ : 0 < δ) (y : ℝ) : 0 < lip026c_S δ y :=
  Real.sqrt_pos.2 (by positivity)

theorem lip026c_S_sq {δ : ℝ} (y : ℝ) : lip026c_S δ y ^ 2 = y ^ 2 + δ ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem lip026c_hasDerivAt_S {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    HasDerivAt (lip026c_S δ) (y / lip026c_S δ y) y := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + δ ^ 2) (2 * y) y := by
    simpa using ((hasDerivAt_id y).pow 2).add_const (δ ^ 2)
  have h2 : HasDerivAt (lip026c_S δ) (2 * y / (2 * lip026c_S δ y)) y := h1.sqrt (by positivity)
  refine h2.congr_deriv ?_
  rw [mul_div_mul_left _ _ two_ne_zero]

theorem lip026c_hasDerivAt_ratio {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    HasDerivAt (fun y => y / lip026c_S δ y) (δ ^ 2 / lip026c_S δ y ^ 3) y := by
  have h := (hasDerivAt_id' y).div (lip026c_hasDerivAt_S hδ y) (lip026c_S_pos hδ y).ne'
  refine h.congr_deriv ?_
  have hp := lip026c_S_pos hδ y
  have hsq := lip026c_S_sq (δ := δ) y
  field_simp
  nlinarith [hsq]

theorem lip026c_hasDerivAt_hd {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    HasDerivAt (lip026c_hd δ) (((lip026c_S δ y - y) / 2) * ((y / lip026c_S δ y - 1) / 2)) y := by
  have hq : HasDerivAt (fun y => (lip026c_S δ y - y) / 2) ((y / lip026c_S δ y - 1) / 2) y :=
    ((lip026c_hasDerivAt_S hδ y).sub (hasDerivAt_id y)).div_const 2 |>.congr_deriv (by simp)
  have := (hq.pow 2).div_const 2
  unfold lip026c_hd
  convert this using 1
  ring

theorem lip026c_deriv_hd {δ : ℝ} (hδ : 0 < δ) :
    deriv (lip026c_hd δ) = fun y => ((lip026c_S δ y - y) / 2) * ((y / lip026c_S δ y - 1) / 2) :=
  funext fun y => (lip026c_hasDerivAt_hd hδ y).deriv

theorem lip026c_hasDerivAt_dhd {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    HasDerivAt (deriv (lip026c_hd δ)) (lip026c_hd2 δ y) y := by
  rw [lip026c_deriv_hd hδ]
  have hq : HasDerivAt (fun y => (lip026c_S δ y - y) / 2) ((y / lip026c_S δ y - 1) / 2) y :=
    ((lip026c_hasDerivAt_S hδ y).sub (hasDerivAt_id y)).div_const 2 |>.congr_deriv (by simp)
  have hq' : HasDerivAt (fun y => (y / lip026c_S δ y - 1) / 2) (δ ^ 2 / lip026c_S δ y ^ 3 / 2) y :=
    ((lip026c_hasDerivAt_ratio hδ y).sub_const 1).div_const 2
  have := hq.mul hq'
  unfold lip026c_hd2
  convert this using 1
  ring

theorem lip026c_contDiff_S {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ ∞ (lip026c_S δ) := by
  unfold lip026c_S
  exact (((contDiff_id.pow 2).add contDiff_const).sqrt (fun y => by positivity))

theorem lip026c_contDiff_hd {δ : ℝ} (hδ : 0 < δ) {n : ℕ∞} : ContDiff ℝ n (lip026c_hd δ) := by
  unfold lip026c_hd
  exact ((((lip026c_contDiff_S hδ).of_le (by exact_mod_cast le_top)).sub contDiff_id).div_const 2 |>.pow 2).div_const 2


theorem lip026c_abs_le_S {δ : ℝ} (y : ℝ) : |y| ≤ lip026c_S δ y := by
  unfold lip026c_S
  exact Real.abs_le_sqrt (by nlinarith [sq_nonneg δ])

theorem lip026c_S_le {δ : ℝ} (hδ : 0 < δ) (y : ℝ) : lip026c_S δ y ≤ |y| + δ := by
  unfold lip026c_S
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  nlinarith [sq_abs y, abs_nonneg y]

theorem lip026c_hd2_bound {δ : ℝ} (hδ : 0 < δ) (y : ℝ) : 0 ≤ lip026c_hd2 δ y ∧
    lip026c_hd2 δ y ≤ 3 / 2 := by
  have hp := lip026c_S_pos hδ y
  have hsq := lip026c_S_sq (δ := δ) y
  have hy := lip026c_abs_le_S (δ := δ) y
  have hm1 : y / lip026c_S δ y ≤ 1 := by
    rw [div_le_one hp]; exact (le_abs_self y).trans hy
  have hm2 : -1 ≤ y / lip026c_S δ y := by
    rw [le_div_iff₀ hp]; linarith [neg_abs_le y]
  have hSy : 0 ≤ lip026c_S δ y - y := by linarith [le_abs_self y]
  have hSy2 : lip026c_S δ y - y ≤ 2 * lip026c_S δ y := by linarith [neg_abs_le y]
  have hδS : δ ^ 2 ≤ lip026c_S δ y ^ 2 := by nlinarith [sq_nonneg y]
  have h3 : 0 < lip026c_S δ y ^ 3 := by positivity
  unfold lip026c_hd2
  have t1 : 0 ≤ ((y / lip026c_S δ y - 1) / 2) ^ 2 := sq_nonneg _
  have t1' : ((y / lip026c_S δ y - 1) / 2) ^ 2 ≤ 1 := by nlinarith
  have t2 : 0 ≤ (lip026c_S δ y - y) / 2 * (δ ^ 2 / (2 * lip026c_S δ y ^ 3)) := by positivity
  have t2' : (lip026c_S δ y - y) / 2 * (δ ^ 2 / (2 * lip026c_S δ y ^ 3)) ≤ 1 / 2 := by
    have : δ ^ 2 / (2 * lip026c_S δ y ^ 3) ≤ 1 / (2 * lip026c_S δ y) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hδS, hp]
    calc (lip026c_S δ y - y) / 2 * (δ ^ 2 / (2 * lip026c_S δ y ^ 3))
        ≤ (2 * lip026c_S δ y) / 2 * (1 / (2 * lip026c_S δ y)) := by
          apply mul_le_mul (by linarith) this (by positivity) (by positivity)
      _ = 1 / 2 := by field_simp
  constructor <;> linarith

theorem lip026c_continuous_hd2 {δ : ℝ} (hδ : 0 < δ) : Continuous (lip026c_hd2 δ) := by
  have hS : Continuous (lip026c_S δ) := (lip026c_contDiff_S hδ).continuous
  have hne : ∀ y, lip026c_S δ y ≠ 0 := fun y => (lip026c_S_pos hδ y).ne'
  unfold lip026c_hd2
  refine Continuous.add ?_ ?_
  · exact (((continuous_id.div hS hne).sub continuous_const).div_const 2).pow 2
  · exact ((hS.sub continuous_id).div_const 2).mul
      (continuous_const.div ((continuous_const.mul (hS.pow 3))) fun y => by
        have := lip026c_S_pos hδ y; positivity)

theorem lip026c_tendsto_hd2 {y : ℝ} (hy : y ≠ 0) :
    Tendsto (fun δ : ℝ => lip026c_hd2 δ y) (𝓝[>] 0) (𝓝 (if y < 0 then 1 else 0)) := by
  have hS : Tendsto (fun δ : ℝ => lip026c_S δ y) (𝓝 0) (𝓝 |y|) := by
    have : Continuous (fun δ : ℝ => lip026c_S δ y) := by
      unfold lip026c_S; fun_prop
    have h := this.tendsto 0
    simpa [lip026c_S, Real.sqrt_sq_eq_abs] using h
  have hya : |y| ≠ 0 := abs_ne_zero.2 hy
  have hd : Tendsto (fun δ : ℝ => δ ^ 2 / (2 * lip026c_S δ y ^ 3)) (𝓝 0) (𝓝 0) := by
    have h1 : Tendsto (fun δ : ℝ => δ ^ 2) (𝓝 0) (𝓝 0) := by
      have : Continuous (fun δ : ℝ => δ ^ 2) := by fun_prop
      simpa using this.tendsto (0 : ℝ)
    have := Tendsto.div h1 ((hS.pow 3).const_mul 2) (by simp [hya])
    rw [zero_div] at this
    exact this
  have hr : Tendsto (fun δ : ℝ => y / lip026c_S δ y) (𝓝 0) (𝓝 (y / |y|)) :=
    tendsto_const_nhds.div hS hya
  have hall : Tendsto (fun δ : ℝ => lip026c_hd2 δ y) (𝓝 0)
      (𝓝 (((y / |y| - 1) / 2) ^ 2 + (|y| - y) / 2 * 0)) := by
    unfold lip026c_hd2
    exact (((hr.sub_const 1).div_const 2).pow 2).add (((hS.sub_const y).div_const 2).mul hd)
  have hlim : ((y / |y| - 1) / 2) ^ 2 + (|y| - y) / 2 * 0 = if y < 0 then 1 else 0 := by
    rcases lt_or_gt_of_ne hy with h | h
    · rw [abs_of_neg h]
      simp only [h, ite_true]
      have : y / -y = -1 := by field_simp
      rw [this]; norm_num
    · rw [abs_of_pos h]
      simp only [not_lt.2 h.le, ite_false]
      have : y / y = 1 := by field_simp
      rw [this]; norm_num
  rw [← hlim]
  exact hall.mono_left nhdsWithin_le_nhds


theorem lip026c_hd_sub_le {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    |lip026c_hd δ y - (min y 0) ^ 2 / 2| ≤ δ * (|y| + δ) := by
  have h1 := lip026c_abs_le_S (δ := δ) y
  have h2 := lip026c_S_le hδ y
  unfold lip026c_hd
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy] at h1 h2 ⊢
    rw [min_eq_right hy]
    have hq0 : 0 ≤ (lip026c_S δ y - y) / 2 := by linarith
    have hq1 : (lip026c_S δ y - y) / 2 ≤ δ / 2 := by linarith
    rw [abs_of_nonneg (by nlinarith [sq_nonneg ((lip026c_S δ y - y) / 2)])]
    nlinarith
  · rw [abs_of_neg hy] at h1 h2 ⊢
    rw [min_eq_left hy.le]
    have hq0 : 0 ≤ (lip026c_S δ y - y) / 2 + y := by linarith
    have hq1 : (lip026c_S δ y - y) / 2 + y ≤ δ / 2 := by linarith
    have : ((lip026c_S δ y - y) / 2) ^ 2 / 2 - y ^ 2 / 2 =
        ((lip026c_S δ y - y) / 2 + y) * ((lip026c_S δ y - y) / 2 - y) / 2 := by ring
    rw [this, abs_of_nonneg (by nlinarith)]
    nlinarith

theorem lip026c_hd_le {δ : ℝ} (hδ : 0 < δ) (y : ℝ) : |lip026c_hd δ y| ≤ (|y| + δ) ^ 2 / 2 := by
  have h1 := lip026c_abs_le_S (δ := δ) y
  have h2 := lip026c_S_le hδ y
  unfold lip026c_hd
  have hq0 : 0 ≤ (lip026c_S δ y - y) / 2 := by linarith [le_abs_self y]
  have hq1 : (lip026c_S δ y - y) / 2 ≤ |y| + δ := by linarith [neg_abs_le y]
  rw [abs_of_nonneg (by positivity)]
  nlinarith [abs_nonneg y]

theorem lip026c_tendsto_hd (y : ℝ) :
    Tendsto (fun δ : ℝ => lip026c_hd δ y) (𝓝[>] 0) (𝓝 ((min y 0) ^ 2 / 2)) := by
  have hb : Tendsto (fun δ : ℝ => δ * (|y| + δ)) (𝓝[>] 0) (𝓝 0) := by
    have : Continuous (fun δ : ℝ => δ * (|y| + δ)) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [Real.norm_eq_abs]
  exact lip026c_hd_sub_le hδ y

/-! ### Slice and time limits for the approximants -/

theorem lip026c_ae_slice {T : ℝ} {u : ℝ → Torus d → ℝ} {g J : ℝ → Torus d → Tangent d}
    (S : lip026c_Setting T u g J) :
    ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)),
      IsWeakGradient (u r) (g r) ∧ MemLp (J r) 2 (haar d) := by
  have hJ2 : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), MemLp (J r) 2 (haar d) := by
    filter_upwards [S.int_J.prod_right_ae] with r hr
    exact (memLp_two_iff_integrable_sq_norm
      (lip026b_measurable_slice S.div.measurable_J r).aestronglyMeasurable).2 hr
  exact S.grad.and hJ2

theorem lip026c_aesm_limit {T : ℝ} {u : ℝ → Torus d → ℝ} {g J : ℝ → Torus d → Tangent d}
    (S : lip026c_Setting T u g J) {a : ℝ → ℝ} (ha : Continuous a) (hT : 0 ≤ T) :
    AEStronglyMeasurable (fun r => ∫ x, a (u r x) * ⟪g r x, J r x⟫ ∂haar d)
      (volume.restrict (Icc (0 : ℝ) T)) := by
  obtain ⟨M, hM⟩ := S.bdd
  have hseq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity⟩
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun n : ℕ => fun r => ∫ x, a (heatOp (1 / ((n : ℝ) + 1)) (u r) x) *
      ⟪heatGrad (1 / ((n : ℝ) + 1)) (g r) x, heatGrad (1 / ((n : ℝ) + 1)) (J r) x⟫ ∂haar d)
    (fun n => lip026c_aesm_Phi S (by positivity) ha hT) ?_
  filter_upwards [lip026c_ae_slice S, ae_restrict_mem measurableSet_Icc] with r hr hrT
  exact (lip026c_tendsto_slice ha hr.1.memLp (hM r hrT) hr.1.memLp_grad hr.2).comp hseq

theorem lip026c_tendsto_slice_neg {f : Torus d → ℝ} {g V : Torus d → Tangent d}
    (hw : IsWeakGradient f g) (hV : MemLp V 2 (haar d)) :
    Tendsto (fun δ : ℝ => ∫ x, lip026c_hd2 δ (f x) * ⟪g x, V x⟫ ∂haar d) (𝓝[>] 0)
      (𝓝 (∫ x, (if f x < 0 then ⟪g x, V x⟫ else 0) ∂haar d)) := by
  have hgV : Integrable (fun x => ‖g x‖ * ‖V x‖) (haar d) :=
    hw.memLp_grad.norm.integrable_mul hV.norm
  refine tendsto_integral_filter_of_dominated_convergence (fun x => 3 / 2 * (‖g x‖ * ‖V x‖)) ?_
    ?_ (hgV.const_mul _) ?_
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact ((lip026c_continuous_hd2 hδ).comp_aestronglyMeasurable
      hw.memLp.aestronglyMeasurable).mul
      (hw.memLp_grad.aestronglyMeasurable.inner hV.aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := lip026c_hd2_bound hδ (f x)
    have h2 : |⟪g x, V x⟫| ≤ ‖g x‖ * ‖V x‖ := abs_real_inner_le_norm _ _
    rw [abs_of_nonneg h1.1]
    exact mul_le_mul h1.2 h2 (abs_nonneg _) (by norm_num)
  · filter_upwards [hw.ae_grad_eq_zero 0] with x hx
    by_cases hu : f x = 0
    · have hg0 := hx hu
      simp only [hu, hg0, inner_zero_left, mul_zero, lt_self_iff_false, ite_false]
      exact tendsto_const_nhds
    · have := (lip026c_tendsto_hd2 hu).mul_const ⟪g x, V x⟫
      by_cases h : f x < 0
      · simpa [h] using this
      · simpa [h] using this

theorem lip026c_slice_bound_neg {δ : ℝ} (hδ : 0 < δ) {f : Torus d → ℝ} {g V : Torus d → Tangent d}
    (hg : MemLp g 2 (haar d)) (hV : MemLp V 2 (haar d)) :
    |∫ x, lip026c_hd2 δ (f x) * ⟪g x, V x⟫ ∂haar d| ≤
      3 / 4 * (∫ x, ‖g x‖ ^ 2 ∂haar d + ∫ x, ‖V x‖ ^ 2 ∂haar d) := by
  have hGi : Integrable (fun x => ‖g x‖ ^ 2) (haar d) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  have hWi : Integrable (fun x => ‖V x‖ ^ 2) (haar d) :=
    (memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).1 hV
  have hb : Integrable (fun x => 3 / 4 * (‖g x‖ ^ 2 + ‖V x‖ ^ 2)) (haar d) :=
    (hGi.add hWi).const_mul _
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun x => ?_)).trans ?_
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := lip026c_hd2_bound hδ (f x)
    have h2 : |⟪g x, V x⟫| ≤ ‖g x‖ * ‖V x‖ := abs_real_inner_le_norm _ _
    rw [abs_of_nonneg h1.1]
    calc lip026c_hd2 δ (f x) * |⟪g x, V x⟫| ≤ 3 / 2 * (‖g x‖ * ‖V x‖) :=
          mul_le_mul h1.2 h2 (abs_nonneg _) (by norm_num)
      _ ≤ _ := by nlinarith [sq_nonneg (‖g x‖ - ‖V x‖)]
  · rw [integral_const_mul, integral_add hGi hWi]

theorem lip026c_tendsto_int_neg {T : ℝ} {u : ℝ → Torus d → ℝ} {g J : ℝ → Torus d → Tangent d}
    (S : lip026c_Setting T u g J) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    Tendsto (fun δ : ℝ => ∫ r in s..t, ∫ x, lip026c_hd2 δ (u r x) * ⟪g r x, J r x⟫ ∂haar d)
      (𝓝[>] 0)
      (𝓝 (∫ r in s..t, ∫ x, (if u r x < 0 then ⟪g r x, J r x⟫ else 0) ∂haar d)) := by
  have hT : 0 ≤ T := hs.trans (hst.trans ht)
  have hsub : Ioc s t ⊆ Icc 0 T := fun r hr => ⟨hs.trans hr.1.le, hr.2.trans ht⟩
  have hfacts : ∀ᵐ r ∂(volume.restrict (Ioc s t)),
      IsWeakGradient (u r) (g r) ∧ MemLp (J r) 2 (haar d) :=
    ae_restrict_of_ae_restrict_of_subset hsub (lip026c_ae_slice S)
  have hfacts' := (ae_restrict_iff' measurableSet_Ioc).1 hfacts
  have hGi : Integrable (fun r => ∫ x, ‖g r x‖ ^ 2 ∂haar d)
      (volume.restrict (Icc (0 : ℝ) T)) := S.int_g.integral_prod_left
  have hKi : Integrable (fun r => ∫ x, ‖J r x‖ ^ 2 ∂haar d)
      (volume.restrict (Icc (0 : ℝ) T)) := S.int_J.integral_prod_left
  have hbint : IntervalIntegrable (fun r => 3 / 4 * (∫ x, ‖g r x‖ ^ 2 ∂haar d +
      ∫ x, ‖J r x‖ ^ 2 ∂haar d)) volume s t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
    exact ((hGi.add hKi).const_mul _).mono_measure (Measure.restrict_mono hsub le_rfl)
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hbint ?_
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [Set.uIoc_of_le hst]
    exact (lip026c_aesm_limit S (lip026c_continuous_hd2 hδ) hT).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [hfacts'] with r hr hrI
    rw [Set.uIoc_of_le hst] at hrI
    obtain ⟨hw, hJr⟩ := hr hrI
    rw [Real.norm_eq_abs]
    exact lip026c_slice_bound_neg hδ hw.memLp_grad hJr
  · filter_upwards [hfacts'] with r hr hrI
    rw [Set.uIoc_of_le hst] at hrI
    obtain ⟨hw, hJr⟩ := hr hrI
    exact lip026c_tendsto_slice_neg hw hJr

/-! ### Part B: the negative-part energy -/

theorem lip026c_tendsto_hd_int {M : ℝ} {f : Torus d → ℝ} (hf : AEStronglyMeasurable f (haar d))
    (hfM : ∀ᵐ x ∂haar d, |f x| ≤ M) :
    Tendsto (fun δ : ℝ => ∫ x, lip026c_hd δ (f x) ∂haar d) (𝓝[>] 0)
      (𝓝 (∫ x, (min (f x) 0) ^ 2 / 2 ∂haar d)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (M + 1) ^ 2 / 2) ?_ ?_
    (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hc : Continuous (lip026c_hd δ) := (lip026c_contDiff_hd (n := 0) hδ).continuous
    exact hc.comp_aestronglyMeasurable hf
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with δ hδ
    filter_upwards [hfM] with x hx
    rw [Real.norm_eq_abs]
    refine (lip026c_hd_le hδ.1 (f x)).trans ?_
    have : |f x| + δ ≤ M + 1 := by linarith [hδ.2]
    have h0 : 0 ≤ |f x| + δ := by linarith [abs_nonneg (f x), hδ.1]
    have := pow_le_pow_left₀ h0 this 2
    linarith
  · exact Eventually.of_forall fun x => lip026c_tendsto_hd (f x)

theorem lip026c_chain_rule_neg {T : ℝ} {u : ℝ → Torus d → ℝ} {g J : ℝ → Torus d → Tangent d}
    (S : lip026c_Setting T u g J) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    ∫ x, (min (u t x) 0) ^ 2 / 2 ∂haar d - ∫ x, (min (u s x) 0) ^ 2 / 2 ∂haar d =
      -∫ r in s..t, ∫ x, (if u r x < 0 then ⟪g r x, J r x⟫ else 0) ∂haar d := by
  obtain ⟨M, hM⟩ := S.bdd
  have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs, hst.trans ht⟩
  have htI : t ∈ Icc (0 : ℝ) T := ⟨hs.trans hst, ht⟩
  have hL : ∀ r ∈ Icc (0 : ℝ) T, Tendsto (fun δ : ℝ => ∫ x, lip026c_hd δ (u r x) ∂haar d)
      (𝓝[>] 0) (𝓝 (∫ x, (min (u r x) 0) ^ 2 / 2 ∂haar d)) := fun r hr =>
    lip026c_tendsto_hd_int (S.div.integrable_u r hr).aestronglyMeasurable (hM r hr)
  have hR := (lip026c_tendsto_int_neg S hs hst ht).neg
  refine tendsto_nhds_unique ((hL t htI).sub (hL s hsI)) (hR.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hH : ContDiff ℝ 2 (lip026c_hd δ) := by
    exact_mod_cast lip026c_contDiff_hd (n := 2) hδ
  have h := lip026c_chain_rule_C2 S hH hs hst ht
  have hd : deriv (deriv (lip026c_hd δ)) = lip026c_hd2 δ :=
    funext fun y => (lip026c_hasDerivAt_dhd hδ y).deriv
  rw [hd] at h
  exact h.symm

/-! ### Part C: locality -/

theorem lip026c_locality {u : Torus d → ℝ} {g : Torus d → Tangent d} (h : IsWeakGradient u g) :
    ∀ᵐ x ∂haar d, u x = 0 → g x = 0 :=
  h.ae_grad_eq_zero 0

/-! ### Extension to arbitrary endpoint pairs and the main theorem -/

theorem lip026c_extend {T : ℝ} {A F : ℝ → ℝ}
    (h : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → A t - A s = -∫ r in s..t, F r) :
    ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, A t - A s = -∫ r in s..t, F r := by
  intro s hs t ht
  rcases le_total s t with hst | hst
  · exact h s t hs.1 hst ht.2
  · have := h t s ht.1 hst hs.2
    have e := intervalIntegral.integral_symm (μ := volume) (f := F) s t
    linarith

/-- **LIP026.**  Parabolic chain rule for `C²` functions and for `h(r) = (r⁻)²/2` along curves
with `∂ₜu = div J`, and locality of weak gradients on the zero set. -/
theorem parabolic_chain_rule_and_sobolev_zero_set_locality {d : ℕ} :
    (∀ {T : ℝ} {u : ℝ → Torus d → ℝ} {g J : ℝ → Torus d → Tangent d},
      lip026c_Setting T u g J → ∀ {H : ℝ → ℝ}, ContDiff ℝ 2 H →
      ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
        ∫ x, H (u t x) ∂haar d - ∫ x, H (u s x) ∂haar d =
          -∫ r in s..t, ∫ x, deriv (deriv H) (u r x) * ⟪g r x, J r x⟫ ∂haar d) ∧
    (∀ {T : ℝ} {u : ℝ → Torus d → ℝ} {g J : ℝ → Torus d → Tangent d},
      lip026c_Setting T u g J →
      ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
        ∫ x, (min (u t x) 0) ^ 2 / 2 ∂haar d - ∫ x, (min (u s x) 0) ^ 2 / 2 ∂haar d =
          -∫ r in s..t, ∫ x, (if u r x < 0 then ⟪g r x, J r x⟫ else 0) ∂haar d) ∧
    (∀ {u : Torus d → ℝ} {g : Torus d → Tangent d}, IsWeakGradient u g →
      ∀ᵐ x ∂haar d, u x = 0 → g x = 0) :=
  ⟨fun S _ hH => lip026c_extend (fun _ _ hs hst ht => lip026c_chain_rule_C2 S hH hs hst ht),
   fun S => lip026c_extend (fun _ _ hs hst ht => lip026c_chain_rule_neg S hs hst ht),
   fun h => lip026c_locality h⟩

end DGPS.Lipschitz
