import DGPS.FiniteN.ScalarFold
import DGPS.FiniteN.ScalarFoldFIN057

/-!
# FIN059: fold local Dirichlet power two thirds

For the scalar auxiliary potential `ψ = ψ_{h_c}` at the fold, every smooth `f` supported in the
fixed fold patch `(α, β) ∋ t_*` satisfies `∫ f'² e^{-Nψ} ≥ c N^{2/3} ∫ f² e^{-Nψ}` for `N ≥ 1`,
with `c > 0` and the patch depending only on `κ`.

Proof (following `scalar_cos_fold_finite_size.md` §4.1).  In the exact cubic coordinate `v` of
FIN057 one has `ψ(T w) = ψ(t_*) - w³/3`, so `e^{-Nψ(T w)} = e^{-Nψ(t_*)} e^{N w³/3}`.
Pulling `f` back to `F = f ∘ T` (zero extension) and changing variables, the weighted Dirichlet
form and `L²` norm are compared with the flat ones `∫ F'² e^{N w³/3}`, `∫ F² e^{N w³/3}` up to the
Jacobian bounds `1/M ≤ T' ≤ 1/m`.  The substitution `y = N^{1/3} w` together with the
multiplier `e^{y³/6}` turns `∫ F'² e^{N w³/3}` into `N^{2/3}` times the FIN058 form
`∫ (U' - y² U / 2)²`, which is bounded below by `b₀ ∫ U²` (FIN058).
-/

open MeasureTheory Set
open scoped ContDiff

namespace DGPS.FiniteN.ScalarFoldFIN059

theorem rescaled_gap_FIN059 {b0 : ℝ}
    (hb : ∀ u : ℝ → ℝ, ContDiff ℝ ∞ u → HasCompactSupport u →
      b0 * ∫ y, u y ^ 2 ≤ ∫ y, (deriv u y - y ^ 2 * u y / 2) ^ 2)
    {r N : ℝ} (hr : 0 < r) (hN : r ^ 3 = N) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFs : HasCompactSupport F) :
    b0 * r ^ 2 * ∫ w, F w ^ 2 * Real.exp (N * w ^ 3 / 3) ≤
      ∫ w, deriv F w ^ 2 * Real.exp (N * w ^ 3 / 3) := by
  subst hN
  have hr0 : r ≠ 0 := hr.ne'
  set U : ℝ → ℝ := fun y => F (r⁻¹ * y) * Real.exp (y ^ 3 / 6) with hU
  have hFd : ∀ x, HasDerivAt F (deriv F x) x := fun x =>
    ((hF.differentiable (by simp)) x).hasDerivAt
  have hUs : ContDiff ℝ ∞ U := (hF.comp (contDiff_const.mul contDiff_id)).mul
      (Real.contDiff_exp.comp ((contDiff_id.pow 3).div_const 6))
  have hUc : HasCompactSupport U := by
    have : HasCompactSupport (fun y => F (r⁻¹ * y)) := by
      simpa [smul_eq_mul] using hFs.comp_smul (inv_ne_zero hr0)
    exact this.mul_right
  have hderiv : ∀ y, deriv U y = r⁻¹ * deriv F (r⁻¹ * y) * Real.exp (y ^ 3 / 6)
      + F (r⁻¹ * y) * (Real.exp (y ^ 3 / 6) * (y ^ 2 / 2)) := by
    intro y
    have h1 : HasDerivAt (fun y => F (r⁻¹ * y)) (deriv F (r⁻¹ * y) * r⁻¹) y := by
      have := (hFd (r⁻¹ * y)).comp y ((hasDerivAt_id' y).const_mul r⁻¹)
      rw [mul_one] at this
      exact this
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (y ^ 3 / 6))
        (Real.exp (y ^ 3 / 6) * (y ^ 2 / 2)) y := by
      have := ((hasDerivAt_pow 3 y).div_const 6).exp
      convert this using 1
      norm_num
      ring
    have h3 : HasDerivAt U (deriv F (r⁻¹ * y) * r⁻¹ * Real.exp (y ^ 3 / 6)
        + F (r⁻¹ * y) * (Real.exp (y ^ 3 / 6) * (y ^ 2 / 2))) y := h1.mul h2
    rw [h3.deriv]; ring
  have hkey : ∀ y, deriv U y - y ^ 2 * U y / 2 = r⁻¹ * deriv F (r⁻¹ * y) * Real.exp (y ^ 3 / 6) := by
    intro y; rw [hderiv]; simp only [hU]; ring
  have hexp : ∀ y : ℝ, Real.exp (y ^ 3 / 6) ^ 2 = Real.exp (r ^ 3 * (r⁻¹ * y) ^ 3 / 3) := by
    intro y
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
    push_cast
    ring
  have e1 : ∀ y, U y ^ 2 = (fun w => F w ^ 2 * Real.exp (r ^ 3 * w ^ 3 / 3)) (r⁻¹ * y) := by
    intro y; simp only [hU]; rw [mul_pow, hexp]
  have e2 : ∀ y, (deriv U y - y ^ 2 * U y / 2) ^ 2 =
      (r⁻¹) ^ 2 * (fun w => deriv F w ^ 2 * Real.exp (r ^ 3 * w ^ 3 / 3)) (r⁻¹ * y) := by
    intro y; rw [hkey, mul_pow, mul_pow, hexp]; ring
  have hmain := hb U hUs hUc
  have I1 : ∫ y, U y ^ 2 = r * ∫ w, F w ^ 2 * Real.exp (r ^ 3 * w ^ 3 / 3) := by
    rw [show (fun y => U y ^ 2) = fun y =>
      (fun w => F w ^ 2 * Real.exp (r ^ 3 * w ^ 3 / 3)) (r⁻¹ * y) from funext e1,
      Measure.integral_comp_inv_mul_left (fun w => F w ^ 2 * Real.exp (r ^ 3 * w ^ 3 / 3)) r,
      abs_of_pos hr, smul_eq_mul]
  have I2 : ∫ y, (deriv U y - y ^ 2 * U y / 2) ^ 2 =
      r⁻¹ ^ 2 * (r * ∫ w, deriv F w ^ 2 * Real.exp (r ^ 3 * w ^ 3 / 3)) := by
    rw [show (fun y => (deriv U y - y ^ 2 * U y / 2) ^ 2) = fun y =>
      (r⁻¹) ^ 2 * (fun w => deriv F w ^ 2 * Real.exp (r ^ 3 * w ^ 3 / 3)) (r⁻¹ * y)
      from funext e2, integral_const_mul,
      Measure.integral_comp_inv_mul_left
        (fun w => deriv F w ^ 2 * Real.exp (r ^ 3 * w ^ 3 / 3)) r, abs_of_pos hr, smul_eq_mul]
  rw [I1, I2] at hmain
  have h2 : r * (r⁻¹ ^ 2 * (r * ∫ w, deriv F w ^ 2 * Real.exp (r ^ 3 * w ^ 3 / 3))) =
      ∫ w, deriv F w ^ 2 * Real.exp (r ^ 3 * w ^ 3 / 3) := by
    field_simp
  rw [← h2, show b0 * r ^ 2 * ∫ w, F w ^ 2 * Real.exp (r ^ 3 * w ^ 3 / 3) =
      r * (b0 * (r * ∫ w, F w ^ 2 * Real.exp (r ^ 3 * w ^ 3 / 3))) by ring]
  exact mul_le_mul_of_nonneg_left hmain hr.le


/-- Pullback of `f` along the chart `T : (a, b) → (α, β)`, extended by zero outside `(a, b)`. -/
noncomputable def pullbackFIN059 (a b : ℝ) (T f : ℝ → ℝ) : ℝ → ℝ :=
  Set.indicator (Ioo a b) (fun w => f (T w))

/-- The hypotheses on an exact chart of the fold consumed from FIN057. -/
structure ChartFIN059 (ψ : ℝ → ℝ) (α β a b ψs m M : ℝ) (v T : ℝ → ℝ) : Prop where
  psi_cont : Continuous ψ
  m_pos : 0 < m
  m_le : m ≤ M
  v_cont : ContinuousOn v (Ioo α β)
  T_smooth : ContDiffOn ℝ ∞ T (Ioo a b)
  maps : ∀ w ∈ Ioo a b, T w ∈ Ioo α β ∧ v (T w) = w ∧ ψ (T w) = ψs - w ^ 3 / 3 ∧
    1 / M ≤ deriv T w ∧ deriv T w ≤ 1 / m
  back : ∀ t ∈ Ioo α β, v t ∈ Ioo a b ∧ T (v t) = t

section Transfer

variable {ψ : ℝ → ℝ} {α β a b ψs m M : ℝ} {v T f : ℝ → ℝ}

theorem tsupport_isCompact_FIN059 (hfs : tsupport f ⊆ Ioo α β) : IsCompact (tsupport f) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport f)
    ((Metric.isBounded_Ioo α β).subset hfs)

theorem image_isCompact_FIN059 (C : ChartFIN059 ψ α β a b ψs m M v T)
    (hfs : tsupport f ⊆ Ioo α β) : IsCompact (v '' tsupport f) :=
  (tsupport_isCompact_FIN059 hfs).image_of_continuousOn (C.v_cont.mono hfs)

theorem image_subset_FIN059 (C : ChartFIN059 ψ α β a b ψs m M v T)
    (hfs : tsupport f ⊆ Ioo α β) : v '' tsupport f ⊆ Ioo a b := by
  rintro w ⟨t, ht, rfl⟩
  exact (C.back t (hfs ht)).1

theorem pullback_vanish_FIN059 (C : ChartFIN059 ψ α β a b ψs m M v T) {w : ℝ}
    (hw : w ∉ v '' tsupport f) : pullbackFIN059 a b T f w = 0 := by
  unfold pullbackFIN059
  by_cases hJ : w ∈ Ioo a b
  · rw [indicator_of_mem hJ]
    by_contra h
    exact hw ⟨T w, subset_tsupport f h, (C.maps w hJ).2.1⟩
  · rw [indicator_of_notMem hJ]

theorem pullback_eq_FIN059 {w : ℝ} (hJ : w ∈ Ioo a b) :
    pullbackFIN059 a b T f w = f (T w) := by
  simp [pullbackFIN059, indicator_of_mem hJ]

theorem pullback_contDiff_FIN059 (C : ChartFIN059 ψ α β a b ψs m M v T)
    (hf : ContDiff ℝ ∞ f) (hfs : tsupport f ⊆ Ioo α β) :
    ContDiff ℝ ∞ (pullbackFIN059 a b T f) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hJ : w ∈ Ioo a b
  · have hT : ContDiffAt ℝ ∞ T w := C.T_smooth.contDiffAt (isOpen_Ioo.mem_nhds hJ)
    have h1 : ContDiffAt ℝ ∞ (fun w => f (T w)) w := hf.contDiffAt.comp w hT
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hJ] with x hx
    exact pullback_eq_FIN059 hx
  · have hwK : w ∉ v '' tsupport f := fun h => hJ (image_subset_FIN059 C hfs h)
    have hopen : IsOpen (v '' tsupport f)ᶜ := (image_isCompact_FIN059 C hfs).isClosed.isOpen_compl
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hwK] with x hx
    exact pullback_vanish_FIN059 C hx

theorem pullback_hasCompactSupport_FIN059 (C : ChartFIN059 ψ α β a b ψs m M v T)
    (hfs : tsupport f ⊆ Ioo α β) : HasCompactSupport (pullbackFIN059 a b T f) :=
  HasCompactSupport.intro (image_isCompact_FIN059 C hfs) (fun _ hw => pullback_vanish_FIN059 C hw)

theorem pullback_deriv_FIN059 (C : ChartFIN059 ψ α β a b ψs m M v T)
    (hf : ContDiff ℝ ∞ f) {w : ℝ} (hJ : w ∈ Ioo a b) :
    deriv (pullbackFIN059 a b T f) w = deriv f (T w) * deriv T w := by
  have hT : DifferentiableAt ℝ T w :=
    (C.T_smooth.contDiffAt (isOpen_Ioo.mem_nhds hJ)).differentiableAt (by simp)
  have heq : pullbackFIN059 a b T f =ᶠ[nhds w] fun w => f (T w) := by
    filter_upwards [isOpen_Ioo.mem_nhds hJ] with x hx
    exact pullback_eq_FIN059 hx
  rw [heq.deriv_eq]
  exact deriv_comp w (hf.differentiable (by simp) _) hT

theorem pullback_deriv_zero_FIN059 (C : ChartFIN059 ψ α β a b ψs m M v T)
    (hfs : tsupport f ⊆ Ioo α β) {w : ℝ} (hJ : w ∉ Ioo a b) :
    deriv (pullbackFIN059 a b T f) w = 0 := by
  have hwK : w ∉ v '' tsupport f := fun h => hJ (image_subset_FIN059 C hfs h)
  have hopen : IsOpen (v '' tsupport f)ᶜ := (image_isCompact_FIN059 C hfs).isClosed.isOpen_compl
  have heq : pullbackFIN059 a b T f =ᶠ[nhds w] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hwK] with x hx
    exact pullback_vanish_FIN059 C hx
  rw [heq.deriv_eq]
  simp

/-- Change of variables `t = T w` for a continuous function supported in the patch. -/
theorem change_of_variables_FIN059 (C : ChartFIN059 ψ α β a b ψs m M v T) {g : ℝ → ℝ}
    (hg : Continuous g) {S : Set ℝ} (hS : IsCompact S) (hSsub : S ⊆ Ioo α β)
    (hgz : ∀ t, t ∉ S → g t = 0) :
    IntegrableOn (fun w => |deriv T w| • g (T w)) (Ioo a b) ∧
      ∫ t, g t = ∫ w in Ioo a b, |deriv T w| • g (T w) := by
  have himg : T '' Ioo a b = Ioo α β := by
    ext t
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (C.maps w hw).1
    · intro ht
      exact ⟨v t, (C.back t ht).1, (C.back t ht).2⟩
  have hder : ∀ w ∈ Ioo a b, HasDerivWithinAt T (deriv T w) (Ioo a b) w := fun w hw =>
    ((C.T_smooth.contDiffAt (isOpen_Ioo.mem_nhds hw)).differentiableAt
      (by simp)).hasDerivAt.hasDerivWithinAt
  have hinj : InjOn T (Ioo a b) := fun w1 h1 w2 h2 h => by
    rw [← (C.maps w1 h1).2.1, ← (C.maps w2 h2).2.1, h]
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport (HasCompactSupport.intro hS hgz)
  constructor
  · refine (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hder hinj g).1 ?_
    rw [himg]
    exact hgi.integrableOn
  · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo α β)
      (fun t ht => hgz t (fun h => ht (hSsub h))), ← himg]
    exact integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hder hinj g


theorem exp_chart_FIN059 (C : ChartFIN059 ψ α β a b ψs m M v T) (N : ℝ) {w : ℝ}
    (hw : w ∈ Ioo a b) :
    Real.exp (-(N * ψ (T w))) = Real.exp (-(N * ψs)) * Real.exp (N * w ^ 3 / 3) := by
  rw [← Real.exp_add, (C.maps w hw).2.2.1]
  congr 1
  ring

theorem deriv_T_pos_FIN059 (C : ChartFIN059 ψ α β a b ψs m M v T) {w : ℝ} (hw : w ∈ Ioo a b) :
    0 < deriv T w := by
  have hM : 0 < M := lt_of_lt_of_le C.m_pos C.m_le
  exact lt_of_lt_of_le (one_div_pos.2 hM) (C.maps w hw).2.2.2.1

/-- Lower bound of the weighted Dirichlet form by the flat one. -/
theorem dirichlet_lower_FIN059 (C : ChartFIN059 ψ α β a b ψs m M v T)
    (hf : ContDiff ℝ ∞ f) (hfs : tsupport f ⊆ Ioo α β) (N : ℝ) :
    m * Real.exp (-(N * ψs)) *
        ∫ w, deriv (pullbackFIN059 a b T f) w ^ 2 * Real.exp (N * w ^ 3 / 3) ≤
      ∫ t, deriv f t ^ 2 * Real.exp (-(N * ψ t)) := by
  set F := pullbackFIN059 a b T f with hFdef
  have hFs : HasCompactSupport F := pullback_hasCompactSupport_FIN059 C hfs
  have hFsm : ContDiff ℝ ∞ F := pullback_contDiff_FIN059 C hf hfs
  have hdFc : Continuous (deriv F) := hFsm.continuous_deriv (by simp)
  have hdFs : HasCompactSupport (deriv F) := hFs.deriv
  have hdfc : Continuous (deriv f) := hf.continuous_deriv (by simp)
  have hg : Continuous (fun t => deriv f t ^ 2 * Real.exp (-(N * ψ t))) :=
    (hdfc.pow 2).mul (Real.continuous_exp.comp (C.psi_cont.const_mul N).neg)
  obtain ⟨hBi, hBeq⟩ := change_of_variables_FIN059 C hg (tsupport_isCompact_FIN059 hfs) hfs
    (fun t ht => by
      have : deriv f t = 0 := by
        by_contra h; exact ht (support_deriv_subset (𝕜 := ℝ) h)
      simp [this])
  have hAc : Continuous (fun w => m * Real.exp (-(N * ψs)) *
      (deriv F w ^ 2 * Real.exp (N * w ^ 3 / 3))) :=
    continuous_const.mul ((hdFc.pow 2).mul (Real.continuous_exp.comp (by fun_prop)))
  have hAi : Integrable (fun w => m * Real.exp (-(N * ψs)) *
      (deriv F w ^ 2 * Real.exp (N * w ^ 3 / 3))) :=
    hAc.integrable_of_hasCompactSupport (HasCompactSupport.intro hdFs (fun w hw => by
      simp [image_eq_zero_of_notMem_tsupport hw]))
  have hAeq : ∫ w in Ioo a b, m * Real.exp (-(N * ψs)) *
      (deriv F w ^ 2 * Real.exp (N * w ^ 3 / 3)) =
      m * Real.exp (-(N * ψs)) * ∫ w, deriv F w ^ 2 * Real.exp (N * w ^ 3 / 3) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, integral_const_mul]
    intro w hw
    simp [hFdef, pullback_deriv_zero_FIN059 C hfs hw]
  rw [hBeq, ← hAeq]
  refine setIntegral_mono_on hAi.integrableOn hBi measurableSet_Ioo (fun w hw => ?_)
  have hT' := deriv_T_pos_FIN059 C hw
  have hTle : deriv T w ≤ 1 / m := (C.maps w hw).2.2.2.2
  have hmT : m * deriv T w ≤ 1 := by
    rw [le_div_iff₀ C.m_pos] at hTle; linarith
  have hd : deriv F w = deriv f (T w) * deriv T w := pullback_deriv_FIN059 C hf hw
  simp only [smul_eq_mul, abs_of_pos hT', exp_chart_FIN059 C N hw, hd]
  have hE : 0 < Real.exp (-(N * ψs)) * Real.exp (N * w ^ 3 / 3) := by positivity
  set E := Real.exp (-(N * ψs)) * Real.exp (N * w ^ 3 / 3) with hEdef
  have hrw : m * Real.exp (-(N * ψs)) * ((deriv f (T w) * deriv T w) ^ 2 *
      Real.exp (N * w ^ 3 / 3)) = (m * deriv T w) * (deriv T w * (deriv f (T w) ^ 2 * E)) := by
    rw [hEdef]; ring
  rw [hrw]
  calc (m * deriv T w) * (deriv T w * (deriv f (T w) ^ 2 * E))
      ≤ 1 * (deriv T w * (deriv f (T w) ^ 2 * E)) :=
        mul_le_mul_of_nonneg_right hmT (by positivity)
    _ = deriv T w * (deriv f (T w) ^ 2 * E) := one_mul _

/-- Upper bound of the weighted `L²` norm by the flat one. -/
theorem l2_upper_FIN059 (C : ChartFIN059 ψ α β a b ψs m M v T)
    (hf : ContDiff ℝ ∞ f) (hfs : tsupport f ⊆ Ioo α β) (N : ℝ) :
    ∫ t, f t ^ 2 * Real.exp (-(N * ψ t)) ≤
      m⁻¹ * Real.exp (-(N * ψs)) *
        ∫ w, pullbackFIN059 a b T f w ^ 2 * Real.exp (N * w ^ 3 / 3) := by
  set F := pullbackFIN059 a b T f with hFdef
  have hFs : HasCompactSupport F := pullback_hasCompactSupport_FIN059 C hfs
  have hFsm : ContDiff ℝ ∞ F := pullback_contDiff_FIN059 C hf hfs
  have hFc : Continuous F := hFsm.continuous
  have hg : Continuous (fun t => f t ^ 2 * Real.exp (-(N * ψ t))) :=
    (hf.continuous.pow 2).mul (Real.continuous_exp.comp (C.psi_cont.const_mul N).neg)
  obtain ⟨hBi, hBeq⟩ := change_of_variables_FIN059 C hg (tsupport_isCompact_FIN059 hfs) hfs
    (fun t ht => by
      have : f t = 0 := image_eq_zero_of_notMem_tsupport ht
      simp [this])
  have hAc : Continuous (fun w => m⁻¹ * Real.exp (-(N * ψs)) *
      (F w ^ 2 * Real.exp (N * w ^ 3 / 3))) :=
    continuous_const.mul ((hFc.pow 2).mul (Real.continuous_exp.comp (by fun_prop)))
  have hAi : Integrable (fun w => m⁻¹ * Real.exp (-(N * ψs)) *
      (F w ^ 2 * Real.exp (N * w ^ 3 / 3))) :=
    hAc.integrable_of_hasCompactSupport (HasCompactSupport.intro hFs (fun w hw => by
      simp [image_eq_zero_of_notMem_tsupport hw]))
  have hAeq : ∫ w in Ioo a b, m⁻¹ * Real.exp (-(N * ψs)) *
      (F w ^ 2 * Real.exp (N * w ^ 3 / 3)) =
      m⁻¹ * Real.exp (-(N * ψs)) * ∫ w, F w ^ 2 * Real.exp (N * w ^ 3 / 3) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, integral_const_mul]
    intro w hw
    have : F w = 0 := pullback_vanish_FIN059 C (fun h => hw (image_subset_FIN059 C hfs h))
    simp [this]
  rw [hBeq, ← hAeq]
  refine setIntegral_mono_on hBi hAi.integrableOn measurableSet_Ioo (fun w hw => ?_)
  have hT' := deriv_T_pos_FIN059 C hw
  have hTle : deriv T w ≤ m⁻¹ := by
    have := (C.maps w hw).2.2.2.2
    rwa [one_div] at this
  have hF : F w = f (T w) := pullback_eq_FIN059 hw
  simp only [smul_eq_mul, abs_of_pos hT', exp_chart_FIN059 C N hw, hF]
  have hE : 0 < Real.exp (-(N * ψs)) * Real.exp (N * w ^ 3 / 3) := by positivity
  set E := Real.exp (-(N * ψs)) * Real.exp (N * w ^ 3 / 3) with hEdef
  have hrw : m⁻¹ * Real.exp (-(N * ψs)) * (f (T w) ^ 2 * Real.exp (N * w ^ 3 / 3)) =
      m⁻¹ * (f (T w) ^ 2 * E) := by
    rw [hEdef]; ring
  rw [hrw]
  calc deriv T w * (f (T w) ^ 2 * E) ≤ m⁻¹ * (f (T w) ^ 2 * E) :=
        mul_le_mul_of_nonneg_right hTle (by positivity)

end Transfer

end DGPS.FiniteN.ScalarFoldFIN059

namespace DGPS.FiniteN

open DGPS.Models

/-- **FIN059.** Fold local Dirichlet power two thirds.  Fix `κ > 2` and put `h_c = scalarFoldField κ`,
`ψ = scalarPsi κ h_c`, `t_* = -scalarFoldPoint κ`.  There is a fixed fold patch `(α, β) ∋ t_*` and
a constant `c > 0`, depending only on `κ`, such that for every `N ≥ 1` and every smooth `f`
supported in the patch,
`c N^{2/3} ∫ f² e^{-Nψ} ≤ ∫ (f')² e^{-Nψ}`. -/
theorem fold_local_dirichlet_power_two_thirds (κ : ℝ) (hκ : 2 < κ) :
    let hc := scalarFoldField κ
    let ψ := scalarPsi κ hc
    let tStar := -scalarFoldPoint κ
    ∃ α β c : ℝ, α < tStar ∧ tStar < β ∧ 0 < c ∧
      ∀ N : ℝ, 1 ≤ N → ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → tsupport f ⊆ Set.Ioo α β →
        c * N ^ (2 / 3 : ℝ) * ∫ t, f t ^ 2 * Real.exp (-(N * ψ t)) ≤
          ∫ t, deriv f t ^ 2 * Real.exp (-(N * ψ t)) := by
  intro hc ψ tStar
  obtain ⟨α, β, v, T, m, M, hα, hβ, hm, hmM, hvsm, hv0, hcube, hbd, hmono, hTsm, h0J, hT0,
    hT1, hT2⟩ := exact_fold_cubic_coordinate κ hκ
  obtain ⟨b0, hb0, hgap⟩ := positive_cubic_transformed_dirichlet_gap
  have hψc : Continuous ψ := (ScalarFoldFIN057.scalarPsi_contDiff_FIN057 κ hc).continuous
  have C : ScalarFoldFIN059.ChartFIN059 ψ α β (v α) (v β) (ψ tStar) m M v T :=
    { psi_cont := hψc
      m_pos := hm
      m_le := hmM
      v_cont := hvsm.continuousOn
      T_smooth := hTsm
      maps := fun w hw => by
        obtain ⟨h1, h2, h3, h4, h5⟩ := hT1 w hw
        exact ⟨h1, h2, h3, h4, h5⟩
      back := fun t ht => by
        obtain ⟨h1, h2⟩ := hT2 t ht
        exact ⟨h1, h2⟩ }
  refine ⟨α, β, b0 * m ^ 2, hα, hβ, by positivity, ?_⟩
  intro N hN f hf hfs
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  set r : ℝ := N ^ (1 / 3 : ℝ) with hrdef
  have hr : 0 < r := Real.rpow_pos_of_pos hN0 _
  have hr3 : r ^ 3 = N := by
    rw [hrdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hr2 : N ^ (2 / 3 : ℝ) = r ^ 2 := by
    rw [hrdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  set F := ScalarFoldFIN059.pullbackFIN059 (v α) (v β) T f with hFdef
  have hFs : HasCompactSupport F := ScalarFoldFIN059.pullback_hasCompactSupport_FIN059 C hfs
  have hFsm : ContDiff ℝ ∞ F := ScalarFoldFIN059.pullback_contDiff_FIN059 C hf hfs
  have hA := ScalarFoldFIN059.rescaled_gap_FIN059 hgap hr hr3 hFsm hFs
  have hD := ScalarFoldFIN059.dirichlet_lower_FIN059 C hf hfs N
  have hL := ScalarFoldFIN059.l2_upper_FIN059 C hf hfs N
  rw [hr2]
  set S1 := ∫ w, F w ^ 2 * Real.exp (N * w ^ 3 / 3)
  set S2 := ∫ w, deriv F w ^ 2 * Real.exp (N * w ^ 3 / 3)
  set Lt := ∫ t, f t ^ 2 * Real.exp (-(N * ψ t))
  set Dt := ∫ t, deriv f t ^ 2 * Real.exp (-(N * ψ t))
  have hE : 0 < Real.exp (-(N * ψ tStar)) := Real.exp_pos _
  have hcoef : 0 ≤ b0 * m ^ 2 * r ^ 2 := by positivity
  calc b0 * m ^ 2 * r ^ 2 * Lt
      ≤ b0 * m ^ 2 * r ^ 2 * (m⁻¹ * Real.exp (-(N * ψ tStar)) * S1) :=
        mul_le_mul_of_nonneg_left hL hcoef
    _ = m * Real.exp (-(N * ψ tStar)) * (b0 * r ^ 2 * S1) := by
        field_simp
    _ ≤ m * Real.exp (-(N * ψ tStar)) * S2 :=
        mul_le_mul_of_nonneg_left hA (by positivity)
    _ ≤ Dt := hD

end DGPS.FiniteN
