import SharpSymmetricLSI.Paper.CircleSobolev
import SharpSymmetricLSI.Paper.CircleLSIExt
import SharpSymmetricLSI.Paper.AppAPos5
import SharpSymmetricLSI.Paper.FourierSynth
import SharpSymmetricLSI.Paper.CosineExpansion
import SharpSymmetricLSI.Infra.ChainRule

/-!
# Section 9 regularity, module A: continuous representatives, smooth tests, `|w| ∈ H¹`

Lane C of the Section 9 formalization (H8 `sMin_regularity`).  This file is a COPY, with the
namespace changed from `SharpLSI.FL.Prop82` to `SharpLSI.FL.Ex.Reg` and otherwise unmodified, of

* `FullLabeledLSI/Nonvacuity/Prop82/CCircle.lean` (continuous `H¹(𝕋)` representative via
  mollification; smooth tests give weak derivatives), and
* `FullLabeledLSI/Nonvacuity/Prop82/CAbs.lean` (`|w|/c ∈ H¹` with the gradient bound),

from branch `claude/prop82-lane-c-s8pz05` at commit `ce7043d` (Prop 8.2 lane C).  That branch is
neither imported nor edited.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Ex.Reg

open SharpLSI UnitAddTorus

theorem lineT_secT (y : Torus 1) : lineT (secT y 0) = y := by
  unfold lineT; rw [← secT_eq_lineF]; exact liftT_secT y

theorem lineT_add_one (x : ℝ) : lineT (x + 1) = lineT x := by
  simpa using lineT_add_int x 1

theorem periodic_lineT : Function.Periodic lineT 1 := lineT_add_one

theorem secT_mem_Icc (y : Torus 1) : secT y 0 ∈ Icc (0 : ℝ) 1 := by
  have := (AddCircle.measurableEquivIoc 1 0 (y 0)).2
  have h2 : ((AddCircle.measurableEquivIoc 1 0 (y 0) : ℝ)) ≤ 1 := by simpa using this.2
  exact ⟨this.1.le, h2⟩

theorem secT_lineT_sub (r : ℝ) : ∃ m : ℤ, secT (lineT r) 0 = r + m := by
  obtain ⟨m, hm⟩ := secT_liftT_eq (lineF r)
  refine ⟨m 0, ?_⟩
  have := congrFun hm 0
  simpa [lineT, lineF, intVec] using this

/-- A property holding a.e. on the circle holds for a.e. real `r` along `lineT`. -/
theorem ae_real_of_ae_torus {p : Torus 1 → Prop} (h : ∀ᵐ y ∂haar 1, p y) :
    ∀ᵐ r : ℝ, p (lineT r) := by
  have h0 := ae_lineT h
  have hall : ∀ n : ℤ, ∀ᵐ r ∂(volume : Measure ℝ).restrict (Ioc (n : ℝ) (n + 1)), p (lineT r) := by
    intro n
    have hmp := (measurePreserving_sub_right (volume : Measure ℝ) (n : ℝ)).restrict_preimage_emb
      (measurableEmbedding_subRight (n : ℝ)) (Ioc (0 : ℝ) 1)
    have hpre : (fun r : ℝ => r - n) ⁻¹' Ioc (0 : ℝ) 1 = Ioc (n : ℝ) (n + 1) := by
      ext r; simp only [mem_preimage, mem_Ioc]; constructor <;> intro hr <;> constructor <;> linarith [hr.1, hr.2]
    rw [hpre] at hmp
    have := hmp.quasiMeasurePreserving.ae h0
    filter_upwards [this] with r hr
    have e : lineT (r - n) = lineT r := by
      have := lineT_add_int (r - n) n
      simpa using this.symm
    rwa [e] at hr
  have : ∀ᵐ r ∂(volume : Measure ℝ).restrict (⋃ n : ℤ, Ioc (n : ℝ) (n + 1)), p (lineT r) :=
    (ae_restrict_iUnion_iff _ _).2 hall
  rwa [iUnion_Ioc_intCast, Measure.restrict_univ] at this

theorem intervalIntegrable_lineT_all {g : Torus 1 → ℝ} (hg : Integrable g (haar 1)) (a b : ℝ) :
    IntervalIntegrable (fun r => g (lineT r)) volume a b :=
  (periodic_lineT.comp g).intervalIntegrable₀ one_ne_zero (intervalIntegrable_lineT hg) a b

/-- FTC for the mollifications. -/
theorem moll_sub_eq_integral {f g : Torus 1 → ℝ} (hw : IsWeakGrad f (fun y _ => g y))
    (hf : Integrable f (haar 1)) (n : ℕ) (s t : ℝ) :
    moll n f (lineT t) - moll n f (lineT s) = ∫ r in s..t, moll n g (lineT r) := by
  set Φ := moll n f ∘ liftT with hΦdef
  have hΦ : ContDiff ℝ ∞ Φ := moll_comp_liftT_contDiff n hf
  set V : ℝ → ℝ := fun s => Φ (lineF s) with hV
  have hline : ∀ s, HasDerivAt (fun r : ℝ => lineF r) (Pi.single 0 1) s := by
    intro s
    have : (fun r : ℝ => lineF r) = fun r => r • (Pi.single 0 1 : Fin 1 → ℝ) := by
      funext r i; rw [Subsingleton.elim i 0]; simp [lineF]
    rw [this]
    simpa using (hasDerivAt_id s).smul_const (Pi.single 0 1 : Fin 1 → ℝ)
  have hVd : ∀ s, HasDerivAt V (fderiv ℝ Φ (lineF s) (Pi.single 0 1)) s := fun s =>
    ((hΦ.differentiable (by simp)) (lineF s)).hasFDerivAt.comp_hasDerivAt s (hline s)
  have hder : ∀ s, fderiv ℝ Φ (lineF s) (Pi.single 0 1) = moll n g (lineT s) := by
    intro s
    rw [hΦdef, moll_comp_liftT, fderiv_mollL_of_isWeakGrad hw n (lineF s) 0]
    exact (congrFun (moll_comp_liftT n g) (lineF s)).symm
  have hcont : Continuous fun s => moll n g (lineT s) := by
    have : (fun s => moll n g (lineT s)) = fun s => mollL n (g ∘ liftT) (lineF s) := by
      funext s
      have := congrFun (moll_comp_liftT n g) (lineF s)
      simpa [lineT] using this
    rw [this]
    exact ((contDiff_mollL n (hw.locInt_grad 0)).continuous).comp
      (continuous_pi fun _ => continuous_id)
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => by
      simpa [hder r] using hVd r) (hcont.intervalIntegrable s t)
  rw [this]
  rfl

theorem abs_integral_lineT_le {h : Torus 1 → ℝ} (hh : Integrable h (haar 1)) {c d : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) (hd : d ∈ Icc (0 : ℝ) 1) :
    |∫ r in c..d, h (lineT r)| ≤ ∫ y, |h y| ∂haar 1 := by
  have habs : Integrable (fun y => |h y|) (haar 1) := hh.abs
  have key : ∀ c d : ℝ, c ∈ Icc (0 : ℝ) 1 → d ∈ Icc (0 : ℝ) 1 → c ≤ d →
      |∫ r in c..d, h (lineT r)| ≤ ∫ y, |h y| ∂haar 1 := by
    intro c d hc hd hcd
    have h1 : |∫ r in c..d, h (lineT r)| ≤ ∫ r in c..d, |h (lineT r)| :=
      intervalIntegral.abs_integral_le_integral_abs hcd
    refine h1.trans ?_
    rw [← intervalIntegral_lineT habs.aestronglyMeasurable]
    exact intervalIntegral.integral_mono_interval hc.1 hcd hd.2
      (Eventually.of_forall fun r => abs_nonneg _) (intervalIntegrable_lineT habs)
  rcases le_total c d with hcd | hdc
  · exact key c d hc hd hcd
  · rw [intervalIntegral.integral_symm, abs_neg]; exact key d c hd hc hdc

theorem tendsto_moll_integral {g : Torus 1 → ℝ} (hg : Integrable g (haar 1)) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => ∫ r in s..t, moll n g (lineT r)) atTop (𝓝 (∫ r in s..t, g (lineT r))) := by
  have hmi : ∀ n, Integrable (moll n g) (haar 1) := fun n => integrable_moll n hg
  have hbd : ∀ n, |(∫ r in s..t, moll n g (lineT r)) - ∫ r in s..t, g (lineT r)| ≤
      ∫ y, |moll n g y - g y| ∂haar 1 := by
    intro n
    rw [← intervalIntegral.integral_sub (intervalIntegrable_lineT_all (hmi n) s t)
      (intervalIntegrable_lineT_all hg s t)]
    exact abs_integral_lineT_le (h := fun y => moll n g y - g y) ((hmi n).sub hg) hs ht
  have hlim : Tendsto (fun n => ∫ y, |moll n g y - g y| ∂haar 1) atTop (𝓝 0) := by
    have h0 := tendsto_moll hg
    have h1 : Tendsto (fun n => (∫⁻ y, ‖moll n g y - g y‖ₑ).toReal) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
    refine h1.congr fun n => ?_
    have := integral_norm_eq_lintegral_enorm ((hmi n).sub hg).aestronglyMeasurable
    simpa [Real.norm_eq_abs] using this.symm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  simpa [Real.norm_eq_abs] using hbd n


/-- Key identity: for a.e. pair of points, `f x - f y = ∫_{secT y}^{secT x} g ∘ lineT`. -/
theorem exists_good_set {f g : Torus 1 → ℝ} (hw : IsWeakGrad f (fun y _ => g y))
    (hf : Integrable f (haar 1)) (hg : Integrable g (haar 1)) :
    ∃ G : Set (Torus 1), (∀ᵐ y ∂haar 1, y ∈ G) ∧ ∀ x ∈ G, ∀ y ∈ G,
      f x - f y = ∫ r in secT y 0..secT x 0, g (lineT r) := by
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_of_tendsto_lintegral
    (fun n => (measurable_moll n hf).aestronglyMeasurable) hf.aestronglyMeasurable
    (tendsto_moll hf)
  refine ⟨{y | Tendsto (fun k => moll (ns k) f y) atTop (𝓝 (f y))}, hae, ?_⟩
  intro x hx y hy
  have h1 : Tendsto (fun k => moll (ns k) f (lineT (secT x 0)) - moll (ns k) f (lineT (secT y 0)))
      atTop (𝓝 (f x - f y)) := by
    rw [lineT_secT, lineT_secT]; exact hx.sub hy
  have h2 : Tendsto (fun k => ∫ r in secT y 0..secT x 0, moll (ns k) g (lineT r)) atTop
      (𝓝 (∫ r in secT y 0..secT x 0, g (lineT r))) :=
    (tendsto_moll_integral hg (secT_mem_Icc y) (secT_mem_Icc x)).comp hns.tendsto_atTop
  refine tendsto_nhds_unique h1 (h2.congr fun k => ?_)
  rw [moll_sub_eq_integral hw hf]

theorem exists_continuous_rep {f g : Torus 1 → ℝ} (hw : IsWeakGrad f (fun y _ => g y))
    (hf : Integrable f (haar 1)) (hg : Integrable g (haar 1)) :
    ∃ F : ℝ → ℝ, Continuous F ∧ Function.Periodic F 1 ∧
      (∀ s t, F t - F s = ∫ r in s..t, g (lineT r)) ∧
      (∀ᵐ y ∂haar 1, f y = F (secT y 0)) ∧ ∀ᵐ r : ℝ, f (lineT r) = F r := by
  obtain ⟨G, hG, hGp⟩ := exists_good_set hw hf hg
  obtain ⟨y0, hy0⟩ := hG.exists
  set b0 := secT y0 0 with hb0
  set F : ℝ → ℝ := fun t => f y0 + ∫ r in b0..t, g (lineT r) with hF
  have hint := intervalIntegrable_lineT_all hg
  have hdiff : ∀ s t, F t - F s = ∫ r in s..t, g (lineT r) := by
    intro s t
    simp only [hF]
    rw [add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _)]
  have hcont : Continuous F :=
    continuous_const.add (intervalIntegral.continuous_primitive hint b0)
  have hper : Function.Periodic F 1 := by
    intro t
    have h1 := hdiff t (t + 1)
    have h2 : ∫ r in t..t + 1, g (lineT r) = 0 := by
      have hp := (periodic_lineT.comp g).intervalIntegral_add_eq t 0
      simp only [Function.comp_apply, zero_add] at hp
      rw [hp, intervalIntegral_lineT hg.aestronglyMeasurable]
      exact integral_weakGrad_eq_zero hw hf (fun _ => hg) 0
    linarith
  have hae : ∀ᵐ y ∂haar 1, f y = F (secT y 0) := by
    filter_upwards [hG] with x hx
    have := hGp x hx y0 hy0
    simp only [hF, hb0]
    linarith
  refine ⟨F, hcont, hper, hdiff, hae, ?_⟩
  filter_upwards [ae_real_of_ae_torus hae] with r hr
  obtain ⟨m, hm⟩ := secT_lineT_sub r
  rw [hr, hm]
  simpa using hper.int_mul m r


/-! ### Smooth tests give weak derivatives -/

/-- `cos(2π k x)` on the circle, through the section `secT`. -/
noncomputable def cosK (k : ℤ) (y : Torus 1) : ℝ := Real.cos (2 * π * k * secT y 0)

/-- `sin(2π k x)` on the circle. -/
noncomputable def sinK (k : ℤ) (y : Torus 1) : ℝ := Real.sin (2 * π * k * secT y 0)

theorem secT_liftT_zero (z : Fin 1 → ℝ) : ∃ m : ℤ, secT (liftT z) 0 = z 0 + m := by
  obtain ⟨m, hm⟩ := secT_liftT_eq z
  refine ⟨m 0, ?_⟩
  have := congrFun hm 0
  simpa [intVec] using this

theorem cosK_lift (k : ℤ) : cosK k ∘ liftT = fun z : Fin 1 → ℝ => Real.cos (2 * π * k * z 0) := by
  funext z
  obtain ⟨m, hm⟩ := secT_liftT_zero z
  simp only [Function.comp, cosK, hm]
  rw [show 2 * π * k * (z 0 + m) = 2 * π * k * z 0 + ((k * m : ℤ) : ℝ) * (2 * π) by push_cast; ring]
  exact Real.cos_add_int_mul_two_pi _ _

theorem sinK_lift (k : ℤ) : sinK k ∘ liftT = fun z : Fin 1 → ℝ => Real.sin (2 * π * k * z 0) := by
  funext z
  obtain ⟨m, hm⟩ := secT_liftT_zero z
  simp only [Function.comp, sinK, hm]
  rw [show 2 * π * k * (z 0 + m) = 2 * π * k * z 0 + ((k * m : ℤ) : ℝ) * (2 * π) by push_cast; ring]
  exact Real.sin_add_int_mul_two_pi _ _

theorem isSmoothT_cosK (k : ℤ) : IsSmoothT (cosK k) := by
  unfold IsSmoothT
  rw [cosK_lift]
  exact (Real.contDiff_cos.comp (contDiff_const.mul (contDiff_apply ℝ ℝ 0))).of_le le_top

theorem isSmoothT_sinK (k : ℤ) : IsSmoothT (sinK k) := by
  unfold IsSmoothT
  rw [sinK_lift]
  exact (Real.contDiff_sin.comp (contDiff_const.mul (contDiff_apply ℝ ℝ 0))).of_le le_top

theorem dpart_cosK (k : ℤ) (y : Torus 1) :
    dpart_appA (cosK k) 0 y = -(2 * π * k) * sinK k y := by
  unfold dpart_appA
  have hd : HasDerivAt (fun t : ℝ => (cosK k ∘ liftT) (secT y + t • (Pi.single 0 1 : Fin 1 → ℝ)))
      (-(2 * π * k) * Real.sin (2 * π * k * secT y 0)) 0 := by
    rw [cosK_lift]
    have := (((hasDerivAt_id (0 : ℝ)).const_add (secT y 0)).const_mul (2 * π * k)).cos
    convert this using 1
    · funext t; simp
    · simp; ring
  rw [fderiv_apply_of_line ((isSmoothT_cosK k).differentiable (by simp) (secT y)) hd]
  rfl

theorem dpart_sinK (k : ℤ) (y : Torus 1) :
    dpart_appA (sinK k) 0 y = (2 * π * k) * cosK k y := by
  unfold dpart_appA
  have hd : HasDerivAt (fun t : ℝ => (sinK k ∘ liftT) (secT y + t • (Pi.single 0 1 : Fin 1 → ℝ)))
      ((2 * π * k) * Real.cos (2 * π * k * secT y 0)) 0 := by
    rw [sinK_lift]
    have := (((hasDerivAt_id (0 : ℝ)).const_add (secT y 0)).const_mul (2 * π * k)).sin
    convert this using 1
    · funext t; simp
    · simp; ring
  rw [fderiv_apply_of_line ((isSmoothT_sinK k).differentiable (by simp) (secT y)) hd]
  rfl

theorem abs_cosK_le (k : ℤ) (y : Torus 1) : |cosK k y| ≤ 1 := Real.abs_cos_le_one _
theorem abs_sinK_le (k : ℤ) (y : Torus 1) : |sinK k y| ≤ 1 := Real.abs_sin_le_one _

theorem measurable_cosK (k : ℤ) : Measurable (cosK k) :=
  Real.measurable_cos.comp ((measurable_const.mul (measurable_secT.eval (a := 0))))

theorem measurable_sinK (k : ℤ) : Measurable (sinK k) :=
  Real.measurable_sin.comp ((measurable_const.mul (measurable_secT.eval (a := 0))))

theorem cf_eq_cosK_sinK {f : Torus 1 → ℝ} (hf : Integrable f (haar 1)) (k : ℤ) :
    cf f (fun _ => k) = ((∫ y, f y * cosK k y : ℝ) : ℂ) - Complex.I * ((∫ y, f y * sinK k y : ℝ) : ℂ) := by
  have hc : Integrable (fun y => f y * cosK k y) (haar 1) :=
    hf.mul_bdd (measurable_cosK k).aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact abs_cosK_le k y)
  have hs : Integrable (fun y => f y * sinK k y) (haar 1) :=
    hf.mul_bdd (measurable_sinK k).aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact abs_sinK_le k y)
  have hpt : ∀ y : Torus 1, mFourier (-(fun _ : Fin 1 => k)) y • (f y : ℂ) =
      ((f y * cosK k y : ℝ) : ℂ) - Complex.I * ((f y * sinK k y : ℝ) : ℂ) := by
    intro y
    have h1 : mFourier (-(fun _ : Fin 1 => k)) y =
        Complex.exp (-(2 * π * Complex.I * (k * secT y 0 : ℝ))) := by
      conv_lhs => rw [← liftT_secT y]
      rw [mFourier_liftT]
      congr 1
      simp
    have h2 : Complex.exp (-(2 * (π : ℂ) * Complex.I * ((k * secT y 0 : ℝ) : ℂ))) =
        Complex.exp (((-(2 * π * k * secT y 0) : ℝ) : ℂ) * Complex.I) := by
      congr 1; push_cast; ring
    rw [h1, h2, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg, smul_eq_mul]
    simp only [cosK, sinK]
    push_cast
    ring
  unfold cf
  rw [mFourierCoeff_eq_integral]
  simp_rw [hpt]
  rw [integral_sub hc.ofReal (hs.ofReal.const_mul _), integral_const_mul,
    integral_complex_ofReal, integral_complex_ofReal]

theorem isWeakGrad_of_smooth_tests {f g : Torus 1 → ℝ} (hf : MemLp f 2 (haar 1))
    (hg : MemLp g 2 (haar 1))
    (h : ∀ φ : Torus 1 → ℝ, IsSmoothT φ →
      ∫ y, f y * dpart_appA φ 0 y = -∫ y, g y * φ y) :
    IsWeakGrad f (fun y _ => g y) := by
  have hfi : Integrable f (haar 1) := hf.integrable one_le_two
  have hgi : Integrable g (haar 1) := hg.integrable one_le_two
  refine isWeakGrad_of_cf hf (fun _ => hg) ?_
  intro j n
  have hn : n = fun _ => n 0 := by funext i; rw [Subsingleton.elim i 0]
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  rw [hn]
  simp only
  set k := n 0
  have hc := h (cosK k) (isSmoothT_cosK k)
  have hs := h (sinK k) (isSmoothT_sinK k)
  simp_rw [dpart_cosK, dpart_sinK] at hc hs
  have e1 : ∫ y, f y * (-(2 * π * k) * sinK k y) = -(2 * π * k) * ∫ y, f y * sinK k y := by
    rw [← integral_const_mul]; congr 1; funext y; ring
  have e2 : ∫ y, f y * ((2 * π * k) * cosK k y) = (2 * π * k) * ∫ y, f y * cosK k y := by
    rw [← integral_const_mul]; congr 1; funext y; ring
  rw [e1] at hc
  rw [e2] at hs
  rw [cf_eq_cosK_sinK hgi, cf_eq_cosK_sinK hfi]
  have hc' : ∫ y, g y * cosK k y = 2 * π * k * ∫ y, f y * sinK k y := by linarith
  have hs' : ∫ y, g y * sinK k y = -(2 * π * k * ∫ y, f y * cosK k y) := by linarith
  rw [hc', hs']
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring


theorem isWeakGrad_zero_of_memH1 {u : Torus 1 → ℝ} (hu : MemH1 (haar 1) u) :
    IsWeakGrad u (fun y _ => weakGrad u y 0) := by
  have h := isWeakGrad_weakGrad hu.1
  have e : weakGrad u = fun y _ => weakGrad u y 0 := by
    funext y i; rw [Subsingleton.elim i 0]
  rw [e] at h
  exact h

theorem integrable_weakGrad_zero {u : Torus 1 → ℝ} (hu : MemH1 (haar 1) u) :
    Integrable (fun y => weakGrad u y 0) (haar 1) :=
  (memLp_weakGrad_zero hu).integrable one_le_two

/-- Continuous representative of an `H¹(𝕋)` function. -/
theorem exists_continuous_rep_memH1 {u : Torus 1 → ℝ} (hu : MemH1 (haar 1) u) :
    ∃ F : ℝ → ℝ, Continuous F ∧ Function.Periodic F 1 ∧
      (∀ s t, F t - F s = ∫ r in s..t, weakGrad u (lineT r) 0) ∧
      (∀ᵐ y ∂haar 1, u y = F (secT y 0)) ∧ ∀ᵐ r : ℝ, u (lineT r) = F r :=
  exists_continuous_rep (isWeakGrad_zero_of_memH1 hu) (hu.2.1.integrable one_le_two)
    (integrable_weakGrad_zero hu)




/-- Smooth approximation of `|·|`. -/
noncomputable def absApprox (j : ℕ) (s : ℝ) : ℝ := Real.sqrt (s ^ 2 + (1 / ((j : ℝ) + 1)) ^ 2)

private lemma absApprox_pos (j : ℕ) (s : ℝ) : 0 < s ^ 2 + (1 / ((j : ℝ) + 1)) ^ 2 := by
  have : 0 < (1 / ((j : ℝ) + 1)) ^ 2 := by positivity
  positivity

lemma absApprox_contDiff (j : ℕ) : ContDiff ℝ 1 (absApprox j) := by
  unfold absApprox
  refine ContDiff.sqrt (by fun_prop) fun s => (absApprox_pos j s).ne'

lemma absApprox_hasDerivAt (j : ℕ) (s : ℝ) :
    HasDerivAt (absApprox j) (s / Real.sqrt (s ^ 2 + (1 / ((j : ℝ) + 1)) ^ 2)) s := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + (1 / ((j : ℝ) + 1)) ^ 2) (2 * s) s := by
    simpa using ((hasDerivAt_pow 2 s).add_const ((1 / ((j : ℝ) + 1)) ^ 2))
  have h2 := h1.sqrt (absApprox_pos j s).ne'
  have hs : 0 < Real.sqrt (s ^ 2 + (1 / ((j : ℝ) + 1)) ^ 2) := Real.sqrt_pos.mpr (absApprox_pos j s)
  have e : absApprox j = fun y => Real.sqrt (y ^ 2 + (1 / ((j : ℝ) + 1)) ^ 2) := rfl
  rw [e]
  convert h2 using 1
  field_simp

lemma absApprox_deriv (j : ℕ) (s : ℝ) :
    deriv (absApprox j) s = s / Real.sqrt (s ^ 2 + (1 / ((j : ℝ) + 1)) ^ 2) :=
  (absApprox_hasDerivAt j s).deriv

lemma absApprox_deriv_abs_le (j : ℕ) (t : ℝ) : |deriv (absApprox j) t| ≤ 1 := by
  rw [absApprox_deriv]
  have hs : 0 < Real.sqrt (t ^ 2 + (1 / ((j : ℝ) + 1)) ^ 2) :=
    Real.sqrt_pos.mpr (absApprox_pos j t)
  rw [abs_div, abs_of_pos hs, div_le_one hs]
  exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (1 / ((j : ℝ) + 1))])

lemma absApprox_unif {ε : ℝ} (hε : 0 < ε) : ∀ᶠ j : ℕ in atTop, ∀ t, abs (absApprox j t - |t|) ≤ ε := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  filter_upwards [h.eventually (Iic_mem_nhds hε)] with j hj t
  have hj' : 1 / ((j : ℝ) + 1) ≤ ε := hj
  have h0 : 0 ≤ 1 / ((j : ℝ) + 1) := by positivity
  have hA : |t| ≤ absApprox j t := by
    unfold absApprox
    exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (1 / ((j : ℝ) + 1))])
  have hB : absApprox j t ≤ |t| + 1 / ((j : ℝ) + 1) := by
    unfold absApprox
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_abs t, abs_nonneg t]
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- The sign function `s / |s|` (with value `0` at `0`). -/
noncomputable def sgn (s : ℝ) : ℝ := s / |s|

lemma sgn_measurable : Measurable sgn := measurable_id.div measurable_id.abs

lemma sgn_abs_le (s : ℝ) : |sgn s| ≤ 1 := by
  unfold sgn
  rw [abs_div, abs_abs]
  rcases eq_or_ne |s| 0 with h | h
  · rw [h]; simp
  · rw [div_self h]

lemma absApprox_tendsto (t : ℝ) :
    Tendsto (fun j => deriv (absApprox j) t) atTop (𝓝 (sgn t)) := by
  simp_rw [absApprox_deriv]
  rcases eq_or_ne t 0 with h | h
  · subst h; simp [sgn]
  · have h1 : Tendsto (fun j : ℕ => t ^ 2 + (1 / ((j : ℝ) + 1)) ^ 2) atTop (𝓝 (t ^ 2 + 0 ^ 2)) :=
      tendsto_const_nhds.add ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2)
    have h2 := (Real.continuous_sqrt.tendsto _).comp h1
    have h3 : Real.sqrt (t ^ 2 + 0 ^ 2) = |t| := by simp [Real.sqrt_sq_eq_abs]
    rw [h3] at h2
    have := (tendsto_const_nhds (x := t)).div h2 (abs_ne_zero.mpr h)
    exact this

theorem isWeakGrad_abs {w : Torus 1 → ℝ} {g : Torus 1 → Fin 1 → ℝ}
    (h : IsWeakGrad w g) (hw : Integrable w (haar 1)) (hg : ∀ k, Integrable (fun y => g y k) (haar 1)) :
    IsWeakGrad (fun y => |w y|) (fun y k => sgn (w y) * g y k) :=
  isWeakGrad_comp_limit h hw hg (fun j => absApprox_contDiff j) (L := 1)
    (fun j t => absApprox_deriv_abs_le j t) continuous_abs sgn_measurable
    (fun _ hε => absApprox_unif hε) absApprox_tendsto

theorem memH1_abs_div {w : Torus 1 → ℝ} (hw : MemH1 (haar 1) w) {c : ℝ} (hc : 0 < c) :
    MemH1 (haar 1) (fun x => |w x| / c) ∧
    (∀ᵐ x ∂(haar 1), weakGrad (fun y => |w y| / c) x 0 ^ 2 ≤ weakGrad w x 0 ^ 2 / c ^ 2) := by
  have : IsProbabilityMeasure (haar 1) := haar_isProbabilityMeasure 1
  have h := isWeakGrad_weakGrad hw.1
  have hwi : Integrable w (haar 1) := hw.2.1.integrable (by norm_num)
  have hgL := memLp_weakGrad_zero hw
  have hgi : ∀ k : Fin 1, Integrable (fun y => weakGrad w y k) (haar 1) := by
    intro k
    have : k = 0 := Subsingleton.elim _ _
    subst this
    exact hgL.integrable (by norm_num)
  have h1 := isWeakGrad_abs h hwi hgi
  have h2 := h1.cmul c⁻¹
  have e1 : (fun y => c⁻¹ * |w y|) = fun y => |w y| / c := by
    funext y; rw [div_eq_inv_mul]
  rw [e1] at h2
  have hae := weakGrad_ae_eq h2
  have hbd : ∀ᵐ x ∂(haar 1), |weakGrad (fun y => |w y| / c) x 0| ≤ c⁻¹ * |weakGrad w x 0| := by
    filter_upwards [hae] with x hx
    rw [hx]
    show |c⁻¹ * (sgn (w x) * weakGrad w x 0)| ≤ _
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hc)]
    gcongr
    calc |sgn (w x)| * |weakGrad w x 0| ≤ 1 * |weakGrad w x 0| := by
          gcongr; exact sgn_abs_le _
      _ = _ := one_mul _
  have hwc := hw.2.1.const_mul c⁻¹
  have hsq : ∀ x, Real.sqrt (sqNorm (weakGrad (fun y => |w y| / c) x)) =
      |weakGrad (fun y => |w y| / c) x 0| := by
    intro x
    simp [sqNorm, Real.sqrt_sq_eq_abs]
  refine ⟨⟨⟨_, h2⟩, ?_, ?_⟩, ?_⟩
  · refine MemLp.of_le hwc h2.aestronglyMeasurable_fun (Eventually.of_forall fun x => le_of_eq ?_)
    simp only [Real.norm_eq_abs, abs_div, abs_abs, abs_mul, abs_of_pos hc, abs_of_pos (inv_pos.mpr hc)]
    rw [div_eq_inv_mul]
  · have hg2 := hgL.const_mul c⁻¹
    refine MemLp.of_le hg2.norm ?_ ?_
    · exact Real.continuous_sqrt.comp_aestronglyMeasurable
        (isWeakGrad_weakGrad (u := fun y => |w y| / c) ⟨_, h2⟩).aestronglyMeasurable_sqNorm
    · filter_upwards [hbd] with x hx
      rw [hsq x]
      simp only [Real.norm_eq_abs, abs_abs, abs_mul, abs_of_pos (inv_pos.mpr hc)]
      exact hx
  · filter_upwards [hbd] with x hx
    have h3 : weakGrad (fun y => |w y| / c) x 0 ^ 2 ≤ (c⁻¹ * |weakGrad w x 0|) ^ 2 := by
      rw [← sq_abs (weakGrad (fun y => |w y| / c) x 0)]
      exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    calc weakGrad (fun y => |w y| / c) x 0 ^ 2 ≤ (c⁻¹ * |weakGrad w x 0|) ^ 2 := h3
      _ = weakGrad w x 0 ^ 2 / c ^ 2 := by rw [mul_pow, sq_abs]; field_simp


end SharpLSI.FL.Ex.Reg
