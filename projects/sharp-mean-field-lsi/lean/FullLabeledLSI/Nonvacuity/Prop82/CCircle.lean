import SharpSymmetricLSI.Paper.CircleSobolev
import SharpSymmetricLSI.Paper.CircleLSIExt
import SharpSymmetricLSI.Paper.AppAPos5
import SharpSymmetricLSI.Paper.FourierSynth
import SharpSymmetricLSI.Paper.CosineExpansion

/-!
# Lane C, module C1: `H¹(𝕋)` has a continuous representative

For `f ∈ L¹(𝕋)` with weak derivative `g ∈ L¹(𝕋)` there is a continuous `1`-periodic
`F : ℝ → ℝ` with `F t - F s = ∫_s^t g(lineT r) dr` and `f = F ∘ secT` almost everywhere
(`exists_continuous_rep`). The proof mollifies: for smooth periodic functions the formula is the
fundamental theorem of calculus, and both sides pass to the limit along an a.e. convergent
subsequence.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Prop82

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

end SharpLSI.FL.Prop82
