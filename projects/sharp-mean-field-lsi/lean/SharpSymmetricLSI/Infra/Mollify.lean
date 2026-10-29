import SharpSymmetricLSI.Infra.Periodic
import SharpSymmetricLSI.Infra.SmoothWeakGrad

/-!
# Mollification of periodic functions (Phase 2, I1, milestone 1)

`φ_n` is a normalized smooth bump on `ℝ^ι` with support radius `2/(n+2) → 0`. For a torus function
`u`, `moll n u` is the torus function whose lift is `φ_n ⋆ (u ∘ liftT)`. It is smooth, periodic,
the mollification of a weak gradient is the gradient of the mollification
(`fderiv_mollL_of_isWeakGrad`), it is an `L¹(m)` contraction (`lintegral_moll_le`), and
`moll n u → u` in `L¹(m)` (`tendsto_moll`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Convolution

namespace SharpLSI

variable {ι : Type*} [Fintype ι]

/-- The bump functions `φ_n`, `rIn = 1/(n+2)`, `rOut = 2/(n+2)`. -/
noncomputable def bumpSeq (n : ℕ) : ContDiffBump (0 : ι → ℝ) where
  rIn := 1 / (n + 2)
  rOut := 2 / (n + 2)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : (0 : ℝ) < n + 2 := by positivity
    rw [div_lt_div_iff_of_pos_right this]; norm_num

/-- The normalized bump `φ_n`. -/
noncomputable def phiSeq (n : ℕ) : (ι → ℝ) → ℝ := (bumpSeq (ι := ι) n).normed volume

theorem phiSeq_nonneg (n : ℕ) (x : ι → ℝ) : 0 ≤ phiSeq n x := ContDiffBump.nonneg_normed _ x

theorem integral_phiSeq (n : ℕ) : ∫ x, phiSeq (ι := ι) n x = 1 := ContDiffBump.integral_normed _

theorem hasCompactSupport_phiSeq (n : ℕ) : HasCompactSupport (phiSeq (ι := ι) n) :=
  ContDiffBump.hasCompactSupport_normed _

theorem contDiff_phiSeq (n : ℕ) : ContDiff ℝ ∞ (phiSeq (ι := ι) n) := ContDiffBump.contDiff_normed _

theorem tendsto_rOut_bumpSeq : Tendsto (fun n => (bumpSeq (ι := ι) n).rOut) atTop (𝓝 0) := by
  have : Tendsto (fun n : ℕ => (2 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    have h := tendsto_const_nhds (x := (2 : ℝ)).div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    exact h
  exact this

/-- Mollification on `ℝ^ι`: `(F ⋆ φ_n)(x) = ∫ F(t) φ_n(x - t) dt`. -/
noncomputable def mollL (n : ℕ) (F : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  (F ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] phiSeq n : (ι → ℝ) → ℝ)

theorem mollL_apply (n : ℕ) (F : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    mollL n F x = ∫ t, F t * phiSeq n (x - t) := rfl

/-- The other form `∫ φ_n(s) F(x - s) ds`. -/
theorem mollL_apply' (n : ℕ) (F : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    mollL n F x = ∫ s, phiSeq n s * F (x - s) := by
  rw [mollL_apply, ← integral_sub_left_eq_self (fun t => F t * phiSeq n (x - t)) volume x]
  simp only [sub_sub_cancel]
  congr 1; funext s; ring

theorem contDiff_mollL (n : ℕ) {F : (ι → ℝ) → ℝ} (hF : LocallyIntegrable F volume) :
    ContDiff ℝ ∞ (mollL n F) :=
  (hasCompactSupport_phiSeq n).contDiff_convolution_right _ hF (contDiff_phiSeq n)

/-- Mollification of a periodic function is periodic. -/
theorem mollL_comp_liftT_add (n : ℕ) (u : UnitAddTorus ι → ℝ) (x : ι → ℝ) (m : ι → ℤ) :
    mollL n (u ∘ liftT) (x + intVec m) = mollL n (u ∘ liftT) x := by
  simp only [mollL_apply', Function.comp]
  congr 1; funext t
  rw [show x + intVec m - t = (x - t) + intVec m by abel, liftT_add_intVec]

/-- The derivative of a mollification is the mollification of the weak gradient. -/
theorem fderiv_mollL_of_isWeakGrad [DecidableEq ι] {f : UnitAddTorus ι → ℝ}
    {g : UnitAddTorus ι → ι → ℝ} (h : IsWeakGrad f g) (n : ℕ) (x : ι → ℝ) (k : ι) :
    fderiv ℝ (mollL n (f ∘ liftT)) x (Pi.single k 1) = mollL n (fun z => g (liftT z) k) x := by
  have hd := (hasCompactSupport_phiSeq (ι := ι) n).hasFDerivAt_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) h.locInt ((contDiff_phiSeq n).of_le (by simp)) x
  rw [show mollL n (f ∘ liftT) = (f ∘ liftT ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] phiSeq n)
    from rfl, hd.fderiv, convolution_precompR_apply _ h.locInt
    ((hasCompactSupport_phiSeq n).fderiv (𝕜 := ℝ))
    ((contDiff_phiSeq n).continuous_fderiv (by simp)) x (Pi.single k 1)]
  -- the test function `ψ(t) = φ_n(x - t)`
  set ψ : (ι → ℝ) → ℝ := fun t => phiSeq n (x - t) with hψ
  have hψs : ContDiff ℝ ∞ ψ := (contDiff_phiSeq n).comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := by
    have := (hasCompactSupport_phiSeq (ι := ι) n).comp_homeomorph (Homeomorph.subLeft x)
    exact this
  have hψd : ∀ t, fderiv ℝ ψ t (Pi.single k 1) = -fderiv ℝ (phiSeq n) (x - t) (Pi.single k 1) := by
    intro t
    have h1 : HasFDerivAt (fun t : ι → ℝ => x - t) (-ContinuousLinearMap.id ℝ (ι → ℝ)) t := by
      simpa using (hasFDerivAt_id (𝕜 := ℝ) t).const_sub x
    have h2 := (((contDiff_phiSeq (ι := ι) n).differentiable (by simp)) (x - t)).hasFDerivAt.comp t h1
    rw [show ψ = phiSeq n ∘ HSub.hSub x from rfl, h2.fderiv]; simp
  have hibp := h.ibp ψ hψs hψc k
  simp_rw [hψd, mul_neg, integral_neg, neg_inj] at hibp
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  exact hibp

omit [Fintype ι] in
theorem secT_liftT_eq (x : ι → ℝ) : ∃ m : ι → ℤ, secT (liftT x) = x + intVec m := by
  have h : ∀ i, ∃ n : ℤ, (n : ℝ) = secT (liftT x) i - x i := by
    intro i
    have h0 : ((secT (liftT x) i - x i : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub]
      have := congrFun (liftT_secT (liftT x)) i
      simp only [liftT] at this
      rw [this]; simp [liftT]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h0
    exact ⟨n, by simpa using hn⟩
  choose m hm using h
  exact ⟨m, by funext i; simp [intVec, hm]⟩

/-- The torus mollification `moll n u`, with lift `φ_n ⋆ (u ∘ liftT)`. -/
noncomputable def moll (n : ℕ) (u : UnitAddTorus ι → ℝ) : UnitAddTorus ι → ℝ :=
  fun y => mollL n (u ∘ liftT) (secT y)

theorem moll_comp_liftT (n : ℕ) (u : UnitAddTorus ι → ℝ) :
    moll n u ∘ liftT = mollL n (u ∘ liftT) := by
  funext x
  obtain ⟨m, hm⟩ := secT_liftT_eq x
  simp only [Function.comp, moll, hm, mollL_comp_liftT_add]

/-! ### `L¹` contraction -/

theorem continuous_liftT : Continuous (liftT (ι := ι)) :=
  continuous_pi fun i => (continuous_quotient_mk').comp (continuous_apply i)

theorem lintegral_unitBox_sub {H : UnitAddTorus ι → ℝ≥0∞} (hH : Measurable H) (s : ι → ℝ) :
    ∫⁻ x in unitBox ι, H (liftT (x - s)) = ∫⁻ y, H y := by
  have : (volume : Measure (UnitAddTorus ι)).IsAddRightInvariant := Measure.pi.isAddRightInvariant _
  simp_rw [liftT_sub]
  rw [show (∫⁻ x in unitBox ι, H (liftT x - liftT s)) = ∫⁻ y, H (y - liftT s) from
    (measurePreserving_liftT (ι := ι)).lintegral_comp (f := fun y => H (y - liftT s))
      (hH.comp (measurable_sub_const _))]
  exact lintegral_sub_right_eq_self _ _

theorem enorm_mollL_le (n : ℕ) (F : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    ‖mollL n F x‖ₑ ≤ ∫⁻ s, ENNReal.ofReal (phiSeq n s) * ‖F (x - s)‖ₑ := by
  rw [mollL_apply']
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  refine lintegral_congr fun s => ?_
  rw [enorm_mul, Real.enorm_of_nonneg (phiSeq_nonneg n s)]

theorem lintegral_ofReal_phiSeq (n : ℕ) : ∫⁻ s, ENNReal.ofReal (phiSeq (ι := ι) n s) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (f := phiSeq (ι := ι) n)
    (ContDiffBump.integrable_normed _) (Eventually.of_forall (phiSeq_nonneg n)), integral_phiSeq,
    ENNReal.ofReal_one]

theorem measurable_moll (n : ℕ) {u : UnitAddTorus ι → ℝ} (hu : Integrable u volume) :
    Measurable (moll n u) :=
  (contDiff_mollL n (locallyIntegrable_comp_liftT hu)).continuous.measurable.comp measurable_secT

/-- Mollification is an `L¹(m)` contraction (measurable case). -/
theorem lintegral_moll_le_of_measurable (n : ℕ) {u : UnitAddTorus ι → ℝ} (hu : Measurable u)
    (hi : Integrable u volume) : ∫⁻ y, ‖moll n u y‖ₑ ≤ ∫⁻ y, ‖u y‖ₑ := by
  have hU : Measurable (u ∘ liftT) := hu.comp measurable_liftT
  rw [← (measurePreserving_liftT (ι := ι)).lintegral_comp (measurable_moll n hi).enorm]
  simp_rw [show ∀ x, moll n u (liftT x) = mollL n (u ∘ liftT) x from
    fun x => congrFun (moll_comp_liftT n u) x]
  have hmeas : Measurable (Function.uncurry fun (x s : ι → ℝ) =>
      ENNReal.ofReal (phiSeq n s) * ‖(u ∘ liftT) (x - s)‖ₑ) :=
    (ENNReal.measurable_ofReal.comp ((contDiff_phiSeq n).continuous.measurable.comp
      measurable_snd)).mul (hU.comp (measurable_fst.sub measurable_snd)).enorm
  calc ∫⁻ x in unitBox ι, ‖mollL n (u ∘ liftT) x‖ₑ
      ≤ ∫⁻ x in unitBox ι, ∫⁻ s, ENNReal.ofReal (phiSeq n s) * ‖(u ∘ liftT) (x - s)‖ₑ :=
        lintegral_mono fun x => enorm_mollL_le n _ x
    _ = ∫⁻ s, ∫⁻ x in unitBox ι, ENNReal.ofReal (phiSeq n s) * ‖(u ∘ liftT) (x - s)‖ₑ :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ s, ENNReal.ofReal (phiSeq n s) * ∫⁻ y, ‖u y‖ₑ := by
        refine lintegral_congr fun s => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_unitBox_sub hu.enorm s
    _ = ∫⁻ y, ‖u y‖ₑ := by
        rw [lintegral_mul_const' _ _ hi.2.ne, lintegral_ofReal_phiSeq, one_mul]

/-- Mollification only depends on the a.e. class. -/
theorem moll_congr_ae (n : ℕ) {u v : UnitAddTorus ι → ℝ} (h : u =ᵐ[volume] v) :
    moll n u = moll n v := by
  funext y
  simp only [moll, mollL_apply]
  refine integral_congr_ae ?_
  filter_upwards [ae_liftT_of_ae h] with t ht
  show u (liftT t) * _ = v (liftT t) * _
  rw [ht]

/-- Mollification is an `L¹(m)` contraction. -/
theorem lintegral_moll_le (n : ℕ) {u : UnitAddTorus ι → ℝ} (hi : Integrable u volume) :
    ∫⁻ y, ‖moll n u y‖ₑ ≤ ∫⁻ y, ‖u y‖ₑ := by
  set v := hi.aestronglyMeasurable.mk u with hv
  have huv : u =ᵐ[volume] v := hi.aestronglyMeasurable.ae_eq_mk
  rw [moll_congr_ae n huv]
  calc ∫⁻ y, ‖moll n v y‖ₑ ≤ ∫⁻ y, ‖v y‖ₑ :=
        lintegral_moll_le_of_measurable n
          hi.aestronglyMeasurable.stronglyMeasurable_mk.measurable (hi.congr huv)
    _ = ∫⁻ y, ‖u y‖ₑ := (lintegral_congr_ae (huv.mono fun y hy => by simp [hy])).symm

theorem moll_sub (n : ℕ) {u v : UnitAddTorus ι → ℝ} (hu : Integrable u volume)
    (hv : Integrable v volume) (y : UnitAddTorus ι) :
    moll n (fun z => u z - v z) y = moll n u y - moll n v y := by
  simp only [moll, mollL_apply, Function.comp]
  have iu := ((hasCompactSupport_phiSeq n).convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
    (locallyIntegrable_comp_liftT hu) (contDiff_phiSeq n).continuous (secT y)).integrable
  have iv := ((hasCompactSupport_phiSeq n).convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
    (locallyIntegrable_comp_liftT hv) (contDiff_phiSeq n).continuous (secT y)).integrable
  have iu' : Integrable (fun t => u (liftT t) * phiSeq n (secT y - t)) volume := iu
  have iv' : Integrable (fun t => v (liftT t) * phiSeq n (secT y - t)) volume := iv
  rw [← integral_sub iu' iv']
  congr 1; funext t
  ring

/-! ### Convergence -/

/-- For continuous `h`, `moll n h → h` uniformly. -/
theorem moll_uniform_of_continuous {h : UnitAddTorus ι → ℝ} (hc : Continuous h) {δ : ℝ}
    (hδ : 0 < δ) : ∀ᶠ n in atTop, ∀ y, dist (moll n h y) (h y) ≤ δ := by
  have hlift : UniformContinuous (liftT (ι := ι)) := by
    let L : (ι → ℝ) →+ UnitAddTorus ι :=
      { toFun := liftT, map_zero' := by funext i; simp [liftT],
        map_add' := liftT_add }
    exact L.uniformContinuous_of_continuousAt_zero continuous_liftT.continuousAt
  have hH : UniformContinuous (h ∘ liftT) :=
    (CompactSpace.uniformContinuous_of_continuous hc).comp hlift
  obtain ⟨r, hr, hrH⟩ := Metric.uniformContinuous_iff.mp hH δ hδ
  have hev : ∀ᶠ n in atTop, (bumpSeq (ι := ι) n).rOut < r :=
    (tendsto_order.mp tendsto_rOut_bumpSeq).2 r hr
  filter_upwards [hev] with n hn y
  have e1 : moll n h y = ((bumpSeq (ι := ι) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      volume] (h ∘ liftT) : (ι → ℝ) → ℝ) (secT y) := by
    rw [moll, mollL_apply', convolution_lsmul]; rfl
  have e2 : h y = (h ∘ liftT) (secT y) := by simp [Function.comp, liftT_secT]
  rw [e1, e2]
  refine ContDiffBump.dist_normed_convolution_le (hc.comp continuous_liftT).aestronglyMeasurable
    fun x hx => (hrH ?_).le
  exact lt_trans (Metric.mem_ball.mp hx) hn

/-- `moll n u → u` in `L¹(m)`. -/
theorem tendsto_moll {u : UnitAddTorus ι → ℝ} (hu : Integrable u volume) :
    Tendsto (fun n => ∫⁻ y, ‖moll n u y - u y‖ₑ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : ε / 3 ≠ 0 := by simp [hε.ne']
  obtain ⟨h, hh, -⟩ := (memLp_one_iff_integrable.mpr hu).exists_boundedContinuous_eLpNorm_sub_le
    ENNReal.one_ne_top hε3
  have hhc : Continuous h := h.continuous
  have hhi : Integrable (h : UnitAddTorus ι → ℝ) volume :=
    (BoundedContinuousFunction.integrable _ h)
  have huh : ∫⁻ y, ‖u y - h y‖ₑ ≤ ε / 3 := by
    rwa [eLpNorm_one_eq_lintegral_enorm (hu.aestronglyMeasurable.sub
      hhi.aestronglyMeasurable)] at hh
  set δ := (ε / 3).toReal with hδ
  by_cases hεtop : ε = ⊤
  · exact Eventually.of_forall fun n => by rw [hεtop]; exact le_top
  have hδpos : 0 < δ := ENNReal.toReal_pos hε3 (ENNReal.div_ne_top hεtop (by norm_num))
  filter_upwards [moll_uniform_of_continuous hhc hδpos] with n hn
  have hdiff : ∀ y, moll n u y - u y =
      moll n (fun z => u z - h z) y + (moll n h y - h y) + (h y - u y) := by
    intro y; rw [moll_sub n hu hhi]; ring
  have hm1 : Measurable (moll n (fun z => u z - h z)) := measurable_moll n (hu.sub hhi)
  have hm2 : Measurable fun y => moll n h y - h y :=
    (measurable_moll n hhi).sub hhc.measurable
  calc ∫⁻ y, ‖moll n u y - u y‖ₑ
      ≤ ∫⁻ y, (‖moll n (fun z => u z - h z) y‖ₑ + ‖moll n h y - h y‖ₑ + ‖h y - u y‖ₑ) := by
        refine lintegral_mono fun y => ?_
        rw [hdiff]
        exact (enorm_add_le _ _).trans (add_le_add (enorm_add_le _ _) le_rfl)
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        rw [lintegral_add_left (f := fun y => ‖moll n (fun z => u z - h z) y‖ₑ +
          ‖moll n h y - h y‖ₑ) (hm1.enorm.add hm2.enorm),
          lintegral_add_left (f := fun y => ‖moll n (fun z => u z - h z) y‖ₑ) hm1.enorm]
        gcongr
        · exact (lintegral_moll_le n (hu.sub hhi)).trans huh
        · calc ∫⁻ y, ‖moll n h y - h y‖ₑ ≤ ∫⁻ _y, ENNReal.ofReal δ :=
                lintegral_mono fun y => by
                  rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hn y)
            _ = ε / 3 := by
                rw [lintegral_const, measure_univ, mul_one, hδ, ENNReal.ofReal_toReal
                  (ENNReal.div_ne_top hεtop (by norm_num))]
        · calc ∫⁻ y, ‖h y - u y‖ₑ = ∫⁻ y, ‖u y - h y‖ₑ := by
                congr 1; funext y; rw [← enorm_neg, neg_sub]
            _ ≤ ε / 3 := huh
    _ = ε := ENNReal.add_thirds ε

/-- `L¹` convergence gives an a.e. convergent subsequence. -/
theorem exists_subseq_ae_of_tendsto_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {f : α → ℝ} (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hf : AEStronglyMeasurable f μ)
    (h : Tendsto (fun n => ∫⁻ y, ‖F n y - f y‖ₑ ∂μ) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ y ∂μ, Tendsto (fun k => F (ns k) y) atTop (𝓝 (f y)) := by
  have h' : Tendsto (fun n => eLpNorm (F n - f) 1 μ) atTop (𝓝 0) := by
    refine h.congr fun n => ?_
    rw [eLpNorm_one_eq_lintegral_enorm ((hF n).sub hf)]; rfl
  exact (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero h').exists_seq_tendsto_ae

/-! ### Milestone 1: smooth approximation of weak-gradient pairs -/

theorem moll_comp_liftT_contDiff (n : ℕ) {u : UnitAddTorus ι → ℝ} (hu : Integrable u volume) :
    ContDiff ℝ ∞ (moll n u ∘ liftT) := by
  rw [moll_comp_liftT]; exact contDiff_mollL n (locallyIntegrable_comp_liftT hu)

/-- The mollifications form weak-gradient pairs: `∇(moll n f) = moll n (∇f)`. -/
theorem isWeakGrad_moll [DecidableEq ι] {f : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad f g) (hf : Integrable f volume) (n : ℕ) :
    IsWeakGrad (moll n f) (fun y k => moll n (fun z => g z k) y) := by
  have hc := isWeakGrad_of_contDiff ((moll_comp_liftT_contDiff n hf).of_le (by simp))
  convert hc using 1
  funext y k
  rw [moll_comp_liftT, fderiv_mollL_of_isWeakGrad h n (secT y) k]
  rfl

/-- **Milestone 1.** A weak-gradient pair `(f, g)` with `f, g ∈ L¹(m)` is the `L¹(m)` limit of
smooth periodic weak-gradient pairs. -/
theorem exists_smooth_approx [DecidableEq ι] {f : UnitAddTorus ι → ℝ}
    {g : UnitAddTorus ι → ι → ℝ} (h : IsWeakGrad f g) (hf : Integrable f volume)
    (hg : ∀ k, Integrable (fun y => g y k) volume) :
    ∃ (F : ℕ → UnitAddTorus ι → ℝ) (G : ℕ → UnitAddTorus ι → ι → ℝ),
      (∀ n, ContDiff ℝ ∞ (F n ∘ liftT)) ∧ (∀ n, IsWeakGrad (F n) (G n)) ∧
      (∀ n, Measurable (F n)) ∧ (∀ n k, Measurable fun y => G n y k) ∧
      Tendsto (fun n => ∫⁻ y, ‖F n y - f y‖ₑ) atTop (𝓝 0) ∧
      ∀ k, Tendsto (fun n => ∫⁻ y, ‖G n y k - g y k‖ₑ) atTop (𝓝 0) :=
  ⟨fun n => moll n f, fun n y k => moll n (fun z => g z k) y,
    fun n => moll_comp_liftT_contDiff n hf, fun n => isWeakGrad_moll h hf n,
    fun n => measurable_moll n hf, fun n k => measurable_moll n (hg k),
    tendsto_moll hf, fun k => tendsto_moll (hg k)⟩

end SharpLSI
