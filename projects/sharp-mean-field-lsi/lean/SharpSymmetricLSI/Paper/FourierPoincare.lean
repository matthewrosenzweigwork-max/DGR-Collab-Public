import SharpSymmetricLSI.Paper.EntFinite

/-!
# The Poincaré inequality on `𝕋^ι` via Fourier series (Phase 3, lane C)

For a weak-gradient pair `(u, g)` on `𝕋^ι` with `u, gₖ ∈ L²`:
`4π² Var(u) ≤ ∑ₖ ∫ gₖ²` (Haar measure), i.e. the spectral gap `a = 4π²` used in (3.28).

* `integral_fderiv_torus_eq_zero`: `∫ ∂_e W = 0` for `C¹` periodic `W` (translation invariance and
  differentiation under the integral);
* `mFourierCoeff_grad_of_contDiff`, `mFourierCoeff_grad`: `ĝⱼ(k) = 2πi kⱼ û(k)` for smooth, then
  (by mollification) weak gradients;
* `poincare_haar`: Parseval.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal Real

namespace SharpLSI

variable {ι : Type*} [Fintype ι]

/-! ### Periodic functions -/

theorem periodic_bounded {E : Type*} [NormedAddCommGroup E] {Φ : (ι → ℝ) → E}
    (hc : Continuous Φ) (hp : ∀ (m : ι → ℤ) x, Φ (x + intVec m) = Φ x) :
    ∃ C, ∀ x, ‖Φ x‖ ≤ C := by
  have hK : IsCompact (univ.pi fun _ : ι => Icc (0 : ℝ) 1) := isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun x => ?_⟩
  have hx : x = (fun i => Int.fract (x i)) + intVec (fun i => ⌊x i⌋) := by
    funext i
    simp only [Pi.add_apply, intVec]
    exact (Int.fract_add_floor (x i)).symm
  rw [hx, hp]
  exact hC _ fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

omit [Fintype ι] in
theorem lift_periodic {E : Type*} (W : UnitAddTorus ι → E) (m : ι → ℤ) (x : ι → ℝ) :
    (W ∘ liftT) (x + intVec m) = (W ∘ liftT) x := by
  simp only [Function.comp_apply, liftT_add_intVec]

theorem fderiv_lift_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : UnitAddTorus ι → E) (m : ι → ℤ) (x : ι → ℝ) :
    fderiv ℝ (W ∘ liftT) (x + intVec m) = fderiv ℝ (W ∘ liftT) x := by
  rw [← fderiv_comp_add_right (𝕜 := ℝ) (f := W ∘ liftT) (x := x) (intVec m)]
  congr 1
  funext z
  exact lift_periodic W m z

/-- `∫_{𝕋^ι} ∂_e W = 0` for `C¹` periodic `W`. -/
theorem integral_fderiv_torus_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {W : UnitAddTorus ι → E} (hW : ContDiff ℝ 1 (W ∘ liftT)) (e : ι → ℝ) :
    ∫ y, fderiv ℝ (W ∘ liftT) (secT y) e = 0 := by
  set Φ := W ∘ liftT with hΦ
  have hdc : Continuous (fderiv ℝ Φ) := hW.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := periodic_bounded hdc (fderiv_lift_periodic W)
  obtain ⟨C₀, hC₀⟩ := periodic_bounded hW.continuous (lift_periodic W)
  set F : ℝ → UnitAddTorus ι → E := fun t y => Φ (secT y + t • e) with hF
  set F' : ℝ → UnitAddTorus ι → E := fun t y => fderiv ℝ Φ (secT y + t • e) e with hF'
  have hconst : ∀ t, ∫ y, F t y = ∫ y, W y := by
    intro t
    have : ∀ y, F t y = W (y + liftT (t • e)) := fun y => by
      simp only [hF, hΦ, Function.comp_apply, liftT_add, liftT_secT]
    simp_rw [this]
    exact integral_add_right_eq_self W _
  have hmeasF : ∀ t, AEStronglyMeasurable (F t) volume := fun t =>
    (hW.continuous.comp (continuous_id.add continuous_const)).comp_aestronglyMeasurable
      measurable_secT.aestronglyMeasurable
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := (0 : ℝ))
    (F := F) (F' := F') (bound := fun _ => C * ‖e‖) Filter.univ_mem
    (Eventually.of_forall hmeasF)
    (Integrable.of_bound (hmeasF 0) C₀ (Eventually.of_forall fun y => hC₀ _))
    (((hdc.clm_apply continuous_const).comp
      (continuous_id.add continuous_const)).comp_aestronglyMeasurable
      measurable_secT.aestronglyMeasurable)
    (Eventually.of_forall fun y t _ => (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)))
    (integrable_const _)
    (Eventually.of_forall fun y t _ => by
      have h1 := ((hW.differentiable one_ne_zero) (secT y + t • e)).hasFDerivAt
      have h2 : HasDerivAt (fun s : ℝ => secT y + s • e) e t := by
        simpa using ((hasDerivAt_id t).smul_const e).const_add (secT y)
      exact h1.comp_hasDerivAt t h2)
  have h0 : HasDerivAt (fun t => ∫ y, F t y) 0 0 := by
    simp_rw [hconst]; exact hasDerivAt_const _ _
  have := hd.2.unique h0
  simpa [hF'] using this

/-! ### Fourier characters along the lift -/

open UnitAddTorus

/-- Mathlib's Fourier theory on `𝕋^ι` uses the normalized Haar measure `haarAddCircle` (a local
instance there); it agrees with `volume`. -/
theorem volume_eq_haarPi :
    (volume : Measure (UnitAddTorus ι)) =
      Measure.pi fun _ => (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  have : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp
  show Measure.pi (fun _ => (volume : Measure UnitAddCircle)) = _
  rw [this]

theorem mFourierCoeff_eq_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : UnitAddTorus ι → E) (n : ι → ℤ) :
    mFourierCoeff f n = ∫ t, mFourier (-n) t • f t := by
  rw [volume_eq_haarPi]; rfl

theorem mFourier_liftT (k : ι → ℤ) (x : ι → ℝ) :
    mFourier k (liftT x) = cexp (2 * π * I * ∑ i, (k i : ℂ) * (x i : ℂ)) := by
  simp only [mFourier, ContinuousMap.coe_mk, liftT, fourier_coe_apply, Complex.ofReal_one,
    div_one]
  rw [← Complex.exp_sum, Finset.mul_sum]
  exact congrArg cexp (Finset.sum_congr rfl fun i _ => by ring)

theorem norm_mFourier_le (k : ι → ℤ) (y : UnitAddTorus ι) : ‖mFourier k y‖ ≤ 1 :=
  (ContinuousMap.norm_coe_le_norm _ _).trans mFourier_norm.le

theorem contDiff_mFourier_liftT (k : ι → ℤ) :
    ContDiff ℝ ⊤ (fun x : ι → ℝ => mFourier k (liftT x)) := by
  simp_rw [mFourier_liftT]
  refine Complex.contDiff_exp.comp (contDiff_const.mul (ContDiff.sum fun i _ =>
    contDiff_const.mul ?_))
  exact Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ i)

theorem sum_single_line [DecidableEq ι] (k : ι → ℤ) (x : ι → ℝ) (j : ι) (t : ℝ) :
    ∑ i, (k i : ℂ) * (((x + t • (Pi.single j 1 : ι → ℝ)) i : ℝ) : ℂ) =
      ∑ i, (k i : ℂ) * (x i : ℂ) + (k j : ℂ) * t := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul,
    mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_apply, hi])
    (fun h => (h (Finset.mem_univ j)).elim)]
  simp

theorem fderiv_mFourier_liftT [DecidableEq ι] (k : ι → ℤ) (x : ι → ℝ) (j : ι) :
    fderiv ℝ (fun x : ι → ℝ => mFourier k (liftT x)) x (Pi.single j 1) =
      2 * π * I * k j * mFourier k (liftT x) := by
  have hd := ((contDiff_mFourier_liftT k).differentiable (by simp) x).hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => x + t • Pi.single j (1 : ℝ)) (Pi.single j 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single j (1 : ℝ))).const_add x
  have h3 := hd.comp_hasDerivAt_of_eq (0 : ℝ) h2 (by simp)
  have hfun : (fun x : ι → ℝ => mFourier k (liftT x)) ∘ (fun t : ℝ => x + t • Pi.single j 1) =
      fun t : ℝ => cexp (2 * π * I * ∑ i, (k i : ℂ) * (x i : ℂ) +
        2 * π * I * (k j : ℂ) * (t : ℂ)) := by
    funext t
    rw [Function.comp_apply, mFourier_liftT, sum_single_line]
    ring_nf
  rw [hfun] at h3
  have h4 : HasDerivAt (fun t : ℝ => cexp (2 * π * I * ∑ i, (k i : ℂ) * (x i : ℂ) +
      2 * π * I * (k j : ℂ) * (t : ℂ))) (cexp (2 * π * I * ∑ i, (k i : ℂ) * (x i : ℂ) +
      2 * π * I * (k j : ℂ) * ((0 : ℝ) : ℂ)) * (2 * π * I * (k j : ℂ))) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (2 * π * I * (k j : ℂ))).const_add
      (2 * π * I * ∑ i, (k i : ℂ) * (x i : ℂ))
    simpa using this.cexp
  rw [h3.unique h4, mFourier_liftT]
  simp only [Complex.ofReal_zero, mul_zero, add_zero]
  ring

/-! ### Fourier coefficients of gradients -/

theorem bounded_lift {v : UnitAddTorus ι → ℝ} (hv : Continuous (v ∘ liftT)) :
    ∃ C, ∀ y, ‖v y‖ ≤ C := by
  obtain ⟨C, hC⟩ := periodic_bounded hv (lift_periodic v)
  exact ⟨C, fun y => by simpa [liftT_secT] using hC (secT y)⟩

/-- `(∂ⱼv)^(k) = 2πi kⱼ v̂(k)` for `C¹` periodic `v`. -/
theorem mFourierCoeff_grad_of_contDiff [DecidableEq ι] {v : UnitAddTorus ι → ℝ}
    (hv : ContDiff ℝ 1 (v ∘ liftT)) (k : ι → ℤ) (j : ι) :
    mFourierCoeff (fun y => (fderiv ℝ (v ∘ liftT) (secT y) (Pi.single j 1) : ℂ)) k =
      2 * π * I * k j * mFourierCoeff (fun y => (v y : ℂ)) k := by
  set E : (ι → ℝ) → ℂ := fun x => mFourier (-k) (liftT x) with hEdef
  set W : UnitAddTorus ι → ℂ := fun y => (v y : ℂ) * mFourier (-k) y with hWdef
  have hWl : W ∘ liftT = fun x => (((v ∘ liftT) x : ℝ) : ℂ) * E x := rfl
  have hc1 : ContDiff ℝ 1 (fun x => (((v ∘ liftT) x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hv
  have hE : ContDiff ℝ 1 E := (contDiff_mFourier_liftT (-k)).of_le le_top
  have hW : ContDiff ℝ 1 (W ∘ liftT) := by rw [hWl]; exact hc1.mul hE
  have h0 := integral_fderiv_torus_eq_zero hW (Pi.single j 1)
  have hofR : ∀ x, fderiv ℝ (fun x => (((v ∘ liftT) x : ℝ) : ℂ)) x (Pi.single j 1) =
      ((fderiv ℝ (v ∘ liftT) x (Pi.single j 1) : ℝ) : ℂ) := by
    intro x
    rw [show (fun x => (((v ∘ liftT) x : ℝ) : ℂ)) = Complex.ofRealCLM ∘ (v ∘ liftT) from rfl,
      fderiv_comp x Complex.ofRealCLM.differentiableAt (hv.differentiable one_ne_zero x),
      ContinuousLinearMap.fderiv]
    rfl
  have hder : ∀ x, fderiv ℝ (W ∘ liftT) x (Pi.single j 1) =
      2 * π * I * ((-k) j : ℤ) * ((((v ∘ liftT) x : ℝ) : ℂ) * E x) +
        E x * ((fderiv ℝ (v ∘ liftT) x (Pi.single j 1) : ℝ) : ℂ) := by
    intro x
    rw [hWl, fderiv_fun_mul (hc1.differentiable one_ne_zero x) (hE.differentiable one_ne_zero x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hEdef, fderiv_mFourier_liftT, hofR]
    ring
  simp_rw [hder] at h0
  have hEs : ∀ y, E (secT y) = mFourier (-k) y := fun y => by simp [hEdef, liftT_secT]
  have hvs : ∀ y, (v ∘ liftT) (secT y) = v y := fun y => by simp [liftT_secT]
  simp_rw [hEs, hvs] at h0
  -- integrability
  obtain ⟨Cv, hCv⟩ := bounded_lift hv.continuous
  have hdc : Continuous (fderiv ℝ (v ∘ liftT)) := hv.continuous_fderiv one_ne_zero
  obtain ⟨CD, hCD⟩ := periodic_bounded hdc (fderiv_lift_periodic v)
  have hvm : AEStronglyMeasurable (fun y => (v y : ℂ)) volume := by
    have : (fun y => (v y : ℂ)) = fun y => (((v ∘ liftT) (secT y) : ℝ) : ℂ) := by
      funext y; rw [hvs]
    rw [this]
    exact (Complex.continuous_ofReal.comp hv.continuous).comp_aestronglyMeasurable
      measurable_secT.aestronglyMeasurable
  have hDm : AEStronglyMeasurable
      (fun y => ((fderiv ℝ (v ∘ liftT) (secT y) (Pi.single j 1) : ℝ) : ℂ)) volume :=
    (Complex.continuous_ofReal.comp (hdc.clm_apply continuous_const)).comp_aestronglyMeasurable
      measurable_secT.aestronglyMeasurable
  have hem : AEStronglyMeasurable (fun y => mFourier (-k) y) volume :=
    (mFourier (-k)).continuous.aestronglyMeasurable
  have hi1 : Integrable (fun y => (v y : ℂ) * mFourier (-k) y) volume :=
    Integrable.of_bound (hvm.mul hem) Cv (Eventually.of_forall fun y => by
      rw [norm_mul, Complex.norm_real]
      exact (mul_le_of_le_one_right (norm_nonneg _) (norm_mFourier_le _ _)).trans (hCv y))
  have hi2 : Integrable (fun y => mFourier (-k) y *
      ((fderiv ℝ (v ∘ liftT) (secT y) (Pi.single j 1) : ℝ) : ℂ)) volume :=
    Integrable.of_bound (hem.mul hDm) (CD * ‖(Pi.single j (1 : ℝ) : ι → ℝ)‖)
      (Eventually.of_forall fun y => by
        rw [norm_mul, Complex.norm_real]
        refine (mul_le_of_le_one_left (norm_nonneg _) (norm_mFourier_le _ _)).trans ?_
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hCD _) (norm_nonneg _)))
  rw [integral_add (hi1.const_mul _) hi2, integral_const_mul] at h0
  simp only [mFourierCoeff_eq_integral, smul_eq_mul]
  simp_rw [mul_comm (mFourier (-k) _)] at h0 ⊢
  simp only [Pi.neg_apply, Int.cast_neg] at h0
  have key : ∫ a, ((fderiv ℝ (v ∘ liftT) (secT a) (Pi.single j 1) : ℝ) : ℂ) * mFourier (-k) a =
      2 * π * I * k j * ∫ a, (v a : ℂ) * mFourier (-k) a := by
    linear_combination h0
  exact key

theorem norm_mFourierCoeff_sub_le {f h : UnitAddTorus ι → ℝ} (hf : Integrable f volume)
    (hh : Integrable h volume) (k : ι → ℤ) :
    ‖mFourierCoeff (fun y => (f y : ℂ)) k - mFourierCoeff (fun y => (h y : ℂ)) k‖ ≤
      (∫⁻ y, ‖f y - h y‖ₑ).toReal := by
  have hem : AEStronglyMeasurable (fun y => mFourier (-k) y) volume :=
    (mFourier (-k)).continuous.aestronglyMeasurable
  have hint : ∀ {F : UnitAddTorus ι → ℝ}, Integrable F volume →
      Integrable (fun y => mFourier (-k) y • (F y : ℂ)) volume := fun {F} hF =>
    Integrable.mono' hF.norm (hem.smul hF.ofReal.aestronglyMeasurable)
      (Eventually.of_forall fun y => by
        rw [norm_smul, Complex.norm_real]
        exact mul_le_of_le_one_left (norm_nonneg _) (norm_mFourier_le _ _))
  have hn := integral_norm_eq_lintegral_enorm (hf.sub hh).aestronglyMeasurable
  simp only [Pi.sub_apply] at hn
  rw [mFourierCoeff_eq_integral, mFourierCoeff_eq_integral, ← integral_sub (hint hf) (hint hh),
    ← hn]
  refine (norm_integral_le_integral_norm _).trans (integral_mono ((hint hf).sub (hint hh)).norm
    (hf.sub hh).norm fun y => ?_)
  rw [← smul_sub, norm_smul, ← Complex.ofReal_sub, Complex.norm_real]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_mFourier_le _ _)

/-- `ĝⱼ(k) = 2πi kⱼ û(k)` for a weak-gradient pair with `u, gⱼ ∈ L¹`. -/
theorem mFourierCoeff_grad [DecidableEq ι] {u : UnitAddTorus ι → ℝ}
    {g : UnitAddTorus ι → ι → ℝ} (h : IsWeakGrad u g) (hu : Integrable u volume)
    (hg : ∀ j, Integrable (fun y => g y j) volume) (k : ι → ℤ) (j : ι) :
    mFourierCoeff (fun y => (g y j : ℂ)) k =
      2 * π * I * k j * mFourierCoeff (fun y => (u y : ℂ)) k := by
  have hn : ∀ n, mFourierCoeff (fun y => (moll n (fun z => g z j) y : ℂ)) k =
      2 * π * I * k j * mFourierCoeff (fun y => (moll n u y : ℂ)) k := by
    intro n
    have hs := mFourierCoeff_grad_of_contDiff ((moll_comp_liftT_contDiff n hu).of_le (by simp)) k j
    have hd : ∀ y, fderiv ℝ (moll n u ∘ liftT) (secT y) (Pi.single j 1) =
        moll n (fun z => g z j) y := by
      intro y; rw [moll_comp_liftT, fderiv_mollL_of_isWeakGrad h n (secT y) j]; rfl
    simp_rw [hd] at hs; exact hs
  have tend : ∀ {F : ℕ → UnitAddTorus ι → ℝ} {f : UnitAddTorus ι → ℝ},
      (∀ n, Integrable (F n) volume) → Integrable f volume →
      Tendsto (fun n => ∫⁻ y, ‖F n y - f y‖ₑ) atTop (𝓝 0) →
      Tendsto (fun n => mFourierCoeff (fun y => (F n y : ℂ)) k) atTop
        (𝓝 (mFourierCoeff (fun y => (f y : ℂ)) k)) := by
    intro F f hF hf hT
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => norm_mFourierCoeff_sub_le (hF n) hf k) ?_
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hT
    exact this
  have h1 := tend (fun n => integrable_moll n (hg j)) (hg j) (tendsto_moll (hg j))
  have h2 := (tend (fun n => integrable_moll n hu) hu (tendsto_moll hu)).const_mul
    (2 * π * I * k j)
  simp_rw [hn] at h1
  exact tendsto_nhds_unique h1 h2

/-! ### Parseval and the Poincaré inequality -/

theorem hasSum_sq_mFourierCoeff_real {u : UnitAddTorus ι → ℝ} (hu : MemLp u 2 volume) :
    HasSum (fun k => ‖mFourierCoeff (fun y => (u y : ℂ)) k‖ ^ 2) (∫ y, u y ^ 2) := by
  set μ' : Measure (UnitAddTorus ι) := Measure.pi fun _ => AddCircle.haarAddCircle with hμ'
  have hu' : MemLp (fun y => (u y : ℂ)) 2 μ' := by rw [hμ', ← volume_eq_haarPi]; exact hu.ofReal
  have hP := hasSum_sq_mFourierCoeff (hu'.toLp _)
  have hc : ∀ k, mFourierCoeff (hu'.toLp _ : UnitAddTorus ι → ℂ) k =
      mFourierCoeff (fun y => (u y : ℂ)) k := fun k =>
    integral_congr_ae (hu'.coeFn_toLp.mono fun t ht => by simp only [ht])
  have hi : ∫ t, ‖(hu'.toLp _ : UnitAddTorus ι → ℂ) t‖ ^ 2 ∂μ' = ∫ y, u y ^ 2 := by
    have e : ∫ t, ‖(hu'.toLp _ : UnitAddTorus ι → ℂ) t‖ ^ 2 ∂μ' = ∫ t, ‖(u t : ℂ)‖ ^ 2 ∂μ' :=
      integral_congr_ae (hu'.coeFn_toLp.mono fun t ht => by simp only [ht])
    rw [e, hμ', ← volume_eq_haarPi]
    congr 1; funext t; rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [hc] at hP
  rw [← hi]
  exact hP

theorem one_le_sum_sq_of_ne_zero {k : ι → ℤ} (hk : k ≠ 0) : 1 ≤ ∑ j, ((k j : ℝ)) ^ 2 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hk
  have : (1 : ℝ) ≤ ((k j : ℝ)) ^ 2 := by
    have h1 : (1 : ℤ) ≤ |k j| := Int.one_le_abs hj
    have h2 : (1 : ℝ) ≤ |(k j : ℝ)| := by exact_mod_cast h1
    nlinarith [sq_abs (k j : ℝ), abs_nonneg (k j : ℝ)]
  exact this.trans (Finset.single_le_sum (f := fun j => ((k j : ℝ)) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ j))

/-- **Poincaré inequality on `𝕋^ι`**: `4π² Var(u) ≤ ∑ⱼ ∫ gⱼ²`. -/
theorem poincare_torus [DecidableEq ι] {u : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad u g) (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (fun y => g y j) 2 volume) :
    4 * π ^ 2 * ProbabilityTheory.variance u volume ≤ ∑ j, ∫ y, g y j ^ 2 := by
  have hui : Integrable u volume := hu.integrable one_le_two
  have hgi : ∀ j, Integrable (fun y => g y j) volume := fun j => (hg j).integrable one_le_two
  set c := fun k => mFourierCoeff (fun y => (u y : ℂ)) k with hc
  have hP := hasSum_sq_mFourierCoeff_real hu
  have hG : ∀ j, HasSum (fun k => 4 * π ^ 2 * ((k j : ℝ)) ^ 2 * ‖c k‖ ^ 2)
      (∫ y, g y j ^ 2) := by
    intro j
    have := hasSum_sq_mFourierCoeff_real (hg j)
    convert this using 1
    funext k
    rw [mFourierCoeff_grad h hui hgi k j, norm_mul]
    have : ‖2 * (π : ℂ) * I * (k j : ℂ)‖ = 2 * π * |(k j : ℝ)| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_two]
      rw [show ((k j : ℤ) : ℂ) = (((k j : ℤ) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      ring
    rw [this, mul_pow, mul_pow, mul_pow, sq_abs]
    ring
  have hsum := hasSum_sum (s := Finset.univ) (fun j _ => hG j)
  have hb := (hP.update 0 0).mul_left (4 * π ^ 2)
  have hle := hasSum_le (fun k => ?_) hb hsum
  · have hc0 : mFourierCoeff (fun y => (u y : ℂ)) 0 = ((∫ y, u y : ℝ) : ℂ) := by
      simp only [mFourierCoeff_eq_integral, neg_zero, mFourier_zero, ContinuousMap.one_apply,
        one_smul]
      exact integral_ofReal
    rw [hc0, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hle
    rw [ProbabilityTheory.variance_eq_sub hu]
    simp only [Pi.pow_apply] at hle ⊢
    linarith
  · by_cases hk : k = 0
    · subst hk
      simp only [Function.update_self, mul_zero]
      exact Finset.sum_nonneg fun j _ => by positivity
    · rw [Function.update_of_ne hk]
      have h1 := one_le_sum_sq_of_ne_zero hk
      have e : ∑ i, 4 * π ^ 2 * ((k i : ℝ)) ^ 2 * ‖c k‖ ^ 2 =
          4 * π ^ 2 * (∑ i, ((k i : ℝ)) ^ 2) * ‖c k‖ ^ 2 := by
        rw [Finset.mul_sum, Finset.sum_mul]
      show 4 * π ^ 2 * ‖c k‖ ^ 2 ≤ _
      rw [e]
      calc 4 * π ^ 2 * ‖c k‖ ^ 2 = 4 * π ^ 2 * 1 * ‖c k‖ ^ 2 := by ring
        _ ≤ 4 * π ^ 2 * (∑ i, ((k i : ℝ)) ^ 2) * ‖c k‖ ^ 2 := by gcongr

/-- **Poincaré inequality on `𝕋^ι`** for `H¹(m)`: `4π² Var_m(u) ≤ ∫ |∇u|² dm`. -/
theorem poincare_haar [DecidableEq ι] {u : UnitAddTorus ι → ℝ} (hu : MemH1 volume u) :
    ENNReal.ofReal (4 * π ^ 2) * var volume u ≤ dirichlet volume u := by
  have hw := isWeakGrad_weakGrad hu.1
  have hg : ∀ j, MemLp (fun y => weakGrad u y j) 2 volume := fun j =>
    hu.2.2.of_le (hw.aestronglyMeasurable_grad j) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact abs_le_sqrt_sqNorm _ j)
  have hP := poincare_torus hw hu.2.1 hg
  have hsq : Integrable (fun y => sqNorm (weakGrad u y)) volume := by
    unfold sqNorm
    exact integrable_finsetSum _ fun j _ => (hg j).integrable_sq
  have hD : dirichlet volume u = ENNReal.ofReal (∑ j, ∫ y, weakGrad u y j ^ 2) := by
    unfold dirichlet
    rw [← ofReal_integral_eq_lintegral_ofReal hsq (Eventually.of_forall fun y => sqNorm_nonneg _)]
    unfold sqNorm
    rw [integral_finsetSum _ fun j _ => (hg j).integrable_sq]
  rw [hD, var, ← ProbabilityTheory.ofReal_variance hu.2.1, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hP

end SharpLSI
