import SharpSymmetricLSI.Paper.GroundState

/-!
# Fourier partial sums, synthesis and compactness on `𝕋^ι` (Phase 3, lane C; R39 Step 2)

For real `h ∈ L²(𝕋^ι)`, the partial sums `S_R h = Re ∑_{k∈[-R,R]^ι} ĥ(k) e_k` are smooth, real
(`ĥ(-k) = conj ĥ(k)`), have coefficients `ĥ · 1_{[-R,R]^ι}`, and converge to `h` in `L²`.
Consequences: a Fourier criterion for weak gradients, synthesis of real `L²` functions from
`ℓ²` coefficients, and the Rellich compactness of bounded sequences in `H¹`.
-/

open MeasureTheory InformationTheory Set Filter Topology Complex
open scoped ENNReal Real ContDiff ComplexConjugate
open UnitAddTorus

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The real Fourier coefficient shorthand. -/
noncomputable abbrev cf (h : UnitAddTorus ι → ℝ) (k : ι → ℤ) : ℂ :=
  mFourierCoeff (fun y => (h y : ℂ)) k

theorem integral_mFourier (n : ι → ℤ) :
    ∫ y : UnitAddTorus ι, mFourier n y = if n = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (orthonormal_mFourier (d := ι))) 0 n
  rw [ContinuousMap.inner_toLp] at h
  simp only [mFourier_zero, ContinuousMap.one_apply, map_one, mul_one] at h
  rw [volume_eq_haarPi]
  convert h using 1
  simp only [eq_comm]

theorem cf_neg (h : UnitAddTorus ι → ℝ) (k : ι → ℤ) : cf h (-k) = conj (cf h k) := by
  simp only [cf, SharpLSI.mFourierCoeff_eq_integral]
  rw [← integral_conj]
  congr 1; funext t
  simp only [neg_neg, smul_eq_mul, map_mul, Complex.conj_ofReal, ← mFourier_neg]

theorem integrable_mFourier_smul' {f : UnitAddTorus ι → ℝ} (hf : Integrable f volume)
    (k : ι → ℤ) : Integrable (fun t => mFourier k t • (f t : ℂ)) volume := by
  have := hf.ofReal.bdd_mul (c := 1) (mFourier k).continuous.aestronglyMeasurable
    (Eventually.of_forall fun t => norm_mFourier_le k t)
  simp only [smul_eq_mul]; exact this

theorem cf_sub {f g : UnitAddTorus ι → ℝ} (hf : Integrable f volume) (hg : Integrable g volume)
    (k : ι → ℤ) : cf (fun y => f y - g y) k = cf f k - cf g k := by
  simp only [cf, SharpLSI.mFourierCoeff_eq_integral, Complex.ofReal_sub, smul_sub]
  exact integral_sub (integrable_mFourier_smul' hf (-k)) (integrable_mFourier_smul' hg (-k))

/-- The box `[-R,R]^ι`. -/
def box (R : ℕ) : Finset (ι → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(R : ℤ)) R

theorem neg_mem_box {R : ℕ} {k : ι → ℤ} (hk : k ∈ box R) : -k ∈ box R := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc, Pi.neg_apply] at hk ⊢
  exact fun i => ⟨by linarith [(hk i).2], by linarith [(hk i).1]⟩

theorem eventually_mem_box (k : ι → ℤ) : ∀ᶠ R in atTop, k ∈ box R := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ i, |k i| ≤ M :=
    ⟨Finset.univ.sup fun i => (k i).natAbs, fun i => by
      have := Finset.le_sup (f := fun i => (k i).natAbs) (Finset.mem_univ i)
      rw [Int.abs_eq_natAbs]; exact_mod_cast this⟩
  filter_upwards [eventually_ge_atTop M] with R hR
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have := abs_le.mp (hM i)
  constructor <;> omega

/-- The (complex) partial sum. -/
noncomputable def psumC (c : (ι → ℤ) → ℂ) (R : ℕ) (y : UnitAddTorus ι) : ℂ :=
  ∑ k ∈ box R, c k * mFourier k y

/-- The real partial sum. -/
noncomputable def psum (c : (ι → ℤ) → ℂ) (R : ℕ) (y : UnitAddTorus ι) : ℝ := (psumC c R y).re

theorem psumC_real {c : (ι → ℤ) → ℂ} (hc : ∀ k, c (-k) = conj (c k)) (R : ℕ) (y : UnitAddTorus ι) :
    ((psum c R y : ℝ) : ℂ) = psumC c R y := by
  unfold psum psumC
  rw [← Complex.conj_eq_iff_re, map_sum]
  refine Finset.sum_nbij' (fun k => -k) (fun k => -k) (fun k hk => neg_mem_box hk)
    (fun k hk => neg_mem_box hk) (fun k _ => neg_neg k) (fun k _ => neg_neg k) fun k _ => ?_
  rw [map_mul, ← hc, ← mFourier_neg]

theorem cf_psum {c : (ι → ℤ) → ℂ} (hc : ∀ k, c (-k) = conj (c k)) (R : ℕ) (k : ι → ℤ) :
    cf (psum c R) k = if k ∈ box R then c k else 0 := by
  simp only [cf, SharpLSI.mFourierCoeff_eq_integral]
  simp_rw [psumC_real hc]
  simp only [psumC, Finset.smul_sum]
  rw [integral_finset_sum (f := fun m t => mFourier (-k) t • (c m * mFourier m t)) _
    fun m _ => ((mFourier (-k)).continuous.smul
    (continuous_const.mul (mFourier m).continuous)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)]
  have hterm : ∀ m, ∫ t, mFourier (-k) t • (c m * mFourier m t) = if m = k then c m else 0 :=
    fun m => by
      simp_rw [smul_eq_mul, show ∀ t, mFourier (-k) t * (c m * mFourier m t) =
        c m * mFourier (m + -k) t from fun t => by rw [mFourier_add]; ring]
      rw [integral_const_mul, integral_mFourier]
      by_cases hm : m = k
      · subst hm; simp
      · have : m + -k ≠ 0 := fun h => hm (by rw [← sub_eq_add_neg, sub_eq_zero] at h; exact h)
        simp [hm, this]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq']

theorem contDiff_psum (c : (ι → ℤ) → ℂ) (R : ℕ) : ContDiff ℝ ∞ (psum c R ∘ liftT) := by
  have : psum c R ∘ liftT = fun x => Complex.reCLM (∑ k ∈ box R, c k * mFourier k (liftT x)) := by
    funext x; rfl
  rw [this]
  exact Complex.reCLM.contDiff.comp (ContDiff.sum fun k _ =>
    contDiff_const.mul ((contDiff_mFourier_liftT k).of_le le_top))

theorem fderiv_psum (c : (ι → ℤ) → ℂ) (R : ℕ) (x : ι → ℝ) (j : ι) :
    fderiv ℝ (psum c R ∘ liftT) x (Pi.single j 1) =
      psum (fun k => 2 * π * I * k j * c k) R (liftT x) := by
  have hsum : ∀ k ∈ box R, DifferentiableAt ℝ (fun x : ι → ℝ => c k * mFourier k (liftT x)) x :=
    fun k _ => (contDiff_const.mul (contDiff_mFourier_liftT k)).differentiable (by simp) x
  have hS : DifferentiableAt ℝ (fun x : ι → ℝ => ∑ k ∈ box R, c k * mFourier k (liftT x)) x :=
    DifferentiableAt.fun_sum hsum
  have : psum c R ∘ liftT =
      Complex.reCLM ∘ (fun x => ∑ k ∈ box R, c k * mFourier k (liftT x)) := by
    funext x; rfl
  rw [this, (Complex.reCLM.hasFDerivAt.comp x hS.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [fderiv_fun_sum hsum]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  rw [psum, psumC, Complex.reCLM_apply]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fderiv_const_mul ((contDiff_mFourier_liftT k).differentiable (by simp) x),
    ContinuousLinearMap.smul_apply, fderiv_mFourier_liftT, smul_eq_mul]
  ring

theorem continuous_psum (c : (ι → ℤ) → ℂ) (R : ℕ) : Continuous (psum c R) :=
  Complex.continuous_re.comp (continuous_finset_sum _ fun k _ =>
    continuous_const.mul (mFourier k).continuous)

theorem abs_psum_le (c : (ι → ℤ) → ℂ) (R : ℕ) (y : UnitAddTorus ι) :
    |psum c R y| ≤ ∑ k ∈ box R, ‖c k‖ := by
  refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_))
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_mFourier_le k y)

theorem memLp_psum (c : (ι → ℤ) → ℂ) (R : ℕ) (p : ℝ≥0∞) : MemLp (psum c R) p volume :=
  MemLp.of_bound (continuous_psum c R).aestronglyMeasurable _
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact abs_psum_le c R y)

/-- `L¹` bound by the `L²` norm on a probability space. -/
theorem lintegral_enorm_le_sqrt {α : Type*} [MeasurableSpace α] {P : Measure α}
    [IsProbabilityMeasure P] {f : α → ℝ} (hf : MemLp f 2 P) :
    ∫⁻ x, ‖f x‖ₑ ∂P ≤ ENNReal.ofReal (Real.sqrt (∫ x, f x ^ 2 ∂P)) := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm (hf.integrable one_le_two)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hfa : MemLp (fun x => |f x|) 2 P := hf.abs
  have hv := ProbabilityTheory.variance_nonneg (fun x => |f x|) P
  rw [ProbabilityTheory.variance_eq_sub hfa] at hv
  simp only [Pi.pow_apply, sq_abs] at hv
  simp only [Real.norm_eq_abs]
  exact Real.le_sqrt_of_sq_le (by linarith)

/-- `S_R h → h` in `L²`. -/
theorem tendsto_psum_sq {h : UnitAddTorus ι → ℝ} (hh : MemLp h 2 volume) :
    Tendsto (fun R => ∫ y, (psum (cf h) R y - h y) ^ 2) atTop (𝓝 0) := by
  have hi : Integrable h volume := hh.integrable one_le_two
  have hs : ∀ k, cf h (-k) = conj (cf h k) := cf_neg h
  have hval : ∀ R, ∫ y, (psum (cf h) R y - h y) ^ 2 =
      ∑' k, (if k ∈ box R then 0 else ‖cf h k‖ ^ 2) := by
    intro R
    have hP := hasSum_sq_mFourierCoeff_real ((memLp_psum (cf h) R 2).sub hh)
    simp only [Pi.sub_apply] at hP
    rw [← hP.tsum_eq]
    congr 1; funext k
    show ‖cf (fun y => psum (cf h) R y - h y) k‖ ^ 2 = _
    rw [cf_sub ((memLp_psum (cf h) R 1).integrable le_rfl) hi, cf_psum hs]
    split_ifs <;> simp
  simp_rw [hval]
  have hsum : Summable fun k => ‖cf h k‖ ^ 2 := (hasSum_sq_mFourierCoeff_real hh).summable
  have h0 : (0 : ℝ) = ∑' k : ι → ℤ, (0 : ℝ) := by simp
  rw [h0]
  refine tendsto_tsum_of_dominated_convergence hsum (fun k => ?_) (Eventually.of_forall fun R k => ?_)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_mem_box k] with R hR
    simp [hR]
  · split_ifs <;> simp

theorem tendsto_lintegral_psum {h : UnitAddTorus ι → ℝ} (hh : MemLp h 2 volume) :
    Tendsto (fun R => ∫⁻ y, ‖psum (cf h) R y - h y‖ₑ) atTop (𝓝 0) := by
  have hb : ∀ R, ∫⁻ y, ‖psum (cf h) R y - h y‖ₑ ≤
      ENNReal.ofReal (Real.sqrt (∫ y, (psum (cf h) R y - h y) ^ 2)) := fun R =>
    lintegral_enorm_le_sqrt ((memLp_psum (cf h) R 2).sub hh)
  have hlim := (ENNReal.continuous_ofReal.tendsto _).comp
    ((Real.continuous_sqrt.tendsto _).comp (tendsto_psum_sq hh))
  simp only [Function.comp_def, Real.sqrt_zero, ENNReal.ofReal_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun R => zero_le) hb

/-- **Fourier criterion for weak gradients.** -/
theorem isWeakGrad_of_cf {f : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (hf : MemLp f 2 volume) (hg : ∀ j, MemLp (fun y => g y j) 2 volume)
    (hcoef : ∀ j k, cf (fun y => g y j) k = 2 * π * I * k j * cf f k) : IsWeakGrad f g := by
  have hFG : ∀ R, IsWeakGrad (psum (cf f) R) (fun y j => psum (cf (fun y => g y j)) R y) := by
    intro R
    have h := isWeakGrad_of_contDiff ((contDiff_psum (cf f) R).of_le (by simp))
    convert h using 1
    funext y j
    rw [fderiv_psum, liftT_secT]
    congr 1; funext k; rw [hcoef]
  exact isWeakGrad_of_tendsto hFG (fun R => (memLp_psum _ R 1).integrable le_rfl)
    (fun R j => (memLp_psum _ R 1).integrable le_rfl) (hf.integrable one_le_two)
    (fun j => (hg j).integrable one_le_two) (tendsto_lintegral_psum hf)
    (fun j => tendsto_lintegral_psum (hg j))

/-- **Synthesis**: real `ℓ²` coefficients with `c(-k) = conj c(k)` come from a real `L²` function. -/
theorem exists_of_cf {c : (ι → ℤ) → ℂ} (hc : Summable fun k => ‖c k‖ ^ 2)
    (hs : ∀ k, c (-k) = conj (c k)) : ∃ f : UnitAddTorus ι → ℝ, MemLp f 2 volume ∧ ∀ k, cf f k = c k := by
  have hmem : Memℓp c 2 := (memℓp_gen_iff (by norm_num)).2 (by simpa using hc)
  set F := mFourierBasis.repr.symm (⟨c, hmem⟩ : lp (fun _ : ι → ℤ => ℂ) 2) with hF
  have hcF : ∀ k, mFourierCoeff (F : UnitAddTorus ι → ℂ) k = c k := fun k => by
    rw [← mFourierBasis_repr, hF, LinearIsometryEquiv.apply_symm_apply]
  have hF2 : MemLp (F : UnitAddTorus ι → ℂ) 2 (Measure.pi fun _ => AddCircle.haarAddCircle) :=
    Lp.memLp F
  have hF1 : Integrable (F : UnitAddTorus ι → ℂ) (Measure.pi fun _ => AddCircle.haarAddCircle) :=
    hF2.integrable one_le_two
  refine ⟨fun t => (F t).re, ?_, fun k => ?_⟩
  · rw [volume_eq_haarPi]
    exact hF2.re
  · -- the coefficient of `re F`
    have hconj : mFourierCoeff (fun t => (starRingEnd ℂ) (F t)) k = conj (c (-k)) := by
      rw [← hcF]
      simp only [mFourierCoeff]
      rw [← integral_conj]
      congr 1; funext t
      simp only [smul_eq_mul, map_mul, Complex.conj_conj, ← mFourier_neg, neg_neg]
    have hre : (fun t => (((F t).re : ℝ) : ℂ)) = fun t => (F t + (starRingEnd ℂ) (F t)) / 2 := by
      funext t; rw [Complex.add_conj]; push_cast; ring
    simp only [cf]
    rw [hre]
    have hi1 : Integrable (fun t => mFourier (-k) t • F t)
        (Measure.pi fun _ => AddCircle.haarAddCircle) := by
      have := hF1.bdd_mul (c := 1) (mFourier (-k)).continuous.aestronglyMeasurable
        (Eventually.of_forall fun t => norm_mFourier_le (-k) t)
      simpa only [smul_eq_mul] using this
    have hi2 : Integrable (fun t => mFourier (-k) t • (starRingEnd ℂ) (F t))
        (Measure.pi fun _ => AddCircle.haarAddCircle) := by
      have hcI : Integrable (fun t => (starRingEnd ℂ) (F t))
          (Measure.pi fun _ => AddCircle.haarAddCircle) :=
        hF1.mono (Complex.continuous_conj.comp_aestronglyMeasurable hF1.1)
          (Eventually.of_forall fun t => by simp)
      have := hcI.bdd_mul (c := 1) (mFourier (-k)).continuous.aestronglyMeasurable
        (Eventually.of_forall fun t => norm_mFourier_le (-k) t)
      simpa only [smul_eq_mul] using this
    have : mFourierCoeff (fun t => (F t + (starRingEnd ℂ) (F t)) / 2) k =
        (mFourierCoeff (F : UnitAddTorus ι → ℂ) k +
          mFourierCoeff (fun t => (starRingEnd ℂ) (F t)) k) / 2 := by
      have hi1v : Integrable (fun t => mFourier (-k) t * F t) volume := by
        rw [volume_eq_haarPi]; simpa only [smul_eq_mul] using hi1
      have hi2v : Integrable (fun t => mFourier (-k) t * (starRingEnd ℂ) (F t)) volume := by
        rw [volume_eq_haarPi]; simpa only [smul_eq_mul] using hi2
      simp only [SharpLSI.mFourierCoeff_eq_integral, smul_eq_mul, mul_div_assoc', mul_add]
      rw [integral_div, integral_add hi1v hi2v]
    rw [this, hcF, hconj, hs, Complex.conj_conj]
    ring

/-! ### Parseval for products and `ℓ²` limits -/

theorem hasSum_prod_cf_real {a b : UnitAddTorus ι → ℝ} (ha : MemLp a 2 volume)
    (hb : MemLp b 2 volume) :
    HasSum (fun k => conj (cf a k) * cf b k) ((∫ y, a y * b y : ℝ) : ℂ) := by
  set μ' : Measure (UnitAddTorus ι) := Measure.pi fun _ => AddCircle.haarAddCircle with hμ'
  have ha' : MemLp (fun y => (a y : ℂ)) 2 μ' := by rw [hμ', ← volume_eq_haarPi]; exact ha.ofReal
  have hb' : MemLp (fun y => (b y : ℂ)) 2 μ' := by rw [hμ', ← volume_eq_haarPi]; exact hb.ofReal
  have hP := hasSum_prod_mFourierCoeff (ha'.toLp _) (hb'.toLp _)
  have hca : ∀ k, mFourierCoeff (ha'.toLp _ : UnitAddTorus ι → ℂ) k = cf a k := fun k =>
    integral_congr_ae (ha'.coeFn_toLp.mono fun t ht => by simp only [ht])
  have hcb : ∀ k, mFourierCoeff (hb'.toLp _ : UnitAddTorus ι → ℂ) k = cf b k := fun k =>
    integral_congr_ae (hb'.coeFn_toLp.mono fun t ht => by simp only [ht])
  have hi : ∫ t, conj ((ha'.toLp _ : UnitAddTorus ι → ℂ) t) * (hb'.toLp _ : UnitAddTorus ι → ℂ) t ∂μ' =
      ((∫ y, a y * b y : ℝ) : ℂ) := by
    have e : ∫ t, conj ((ha'.toLp _ : UnitAddTorus ι → ℂ) t) *
        (hb'.toLp _ : UnitAddTorus ι → ℂ) t ∂μ' = ∫ t, ((a t * b t : ℝ) : ℂ) ∂μ' :=
      integral_congr_ae ((ha'.coeFn_toLp.and hb'.coeFn_toLp).mono fun t ht => by
        simp only [ht.1, ht.2, Complex.conj_ofReal, Complex.ofReal_mul])
    rw [e, hμ', ← volume_eq_haarPi, integral_complex_ofReal]
  simp only [hca, hcb] at hP
  rw [← hi]
  exact hP

/-- The tail of an `ℓ¹` family outside the boxes tends to zero. -/
theorem tendsto_tail_box {F : (ι → ℤ) → ℝ} (hF : Summable F) (hF0 : ∀ k, 0 ≤ F k) :
    Tendsto (fun R => ∑' k, if k ∈ box R then 0 else F k) atTop (𝓝 0) := by
  have h0 : (0 : ℝ) = ∑' k : ι → ℤ, (0 : ℝ) := by simp
  rw [h0]
  refine tendsto_tsum_of_dominated_convergence hF (fun k => ?_) (Eventually.of_forall fun R k => ?_)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_mem_box k] with R hR
    simp [hR]
  · split_ifs
    · simp [hF0 k]
    · rw [Real.norm_of_nonneg (hF0 k)]

theorem tsum_split_box {F : (ι → ℤ) → ℝ} (hF : Summable F) (R : ℕ) :
    ∑' k, F k = ∑ k ∈ box R, F k + ∑' k, if k ∈ box R then 0 else F k := by
  have h1 : Summable fun k => if k ∈ box R then F k else 0 :=
    summable_of_ne_finset_zero (s := box R) fun k hk => if_neg hk
  have e : ∀ k, (if k ∈ box R then 0 else F k) = F k - if k ∈ box R then F k else 0 := fun k => by
    split_ifs <;> ring
  have h2 : Summable fun k => if k ∈ box R then 0 else F k := by
    simp_rw [e]; exact hF.sub h1
  have h3 : ∑' k, (if k ∈ box R then F k else 0) = ∑ k ∈ box R, F k := by
    rw [tsum_eq_sum (s := box R) fun k hk => if_neg hk]
    exact Finset.sum_congr rfl fun k hk => if_pos hk
  rw [← h3, ← h1.tsum_add h2]
  congr 1; funext k; split_ifs <;> ring

/-- The Sobolev weight `1 + 4π² |k|²`. -/
noncomputable def wt (k : ι → ℤ) : ℝ := 1 + 4 * π ^ 2 * ∑ j, ((k j : ℝ)) ^ 2

theorem norm_sub_sq_le (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem one_le_wt (k : ι → ℤ) : 1 ≤ wt k := by
  unfold wt; have : 0 ≤ ∑ j, ((k j : ℝ)) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  nlinarith [Real.pi_pos]

theorem wt_ge_of_not_mem_box {R : ℕ} {k : ι → ℤ} (hk : k ∉ box R) : ((R : ℝ) + 1) ^ 2 ≤ wt k := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc, not_forall] at hk
  obtain ⟨i, hi⟩ := hk
  have h1 : ((R : ℝ) + 1) ^ 2 ≤ ((k i : ℝ)) ^ 2 := by
    have : (R : ℤ) + 1 ≤ |k i| := by
      rcases le_or_gt 0 (k i) with h | h
      · rw [abs_of_nonneg h]; omega
      · rw [abs_of_neg h]; omega
    have h' : ((R : ℝ) + 1) ≤ |((k i : ℤ) : ℝ)| := by exact_mod_cast this
    nlinarith [sq_abs ((k i : ℤ) : ℝ), abs_nonneg ((k i : ℤ) : ℝ)]
  have h2 : ((k i : ℝ)) ^ 2 ≤ ∑ j, ((k j : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun j => ((k j : ℝ)) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  unfold wt
  have h4 : (1 : ℝ) ≤ 4 * π ^ 2 := by nlinarith [Real.pi_gt_three]
  nlinarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg ((k j : ℝ)))]

/-- Strong `ℓ²` convergence from pointwise convergence and a uniform `H¹`-weighted bound. -/
theorem tendsto_tsum_sub_sq {x : ℕ → (ι → ℤ) → ℂ} {y : (ι → ℤ) → ℂ} {B : ℝ}
    (hx : ∀ k, Tendsto (fun n => x n k) atTop (𝓝 (y k)))
    (hxs : ∀ n, Summable fun k => wt k * ‖x n k‖ ^ 2) (hxB : ∀ n, ∑' k, wt k * ‖x n k‖ ^ 2 ≤ B)
    (hys : Summable fun k => wt k * ‖y k‖ ^ 2) (hyB : ∑' k, wt k * ‖y k‖ ^ 2 ≤ B) :
    Tendsto (fun n => ∑' k, ‖x n k - y k‖ ^ 2) atTop (𝓝 0) := by
  have hB0 : 0 ≤ B := le_trans (tsum_nonneg fun k => mul_nonneg (le_trans zero_le_one (one_le_wt k))
    (sq_nonneg _)) hyB
  have hdom : ∀ n k, ‖x n k - y k‖ ^ 2 ≤ 2 * (wt k * ‖x n k‖ ^ 2) + 2 * (wt k * ‖y k‖ ^ 2) :=
    fun n k => by
      have h2 := norm_sub_sq_le (x n k) (y k)
      have hw := one_le_wt k
      have h3 := mul_le_mul_of_nonneg_right hw (sq_nonneg ‖x n k‖)
      have h4 := mul_le_mul_of_nonneg_right hw (sq_nonneg ‖y k‖)
      nlinarith
  have hDs : ∀ n, Summable fun k => ‖x n k - y k‖ ^ 2 := fun n =>
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) (hdom n) (((hxs n).mul_left 2).add (hys.mul_left 2))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R, hR⟩ : ∃ R : ℕ, 4 * B / ((R : ℝ) + 1) ^ 2 < ε / 2 := by
    obtain ⟨R, hR⟩ := exists_nat_gt (8 * B / ε)
    refine ⟨R, ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    have hR1 : (8 * B / ε) < (R : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ hε] at hR1
    nlinarith [sq_nonneg ((R : ℝ) + 1), show (1 : ℝ) ≤ (R : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) R]]
  -- finite part
  have hfin : Tendsto (fun n => ∑ k ∈ box R, ‖x n k - y k‖ ^ 2) atTop (𝓝 0) := by
    have := tendsto_finset_sum (box R) fun k _ =>
      (((hx k).sub_const (y k)).norm.pow 2)
    simpa using this
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hfin) (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun k => sq_nonneg _),
    tsum_split_box (hDs n) R]
  have h1 := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _)] at h1
  -- the tail
  have hRp : (0 : ℝ) < ((R : ℝ) + 1) ^ 2 := by positivity
  have htail : ∑' k, (if k ∈ box R then 0 else ‖x n k - y k‖ ^ 2) ≤ 4 * B / ((R : ℝ) + 1) ^ 2 := by
    have hle : ∀ k, (if k ∈ box R then 0 else ‖x n k - y k‖ ^ 2) ≤
        (2 / ((R : ℝ) + 1) ^ 2) * (wt k * ‖x n k‖ ^ 2 + wt k * ‖y k‖ ^ 2) := fun k => by
      have hw0 : 0 ≤ wt k := le_trans zero_le_one (one_le_wt k)
      split_ifs with hk
      · exact mul_nonneg (by positivity) (add_nonneg (mul_nonneg hw0 (sq_nonneg _))
          (mul_nonneg hw0 (sq_nonneg _)))
      · have hw := wt_ge_of_not_mem_box hk
        have h2 := norm_sub_sq_le (x n k) (y k)
        rw [div_mul_eq_mul_div, le_div_iff₀ hRp]
        calc ‖x n k - y k‖ ^ 2 * ((R : ℝ) + 1) ^ 2
            ≤ (2 * ‖x n k‖ ^ 2 + 2 * ‖y k‖ ^ 2) * ((R : ℝ) + 1) ^ 2 :=
              mul_le_mul_of_nonneg_right h2 hRp.le
          _ = 2 * (‖x n k‖ ^ 2 * ((R : ℝ) + 1) ^ 2) + 2 * (‖y k‖ ^ 2 * ((R : ℝ) + 1) ^ 2) := by ring
          _ ≤ 2 * (‖x n k‖ ^ 2 * wt k) + 2 * (‖y k‖ ^ 2 * wt k) := by
              gcongr
          _ = 2 * (wt k * ‖x n k‖ ^ 2 + wt k * ‖y k‖ ^ 2) := by ring
    have hs1 : Summable fun k => if k ∈ box R then 0 else ‖x n k - y k‖ ^ 2 := by
      refine Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity) (fun k => ?_) (hDs n)
      split_ifs <;> simp
    calc ∑' k, (if k ∈ box R then 0 else ‖x n k - y k‖ ^ 2)
        ≤ ∑' k, (2 / ((R : ℝ) + 1) ^ 2) * (wt k * ‖x n k‖ ^ 2 + wt k * ‖y k‖ ^ 2) :=
          hs1.tsum_le_tsum hle (((hxs n).add hys).mul_left _)
      _ = (2 / ((R : ℝ) + 1) ^ 2) * (∑' k, wt k * ‖x n k‖ ^ 2 + ∑' k, wt k * ‖y k‖ ^ 2) := by
          rw [tsum_mul_left, (hxs n).tsum_add hys]
      _ ≤ (2 / ((R : ℝ) + 1) ^ 2) * (B + B) :=
          mul_le_mul_of_nonneg_left (add_le_add (hxB n) hyB) (by positivity)
      _ = 4 * B / ((R : ℝ) + 1) ^ 2 := by ring
  linarith

theorem tsum_split_boxC {F : (ι → ℤ) → ℂ} (hF : Summable F) (R : ℕ) :
    ∑' k, F k = ∑ k ∈ box R, F k + ∑' k, if k ∈ box R then 0 else F k := by
  have h1 : Summable fun k => if k ∈ box R then F k else 0 :=
    summable_of_ne_finset_zero (s := box R) fun k hk => if_neg hk
  have e : ∀ k, (if k ∈ box R then 0 else F k) = F k - if k ∈ box R then F k else 0 := fun k => by
    split_ifs <;> simp
  have h2 : Summable fun k => if k ∈ box R then 0 else F k := by
    simp_rw [e]; exact hF.sub h1
  have h3 : ∑' k, (if k ∈ box R then F k else 0) = ∑ k ∈ box R, F k := by
    rw [tsum_eq_sum (s := box R) fun k hk => if_neg hk]
    exact Finset.sum_congr rfl fun k hk => if_pos hk
  rw [← h3, ← h1.tsum_add h2]
  congr 1; funext k; split_ifs <;> simp

theorem norm_conj_mul_le (a b : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    ‖conj a * b‖ ≤ (δ * ‖a‖ ^ 2 + ‖b‖ ^ 2 / δ) / 2 := by
  rw [norm_mul, Complex.norm_conj]
  have : (δ * ‖a‖ ^ 2 + ‖b‖ ^ 2 / δ) / 2 - ‖a‖ * ‖b‖ = (δ * ‖a‖ - ‖b‖) ^ 2 / (2 * δ) := by
    field_simp; ring
  have h0 : 0 ≤ (δ * ‖a‖ - ‖b‖) ^ 2 / (2 * δ) := by positivity
  linarith

theorem summable_conj_mul {a b : (ι → ℤ) → ℂ} (ha : Summable fun k => ‖a k‖ ^ 2)
    (hb : Summable fun k => ‖b k‖ ^ 2) : Summable fun k => ‖conj (a k) * b k‖ :=
  Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (fun k => norm_conj_mul_le (a k) (b k) 1 one_pos)
    ((((ha.mul_left 1).add (hb.div_const 1))).div_const 2)

/-- Weak `ℓ²` convergence from pointwise convergence and a uniform `ℓ²` bound. -/
theorem tendsto_tsum_conj_mul {x : ℕ → (ι → ℤ) → ℂ} {x0 b : (ι → ℤ) → ℂ} {M : ℝ}
    (hx : ∀ k, Tendsto (fun n => x n k) atTop (𝓝 (x0 k)))
    (hxs : ∀ n, Summable fun k => ‖x n k‖ ^ 2) (hxM : ∀ n, ∑' k, ‖x n k‖ ^ 2 ≤ M)
    (h0s : Summable fun k => ‖x0 k‖ ^ 2) (h0M : ∑' k, ‖x0 k‖ ^ 2 ≤ M)
    (hbs : Summable fun k => ‖b k‖ ^ 2) :
    Tendsto (fun n => ∑' k, conj (x n k) * b k) atTop (𝓝 (∑' k, conj (x0 k) * b k)) := by
  have hM0 : 0 ≤ M := le_trans (tsum_nonneg fun k => sq_nonneg _) h0M
  have hD : ∀ n, Summable fun k => ‖conj (x n k - x0 k) * b k‖ := fun n => by
    have hs : Summable fun k => ‖x n k - x0 k‖ ^ 2 :=
      Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => norm_sub_sq_le _ _)
        (((hxs n).mul_left 2).add (h0s.mul_left 2))
    exact summable_conj_mul hs hbs
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := ε / (8 * (M + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have htail := tendsto_tail_box hbs (fun k => sq_nonneg _)
  obtain ⟨R, hR⟩ := (Metric.tendsto_atTop.1 htail) (ε * δ / 2) (by positivity)
  have hR' := hR R le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun k => by split_ifs <;> positivity)]
    at hR'
  have hfin : Tendsto (fun n => ∑ k ∈ box R, conj (x n k - x0 k) * b k) atTop (𝓝 0) := by
    have := tendsto_finset_sum (box R) fun k _ =>
      ((Complex.continuous_conj.tendsto _).comp ((hx k).sub_const (x0 k))).mul_const (b k)
    simpa [Function.comp_def] using this
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hfin) (ε / 4) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [dist_zero_right] at h1
  have hsum_eq : ∑' k, conj (x n k) * b k - ∑' k, conj (x0 k) * b k =
      ∑' k, conj (x n k - x0 k) * b k := by
    rw [← (summable_conj_mul (hxs n) hbs).of_norm.tsum_sub (summable_conj_mul h0s hbs).of_norm]
    congr 1; funext k; rw [map_sub]; ring
  rw [dist_eq_norm, hsum_eq, tsum_split_boxC (hD n).of_norm R]
  -- tail estimate
  have htl : ‖∑' k, (if k ∈ box R then 0 else conj (x n k - x0 k) * b k)‖ ≤
      2 * δ * M + (∑' k, if k ∈ box R then 0 else ‖b k‖ ^ 2) / (2 * δ) := by
    have hs1 : Summable fun k => ‖(if k ∈ box R then 0 else conj (x n k - x0 k) * b k)‖ := by
      refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (hD n)
      split_ifs
      · rw [norm_zero]; exact norm_nonneg _
      · exact le_rfl
    have hsb : Summable fun k => if k ∈ box R then 0 else ‖b k‖ ^ 2 := by
      refine Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity) (fun k => ?_) hbs
      split_ifs <;> simp
    have hsx : Summable fun k => ‖x n k - x0 k‖ ^ 2 :=
      Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => norm_sub_sq_le _ _)
        (((hxs n).mul_left 2).add (h0s.mul_left 2))
    calc ‖∑' k, (if k ∈ box R then 0 else conj (x n k - x0 k) * b k)‖
        ≤ ∑' k, ‖(if k ∈ box R then 0 else conj (x n k - x0 k) * b k)‖ :=
          norm_tsum_le_tsum_norm hs1
      _ ≤ ∑' k, ((δ * ‖x n k - x0 k‖ ^ 2) / 2 +
            (if k ∈ box R then 0 else ‖b k‖ ^ 2) / (2 * δ)) := by
          refine hs1.tsum_le_tsum (fun k => ?_) (((hsx.mul_left δ).div_const 2).add
            (hsb.div_const _))
          split_ifs
          · simp only [norm_zero, zero_div, add_zero]; positivity
          · have := norm_conj_mul_le (x n k - x0 k) (b k) δ hδ
            calc _ ≤ (δ * ‖x n k - x0 k‖ ^ 2 + ‖b k‖ ^ 2 / δ) / 2 := this
              _ = _ := by field_simp
      _ = δ / 2 * ∑' k, ‖x n k - x0 k‖ ^ 2 + (∑' k, if k ∈ box R then 0 else ‖b k‖ ^ 2) / (2 * δ) := by
          rw [((hsx.mul_left δ).div_const 2).tsum_add (hsb.div_const _), tsum_div_const,
            tsum_div_const, tsum_mul_left]; ring
      _ ≤ δ / 2 * (2 * M + 2 * M) + (∑' k, if k ∈ box R then 0 else ‖b k‖ ^ 2) / (2 * δ) := by
          gcongr
          calc ∑' k, ‖x n k - x0 k‖ ^ 2 ≤ ∑' k, (2 * ‖x n k‖ ^ 2 + 2 * ‖x0 k‖ ^ 2) :=
                hsx.tsum_le_tsum (fun k => norm_sub_sq_le _ _) (((hxs n).mul_left 2).add (h0s.mul_left 2))
            _ = 2 * ∑' k, ‖x n k‖ ^ 2 + 2 * ∑' k, ‖x0 k‖ ^ 2 := by
                rw [((hxs n).mul_left 2).tsum_add (h0s.mul_left 2), tsum_mul_left, tsum_mul_left]
            _ ≤ 2 * M + 2 * M := by linarith [hxM n]
      _ = 2 * δ * M + (∑' k, if k ∈ box R then 0 else ‖b k‖ ^ 2) / (2 * δ) := by ring
  have hδM : 2 * δ * M ≤ ε / 4 := by
    have e : 2 * δ * M = ε / 4 * (M / (M + 1)) := by rw [hδdef]; field_simp; ring
    rw [e]
    have : M / (M + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith
  have htb : (∑' k, if k ∈ box R then 0 else ‖b k‖ ^ 2) / (2 * δ) < ε / 4 := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  calc ‖∑ k ∈ box R, conj (x n k - x0 k) * b k +
        ∑' k, (if k ∈ box R then 0 else conj (x n k - x0 k) * b k)‖
      ≤ ‖∑ k ∈ box R, conj (x n k - x0 k) * b k‖ +
        ‖∑' k, (if k ∈ box R then 0 else conj (x n k - x0 k) * b k)‖ := norm_add_le _ _
    _ < ε := by linarith

/-! ### Rellich compactness -/

theorem norm_grad_coeff_sq (k : ι → ℤ) (j : ι) (c : ℂ) :
    ‖2 * π * I * k j * c‖ ^ 2 = 4 * π ^ 2 * ((k j : ℝ)) ^ 2 * ‖c‖ ^ 2 := by
  have : ‖2 * (π : ℂ) * I * (k j : ℂ)‖ = 2 * π * |(k j : ℝ)| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_two]
    rw [show ((k j : ℤ) : ℂ) = (((k j : ℤ) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    ring
  rw [norm_mul, this, mul_pow, mul_pow, mul_pow, sq_abs]; ring

theorem norm_grad_coeff_sq_le (k : ι → ℤ) (j : ι) (c : ℂ) :
    ‖2 * π * I * k j * c‖ ^ 2 ≤ wt k * ‖c‖ ^ 2 := by
  rw [norm_grad_coeff_sq]
  have h1 : ((k j : ℝ)) ^ 2 ≤ ∑ i, ((k i : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun i => ((k i : ℝ)) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  unfold wt
  have : 4 * π ^ 2 * ((k j : ℝ)) ^ 2 ≤ 1 + 4 * π ^ 2 * ∑ i, ((k i : ℝ)) ^ 2 := by
    nlinarith [Real.pi_pos]
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

theorem hasSum_wt_cf {u : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ} (hw : IsWeakGrad u g)
    (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (fun y => g y j) 2 volume) :
    HasSum (fun k => wt k * ‖cf u k‖ ^ 2) ((∫ y, u y ^ 2) + ∑ j, ∫ y, g y j ^ 2) := by
  have hui : Integrable u volume := hu.integrable one_le_two
  have hgi : ∀ j, Integrable (fun y => g y j) volume := fun j => (hg j).integrable one_le_two
  have hP := hasSum_sq_mFourierCoeff_real hu
  have hG : ∀ j, HasSum (fun k => 4 * π ^ 2 * ((k j : ℝ)) ^ 2 * ‖cf u k‖ ^ 2) (∫ y, g y j ^ 2) := by
    intro j
    have := hasSum_sq_mFourierCoeff_real (hg j)
    convert this using 1
    funext k
    rw [mFourierCoeff_grad hw hui hgi k j, norm_mul]
    have : ‖2 * (π : ℂ) * I * (k j : ℂ)‖ = 2 * π * |(k j : ℝ)| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_two]
      rw [show ((k j : ℤ) : ℂ) = (((k j : ℤ) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      ring
    rw [this, mul_pow, mul_pow, mul_pow, sq_abs]
    ring
  have hsum := hasSum_sum (s := Finset.univ) (fun j _ => hG j)
  have := hP.add hsum
  convert this using 1
  funext k
  unfold wt
  rw [add_mul, one_mul, Finset.mul_sum, Finset.sum_mul]

/-- **Rellich**: a sequence bounded in `H¹(𝕋^ι)` has a subsequence converging strongly in `L²`,
whose gradients converge weakly in `L²`, to an `H¹` limit. -/
theorem rellich_torus {u : ℕ → UnitAddTorus ι → ℝ} {g : ℕ → UnitAddTorus ι → ι → ℝ}
    (hw : ∀ n, IsWeakGrad (u n) (g n)) (hu : ∀ n, MemLp (u n) 2 volume)
    (hg : ∀ n j, MemLp (fun y => g n y j) 2 volume) {B : ℝ}
    (hB : ∀ n, (∫ y, u n y ^ 2) + ∑ j, ∫ y, g n y j ^ 2 ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (f : UnitAddTorus ι → ℝ) (G : UnitAddTorus ι → ι → ℝ),
      MemLp f 2 volume ∧ (∀ j, MemLp (fun y => G y j) 2 volume) ∧ IsWeakGrad f G ∧
      Tendsto (fun n => ∫ y, (u (φ n) y - f y) ^ 2) atTop (𝓝 0) ∧
      ∀ j (h : UnitAddTorus ι → ℝ), MemLp h 2 volume →
        Tendsto (fun n => ∫ y, g (φ n) y j * h y) atTop (𝓝 (∫ y, G y j * h y)) := by
  set v : ℕ → (ι → ℤ) → ℂ := fun n => cf (u n) with hv
  have hW := fun n => hasSum_wt_cf (hw n) (hu n) (hg n)
  have hwt0 : ∀ k : ι → ℤ, 0 ≤ wt k := fun k => le_trans zero_le_one (one_le_wt k)
  have hvB : ∀ n k, ‖v n k‖ ^ 2 ≤ B := fun n k => by
    have h1 : wt k * ‖v n k‖ ^ 2 ≤ (∫ y, u n y ^ 2) + ∑ j, ∫ y, g n y j ^ 2 :=
      le_hasSum (hW n) k fun k' _ => mul_nonneg (hwt0 k') (sq_nonneg _)
    have h2 : ‖v n k‖ ^ 2 ≤ wt k * ‖v n k‖ ^ 2 := le_mul_of_one_le_left (sq_nonneg _) (one_le_wt k)
    linarith [hB n]
  have hB0 : 0 ≤ B := le_trans (sq_nonneg _) (hvB 0 0)
  -- compactness of the coefficient sequences
  have hK : IsCompact (Set.univ.pi fun _ : ι → ℤ => Metric.closedBall (0 : ℂ) (Real.sqrt B)) :=
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hmem : ∀ n, v n ∈ Set.univ.pi fun _ : ι → ℤ => Metric.closedBall (0 : ℂ) (Real.sqrt B) :=
    fun n => Set.mem_univ_pi.2 fun k => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact Real.le_sqrt_of_sq_le (hvB n k)
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hpt : ∀ k, Tendsto (fun n => v (φ n) k) atTop (𝓝 (a k)) := fun k =>
    tendsto_pi_nhds.1 hlim k
  refine ⟨φ, hφ, ?_⟩
  -- properties of the limit
  have hsym : ∀ k, a (-k) = conj (a k) := fun k => by
    refine tendsto_nhds_unique (hpt (-k)) ?_
    have := (Complex.continuous_conj.tendsto _).comp (hpt k)
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, hv, cf_neg]
  have hfinB : ∀ S : Finset (ι → ℤ), ∑ k ∈ S, wt k * ‖a k‖ ^ 2 ≤ B := fun S => by
    have hl : Tendsto (fun n => ∑ k ∈ S, wt k * ‖v (φ n) k‖ ^ 2) atTop
        (𝓝 (∑ k ∈ S, wt k * ‖a k‖ ^ 2)) :=
      tendsto_finset_sum S fun k _ => ((hpt k).norm.pow 2).const_mul _
    refine le_of_tendsto' hl fun n => ?_
    exact (sum_le_hasSum S (fun k _ => mul_nonneg (hwt0 k) (sq_nonneg _)) (hW (φ n))).trans (hB _)
  have haS : Summable fun k => wt k * ‖a k‖ ^ 2 :=
    summable_of_sum_le (fun k => mul_nonneg (hwt0 k) (sq_nonneg _)) hfinB
  have haB : ∑' k, wt k * ‖a k‖ ^ 2 ≤ B := haS.tsum_le_of_sum_le hfinB
  have ha2 : Summable fun k => ‖a k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _)
      (fun k => le_mul_of_one_le_left (sq_nonneg _) (one_le_wt k)) haS
  obtain ⟨f, hf2, hfc⟩ := exists_of_cf ha2 hsym
  have hGex : ∀ j, ∃ Gj : UnitAddTorus ι → ℝ, MemLp Gj 2 volume ∧
      ∀ k, cf Gj k = 2 * π * I * k j * a k := fun j => by
    refine exists_of_cf (Summable.of_nonneg_of_le (fun k => sq_nonneg _)
      (fun k => norm_grad_coeff_sq_le k j (a k)) haS) fun k => ?_
    rw [hsym]
    simp only [Pi.neg_apply, Int.cast_neg, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
      map_intCast]
    ring
  choose Gf hGf2 hGfc using hGex
  refine ⟨f, fun y j => Gf j y, hf2, hGf2,
    isWeakGrad_of_cf hf2 hGf2 (fun j k => by rw [hGfc, hfc]), ?_, ?_⟩
  · have hval : ∀ n, ∫ y, (u (φ n) y - f y) ^ 2 = ∑' k, ‖v (φ n) k - a k‖ ^ 2 := fun n => by
      have hP := hasSum_sq_mFourierCoeff_real ((hu (φ n)).sub hf2)
      simp only [Pi.sub_apply] at hP
      rw [← hP.tsum_eq]
      congr 1; funext k
      show ‖cf (fun y => u (φ n) y - f y) k‖ ^ 2 = _
      rw [cf_sub ((hu _).integrable one_le_two) (hf2.integrable one_le_two), hfc]
    simp_rw [hval]
    exact tendsto_tsum_sub_sq hpt (fun n => (hW (φ n)).summable)
      (fun n => (hW (φ n)).tsum_eq.le.trans (hB _)) haS haB
  · intro j h hh
    have hgc : ∀ n k, cf (fun y => g n y j) k = 2 * π * I * k j * v n k := fun n k =>
      mFourierCoeff_grad (hw n) ((hu n).integrable one_le_two)
        (fun j => (hg n j).integrable one_le_two) k j
    have hval : ∀ n, ((∫ y, g (φ n) y j * h y : ℝ) : ℂ) =
        ∑' k, conj (2 * π * I * k j * v (φ n) k) * cf h k := fun n => by
      rw [← (hasSum_prod_cf_real (hg (φ n) j) hh).tsum_eq]
      congr 1; funext k; rw [hgc]
    have hval0 : ((∫ y, Gf j y * h y : ℝ) : ℂ) = ∑' k, conj (2 * π * I * k j * a k) * cf h k := by
      rw [← (hasSum_prod_cf_real (hGf2 j) hh).tsum_eq]
      congr 1; funext k; rw [hGfc]
    have hxs : ∀ n, Summable fun k => ‖2 * π * I * k j * v (φ n) k‖ ^ 2 := fun n =>
      Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => norm_grad_coeff_sq_le k j _)
        (hW (φ n)).summable
    have hxM : ∀ n, ∑' k, ‖2 * π * I * k j * v (φ n) k‖ ^ 2 ≤ B := fun n =>
      ((hxs n).tsum_le_tsum (fun k => norm_grad_coeff_sq_le k j _) (hW (φ n)).summable).trans
        ((hW (φ n)).tsum_eq.le.trans (hB _))
    have h0s : Summable fun k => ‖2 * π * I * k j * a k‖ ^ 2 :=
      Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => norm_grad_coeff_sq_le k j _) haS
    have h0M : ∑' k, ‖2 * π * I * k j * a k‖ ^ 2 ≤ B :=
      (h0s.tsum_le_tsum (fun k => norm_grad_coeff_sq_le k j _) haS).trans haB
    have hlim := tendsto_tsum_conj_mul (x := fun n k => 2 * π * I * k j * v (φ n) k)
      (x0 := fun k => 2 * π * I * k j * a k) (b := cf h) (M := B)
      (fun k => (hpt k).const_mul _) hxs hxM h0s h0M (hasSum_sq_mFourierCoeff_real hh).summable
    simp_rw [← hval, ← hval0] at hlim
    have := (Complex.continuous_re.tendsto _).comp hlim
    simpa [Function.comp_def] using this

end SharpLSI
