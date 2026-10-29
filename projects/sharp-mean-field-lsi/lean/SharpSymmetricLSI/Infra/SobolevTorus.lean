import SharpSymmetricLSI.Infra.MollifyL2
import SharpSymmetricLSI.Infra.ChainRule

/-!
# A Sobolev embedding on the torus (Phase 2, I1)

For `n = |ι| ≥ 1` and `p = (n+1)/n`: functions in `H¹(𝕋^ι)` lie in `L^{2p}(𝕋^ι)`, with
`∫ |u|^{2p} ≤ K (∫ u² + ∫ |∇u|²)^p` (`lintegral_rpow_le_of_isWeakGrad`). The proof applies
Mathlib's Gagliardo–Nirenberg–Sobolev inequality on `(ι → ℝ) × ℝ` (dimension `n + 1 ≥ 2`) to
`χ(z) Φ(z₁)²`, `Φ` a mollified periodic lift and `χ` a bump equal to `1` on the unit box, and
passes to the limit with the `L²` contraction of mollification and Fatou's lemma.
-/

open MeasureTheory Set Filter Topology Module
open scoped ENNReal ContDiff

namespace SharpLSI

variable {ι : Type*} [Fintype ι]

/-- The exponent `p = (n+1)/n`. -/
noncomputable def sobExp (ι : Type*) [Fintype ι] : ℝ := (Fintype.card ι + 1) / Fintype.card ι

theorem holderConjugate_sobExp [Nonempty ι] :
    Real.HolderConjugate (finrank ℝ ((ι → ℝ) × ℝ)) (sobExp ι) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_self]
  rw [Real.holderConjugate_iff]
  push_cast
  refine ⟨by linarith, ?_⟩
  unfold sobExp
  field_simp
  ring

theorem one_lt_sobExp [Nonempty ι] : 1 < sobExp ι := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold sobExp; rw [one_lt_div hn]; linarith

/-- The bump `χ` on `(ι → ℝ) × ℝ`, equal to `1` on `[0,1]^ι × [0,1]`. -/
noncomputable def boxBump (ι : Type*) [Fintype ι] :
    ContDiffBump ((fun _ => (1 / 2 : ℝ), (1 / 2 : ℝ)) : (ι → ℝ) × ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := one_pos
  rIn_lt_rOut := one_lt_two

theorem boxBump_eq_one {x : ι → ℝ} (hx : x ∈ unitBox ι) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    boxBump ι (x, s) = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, show (boxBump ι).rIn = 1 from rfl]
  dsimp only
  constructor
  · refine (dist_pi_le_iff zero_le_one).mpr fun i => ?_
    have := hx i (mem_univ i)
    rw [Real.dist_eq, abs_le]; constructor <;> linarith [this.1, this.2]
  · rw [Real.dist_eq, abs_le]; constructor <;> linarith [hs.1, hs.2]

theorem boxBump_support {z : (ι → ℝ) × ℝ} (hz : boxBump ι z ≠ 0) :
    z.1 ∈ cube ι 3 ∧ z.2 ∈ Icc (-3 : ℝ) 3 := by
  have h := (boxBump ι).support_eq ▸ (Function.mem_support.mpr hz)
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, show (boxBump ι).rOut = 2 from rfl] at h
  obtain ⟨h1, h2⟩ := h
  dsimp only at h1 h2
  refine ⟨fun i _ => ?_, ?_⟩
  · have := (dist_le_pi_dist z.1 (fun _ => (1 / 2 : ℝ)) i).trans_lt h1
    rw [Real.dist_eq, abs_lt] at this
    change z.1 i ∈ Icc (-(3 : ℝ)) 3
    constructor <;> linarith [this.1, this.2]
  · rw [Real.dist_eq, abs_lt] at h2
    constructor <;> linarith [h2.1, h2.2]

theorem enorm_sq_rpow (a : ℝ) (q : ℝ) : ‖a ^ 2‖ₑ ^ q = ‖a‖ₑ ^ (2 * q) := by
  rw [enorm_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

/-- The lower bound: the torus integral of `|F|^{2q}` is at most the integral of `|χ Φ²|^q`. -/
theorem lintegral_torus_le_bump {F : UnitAddTorus ι → ℝ} (hF : Measurable F) (q : ℝ) :
    ∫⁻ y, ‖F y‖ₑ ^ (2 * q) ≤
      ∫⁻ z : (ι → ℝ) × ℝ, ‖boxBump ι z * F (liftT z.1) ^ 2‖ₑ ^ q := by
  have hbox : MeasurableSet (unitBox ι) := MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  have hm : Measurable fun z : (ι → ℝ) × ℝ => ‖boxBump ι z * F (liftT z.1) ^ 2‖ₑ ^ q :=
    (((boxBump ι).contDiff (n := 0)).continuous.measurable.mul
      ((hF.comp (measurable_liftT.comp measurable_fst)).pow_const 2)).enorm.pow_const q
  calc ∫⁻ y, ‖F y‖ₑ ^ (2 * q)
      = ∫⁻ x in unitBox ι, ‖F (liftT x)‖ₑ ^ (2 * q) :=
        ((measurePreserving_liftT (ι := ι)).lintegral_comp (hF.enorm.pow_const _)).symm
    _ = ∫⁻ x in unitBox ι, ∫⁻ s in Ioc (0 : ℝ) 1, ‖F (liftT x)‖ₑ ^ (2 * q) := by
        congr 1; funext x; simp
    _ = ∫⁻ x in unitBox ι, ∫⁻ s in Ioc (0 : ℝ) 1,
          ‖boxBump ι (x, s) * F (liftT x) ^ 2‖ₑ ^ q := by
        refine setLIntegral_congr_fun hbox fun x hx => ?_
        refine setLIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
        rw [boxBump_eq_one hx hs, one_mul, enorm_sq_rpow]
    _ = ∫⁻ z in unitBox ι ×ˢ Ioc (0 : ℝ) 1, ‖boxBump ι z * F (liftT z.1) ^ 2‖ₑ ^ q := by
        rw [Measure.volume_eq_prod, setLIntegral_prod _ hm.aemeasurable]
    _ ≤ _ := setLIntegral_le_lintegral _ _

theorem boxBump_tsupport {z : (ι → ℝ) × ℝ} (hz : z ∈ tsupport (boxBump ι)) :
    z ∈ cube ι 3 ×ˢ Icc (-3 : ℝ) 3 := by
  rw [ContDiffBump.tsupport_eq, Metric.mem_closedBall, Prod.dist_eq, max_le_iff,
    show (boxBump ι).rOut = 2 from rfl] at hz
  obtain ⟨h1, h2⟩ := hz
  dsimp only at h1 h2
  refine ⟨fun i _ => ?_, ?_⟩
  · have := (dist_le_pi_dist z.1 (fun _ => (1 / 2 : ℝ)) i).trans h1
    rw [Real.dist_eq, abs_le] at this
    change z.1 i ∈ Icc (-(3 : ℝ)) 3
    constructor <;> linarith [this.1, this.2]
  · rw [Real.dist_eq, abs_le] at h2
    constructor <;> linarith [h2.1, h2.2]

theorem opNorm_le_sum_single [DecidableEq ι] (L : (ι → ℝ) →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ k, |L (Pi.single k 1)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun k _ => abs_nonneg _)
    fun v => ?_
  have hv : v = ∑ k, v k • Pi.single k (1 : ℝ) := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum, Real.norm_eq_abs, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [map_smul, smul_eq_mul, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs (v k)).symm ▸ norm_le_pi_norm v k)
    (abs_nonneg _)

/-- Pointwise bound on the derivative of `χ(z) Φ(z₁)²`. -/
theorem norm_fderiv_bump_le {Φ : (ι → ℝ) → ℝ} (hΦ : ContDiff ℝ 1 Φ) {A : ℝ}
    (hA : ∀ z, ‖fderiv ℝ (boxBump ι) z‖ ≤ A) (z : (ι → ℝ) × ℝ) :
    ‖fderiv ℝ (fun z : (ι → ℝ) × ℝ => boxBump ι z * Φ z.1 ^ 2) z‖ ≤
      (cube ι 3 ×ˢ Icc (-3 : ℝ) 3).indicator
        (fun z => A * Φ z.1 ^ 2 + 2 * |Φ z.1| * ‖fderiv ℝ Φ z.1‖) z := by
  have hA0 : 0 ≤ A := le_trans (norm_nonneg _) (hA 0)
  by_cases hz : z ∈ tsupport (boxBump ι)
  · rw [indicator_of_mem (boxBump_tsupport hz)]
    have hχ := ((boxBump ι).contDiff (n := 1)).differentiable one_ne_zero z
    have hΦd := (hΦ.differentiable one_ne_zero) z.1
    have h1 : HasFDerivAt (fun z : (ι → ℝ) × ℝ => Φ z.1)
        ((fderiv ℝ Φ z.1).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) ℝ)) z :=
      hΦd.hasFDerivAt.comp z hasFDerivAt_fst
    have h2 := h1.pow 2
    have h3 := hχ.hasFDerivAt.mul h2
    rw [show (fun z : (ι → ℝ) × ℝ => boxBump ι z * Φ z.1 ^ 2) =
      (⇑(boxBump ι) * fun x => Φ x.1 ^ 2) from rfl, h3.fderiv]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul (boxBump ι z), norm_smul (Φ z.1 ^ 2)]
    have hχ0 : 0 ≤ boxBump ι z := (boxBump ι).nonneg
    have hχ1 : boxBump ι z ≤ 1 := (boxBump ι).le_one
    have hfst : ‖(fderiv ℝ Φ z.1).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) ℝ)‖ ≤
        ‖fderiv ℝ Φ z.1‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_fst_le _ _ _))
    have e0 : ‖(2 • Φ z.1 ^ (2 - 1)) •
        (fderiv ℝ Φ z.1).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) ℝ)‖ ≤
        2 * |Φ z.1| * ‖fderiv ℝ Φ z.1‖ := by
      rw [norm_smul, Real.norm_eq_abs, nsmul_eq_mul]
      have : |(2 : ℕ) * Φ z.1 ^ (2 - 1)| = 2 * |Φ z.1| := by
        norm_num [abs_mul]
      rw [this]
      exact mul_le_mul_of_nonneg_left hfst (by positivity)
    have e1 : ‖boxBump ι z‖ * ‖(2 • Φ z.1 ^ (2 - 1)) •
        (fderiv ℝ Φ z.1).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) ℝ)‖ ≤
        2 * |Φ z.1| * ‖fderiv ℝ Φ z.1‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hχ0]
      calc boxBump ι z * _ ≤ 1 * (2 * |Φ z.1| * ‖fderiv ℝ Φ z.1‖) :=
            mul_le_mul hχ1 e0 (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    have e2 : ‖Φ z.1 ^ 2‖ * ‖fderiv ℝ (boxBump ι) z‖ ≤ A * Φ z.1 ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_comm]
      exact mul_le_mul_of_nonneg_right (hA z) (sq_nonneg _)
    linarith
  · have hz' : (fun z : (ι → ℝ) × ℝ => boxBump ι z * Φ z.1 ^ 2) =ᶠ[𝓝 z] fun _ => 0 := by
      have : ∀ᶠ w in 𝓝 z, w ∉ tsupport (boxBump ι) :=
        (isClosed_tsupport _).isOpen_compl.eventually_mem hz
      filter_upwards [this] with w hw
      rw [image_eq_zero_of_notMem_tsupport hw, zero_mul]
    rw [hz'.fderiv_eq, fderiv_const_apply, norm_zero]
    by_cases hm : z ∈ cube ι 3 ×ˢ Icc (-3 : ℝ) 3
    · rw [indicator_of_mem hm]; positivity
    · rw [indicator_of_notMem hm]

theorem two_abs_mul_sum_le (a : ℝ) (b : ι → ℝ) :
    2 * |a| * ∑ k, |b k| ≤ Fintype.card ι * a ^ 2 + ∑ k, b k ^ 2 := by
  rw [Finset.mul_sum]
  have : ∀ k, 2 * |a| * |b k| ≤ a ^ 2 + b k ^ 2 := fun k => by
    nlinarith [sq_nonneg (|a| - |b k|), sq_abs a, sq_abs (b k)]
  calc ∑ k, 2 * |a| * |b k| ≤ ∑ k, (a ^ 2 + b k ^ 2) := Finset.sum_le_sum fun k _ => this k
    _ = _ := by rw [Finset.sum_add_distrib]; simp

/-- The upper bound: `∫ |D(χΦ²)| ≤ 6·8ⁿ ∫_𝕋 ((A+n)F² + |∇F|²)`. -/
theorem lintegral_fderiv_bump_le [DecidableEq ι] {F : UnitAddTorus ι → ℝ} (hF : Measurable F)
    (hΦ : ContDiff ℝ 1 (F ∘ liftT)) {A : ℝ} (hA : ∀ z, ‖fderiv ℝ (boxBump ι) z‖ ≤ A) :
    ∫⁻ z : (ι → ℝ) × ℝ, ‖fderiv ℝ (fun z : (ι → ℝ) × ℝ => boxBump ι z * F (liftT z.1) ^ 2) z‖ₑ ≤
      6 * ((2 * 3 + 2 : ℕ) : ℝ≥0∞) ^ Fintype.card ι * ∫⁻ y, ENNReal.ofReal
        ((A + Fintype.card ι) * F y ^ 2 +
          ∑ k, fderiv ℝ (F ∘ liftT) (secT y) (Pi.single k 1) ^ 2) := by
  set Φ := F ∘ liftT with hΦdef
  have hA0 : 0 ≤ A := le_trans (norm_nonneg _) (hA 0)
  set H : (ι → ℝ) → ℝ := fun x => A * Φ x ^ 2 + 2 * |Φ x| * ‖fderiv ℝ Φ x‖ with hH
  have hH0 : ∀ x, 0 ≤ H x := fun x => by simp only [hH]; positivity
  have hcont' : Continuous fun x => ‖fderiv ℝ Φ x‖ := (hΦ.continuous_fderiv one_ne_zero).norm
  set Ht : UnitAddTorus ι → ℝ := fun y => A * F y ^ 2 + 2 * |F y| * ‖fderiv ℝ Φ (secT y)‖ with hHtdef
  have hHm : Measurable H := by
    simp only [hH]
    exact (measurable_const.mul ((hΦ.continuous.measurable).pow_const 2)).add
      ((measurable_const.mul hΦ.continuous.measurable.abs).mul hcont'.measurable)
  have hHt : ∀ x, Ht (liftT x) = H x := fun x => by
    simp only [hHtdef, hH, hΦdef, Function.comp_apply, fderiv_lift_secT]
  have hHtm : Measurable Ht := by
    simp only [hHtdef]
    exact (measurable_const.mul (hF.pow_const 2)).add ((measurable_const.mul hF.abs).mul
      (hcont'.measurable.comp measurable_secT))
  have hcube : MeasurableSet (cube ι 3) := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  calc ∫⁻ z : (ι → ℝ) × ℝ, ‖fderiv ℝ (fun z : (ι → ℝ) × ℝ => boxBump ι z * Φ z.1 ^ 2) z‖ₑ
      ≤ ∫⁻ z : (ι → ℝ) × ℝ, (cube ι 3 ×ˢ Icc (-3 : ℝ) 3).indicator
          (fun z => ENNReal.ofReal (H z.1)) z := by
        refine lintegral_mono fun z => ?_
        rw [← ofReal_norm]
        have := norm_fderiv_bump_le (hΦ) hA z
        by_cases hz : z ∈ cube ι 3 ×ˢ Icc (-3 : ℝ) 3
        · rw [indicator_of_mem hz] at this ⊢
          exact ENNReal.ofReal_le_ofReal this
        · rw [indicator_of_notMem hz] at this ⊢
          rw [le_antisymm this (norm_nonneg _), ENNReal.ofReal_zero]
    _ = ∫⁻ x in cube ι 3, ∫⁻ s in Icc (-3 : ℝ) 3, ENNReal.ofReal (H x) := by
        rw [lintegral_indicator (hcube.prod measurableSet_Icc), Measure.volume_eq_prod,
          setLIntegral_prod (fun z : (ι → ℝ) × ℝ => ENNReal.ofReal (H z.1))
            ((ENNReal.measurable_ofReal.comp hHm).comp measurable_fst).aemeasurable]
    _ = ∫⁻ x in cube ι 3, ENNReal.ofReal (H x) * 6 := by
        congr 1; funext x
        rw [setLIntegral_const, Real.volume_Icc]; norm_num
    _ = (∫⁻ x in cube ι 3, ENNReal.ofReal (Ht (liftT x))) * 6 := by
        have := lintegral_mul_const (μ := volume.restrict (cube ι 3)) (6 : ℝ≥0∞)
          (ENNReal.measurable_ofReal.comp hHm)
        simp only [Function.comp_apply] at this
        rw [this]; simp_rw [hHt]
    _ ≤ (((2 * 3 + 2 : ℕ) : ℝ≥0∞) ^ Fintype.card ι * ∫⁻ y, ENNReal.ofReal (Ht y)) * 6 := by
        gcongr
        exact lintegral_cube_le 3 (ENNReal.measurable_ofReal.comp hHtm).aemeasurable
    _ ≤ 6 * ((2 * 3 + 2 : ℕ) : ℝ≥0∞) ^ Fintype.card ι * ∫⁻ y, ENNReal.ofReal
          ((A + Fintype.card ι) * F y ^ 2 +
            ∑ k, fderiv ℝ (F ∘ liftT) (secT y) (Pi.single k 1) ^ 2) := by
        rw [mul_comm _ (6 : ℝ≥0∞), mul_assoc]
        gcongr with y
        simp only [hHtdef]
        have h1 := opNorm_le_sum_single (fderiv ℝ Φ (secT y))
        have h2 := two_abs_mul_sum_le (F y) (fun k => fderiv ℝ Φ (secT y) (Pi.single k 1))
        have h3 : 2 * |F y| * ‖fderiv ℝ Φ (secT y)‖ ≤
            2 * |F y| * ∑ k, |fderiv ℝ Φ (secT y) (Pi.single k 1)| :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        rw [hΦdef] at h2 h3 ⊢
        nlinarith [h2, h3]

theorem exists_bound_fderiv_boxBump : ∃ A, ∀ z, ‖fderiv ℝ (boxBump ι) z‖ ≤ A :=
  (((boxBump ι).contDiff (n := 1)).continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    ((boxBump ι).hasCompactSupport.fderiv (𝕜 := ℝ))

instance : (volume : Measure ((ι → ℝ) × ℝ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; infer_instance

/-- The derivative bound for the bump. -/
noncomputable def bumpA (ι : Type*) [Fintype ι] : ℝ := (exists_bound_fderiv_boxBump (ι := ι)).choose

/-- The Sobolev constant. -/
noncomputable def sobConst (ι : Type*) [Fintype ι] : ℝ≥0∞ :=
  (lintegralPowLePowLIntegralFDerivConst (volume : Measure ((ι → ℝ) × ℝ)) (sobExp ι) : ℝ≥0∞) *
    (6 * ((2 * 3 + 2 : ℕ) : ℝ≥0∞) ^ Fintype.card ι *
      ENNReal.ofReal (bumpA ι + Fintype.card ι + 1)) ^ sobExp ι

theorem sobConst_lt_top [Nonempty ι] : sobConst ι < (∞ : ℝ≥0∞) := by
  unfold sobConst
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.rpow_lt_top_of_nonneg
    (by linarith [one_lt_sobExp (ι := ι)]) ?_)
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
    (ENNReal.pow_ne_top (by norm_num))) ENNReal.ofReal_ne_top

/-- **Smooth torus Sobolev inequality.** -/
theorem lintegral_rpow_le_of_contDiff [Nonempty ι] [DecidableEq ι] {F : UnitAddTorus ι → ℝ}
    (hF : Measurable F) (hΦ : ContDiff ℝ 1 (F ∘ liftT)) :
    ∫⁻ y, ‖F y‖ₑ ^ (2 * sobExp ι) ≤ sobConst ι * (∫⁻ y, ENNReal.ofReal
      (F y ^ 2 + ∑ k, fderiv ℝ (F ∘ liftT) (secT y) (Pi.single k 1) ^ 2)) ^ sobExp ι := by
  have hA := (exists_bound_fderiv_boxBump (ι := ι)).choose_spec
  set A := bumpA ι
  have hA0 : 0 ≤ A := le_trans (norm_nonneg _) (hA 0)
  have hp0 : 0 ≤ sobExp ι := by linarith [one_lt_sobExp (ι := ι)]
  set u : (ι → ℝ) × ℝ → ℝ := fun z => boxBump ι z * F (liftT z.1) ^ 2 with hu
  have hu1 : ContDiff ℝ 1 u :=
    (boxBump ι).contDiff.mul ((hΦ.comp contDiff_fst).pow 2)
  have hu2 : HasCompactSupport u := (boxBump ι).hasCompactSupport.mul_right
  have hGNS := lintegral_pow_le_pow_lintegral_fderiv (μ := volume) hu1 hu2
    (holderConjugate_sobExp (ι := ι))
  have hD := lintegral_fderiv_bump_le hF hΦ hA
  set c : ℝ := A + Fintype.card ι + 1
  have hc : 0 ≤ c := by positivity
  have hcmp : ∫⁻ y, ENNReal.ofReal ((A + Fintype.card ι) * F y ^ 2 +
      ∑ k, fderiv ℝ (F ∘ liftT) (secT y) (Pi.single k 1) ^ 2) ≤
      ENNReal.ofReal c * ∫⁻ y, ENNReal.ofReal
        (F y ^ 2 + ∑ k, fderiv ℝ (F ∘ liftT) (secT y) (Pi.single k 1) ^ 2) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun y => ?_
    rw [← ENNReal.ofReal_mul hc]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : 0 ≤ ∑ k, fderiv ℝ (F ∘ liftT) (secT y) (Pi.single k 1) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h2 := sq_nonneg (F y)
    have : (A + Fintype.card ι) * F y ^ 2 ≤ c * F y ^ 2 :=
      mul_le_mul_of_nonneg_right (by simp only [c]; linarith) h2
    have : ∑ k, fderiv ℝ (F ∘ liftT) (secT y) (Pi.single k 1) ^ 2 ≤
        c * ∑ k, fderiv ℝ (F ∘ liftT) (secT y) (Pi.single k 1) ^ 2 :=
      le_mul_of_one_le_left h1 (by simp only [c]; linarith)
    linarith
  calc ∫⁻ y, ‖F y‖ₑ ^ (2 * sobExp ι) ≤ ∫⁻ z, ‖u z‖ₑ ^ sobExp ι := lintegral_torus_le_bump hF _
    _ ≤ _ := hGNS
    _ ≤ (lintegralPowLePowLIntegralFDerivConst (volume : Measure ((ι → ℝ) × ℝ)) (sobExp ι) :
          ℝ≥0∞) * ((6 * ((2 * 3 + 2 : ℕ) : ℝ≥0∞) ^ Fintype.card ι * ENNReal.ofReal c) *
            ∫⁻ y, ENNReal.ofReal (F y ^ 2 +
              ∑ k, fderiv ℝ (F ∘ liftT) (secT y) (Pi.single k 1) ^ 2)) ^ sobExp ι := by
        gcongr
        refine hD.trans ?_
        rw [mul_assoc _ (ENNReal.ofReal c)]
        gcongr
        exact hcmp
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0, ← mul_assoc]; rfl

theorem ofReal_sq_eq_enorm_sq (a : ℝ) : ENNReal.ofReal (a ^ 2) = ‖a‖ₑ ^ 2 := by
  rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg a)]

theorem lintegral_ofReal_sq_add_sum {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a : α → ℝ} {b : α → ι → ℝ} (ha : Measurable a) (hb : ∀ k, Measurable fun y => b y k) :
    ∫⁻ y, ENNReal.ofReal (a y ^ 2 + ∑ k, b y k ^ 2) ∂μ =
      (∫⁻ y, ‖a y‖ₑ ^ 2 ∂μ) + ∑ k, ∫⁻ y, ‖b y k‖ₑ ^ 2 ∂μ := by
  have : ∀ y, ENNReal.ofReal (a y ^ 2 + ∑ k, b y k ^ 2) = ‖a y‖ₑ ^ 2 + ∑ k, ‖b y k‖ₑ ^ 2 := by
    intro y
    rw [ENNReal.ofReal_add (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _, ofReal_sq_eq_enorm_sq]
    simp_rw [ofReal_sq_eq_enorm_sq]
  simp_rw [this]
  rw [lintegral_add_left (ha.enorm.pow_const 2),
    lintegral_finsetSum _ fun k _ => (hb k).enorm.pow_const 2]

/-- **Torus Sobolev inequality** for weak-gradient pairs:
`∫ |f|^{2p} ≤ K (∫ f² + ∑ₖ ∫ gₖ²)^p` with `p = (n+1)/n`. -/
theorem lintegral_rpow_le_of_isWeakGrad [Nonempty ι] [DecidableEq ι] {f : UnitAddTorus ι → ℝ}
    {g : UnitAddTorus ι → ι → ℝ} (h : IsWeakGrad f g) (hf : Integrable f volume)
    (hg : ∀ k, Integrable (fun y => g y k) volume) :
    ∫⁻ y, ‖f y‖ₑ ^ (2 * sobExp ι) ≤
      sobConst ι * ((∫⁻ y, ‖f y‖ₑ ^ 2) + ∑ k, ∫⁻ y, ‖g y k‖ₑ ^ 2) ^ sobExp ι := by
  have hp0 : 0 ≤ sobExp ι := by linarith [one_lt_sobExp (ι := ι)]
  set B := (∫⁻ y, ‖f y‖ₑ ^ 2) + ∑ k, ∫⁻ y, ‖g y k‖ₑ ^ 2
  -- the uniform bound for the mollifications
  have hn : ∀ n, ∫⁻ y, ‖moll n f y‖ₑ ^ (2 * sobExp ι) ≤ sobConst ι * B ^ sobExp ι := by
    intro n
    have hs := lintegral_rpow_le_of_contDiff (measurable_moll n hf)
      ((moll_comp_liftT_contDiff n hf).of_le (by simp))
    have hd : ∀ y k, fderiv ℝ (moll n f ∘ liftT) (secT y) (Pi.single k 1) =
        moll n (fun z => g z k) y := by
      intro y k
      rw [moll_comp_liftT, fderiv_mollL_of_isWeakGrad h n (secT y) k]
      rfl
    simp_rw [hd] at hs
    rw [lintegral_ofReal_sq_add_sum (measurable_moll n hf)
      (fun k => measurable_moll n (hg k))] at hs
    refine hs.trans ?_
    gcongr
    exact (add_le_add (lintegral_moll_sq_le n hf)
      (Finset.sum_le_sum fun k _ => lintegral_moll_sq_le n (hg k)))
  -- an a.e. convergent subsequence and Fatou
  obtain ⟨ns, -, hae⟩ := exists_subseq_ae_of_tendsto_lintegral
    (fun n => (measurable_moll n hf).aestronglyMeasurable) hf.aestronglyMeasurable
    (tendsto_moll hf)
  have hlim : ∀ᵐ y, ‖f y‖ₑ ^ (2 * sobExp ι) =
      liminf (fun k => ‖moll (ns k) f y‖ₑ ^ (2 * sobExp ι)) atTop := by
    filter_upwards [hae] with y hy
    refine (Tendsto.liminf_eq ?_).symm
    exact (ENNReal.continuous_rpow_const.tendsto _).comp
      ((continuous_enorm.tendsto _).comp hy)
  calc ∫⁻ y, ‖f y‖ₑ ^ (2 * sobExp ι)
      = ∫⁻ y, liminf (fun k => ‖moll (ns k) f y‖ₑ ^ (2 * sobExp ι)) atTop :=
        lintegral_congr_ae hlim
    _ ≤ liminf (fun k => ∫⁻ y, ‖moll (ns k) f y‖ₑ ^ (2 * sobExp ι)) atTop :=
        lintegral_liminf_le' fun k =>
          ((measurable_moll (ns k) hf).enorm.pow_const _).aemeasurable
    _ ≤ sobConst ι * B ^ sobExp ι :=
        liminf_le_of_frequently_le' (Frequently.of_forall fun k => hn (ns k))

end SharpLSI
