import SharpSymmetricLSI.Paper.CircleLSI
import SharpSymmetricLSI.Paper.CosineDissipation

/-!
# Lemma 3.2 for `√ρ ∈ H¹` (Phase 3, lane C; R10 sub-milestones (d), (e))

The circle `𝕋 = 𝕋^1` is parametrized by `lineT : (0,1] → 𝕋` (measure preserving). For a
density `ρ` with `u = √ρ ∈ H¹(m)`, the `1`-periodic lift `ρ̃ = ρ ∘ lineT` runs the heat flow
`p_s` of `Infra/HeatCircle`. Then
* `∂ₓ p_s = K_s * (2uu')` (Fourier coefficients, `mFourierCoeff_grad`), and Cauchy–Schwarz
  against the positive kernel gives `I(p_s) ≤ 4∫u'² = I(ρ)`;
* `p_s → ρ` in `L²(m)` as `s → 0` (Parseval), hence a.e. along a sequence, and Fatou gives
  `H(ρ) ≤ liminf H(p_s)`.
Together with `entropyH_le_log_fisher` this is (3.10); (3.11) follows from `e^s ≥ 1 + s + s²/2`.
-/

open MeasureTheory InformationTheory Set Filter Topology Complex
open scoped ENNReal Real ContDiff
open UnitAddTorus

namespace SharpLSI

/-! ### The parametrization `(0,1] → 𝕋` -/

/-- `x ↦ [x] ∈ 𝕋`. -/
noncomputable def lineT (x : ℝ) : Torus 1 := liftT (lineF x)

theorem measurePreserving_lineT :
    MeasurePreserving lineT ((volume : Measure ℝ).restrict (Ioc 0 1)) (haar 1) := by
  have h1 := UnitAddCircle.measurePreserving_mk 0
  simp only [zero_add] at h1
  have h2 := (volume_preserving_funUnique (Fin 1) UnitAddCircle).symm
  exact h2.comp h1

theorem integral_lineT {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : Torus 1 → E}
    (hg : AEStronglyMeasurable g (haar 1)) :
    ∫ x in Ioc (0 : ℝ) 1, g (lineT x) = ∫ y, g y ∂haar 1 := by
  have h := integral_map (μ := (volume : Measure ℝ).restrict (Ioc 0 1))
    measurePreserving_lineT.measurable.aemeasurable (f := g)
    (by rw [measurePreserving_lineT.map_eq]; exact hg)
  rw [measurePreserving_lineT.map_eq] at h
  exact h.symm

theorem intervalIntegral_lineT {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Torus 1 → E} (hg : AEStronglyMeasurable g (haar 1)) :
    ∫ x in (0 : ℝ)..1, g (lineT x) = ∫ y, g y ∂haar 1 := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_lineT hg]

theorem integrableOn_lineT {E : Type*} [NormedAddCommGroup E] {g : Torus 1 → E}
    (hg : Integrable g (haar 1)) : IntegrableOn (fun x => g (lineT x)) (Ioc 0 1) :=
  (measurePreserving_lineT.integrable_comp hg.aestronglyMeasurable).mpr hg

theorem intervalIntegrable_lineT {E : Type*} [NormedAddCommGroup E] {g : Torus 1 → E}
    (hg : Integrable g (haar 1)) : IntervalIntegrable (fun x => g (lineT x)) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr (integrableOn_lineT hg)

theorem ae_lineT {p : Torus 1 → Prop} (h : ∀ᵐ y ∂haar 1, p y) :
    ∀ᵐ x ∂(volume : Measure ℝ).restrict (Ioc 0 1), p (lineT x) :=
  measurePreserving_lineT.quasiMeasurePreserving.ae h

theorem lintegral_lineT {g : Torus 1 → ℝ≥0∞} (hg : AEMeasurable g (haar 1)) :
    ∫⁻ x in Ioc (0 : ℝ) 1, g (lineT x) = ∫⁻ y, g y ∂haar 1 := by
  have h := lintegral_map' (μ := (volume : Measure ℝ).restrict (Ioc 0 1))
    (by rw [measurePreserving_lineT.map_eq]; exact hg)
    measurePreserving_lineT.measurable.aemeasurable
  rw [measurePreserving_lineT.map_eq] at h
  exact h.symm

/-- Fourier coefficients on `𝕋` are those of the periodic lift. -/
theorem mFourierCoeff_eq_heatCoeff {f : Torus 1 → ℝ} (hf : AEStronglyMeasurable f (haar 1))
    (k : Fin 1 → ℤ) :
    mFourierCoeff (fun y => (f y : ℂ)) k = heatCoeff (fun x => f (lineT x)) (k 0) := by
  rw [mFourierCoeff_eq_integral, ← integral_lineT (g := fun t => mFourier (-k) t • (f t : ℂ))
    (((mFourier (-k)).continuous.aestronglyMeasurable).smul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hf)), heatCoeff,
    intervalIntegral.integral_of_le zero_le_one]
  refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
  simp only [lineT, mFourier_liftT, Fin.sum_univ_one, smul_eq_mul, lineF, Pi.neg_apply]
  rw [mul_comm]
  congr 2
  push_cast; ring

theorem lineT_add_int (x : ℝ) (n : ℤ) : lineT (x + n) = lineT x := by
  rw [lineT, lineT, show lineF (x + n) = lineF x + intVec (fun _ => n) from by
    funext i; simp [lineF, intVec], liftT_add_intVec]

/-! ### The density data -/

theorem memLp_weakGrad_zero {u : Torus 1 → ℝ} (hu : MemH1 (haar 1) u) :
    MemLp (fun x => weakGrad u x 0) 2 (haar 1) :=
  hu.2.2.of_le ((isWeakGrad_weakGrad hu.1).aestronglyMeasurable_grad 0)
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact abs_le_sqrt_sqNorm _ 0)

theorem fisherInfo_densMeasure_eq {ρ : Torus 1 → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar 1 = 1) (hρ : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    fisherInfo (densMeasure ρ) (haar 1) =
      ENNReal.ofReal (4 * ∫ x, weakGrad (fun x => Real.sqrt (ρ x)) x 0 ^ 2 ∂haar 1) := by
  set u : Torus 1 → ℝ := fun x => Real.sqrt (ρ x) with hu_def
  have hi := integrable_of_integral_eq_one hρ1
  have hm : AEMeasurable (fun x => ENNReal.ofReal (ρ x)) (haar 1) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hi.aestronglyMeasurable.aemeasurable
  have huv : u =ᵐ[haar 1] (fun x => Real.sqrt ((densMeasure ρ).rnDeriv (haar 1) x).toReal) := by
    filter_upwards [Measure.rnDeriv_withDensity₀ (haar 1) hm] with x hx
    rw [hu_def, show densMeasure ρ = (haar 1).withDensity _ from rfl, hx,
      ENNReal.toReal_ofReal (hρ0 x)]
  obtain ⟨hH1, hdir⟩ := memH1_congr_ae (Q := haar 1) (Measure.AbsolutelyContinuous.refl _)
    (Measure.AbsolutelyContinuous.refl _) hρ huv
  have hfi : fisherInfo (densMeasure ρ) (haar 1) = 4 * dirichlet (haar 1) u := by
    unfold fisherInfo; rw [if_pos ⟨withDensity_absolutelyContinuous _ _, hH1⟩, hdir]
  rw [hfi]; unfold dirichlet
  have hg2 := memLp_weakGrad_zero hρ
  have : ∀ x, sqNorm (weakGrad u x) = weakGrad u x 0 ^ 2 := fun x => by simp [sqNorm]
  simp_rw [this]
  rw [← ofReal_integral_eq_lintegral_ofReal hg2.integrable_sq
    (Eventually.of_forall fun x => sq_nonneg _), ENNReal.ofReal_mul (by norm_num)]
  simp

theorem ae_bounded_of_memH1 {u : Torus 1 → ℝ} (hu : MemH1 (haar 1) u) :
    ∃ M, ∀ᵐ x ∂haar 1, |u x| ≤ M := by
  refine ⟨|∫ y, u y ∂haar 1| + ∫ y, |weakGrad u y 0| ∂haar 1, ?_⟩
  filter_upwards [ae_abs_sub_mean_le hu] with x hx
  calc |u x| = |(u x - ∫ y, u y ∂haar 1) + ∫ y, u y ∂haar 1| := by ring_nf
    _ ≤ |u x - ∫ y, u y ∂haar 1| + |∫ y, u y ∂haar 1| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem memLp_two_of_sqrt_memH1 {ρ : Torus 1 → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar 1 = 1) (hρ : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    MemLp ρ 2 (haar 1) := by
  obtain ⟨M, hM⟩ := ae_bounded_of_memH1 hρ
  refine MemLp.of_bound (integrable_of_integral_eq_one hρ1).aestronglyMeasurable (M ^ 2) ?_
  filter_upwards [hM] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 x), ← Real.sq_sqrt (hρ0 x)]
  calc Real.sqrt (ρ x) ^ 2 = |Real.sqrt (ρ x)| ^ 2 := (sq_abs _).symm
    _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hx 2

/-- `\widehat{2uu'}(n) = 2πin ρ̂(n)` for the periodic lifts. -/
theorem heatCoeff_lift_grad {ρ : Torus 1 → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar 1 = 1) (hρ : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) (n : ℤ) :
    heatCoeff (fun x => 2 * Real.sqrt (ρ (lineT x)) *
        weakGrad (fun x => Real.sqrt (ρ x)) (lineT x) 0) n =
      2 * π * I * n * heatCoeff (fun x => ρ (lineT x)) n := by
  set u : Torus 1 → ℝ := fun x => Real.sqrt (ρ x) with hu_def
  have hw := isWeakGrad_weakGrad hρ.1
  have hu2 : MemLp u 2 (haar 1) := hρ.2.1
  have hg2 := memLp_weakGrad_zero hρ
  have hg2' : ∀ j, MemLp (fun x => weakGrad u x j) 2 (haar 1) := fun j => by
    rw [Subsingleton.elim j 0]; exact hg2
  have hsq := isWeakGrad_sq hw hu2 hg2'
  have hρu : (fun y => u y ^ 2) = ρ := funext fun y => Real.sq_sqrt (hρ0 y)
  rw [hρu] at hsq
  have hi := integrable_of_integral_eq_one hρ1
  have hgi : ∀ j, Integrable (fun y => 2 * u y * weakGrad u y j) (haar 1) := fun j => by
    rw [Subsingleton.elim j 0]
    refine Integrable.mono' (hu2.integrable_sq.add hg2.integrable_sq)
      ((hu2.aestronglyMeasurable.const_mul 2).mul hg2.aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    show ‖2 * u y * weakGrad u y 0‖ ≤ u y ^ 2 + weakGrad u y 0 ^ 2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg (u y + weakGrad u y 0), sq_nonneg (u y - weakGrad u y 0)]
  have h := mFourierCoeff_grad hsq hi hgi (fun _ => n) 0
  rw [mFourierCoeff_eq_heatCoeff (hgi 0).aestronglyMeasurable,
    mFourierCoeff_eq_heatCoeff hi.aestronglyMeasurable] at h
  exact h

/-! ### `I(p_s) ≤ I(ρ)` -/

theorem sq_le_four_mul_of_forall {A Q D : ℝ} (hA : 0 < A) (hQ : 0 ≤ Q)
    (h : ∀ l > 0, |D| ≤ l * A + Q / l) : D ^ 2 ≤ 4 * A * Q := by
  by_cases hD : D = 0
  · subst hD; nlinarith
  have hDp : 0 < |D| := abs_pos.mpr hD
  have hl : 0 < |D| / (2 * A) := by positivity
  have h1 := h _ hl
  have h2 : |D| / (2 * A) * A = |D| / 2 := by field_simp
  have h3 : Q / (|D| / (2 * A)) = 2 * A * Q / |D| := by field_simp
  rw [h2, h3] at h1
  have h4 : |D| / 2 ≤ 2 * A * Q / |D| := by linarith
  rw [le_div_iff₀ hDp] at h4
  nlinarith [sq_abs D]

theorem two_mul_le_of_pos {l : ℝ} (hl : 0 < l) (a b : ℝ) :
    2 * a * b ≤ l * a ^ 2 + b ^ 2 / l := by
  have : l * a ^ 2 + b ^ 2 / l - 2 * a * b = (l * a - b) ^ 2 / l := by field_simp; ring
  have h0 : 0 ≤ (l * a - b) ^ 2 / l := div_nonneg (sq_nonneg _) hl.le
  linarith

theorem abs_heatK_le {t : ℝ} (ht : 0 < t) (z : ℝ) : |heatK t z| ≤ ∑' n, heatBound 1 0 t n :=
  (Complex.abs_re_le_norm _).trans (norm_heatSeries_le (c := fun _ => 1) (C := 1)
    (fun n => by simp) 0 ht le_rfl z)

/-- `I(p_s) ≤ 4∫w²` when `r = v²` and `\widehat{2vw}(n) = 2πin r̂(n)`: weighted Cauchy–Schwarz
`(K_s*(2vw))² ≤ (K_s*v²)(K_s*4w²)` and `∫₀¹ K_s(x - y) dx = 1`. -/
theorem fisherI_le_of_coeff {r v w : ℝ → ℝ} (hr0 : ∀ y, 0 ≤ r y)
    (hr1 : ∫ y in (0 : ℝ)..1, r y = 1) (hrv : ∀ y, r y = v y ^ 2)
    (hv : IntegrableOn (fun y => v y ^ 2) (Ioc 0 1)) (hw : IntegrableOn (fun y => w y ^ 2) (Ioc 0 1))
    (hvw : IntegrableOn (fun y => 2 * v y * w y) (Ioc 0 1))
    (hcoef : ∀ n : ℤ, heatCoeff (fun y => 2 * v y * w y) n = 2 * π * I * n * heatCoeff r n)
    {s : ℝ} (hs : 0 < s) : fisherI r s ≤ 4 * ∫ y in (0 : ℝ)..1, w y ^ 2 := by
  have hrI : IntervalIntegrable r volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact hv.congr_fun (fun y _ => (hrv y).symm) measurableSet_Ioc
  set G : ℝ → ℝ := fun y => 2 * v y * w y with hG
  have hGI : IntervalIntegrable G volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hvw
  have hwI : IntervalIntegrable (fun y => w y ^ 2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hw
  have hKc : ∀ x, Continuous fun y => heatK s (x - y) := fun x =>
    (continuous_heatK hs).comp (continuous_const.sub continuous_id)
  have hK0 : ∀ z, 0 ≤ heatK s z := fun z => (heatK_pos hs z).le
  set Q : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..1, heatK s (x - y) * w y ^ 2 with hQdef
  -- pointwise Cauchy–Schwarz
  have hpt : ∀ x, heatD r 1 s x ^ 2 / heat r s x ≤ 4 * Q x := by
    intro x
    have hp := heat_pos hrI hr0 hr1 hs x
    have hQ : 0 ≤ Q x := intervalIntegral.integral_nonneg zero_le_one fun y _ =>
      mul_nonneg (hK0 _) (sq_nonneg _)
    rw [div_le_iff₀ hp, heatD_one_eq_heat hcoef]
    have i1 := hGI.continuousOn_mul (hKc x).continuousOn
    have i2 := hrI.continuousOn_mul (hKc x).continuousOn
    have i3 := hwI.continuousOn_mul (hKc x).continuousOn
    have key := sq_le_four_mul_of_forall hp hQ (D := heat G s x) (fun l hl => by
      rw [heat_eq_conv hGI hs x, heat_eq_conv hrI hs x]
      have hsplit : l * (∫ y in (0 : ℝ)..1, heatK s (x - y) * r y) + Q x / l =
          ∫ y in (0 : ℝ)..1, (l * (heatK s (x - y) * r y) + heatK s (x - y) * w y ^ 2 / l) := by
        rw [intervalIntegral.integral_add (i2.const_mul l) (i3.div_const l),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
      rw [hsplit, abs_le]
      constructor
      · rw [← intervalIntegral.integral_neg]
        refine intervalIntegral.integral_mono_on zero_le_one
          (((i2.const_mul l).add (i3.div_const l)).neg) i1 fun y _ => ?_
        have h2 := mul_le_mul_of_nonneg_left (two_mul_le_of_pos hl (-v y) (w y)) (hK0 (x - y))
        have e1 : heatK s (x - y) * (l * (-v y) ^ 2 + w y ^ 2 / l) =
            l * (heatK s (x - y) * r y) + heatK s (x - y) * w y ^ 2 / l := by rw [hrv y]; ring
        have e2 : heatK s (x - y) * (2 * (-v y) * w y) = -(heatK s (x - y) * G y) := by
          simp only [hG]; ring
        show -(l * (heatK s (x - y) * r y) + heatK s (x - y) * w y ^ 2 / l) ≤
          heatK s (x - y) * G y
        linarith
      · refine intervalIntegral.integral_mono_on zero_le_one i1
          ((i2.const_mul l).add (i3.div_const l)) fun y _ => ?_
        have h2 := mul_le_mul_of_nonneg_left (two_mul_le_of_pos hl (v y) (w y)) (hK0 (x - y))
        have e1 : heatK s (x - y) * (l * (v y) ^ 2 + w y ^ 2 / l) =
            l * (heatK s (x - y) * r y) + heatK s (x - y) * w y ^ 2 / l := by rw [hrv y]; ring
        have e2 : heatK s (x - y) * (2 * v y * w y) = heatK s (x - y) * G y := rfl
        show heatK s (x - y) * G y ≤ l * (heatK s (x - y) * r y) + heatK s (x - y) * w y ^ 2 / l
        linarith)
    linarith
  -- Fubini
  set μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioc 0 1) with hμ
  have hF : Integrable (fun z : ℝ × ℝ => heatK s (z.1 - z.2) * w z.2 ^ 2) (μ.prod μ) := by
    have h1 : Integrable (fun z : ℝ × ℝ => (1 : ℝ) * w z.2 ^ 2) (μ.prod μ) :=
      (integrable_const (1 : ℝ)).mul_prod hw
    simp only [one_mul] at h1
    exact h1.bdd_mul ((continuous_heatK hs).comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact abs_heatK_le hs _)
  have hQeq : Q = fun x => ∫ y, heatK s (x - y) * w y ^ 2 ∂μ :=
    funext fun x => intervalIntegral.integral_of_le zero_le_one
  have hQI : IntervalIntegrable Q volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one, hQeq]
    exact hF.integral_prod_left
  have hfub : ∫ x in (0 : ℝ)..1, Q x = ∫ y in (0 : ℝ)..1, w y ^ 2 := by
    rw [hQeq, intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
      integral_integral_swap (f := fun x y => heatK s (x - y) * w y ^ 2) hF]
    refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
    rw [integral_mul_const, ← intervalIntegral.integral_of_le zero_le_one, integral_heatK_sub hs,
      one_mul]
  have hcont : Continuous fun x => heatD r 1 s x ^ 2 / heat r s x :=
    ((continuous_heatD r 1 hs).pow 2).div (continuous_heatD r 0 hs)
      fun x => (heat_pos hrI hr0 hr1 hs x).ne'
  unfold fisherI
  calc ∫ x in (0 : ℝ)..1, heatD r 1 s x ^ 2 / heat r s x ≤ ∫ x in (0 : ℝ)..1, 4 * Q x :=
        intervalIntegral.integral_mono_on zero_le_one (hcont.intervalIntegrable 0 1)
          (hQI.const_mul 4) fun x _ => hpt x
    _ = 4 * ∫ y in (0 : ℝ)..1, w y ^ 2 := by rw [intervalIntegral.integral_const_mul, hfub]

/-! ### `p_s → ρ` in `L²(m)` -/

theorem integral_abs_le_sqrt {f : Torus 1 → ℝ} (hf : MemLp f 2 (haar 1)) :
    ∫ y, |f y| ∂haar 1 ≤ Real.sqrt (∫ y, f y ^ 2 ∂haar 1) := by
  have hfa : MemLp (fun y => |f y|) 2 (haar 1) := hf.abs
  have hv := ProbabilityTheory.variance_nonneg (fun y => |f y|) (haar 1)
  rw [ProbabilityTheory.variance_eq_sub hfa] at hv
  simp only [Pi.pow_apply, sq_abs] at hv
  exact Real.le_sqrt_of_sq_le (by linarith)

theorem integrable_mFourier_smul {f : Torus 1 → ℝ} (hf : Integrable f (haar 1)) (k : Fin 1 → ℤ) :
    Integrable (fun t => mFourier k t • (f t : ℂ)) (haar 1) := by
  have := hf.ofReal.bdd_mul (c := 1) (mFourier k).continuous.aestronglyMeasurable
    (Eventually.of_forall fun t => norm_mFourier_le k t)
  simp only [smul_eq_mul]; exact this

theorem mFourierCoeff_sub_real {f g : Torus 1 → ℝ} (hf : Integrable f (haar 1))
    (hg : Integrable g (haar 1)) (k : Fin 1 → ℤ) :
    mFourierCoeff (fun y => ((f y - g y : ℝ) : ℂ)) k =
      mFourierCoeff (fun y => (f y : ℂ)) k - mFourierCoeff (fun y => (g y : ℂ)) k := by
  simp only [mFourierCoeff_eq_integral]
  rw [← integral_sub (integrable_mFourier_smul hf (-k)) (integrable_mFourier_smul hg (-k))]
  congr 1; funext t
  push_cast
  rw [smul_sub]

/-- The heat flow of the periodic lift, as a function on `𝕋`. -/
noncomputable def heatLift (ρ : Torus 1 → ℝ) (s : ℝ) (z : Torus 1) : ℝ :=
  heat (fun x => ρ (lineT x)) s (secT z 0)

theorem heatLift_lineT (ρ : Torus 1 → ℝ) (s x : ℝ) :
    heatLift ρ s (lineT x) = heat (fun x => ρ (lineT x)) s x := by
  obtain ⟨m, hm⟩ := secT_liftT_eq (lineF x)
  unfold heatLift lineT
  rw [hm]
  exact periodic_int (fun y => heatD_add_one _ 0 s y) (m 0) x

theorem measurable_heatLift (ρ : Torus 1 → ℝ) {s : ℝ} (hs : 0 < s) :
    Measurable (heatLift ρ s) :=
  (continuous_heatD _ 0 hs).measurable.comp ((measurable_pi_apply 0).comp measurable_secT)

theorem abs_heatLift_le (ρ : Torus 1 → ℝ) {s : ℝ} (hs : 0 < s) (z : Torus 1) :
    |heatLift ρ s z| ≤ ∑' n, heatBound (∫ y in (0 : ℝ)..1, |ρ (lineT y)|) 0 s n :=
  abs_heatD_le _ 0 hs le_rfl _

theorem memLp_heatLift (ρ : Torus 1 → ℝ) {s : ℝ} (hs : 0 < s) (p : ℝ≥0∞) :
    MemLp (heatLift ρ s) p (haar 1) :=
  MemLp.of_bound (measurable_heatLift ρ hs).aestronglyMeasurable _
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact abs_heatLift_le ρ hs z)

theorem mFourierCoeff_heatLift {ρ : Torus 1 → ℝ} (hρ : Integrable ρ (haar 1)) {s : ℝ} (hs : 0 < s)
    (k : Fin 1 → ℤ) :
    mFourierCoeff (fun y => (heatLift ρ s y : ℂ)) k =
      mFourierCoeff (fun y => (ρ y : ℂ)) k * (Real.exp (-(4 * π ^ 2) * (k 0) ^ 2 * s) : ℂ) := by
  rw [mFourierCoeff_eq_heatCoeff (measurable_heatLift ρ hs).aestronglyMeasurable,
    mFourierCoeff_eq_heatCoeff hρ.aestronglyMeasurable]
  simp_rw [heatLift_lineT]
  exact heatCoeff_heat _ hs _

theorem tendsto_heatLift_L2 {ρ : Torus 1 → ℝ} (hρ : MemLp ρ 2 (haar 1)) :
    Tendsto (fun n : ℕ => ∫ y, (heatLift ρ (1 / (n + 1)) y - ρ y) ^ 2 ∂haar 1) atTop (𝓝 0) := by
  have hρi : Integrable ρ (haar 1) := hρ.integrable one_le_two
  set c := fun k => mFourierCoeff (fun y => (ρ y : ℂ)) k with hc
  set e : ℕ → (Fin 1 → ℤ) → ℝ := fun n k => Real.exp (-(4 * π ^ 2) * (k 0) ^ 2 * (1 / (n + 1)))
    with he
  have hs : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  have hval : ∀ n : ℕ, ∫ y, (heatLift ρ (1 / (n + 1)) y - ρ y) ^ 2 ∂haar 1 =
      ∑' k, ‖c k‖ ^ 2 * (1 - e n k) ^ 2 := by
    intro n
    have hP := hasSum_sq_mFourierCoeff_real ((memLp_heatLift ρ (hs n) 2).sub hρ)
    simp only [Pi.sub_apply] at hP
    rw [← hP.tsum_eq]
    congr 1; funext k
    rw [mFourierCoeff_sub_real ((memLp_heatLift ρ (hs n) 1).integrable le_rfl) hρi,
      mFourierCoeff_heatLift hρi (hs n),
      show mFourierCoeff (fun y => (ρ y : ℂ)) k = c k from rfl,
      show Real.exp (-(4 * π ^ 2) * (k 0) ^ 2 * (1 / (n + 1))) = e n k from rfl,
      show c k * (e n k : ℂ) - c k = c k * ((e n k - 1 : ℝ) : ℂ) by push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  simp_rw [hval]
  have hsum : Summable fun k => ‖c k‖ ^ 2 := (hasSum_sq_mFourierCoeff_real hρ).summable
  have h0 : (0 : ℝ) = ∑' k : Fin 1 → ℤ, (0 : ℝ) := by simp
  rw [h0]
  refine tendsto_tsum_of_dominated_convergence hsum (fun k => ?_) (Eventually.of_forall fun n k => ?_)
  · have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ => e n k) atTop (𝓝 1) := by
      have := ((Real.continuous_exp.tendsto _).comp (h1.const_mul (-(4 * π ^ 2) * (k 0) ^ 2)))
      simpa [he, Function.comp_def] using this
    have h3 := ((h2.const_sub 1).pow 2).const_mul (‖c k‖ ^ 2)
    simpa using h3
  · have he0 : 0 < e n k := Real.exp_pos _
    have he1 : e n k ≤ 1 := Real.exp_le_one_iff.mpr (by
      have : 0 ≤ (4 * π ^ 2) * ((k 0 : ℝ) ^ 2 * (1 / (n + 1))) := by positivity
      nlinarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : (1 - e n k) ^ 2 ≤ 1 := by nlinarith
    calc ‖c k‖ ^ 2 * (1 - e n k) ^ 2 ≤ ‖c k‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = ‖c k‖ ^ 2 := mul_one _

/-! ### (3.10) on the full domain -/

/-- Sub-milestone (d): `H(ρ|m) ≤ 6 log(1 + I(ρ|m)/(12a))` for `√ρ ∈ H¹(m)`, with
`I(ρ|m) = 4∫u'²`. -/
theorem klDiv_le_log_fisher_H1 {ρ : Torus 1 → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar 1 = 1) (hρ : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    klDiv (densMeasure ρ) (haar 1) ≤ ENNReal.ofReal (6 * Real.log (1 +
      (4 * ∫ x, weakGrad (fun x => Real.sqrt (ρ x)) x 0 ^ 2 ∂haar 1) / (12 * (4 * π ^ 2)))) := by
  set u : Torus 1 → ℝ := fun x => Real.sqrt (ρ x) with hu_def
  set J := 4 * ∫ x, weakGrad u x 0 ^ 2 ∂haar 1 with hJ
  set B := 6 * Real.log (1 + J / (12 * (4 * π ^ 2))) with hB
  set r : ℝ → ℝ := fun x => ρ (lineT x) with hr
  have hi := integrable_of_integral_eq_one hρ1
  have hu2 : MemLp u 2 (haar 1) := hρ.2.1
  have hg2 := memLp_weakGrad_zero hρ
  have huu : Integrable (fun y => 2 * u y * weakGrad u y 0) (haar 1) := by
    refine Integrable.mono' (hu2.integrable_sq.add hg2.integrable_sq)
      ((hu2.aestronglyMeasurable.const_mul 2).mul hg2.aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    show ‖2 * u y * weakGrad u y 0‖ ≤ u y ^ 2 + weakGrad u y 0 ^ 2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg (u y + weakGrad u y 0), sq_nonneg (u y - weakGrad u y 0)]
  have hrI : IntervalIntegrable r volume 0 1 := intervalIntegrable_lineT hi
  have hr0 : ∀ y, 0 ≤ r y := fun y => hρ0 _
  have hr1 : ∫ y in (0 : ℝ)..1, r y = 1 := by
    rw [hr, intervalIntegral_lineT hi.aestronglyMeasurable]; exact hρ1
  -- the bound along the flow
  have hflow : ∀ s > 0, entropyH r s ≤ B := by
    intro s hs
    have hI := fisherI_le_of_coeff (r := r) (v := fun y => u (lineT y))
      (w := fun y => weakGrad u (lineT y) 0) hr0 hr1 (fun y => (Real.sq_sqrt (hρ0 _)).symm)
      (integrableOn_lineT hu2.integrable_sq) (integrableOn_lineT hg2.integrable_sq)
      (integrableOn_lineT huu) (heatCoeff_lift_grad hρ0 hρ1 hρ) hs
    rw [intervalIntegral_lineT (g := fun y => weakGrad u y 0 ^ 2)
      hg2.integrable_sq.aestronglyMeasurable] at hI
    refine (entropyH_le_log_fisher hrI hr0 hr1 hs).trans ?_
    have hF0 := fisherI_nonneg hrI hr0 hr1 hs
    have hlog := Real.log_le_log (by positivity)
      (show 1 + fisherI r s / (12 * (4 * π ^ 2)) ≤ 1 + J / (12 * (4 * π ^ 2)) by gcongr)
    rw [hB]; linarith
  have hs : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  -- the entropy along the flow as a lintegral
  have hlin : ∀ s > 0, ∫⁻ y, ENNReal.ofReal (klFun (heatLift ρ s y)) ∂haar 1 =
      ENNReal.ofReal (entropyH r s) := by
    intro s hs
    have hpos : ∀ z, 0 < heatLift ρ s z := fun z => heat_pos hrI hr0 hr1 hs _
    set Bd := ∑' n, heatBound (∫ y in (0 : ℝ)..1, |r y|) 0 s n
    have hint : Integrable (fun y => klFun (heatLift ρ s y)) (haar 1) := by
      refine Integrable.of_bound (continuous_klFun.comp_aestronglyMeasurable
        (measurable_heatLift ρ hs).aestronglyMeasurable) ((Bd + 1) ^ 2)
        (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg (hpos z).le)]
      refine (klFun_le_sq (hpos z)).trans ?_
      have hb := abs_heatLift_le ρ hs z
      have h1 : |heatLift ρ s z - 1| ≤ Bd + 1 :=
        (abs_sub _ _).trans (by rw [abs_one]; linarith)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun z => klFun_nonneg (hpos z).le)]
    congr 1
    rw [← integral_lineT hint.aestronglyMeasurable, entropyH,
      intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    simp only [heatLift_lineT, hr]
  -- `L¹` convergence and an a.e. convergent subsequence
  have hρ2 := memLp_two_of_sqrt_memH1 hρ0 hρ1 hρ
  have hL2 := tendsto_heatLift_L2 hρ2
  have hL1 : Tendsto (fun n : ℕ => ∫⁻ y, ‖heatLift ρ (1 / (n + 1)) y - ρ y‖ₑ ∂haar 1) atTop
      (𝓝 0) := by
    have hb : ∀ n : ℕ, ∫⁻ y, ‖heatLift ρ (1 / (n + 1)) y - ρ y‖ₑ ∂haar 1 ≤
        ENNReal.ofReal (Real.sqrt (∫ y, (heatLift ρ (1 / (n + 1)) y - ρ y) ^ 2 ∂haar 1)) := by
      intro n
      have hm := (memLp_heatLift ρ (hs n) 2).sub hρ2
      rw [show (fun y => ‖heatLift ρ (1 / (n + 1)) y - ρ y‖ₑ) =
        fun y => ‖(heatLift ρ (1 / (n + 1)) - ρ) y‖ₑ from rfl,
        ← ofReal_integral_norm_eq_lintegral_enorm (hm.integrable one_le_two)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := integral_abs_le_sqrt hm
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using this
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal
        (Real.sqrt (∫ y, (heatLift ρ (1 / (n + 1)) y - ρ y) ^ 2 ∂haar 1))) atTop (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto _).comp ((Real.continuous_sqrt.tendsto _).comp hL2)
      simpa [Function.comp_def] using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le) hb
  obtain ⟨ns, -, hae⟩ := exists_subseq_ae_of_tendsto_lintegral
    (F := fun n : ℕ => heatLift ρ (1 / (n + 1))) (f := ρ)
    (fun n => (measurable_heatLift ρ (hs n)).aestronglyMeasurable) hi.aestronglyMeasurable hL1
  -- Fatou
  have hcont : Continuous fun p : ℝ => ENNReal.ofReal (klFun p) :=
    ENNReal.continuous_ofReal.comp continuous_klFun
  rw [klDiv_densMeasure hρ0 hρ1]
  calc ∫⁻ y, ENNReal.ofReal (klFun (ρ y)) ∂haar 1
      = ∫⁻ y, liminf (fun k => ENNReal.ofReal (klFun (heatLift ρ (1 / (ns k + 1)) y))) atTop
          ∂haar 1 :=
        lintegral_congr_ae (hae.mono fun y hy =>
          ((hcont.tendsto _).comp hy).liminf_eq.symm)
    _ ≤ liminf (fun k => ∫⁻ y, ENNReal.ofReal (klFun (heatLift ρ (1 / (ns k + 1)) y)) ∂haar 1)
          atTop :=
        lintegral_liminf_le' fun k => (ENNReal.measurable_ofReal.comp
          (continuous_klFun.measurable.comp (measurable_heatLift ρ (hs _)))).aemeasurable
    _ ≤ ENNReal.ofReal B :=
        liminf_le_of_frequently_le' (Eventually.frequently (Eventually.of_forall fun k => by
          rw [hlin _ (hs _)]; exact ENNReal.ofReal_le_ofReal (hflow _ (hs _))))

/-- Sub-milestone (e): Lemma 3.2, (3.10) and (3.11), with finiteness. -/
theorem circle_quantitative_lsi_aux {ρ : Torus 1 → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar 1 = 1) (hρ : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    klDiv (densMeasure ρ) (haar 1) ≠ ⊤ ∧ fisherInfo (densMeasure ρ) (haar 1) ≠ ⊤ ∧
    (klDiv (densMeasure ρ) (haar 1)).toReal ≤
      6 * Real.log (1 + (fisherInfo (densMeasure ρ) (haar 1)).toReal / (12 * aCos)) ∧
    aCos / 6 * (klDiv (densMeasure ρ) (haar 1)).toReal ^ 2 ≤
      (fisherInfo (densMeasure ρ) (haar 1)).toReal -
        2 * aCos * (klDiv (densMeasure ρ) (haar 1)).toReal := by
  set J := 4 * ∫ x, weakGrad (fun x => Real.sqrt (ρ x)) x 0 ^ 2 ∂haar 1 with hJ
  have hJ0 : 0 ≤ J := mul_nonneg (by norm_num) (integral_nonneg fun x => sq_nonneg _)
  have ha : aCos = 4 * π ^ 2 := rfl
  have ha0 : 0 < aCos := by rw [ha]; positivity
  have hfi : fisherInfo (densMeasure ρ) (haar 1) = ENNReal.ofReal J :=
    fisherInfo_densMeasure_eq hρ0 hρ1 hρ
  have hkl := klDiv_le_log_fisher_H1 hρ0 hρ1 hρ
  rw [← hJ, ← ha] at hkl
  have hB0 : 0 ≤ 6 * Real.log (1 + J / (12 * aCos)) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by
      have : 0 ≤ J / (12 * aCos) := by positivity
      linarith))
  have hH := ENNReal.toReal_le_of_le_ofReal hB0 hkl
  have hIt : (fisherInfo (densMeasure ρ) (haar 1)).toReal = J := by
    rw [hfi, ENNReal.toReal_ofReal hJ0]
  rw [hIt]
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl, by rw [hfi]; exact ENNReal.ofReal_ne_top,
    hH, ?_⟩
  set H := (klDiv (densMeasure ρ) (haar 1)).toReal
  have hH0 : 0 ≤ H := ENNReal.toReal_nonneg
  have hpos : 0 < 1 + J / (12 * aCos) := by positivity
  have h1 : Real.exp (H / 6) ≤ 1 + J / (12 * aCos) := by
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.mpr (by linarith)
  have h2 := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ H / 6)
  have h3 : 1 + H / 6 + (H / 6) ^ 2 / 2 ≤ 1 + J / (12 * aCos) := h2.trans h1
  have h4 : 12 * aCos * (H / 6 + (H / 6) ^ 2 / 2) ≤ J := by
    have := mul_le_mul_of_nonneg_left (by linarith : H / 6 + (H / 6) ^ 2 / 2 ≤ J / (12 * aCos))
      (by positivity : (0 : ℝ) ≤ 12 * aCos)
    rwa [mul_div_cancel₀ _ (by positivity)] at this
  nlinarith

end SharpLSI
