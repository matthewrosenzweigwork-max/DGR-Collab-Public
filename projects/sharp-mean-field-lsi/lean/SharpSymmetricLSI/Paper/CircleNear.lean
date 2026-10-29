import SharpSymmetricLSI.Paper.CircleLSIExt

/-!
# Lemma 3.3: near-extremizers of the circle LSI (Phase 3, lane C; R11)

For a sequence with `I(ρ_n)/(2H(ρ_n)) → a`: (3.11) forces `H → 0`, hence `I → 0`; then
`|√ρ - 1| ≤ δ + δ²` with `δ² = I/4` (`H¹(𝕋) ⊂ L^∞` and the mean of `√ρ` tends to `1`), so
`ρ → 1` uniformly. With `S = ∫(ρ-1)²`, the Taylor bounds `S/(2(1+ε)) ≤ H ≤ S/(2(1-ε))`, and
Parseval for `ρ` and for its weak derivative `2uu'` (`∫(2uu')² ≤ (1+ε) I`) give
`2Q ≤ S` and `4π²(4S - 6Q) ≤ (1+ε) I`, whence `Q/H → 1`.
-/

open MeasureTheory InformationTheory Set Filter Topology Complex
open scoped ENNReal Real
open UnitAddTorus

namespace SharpLSI

theorem memH1_sqrt_of_fisherInfo_ne_top {ρ : Torus 1 → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar 1 = 1) (hI : fisherInfo (densMeasure ρ) (haar 1) ≠ ⊤) :
    MemH1 (haar 1) (fun x => Real.sqrt (ρ x)) := by
  have hi := integrable_of_integral_eq_one hρ1
  have hcond : densMeasure ρ ≪ haar 1 ∧ MemH1 (haar 1)
      (fun x => Real.sqrt ((densMeasure ρ).rnDeriv (haar 1) x).toReal) := by
    by_contra hc; apply hI; unfold fisherInfo; rw [if_neg hc]
  have hm : AEMeasurable (fun x => ENNReal.ofReal (ρ x)) (haar 1) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hi.aestronglyMeasurable.aemeasurable
  have huv : (fun x => Real.sqrt ((densMeasure ρ).rnDeriv (haar 1) x).toReal) =ᵐ[haar 1]
      fun x => Real.sqrt (ρ x) := by
    filter_upwards [Measure.rnDeriv_withDensity₀ (haar 1) hm] with x hx
    rw [show densMeasure ρ = (haar 1).withDensity _ from rfl, hx, ENNReal.toReal_ofReal (hρ0 x)]
  exact (memH1_congr_ae (Q := haar 1) (Measure.AbsolutelyContinuous.refl _)
    (Measure.AbsolutelyContinuous.refl _) hcond.2 huv).1

theorem klDiv_toReal_pos {ρ : Torus 1 → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar 1 = 1)
    (hfin : klDiv (densMeasure ρ) (haar 1) ≠ ⊤) (hne : ¬ (ρ =ᵐ[haar 1] fun _ => 1)) :
    0 < (klDiv (densMeasure ρ) (haar 1)).toReal := by
  refine ENNReal.toReal_pos (fun h0 => hne ?_) hfin
  have := isProbabilityMeasure_densMeasure hρ0 hρ1
  have heq : densMeasure ρ = haar 1 := klDiv_eq_zero_iff.mp h0
  have hi := integrable_of_integral_eq_one hρ1
  have hm : AEMeasurable (fun x => ENNReal.ofReal (ρ x)) (haar 1) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hi.aestronglyMeasurable.aemeasurable
  have h1 := Measure.rnDeriv_withDensity₀ (haar 1) hm
  change (densMeasure ρ).rnDeriv (haar 1) =ᵐ[haar 1] _ at h1
  rw [heq] at h1
  filter_upwards [h1, Measure.rnDeriv_self (haar 1)] with x hx1 hx2
  rw [hx1] at hx2
  exact ENNReal.ofReal_eq_one.mp hx2

/-- `|√ρ - 1| ≤ δ + δ²` a.e., `δ² = ∫u'²`. -/
theorem ae_abs_sqrt_sub_one_le {ρ : Torus 1 → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar 1 = 1) (hρ : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    ∀ᵐ x ∂haar 1, |Real.sqrt (ρ x) - 1| ≤
      Real.sqrt (∫ y, weakGrad (fun x => Real.sqrt (ρ x)) y 0 ^ 2 ∂haar 1) +
        ∫ y, weakGrad (fun x => Real.sqrt (ρ x)) y 0 ^ 2 ∂haar 1 := by
  set u : Torus 1 → ℝ := fun x => Real.sqrt (ρ x) with hu_def
  set W := ∫ y, weakGrad u y 0 ^ 2 ∂haar 1 with hW
  have hW0 : 0 ≤ W := integral_nonneg fun y => sq_nonneg _
  have hg2 := memLp_weakGrad_zero hρ
  have hL1 : ∫ y, |weakGrad u y 0| ∂haar 1 ≤ Real.sqrt W := integral_abs_le_sqrt hg2
  have hae := ae_abs_sub_mean_le hρ
  set m := ∫ y, u y ∂haar 1 with hm
  have hu2 : MemLp u 2 (haar 1) := hρ.2.1
  have hm0 : 0 ≤ m := integral_nonneg fun x => Real.sqrt_nonneg _
  have huu : ∫ y, u y ^ 2 ∂haar 1 = 1 := by
    simp_rw [hu_def, Real.sq_sqrt (hρ0 _)]; exact hρ1
  have hvar : ProbabilityTheory.variance u (haar 1) = 1 - m ^ 2 := by
    rw [ProbabilityTheory.variance_eq_sub hu2]
    simp only [Pi.pow_apply]
    rw [huu]
  have hvar' : ProbabilityTheory.variance u (haar 1) = ∫ y, (u y - m) ^ 2 ∂haar 1 :=
    ProbabilityTheory.variance_eq_integral hu2.aestronglyMeasurable.aemeasurable
  have hle : ∫ y, (u y - m) ^ 2 ∂haar 1 ≤ W := by
    have : ∫ y, (u y - m) ^ 2 ∂haar 1 ≤ ∫ y, Real.sqrt W ^ 2 ∂haar 1 := by
      refine integral_mono_ae ((hu2.sub (memLp_const m)).integrable_sq) (integrable_const _) ?_
      filter_upwards [hae] with y hy
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hy.trans hL1) 2
    simpa [Real.sq_sqrt hW0] using this
  have hv0 := ProbabilityTheory.variance_nonneg u (haar 1)
  have hm1 : m ≤ 1 := by nlinarith
  have hmm : |m - 1| ≤ W := by
    rw [abs_of_nonpos (by linarith)]
    nlinarith
  filter_upwards [hae] with x hx
  calc |u x - 1| = |(u x - m) + (m - 1)| := by ring_nf
    _ ≤ |u x - m| + |m - 1| := abs_add_le _ _
    _ ≤ Real.sqrt W + W := by linarith

/-- `|ρ - 1| ≤ e(2 + e)` a.e., `e = δ + δ²`. -/
theorem ae_abs_sub_one_le {ρ : Torus 1 → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar 1 = 1) (hρ : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    ∀ᵐ x ∂haar 1, |ρ x - 1| ≤
      (Real.sqrt (∫ y, weakGrad (fun x => Real.sqrt (ρ x)) y 0 ^ 2 ∂haar 1) +
        ∫ y, weakGrad (fun x => Real.sqrt (ρ x)) y 0 ^ 2 ∂haar 1) *
      (2 + (Real.sqrt (∫ y, weakGrad (fun x => Real.sqrt (ρ x)) y 0 ^ 2 ∂haar 1) +
        ∫ y, weakGrad (fun x => Real.sqrt (ρ x)) y 0 ^ 2 ∂haar 1)) := by
  filter_upwards [ae_abs_sqrt_sub_one_le hρ0 hρ1 hρ] with x hx
  set e := Real.sqrt (∫ y, weakGrad (fun x => Real.sqrt (ρ x)) y 0 ^ 2 ∂haar 1) +
        ∫ y, weakGrad (fun x => Real.sqrt (ρ x)) y 0 ^ 2 ∂haar 1
  have h1 : ρ x - 1 = (Real.sqrt (ρ x) - 1) * ((Real.sqrt (ρ x) - 1) + 2) := by
    have := Real.sq_sqrt (hρ0 x); nlinarith
  rw [h1, abs_mul]
  have h2 : |(Real.sqrt (ρ x) - 1) + 2| ≤ 2 + e :=
    (abs_add_le _ _).trans (by rw [abs_two]; linarith)
  exact mul_le_mul hx h2 (abs_nonneg _) ((abs_nonneg _).trans hx)

/-! ### Fourier bounds -/

theorem mFourierCoeff_neg_real {f : Torus 1 → ℝ} (hf : AEStronglyMeasurable f (haar 1))
    (k : Fin 1 → ℤ) :
    mFourierCoeff (fun y => (f y : ℂ)) (-k) = (starRingEnd ℂ) (mFourierCoeff (fun y => (f y : ℂ)) k) := by
  rw [mFourierCoeff_eq_heatCoeff hf, mFourierCoeff_eq_heatCoeff hf, Pi.neg_apply, heatCoeff_neg]

theorem firstMode_eq_norm_sq {ρ : Torus 1 → ℝ} :
    firstMode ρ = ‖mFourierCoeff (fun y => (ρ y : ℂ)) (-(fun _ : Fin 1 => (1 : ℤ)))‖ ^ 2 := by
  rw [firstMode, Complex.normSq_eq_norm_sq, mFourierCoeff_eq_integral, neg_neg]
  congr 2
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul, mFourier, ContinuousMap.coe_mk, Fin.prod_univ_one, expT]

theorem fourier_near_bounds {ρ : Torus 1 → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar 1 = 1) (hρ : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) {ε : ℝ}
    (hε : ∀ᵐ x ∂haar 1, |ρ x - 1| ≤ ε) :
    2 * firstMode ρ ≤ ∫ x, (ρ x - 1) ^ 2 ∂haar 1 ∧
    4 * π ^ 2 * (4 * ∫ x, (ρ x - 1) ^ 2 ∂haar 1 - 6 * firstMode ρ) ≤
      (1 + ε) * (4 * ∫ x, weakGrad (fun x => Real.sqrt (ρ x)) x 0 ^ 2 ∂haar 1) := by
  set u : Torus 1 → ℝ := fun x => Real.sqrt (ρ x) with hu_def
  set S := ∫ x, (ρ x - 1) ^ 2 ∂haar 1 with hS
  have hi := integrable_of_integral_eq_one hρ1
  have hρ2 := memLp_two_of_sqrt_memH1 hρ0 hρ1 hρ
  set c := fun k => mFourierCoeff (fun y => (ρ y : ℂ)) k with hc
  set x : (Fin 1 → ℤ) → ℝ := fun k => ‖c k‖ ^ 2 with hx
  have hP : HasSum x (∫ y, ρ y ^ 2 ∂haar 1) := hasSum_sq_mFourierCoeff_real hρ2
  have hρρ : ∫ y, ρ y ^ 2 ∂haar 1 = 1 + S := by
    have e : ∀ y, (ρ y - 1) ^ 2 = ρ y ^ 2 - 2 * ρ y + 1 := fun y => by ring
    simp_rw [hS, e]
    rw [integral_add (f := fun y => ρ y ^ 2 - 2 * ρ y) (g := fun _ => (1 : ℝ))
      (hρ2.integrable_sq.sub (hi.const_mul 2)) (integrable_const _),
      integral_sub (f := fun y => ρ y ^ 2) (g := fun y => 2 * ρ y) hρ2.integrable_sq
        (hi.const_mul 2), integral_const_mul, hρ1]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  rw [hρρ] at hP
  set e1 : Fin 1 → ℤ := fun _ => 1 with he1
  have hx0 : x 0 = 1 := by
    have hc0 : c 0 = ((∫ y, ρ y ∂haar 1 : ℝ) : ℂ) := by
      simp only [hc, mFourierCoeff_eq_integral, neg_zero, mFourier_zero, ContinuousMap.one_apply,
        one_smul]
      exact integral_ofReal
    simp only [hx, hc0, hρ1, Complex.ofReal_one, norm_one, one_pow]
  have hQ : firstMode ρ = x (-e1) := firstMode_eq_norm_sq
  have hQ' : x e1 = x (-e1) := by
    simp only [hx, hc]
    rw [mFourierCoeff_neg_real hi.aestronglyMeasurable, Complex.norm_conj]
  have hne1 : e1 ≠ 0 := fun h => by have := congrFun h 0; simp [he1] at this
  have hne2 : -e1 ≠ 0 := fun h => by have := congrFun h 0; simp [he1] at this
  have hne3 : e1 ≠ -e1 := fun h => by have := congrFun h 0; simp [he1] at this
  have hx_nn : ∀ k, 0 ≤ x k := fun k => sq_nonneg _
  refine ⟨?_, ?_⟩
  · -- `x 0 + x e1 + x (-e1) ≤ 1 + S`
    have h := sum_le_hasSum ({0, e1, -e1} : Finset (Fin 1 → ℤ)) (fun k _ => hx_nn k) hP
    rw [Finset.sum_insert (by simp [hne1.symm, hne2.symm]), Finset.sum_insert (by simp [hne3]),
      Finset.sum_singleton, hx0] at h
    rw [hQ]; linarith
  · -- the derivative
    have hw := isWeakGrad_weakGrad hρ.1
    have hu2 : MemLp u 2 (haar 1) := hρ.2.1
    have hg2 := memLp_weakGrad_zero hρ
    have hg2' : ∀ j, MemLp (fun x => weakGrad u x j) 2 (haar 1) := fun j => by
      rw [Subsingleton.elim j 0]; exact hg2
    have hsq := isWeakGrad_sq hw hu2 hg2'
    have hρu : (fun y => u y ^ 2) = ρ := funext fun y => Real.sq_sqrt (hρ0 y)
    rw [hρu] at hsq
    obtain ⟨M, hM⟩ := ae_bounded_of_memH1 hρ
    have hM0 : 0 ≤ M := by
      obtain ⟨y, hy⟩ := hM.exists; exact (abs_nonneg _).trans hy
    have hG2 : ∀ j, MemLp (fun y => 2 * u y * weakGrad u y j) 2 (haar 1) := fun j => by
      rw [Subsingleton.elim j 0]
      refine (hg2.const_mul (2 * M)).of_le ((hu2.aestronglyMeasurable.const_mul 2).mul
        hg2.aestronglyMeasurable) ?_
      filter_upwards [hM] with y hy
      simp only [Real.norm_eq_abs, abs_mul, abs_two]
      rw [abs_of_nonneg hM0]
      calc 2 * |u y| * |weakGrad u y 0| ≤ 2 * M * |weakGrad u y 0| := by gcongr
        _ = _ := by ring
    have hgi : ∀ j, Integrable (fun y => 2 * u y * weakGrad u y j) (haar 1) := fun j =>
      (hG2 j).integrable one_le_two
    have hG : HasSum (fun k => 4 * π ^ 2 * ((k 0 : ℝ)) ^ 2 * x k)
        (∫ y, (2 * u y * weakGrad u y 0) ^ 2 ∂haar 1) := by
      have := hasSum_sq_mFourierCoeff_real (hG2 0)
      convert this using 1
      funext k
      rw [mFourierCoeff_grad hsq hi hgi k 0, norm_mul]
      have : ‖2 * (π : ℂ) * I * (k 0 : ℂ)‖ = 2 * π * |(k 0 : ℝ)| := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_two]
        rw [show ((k 0 : ℤ) : ℂ) = (((k 0 : ℤ) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        ring
      rw [this, mul_pow, mul_pow, mul_pow, sq_abs]
      simp only [hx, hc]
      ring
    -- `∫ (2uu')² ≤ (1+ε) · 4∫u'²`
    have hbd : ∫ y, (2 * u y * weakGrad u y 0) ^ 2 ∂haar 1 ≤
        (1 + ε) * (4 * ∫ y, weakGrad u y 0 ^ 2 ∂haar 1) := by
      rw [← integral_const_mul, ← integral_const_mul]
      refine integral_mono_ae (hG2 0).integrable_sq ((hg2.integrable_sq.const_mul 4).const_mul _) ?_
      filter_upwards [hε] with y hy
      have hρy : u y ^ 2 ≤ 1 + ε := by
        rw [hu_def]; simp only; rw [Real.sq_sqrt (hρ0 y)]
        have := (abs_le.mp hy).2; linarith
      have : (2 * u y * weakGrad u y 0) ^ 2 = 4 * u y ^ 2 * weakGrad u y 0 ^ 2 := by ring
      rw [this]
      nlinarith [sq_nonneg (weakGrad u y 0)]
    -- comparison of the two sums
    have hF : HasSum (fun k => 4 * π ^ 2 * (4 * x k - (if k = 0 then 4 * x 0 else 0) -
        (if k = e1 then 3 * x e1 else 0) - (if k = -e1 then 3 * x (-e1) else 0)))
        (4 * π ^ 2 * (4 * (1 + S) - 4 * x 0 - 3 * x e1 - 3 * x (-e1))) :=
      ((((hP.mul_left 4).sub (hasSum_ite_eq 0 (4 * x 0))).sub
        (hasSum_ite_eq e1 (3 * x e1))).sub (hasSum_ite_eq (-e1) (3 * x (-e1)))).mul_left _
    have hle := hasSum_le (fun k => ?_) hF hG
    · rw [hx0, hQ', ← hQ] at hle
      linarith
    · have hpi : 0 ≤ 4 * π ^ 2 := by positivity
      by_cases h0 : k = 0
      · subst h0
        rw [if_pos rfl, if_neg hne1.symm, if_neg hne2.symm]
        simp
      by_cases h1 : k = e1
      · subst h1
        rw [if_neg hne1, if_pos rfl, if_neg hne3]
        have : ((e1 0 : ℤ) : ℝ) = 1 := by simp [he1]
        rw [this]
        nlinarith [hx_nn e1]
      by_cases h2 : k = -e1
      · subst h2
        rw [if_neg hne2, if_neg (Ne.symm hne3), if_pos rfl]
        have : (((-e1) 0 : ℤ) : ℝ) = -1 := by simp [he1]
        rw [this]
        nlinarith [hx_nn (-e1)]
      · simp only [if_neg h0, if_neg h1, if_neg h2]
        have hk : 4 ≤ ((k 0 : ℤ) : ℝ) ^ 2 := by
          have hk0 : k 0 ≠ 0 := fun h => h0 (funext fun i => by rw [Subsingleton.elim i 0]; exact h)
          have hk1 : k 0 ≠ 1 := fun h => h1 (funext fun i => by rw [Subsingleton.elim i 0]; exact h)
          have hk2 : k 0 ≠ -1 := fun h => h2 (funext fun i => by
            rw [Subsingleton.elim i 0]; simpa [he1] using h)
          have : (2 : ℤ) ≤ |k 0| := by
            rcases le_or_gt 0 (k 0) with hpos | hneg
            · rw [abs_of_nonneg hpos]; omega
            · rw [abs_of_neg hneg]; omega
          have h4 : (4 : ℤ) ≤ k 0 ^ 2 := by nlinarith [sq_abs (k 0), abs_nonneg (k 0)]
          exact_mod_cast h4
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk (hx_nn k)) hpi
        linarith

/-! ### Taylor bounds for the entropy -/

theorem klDiv_near_bounds {ρ : Torus 1 → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar 1 = 1) (hρ2 : MemLp ρ 2 (haar 1)) {ε : ℝ} (hε1 : ε < 1)
    (hε : ∀ᵐ x ∂haar 1, |ρ x - 1| ≤ ε) :
    (∫ x, (ρ x - 1) ^ 2 ∂haar 1) / (2 * (1 + ε)) ≤ (klDiv (densMeasure ρ) (haar 1)).toReal ∧
    (klDiv (densMeasure ρ) (haar 1)).toReal ≤ (∫ x, (ρ x - 1) ^ 2 ∂haar 1) / (2 * (1 - ε)) := by
  have hi := integrable_of_integral_eq_one hρ1
  have hε0 : 0 ≤ ε := by obtain ⟨y, hy⟩ := hε.exists; exact (abs_nonneg _).trans hy
  have hs2 : Integrable (fun x => (ρ x - 1) ^ 2) (haar 1) := (hρ2.sub (memLp_const 1)).integrable_sq
  have hb : ∀ᵐ x ∂haar 1, (ρ x - 1) ^ 2 / (2 * (1 + ε)) ≤ klFun (ρ x) ∧
      klFun (ρ x) ≤ (ρ x - 1) ^ 2 / (2 * (1 - ε)) := by
    filter_upwards [hε] with x hx
    have h := mul_log_taylor_bounds hε1 hx
    rw [show 1 + (ρ x - 1) = ρ x by ring] at h
    rw [klFun_apply]
    constructor <;> linarith [h.1, h.2]
  have hmeas : AEStronglyMeasurable (fun x => klFun (ρ x)) (haar 1) :=
    continuous_klFun.comp_aestronglyMeasurable hi.aestronglyMeasurable
  have hint : Integrable (fun x => klFun (ρ x)) (haar 1) :=
    (hs2.div_const (2 * (1 - ε))).mono' hmeas (hb.mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg (hρ0 x))]; exact hx.2)
  have hH : (klDiv (densMeasure ρ) (haar 1)).toReal = ∫ x, klFun (ρ x) ∂haar 1 := by
    rw [klDiv_densMeasure hρ0 hρ1, integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun x => klFun_nonneg (hρ0 x)) hmeas]
  rw [hH, ← integral_div, ← integral_div]
  exact ⟨integral_mono_ae (hs2.div_const _) hint (hb.mono fun x hx => hx.1),
    integral_mono_ae hint (hs2.div_const _) (hb.mono fun x hx => hx.2)⟩

/-! ### Lemma 3.3 -/

theorem circle_near_extremizers_aux {ρ : ℕ → Torus 1 → ℝ} (hρ0 : ∀ n x, 0 ≤ ρ n x)
    (hρ1 : ∀ n, ∫ x, ρ n x ∂haar 1 = 1) (hne : ∀ n, ¬ (ρ n =ᵐ[haar 1] fun _ => 1))
    (hI : ∀ n, fisherInfo (densMeasure (ρ n)) (haar 1) ≠ ⊤)
    (hlim : Tendsto (fun n => (fisherInfo (densMeasure (ρ n)) (haar 1)).toReal /
        (2 * (klDiv (densMeasure (ρ n)) (haar 1)).toReal)) atTop (𝓝 aCos)) :
    Tendsto (fun n => (klDiv (densMeasure (ρ n)) (haar 1)).toReal) atTop (𝓝 0) ∧
    Tendsto (fun n => (fisherInfo (densMeasure (ρ n)) (haar 1)).toReal) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (fun x => ρ n x - 1) ⊤ (haar 1)) atTop (𝓝 0) ∧
    Tendsto (fun n => firstMode (ρ n) / (klDiv (densMeasure (ρ n)) (haar 1)).toReal) atTop
      (𝓝 1) := by
  set H := fun n => (klDiv (densMeasure (ρ n)) (haar 1)).toReal with hHdef
  set I := fun n => (fisherInfo (densMeasure (ρ n)) (haar 1)).toReal with hIdef
  set r := fun n => I n / (2 * H n) with hrdef
  have ha : aCos = 4 * π ^ 2 := rfl
  have ha0 : 0 < aCos := by rw [ha]; positivity
  have hH1 : ∀ n, MemH1 (haar 1) (fun x => Real.sqrt (ρ n x)) := fun n =>
    memH1_sqrt_of_fisherInfo_ne_top (hρ0 n) (hρ1 n) (hI n)
  have haux := fun n => circle_quantitative_lsi_aux (hρ0 n) (hρ1 n) (hH1 n)
  have hHpos : ∀ n, 0 < H n := fun n => klDiv_toReal_pos (hρ0 n) (hρ1 n) (haux n).1 (hne n)
  set W := fun n => ∫ y, weakGrad (fun x => Real.sqrt (ρ n x)) y 0 ^ 2 ∂haar 1 with hWdef
  have hW0 : ∀ n, 0 ≤ W n := fun n => integral_nonneg fun y => sq_nonneg _
  have hIW : ∀ n, I n = 4 * W n := fun n => by
    simp only [hIdef]
    rw [fisherInfo_densMeasure_eq (hρ0 n) (hρ1 n) (hH1 n),
      ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (hW0 n))]
  -- (1) `H → 0`
  have hHle : ∀ n, H n ≤ 12 / aCos * (r n - aCos) := fun n => by
    have h311 := (haux n).2.2.2
    have hp := hHpos n
    have h : aCos / 12 * H n + aCos ≤ r n := by
      simp only [hrdef]
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ ha0]
    nlinarith
  have hHlim : Tendsto H atTop (𝓝 0) := by
    have hup : Tendsto (fun n => 12 / aCos * (r n - aCos)) atTop (𝓝 0) := by
      have := (hlim.sub_const aCos).const_mul (12 / aCos)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => (hHpos n).le) hHle
  -- (2) `I → 0`
  have hIeq : ∀ n, I n = 2 * H n * r n := fun n => by
    simp only [hrdef]; field_simp [(hHpos n).ne']
  have hIlim : Tendsto I atTop (𝓝 0) := by
    have := (hHlim.const_mul 2).mul hlim
    simp only [mul_zero, zero_mul] at this
    exact this.congr fun n => (hIeq n).symm
  -- (3) uniform convergence
  set e := fun n => Real.sqrt (W n) + W n with hedef
  set ε := fun n => e n * (2 + e n) with hεdef
  have hWlim : Tendsto W atTop (𝓝 0) := by
    have := hIlim.div_const 4
    simp only [zero_div] at this
    exact this.congr fun n => by rw [hIW n]; ring
  have helim : Tendsto e atTop (𝓝 0) := by
    have := ((Real.continuous_sqrt.tendsto 0).comp hWlim).add hWlim
    simpa [Function.comp_def] using this
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have := helim.mul (helim.const_add 2)
    simpa using this
  have hae : ∀ n, ∀ᵐ x ∂haar 1, |ρ n x - 1| ≤ ε n := fun n =>
    ae_abs_sub_one_le (hρ0 n) (hρ1 n) (hH1 n)
  have hε0 : ∀ n, 0 ≤ ε n := fun n => by
    have : 0 ≤ e n := add_nonneg (Real.sqrt_nonneg _) (hW0 n)
    positivity
  refine ⟨hHlim, hIlim, ?_, ?_⟩
  · have hb : ∀ n, eLpNorm (fun x => ρ n x - 1) ⊤ (haar 1) ≤ ENNReal.ofReal (ε n) := fun n => by
      rw [eLpNorm_exponent_top (f := fun x => ρ n x - 1)
        ((integrable_of_integral_eq_one (hρ1 n)).aestronglyMeasurable.sub
          aestronglyMeasurable_const)]
      exact eLpNormEssSup_le_of_ae_bound ((hae n).mono fun x hx => by
        rw [Real.norm_eq_abs]; exact hx)
    have hl : Tendsto (fun n => ENNReal.ofReal (ε n)) atTop (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto 0).comp hεlim
      simpa [Function.comp_def] using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl (fun n => zero_le) hb
  -- (4) `Q/H → 1`
  have hsmall : ∀ᶠ n in atTop, ε n < 1 / 2 := (tendsto_order.1 hεlim).2 _ (by norm_num)
  set L := fun n => 4 / 3 * (1 - ε n) - (1 + ε n) * r n / (12 * π ^ 2) with hLdef
  have hLlim : Tendsto L atTop (𝓝 1) := by
    have := (((hεlim.const_sub 1).const_mul (4 / 3)).sub
      (((hεlim.const_add 1).mul hlim).div_const (12 * π ^ 2)))
    have e1 : (4 / 3 * (1 - 0) - (1 + 0) * aCos / (12 * π ^ 2) : ℝ) = 1 := by
      rw [ha]; field_simp; ring
    rw [e1] at this
    exact this
  have hUlim : Tendsto (fun n => 1 + ε n) atTop (𝓝 1) := by
    simpa using hεlim.const_add 1
  have hbounds : ∀ᶠ n in atTop, L n ≤ firstMode (ρ n) / H n ∧ firstMode (ρ n) / H n ≤ 1 + ε n := by
    filter_upwards [hsmall] with n hn
    have hp := hHpos n
    have hF := fourier_near_bounds (hρ0 n) (hρ1 n) (hH1 n) (hae n)
    have hK := klDiv_near_bounds (hρ0 n) (hρ1 n) (memLp_two_of_sqrt_memH1 (hρ0 n) (hρ1 n) (hH1 n))
      (by linarith) (hae n)
    set S := ∫ x, (ρ n x - 1) ^ 2 ∂haar 1
    set Q := firstMode (ρ n)
    have hεn := hε0 n
    have hIn : 4 * W n = I n := (hIW n).symm
    rw [hIn] at hF
    have hS1 : S ≤ 2 * (1 + ε n) * H n := by
      have := hK.1; rw [div_le_iff₀ (by positivity)] at this; linarith
    have hS2 : 2 * (1 - ε n) * H n ≤ S := by
      have := hK.2; rw [le_div_iff₀ (by nlinarith)] at this; linarith
    have hrH : r n * H n = I n / 2 := by simp only [hrdef]; field_simp
    constructor
    · rw [le_div_iff₀ hp]
      have hpi : 0 < 12 * π ^ 2 := by positivity
      have e2 : L n * H n = 4 / 3 * (1 - ε n) * H n - (1 + ε n) * (r n * H n) / (12 * π ^ 2) := by
        simp only [hLdef]; ring
      rw [e2, hrH]
      have h3 : 4 * π ^ 2 * (4 * S - 6 * Q) ≤ (1 + ε n) * I n := hF.2
      have h4 : (1 + ε n) * (I n / 2) / (12 * π ^ 2) = (1 + ε n) * I n / (24 * π ^ 2) := by
        field_simp; ring
      rw [h4, sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ (by positivity)]
      nlinarith [hS2, h3, Real.pi_pos]
    · rw [div_le_iff₀ hp]
      linarith [hF.1, hS1]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hLlim hUlim
    (hbounds.mono fun n h => h.1) (hbounds.mono fun n h => h.2)

end SharpLSI
