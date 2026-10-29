import FullLabeledLSI.Examples.E01g1_Basic
import FullLabeledLSI.Examples.E01g0_Classify

/-!
# Lane D, Task C (E01g4): near-uniform estimate of the scalar quotient

Statement skeleton (to be proved).  `LamF C = inf_{n ≥ 1} 4π² n² (1 - Ĉ(n))`.
-/

open MeasureTheory InformationTheory Filter Topology UnitAddTorus
open scoped Real ENNReal ContDiff ComplexConjugate

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

/-- `Λ_F = inf_{n ≥ 1} 4π² n² (1 - Ĉ(n))` (real infimum). -/
noncomputable def LamF (C : Torus 1 → ℝ) : ℝ :=
  ⨅ n : ℕ, aCos * ((n : ℝ) + 1) ^ 2 * (1 - chat C ((n : ℤ) + 1))


theorem aux_nonneg_of_deriv {g g' : ℝ → ℝ} {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hg : ∀ t, -1 < t → HasDerivAt g (g' t) t) (hg0 : g 0 = 0)
    (hpos : ∀ t, 0 ≤ t → t ≤ ε → 0 ≤ g' t) (hneg : ∀ t, -ε ≤ t → t ≤ 0 → g' t ≤ 0) :
    ∀ t, |t| ≤ ε → 0 ≤ g t := by
  intro t ht
  have ht' := abs_le.mp ht
  rcases le_total 0 t with h | h
  · have hm : MonotoneOn g (Set.Icc 0 ε) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 ε) ?_ ?_ ?_
      · intro s hs; exact (hg s (by linarith [hs.1])).continuousAt.continuousWithinAt
      · intro s hs; rw [interior_Icc] at hs
        exact (hg s (by linarith [hs.1])).differentiableAt.differentiableWithinAt
      · intro s hs; rw [interior_Icc] at hs
        rw [(hg s (by linarith [hs.1])).deriv]; exact hpos s hs.1.le hs.2.le
    have := hm ⟨le_rfl, hε⟩ ⟨h, ht'.2⟩ h
    simpa [hg0] using this
  · have hm : AntitoneOn g (Set.Icc (-ε) 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc (-ε) 0) ?_ ?_ ?_
      · intro s hs; exact (hg s (by linarith [hs.1])).continuousAt.continuousWithinAt
      · intro s hs; rw [interior_Icc] at hs
        exact (hg s (by linarith [hs.1])).differentiableAt.differentiableWithinAt
      · intro s hs; rw [interior_Icc] at hs
        rw [(hg s (by linarith [hs.1])).deriv]; exact hneg s hs.1.le hs.2.le
    have := hm ⟨ht'.1, h⟩ ⟨by linarith, le_rfl⟩ h
    simpa [hg0] using this

theorem hasDerivAt_Fent (t : ℝ) (ht : -1 < t) :
    HasDerivAt (fun t : ℝ => (1 + t) * Real.log (1 + t) - t) (Real.log (1 + t)) t := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 t := (hasDerivAt_id t).const_add 1
  have hne : (1 + t) ≠ 0 := by linarith
  have h2 := h1.log hne
  have h3 := (h1.mul h2).sub (hasDerivAt_id t)
  refine h3.congr_deriv ?_
  field_simp
  ring

theorem klFun_one_add (t : ℝ) : klFun (1 + t) = (1 + t) * Real.log (1 + t) - t := by
  rw [klFun_apply]; ring

theorem klFun_upper {ε v : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) (hv : |v| ≤ ε) :
    klFun (1 + v) ≤ v ^ 2 / (2 * (1 - ε)) := by
  have hpos : 0 < 1 - ε := by linarith
  have key := aux_nonneg_of_deriv (g := fun t => t ^ 2 / (2 * (1 - ε)) - ((1 + t) * Real.log (1 + t) - t))
    (g' := fun t => t / (1 - ε) - Real.log (1 + t)) hε hε1 ?_ ?_ ?_ ?_ v hv
  · rw [klFun_one_add]; linarith
  · intro t ht
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2 / (2 * (1 - ε))) (t / (1 - ε)) t := by
      have := ((hasDerivAt_pow 2 t).div_const (2 * (1 - ε)))
      refine this.congr_deriv ?_
      norm_num; field_simp
    exact h1.sub (hasDerivAt_Fent t ht)
  · norm_num
  · intro t h0 hte
    have hl : Real.log (1 + t) ≤ t := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + t by linarith); linarith
    have : t ≤ t / (1 - ε) := by
      rw [le_div_iff₀ hpos]; nlinarith
    linarith
  · intro t hte h0
    have h1t : 0 < 1 + t := by linarith
    have hl : t / (1 + t) ≤ Real.log (1 + t) := by
      have := Real.one_sub_inv_le_log_of_pos h1t
      have e : 1 - (1 + t)⁻¹ = t / (1 + t) := by field_simp; ring
      linarith
    have : t / (1 - ε) ≤ t / (1 + t) := by
      rw [div_le_div_iff₀ hpos h1t]; nlinarith
    linarith

theorem klFun_lower {ε v : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) (hv : |v| ≤ ε) :
    v ^ 2 / (2 * (1 + ε)) ≤ klFun (1 + v) := by
  have hpos : 0 < 1 + ε := by linarith
  have key := aux_nonneg_of_deriv (g := fun t => ((1 + t) * Real.log (1 + t) - t) - t ^ 2 / (2 * (1 + ε)))
    (g' := fun t => Real.log (1 + t) - t / (1 + ε)) hε hε1 ?_ ?_ ?_ ?_ v hv
  · rw [klFun_one_add]; linarith
  · intro t ht
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2 / (2 * (1 + ε))) (t / (1 + ε)) t := by
      have := ((hasDerivAt_pow 2 t).div_const (2 * (1 + ε)))
      refine this.congr_deriv ?_
      norm_num; field_simp
    exact (hasDerivAt_Fent t ht).sub h1
  · norm_num
  · intro t h0 hte
    have h1t : 0 < 1 + t := by linarith
    have hl : t / (1 + t) ≤ Real.log (1 + t) := by
      have := Real.one_sub_inv_le_log_of_pos h1t
      have e : 1 - (1 + t)⁻¹ = t / (1 + t) := by field_simp; ring
      linarith
    have : t / (1 + ε) ≤ t / (1 + t) := by
      rw [div_le_div_iff₀ hpos h1t]; nlinarith
    linarith
  · intro t hte h0
    have hl : Real.log (1 + t) ≤ t := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + t by linarith); linarith
    have : t ≤ t / (1 + ε) := by
      rw [le_div_iff₀ hpos]; nlinarith
    linarith


theorem entR_bounds {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) {ρ : Torus 1 → ℝ}
    (hρm : AEStronglyMeasurable ρ (haar 1)) (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar 1 = 1)
    (hb : ∀ x, |ρ x - 1| ≤ ε) :
    (∫ x, (ρ x - 1) ^ 2 ∂haar 1) / (2 * (1 + ε)) ≤ entR ρ ∧
      entR ρ ≤ (∫ x, (ρ x - 1) ^ 2 ∂haar 1) / (2 * (1 - ε)) := by
  have hρae : AEMeasurable ρ (haar 1) := hρm.aemeasurable
  have hkl : AEStronglyMeasurable (fun x => klFun (ρ x)) (haar 1) :=
    (measurable_klFun.comp_aemeasurable hρae).aestronglyMeasurable
  have hv2 : Integrable (fun x => (ρ x - 1) ^ 2) (haar 1) := by
    refine Integrable.of_bound ((hρm.sub aestronglyMeasurable_const).pow 2) (ε ^ 2)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := hb x
    have h2 : |ρ x - 1| ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    rwa [sq_abs] at h2
  have hpos1 : 0 < 1 - ε := by linarith
  have hpos2 : 0 < 1 + ε := by linarith
  have hkint : Integrable (fun x => klFun (ρ x)) (haar 1) := by
    refine Integrable.of_bound hkl ((1 + ε - 1) ^ 2 + 1) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg (h0 x))]
    have h1' : klFun (ρ x) ≤ (ρ x - 1) ^ 2 := by
      rw [klFun_apply]
      rcases (h0 x).eq_or_lt with h | h
      · rw [← h]; simp
      · have := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos h) (h0 x)
        nlinarith
    have h2 := hb x
    have h3 : |ρ x - 1| ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    rw [sq_abs] at h3
    nlinarith
  have hent : entR ρ = ∫ x, klFun (ρ x) ∂haar 1 := by
    unfold entR
    have := isProbabilityMeasure_densMeasure' h0 h1
    rw [klDiv_densMeasure' h0 h1, ← ofReal_integral_eq_lintegral_ofReal hkint
      (Eventually.of_forall fun x => klFun_nonneg (h0 x))]
    exact ENNReal.toReal_ofReal (integral_nonneg fun x => klFun_nonneg (h0 x))
  rw [hent]
  constructor
  · rw [← integral_div]
    refine integral_mono (hv2.div_const _) hkint fun x => ?_
    have := klFun_lower hε0 hε1 (hb x)
    simpa using this
  · rw [← integral_div]
    refine integral_mono hkint (hv2.div_const _) fun x => ?_
    have := klFun_upper hε0 hε1 (hb x)
    simpa using this


theorem cf_convT {g v : Torus 1 → ℝ} (hg : Continuous g) (hev : ∀ x, g (-x) = g x)
    (hv : Integrable v (haar 1)) (k : Fin 1 → ℤ) :
    cf (convT g v) k = cf g k * cf v k := by
  have hF : Integrable (fun p : Torus 1 × Torus 1 =>
      mFourier (-k) p.1 * (((g (p.1 - p.2) * v p.2 : ℝ)) : ℂ)) ((haar 1).prod (haar 1)) := by
    have hV : Integrable (fun p : Torus 1 × Torus 1 => ((v p.2 : ℝ) : ℂ))
        ((haar 1).prod (haar 1)) := (hv.ofReal (𝕜 := ℂ)).comp_snd (haar 1)
    have hA : Continuous (fun p : Torus 1 × Torus 1 =>
        mFourier (-k) p.1 * ((g (p.1 - p.2) : ℝ) : ℂ)) :=
      ((mFourier (-k)).continuous.comp continuous_fst).mul
        (Complex.continuous_ofReal.comp (hg.comp (continuous_fst.sub continuous_snd)))
    obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus 1 × Torus 1)).exists_bound_of_continuousOn hA.continuousOn
    have := hV.bdd_mul (c := M) hA.aestronglyMeasurable
      (Eventually.of_forall fun p => hM p (Set.mem_univ _))
    refine this.congr (Eventually.of_forall fun p => ?_)
    push_cast; ring
  have e1 : cf (convT g v) k = ∫ x, ∫ y, mFourier (-k) x * (((g (x - y) * v y : ℝ)) : ℂ) := by
    simp only [cf, SharpLSI.mFourierCoeff_eq_integral, smul_eq_mul]
    congr 1; funext x
    rw [convT, ← integral_complex_ofReal, ← integral_const_mul]
  rw [e1, integral_integral_swap (f := fun x y => mFourier (-k) x * (((g (x - y) * v y : ℝ)) : ℂ)) hF]
  have e2 : ∀ y, ∫ x, mFourier (-k) x * (((g (x - y) * v y : ℝ)) : ℂ) =
      cf g k * (mFourier (-k) y * (v y : ℂ)) := by
    intro y
    have h := conv_mFourier g (-k) y
    rw [cf_even g hev] at h
    have : ∀ x : Torus 1, mFourier (-k) x * (((g (x - y) * v y : ℝ)) : ℂ) =
        (v y : ℂ) * ((g (y - x) : ℂ) * mFourier (-k) x) := by
      intro x
      have : g (x - y) = g (y - x) := by
        rw [← hev (x - y)]; congr 1; abel
      rw [this]; push_cast; ring
    simp_rw [this]
    rw [integral_const_mul, h]; ring
  simp_rw [e2]
  rw [integral_const_mul]
  congr 1
  simp only [cf, SharpLSI.mFourierCoeff_eq_integral, smul_eq_mul]


theorem memLp_v {ρ : Torus 1 → ℝ} {ε : ℝ} (h1 : ∫ x, ρ x ∂haar 1 = 1)
    (hb : ∀ x, |ρ x - 1| ≤ ε) : MemLp (fun x => ρ x - 1) 2 (haar 1) :=
  MemLp.of_bound ((integrable_of_integral_eq_one' h1).aestronglyMeasurable.sub
    aestronglyMeasurable_const) ε
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)

theorem cf_v_sub {ρ : Torus 1 → ℝ} (h1 : ∫ x, ρ x ∂haar 1 = 1) (k : Fin 1 → ℤ) :
    cf (fun x => ρ x - 1) k = cf ρ k - if k = 0 then 1 else 0 := by
  have := cf_sub (f := ρ) (g := fun _ => (1 : ℝ)) (integrable_of_integral_eq_one' h1)
    (integrable_const 1) k
  rw [this, cf_one]

theorem cf_v_zero {ρ : Torus 1 → ℝ} (h1 : ∫ x, ρ x ∂haar 1 = 1) :
    cf (fun x => ρ x - 1) 0 = 0 := by
  rw [cf_v_sub h1, cf_zero_eq, h1]; simp

theorem cf_v_eq {ρ : Torus 1 → ℝ} (h1 : ∫ x, ρ x ∂haar 1 = 1) {k : Fin 1 → ℤ} (hk : k ≠ 0) :
    cf (fun x => ρ x - 1) k = cf ρ k := by
  rw [cf_v_sub h1]; simp [hk]

theorem cf_C_zero {C : Torus 1 → ℝ} (hC : GoodKernel C) : cf C 0 = 0 := by
  rw [cf_zero_eq, hC.meanZero]; simp

theorem cf_convT_rho {C ρ : Torus 1 → ℝ} (hC : GoodKernel C) (h1 : ∫ x, ρ x ∂haar 1 = 1)
    (k : Fin 1 → ℤ) :
    cf (convT C ρ) k = (((cf C k).re : ℝ) : ℂ) * cf (fun x => ρ x - 1) k := by
  rw [cf_convT (continuous_of_smooth hC.smooth) hC.even (integrable_of_integral_eq_one' h1)]
  by_cases hk : k = 0
  · subst hk; rw [cf_C_zero hC]; simp
  · rw [cf_v_eq h1 hk, ← cf_real_eq C hC.even k]

/-- `‖2π i n z‖² = aCos n² ‖z‖²`. -/
theorem norm_sq_two_pi_I_mul (n : ℤ) (z : ℂ) :
    ‖2 * (π : ℂ) * Complex.I * (n : ℂ) * z‖ ^ 2 = aCos * (n : ℝ) ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  have : ‖2 * (π : ℂ) * Complex.I * (n : ℂ)‖ ^ 2 = aCos * (n : ℝ) ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul, mul_pow, mul_pow, mul_pow]
    simp [aCos]
    left; norm_num
  rw [this]


theorem convT_smooth {C ρ : Torus 1 → ℝ} (hC : GoodKernel C) (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) : IsSmoothT (convT C ρ) := by
  haveI := isProbabilityMeasure_densMeasure' h0 h1
  rw [convT_eq_conv h0 h1]; exact isSmoothT_conv hC.smooth _

theorem convT_dT_smooth {C ρ : Torus 1 → ℝ} (hC : GoodKernel C) (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) : IsSmoothT (convT (dT C) ρ) := by
  haveI := isProbabilityMeasure_densMeasure' h0 h1
  rw [convT_eq_conv h0 h1]; exact isSmoothT_conv (isSmoothT_dT hC.smooth) _

theorem dT_convT {C ρ : Torus 1 → ℝ} (hC : GoodKernel C) (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) : dT (convT C ρ) = convT (dT C) ρ := by
  haveI := isProbabilityMeasure_densMeasure' h0 h1
  funext x
  have hcv : convT C ρ = fun x => ∫ y, C (x - y) ∂densMeasure ρ := convT_eq_conv h0 h1
  rw [hcv, dT_conv hC.smooth, convT_eq_conv h0 h1]

theorem integrable_of_continuous_torus {f : Torus 1 → ℝ} (hf : Continuous f) :
    Integrable f (haar 1) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem memLp_of_continuous_torus {f : Torus 1 → ℝ} (hf : Continuous f) (p : ℝ≥0∞) :
    MemLp f p (haar 1) :=
  hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem cf_dT_smooth {u : Torus 1 → ℝ} (hu : IsSmoothT u) (k : Fin 1 → ℤ) :
    cf (dT u) k = 2 * (π : ℂ) * Complex.I * ((k 0 : ℤ) : ℂ) * cf u k := by
  have hw := isWeakGrad_weakGrad (hasWeakGrad_of_smooth hu)
  have hae := weakGrad_ae_dT hu
  have hint : Integrable u (haar 1) := integrable_of_continuous_torus (continuous_of_smooth hu)
  have hdint : Integrable (dT u) (haar 1) :=
    integrable_of_continuous_torus (continuous_of_smooth (isSmoothT_dT hu))
  have hg : ∀ j : Fin 1, Integrable (fun y => weakGrad u y j) (haar 1) := fun j => by
    rw [Subsingleton.elim j 0]; exact hdint.congr hae.symm
  have := mFourierCoeff_grad hw hint hg k 0
  have e : cf (dT u) k = cf (fun y => weakGrad u y 0) k := by
    simp only [cf, SharpLSI.mFourierCoeff_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    rw [hy]
  rw [e]
  exact this

theorem re_conj_mul (c : ℝ) (z : ℂ) : (conj z * ((c : ℂ) * z)).re = c * ‖z‖ ^ 2 := by
  have : conj z * ((c : ℂ) * z) = (c : ℂ) * (conj z * z) := by ring
  rw [this, Complex.conj_mul', Complex.re_ofReal_mul]
  norm_cast

theorem norm_sq_real_mul (c : ℝ) (z : ℂ) : ‖(c : ℂ) * z‖ ^ 2 = c ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- `G = 2 f f'`, `f = √ρ`. -/
noncomputable def Gfun (ρ : Torus 1 → ℝ) (x : Torus 1) : ℝ :=
  2 * Real.sqrt (ρ x) * weakGrad (fun y => Real.sqrt (ρ y)) x 0

theorem sqrt_le_two {ρ : Torus 1 → ℝ} {ε : ℝ} (hε : ε ≤ 1) (hb : ∀ x, |ρ x - 1| ≤ ε) (x : Torus 1) :
    Real.sqrt (ρ x) ≤ 2 := by
  have := (abs_le.mp (hb x)).2
  rw [Real.sqrt_le_iff]; constructor <;> nlinarith

theorem memLp_Gfun {ρ : Torus 1 → ℝ} {ε : ℝ} (h0 : ∀ x, 0 ≤ ρ x) (hε : ε ≤ 1)
    (hb : ∀ x, |ρ x - 1| ≤ ε) (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    MemLp (Gfun ρ) 2 (haar 1) := by
  have hg := memLp_weakGrad_zero hH
  have hgm := (isWeakGrad_weakGrad hH.1).aestronglyMeasurable_grad 0
  refine hg.of_le_mul (c := 4) ((hH.2.1.aestronglyMeasurable.const_mul 2).mul hgm)
    (Eventually.of_forall fun x => ?_)
  show ‖2 * Real.sqrt (ρ x) * weakGrad (fun y => Real.sqrt (ρ y)) x 0‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := sqrt_le_two hε hb x
  have h2 := Real.sqrt_nonneg (ρ x)
  nlinarith [abs_nonneg (weakGrad (fun y => Real.sqrt (ρ y)) x 0)]

theorem cf_Gfun {ρ : Torus 1 → ℝ} {ε : ℝ} (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar 1 = 1)
    (hε : ε ≤ 1) (hb : ∀ x, |ρ x - 1| ≤ ε) (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x)))
    (k : Fin 1 → ℤ) :
    cf (Gfun ρ) k = 2 * (π : ℂ) * Complex.I * ((k 0 : ℤ) : ℂ) * cf (fun x => ρ x - 1) k := by
  have hw := isWeakGrad_weakGrad hH.1
  have hg2 : MemLp (fun x => weakGrad (fun y => Real.sqrt (ρ y)) x 0) 2 (haar 1) :=
    memLp_weakGrad_zero hH
  have hg2' : ∀ j : Fin 1, MemLp (fun x => weakGrad (fun y => Real.sqrt (ρ y)) x j) 2 (haar 1) :=
    fun j => by rw [Subsingleton.elim j 0]; exact hg2
  have hsq := isWeakGrad_sq hw hH.2.1 hg2'
  have hGi : Integrable (Gfun ρ) (haar 1) := (memLp_Gfun h0 hε hb hH).integrable one_le_two
  have hρi : Integrable (fun y => Real.sqrt (ρ y) ^ 2) (haar 1) := hH.2.1.integrable_sq
  have := mFourierCoeff_grad hsq hρi (fun j => by rw [Subsingleton.elim j 0]; exact hGi) k 0
  have e : ∀ y, ((Real.sqrt (ρ y) ^ 2 : ℝ) : ℂ) = (ρ y : ℂ) := fun y => by
    rw [Real.sq_sqrt (h0 y)]
  simp only [e] at this
  show mFourierCoeff (fun y => ((Gfun ρ y : ℝ) : ℂ)) k = _
  rw [show (fun y => ((Gfun ρ y : ℝ) : ℂ)) = fun y => (((2 * Real.sqrt (ρ y) * weakGrad (fun y => Real.sqrt (ρ y)) y 0 : ℝ)) : ℂ) from rfl, this]
  by_cases hk : k = 0
  · subst hk; simp
  · rw [cf_v_eq h1 hk]

theorem hasSum_Gfun {ρ : Torus 1 → ℝ} {ε : ℝ} (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar 1 = 1)
    (hε : ε ≤ 1) (hb : ∀ x, |ρ x - 1| ≤ ε) (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    HasSum (fun k : Fin 1 → ℤ => aCos * ((k 0 : ℤ) : ℝ) ^ 2 * ‖cf (fun x => ρ x - 1) k‖ ^ 2)
      (∫ x, Gfun ρ x ^ 2 ∂haar 1) := by
  have := hasSum_sq_mFourierCoeff_real (memLp_Gfun h0 hε hb hH)
  convert this using 1
  funext k
  show _ = ‖cf (Gfun ρ) k‖ ^ 2
  rw [cf_Gfun h0 h1 hε hb hH, norm_sq_two_pi_I_mul]

theorem hasSum_v {ρ : Torus 1 → ℝ} {ε : ℝ} (h1 : ∫ x, ρ x ∂haar 1 = 1) (hb : ∀ x, |ρ x - 1| ≤ ε) :
    HasSum (fun k : Fin 1 → ℤ => ‖cf (fun x => ρ x - 1) k‖ ^ 2) (∫ x, (ρ x - 1) ^ 2 ∂haar 1) :=
  hasSum_sq_mFourierCoeff_real (memLp_v h1 hb)

theorem cf_bfun {C ρ : Torus 1 → ℝ} (hC : GoodKernel C) (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) (k : Fin 1 → ℤ) :
    cf (convT (dT C) ρ) k = 2 * (π : ℂ) * Complex.I * ((k 0 : ℤ) : ℂ) *
      ((((cf C k).re : ℝ) : ℂ) * cf (fun x => ρ x - 1) k) := by
  rw [← dT_convT hC h0 h1, cf_dT_smooth (convT_smooth hC h0 h1), cf_convT_rho hC h1]

theorem hasSum_bfun {C ρ : Torus 1 → ℝ} (hC : GoodKernel C) (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) :
    HasSum (fun k : Fin 1 → ℤ => aCos * ((k 0 : ℤ) : ℝ) ^ 2 * (cf C k).re ^ 2 *
        ‖cf (fun x => ρ x - 1) k‖ ^ 2) (∫ x, convT (dT C) ρ x ^ 2 ∂haar 1) := by
  have hbc : Continuous (convT (dT C) ρ) := continuous_of_smooth (convT_dT_smooth hC h0 h1)
  have := hasSum_sq_mFourierCoeff_real (memLp_of_continuous_torus hbc 2)
  convert this using 1
  funext k
  show _ = ‖cf (convT (dT C) ρ) k‖ ^ 2
  rw [cf_bfun hC h0 h1, norm_sq_two_pi_I_mul, norm_sq_real_mul]; ring

theorem hasSum_hfun {C ρ : Torus 1 → ℝ} {ε : ℝ} (hC : GoodKernel C) (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) (hε : ε ≤ 1)
    (hb : ∀ x, |ρ x - 1| ≤ ε) (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    HasSum (fun k : Fin 1 → ℤ => aCos * ((k 0 : ℤ) : ℝ) ^ 2 * (1 - (cf C k).re) ^ 2 *
        ‖cf (fun x => ρ x - 1) k‖ ^ 2)
      (∫ x, (Gfun ρ x - convT (dT C) ρ x) ^ 2 ∂haar 1) := by
  have hbc : Continuous (convT (dT C) ρ) := continuous_of_smooth (convT_dT_smooth hC h0 h1)
  have hGi : Integrable (Gfun ρ) (haar 1) := (memLp_Gfun h0 hε hb hH).integrable one_le_two
  have hbi : Integrable (convT (dT C) ρ) (haar 1) := integrable_of_continuous_torus hbc
  have hL2 : MemLp (fun x => Gfun ρ x - convT (dT C) ρ x) 2 (haar 1) :=
    (memLp_Gfun h0 hε hb hH).sub (memLp_of_continuous_torus hbc 2)
  have := hasSum_sq_mFourierCoeff_real hL2
  convert this using 1
  funext k
  show _ = ‖cf (fun x => Gfun ρ x - convT (dT C) ρ x) k‖ ^ 2
  rw [cf_sub hGi hbi, cf_Gfun h0 h1 hε hb hH, cf_bfun hC h0 h1]
  have : 2 * (π : ℂ) * Complex.I * ((k 0 : ℤ) : ℂ) * cf (fun x => ρ x - 1) k -
      2 * (π : ℂ) * Complex.I * ((k 0 : ℤ) : ℂ) * ((((cf C k).re : ℝ) : ℂ) * cf (fun x => ρ x - 1) k) =
      2 * (π : ℂ) * Complex.I * ((k 0 : ℤ) : ℂ) * ((((1 - (cf C k).re : ℝ)) : ℂ) * cf (fun x => ρ x - 1) k) := by
    push_cast; ring
  rw [this, norm_sq_two_pi_I_mul, norm_sq_real_mul]; ring

theorem integral_convT_eq_zero {C ρ : Torus 1 → ℝ} (hC : GoodKernel C) (h1 : ∫ x, ρ x ∂haar 1 = 1) :
    ∫ x, convT C ρ x ∂haar 1 = 0 := by
  have h := cf_convT_rho hC h1 0
  rw [cf_zero_eq, cf_v_zero h1, mul_zero] at h
  exact_mod_cast h

theorem hasSum_cq {C ρ : Torus 1 → ℝ} {ε : ℝ} (hC : GoodKernel C) (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) (hb : ∀ x, |ρ x - 1| ≤ ε) :
    HasSum (fun k : Fin 1 → ℤ => (cf C k).re * ‖cf (fun x => ρ x - 1) k‖ ^ 2) (cqR C ρ) := by
  have hv2 := memLp_v h1 hb
  have huc : Continuous (convT C ρ) := continuous_of_smooth (convT_smooth hC h0 h1)
  have hu2 : MemLp (convT C ρ) 2 (haar 1) := memLp_of_continuous_torus huc 2
  have hP := hasSum_prod_cf_real hv2 hu2
  have hre := Complex.hasSum_re hP
  have e : (fun k : Fin 1 → ℤ => (conj (cf (fun x => ρ x - 1) k) * cf (convT C ρ) k).re) =
      fun k => (cf C k).re * ‖cf (fun x => ρ x - 1) k‖ ^ 2 := by
    funext k
    rw [cf_convT_rho hC h1, re_conj_mul]
  simp only [e, Complex.ofReal_re] at hre
  have hq : cqR C ρ = ∫ y, (ρ y - 1) * convT C ρ y := by
    unfold cqR
    have : ∀ y, ρ y * convT C ρ y = convT C ρ y + (ρ y - 1) * convT C ρ y := fun y => by ring
    simp_rw [this]
    have hvu : Integrable (fun y => (ρ y - 1) * convT C ρ y) (haar 1) := hv2.integrable_mul hu2
    rw [integral_add (integrable_of_continuous_torus huc) hvu,
      integral_convT_eq_zero hC h1, zero_add]
  rw [hq]
  exact hre

theorem chat_neg {C : Torus 1 → ℝ} (hC : GoodKernel C) (n : ℤ) : chat C (-n) = chat C n := by
  rw [chat_eq, chat_eq, ← K1_neg, cf_even C hC.even]

theorem re_cf_eq_chat (C : Torus 1 → ℝ) (k : Fin 1 → ℤ) : (cf C k).re = chat C (k 0) := by
  rw [chat_eq, ← eq_K1 k]

theorem LamF_le {C : Torus 1 → ℝ} (hC : GoodKernel C) {δ : ℝ} (hδ : 0 < δ)
    (hsup : ∀ n : ℤ, n ≠ 0 → chat C n ≤ 1 - δ) {k : Fin 1 → ℤ} (hk : k ≠ 0) :
    LamF C ≤ aCos * ((k 0 : ℤ) : ℝ) ^ 2 * (1 - (cf C k).re) := by
  have hk0 : k 0 ≠ 0 := fun h => hk (by rw [eq_K1 k, h]; rfl)
  have hn : 1 ≤ (k 0).natAbs := Int.natAbs_pos.mpr hk0
  set n := (k 0).natAbs with hn_def
  have hchat : chat C (k 0) = chat C (n : ℤ) := by
    rcases Int.natAbs_eq (k 0) with h | h
    · rw [← h]
    · rw [h, chat_neg hC]
  have hterm : ∀ m : ℕ, 0 ≤ aCos * ((m : ℝ) + 1) ^ 2 * (1 - chat C ((m : ℤ) + 1)) := by
    intro m
    have h1 := hsup ((m : ℤ) + 1) (by omega)
    have : 0 ≤ aCos := by unfold aCos; positivity
    have h2 : 0 ≤ 1 - chat C ((m : ℤ) + 1) := by linarith
    positivity
  have hbdd : BddBelow (Set.range fun m : ℕ => aCos * ((m : ℝ) + 1) ^ 2 * (1 - chat C ((m : ℤ) + 1))) :=
    ⟨0, by rintro _ ⟨m, rfl⟩; exact hterm m⟩
  have key := ciInf_le hbdd (n - 1)
  unfold LamF
  refine key.trans (le_of_eq ?_)
  have e1 : (((n - 1 : ℕ) : ℤ) + 1) = (n : ℤ) := by omega
  have e2 : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by
    rw [Nat.cast_sub hn]; push_cast; ring
  show aCos * (((n - 1 : ℕ) : ℝ) + 1) ^ 2 * (1 - chat C (((n - 1 : ℕ) : ℤ) + 1)) = _
  rw [e1, e2, re_cf_eq_chat, hchat]
  congr 2
  have := natAbs_sq_real (k 0)
  rw [← hn_def] at this
  exact this

/-- Real-number consequences of the Parseval sums. -/
theorem num_sums {K : Type*} {a c l : K → ℝ} {V Q T B P L δ ε : ℝ} (z : K) (hδ : 0 < δ)
    (hε : ε ≤ δ) (hε0 : 0 ≤ ε)
    (ha0 : ∀ k, 0 ≤ a k) (haz : a z = 0) (hl0 : ∀ k, 0 ≤ l k) (hlz : l z = 0)
    (hc : ∀ k, k ≠ z → 0 ≤ c k ∧ c k ≤ 1 - δ) (hLam : ∀ k, k ≠ z → L ≤ l k * (1 - c k))
    (hV : HasSum a V) (hQ : HasSum (fun k => c k * a k) Q) (hT : HasSum (fun k => l k * a k) T)
    (hB : HasSum (fun k => l k * c k ^ 2 * a k) B)
    (hP : HasSum (fun k => l k * (1 - c k) ^ 2 * a k) P) :
    δ * V ≤ V - Q ∧ L * (V - Q) ≤ P ∧ δ ^ 2 * T ≤ P ∧ B ≤ T ∧ Q ≤ V / (1 + ε) := by
  have hVQ : HasSum (fun k => a k - c k * a k) (V - Q) := hV.sub hQ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine hasSum_le (fun k => ?_) (hV.mul_left δ) hVQ
    by_cases hk : k = z
    · subst hk; simp [haz]
    · obtain ⟨_, h2⟩ := hc k hk
      have := ha0 k
      nlinarith
  · refine hasSum_le (fun k => ?_) (hVQ.mul_left L) hP
    by_cases hk : k = z
    · subst hk; simp [haz]
    · obtain ⟨h1, h2⟩ := hc k hk
      have := ha0 k
      have h3 := hLam k hk
      have h4 : 0 ≤ (1 - c k) * a k := mul_nonneg (by linarith) this
      nlinarith [mul_le_mul_of_nonneg_right h3 h4]
  · refine hasSum_le (fun k => ?_) (hT.mul_left (δ ^ 2)) hP
    by_cases hk : k = z
    · subst hk; simp [haz]
    · obtain ⟨h1, h2⟩ := hc k hk
      have := ha0 k
      have := hl0 k
      have h3 : δ ^ 2 ≤ (1 - c k) ^ 2 := pow_le_pow_left₀ hδ.le (by linarith) 2
      have h4 : 0 ≤ l k * a k := mul_nonneg (hl0 k) (ha0 k)
      nlinarith [mul_le_mul_of_nonneg_right h3 h4]
  · refine hasSum_le (fun k => ?_) hB hT
    by_cases hk : k = z
    · subst hk; simp [haz]
    · obtain ⟨h1, h2⟩ := hc k hk
      have h4 : 0 ≤ l k * a k := mul_nonneg (hl0 k) (ha0 k)
      have h3 : c k ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h3 h4]
  · refine hasSum_le (fun k => ?_) hQ (hV.div_const (1 + ε))
    by_cases hk : k = z
    · subst hk; simp [haz]
    · obtain ⟨h1, h2⟩ := hc k hk
      have := ha0 k
      rw [le_div_iff₀ (by positivity)]
      have h3 : c k * (1 + ε) ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h3 this]

theorem integral_sq_comb {a b : Torus 1 → ℝ} (ha : MemLp a 2 (haar 1)) (hb : MemLp b 2 (haar 1))
    (s : ℝ) :
    ∫ x, (s * a x + b x) ^ 2 ∂haar 1 = s ^ 2 * ∫ x, a x ^ 2 ∂haar 1 +
      2 * s * ∫ x, a x * b x ∂haar 1 + ∫ x, b x ^ 2 ∂haar 1 := by
  have h1 : Integrable (fun x => a x ^ 2) (haar 1) := ha.integrable_sq
  have h2 : Integrable (fun x => b x ^ 2) (haar 1) := hb.integrable_sq
  have h3 : Integrable (fun x => a x * b x) (haar 1) := ha.integrable_mul hb
  have e : (fun x => (s * a x + b x) ^ 2) =
      fun x => (s ^ 2 * a x ^ 2 + 2 * s * (a x * b x)) + b x ^ 2 := by
    funext x; ring
  have i1 : Integrable (fun x => s ^ 2 * a x ^ 2) (haar 1) := h1.const_mul _
  have i3 : Integrable (fun x => 2 * s * (a x * b x)) (haar 1) := h3.const_mul _
  have i13 : Integrable (fun x => s ^ 2 * a x ^ 2 + 2 * s * (a x * b x)) (haar 1) := i1.add i3
  rw [e, integral_add i13 h2, integral_add i1 i3, integral_const_mul, integral_const_mul]

theorem l2_triangle {a b : Torus 1 → ℝ} (ha : MemLp a 2 (haar 1)) (hb : MemLp b 2 (haar 1)) :
    Real.sqrt (∫ x, (a x + b x) ^ 2 ∂haar 1) ≤
      Real.sqrt (∫ x, a x ^ 2 ∂haar 1) + Real.sqrt (∫ x, b x ^ 2 ∂haar 1) := by
  set A := ∫ x, a x ^ 2 ∂haar 1 with hA_def
  set B := ∫ x, b x ^ 2 ∂haar 1 with hB_def
  set X := ∫ x, a x * b x ∂haar 1 with hX_def
  have hA : 0 ≤ A := integral_nonneg fun x => sq_nonneg _
  have hB : 0 ≤ B := integral_nonneg fun x => sq_nonneg _
  have hq : ∀ s : ℝ, 0 ≤ A * (s * s) + 2 * X * s + B := fun s => by
    have := integral_nonneg (μ := haar 1) (f := fun x => (s * a x + b x) ^ 2) (fun x => sq_nonneg _)
    rw [integral_sq_comb ha hb s] at this
    nlinarith
  have hd := discrim_le_zero hq
  have hX2 : X ^ 2 ≤ A * B := by unfold discrim at hd; nlinarith
  have hXle : X ≤ Real.sqrt A * Real.sqrt B := by
    rw [← Real.sqrt_mul hA]; exact (le_abs_self X).trans (Real.abs_le_sqrt hX2)
  have e := integral_sq_comb ha hb 1
  simp only [one_mul, one_pow] at e
  rw [e, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt hA
  have h2 := Real.sq_sqrt hB
  nlinarith

theorem DR_lower {C ρ : Torus 1 → ℝ} {ε δ : ℝ} (hC : GoodKernel C) (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x)))
    (hb : ∀ x, |ρ x - 1| ≤ ε) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hεδ : ε ≤ δ)
    (hBP : δ ^ 2 * ∫ x, convT (dT C) ρ x ^ 2 ∂haar 1 ≤
      ∫ x, (Gfun ρ x - convT (dT C) ρ x) ^ 2 ∂haar 1) :
    (∫ x, (Gfun ρ x - convT (dT C) ρ x) ^ 2 ∂haar 1) * ((1 - ε / δ) ^ 2 / (1 + ε)) ≤ DR C ρ := by
  set bf : Torus 1 → ℝ := convT (dT C) ρ with hbf
  have hbc : Continuous bf := continuous_of_smooth (convT_dT_smooth hC h0 h1)
  have hb2 : MemLp bf 2 (haar 1) := memLp_of_continuous_torus hbc 2
  have hG2 := memLp_Gfun h0 hε1 hb hH
  have hh2 : MemLp (fun x => Gfun ρ x - bf x) 2 (haar 1) := hG2.sub hb2
  -- v * b
  have hvb2 : MemLp (fun x => (ρ x - 1) * bf x) 2 (haar 1) := by
    refine hb2.of_le_mul (c := ε) ?_ (Eventually.of_forall fun x => ?_)
    · exact ((integrable_of_integral_eq_one' h1).aestronglyMeasurable.sub
        aestronglyMeasurable_const).mul hb2.aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs (ρ x - 1)]
      exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
  set w : Torus 1 → ℝ := fun x =>
    2 * weakGrad (fun y => Real.sqrt (ρ y)) x 0 - Real.sqrt (ρ x) * bf x with hw
  set A : Torus 1 → ℝ := fun x => Real.sqrt (ρ x) * w x with hA
  have hid : ∀ x, Gfun ρ x - bf x = A x + (ρ x - 1) * bf x := by
    intro x
    have := Real.sq_sqrt (h0 x)
    simp only [Gfun, hA, hw]
    linear_combination (bf x) * this
  have hA2 : MemLp A 2 (haar 1) := by
    have := hh2.sub hvb2
    refine this.ae_eq (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    rw [hid x]; ring
  have hDRint := integrable_DR_integrand hC h0 h1 hH
  have hDR : DR C ρ = ∫ x, w x ^ 2 ∂haar 1 := rfl
  -- ∫ A² ≤ (1+ε) DR
  have hAle : ∫ x, A x ^ 2 ∂haar 1 ≤ (1 + ε) * DR C ρ := by
    rw [hDR, ← integral_const_mul]
    refine integral_mono hA2.integrable_sq (hDRint.const_mul _) fun x => ?_
    have hs := Real.sq_sqrt (h0 x)
    have hρ := (abs_le.mp (hb x)).2
    show (Real.sqrt (ρ x) * w x) ^ 2 ≤ (1 + ε) * w x ^ 2
    rw [mul_pow, hs]
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  -- ∫ (v b)² ≤ ε² ∫ b²
  have hW : ∫ x, ((ρ x - 1) * bf x) ^ 2 ∂haar 1 ≤ ε ^ 2 * ∫ x, bf x ^ 2 ∂haar 1 := by
    rw [← integral_const_mul]
    refine integral_mono hvb2.integrable_sq (hb2.integrable_sq.const_mul _) fun x => ?_
    show ((ρ x - 1) * bf x) ^ 2 ≤ ε ^ 2 * bf x ^ 2
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have := pow_le_pow_left₀ (abs_nonneg _) (hb x) 2
    rwa [sq_abs] at this
  -- triangle
  have htri := l2_triangle hA2 hvb2
  have ehP : ∫ x, (Gfun ρ x - bf x) ^ 2 ∂haar 1 = ∫ x, (A x + (ρ x - 1) * bf x) ^ 2 ∂haar 1 := by
    congr 1; funext x; rw [hid x]
  set P := ∫ x, (Gfun ρ x - bf x) ^ 2 ∂haar 1 with hP
  set Bq := ∫ x, bf x ^ 2 ∂haar 1 with hBq
  set A2 := ∫ x, A x ^ 2 ∂haar 1 with hA2d
  set W := ∫ x, ((ρ x - 1) * bf x) ^ 2 ∂haar 1 with hWd
  rw [← ehP] at htri
  have hP0 : 0 ≤ P := integral_nonneg fun x => sq_nonneg _
  have hB0 : 0 ≤ Bq := integral_nonneg fun x => sq_nonneg _
  have hW0 : 0 ≤ W := integral_nonneg fun x => sq_nonneg _
  have hA20 : 0 ≤ A2 := integral_nonneg fun x => sq_nonneg _
  have hsW : Real.sqrt W ≤ ε * Real.sqrt Bq := by
    calc Real.sqrt W ≤ Real.sqrt (ε ^ 2 * Bq) := Real.sqrt_le_sqrt hW
      _ = ε * Real.sqrt Bq := by
        rw [Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε0]
  have hsB : δ * Real.sqrt Bq ≤ Real.sqrt P := by
    have : δ * Real.sqrt Bq = Real.sqrt (δ ^ 2 * Bq) := by
      rw [Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ.le]
    rw [this]; exact Real.sqrt_le_sqrt hBP
  -- combine
  have hkey : Real.sqrt P * (1 - ε / δ) ≤ Real.sqrt A2 := by
    have h2 : ε * Real.sqrt Bq ≤ ε * (Real.sqrt P / δ) := by
      refine mul_le_mul_of_nonneg_left ?_ hε0
      rw [le_div_iff₀ hδ]; linarith
    have h3 : ε * (Real.sqrt P / δ) = Real.sqrt P * (ε / δ) := by ring
    nlinarith
  have hfac : 0 ≤ 1 - ε / δ := by
    rw [sub_nonneg, div_le_one hδ]; exact hεδ
  have hsq : (Real.sqrt P * (1 - ε / δ)) ^ 2 ≤ A2 := by
    calc (Real.sqrt P * (1 - ε / δ)) ^ 2 ≤ (Real.sqrt A2) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) hfac) hkey 2
      _ = A2 := Real.sq_sqrt hA20
  rw [mul_pow, Real.sq_sqrt hP0] at hsq
  rw [mul_div_assoc', div_le_iff₀ (by linarith)]
  nlinarith

theorem near_key {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hCpos : ∀ n : ℤ, n ≠ 0 → 0 ≤ chat C n) {δ : ℝ} (hδ : 0 < δ)
    (hsup : ∀ n : ℤ, n ≠ 0 → chat C n ≤ 1 - δ) {ε : ℝ} (hε0 : 0 < ε) (hεδ : ε ≤ δ / 2)
    (hε2 : ε ≤ 1 / 2) {ρ : Torus 1 → ℝ} (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar 1 = 1)
    (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) (hb : ∀ x, |ρ x - 1| ≤ ε) :
    ∃ S : ℝ, 0 ≤ S ∧ 0 ≤ 2 * GR C ρ ∧ 2 * GR C ρ ≤ (1 + ε / ((1 - ε) * δ)) * S ∧
      LamF C * ((1 - ε / δ) ^ 2 / (1 + ε)) * S ≤ DR C ρ := by
  have hε1 : ε < 1 := by linarith
  have hεδ' : ε ≤ δ := by linarith
  have hρm : AEStronglyMeasurable ρ (haar 1) :=
    (integrable_of_integral_eq_one' h1).aestronglyMeasurable
  obtain ⟨hlo, hup⟩ := entR_bounds hε0.le hε1 hρm h0 h1 hb
  have hV := hasSum_v h1 hb
  have hQ := hasSum_cq hC h0 h1 hb
  have hT := hasSum_Gfun h0 h1 (by linarith) hb hH
  have hBs := hasSum_bfun hC h0 h1
  have hPs := hasSum_hfun hC h0 h1 (by linarith) hb hH
  have hAC : 0 ≤ aCos := by unfold aCos; positivity
  have hnum := num_sums (K := Fin 1 → ℤ) (a := fun k => ‖cf (fun x => ρ x - 1) k‖ ^ 2)
    (c := fun k => (cf C k).re) (l := fun k => aCos * ((k 0 : ℤ) : ℝ) ^ 2) (z := 0)
    (L := LamF C) (δ := δ) (ε := ε) hδ hεδ' hε0.le (fun k => sq_nonneg _)
    (by show ‖cf (fun x => ρ x - 1) 0‖ ^ 2 = 0; rw [cf_v_zero h1]; simp)
    (fun k => by positivity) (by simp)
    (fun k hk => by
      have hk0 : k 0 ≠ 0 := fun h => hk (by rw [eq_K1 k, h]; rfl)
      show 0 ≤ (cf C k).re ∧ (cf C k).re ≤ 1 - δ
      rw [re_cf_eq_chat]; exact ⟨hCpos _ hk0, hsup _ hk0⟩)
    (fun k hk => LamF_le hC hδ hsup hk) hV hQ hT hBs hPs
  obtain ⟨n1, n2, n3, n4, n5⟩ := hnum
  have hV0 : 0 ≤ ∫ x, (ρ x - 1) ^ 2 ∂haar 1 := integral_nonneg fun x => sq_nonneg _
  have hGR : 2 * GR C ρ = 2 * entR ρ - cqR C ρ := by unfold GR; ring
  set V := ∫ x, (ρ x - 1) ^ 2 ∂haar 1 with hVd
  set Q := cqR C ρ with hQd
  have hpos1 : 0 < 1 - ε := by linarith
  have hpos2 : 0 < 1 + ε := by linarith
  have hS0 : 0 ≤ V - Q := by nlinarith
  refine ⟨V - Q, hS0, ?_, ?_, ?_⟩
  · rw [hGR]
    have : V / (1 + ε) = 2 * (V / (2 * (1 + ε))) := by field_simp
    linarith
  · rw [hGR]
    have hVS : V ≤ (V - Q) / δ := by rw [le_div_iff₀ hδ]; linarith
    have e : (1 + ε / ((1 - ε) * δ)) * (V - Q) - (V / (1 - ε) - Q) =
        ε / (1 - ε) * ((V - Q) / δ - V) := by
      field_simp; ring
    have e2 : 2 * entR ρ ≤ V / (1 - ε) := by
      have : V / (1 - ε) = 2 * (V / (2 * (1 - ε))) := by field_simp
      linarith
    have : 0 ≤ ε / (1 - ε) * ((V - Q) / δ - V) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  · have hBP : δ ^ 2 * ∫ x, convT (dT C) ρ x ^ 2 ∂haar 1 ≤
        ∫ x, (Gfun ρ x - convT (dT C) ρ x) ^ 2 ∂haar 1 :=
      le_trans (mul_le_mul_of_nonneg_left n4 (sq_nonneg δ)) n3
    have hDL := DR_lower hC h0 h1 hH hb hε0.le (by linarith) hδ hεδ' hBP
    have hκ : 0 ≤ (1 - ε / δ) ^ 2 / (1 + ε) := by positivity
    calc LamF C * ((1 - ε / δ) ^ 2 / (1 + ε)) * (V - Q)
        = ((1 - ε / δ) ^ 2 / (1 + ε)) * (LamF C * (V - Q)) := by ring
      _ ≤ ((1 - ε / δ) ^ 2 / (1 + ε)) * ∫ x, (Gfun ρ x - convT (dT C) ρ x) ^ 2 ∂haar 1 :=
          mul_le_mul_of_nonneg_left n2 hκ
      _ ≤ DR C ρ := by linarith


/-- For densities uniformly close to `1`, `D(ρ) ≥ (Λ_F - η) · 2 G(ρ)`. -/
theorem near_uniform {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hCpos : ∀ n : ℤ, n ≠ 0 → 0 ≤ chat C n)
    (hsup : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℤ, n ≠ 0 → chat C n ≤ 1 - δ) :
    ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∀ ρ : Torus 1 → ℝ, (∀ x, 0 ≤ ρ x) →
      ∫ x, ρ x ∂haar 1 = 1 → MemH1 (haar 1) (fun x => Real.sqrt (ρ x)) →
      (∀ x, |ρ x - 1| ≤ ε) → (LamF C - η) * (2 * GR C ρ) ≤ DR C ρ := by
  intro η hη
  obtain ⟨δ, hδ, hsup'⟩ := hsup
  set L := LamF C with hL
  set ψ : ℝ → ℝ := fun e => (1 - e / δ) ^ 2 / (1 + e) * L - (L - η) * (1 + e / ((1 - e) * δ)) with hψ
  have hcont : ContinuousAt ψ 0 := by
    simp only [hψ]
    have hd1 : (1 + (0 : ℝ)) ≠ 0 := by norm_num
    have hd2 : ((1 - (0 : ℝ)) * δ) ≠ 0 := by simpa using hδ.ne'
    refine ContinuousAt.sub (ContinuousAt.mul (ContinuousAt.div (by fun_prop) (by fun_prop) hd1)
      continuousAt_const) (ContinuousAt.mul continuousAt_const
      (ContinuousAt.add continuousAt_const (ContinuousAt.div (by fun_prop) (by fun_prop) hd2)))
  have hψ0 : ψ 0 = η := by simp [hψ]
  have hev : ∀ᶠ e in 𝓝 (0 : ℝ), 0 < ψ e := hcont.eventually (lt_mem_nhds (by rw [hψ0]; exact hη))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set ε := min (min (r / 2) (δ / 2)) (1 / 2) with hεdef
  have hεpos : 0 < ε := by
    simp only [hεdef]; exact lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
  have hε_r : ε ≤ r / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hε_δ : ε ≤ δ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hε_2 : ε ≤ 1 / 2 := min_le_right _ _
  have hψε : 0 < ψ ε := by
    refine hball ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos hεpos]; linarith
  refine ⟨ε, hεpos, fun ρ h0 h1 hH hb => ?_⟩
  obtain ⟨S, hS0, hG0, hG1, hD⟩ := near_key hC hCpos hδ hsup' hεpos hε_δ hε_2 h0 h1 hH hb
  have hDR0 : 0 ≤ DR C ρ := by unfold DR; exact integral_nonneg fun x => sq_nonneg _
  by_cases hLη : L - η ≤ 0
  · nlinarith
  · have hLη := not_le.mp hLη
    have hψε' : (L - η) * (1 + ε / ((1 - ε) * δ)) < (1 - ε / δ) ^ 2 / (1 + ε) * L := by
      simp only [hψ] at hψε; linarith
    calc (L - η) * (2 * GR C ρ) ≤ (L - η) * ((1 + ε / ((1 - ε) * δ)) * S) :=
          mul_le_mul_of_nonneg_left hG1 hLη.le
      _ = ((L - η) * (1 + ε / ((1 - ε) * δ))) * S := by ring
      _ ≤ ((1 - ε / δ) ^ 2 / (1 + ε) * L) * S := mul_le_mul_of_nonneg_right hψε'.le hS0
      _ = L * ((1 - ε / δ) ^ 2 / (1 + ε)) * S := by ring
      _ ≤ DR C ρ := hD

end SharpLSI.FL.Ex.LaneD
