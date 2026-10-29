import DGPS.Lipschitz.DuhamelPotential
open MeasureTheory Set
open scoped Real RealInnerProductSpace
namespace DGPS.Lipschitz
variable {d : ℕ}

/-! # LIP007d (partial): Fourier-mode Duhamel identities

Sub-lemmas towards `lip007d_duhamel_eq_semigroup`: the Fourier coefficients of the Duhamel
potential `u(t) = H_t f + ∫₀ᵗ H_{t-s}(b · v(s)) ds` satisfy, for every mode `k`, the integral ODE
`û(t,k) - f̂(k) = -w_k ∫₀ᵗ û(s,k) ds + ∫₀ᵗ ĝ_s(k) ds`.
-/

theorem mul_integral_exp_shift (w s t : ℝ) (hst : s ≤ t) :
    w * ∫ τ in Ioo s t, Real.exp (-(w * (τ - s))) = 1 - Real.exp (-(w * (t - s))) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hst,
    ← intervalIntegral.integral_const_mul]
  have hd : ∀ x ∈ uIcc s t, HasDerivAt (fun τ : ℝ => 1 - Real.exp (-(w * (τ - s))))
      (w * Real.exp (-(w * (x - s)))) x := by
    intro x _
    have h1 : HasDerivAt (fun τ : ℝ => -(w * (τ - s))) (-(w * 1)) x :=
      (((hasDerivAt_id x).sub_const s).const_mul w).neg
    have h2 := (h1.exp).const_sub 1
    convert h2 using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)

theorem mode_integral_ode {w t : ℝ} (ht : 0 < t) (a : ℂ) {g : ℝ → ℂ} (hgm : Measurable g)
    {M : ℝ} (hM : ∀ s, ‖g s‖ ≤ M) {U : ℝ → ℂ}
    (hU : ∀ τ, 0 < τ → τ ≤ t → U τ = (Real.exp (-(w * τ)) : ℂ) * a +
      ∫ s in Ioo 0 τ, (Real.exp (-(w * (τ - s))) : ℂ) * g s) :
    U t - a = -(w : ℂ) * (∫ τ in Ioo 0 t, U τ) + ∫ s in Ioo 0 t, g s := by
  set μ : Measure ℝ := volume.restrict (Ioo 0 t) with hμ
  have : IsFiniteMeasure μ := ⟨by simp [hμ]⟩
  let F : ℝ × ℝ → ℂ := fun p =>
    if 0 < p.1 - p.2 ∧ p.1 - p.2 < t then (Real.exp (-(w * (p.1 - p.2))) : ℂ) * g p.2 else 0
  have hFm : Measurable F := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact (measurableSet_lt measurable_const (measurable_fst.sub measurable_snd)).inter
        (measurableSet_lt (measurable_fst.sub measurable_snd) measurable_const)
    · exact (Complex.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_const.mul (measurable_fst.sub measurable_snd)).neg)).mul
        (hgm.comp measurable_snd)
  have hFb : ∀ p, ‖F p‖ ≤ Real.exp (|w| * t) * M := by
    intro p
    by_cases hp : 0 < p.1 - p.2 ∧ p.1 - p.2 < t
    · simp only [F, hp, and_self, ite_true]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul ?_ (hM _) (norm_nonneg _) (Real.exp_pos _).le
      refine Real.exp_le_exp.mpr ?_
      have : -(w * (p.1 - p.2)) ≤ |w| * (p.1 - p.2) := by
        calc -(w * (p.1 - p.2)) ≤ |w * (p.1 - p.2)| := neg_le_abs _
          _ = |w| * (p.1 - p.2) := by rw [abs_mul, abs_of_pos hp.1]
      exact this.trans (mul_le_mul_of_nonneg_left hp.2.le (abs_nonneg _))
    · simp only [F, hp, ite_false, norm_zero]
      exact mul_nonneg (Real.exp_pos _).le ((norm_nonneg _).trans (hM 0))
  have hFi : Integrable F (μ.prod μ) :=
    Integrable.of_bound hFm.aestronglyMeasurable _ (Filter.Eventually.of_forall hFb)
  have hswap := integral_integral_swap (f := fun τ s => F (τ, s)) hFi
  -- inner integrals
  have hin1 : ∀ τ ∈ Ioo 0 t, ∫ s, F (τ, s) ∂μ =
      ∫ s in Ioo 0 τ, (Real.exp (-(w * (τ - s))) : ℂ) * g s := by
    intro τ hτ
    have : ∫ s, F (τ, s) ∂μ = ∫ s in Ioo 0 t, (Ioo 0 τ).indicator
        (fun s => (Real.exp (-(w * (τ - s))) : ℂ) * g s) s := by
      refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
      by_cases h : s < τ
      · have h1 : s ∈ Ioo 0 τ := ⟨hs.1, h⟩
        have h2 : 0 < τ - s ∧ τ - s < t := ⟨by linarith, by linarith [hs.1, hτ.2]⟩
        simp only [F, h2.1, h2.2, and_self, ite_true, indicator_of_mem h1]
      · have h1 : s ∉ Ioo 0 τ := fun hh => h hh.2
        have h2 : ¬ (0 < τ - s ∧ τ - s < t) := fun hh => h (by linarith [hh.1])
        simp only [F, h2, ite_false, indicator_of_notMem h1]
    rw [this, setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.mpr (Ioo_subset_Ioo_right hτ.2.le)]
  have hin2 : ∀ s ∈ Ioo 0 t, (w : ℂ) * ∫ τ, F (τ, s) ∂μ =
      (1 - (Real.exp (-(w * (t - s))) : ℂ)) * g s := by
    intro s hs
    have : ∫ τ, F (τ, s) ∂μ = ∫ τ in Ioo 0 t, (Ioo s t).indicator
        (fun τ => (Real.exp (-(w * (τ - s))) : ℂ) * g s) τ := by
      refine setIntegral_congr_fun measurableSet_Ioo fun τ hτ => ?_
      by_cases h : s < τ
      · have h1 : τ ∈ Ioo s t := ⟨h, hτ.2⟩
        have h2 : 0 < τ - s ∧ τ - s < t := ⟨by linarith, by linarith [hs.1, hτ.2]⟩
        simp only [F, h2.1, h2.2, and_self, ite_true, indicator_of_mem h1]
      · have h1 : τ ∉ Ioo s t := fun hh => h hh.1
        have h2 : ¬ (0 < τ - s ∧ τ - s < t) := fun hh => h (by linarith [hh.1])
        simp only [F, h2, ite_false, indicator_of_notMem h1]
    rw [this, setIntegral_indicator measurableSet_Ioo]
    have hset : Ioo 0 t ∩ Ioo s t = Ioo s t := by
      ext x; simp only [mem_inter_iff, mem_Ioo]
      constructor
      · rintro ⟨_, h⟩; exact h
      · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith [hs.1], h2⟩, h1, h2⟩
    rw [hset, integral_mul_const, integral_complex_ofReal]
    have := mul_integral_exp_shift w s t hs.2.le
    rw [← mul_assoc, ← Complex.ofReal_mul, this]
    push_cast
    ring
  have hI1 : ∫ τ in Ioo 0 t, (Real.exp (-(w * τ)) : ℂ) * a =
      ((∫ τ in Ioo 0 t, Real.exp (-(w * τ)) : ℝ) : ℂ) * a := by
    rw [integral_mul_const, integral_complex_ofReal]
  have hE0 := mul_integral_exp_shift w 0 t ht.le
  simp only [sub_zero] at hE0
  have hexm : Measurable (fun s : ℝ => (Real.exp (-(w * (t - s))) : ℂ)) :=
    Complex.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (measurable_const.sub measurable_id)).neg)
  have hgi : Integrable g μ :=
    Integrable.of_bound hgm.aestronglyMeasurable M (Filter.Eventually.of_forall hM)
  have hegi : Integrable (fun s : ℝ => (Real.exp (-(w * (t - s))) : ℂ) * g s) μ := by
    refine Integrable.of_bound (hexm.mul hgm).aestronglyMeasurable
      (Real.exp (|w| * t) * M) ?_
    rw [hμ, ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun s hs => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul ?_ (hM _) (norm_nonneg _) (Real.exp_pos _).le
    refine Real.exp_le_exp.mpr ?_
    have h0 : 0 < t - s := by linarith [hs.2]
    calc -(w * (t - s)) ≤ |w * (t - s)| := neg_le_abs _
      _ = |w| * (t - s) := by rw [abs_mul, abs_of_pos h0]
      _ ≤ |w| * t := mul_le_mul_of_nonneg_left (by linarith [hs.1]) (abs_nonneg _)
  have hcont : Integrable (fun τ : ℝ => (Real.exp (-(w * τ)) : ℂ) * a) μ := by
    have : Continuous (fun τ : ℝ => (Real.exp (-(w * τ)) : ℂ) * a) := by fun_prop
    exact this.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hUint : ∫ τ in Ioo 0 t, U τ =
      ((∫ τ in Ioo 0 t, Real.exp (-(w * τ)) : ℝ) : ℂ) * a + ∫ τ, ∫ s, F (τ, s) ∂μ ∂μ := by
    have h1 : ∫ τ in Ioo 0 t, U τ = ∫ τ, ((Real.exp (-(w * τ)) : ℂ) * a + ∫ s, F (τ, s) ∂μ) ∂μ :=
      setIntegral_congr_fun measurableSet_Ioo (fun τ hτ => by rw [hU τ hτ.1 hτ.2.le, hin1 τ hτ])
    rw [h1, integral_add hcont hFi.integral_prod_left, ← hI1]
  have hw2 : (w : ℂ) * ∫ τ, ∫ s, F (τ, s) ∂μ ∂μ =
      (∫ s in Ioo 0 t, g s) - ∫ s in Ioo 0 t, (Real.exp (-(w * (t - s))) : ℂ) * g s := by
    rw [hswap, ← integral_const_mul]
    have : ∫ s, (w : ℂ) * ∫ τ, F (τ, s) ∂μ ∂μ =
        ∫ s, (g s - (Real.exp (-(w * (t - s))) : ℂ) * g s) ∂μ :=
      setIntegral_congr_fun measurableSet_Ioo (fun s hs => by rw [hin2 s hs]; ring)
    rw [this, integral_sub hgi hegi]
  have hE0c : (w : ℂ) * ((∫ τ in Ioo 0 t, Real.exp (-(w * τ)) : ℝ) : ℂ) =
      1 - (Real.exp (-(w * t)) : ℂ) := by
    rw [← Complex.ofReal_mul, hE0]; push_cast; ring
  rw [hU t ht le_rfl, hUint]
  linear_combination a * hE0c + hw2

theorem fourierCoeff_duhamelPotential {B0 V : ℝ} {b : Torus d → Tangent d} (hb : Measurable b)
    (hbB : ∀ x, ‖b x‖ ≤ B0) {f : Torus d → ℝ} (hf : Integrable f (haar d))
    {v : ℝ × Torus d → Tangent d} (hv : Measurable v) (hvV : ∀ p, ‖v p‖ ≤ V) {t : ℝ} (ht : 0 < t)
    (k : Fin d → ℤ) :
    fourierCoeff (duhamelPotential b f v t) k =
      (Real.exp (-(gradWeight k * t)) : ℂ) * fourierCoeff f k +
        ∫ s in Ioo 0 t, (Real.exp (-(gradWeight k * (t - s))) : ℂ) * fourierCoeff (gSlice b v s) k := by
  have hJm : Measurable (fun r : Torus d × ℝ => Jint0 b v ((t, r.1), r.2)) :=
    (stronglyMeasurable_Jint0 hb hv).measurable.comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  obtain ⟨e, he⟩ : ∃ e : Torus d → ℂ, e = fun x => UnitAddTorus.mFourier (-k) x := ⟨_, rfl⟩
  have hE : ∀ x, UnitAddTorus.mFourier (-k) x = e x := fun x => by simp [he]
  have hem : Measurable e := by
    have := (UnitAddTorus.mFourier (-k) : C(UnitAddTorus (Fin d), ℂ)).continuous.measurable
    rw [he]; exact this
  have hen : ∀ x, ‖e x‖ ≤ 1 := fun x => by
    have := ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier (-k) : C(UnitAddTorus (Fin d), ℂ)) x
    rw [UnitAddTorus.mFourier_norm] at this
    rw [he]; exact this
  have hint : Integrable (fun r : Torus d × ℝ => e r.1 * ((Jint0 b v ((t, r.1), r.2) : ℝ) : ℂ))
      ((haar d).prod (volume.restrict (Ioo 0 t))) := by
    refine Integrable.of_bound ?_ (B0 * V) (Filter.Eventually.of_forall fun r => ?_)
    · exact ((hem.comp measurable_fst).mul (Complex.measurable_ofReal.comp hJm)).aestronglyMeasurable
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc ‖e r.1‖ * |Jint0 b v ((t, r.1), r.2)| ≤ 1 * (B0 * V) :=
            mul_le_mul (hen _) (abs_Jint0_le hbB hvV _) (abs_nonneg _) zero_le_one
        _ = B0 * V := one_mul _
  have hhc : Integrable (heatOp t f) (haar d) :=
    (continuous_torusConv (continuous_heatKernelT ht) hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hheat : Integrable (fun x => e x * ((heatOp t f x : ℝ) : ℂ)) (haar d) :=
    hhc.ofReal.bdd_mul hem.aestronglyMeasurable (Filter.Eventually.of_forall hen)
  have hcongr : ∀ x, ((duhamelPotential b f v t x : ℝ) : ℂ) =
      ((heatOp t f x : ℝ) : ℂ) + ∫ s in Ioo 0 t, ((Jint0 b v ((t, x), s) : ℝ) : ℂ) := by
    intro x
    rw [duhamelPotential_eq, Complex.ofReal_add, integral_complex_ofReal]
  have h1 : fourierCoeff (duhamelPotential b f v t) k =
      fourierCoeff (heatOp t f) k + ∫ x, ∫ s in Ioo 0 t, e x * ((Jint0 b v ((t, x), s) : ℝ) : ℂ) := by
    unfold fourierCoeff
    rw [mFourierCoeff_ofReal_eq, mFourierCoeff_ofReal_eq]
    simp_rw [hE, hcongr, mul_add]
    have hi2 : ∀ x, e x * ∫ s in Ioo 0 t, ((Jint0 b v ((t, x), s) : ℝ) : ℂ) =
        ∫ s in Ioo 0 t, e x * ((Jint0 b v ((t, x), s) : ℝ) : ℂ) := fun x =>
      (integral_const_mul _ _).symm
    simp_rw [hi2]
    have hg2 : Integrable (fun x => ∫ s in Ioo 0 t, e x * ((Jint0 b v ((t, x), s) : ℝ) : ℂ))
        (haar d) := hint.integral_prod_left
    rw [integral_add hheat hg2]
  rw [h1, fourierCoeff_heatOp ht hf, integral_integral_swap hint]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  have hs' : 0 < t - s := by linarith [hs.2]
  have hg := integrable_gSlice hb hv hbB hvV s
  have : fourierCoeff (heatOp (t - s) (gSlice b v s)) k =
      (Real.exp (-(gradWeight k * (t - s))) : ℂ) * fourierCoeff (gSlice b v s) k :=
    fourierCoeff_heatOp hs' hg k
  rw [← this]
  unfold fourierCoeff
  rw [mFourierCoeff_ofReal_eq]
  simp_rw [hE]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [Jint0_eq b v (t, x) hs']

/-- Integral form of the per-mode Duhamel ODE:
`û(t,k) - f̂(k) = -w_k ∫₀ᵗ û(s,k) ds + ∫₀ᵗ ĝ_s(k) ds`, where `ĝ_s = (b · v(s))^`. -/
theorem fourierCoeff_duhamelPotential_ode {B0 V : ℝ} {b : Torus d → Tangent d} (hb : Measurable b)
    (hbB : ∀ x, ‖b x‖ ≤ B0) {f : Torus d → ℝ} (hf : Integrable f (haar d))
    {v : ℝ × Torus d → Tangent d} (hv : Measurable v) (hvV : ∀ p, ‖v p‖ ≤ V) {t : ℝ} (ht : 0 < t)
    (k : Fin d → ℤ) :
    fourierCoeff (duhamelPotential b f v t) k - fourierCoeff f k =
      -(gradWeight k : ℂ) * (∫ τ in Ioo 0 t, fourierCoeff (duhamelPotential b f v τ) k) +
        ∫ s in Ioo 0 t, fourierCoeff (gSlice b v s) k := by
  have hgm : Measurable (fun s : ℝ => fourierCoeff (gSlice b v s) k) := by
    have hm : Measurable (fun p : ℝ × Torus d =>
        UnitAddTorus.mFourier (-k) p.2 * (gSlice b v p.1 p.2 : ℂ)) := by
      have h1 : Measurable (fun p : ℝ × Torus d => UnitAddTorus.mFourier (-k) p.2) :=
        ((UnitAddTorus.mFourier (-k) : C(UnitAddTorus (Fin d), ℂ)).continuous.measurable).comp
          measurable_snd
      have h2 : Measurable (fun p : ℝ × Torus d => gSlice b v p.1 p.2) :=
        (hb.comp measurable_snd).inner (hv.comp (measurable_fst.prodMk measurable_snd))
      exact h1.mul (Complex.measurable_ofReal.comp h2)
    have := hm.stronglyMeasurable.integral_prod_right' (ν := haar d)
    have heq : (fun s : ℝ => fourierCoeff (gSlice b v s) k) = fun s : ℝ =>
        ∫ x, UnitAddTorus.mFourier (-k) x * (gSlice b v s x : ℂ) ∂haar d :=
      funext fun s => mFourierCoeff_ofReal_eq _ _
    rw [heq]; exact this.measurable
  have hgb : ∀ s, ‖fourierCoeff (gSlice b v s) k‖ ≤ B0 * V := by
    intro s
    unfold fourierCoeff
    rw [mFourierCoeff_ofReal_eq]
    have := norm_integral_le_of_norm_le_const (μ := haar d) (C := B0 * V)
      (f := fun x => UnitAddTorus.mFourier (-k) x * (gSlice b v s x : ℂ))
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have h1 := ContinuousMap.norm_coe_le_norm
          (UnitAddTorus.mFourier (-k) : C(UnitAddTorus (Fin d), ℂ)) x
        rw [UnitAddTorus.mFourier_norm] at h1
        calc _ ≤ 1 * (B0 * V) :=
              mul_le_mul h1 (abs_gSlice_le hbB hvV s x) (abs_nonneg _) zero_le_one
          _ = B0 * V := one_mul _)
    simpa using this
  exact mode_integral_ode ht (fourierCoeff f k) hgm hgb
    (fun τ hτ _ => fourierCoeff_duhamelPotential hb hbB hf hv hvV hτ k)

end DGPS.Lipschitz
