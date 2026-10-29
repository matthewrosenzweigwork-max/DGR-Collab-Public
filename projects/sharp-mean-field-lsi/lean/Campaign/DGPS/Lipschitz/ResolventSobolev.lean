import DGPS.Lipschitz.HeatKernelLr
import DGPS.Basic.ParabolicChainRule

open MeasureTheory Set Filter
open scoped ENNReal

namespace DGPS.Lipschitz

section Minkowski
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem minkowski_bdd (μ : Measure α) [IsFiniteMeasure μ] (ν : Measure β) [IsFiniteMeasure ν]
    {q : ℝ} (hq : 1 ≤ q) {g : β → α → ℝ≥0∞} (hg : Measurable (fun p : β × α => g p.1 p.2))
    {M : ℝ≥0∞} (hM : M ≠ ⊤) (hgM : ∀ t x, g t x ≤ M) :
    (∫⁻ x, (∫⁻ t, g t x ∂ν) ^ q ∂μ) ≤ (∫⁻ t, (∫⁻ x, (g t x) ^ q ∂μ) ^ (1 / q) ∂ν) ^ q := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  set f : α → ℝ≥0∞ := fun x => ∫⁻ t, g t x ∂ν with hf
  have hfm : Measurable f := hg.lintegral_prod_left'
  have hfM : ∀ x, f x ≤ M * ν Set.univ := fun x => by
    calc f x ≤ ∫⁻ t, M ∂ν := lintegral_mono fun t => hgM t x
      _ = M * ν univ := by simp
  have hfin : ∀ x, f x ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hM (measure_ne_top _ _)) (hfM x)
  set N : ℝ≥0∞ := ∫⁻ t, (∫⁻ x, (g t x) ^ q ∂μ) ^ (1 / q) ∂ν with hN
  rcases eq_or_lt_of_le hq with h1 | hq1
  · -- q = 1
    subst h1
    simp only [ENNReal.rpow_one, div_one, hN]
    rw [lintegral_lintegral_swap hg.aemeasurable]
  · set q' := Real.conjExponent q with hq'
    have hconj : q.HolderConjugate q' := Real.HolderConjugate.conjExponent hq1
    have hsum := hconj.inv_add_inv_eq_one
    have hq'pos : 0 < q' := hconj.symm.pos
    have hmul : (q - 1) * q' = q := by
      have h1 : 1 / q + 1 / q' = 1 := by simpa [one_div] using hsum
      field_simp at h1
      nlinarith
    have hAfin : (∫⁻ x, f x ^ q ∂μ) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ∫⁻ x, (M * ν univ) ^ q ∂μ) ?_ (lintegral_mono fun x =>
        ENNReal.rpow_le_rpow (hfM x) hq0.le)
      simp only [lintegral_const]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq0.le
        (ENNReal.mul_ne_top hM (measure_ne_top _ _))) (measure_ne_top _ _)
    set A := ∫⁻ x, f x ^ q ∂μ with hA
    have key : A ≤ N * A ^ (1 / q') := by
      calc A = ∫⁻ x, f x * f x ^ (q - 1) ∂μ := by
            refine lintegral_congr fun x => ?_
            calc f x ^ q = f x ^ (1 + (q - 1)) := by congr 1; ring
              _ = f x ^ (1 : ℝ) * f x ^ (q - 1) :=
                ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by linarith)
              _ = _ := by rw [ENNReal.rpow_one]
        _ = ∫⁻ x, ∫⁻ t, g t x * f x ^ (q - 1) ∂ν ∂μ := by
            refine lintegral_congr fun x => ?_
            exact (lintegral_mul_const _ (hg.comp (measurable_id.prodMk measurable_const))).symm
        _ = ∫⁻ t, ∫⁻ x, g t x * f x ^ (q - 1) ∂μ ∂ν := by
            refine lintegral_lintegral_swap ?_
            show AEMeasurable (fun p : α × β => g p.2 p.1 * f p.1 ^ (q - 1)) _
            exact ((hg.comp measurable_swap).mul ((hfm.comp measurable_fst).pow_const _)).aemeasurable
        _ ≤ ∫⁻ t, (∫⁻ x, (g t x) ^ q ∂μ) ^ (1 / q) * A ^ (1 / q') ∂ν := by
            refine lintegral_mono fun t => ?_
            have := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj
              (f := fun x => g t x) (g := fun x => f x ^ (q - 1))
              (hg.comp (measurable_const.prodMk measurable_id)).aemeasurable
              (hfm.pow_const _).aemeasurable
            refine this.trans (le_of_eq ?_)
            have hh : (∫⁻ x, (f x ^ (q - 1)) ^ q' ∂μ) = A := by
              refine lintegral_congr fun x => ?_
              rw [← ENNReal.rpow_mul, hmul]
            rw [hh]
        _ = N * A ^ (1 / q') := by
            rw [lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) hAfin)]
    by_cases hA0 : A = 0
    · simp [hA0]
    · have hB0 : A ^ (1 / q') ≠ 0 := by
        simpa using ENNReal.rpow_pos (pos_iff_ne_zero.2 hA0) hAfin |>.ne'
      have hBt : A ^ (1 / q') ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hAfin
      have hsplit : A = A ^ (1 / q) * A ^ (1 / q') := by
        rw [← ENNReal.rpow_add _ _ hA0 hAfin]
        have : 1 / q + 1 / q' = 1 := by simpa [one_div] using hsum
        rw [this, ENNReal.rpow_one]
      have h2 : A ^ (1 / q) ≤ N := by
        have : A ^ (1 / q) * A ^ (1 / q') ≤ N * A ^ (1 / q') := by rw [← hsplit]; exact key
        exact (ENNReal.mul_le_mul_iff_left hB0 hBt).1 this
      calc A = (A ^ (1 / q)) ^ q := by
            rw [← ENNReal.rpow_mul]; simp [hq0.ne']
        _ ≤ N ^ q := ENNReal.rpow_le_rpow h2 hq0.le

/-- **Minkowski's integral inequality** (`ℝ≥0∞`-valued, finite measures). -/
theorem minkowski_lintegral (μ : Measure α) [IsFiniteMeasure μ] (ν : Measure β) [IsFiniteMeasure ν]
    {q : ℝ} (hq : 1 ≤ q) {g : β → α → ℝ≥0∞} (hg : Measurable (fun p : β × α => g p.1 p.2)) :
    (∫⁻ x, (∫⁻ t, g t x ∂ν) ^ q ∂μ) ^ (1 / q) ≤ ∫⁻ t, (∫⁻ x, (g t x) ^ q ∂μ) ^ (1 / q) ∂ν := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  set N : ℝ≥0∞ := ∫⁻ t, (∫⁻ x, (g t x) ^ q ∂μ) ^ (1 / q) ∂ν with hN
  have hbd : ∀ n : ℕ, (∫⁻ x, (∫⁻ t, min (g t x) n ∂ν) ^ q ∂μ) ≤ N ^ q := by
    intro n
    refine (minkowski_bdd μ ν hq (g := fun t x => min (g t x) n)
      (hg.min measurable_const) (M := n) (ENNReal.natCast_ne_top n) (fun t x => min_le_right _ _)).trans ?_
    refine ENNReal.rpow_le_rpow (lintegral_mono fun t => ?_) hq0.le
    refine ENNReal.rpow_le_rpow (lintegral_mono fun x => ?_) (by positivity)
    exact ENNReal.rpow_le_rpow (min_le_left _ _) hq0.le
  have hsup : (∫⁻ x, (∫⁻ t, g t x ∂ν) ^ q ∂μ) ≤ N ^ q := by
    have hmono : ∀ x, Monotone fun n : ℕ => (∫⁻ t, min (g t x) n ∂ν) ^ q := fun x a b hab =>
      ENNReal.rpow_le_rpow (lintegral_mono fun t => min_le_min_left _ (by exact_mod_cast hab)) hq0.le
    have h1 : ∀ x, (∫⁻ t, g t x ∂ν) ^ q = ⨆ n : ℕ, (∫⁻ t, min (g t x) n ∂ν) ^ q := by
      intro x
      have hm : Monotone fun n : ℕ => ∫⁻ t, min (g t x) n ∂ν := fun a b hab =>
        lintegral_mono fun t => min_le_min_left _ (by exact_mod_cast hab)
      have e : ∫⁻ t, g t x ∂ν = ⨆ n : ℕ, ∫⁻ t, min (g t x) n ∂ν := by
        rw [← lintegral_iSup (f := fun (n : ℕ) t => min (g t x) (n : ℝ≥0∞))
          (fun n => (hg.comp (measurable_id.prodMk measurable_const)).min measurable_const)
          (fun a b hab t => min_le_min_left _ (by exact_mod_cast hab))]
        refine lintegral_congr fun t => ?_
        refine le_antisymm ?_ (iSup_le fun n => min_le_left _ _)
        by_cases ht : g t x = ⊤
        · rw [ht]; simp [ENNReal.iSup_natCast]
        · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt ht
          exact le_iSup_of_le n (le_min le_rfl hn.le)
      rw [e]
      exact (Monotone.map_iSup_of_continuousAt (f := fun y : ℝ≥0∞ => y ^ q)
        (g := fun n : ℕ => ∫⁻ t, min (g t x) (n : ℝ≥0∞) ∂ν)
        (ENNReal.continuous_rpow_const.continuousAt) (ENNReal.monotone_rpow_of_nonneg hq0.le)
        (by simp [hq0]))
    simp_rw [h1]
    rw [lintegral_iSup (fun n => ?_) (fun a b hab x => hmono x hab)]
    · exact iSup_le hbd
    · have hmn : Measurable fun p : β × α => min (g p.1 p.2) (n : ℝ≥0∞) :=
        hg.min measurable_const
      exact hmn.lintegral_prod_left'.pow_const _
  calc (∫⁻ x, (∫⁻ t, g t x ∂ν) ^ q ∂μ) ^ (1 / q) ≤ (N ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow hsup (by positivity)
    _ = N := by rw [← ENNReal.rpow_mul]; simp [hq0.ne']

end Minkowski

section Gamma

theorem lintegral_exp_rpow {b : ℝ} (hb : -1 < b) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t) * t ^ b) = ENNReal.ofReal (Real.Gamma (b + 1)) := by
  have h := Real.Gamma_eq_integral (s := b + 1) (by linarith)
  rw [h, ← ofReal_integral_eq_lintegral_ofReal]
  · simp
  · have := Real.GammaIntegral_convergent (s := b + 1) (by linarith)
    rwa [add_sub_cancel_right] at this
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt ht) _)

end Gamma

section LqResolvent
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- The exponential weight on `(0,∞)` as a finite measure. -/
noncomputable def expMeasure : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity fun t => ENNReal.ofReal (Real.exp (-t))

theorem expMeasure_univ : expMeasure Set.univ = 1 := by
  unfold expMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_restrict MeasurableSet.univ, univ_inter]
  have := lintegral_exp_rpow (b := 0) (by norm_num)
  simp only [Real.rpow_zero, mul_one, zero_add, Real.Gamma_one, ENNReal.ofReal_one] at this
  exact this

instance : IsFiniteMeasure expMeasure := ⟨by rw [expMeasure_univ]; exact ENNReal.one_lt_top⟩

theorem eLpNorm_timeIntegral_le {Φ : ℝ → Torus d → E}
    (hΦ : StronglyMeasurable (fun p : ℝ × Torus d => Φ p.1 p.2)) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (hqt : q ≠ ⊤) :
    eLpNorm (fun x => ∫ t in Ioi (0 : ℝ), Real.exp (-t) • Φ t x) q (haar d) ≤
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t)) * eLpNorm (Φ t) q (haar d) := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  have hqr : 1 ≤ q.toReal := by
    have := ENNReal.toReal_mono hqt hq
    simpa using this
  have hqr0 : 0 < q.toReal := lt_of_lt_of_le one_pos hqr
  have hΦm : Measurable (fun p : ℝ × Torus d => Φ p.1 p.2) := hΦ.measurable
  set g : ℝ → Torus d → ℝ≥0∞ := fun t x => ‖Φ t x‖ₑ with hg
  have hgm : Measurable (fun p : ℝ × Torus d => g p.1 p.2) := hΦm.enorm
  have hpt : ∀ x, ‖∫ t in Ioi (0 : ℝ), Real.exp (-t) • Φ t x‖ₑ ≤ ∫⁻ t, g t x ∂expMeasure := by
    intro x
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    unfold expMeasure
    have hw : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-t)) := by fun_prop
    have hgx : Measurable fun t => g t x := hgm.comp (measurable_id.prodMk measurable_const)
    rw [lintegral_withDensity_eq_lintegral_mul _ hw hgx]
    refine lintegral_congr fun t => ?_
    simp only [Pi.mul_apply, enorm_smul, hg]
    congr 1
    rw [Real.enorm_eq_ofReal (Real.exp_pos _).le]
  have hmk := minkowski_lintegral (haar d) expMeasure hqr hgm
  have h1 : eLpNorm (fun x => ∫ t in Ioi (0 : ℝ), Real.exp (-t) • Φ t x) q (haar d) ≤
      (∫⁻ x, (∫⁻ t, g t x ∂expMeasure) ^ q.toReal ∂haar d) ^ (1 / q.toReal) := by
    have hI : AEStronglyMeasurable (fun x => ∫ t in Ioi (0 : ℝ), Real.exp (-t) • Φ t x) (haar d) :=
      (((Real.measurable_exp.comp measurable_neg).comp measurable_fst).smul hΦm
        |>.stronglyMeasurable.integral_prod_left (μ := volume.restrict (Ioi (0 : ℝ)))).aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt hI]
    exact ENNReal.rpow_le_rpow (lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt x) hqr0.le)
      (by positivity)
  refine h1.trans (hmk.trans (le_of_eq ?_))
  unfold expMeasure
  have hm : Measurable fun t : ℝ => (∫⁻ x, (g t x) ^ q.toReal ∂haar d) ^ (1 / q.toReal) :=
    (((hgm.pow_const _).lintegral_prod_right')).pow_const _
  have hw : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-t)) := by fun_prop
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hm]
  refine lintegral_congr fun t => ?_
  simp only [Pi.mul_apply]
  have hs : AEStronglyMeasurable (Φ t) (haar d) :=
    (hΦ.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt hs]

end LqResolvent

section Resolvent
variable {d : ℕ}

/-- The resolvent `R F = ∫₀^∞ e^{-t} H_t F dt` (pointwise Bochner integral). -/
noncomputable def resolvent (F : Torus d → ℝ) (x : Torus d) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-t) * heatOp t F x

/-- The resolvent gradient `∇R F = ∫₀^∞ e^{-t} ∇H_t F dt` (Riesz vectors). -/
noncomputable def resolventGrad (F : Torus d → ℝ) (x : Torus d) : Tangent d :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-t) • kerGrad t F x

/-- Jointly measurable version of `(t, x) ↦ H_t F x`. -/
noncomputable def heatJ (G : Torus d → ℝ) (p : ℝ × Torus d) : ℝ :=
  ∫ w, G w * Kt p.1 (secE p.2 - secE w) ∂haar d

/-- Jointly measurable version of `(t, x) ↦ ∇H_t F x`. -/
noncomputable def gradJ (G : Torus d → ℝ) (p : ℝ × Torus d) : Tangent d :=
  ∫ w, G w • Dk p.1 (secE p.2 - secE w) ∂haar d

theorem stronglyMeasurable_heatJ {G : Torus d → ℝ} (hG : Measurable G) :
    StronglyMeasurable (heatJ G) := by
  have h : Measurable fun z : (ℝ × Torus d) × Torus d =>
      G z.2 * Kt z.1.1 (secE z.1.2 - secE z.2) :=
    (hG.comp measurable_snd).mul (measurable_Kt.comp (measurable_fst.comp measurable_fst |>.prodMk
      ((measurable_secE.comp (measurable_snd.comp measurable_fst)).sub
        (measurable_secE.comp measurable_snd))))
  exact h.stronglyMeasurable.integral_prod_right'

theorem stronglyMeasurable_gradJ {G : Torus d → ℝ} (hG : Measurable G) :
    StronglyMeasurable (gradJ G) := by
  have h : Measurable fun z : (ℝ × Torus d) × Torus d =>
      G z.2 • Dk z.1.1 (secE z.1.2 - secE z.2) :=
    (hG.comp measurable_snd).smul (measurable_Dk.comp (measurable_fst.comp measurable_fst |>.prodMk
      ((measurable_secE.comp (measurable_snd.comp measurable_fst)).sub
        (measurable_secE.comp measurable_snd))))
  exact h.stronglyMeasurable.integral_prod_right'

theorem heatJ_eq {F G : Torus d → ℝ} (hFG : F =ᵐ[haar d] G) {t : ℝ} (ht : 0 < t) (x : Torus d) :
    heatJ G (t, x) = heatOp t F x := by
  rw [heatOp_eq_integral]
  unfold heatJ
  refine integral_congr_ae ?_
  filter_upwards [hFG] with w hw
  rw [hw, Kt_eq ht]

theorem gradJ_eq {F G : Torus d → ℝ} (hFG : F =ᵐ[haar d] G) {t : ℝ} (x : Torus d) :
    gradJ G (t, x) = kerGrad t F x := by
  unfold gradJ kerGrad
  refine integral_congr_ae ?_
  filter_upwards [hFG] with w hw
  rw [hw]

theorem resolvent_eq {F G : Torus d → ℝ} (hFG : F =ᵐ[haar d] G) (x : Torus d) :
    resolvent F x = ∫ t in Ioi (0 : ℝ), Real.exp (-t) • heatJ G (t, x) := by
  unfold resolvent
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [smul_eq_mul]
  rw [heatJ_eq hFG ht]

theorem resolventGrad_eq {F G : Torus d → ℝ} (hFG : F =ᵐ[haar d] G) (x : Torus d) :
    resolventGrad F x = ∫ t in Ioi (0 : ℝ), Real.exp (-t) • gradJ G (t, x) := by
  unfold resolventGrad
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [gradJ_eq hFG]


theorem theta_bounds {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q) :
    0 ≤ (p⁻¹).toReal - (q⁻¹).toReal ∧ (p⁻¹).toReal - (q⁻¹).toReal ≤ 1 := by
  have hp1 : p⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hp
  have hqp : q⁻¹ ≤ p⁻¹ := ENNReal.inv_le_inv.2 hpq
  have h1 : (p⁻¹).toReal ≤ 1 := by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hp1
  have h2 : (q⁻¹).toReal ≤ (p⁻¹).toReal := ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top hp1) hqp
  have h3 : 0 ≤ (q⁻¹).toReal := ENNReal.toReal_nonneg
  constructor <;> linarith

theorem lintegral_two_term {c a₁ a₂ : ℝ} (hc : 0 ≤ c) (h₁ : -1 < a₁) (h₂ : -1 < a₂) {f : ℝ → ℝ}
    (hf : ∀ t : ℝ, 0 < t → f t ≤ c * (t ^ a₁ + t ^ a₂)) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t)) * ENNReal.ofReal (f t) ≤
      ENNReal.ofReal (c * (Real.Gamma (a₁ + 1) + Real.Gamma (a₂ + 1))) := by
  have hm : ∀ a : ℝ, Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-t) * t ^ a) := fun a =>
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp measurable_neg).mul
      (measurable_id.pow_const a))
  calc ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t)) * ENNReal.ofReal (f t)
      ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal c * (ENNReal.ofReal (Real.exp (-t) * t ^ a₁) +
          ENNReal.ofReal (Real.exp (-t) * t ^ a₂)) := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        have ht' : 0 < t := ht
        have hE := (Real.exp_pos (-t))
        rw [← ENNReal.ofReal_mul hE.le, ← ENNReal.ofReal_add (mul_nonneg hE.le (Real.rpow_nonneg ht'.le _))
          (mul_nonneg hE.le (Real.rpow_nonneg ht'.le _)), ← ENNReal.ofReal_mul hc]
        refine ENNReal.ofReal_le_ofReal ?_
        calc Real.exp (-t) * f t ≤ Real.exp (-t) * (c * (t ^ a₁ + t ^ a₂)) :=
              mul_le_mul_of_nonneg_left (hf t ht') hE.le
          _ = _ := by ring
    _ = ENNReal.ofReal c * (ENNReal.ofReal (Real.Gamma (a₁ + 1)) + ENNReal.ofReal (Real.Gamma (a₂ + 1))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left (hm a₁),
          lintegral_exp_rpow h₁, lintegral_exp_rpow h₂]
    _ = _ := by
        rw [← ENNReal.ofReal_add (Real.Gamma_pos_of_pos (by linarith)).le
          (Real.Gamma_pos_of_pos (by linarith)).le, ← ENNReal.ofReal_mul hc]

/-- The Lebesgue exponent gap `θ = 1/p - 1/q`. -/
noncomputable def theta (p q : ℝ≥0∞) : ℝ := (p⁻¹).toReal - (q⁻¹).toReal

/-- Constant in the `L^p → L^q` bound for `R`. -/
noncomputable def resConst (d : ℕ) (θ : ℝ) : ℝ := 2 ^ d * (1 + Real.Gamma (1 - d * θ / 2))

/-- Constant in the `L^p → L^q` bound for `∇R`. -/
noncomputable def gradConst (d : ℕ) (θ : ℝ) : ℝ :=
  2 ^ d * (d + 1) * (Real.Gamma (1 / 2) + Real.Gamma (1 / 2 - d * θ / 2))

theorem resConst_pos (d : ℕ) {θ : ℝ} (h : d * θ < 2) : 0 < resConst d θ := by
  unfold resConst
  have := Real.Gamma_pos_of_pos (show 0 < 1 - d * θ / 2 by linarith)
  positivity

theorem gradConst_pos (d : ℕ) {θ : ℝ} (h : d * θ < 1) : 0 < gradConst d θ := by
  unfold gradConst
  have h1 := Real.Gamma_pos_of_pos (show 0 < 1 - d * θ / 2 by linarith)
  have h2 := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
  have h3 := Real.Gamma_pos_of_pos (show 0 < 1 / 2 - d * θ / 2 by linarith)
  positivity

theorem lintegral_res_bound {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθ : d * θ < 2)
    {E : ℝ≥0∞} (hE : E ≠ ⊤) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t)) *
        (ENNReal.ofReal (2 ^ d * (1 + t ^ (-(d : ℝ) / 2)) ^ θ) * E) ≤
      ENNReal.ofReal (resConst d θ) * E := by
  calc _ = (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t)) *
        ENNReal.ofReal (2 ^ d * (1 + t ^ (-(d : ℝ) / 2)) ^ θ)) * E := by
        rw [← lintegral_mul_const' _ _ hE]
        refine lintegral_congr fun t => ?_
        rw [mul_assoc]
    _ ≤ ENNReal.ofReal (resConst d θ) * E := by
        refine mul_le_mul' ?_ le_rfl
        have h2 : -1 < -(d : ℝ) / 2 * θ := by linarith
        have := lintegral_two_term (c := 2 ^ d) (a₁ := 0) (a₂ := -(d : ℝ) / 2 * θ)
          (by positivity) (by norm_num) h2
          (f := fun t => 2 ^ d * (1 + t ^ (-(d : ℝ) / 2)) ^ θ) (fun t ht => by
            simp only [Real.rpow_zero]
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            calc (1 + t ^ (-(d : ℝ) / 2)) ^ θ
                ≤ 1 ^ θ + (t ^ (-(d : ℝ) / 2)) ^ θ :=
                  Real.rpow_add_le_add_rpow zero_le_one (Real.rpow_nonneg ht.le _) hθ0 hθ1
              _ = _ := by rw [Real.one_rpow, ← Real.rpow_mul ht.le])
        refine this.trans (le_of_eq ?_)
        congr 1
        unfold resConst
        simp only [zero_add, Real.Gamma_one]
        congr 3
        ring

theorem lintegral_grad_bound {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθ : d * θ < 1)
    {E : ℝ≥0∞} (hE : E ≠ ⊤) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t)) *
        (ENNReal.ofReal (2 ^ d * (d + 1) *
          (t ^ (-(1 : ℝ) / 2) * (1 + t ^ (-(d : ℝ) / 2)) ^ θ)) * E) ≤
      ENNReal.ofReal (gradConst d θ) * E := by
  calc _ = (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t)) *
        ENNReal.ofReal (2 ^ d * (d + 1) *
          (t ^ (-(1 : ℝ) / 2) * (1 + t ^ (-(d : ℝ) / 2)) ^ θ))) * E := by
        rw [← lintegral_mul_const' _ _ hE]
        refine lintegral_congr fun t => ?_
        exact (mul_assoc _ _ _).symm
    _ ≤ ENNReal.ofReal (gradConst d θ) * E := by
        refine mul_le_mul' ?_ le_rfl
        have h2 : -1 < -(1 : ℝ) / 2 + -(d : ℝ) / 2 * θ := by linarith
        have := lintegral_two_term (c := 2 ^ d * (d + 1)) (a₁ := -(1 : ℝ) / 2)
          (a₂ := -(1 : ℝ) / 2 + -(d : ℝ) / 2 * θ)
          (by positivity) (by norm_num) h2
          (f := fun t => 2 ^ d * (d + 1) *
            (t ^ (-(1 : ℝ) / 2) * (1 + t ^ (-(d : ℝ) / 2)) ^ θ)) (fun t ht => by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            calc t ^ (-(1 : ℝ) / 2) * (1 + t ^ (-(d : ℝ) / 2)) ^ θ
                ≤ t ^ (-(1 : ℝ) / 2) * (1 + t ^ (-(d : ℝ) / 2 * θ)) := by
                  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ht.le _)
                  calc (1 + t ^ (-(d : ℝ) / 2)) ^ θ
                      ≤ 1 ^ θ + (t ^ (-(d : ℝ) / 2)) ^ θ :=
                        Real.rpow_add_le_add_rpow zero_le_one (Real.rpow_nonneg ht.le _) hθ0 hθ1
                    _ = _ := by rw [Real.one_rpow, ← Real.rpow_mul ht.le]
              _ = t ^ (-(1 : ℝ) / 2) + t ^ (-(1 : ℝ) / 2 + -(d : ℝ) / 2 * θ) := by
                  rw [Real.rpow_add ht, mul_add, mul_one])
        refine this.trans (le_of_eq ?_)
        congr 1
        unfold gradConst
        have e1 : (-(1 : ℝ) / 2 + 1) = 1 / 2 := by norm_num
        have e2 : (-(1 : ℝ) / 2 + -(d : ℝ) / 2 * θ + 1) = 1 / 2 - d * θ / 2 := by ring
        rw [e1, e2]

theorem eLpNorm_resolvent_le {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q) (hqt : q ≠ ⊤)
    (hθ : d * theta p q < 2) {F : Torus d → ℝ} (hF : AEStronglyMeasurable F (haar d)) :
    eLpNorm (resolvent F) q (haar d) ≤
      ENNReal.ofReal (resConst d (theta p q)) * eLpNorm F p (haar d) := by
  obtain ⟨hθ0, hθ1⟩ := theta_bounds hp hpq
  have hq : 1 ≤ q := hp.trans hpq
  by_cases hFt : eLpNorm F p (haar d) = ⊤
  · rw [hFt, ENNReal.mul_top]
    · exact le_top
    · exact (ENNReal.ofReal_pos.2 (resConst_pos d hθ)).ne'
  have hFG := hF.ae_eq_mk
  have hGm := hF.stronglyMeasurable_mk.measurable
  have hres : resolvent F = fun x => ∫ t in Ioi (0 : ℝ), Real.exp (-t) • heatJ (hF.mk F) (t, x) :=
    funext (resolvent_eq hFG)
  rw [hres]
  refine (eLpNorm_timeIntegral_le (Φ := fun t x => heatJ (hF.mk F) (t, x))
    (stronglyMeasurable_heatJ hGm) hq hqt).trans ?_
  calc ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t)) *
        eLpNorm (fun x => heatJ (hF.mk F) (t, x)) q (haar d)
      ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t)) *
        (ENNReal.ofReal (2 ^ d * (1 + t ^ (-(d : ℝ) / 2)) ^ theta p q) * eLpNorm F p (haar d)) := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        refine mul_le_mul' le_rfl ?_
        have : (fun x => heatJ (hF.mk F) (t, x)) = heatOp t F := funext (heatJ_eq hFG ht)
        rw [this]
        exact eLpNorm_heatOp_le ht hp hpq hF
    _ ≤ ENNReal.ofReal (resConst d (theta p q)) * eLpNorm F p (haar d) :=
        lintegral_res_bound hθ0 hθ1 hθ hFt

theorem eLpNorm_resolventGrad_le {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q) (hqt : q ≠ ⊤)
    (hθ : d * theta p q < 1) {F : Torus d → ℝ} (hF : AEStronglyMeasurable F (haar d)) :
    eLpNorm (resolventGrad F) q (haar d) ≤
      ENNReal.ofReal (gradConst d (theta p q)) * eLpNorm F p (haar d) := by
  obtain ⟨hθ0, hθ1⟩ := theta_bounds hp hpq
  have hq : 1 ≤ q := hp.trans hpq
  by_cases hFt : eLpNorm F p (haar d) = ⊤
  · rw [hFt, ENNReal.mul_top]
    · exact le_top
    · exact (ENNReal.ofReal_pos.2 (gradConst_pos d hθ)).ne'
  have hFG := hF.ae_eq_mk
  have hGm := hF.stronglyMeasurable_mk.measurable
  have hres : resolventGrad F =
      fun x => ∫ t in Ioi (0 : ℝ), Real.exp (-t) • gradJ (hF.mk F) (t, x) :=
    funext (resolventGrad_eq hFG)
  rw [hres]
  refine (eLpNorm_timeIntegral_le (Φ := fun t x => gradJ (hF.mk F) (t, x))
    (stronglyMeasurable_gradJ hGm) hq hqt).trans ?_
  calc ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t)) *
        eLpNorm (fun x => gradJ (hF.mk F) (t, x)) q (haar d)
      ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t)) *
        (ENNReal.ofReal (2 ^ d * (d + 1) *
          (t ^ (-(1 : ℝ) / 2) * (1 + t ^ (-(d : ℝ) / 2)) ^ theta p q)) * eLpNorm F p (haar d)) := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        refine mul_le_mul' le_rfl ?_
        have : (fun x => gradJ (hF.mk F) (t, x)) = kerGrad t F := funext (gradJ_eq hFG)
        rw [this]
        exact eLpNorm_kerGrad_le ht hp hpq hF
    _ ≤ ENNReal.ofReal (gradConst d (theta p q)) * eLpNorm F p (haar d) :=
        lintegral_grad_bound hθ0 hθ1 hθ hFt


open DGPS.Lipschitz.ParabolicChainRule

/-- Pointwise (every `x`) Hölder bound for a convolution on the torus. -/
theorem enorm_conv_le_holder {p r : ℝ≥0∞} (hpr : p⁻¹ + r⁻¹ = 1) {f g : Torus d → ℝ}
    (hf : AEStronglyMeasurable f (haar d)) (hg : AEStronglyMeasurable g (haar d)) (x : Torus d) :
    ‖∫ y, f (x - y) * g y ∂haar d‖ₑ ≤ eLpNorm f p (haar d) * eLpNorm g r (haar d) := by
  have : ENNReal.HolderTriple p r 1 := ⟨by simpa using hpr⟩
  have hmp : MeasurePreserving (fun y : Torus d => x - y) (haar d) (haar d) :=
    (haar d).measurePreserving_sub_left x
  have hfx : AEStronglyMeasurable (fun y => f (x - y)) (haar d) :=
    hf.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving
  have H := eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm (μ := haar d) (p := p) (q := r) (r := 1)
    (f := fun y => f (x - y)) (g := g) (fun a b : ℝ => a * b) 1 (by fun_prop) hfx hg
    (Filter.Eventually.of_forall fun y => by simp [enorm_mul])
  rw [eLpNorm_one_eq_lintegral_enorm (f := fun y => f (x - y) * g y) (hfx.mul hg)] at H
  have e : eLpNorm (fun y => f (x - y)) p (haar d) = eLpNorm f p (haar d) :=
    eLpNorm_comp_measurePreserving hf hmp
  rw [e, one_mul] at H
  refine (enorm_integral_le_lintegral_enorm _).trans (le_trans (le_of_eq ?_) H)
  simp [enorm_mul]

theorem exists_dual_exponent {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ r : ℝ≥0∞, 1 ≤ r ∧ p⁻¹ + r⁻¹ = 1 ∧ (1 - r⁻¹).toReal = theta p ⊤ := by
  obtain ⟨r, hr, h1, h2⟩ := exists_young_exponent hp (le_top : p ≤ ⊤)
  exact ⟨r, hr, by simpa using h1, h2⟩

theorem enorm_heatOp_le_top {p : ℝ≥0∞} (hp : 1 ≤ p) {t : ℝ} (ht : 0 < t) {F : Torus d → ℝ}
    (hF : AEStronglyMeasurable F (haar d)) (x : Torus d) :
    ‖heatOp t F x‖ₑ ≤
      ENNReal.ofReal (2 ^ d * (1 + t ^ (-(d : ℝ) / 2)) ^ theta p ⊤) * eLpNorm F p (haar d) := by
  obtain ⟨r, hr, hpr, hθ⟩ := exists_dual_exponent hp
  have hK := eLpNorm_heatKernelT_le (d := d) ht hr
  rw [hθ] at hK
  refine le_trans ?_ (mul_le_mul' hK le_rfl)
  exact enorm_conv_le_holder (f := heatKernelT t) (g := F) (p := r) (r := p) ((add_comm _ _).trans hpr) (continuous_heatKernelT ht).aestronglyMeasurable hF x

theorem enorm_kerGrad_le_top {p : ℝ≥0∞} (hp : 1 ≤ p) {t : ℝ} (ht : 0 < t) {F : Torus d → ℝ}
    (hF : AEStronglyMeasurable F (haar d)) (x : Torus d) :
    ‖kerGrad t F x‖ₑ ≤ ENNReal.ofReal (2 ^ d * (d + 1) *
        (t ^ (-(1 : ℝ) / 2) * (1 + t ^ (-(d : ℝ) / 2)) ^ theta p ⊤)) * eLpNorm F p (haar d) := by
  obtain ⟨r, hr, hpr, hθ⟩ := exists_dual_exponent hp
  have hK := eLpNorm_Psi_le (d := d) ht hr
  rw [hθ] at hK
  have h1 : ‖kerGrad t F x‖ₑ ≤ ‖∫ y, Psi t (x - y) * ‖F y‖ ∂haar d‖ₑ :=
    enorm_le_iff_norm_le.2 ((norm_kerGrad_le_conv ht F x).trans (le_abs_self _))
  refine h1.trans (le_trans ?_ (mul_le_mul' hK le_rfl))
  refine (enorm_conv_le_holder (f := Psi t) (g := fun y => ‖F y‖) (p := r) (r := p)
    ((add_comm _ _).trans hpr) (continuous_Psi ht).aestronglyMeasurable hF.norm x).trans ?_
  rw [eLpNorm_norm F hF]

theorem aestronglyMeasurable_resolvent {F : Torus d → ℝ} (hF : AEStronglyMeasurable F (haar d)) :
    AEStronglyMeasurable (resolvent F) (haar d) := by
  have hres : resolvent F = fun x => ∫ t in Ioi (0 : ℝ), Real.exp (-t) • heatJ (hF.mk F) (t, x) :=
    funext (resolvent_eq hF.ae_eq_mk)
  rw [hres]
  exact ((((Real.measurable_exp.comp measurable_neg).comp measurable_fst).smul
    (stronglyMeasurable_heatJ hF.stronglyMeasurable_mk.measurable).measurable).stronglyMeasurable.integral_prod_left
    (μ := volume.restrict (Ioi (0 : ℝ)))).aestronglyMeasurable

theorem aestronglyMeasurable_resolventGrad {F : Torus d → ℝ}
    (hF : AEStronglyMeasurable F (haar d)) :
    AEStronglyMeasurable (resolventGrad F) (haar d) := by
  have hres : resolventGrad F =
      fun x => ∫ t in Ioi (0 : ℝ), Real.exp (-t) • gradJ (hF.mk F) (t, x) :=
    funext (resolventGrad_eq hF.ae_eq_mk)
  rw [hres]
  exact ((((Real.measurable_exp.comp measurable_neg).comp measurable_fst).smul
    (stronglyMeasurable_gradJ hF.stronglyMeasurable_mk.measurable).measurable).stronglyMeasurable.integral_prod_left
    (μ := volume.restrict (Ioi (0 : ℝ)))).aestronglyMeasurable

theorem eLpNorm_resolvent_le_top {p : ℝ≥0∞} (hp : 1 ≤ p) (hθ : d * theta p ⊤ < 2)
    {F : Torus d → ℝ} (hF : AEStronglyMeasurable F (haar d)) :
    eLpNorm (resolvent F) ⊤ (haar d) ≤
      ENNReal.ofReal (resConst d (theta p ⊤)) * eLpNorm F p (haar d) := by
  obtain ⟨hθ0, hθ1⟩ := theta_bounds hp (le_top : p ≤ ⊤)
  by_cases hFt : eLpNorm F p (haar d) = ⊤
  · rw [hFt, ENNReal.mul_top]
    · exact le_top
    · exact (ENNReal.ofReal_pos.2 (resConst_pos d hθ)).ne'
  rw [eLpNorm_exponent_top (aestronglyMeasurable_resolvent hF)]
  refine eLpNormEssSup_le_of_ae_enorm_bound (Filter.Eventually.of_forall fun x => ?_)
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine le_trans ?_ (lintegral_res_bound hθ0 hθ1 hθ hFt)
  refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
  rw [enorm_mul, Real.enorm_eq_ofReal (Real.exp_pos _).le]
  exact mul_le_mul' le_rfl (enorm_heatOp_le_top hp ht hF x)

theorem eLpNorm_resolventGrad_le_top {p : ℝ≥0∞} (hp : 1 ≤ p) (hθ : d * theta p ⊤ < 1)
    {F : Torus d → ℝ} (hF : AEStronglyMeasurable F (haar d)) :
    eLpNorm (resolventGrad F) ⊤ (haar d) ≤
      ENNReal.ofReal (gradConst d (theta p ⊤)) * eLpNorm F p (haar d) := by
  obtain ⟨hθ0, hθ1⟩ := theta_bounds hp (le_top : p ≤ ⊤)
  by_cases hFt : eLpNorm F p (haar d) = ⊤
  · rw [hFt, ENNReal.mul_top]
    · exact le_top
    · exact (ENNReal.ofReal_pos.2 (gradConst_pos d hθ)).ne'
  rw [eLpNorm_exponent_top (aestronglyMeasurable_resolventGrad hF)]
  refine eLpNormEssSup_le_of_ae_enorm_bound (Filter.Eventually.of_forall fun x => ?_)
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine le_trans ?_ (lintegral_grad_bound hθ0 hθ1 hθ hFt)
  refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
  rw [enorm_smul, Real.enorm_eq_ofReal (Real.exp_pos _).le]
  exact mul_le_mul' le_rfl (enorm_kerGrad_le_top hp ht hF x)

/-- **(1)** `L^p → W^{1,q}` bound for the resolvent, `1 ≤ p ≤ q ≤ ∞`, `θ d < 1`. -/
theorem resolvent_Lq_bound {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q) (hθ : d * theta p q < 1)
    {F : Torus d → ℝ} (hF : AEStronglyMeasurable F (haar d)) :
    eLpNorm (resolvent F) q (haar d) ≤
        ENNReal.ofReal (resConst d (theta p q)) * eLpNorm F p (haar d) ∧
      eLpNorm (resolventGrad F) q (haar d) ≤
        ENNReal.ofReal (gradConst d (theta p q)) * eLpNorm F p (haar d) := by
  by_cases hqt : q = ⊤
  · subst hqt
    exact ⟨eLpNorm_resolvent_le_top hp (by linarith) hF, eLpNorm_resolventGrad_le_top hp hθ hF⟩
  · exact ⟨eLpNorm_resolvent_le hp hpq hqt (by linarith) hF,
      eLpNorm_resolventGrad_le hp hpq hqt hθ hF⟩

/-! ### The `C¹` endpoint -/

theorem one_add_rpow_le {x θ : ℝ} (hx : 0 ≤ x) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 + x) ^ θ ≤ 1 + x ^ θ := by
  simpa using Real.rpow_add_le_add_rpow (zero_le_one) hx hθ0 hθ1

theorem integrableOn_exp_rpow {b : ℝ} (hb : -1 < b) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ b) (Ioi 0) := by
  have := Real.GammaIntegral_convergent (s := b + 1) (by linarith)
  rwa [add_sub_cancel_right] at this

theorem integrableOn_resBound {θ a : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθ : d * θ < 2) (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * (2 ^ d * (1 + t ^ (-(d : ℝ) / 2)) ^ θ * a))
      (Ioi 0) := by
  have h0 := integrableOn_exp_rpow (b := 0) (by norm_num)
  have h1 := integrableOn_exp_rpow (b := -(d : ℝ) / 2 * θ) (by linarith)
  refine ((h0.add h1).const_mul (2 ^ d * a)).mono' ?_ ?_
  · exact (by fun_prop : Measurable fun t : ℝ =>
      Real.exp (-t) * (2 ^ d * (1 + t ^ (-(d : ℝ) / 2)) ^ θ * a)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    have hE := Real.exp_pos (-t)
    have hx : 0 ≤ t ^ (-(d : ℝ) / 2) := Real.rpow_nonneg ht'.le _
    have h2 := one_add_rpow_le hx hθ0 hθ1
    rw [← Real.rpow_mul ht'.le] at h2
    rw [Real.norm_of_nonneg (by positivity)]
    have h3 : 2 ^ d * (1 + t ^ (-(d : ℝ) / 2)) ^ θ * a ≤ 2 ^ d * (1 + t ^ (-(d : ℝ) / 2 * θ)) * a := by
      gcongr
    calc _ ≤ Real.exp (-t) * (2 ^ d * (1 + t ^ (-(d : ℝ) / 2 * θ)) * a) :=
          mul_le_mul_of_nonneg_left h3 hE.le
      _ = _ := by simp only [Pi.add_apply, Real.rpow_zero, mul_one]; ring

theorem integrableOn_gradBound {θ a : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθ : d * θ < 1) (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * (2 ^ d * (d + 1) *
      (t ^ (-(1 : ℝ) / 2) * (1 + t ^ (-(d : ℝ) / 2)) ^ θ) * a)) (Ioi 0) := by
  have h0 := integrableOn_exp_rpow (b := -(1 : ℝ) / 2) (by norm_num)
  have h1 := integrableOn_exp_rpow (b := -(1 : ℝ) / 2 + -(d : ℝ) / 2 * θ) (by linarith)
  refine ((h0.add h1).const_mul (2 ^ d * (d + 1) * a)).mono' ?_ ?_
  · exact (by fun_prop : Measurable fun t : ℝ => Real.exp (-t) * (2 ^ d * (d + 1) *
      (t ^ (-(1 : ℝ) / 2) * (1 + t ^ (-(d : ℝ) / 2)) ^ θ) * a)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    have hE := Real.exp_pos (-t)
    have hx : 0 ≤ t ^ (-(d : ℝ) / 2) := Real.rpow_nonneg ht'.le _
    have h2 := one_add_rpow_le hx hθ0 hθ1
    rw [← Real.rpow_mul ht'.le] at h2
    rw [Real.norm_of_nonneg (by positivity)]
    have h4 : 0 ≤ t ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg ht'.le _
    have h3 : 2 ^ d * (d + 1) * (t ^ (-(1 : ℝ) / 2) * (1 + t ^ (-(d : ℝ) / 2)) ^ θ) * a ≤
        2 ^ d * (d + 1) * (t ^ (-(1 : ℝ) / 2) * (1 + t ^ (-(d : ℝ) / 2 * θ))) * a := by
      gcongr
    calc _ ≤ Real.exp (-t) * (2 ^ d * (d + 1) *
          (t ^ (-(1 : ℝ) / 2) * (1 + t ^ (-(d : ℝ) / 2 * θ))) * a) :=
          mul_le_mul_of_nonneg_left h3 hE.le
      _ = _ := by
          simp only [Pi.add_apply]
          rw [Real.rpow_add ht']
          ring

theorem norm_le_of_enorm_le {V : Type*} [NormedAddCommGroup V] {y : V} {c : ℝ} {E : ℝ≥0∞}
    (hc : 0 ≤ c) (hE : E ≠ ⊤) (h : ‖y‖ₑ ≤ ENNReal.ofReal c * E) : ‖y‖ ≤ c * E.toReal := by
  rw [← ofReal_norm] at h
  have := (ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE)).1 h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at this

theorem fderiv_Hl_eq_toDual {t : ℝ} (ht : 0 < t) {F : Torus d → ℝ} (hF : Integrable F (haar d))
    (v : Tangent d) :
    fderiv ℝ (Hl t F) v =
      InnerProductSpace.toDual ℝ (Tangent d) (kerGrad t F (torusLift v.ofLp)) := by
  rw [toDual_kerGrad ht hF, (hasFDerivAt_Hl ht hF v).fderiv]
  obtain ⟨m, hm⟩ := SharpLSI.secT_liftT_eq (ι := Fin d) v.ofLp
  have hsec : secE (torusLift v.ofLp) = v + nE m := by
    unfold secE torusLift; rw [hm]; rfl
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only
  rw [hsec, show v + nE m - secE w = (v - secE w) + nE m by abel, fderiv_Kh_add_nE]

theorem enorm_resolvent_le_top {p : ℝ≥0∞} (hp : 1 ≤ p) (hθ : d * theta p ⊤ < 2)
    {F : Torus d → ℝ} (hF : AEStronglyMeasurable F (haar d))
    (hFt : eLpNorm F p (haar d) ≠ ⊤) (x : Torus d) :
    ‖resolvent F x‖ₑ ≤ ENNReal.ofReal (resConst d (theta p ⊤)) * eLpNorm F p (haar d) := by
  obtain ⟨hθ0, hθ1⟩ := theta_bounds hp (le_top : p ≤ ⊤)
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine le_trans ?_ (lintegral_res_bound hθ0 hθ1 hθ hFt)
  refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
  rw [enorm_mul, Real.enorm_eq_ofReal (Real.exp_pos _).le]
  exact mul_le_mul' le_rfl (enorm_heatOp_le_top hp ht hF x)

theorem enorm_resolventGrad_le_top {p : ℝ≥0∞} (hp : 1 ≤ p) (hθ : d * theta p ⊤ < 1)
    {F : Torus d → ℝ} (hF : AEStronglyMeasurable F (haar d))
    (hFt : eLpNorm F p (haar d) ≠ ⊤) (x : Torus d) :
    ‖resolventGrad F x‖ₑ ≤ ENNReal.ofReal (gradConst d (theta p ⊤)) * eLpNorm F p (haar d) := by
  obtain ⟨hθ0, hθ1⟩ := theta_bounds hp (le_top : p ≤ ⊤)
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine le_trans ?_ (lintegral_grad_bound hθ0 hθ1 hθ hFt)
  refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
  rw [enorm_smul, Real.enorm_eq_ofReal (Real.exp_pos _).le]
  exact mul_le_mul' le_rfl (enorm_kerGrad_le_top hp ht hF x)

/-- **(3)** The resolvent of an `L^p` function, `p > d`, is a `C¹` function on the torus, with
sup bounds on the function and its gradient. -/
theorem resolvent_C1 {p : ℝ≥0∞} (hp : 1 ≤ p) (hθ : d * theta p ⊤ < 1) {F : Torus d → ℝ}
    (hFi : Integrable F (haar d)) (hFt : eLpNorm F p (haar d) ≠ ⊤) :
    IsC1Periodic (resolvent F) ∧
      (∀ v : Tangent d, HasFDerivAt (fun u : Tangent d => resolvent F (torusLift u.ofLp))
        (InnerProductSpace.toDual ℝ (Tangent d) (resolventGrad F (torusLift v.ofLp))) v) ∧
      (∀ x, |resolvent F x| ≤ resConst d (theta p ⊤) * (eLpNorm F p (haar d)).toReal) ∧
      (∀ x, ‖resolventGrad F x‖ ≤ gradConst d (theta p ⊤) * (eLpNorm F p (haar d)).toReal) := by
  obtain ⟨hθ0, hθ1⟩ := theta_bounds hp (le_top : p ≤ ⊤)
  have hθ2 : (d : ℝ) * theta p ⊤ < 2 := by linarith
  have hFm : AEStronglyMeasurable F (haar d) := hFi.aestronglyMeasurable
  set a := (eLpNorm F p (haar d)).toReal with ha
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  set θ := theta p ⊤ with hθdef
  have hFG := hFm.ae_eq_mk
  have hGm := hFm.stronglyMeasurable_mk.measurable
  -- sup bounds at every point
  have hs1 : ∀ x, |resolvent F x| ≤ resConst d θ * a := fun x => by
    have := norm_le_of_enorm_le (resConst_pos d hθ2).le hFt (enorm_resolvent_le_top hp hθ2 hFm hFt x)
    simpa using this
  have hs2 : ∀ x, ‖resolventGrad F x‖ ≤ gradConst d θ * a := fun x =>
    norm_le_of_enorm_le (gradConst_pos d hθ).le hFt (enorm_resolventGrad_le_top hp hθ hFm hFt x)
  -- pointwise-in-t bounds
  have hb1 : ∀ t : ℝ, 0 < t → ∀ v : Tangent d,
      |Hl t F v| ≤ 2 ^ d * (1 + t ^ (-(d : ℝ) / 2)) ^ θ * a := fun t ht v => by
    have := norm_le_of_enorm_le (y := heatOp t F (torusLift v.ofLp))
      (c := 2 ^ d * (1 + t ^ (-(d : ℝ) / 2)) ^ θ) (by positivity) hFt
      (enorm_heatOp_le_top hp ht hFm _)
    simpa [Hl] using this
  have hb2 : ∀ t : ℝ, 0 < t → ∀ v : Tangent d,
      ‖fderiv ℝ (Hl t F) v‖ ≤ 2 ^ d * (d + 1) *
        (t ^ (-(1 : ℝ) / 2) * (1 + t ^ (-(d : ℝ) / 2)) ^ θ) * a := fun t ht v => by
    rw [fderiv_Hl_eq_toDual ht hFi, LinearIsometryEquiv.norm_map]
    exact norm_le_of_enorm_le (by positivity) hFt (enorm_kerGrad_le_top hp ht hFm _)
  -- measurability in t
  have mHl : ∀ v : Tangent d, AEStronglyMeasurable (fun t => Real.exp (-t) * Hl t F v)
      (volume.restrict (Ioi (0 : ℝ))) := fun v => by
    have hm : Measurable fun t : ℝ => Real.exp (-t) * heatJ (hFm.mk F) (t, torusLift v.ofLp) :=
      (Real.measurable_exp.comp measurable_neg).mul
        ((stronglyMeasurable_heatJ hGm).measurable.comp (measurable_id.prodMk measurable_const))
    refine hm.aestronglyMeasurable.congr ((ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun t ht => ?_))
    simp only [Hl]
    rw [heatJ_eq hFG ht]
  have mDHl : ∀ v : Tangent d, AEStronglyMeasurable
      (fun t => Real.exp (-t) • fderiv ℝ (Hl t F) v) (volume.restrict (Ioi (0 : ℝ))) := fun v => by
    have hm : Measurable fun t : ℝ => Real.exp (-t) •
        InnerProductSpace.toDual ℝ (Tangent d) (gradJ (hFm.mk F) (t, torusLift v.ofLp)) :=
      (Real.measurable_exp.comp measurable_neg).smul
        ((InnerProductSpace.toDual ℝ (Tangent d)).continuous.measurable.comp
          ((stronglyMeasurable_gradJ hGm).measurable.comp (measurable_id.prodMk measurable_const)))
    refine hm.aestronglyMeasurable.congr ((ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun t ht => ?_))
    simp only
    rw [fderiv_Hl_eq_toDual ht hFi, gradJ_eq hFG]
  have iB1 := integrableOn_resBound (d := d) hθ0 hθ1 hθ2 ha0
  have iB2 := integrableOn_gradBound (d := d) hθ0 hθ1 hθ ha0
  have hD : ∀ v : Tangent d, HasFDerivAt (fun u : Tangent d => resolvent F (torusLift u.ofLp))
      (∫ t in Ioi (0 : ℝ), Real.exp (-t) • fderiv ℝ (Hl t F) v) v := fun v => by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun (u : Tangent d) t =>
      Real.exp (-t) * Hl t F u) (F' := fun u t => Real.exp (-t) • fderiv ℝ (Hl t F) u)
      (bound := fun t => Real.exp (-t) * (2 ^ d * (d + 1) *
        (t ^ (-(1 : ℝ) / 2) * (1 + t ^ (-(d : ℝ) / 2)) ^ θ) * a)) (s := univ) Filter.univ_mem
      (Filter.Eventually.of_forall mHl) ?_ (mDHl v) ?_ iB2 ?_
    · refine Integrable.mono' iB1 (mHl v) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_left (hb1 t ht v) (Real.exp_pos _).le
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht x _ => ?_)
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_left (hb2 t ht x) (Real.exp_pos _).le
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht x _ => ?_)
      have h0 := hasFDerivAt_Hl ht hFi x
      rw [h0.fderiv]
      exact h0.const_mul (Real.exp (-t))
  have hderiv : ∀ v : Tangent d, (∫ t in Ioi (0 : ℝ), Real.exp (-t) • fderiv ℝ (Hl t F) v) =
      InnerProductSpace.toDual ℝ (Tangent d) (resolventGrad F (torusLift v.ofLp)) := fun v => by
    unfold resolventGrad
    have h := (InnerProductSpace.toDual ℝ (Tangent d)).toLinearIsometry.integral_comp_comm
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (fun t => Real.exp (-t) • kerGrad t F (torusLift v.ofLp))
    refine Eq.trans ?_ h
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [LinearIsometryEquiv.coe_toLinearIsometry, map_smul]
    rw [fderiv_Hl_eq_toDual ht hFi]
  have hcont : Continuous fun v : Tangent d => ∫ t in Ioi (0 : ℝ), Real.exp (-t) • fderiv ℝ (Hl t F) v := by
    refine continuous_of_dominated (bound := fun t => Real.exp (-t) * (2 ^ d * (d + 1) *
        (t ^ (-(1 : ℝ) / 2) * (1 + t ^ (-(d : ℝ) / 2)) ^ θ) * a)) mDHl ?_ iB2 ?_
    · intro v
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_left (hb2 t ht v) (Real.exp_pos _).le
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
      exact (continuous_const (y := Real.exp (-t))).smul ((contDiff_Hl ht hFi).continuous_fderiv (by simp))
  have hC1 : ContDiff ℝ 1 fun u : Tangent d => resolvent F (torusLift u.ofLp) := by
    rw [contDiff_one_iff_fderiv]
    refine ⟨fun v => (hD v).differentiableAt, ?_⟩
    have : fderiv ℝ (fun u : Tangent d => resolvent F (torusLift u.ofLp)) =
        fun v => ∫ t in Ioi (0 : ℝ), Real.exp (-t) • fderiv ℝ (Hl t F) v :=
      funext fun v => (hD v).fderiv
    rw [this]
    exact hcont
  refine ⟨hC1.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.contDiff,
    fun v => ?_, hs1, hs2⟩
  rw [← hderiv v]
  exact hD v


theorem theta_top_lt_one_of_gt {p : ℝ≥0∞} (hp : (d : ℝ≥0∞) < p) : d * theta p ⊤ < 1 := by
  unfold theta
  rw [ENNReal.inv_top, ENNReal.toReal_zero, sub_zero]
  rcases eq_or_ne p ⊤ with rfl | hpt
  · simp
  · have hp' : (d : ℝ) < p.toReal := by
      have := (ENNReal.toReal_lt_toReal (by simp) hpt).2 hp
      simpa using this
    have hpos : 0 < p.toReal := lt_of_le_of_lt (Nat.cast_nonneg d) hp'
    rw [ENNReal.toReal_inv, mul_inv_lt_iff₀ hpos]
    linarith

/-- **LIP010c2, main result.**  Let `R F = ∫₀^∞ e^{-t} H_t F dt` and `∇R F = ∫₀^∞ e^{-t} ∇H_t F dt`.

(1) for `1 ≤ p ≤ q ≤ ∞` with `d (1/p - 1/q) < 1`, `‖R F‖_q + ‖∇R F‖_q ≤ C ‖F‖_p` with the explicit
constant `C = resConst + gradConst` (Gamma function values);
(3) for `p > d`, `R F` is a `C¹` function on the torus whose derivative is the Riesz vector
`∇R F`, with `‖R F‖_∞ + ‖∇R F‖_∞ ≤ C ‖F‖_p`.

Part (2) (identification with the Fourier multiplier / the `H¹` weak solution) is not included. -/
theorem lip010c2_resolvent_sobolev (d : ℕ) :
    (∀ p q : ℝ≥0∞, 1 ≤ p → p ≤ q → d * theta p q < 1 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Torus d → ℝ, AEStronglyMeasurable F (haar d) →
        eLpNorm (resolvent F) q (haar d) + eLpNorm (resolventGrad F) q (haar d) ≤
          ENNReal.ofReal C * eLpNorm F p (haar d)) ∧
    (∀ p : ℝ≥0∞, (d : ℝ≥0∞) < p → 1 ≤ p → ∀ F : Torus d → ℝ, Integrable F (haar d) →
      eLpNorm F p (haar d) ≠ ⊤ →
        IsC1Periodic (resolvent F) ∧
        (∀ v : Tangent d, HasFDerivAt (fun u : Tangent d => resolvent F (torusLift u.ofLp))
          (InnerProductSpace.toDual ℝ (Tangent d) (resolventGrad F (torusLift v.ofLp))) v) ∧
        (∀ x, |resolvent F x| + ‖resolventGrad F x‖ ≤
          (resConst d (theta p ⊤) + gradConst d (theta p ⊤)) * (eLpNorm F p (haar d)).toReal)) := by
  refine ⟨fun p q hp hpq hθ => ?_, fun p hdp hp F hFi hFt => ?_⟩
  · have hθ2 : (d : ℝ) * theta p q < 2 := by linarith
    refine ⟨resConst d (theta p q) + gradConst d (theta p q),
      (add_pos (resConst_pos d hθ2) (gradConst_pos d hθ)).le, fun F hF => ?_⟩
    obtain ⟨h1, h2⟩ := resolvent_Lq_bound hp hpq hθ hF
    rw [ENNReal.ofReal_add (resConst_pos d hθ2).le (gradConst_pos d hθ).le, add_mul]
    exact add_le_add h1 h2
  · have hθ := theta_top_lt_one_of_gt hdp
    obtain ⟨h1, h2, h3, h4⟩ := resolvent_C1 hp hθ hFi hFt
    refine ⟨h1, h2, fun x => ?_⟩
    rw [add_mul]
    exact add_le_add (h3 x) (h4 x)

end Resolvent

end DGPS.Lipschitz
