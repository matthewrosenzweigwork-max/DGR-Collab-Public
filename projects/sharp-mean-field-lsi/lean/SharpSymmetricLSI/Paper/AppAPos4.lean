import SharpSymmetricLSI.Paper.AppAFourier3

/-!
# Positivity (4): the time identity for `ρ^ε = e^{εΔ}ρ`

For a linear mild solution and `ε > 0`, for every `t ∈ [0,T]`:
`e^{εΔ}ρ_t = e^{εΔ}ρ₀ + ∫_{(0,t]} (Δe^{εΔ}ρ_u + ∇·e^{εΔ}N_u) du` almost everywhere
(`heat_time_identity`), by comparing Fourier coefficients.
-/

open MeasureTheory Set Filter Topology Complex UnitAddTorus
open scoped Real ENNReal

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Coefficients of a time integral (Fubini). -/
theorem cf_setIntegral {G : ℝ → UnitAddTorus ι → ℝ} (hG : Measurable (Function.uncurry G))
    {t C : ℝ} (hC : ∀ u ∈ Ioc 0 t, ∀ x, |G u x| ≤ C) (n : ι → ℤ) :
    cf (fun x => ∫ u in Ioc 0 t, G u x) n = ∫ u in Ioc 0 t, cf (G u) n := by
  set g : ℝ → ℝ := (Ioc 0 t).indicator fun _ => C with hg
  have hgi : Integrable g := by
    refine IntegrableOn.integrable_indicator ?_ measurableSet_Ioc
    haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) :=
      isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
    exact integrable_const C
  set H : UnitAddTorus ι × ℝ → ℂ := fun p =>
    mFourier (-n) p.1 * (((Ioc 0 t).indicator (fun u => G u p.1) p.2 : ℝ) : ℂ) with hH
  have hHm : Measurable fun p : UnitAddTorus ι × ℝ => (Ioc 0 t).indicator (fun u => G u p.1) p.2 := by
    have e : (fun p : UnitAddTorus ι × ℝ => (Ioc 0 t).indicator (fun u => G u p.1) p.2) =
        {p : UnitAddTorus ι × ℝ | p.2 ∈ Ioc 0 t}.indicator (fun p => G p.2 p.1) := by
      funext p; simp [Set.indicator]
    rw [e]
    exact (hG.comp (measurable_snd.prodMk measurable_fst)).indicator
      (measurableSet_Ioc.preimage measurable_snd)
  have hHi : Integrable H (volume.prod volume) := by
    refine ((integrable_const (1 : ℝ)).mul_prod hgi).mono'
      (((mFourier (-n)).continuous.measurable.comp measurable_fst).mul
        (Complex.measurable_ofReal.comp hHm)).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    simp only [hH, norm_mul, Complex.norm_real, Real.norm_eq_abs, one_mul]
    refine mul_le_mul (norm_mFourier_le _ _) ?_ (abs_nonneg _) zero_le_one |>.trans (by rw [one_mul])
    by_cases hp : p.2 ∈ Ioc 0 t
    · simp only [hg, indicator_of_mem hp]; exact hC p.2 hp p.1
    · simp only [hg, indicator_of_notMem hp, abs_zero, le_refl]
  simp only [cf]
  rw [mFourierCoeff_eq_integral]
  have e1 : (fun x => mFourier (-n) x • (((∫ u in Ioc 0 t, G u x) : ℝ) : ℂ)) =
      fun x => ∫ u, H (x, u) := by
    funext x
    rw [← integral_indicator measurableSet_Ioc, smul_eq_mul, ← integral_complex_ofReal,
      ← integral_const_mul]
  rw [e1, integral_integral_swap hHi, ← integral_indicator measurableSet_Ioc]
  congr 1; funext u
  by_cases hu : u ∈ Ioc 0 t
  · rw [indicator_of_mem hu, mFourierCoeff_eq_integral]
    congr 1; funext x
    simp only [hH, indicator_of_mem hu, smul_eq_mul]
  · rw [indicator_of_notMem hu]
    simp only [hH, indicator_of_notMem hu, Complex.ofReal_zero, mul_zero, integral_zero]

/-- `L²` uniqueness from Fourier coefficients. -/
theorem ae_eq_of_cf_eq_appA {f g : UnitAddTorus ι → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (h : ∀ n, cf f n = cf g n) : f =ᵐ[volume] g := by
  have hfg := hf.sub hg
  have hs := hasSum_sq_mFourierCoeff_real hfg
  have h0 : ∀ n, ‖mFourierCoeff (fun y => ((f - g) y : ℂ)) n‖ ^ 2 = 0 := fun n => by
    have := cf_sub (hf.integrable one_le_two) (hg.integrable one_le_two) n
    simp only [cf] at this h
    simp only [Pi.sub_apply]
    rw [this, h n, sub_self, norm_zero]; ring
  simp_rw [h0] at hs
  have hint : ∫ y, (f - g) y ^ 2 = 0 := hs.unique hasSum_zero
  rw [integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg _) hfg.integrable_sq] at hint
  filter_upwards [hint] with y hy
  simp only [Pi.sub_apply, Pi.zero_apply, pow_eq_zero_iff two_ne_zero, sub_eq_zero] at hy
  exact hy

theorem measurable_divHeatT_joint {s : ℝ} (hs : 0 < s) {N : ℝ → UnitAddTorus ι → ι → ℝ}
    (hN : ∀ k, Measurable fun p : ℝ × UnitAddTorus ι => N p.1 p.2 k) :
    Measurable fun p : ℝ × UnitAddTorus ι => divHeatT s (N p.1) p.2 := by
  unfold divHeatT
  refine Finset.measurable_sum _ fun k _ => ?_
  have hm : StronglyMeasurable (fun q : (ℝ × UnitAddTorus ι) × (ι → ℝ) =>
      fderiv ℝ (heatKernel s) q.2 (Pi.single k 1) * N q.1.1 (q.1.2 - liftT q.2) k) :=
    (((measurable_fderiv_heatKernel hs k).comp measurable_snd).mul
      ((hN k).comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).sub (measurable_liftT.comp measurable_snd))))).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

namespace LinMild

variable {ρ₀ : UnitAddTorus ι → ℝ} {ρ : ℝ → UnitAddTorus ι → ℝ}
  {N : ℝ → UnitAddTorus ι → ι → ℝ} {A : ℝ} (h : LinMild ρ₀ ρ N A)
include h

/-- The forcing `Δe^{εΔ}ρ_u + ∇·e^{εΔ}N_u` of `ρ^ε`. -/
noncomputable def forcing (ε : ℝ) (u : ℝ) (x : UnitAddTorus ι) : ℝ :=
  lapHeat ε (ρ u) x + divHeatT ε (N u) x

omit h in
theorem measurable_forcing (h : LinMild ρ₀ ρ N A) {ε : ℝ} (hε : 0 < ε) :
    Measurable (Function.uncurry (forcing (ρ := ρ) (N := N) ε)) :=
  (measurable_lapHeat_joint h.meas).add (measurable_divHeatT_joint hε h.measN)

theorem abs_forcing_le {ε : ℝ} (hε : 0 < ε) {T K : ℝ}
    (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K) {u : ℝ} (hu : u ∈ Icc 0 T) (x : UnitAddTorus ι) :
    |forcing (ρ := ρ) (N := N) ε u x| ≤
      (∫ y, |lapKer (ι := ι) ε y|) * K + Fintype.card ι * divConst ε * (A * K) := by
  unfold forcing
  exact (abs_add_le _ _).trans (add_le_add (abs_lapHeat_le hε (hK u hu) x)
    (abs_divHeatT_le hε (fun k => Eventually.of_forall fun y => h.abs_N_le hK hu y k) x))

/-- **The time identity for `ρ^ε`.** -/
theorem heat_time_identity {ε : ℝ} (hε : 0 < ε) {T K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K) {t : ℝ} (ht : t ∈ Icc 0 T) :
    heatT ε (ρ t) =ᵐ[volume] fun x =>
      heatT ε ρ₀ x + ∫ u in Ioc 0 t, forcing (ρ := ρ) (N := N) ε u x := by
  have hT0 : 0 ≤ T := ht.1.trans ht.2
  have hρ₀b : ∀ x, |ρ₀ x| ≤ K := fun x => by rw [← h.init]; exact hK 0 ⟨le_rfl, hT0⟩ x
  set C := (∫ y, |lapKer (ι := ι) ε y|) * K + Fintype.card ι * divConst ε * (A * K)
  have hfb : ∀ u ∈ Ioc 0 t, ∀ x, |forcing (ρ := ρ) (N := N) ε u x| ≤ C := fun u hu x =>
    h.abs_forcing_le hε hK ⟨hu.1.le, hu.2.trans ht.2⟩ x
  have hfm := h.measurable_forcing hε
  have hHm : ∀ f : UnitAddTorus ι → ℝ, Measurable f → Measurable (heatT ε f) := fun f hf =>
    (measurable_heatT_joint hf).comp measurable_prodMk_left
  have hIm : Measurable fun x => ∫ u in Ioc 0 t, forcing (ρ := ρ) (N := N) ε u x := by
    have e : (fun x => ∫ u in Ioc 0 t, forcing (ρ := ρ) (N := N) ε u x) =
        fun x => ∫ u, (Ioc 0 t).indicator (fun u => forcing (ρ := ρ) (N := N) ε u x) u := by
      funext x; rw [integral_indicator measurableSet_Ioc]
    rw [e]
    have hm : Measurable fun p : UnitAddTorus ι × ℝ =>
        (Ioc 0 t).indicator (fun u => forcing (ρ := ρ) (N := N) ε u p.1) p.2 := by
      have e2 : (fun p : UnitAddTorus ι × ℝ =>
          (Ioc 0 t).indicator (fun u => forcing (ρ := ρ) (N := N) ε u p.1) p.2) =
          {p : UnitAddTorus ι × ℝ | p.2 ∈ Ioc 0 t}.indicator
            (fun p => forcing (ρ := ρ) (N := N) ε p.2 p.1) := by
        funext p; simp [Set.indicator]
      rw [e2]
      exact (hfm.comp (measurable_snd.prodMk measurable_fst)).indicator
        (measurableSet_Ioc.preimage measurable_snd)
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  have hIb : ∀ x, |∫ u in Ioc 0 t, forcing (ρ := ρ) (N := N) ε u x| ≤ C * t := fun x => by
    rw [← Real.norm_eq_abs]
    refine (norm_setIntegral_le_of_norm_le_const (C := C) measure_Ioc_lt_top
      fun u hu => by rw [Real.norm_eq_abs]; exact hfb u hu x).trans (le_of_eq ?_)
    simp [ht.1]
  have hHb : ∀ f : UnitAddTorus ι → ℝ, Measurable f → (∀ x, |f x| ≤ K) → ∀ x, |heatT ε f x| ≤ K :=
    fun f hf hb x => abs_heatT_le hε hf.aestronglyMeasurable (Eventually.of_forall hb) x
  have memLp2 : ∀ {f : UnitAddTorus ι → ℝ} {B : ℝ}, Measurable f → (∀ x, |f x| ≤ B) →
      MemLp f 2 volume := fun {f} {B} hf hb =>
    MemLp.of_bound hf.aestronglyMeasurable B (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hb x)
  refine ae_eq_of_cf_eq_appA (memLp2 (hHm _ (h.measurable_section t)) (hHb _ (h.measurable_section t) (hK t ht)))
    (memLp2 ((hHm _ h.meas0).add hIm) (fun x => (abs_add_le _ _).trans
      (add_le_add (hHb _ h.meas0 hρ₀b x) (hIb x)))) fun n => ?_
  -- the coefficients
  set lam := lamN n
  set c := cf ρ₀ n
  set b := modeB N T n
  have hbm := h.measurable_modeB T n
  have hbB := h.norm_modeB_le hK0 hK n
  have hode := mode_ode (lamN_nonneg n) hbm hbB c ht.1
  have hcfu : ∀ u ∈ Ioc 0 t, cf (forcing (ρ := ρ) (N := N) ε u) n =
      (heatMult ε n : ℂ) * (-(lam : ℂ) * ((Real.exp (-lam * u) : ℂ) * c + modeD lam b u) + b u) := by
    intro u hu
    have hu' : u ∈ Icc 0 T := ⟨hu.1.le, hu.2.trans ht.2⟩
    have hlm : Measurable (lapHeat ε (ρ u)) :=
      (measurable_lapHeat_joint h.meas).comp measurable_prodMk_left
    have hdm : Measurable (divHeatT ε (N u)) :=
      (measurable_divHeatT_joint hε h.measN).comp measurable_prodMk_left
    have i1 : Integrable (lapHeat ε (ρ u)) :=
      appA_integrable_of_abs_le' hlm (abs_lapHeat_le hε (hK u hu'))
    have i2 : Integrable (divHeatT ε (N u)) := appA_integrable_of_abs_le' hdm
      (abs_divHeatT_le hε (fun k => Eventually.of_forall fun y => h.abs_N_le hK hu' y k))
    show cf (fun x => lapHeat ε (ρ u) x + divHeatT ε (N u) x) n = _
    rw [cf_add i1 i2, cf_lapHeat hε (h.measurable_section u) (hK u hu'),
      cf_divHeatT hε (fun k => h.measurable_sectionN u k) (fun z k => h.abs_N_le hK hu' z k),
      h.cf_eq_mode hK0 hK n hu']
    simp only [b, modeB, if_pos hu']
    have hs : (heatMult ε n : ℂ) * ∑ k, 2 * π * I * n k * cf (fun z => N u z k) n =
        ∑ k, 2 * π * I * n k * ((heatMult ε n : ℂ) * cf (fun z => N u z k) n) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    linear_combination (-1 : ℂ) * hs
  have i3 : Integrable (heatT ε ρ₀) := appA_integrable_of_abs_le' (hHm _ h.meas0) (hHb _ h.meas0 hρ₀b)
  have i4 : Integrable fun x => ∫ u in Ioc 0 t, forcing (ρ := ρ) (N := N) ε u x :=
    appA_integrable_of_abs_le' hIm hIb
  rw [cf_heatT hε (h.measurable_section t) (hK t ht), h.cf_eq_mode hK0 hK n ht,
    cf_add i3 i4, cf_heatT hε h.meas0 hρ₀b, cf_setIntegral hfm hfb n,
    setIntegral_congr_fun measurableSet_Ioc hcfu, integral_const_mul]
  show (heatMult ε n : ℂ) * ((Real.exp (-lam * t) : ℂ) * c + modeD lam b t) = _
  rw [hode]; ring

end LinMild

end SharpLSI
