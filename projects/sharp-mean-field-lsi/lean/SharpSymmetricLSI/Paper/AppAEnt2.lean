import SharpSymmetricLSI.Paper.AppAWeak5
import SharpSymmetricLSI.Paper.AppAEnt1

/-!
# The entropy (2): the time identity at level `ε`

For `G(x, ·) ∈ C¹` (locally bounded, uniformly in `x`) and a linear mild solution, with
`φ_u = e^{εΔ}ρ_u`:
`∫ G(x, φ_t) = ∫ G(x, φ_0) + ∫_{(0,t]} ∫ ∂ᵣG(x, φ_u) (Δφ_u + ∇·e^{εΔ}N_u) du` (`energy_eq`),
in time-integrated form (the chain rule is applied pointwise to the absolutely continuous version).
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace LinMild

variable {ρ₀ : UnitAddTorus ι → ℝ} {ρ : ℝ → UnitAddTorus ι → ℝ}
  {N : ℝ → UnitAddTorus ι → ι → ℝ} {A : ℝ} (h : LinMild ρ₀ ρ N A)
include h

/-- The absolutely continuous version `c + ∫_{(0,u]} forcing` and its properties. -/
theorem exists_version {ε : ℝ} (hε : 0 < ε) {T K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K) (hT0 : 0 ≤ T) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧
      (∀ v ∈ Icc 0 T, ∀ x, |forcing (ρ := ρ) (N := N) ε v x| ≤ C) ∧
      Measurable (fun p : ℝ × UnitAddTorus ι =>
        heatT ε ρ₀ p.2 + ∫ v in Ioc 0 p.1, forcing (ρ := ρ) (N := N) ε v p.2) ∧
      (∀ u ∈ Icc 0 T, ∀ x, |heatT ε ρ₀ x + ∫ v in Ioc 0 u, forcing (ρ := ρ) (N := N) ε v x| ≤ R) ∧
      (∀ u ∈ Icc 0 T, ∀ x, |heatT ε (ρ u) x| ≤ R) := by
  have hρ₀b : ∀ x, |ρ₀ x| ≤ K := fun x => by rw [← h.init]; exact hK 0 ⟨le_rfl, hT0⟩ x
  set Fo := forcing (ρ := ρ) (N := N) ε with hFo
  set C := (∫ y, |lapKer (ι := ι) ε y|) * K + Fintype.card ι * divConst ε * (A * K) with hC
  have hC0 : 0 ≤ C := by
    have := h.abs_forcing_le hε hK ⟨le_rfl, hT0⟩ (0 : UnitAddTorus ι)
    exact (abs_nonneg _).trans this
  have hFb : ∀ v ∈ Icc 0 T, ∀ x, |Fo v x| ≤ C := fun v hv x => h.abs_forcing_le hε hK hv x
  have hFm : Measurable (Function.uncurry Fo) := h.measurable_forcing hε
  have hcm : Measurable (heatT ε ρ₀) := (measurable_heatT_joint h.meas0).comp measurable_prodMk_left
  have hcb : ∀ x, |heatT ε ρ₀ x| ≤ K := fun x =>
    abs_heatT_le hε h.meas0.aestronglyMeasurable (Eventually.of_forall hρ₀b) x
  have hIb : ∀ u ∈ Icc 0 T, ∀ x, |∫ v in Ioc 0 u, Fo v x| ≤ C * T := fun u hu x => by
    rw [← Real.norm_eq_abs]
    refine (norm_setIntegral_le_of_norm_le_const (C := C) measure_Ioc_lt_top
      fun v hv => by
        rw [Real.norm_eq_abs]
        exact hFb v ⟨hv.1.le, hv.2.trans hu.2⟩ x).trans ?_
    simp only [Real.volume_real_Ioc, sub_zero, max_eq_left hu.1]
    exact mul_le_mul_of_nonneg_left hu.2 hC0
  refine ⟨C, K + C * T, hC0, by positivity, hFb,
    (hcm.comp measurable_snd).add (measurable_setIntegral_family h hFm),
    fun u hu x => (abs_add_le _ _).trans (add_le_add (hcb x) (hIb u hu x)), fun u hu x => ?_⟩
  exact (abs_heatT_le hε (h.measurable_section u).aestronglyMeasurable
    (Eventually.of_forall (hK u hu)) x).trans (by nlinarith)

/-- **The time identity** at level `ε`. -/
theorem energy_eq {G Gp : UnitAddTorus ι → ℝ → ℝ} (hG : ∀ x r, HasDerivAt (G x) (Gp x r) r)
    (hGpc : ∀ x, Continuous (Gp x)) (hGm : Measurable (Function.uncurry G))
    (hGpm : Measurable (Function.uncurry Gp))
    (hGb : ∀ R, ∃ M, 0 ≤ M ∧ ∀ x r, |r| ≤ R → |G x r| ≤ M ∧ |Gp x r| ≤ M)
    {ε : ℝ} (hε : 0 < ε) {T K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∫ x, G x (heatT ε (ρ t) x) = (∫ x, G x (heatT ε ρ₀ x)) +
      ∫ u in Ioc 0 t, ∫ x, Gp x (heatT ε (ρ u) x) * forcing (ρ := ρ) (N := N) ε u x := by
  have hT0 : 0 ≤ T := ht.1.trans ht.2
  obtain ⟨C, R, hC0, hR0, hFb, hfvm, hfvb, hφb⟩ := h.exists_version hε hK0 hK hT0
  set Fo := forcing (ρ := ρ) (N := N) ε with hFo
  have hFm : Measurable (Function.uncurry Fo) := h.measurable_forcing hε
  set c : UnitAddTorus ι → ℝ := heatT ε ρ₀ with hc
  set fv : ℝ → UnitAddTorus ι → ℝ := fun u x => c x + ∫ v in Ioc 0 u, Fo v x with hfv
  have hfvm' : Measurable (Function.uncurry fv) := hfvm
  obtain ⟨M, hM0, hM⟩ := hGb R
  -- (1) the chain rule at each `x`
  have hchain : ∀ x, G x (fv t x) - G x (c x) = ∫ u in Ioc 0 t, Gp x (fv u x) * Fo u x := by
    intro x
    have hgm : Measurable fun v => Fo v x := hFm.comp (measurable_id.prodMk measurable_const)
    have hgi : IntervalIntegrable (fun v => Fo v x) volume 0 t := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1]
      haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) :=
        isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
      exact (integrable_const C).mono' hgm.aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv => by
          rw [Real.norm_eq_abs]; exact hFb v ⟨hv.1.le, hv.2.trans ht.2⟩ x))
    have := chain_rule_intervalIntegral ht.1 hgi (hG x) (hGpc x) (c x)
    rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1] at this
    simp only [hfv]
    rw [this]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    rw [intervalIntegral.integral_of_le hu.1.le]
  -- (2) Fubini
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  set H : UnitAddTorus ι × ℝ → ℝ := fun p =>
    (Icc 0 t).indicator (fun u => Gp p.1 (fv u p.1) * Fo u p.1) p.2 with hH
  have hHm : Measurable H := by
    have e : H = {p : UnitAddTorus ι × ℝ | p.2 ∈ Icc 0 t}.indicator
        (fun p => Gp p.1 (fv p.2 p.1) * Fo p.2 p.1) := by
      funext p; simp [hH, Set.indicator]
    rw [e]
    exact ((hGpm.comp (measurable_fst.prodMk (hfvm'.comp (measurable_snd.prodMk measurable_fst)))).mul
      (hFm.comp (measurable_snd.prodMk measurable_fst))).indicator
      (measurableSet_Icc.preimage measurable_snd)
  have hHb : ∀ p, |H p| ≤ M * C := fun p => by
    simp only [hH]
    by_cases hp : p.2 ∈ Icc 0 t
    · rw [indicator_of_mem hp, abs_mul]
      exact mul_le_mul (hM _ _ (hfvb p.2 ⟨hp.1, hp.2.trans ht.2⟩ p.1)).2
        (hFb p.2 ⟨hp.1, hp.2.trans ht.2⟩ p.1) (abs_nonneg _) hM0
    · rw [indicator_of_notMem hp, abs_zero]; positivity
  have hHi : Integrable H (volume.prod (volume.restrict (Ioc 0 t))) :=
    (integrable_const (M * C)).mono' hHm.aestronglyMeasurable
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hHb p)
  have hHx : ∀ x, ∫ u in Ioc 0 t, Gp x (fv u x) * Fo u x = ∫ u in Ioc 0 t, H (x, u) := fun x =>
    setIntegral_congr_fun measurableSet_Ioc fun u hu => by
      simp only [hH, indicator_of_mem (Ioc_subset_Icc_self hu)]
  -- (3) the replacement `fv u = e^{εΔ}ρ_u` a.e.
  have hrep : ∀ u ∈ Ioc 0 t, ∫ x, H (x, u) = ∫ x, Gp x (heatT ε (ρ u) x) * Fo u x := by
    intro u hu
    have hid := h.heat_time_identity hε hK0 hK ⟨hu.1.le, hu.2.trans ht.2⟩
    refine integral_congr_ae ?_
    filter_upwards [hid] with x hx
    simp only [hH, indicator_of_mem (Ioc_subset_Icc_self hu)]
    rw [hx]
  -- (4) assemble
  have hφt := h.heat_time_identity hε hK0 hK ht
  have hGfv : ∀ x, G x (fv t x) = G x (c x) + ∫ u in Ioc 0 t, H (x, u) := fun x => by
    rw [← hHx]; linarith [hchain x]
  have hcm : Measurable c := (measurable_heatT_joint h.meas0).comp measurable_prodMk_left
  have hGcm : Integrable fun x => G x (c x) :=
    appA_integrable_of_abs_le' (hGm.comp (measurable_id.prodMk hcm)) fun x =>
      (hM _ _ (by simpa [hfv] using hfvb 0 ⟨le_rfl, hT0⟩ x)).1
  have hInt := hHi.integral_prod_left
  calc ∫ x, G x (heatT ε (ρ t) x) = ∫ x, G x (fv t x) := by
        refine integral_congr_ae ?_
        filter_upwards [hφt] with x hx
        rw [hx]
    _ = (∫ x, G x (c x)) + ∫ x, ∫ u in Ioc 0 t, H (x, u) := by
        simp_rw [hGfv]; rw [integral_add hGcm hInt]
    _ = (∫ x, G x (c x)) + ∫ u in Ioc 0 t, ∫ x, H (x, u) := by
        rw [integral_integral_swap hHi]
    _ = (∫ x, G x (c x)) + ∫ u in Ioc 0 t, ∫ x, Gp x (heatT ε (ρ u) x) * Fo u x := by
        rw [setIntegral_congr_fun measurableSet_Ioc hrep]

end LinMild

end SharpLSI
