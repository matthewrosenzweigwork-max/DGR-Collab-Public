import SharpSymmetricLSI.Paper.AppAPos6

/-!
# Positivity (7): the energy inequality at level `ε`

`∫ G(e^{εΔ}ρ_t) ≤ ∫ G(e^{εΔ}ρ₀) + ∫_{(0,t]} ∫ G''(e^{εΔ}ρ_u) |e^{εΔ}N_u|²/4 du`
(`LinMild.energy_ineq`), in time-integrated form: the chain rule is applied, for each `x`, to the
absolutely continuous version `c(x) + ∫_{(0,u]} forcing`, which equals `e^{εΔ}ρ_u` a.e. for each `u`.
-/

open MeasureTheory Set Filter Topology Complex UnitAddTorus
open scoped Real ENNReal ContDiff

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace LinMild

variable {ρ₀ : UnitAddTorus ι → ℝ} {ρ : ℝ → UnitAddTorus ι → ℝ}
  {N : ℝ → UnitAddTorus ι → ι → ℝ} {A : ℝ} (h : LinMild ρ₀ ρ N A)
include h

theorem measurable_setIntegral_family {F : ℝ → UnitAddTorus ι → ℝ}
    (hF : Measurable (Function.uncurry F)) :
    Measurable fun p : ℝ × UnitAddTorus ι => ∫ v in Ioc 0 p.1, F v p.2 := by
  have e : (fun p : ℝ × UnitAddTorus ι => ∫ v in Ioc 0 p.1, F v p.2) =
      fun p => ∫ v, {q : (ℝ × UnitAddTorus ι) × ℝ | q.2 ∈ Ioc 0 q.1.1}.indicator
        (fun q => F q.2 q.1.2) (p, v) := by
    funext p
    rw [← integral_indicator measurableSet_Ioc]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [Set.indicator, mem_setOf_eq]
  rw [e]
  refine Measurable.stronglyMeasurable ?_ |>.integral_prod_right' |>.measurable
  refine (hF.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).indicator ?_
  exact (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd (measurable_fst.comp measurable_fst))

/-- **The energy inequality** for `ρ^ε`. -/
theorem energy_ineq {G Gp Gpp : ℝ → ℝ} (hG : ∀ r, HasDerivAt G (Gp r) r)
    (hGp : ∀ r, HasDerivAt Gp (Gpp r) r) (hGpp : Continuous Gpp) (hGpp0 : ∀ r, 0 ≤ Gpp r)
    {ε : ℝ} (hε : 0 < ε) {T K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∫ x, G (heatT ε (ρ t) x) ≤ (∫ x, G (heatT ε ρ₀ x)) +
      ∫ u in Ioc 0 t, ∫ x, Gpp (heatT ε (ρ u) x) * (∑ j, (heatT ε (fun z => N u z j) x) ^ 2) / 4 := by
  have hT0 : 0 ≤ T := ht.1.trans ht.2
  have hρ₀b : ∀ x, |ρ₀ x| ≤ K := fun x => by rw [← h.init]; exact hK 0 ⟨le_rfl, hT0⟩ x
  set Fo := forcing (ρ := ρ) (N := N) ε with hFo
  set C := (∫ y, |lapKer (ι := ι) ε y|) * K + Fintype.card ι * divConst ε * (A * K) with hC
  have hC0 : 0 ≤ C := by
    have := h.abs_forcing_le hε hK ⟨le_rfl, hT0⟩ (0 : UnitAddTorus ι)
    exact (abs_nonneg _).trans this
  have hFb : ∀ v ∈ Icc 0 T, ∀ x, |Fo v x| ≤ C := fun v hv x => h.abs_forcing_le hε hK hv x
  have hFm : Measurable (Function.uncurry Fo) := h.measurable_forcing hε
  set c : UnitAddTorus ι → ℝ := heatT ε ρ₀ with hc
  have hcm : Measurable c := (measurable_heatT_joint h.meas0).comp measurable_prodMk_left
  have hcb : ∀ x, |c x| ≤ K := fun x =>
    abs_heatT_le hε h.meas0.aestronglyMeasurable (Eventually.of_forall hρ₀b) x
  set fv : ℝ → UnitAddTorus ι → ℝ := fun u x => c x + ∫ v in Ioc 0 u, Fo v x with hfv
  have hfvm : Measurable (Function.uncurry fv) :=
    (hcm.comp measurable_snd).add (measurable_setIntegral_family h hFm)
  have hIb : ∀ u ∈ Icc 0 t, ∀ x, |∫ v in Ioc 0 u, Fo v x| ≤ C * T := fun u hu x => by
    rw [← Real.norm_eq_abs]
    refine (norm_setIntegral_le_of_norm_le_const (C := C) measure_Ioc_lt_top
      fun v hv => by
        rw [Real.norm_eq_abs]
        exact hFb v ⟨hv.1.le, hv.2.trans (hu.2.trans ht.2)⟩ x).trans ?_
    simp only [Real.volume_real_Ioc, sub_zero, max_eq_left hu.1]
    exact mul_le_mul_of_nonneg_left (hu.2.trans ht.2) hC0
  set R := K + C * T
  have hfvb : ∀ u ∈ Icc 0 t, ∀ x, |fv u x| ≤ R := fun u hu x =>
    (abs_add_le _ _).trans (add_le_add (hcb x) (hIb u hu x))
  have hGpc : Continuous Gp := continuous_iff_continuousAt.2 fun r => (hGp r).continuousAt
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun r => (hG r).continuousAt
  obtain ⟨MGp, hMGp0, hMGp⟩ := exists_bound_on_Icc hGpc R
  obtain ⟨MG, hMG0, hMG⟩ := exists_bound_on_Icc hGc R
  obtain ⟨MGpp, hMGpp0, hMGpp⟩ := exists_bound_on_Icc hGpp R
  -- (1) the chain rule at each `x`
  have hchain : ∀ x, G (fv t x) - G (c x) = ∫ u in Ioc 0 t, Gp (fv u x) * Fo u x := by
    intro x
    have hgm : Measurable fun v => Fo v x := hFm.comp (measurable_id.prodMk measurable_const)
    have hgi : IntervalIntegrable (fun v => Fo v x) volume 0 t := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1]
      haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) :=
        isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
      exact (integrable_const C).mono' hgm.aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv => by
          rw [Real.norm_eq_abs]; exact hFb v ⟨hv.1.le, hv.2.trans ht.2⟩ x))
    have := chain_rule_intervalIntegral ht.1 hgi hG hGpc (c x)
    rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1] at this
    simp only [hfv]
    rw [this]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    rw [intervalIntegral.integral_of_le hu.1.le]
  -- (2) Fubini
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  set H : UnitAddTorus ι × ℝ → ℝ := fun p =>
    (Icc 0 t).indicator (fun u => Gp (fv u p.1) * Fo u p.1) p.2 with hH
  have hHm : Measurable H := by
    have e : H = {p : UnitAddTorus ι × ℝ | p.2 ∈ Icc 0 t}.indicator
        (fun p => Gp (fv p.2 p.1) * Fo p.2 p.1) := by
      funext p; simp [hH, Set.indicator]
    rw [e]
    exact ((hGpc.measurable.comp (hfvm.comp (measurable_snd.prodMk measurable_fst))).mul
      (hFm.comp (measurable_snd.prodMk measurable_fst))).indicator
      (measurableSet_Icc.preimage measurable_snd)
  have hHb : ∀ p, |H p| ≤ MGp * C := fun p => by
    simp only [hH]
    by_cases hp : p.2 ∈ Icc 0 t
    · rw [indicator_of_mem hp, abs_mul]
      exact mul_le_mul (hMGp _ (hfvb p.2 hp p.1)) (hFb p.2 ⟨hp.1, hp.2.trans ht.2⟩ p.1)
        (abs_nonneg _) hMGp0
    · rw [indicator_of_notMem hp, abs_zero]; positivity
  have hHi : Integrable H (volume.prod (volume.restrict (Ioc 0 t))) :=
    (integrable_const (MGp * C)).mono' hHm.aestronglyMeasurable
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hHb p)
  have hHx : ∀ x, ∫ u in Ioc 0 t, Gp (fv u x) * Fo u x = ∫ u in Ioc 0 t, H (x, u) := fun x =>
    setIntegral_congr_fun measurableSet_Ioc fun u hu => by
      simp only [hH, indicator_of_mem (Ioc_subset_Icc_self hu)]
  -- (3) the replacement `fv u = e^{εΔ}ρ_u` a.e.
  have hrep : ∀ u ∈ Ioc 0 t, ∫ x, H (x, u) = ∫ x, Gp (heatT ε (ρ u) x) * Fo u x := by
    intro u hu
    have hid := h.heat_time_identity hε hK0 hK ⟨hu.1.le, hu.2.trans ht.2⟩
    refine integral_congr_ae ?_
    filter_upwards [hid] with x hx
    simp only [hH, indicator_of_mem (Ioc_subset_Icc_self hu)]
    rw [hx]
  -- (4) the rate bound
  set B := max K (A * K)
  have hrate : ∀ u ∈ Ioc 0 t, ∫ x, Gp (heatT ε (ρ u) x) * Fo u x ≤
      ∫ x, Gpp (heatT ε (ρ u) x) * (∑ j, (heatT ε (fun z => N u z j) x) ^ 2) / 4 := by
    intro u hu
    have hu' : u ∈ Icc 0 T := ⟨hu.1.le, hu.2.trans ht.2⟩
    exact energy_rate_le hGp hGpp hGpp0 hε (h.measurable_section u) (fun k => h.measurable_sectionN u k)
      (fun x => (hK u hu' x).trans (le_max_left _ _))
      (fun z k => (h.abs_N_le hK hu' z k).trans (le_max_right _ _))
  -- (5) assemble
  have hφt := h.heat_time_identity hε hK0 hK ht
  have hGfv : ∀ x, G (fv t x) = G (c x) + ∫ u in Ioc 0 t, H (x, u) := fun x => by
    rw [← hHx]; linarith [hchain x]
  have hGcm : Integrable fun x => G (c x) :=
    appA_integrable_of_abs_le' (hGc.measurable.comp hcm) fun x => hMG _ ((hcb x).trans (by
      have : 0 ≤ C * T := mul_nonneg hC0 hT0
      simp only [R]; linarith))
  have hInt := hHi.integral_prod_left
  calc ∫ x, G (heatT ε (ρ t) x) = ∫ x, G (fv t x) := by
        refine integral_congr_ae ?_
        filter_upwards [hφt] with x hx
        rw [hx]
    _ = (∫ x, G (c x)) + ∫ x, ∫ u in Ioc 0 t, H (x, u) := by
        simp_rw [hGfv]; rw [integral_add hGcm hInt]
    _ = (∫ x, G (c x)) + ∫ u in Ioc 0 t, ∫ x, H (x, u) := by
        rw [integral_integral_swap hHi]
    _ ≤ (∫ x, G (c x)) + ∫ u in Ioc 0 t,
          ∫ x, Gpp (heatT ε (ρ u) x) * (∑ j, (heatT ε (fun z => N u z j) x) ^ 2) / 4 := by
        refine add_le_add le_rfl (setIntegral_mono_on hHi.integral_prod_right ?_ measurableSet_Ioc
          fun u hu => ?_)
        · have hJm : Measurable fun p : ℝ × UnitAddTorus ι => Gpp (heatT ε (ρ p.1) p.2) *
              (∑ j, (heatT ε (fun z => N p.1 z j) p.2) ^ 2) / 4 :=
            ((hGpp.measurable.comp (measurable_heatT_family h.meas)).mul
              (Finset.measurable_sum _ fun j _ => (measurable_heatT_family (ρ := fun u z => N u z j)
                (h.measN j)).pow_const 2)).div_const 4
          set Mb := MGpp * (Fintype.card ι * (A * K) ^ 2) / 4
          refine (integrable_const Mb).mono' hJm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
            ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_))
          have hu' : u ∈ Icc 0 T := ⟨hu.1.le, hu.2.trans ht.2⟩
          rw [Real.norm_eq_abs]
          refine (abs_integral_le_integral_abs).trans ?_
          refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
            (integrable_const Mb) (Eventually.of_forall fun x => ?_)).trans (by simp)
          have hφb : |heatT ε (ρ u) x| ≤ R := (abs_heatT_le hε (h.measurable_section u).aestronglyMeasurable
            (Eventually.of_forall (hK u hu')) x).trans (by
              have : 0 ≤ C * T := mul_nonneg hC0 hT0
              simp only [R]; linarith)
          have hψb : ∀ j, (heatT ε (fun z => N u z j) x) ^ 2 ≤ (A * K) ^ 2 := fun j => by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (abs_heatT_le hε (h.measurable_sectionN u j).aestronglyMeasurable
              (Eventually.of_forall fun z => h.abs_N_le hK hu' z j) x) 2
          have hs : ∑ j, (heatT ε (fun z => N u z j) x) ^ 2 ≤ Fintype.card ι * (A * K) ^ 2 := by
            calc ∑ j, (heatT ε (fun z => N u z j) x) ^ 2 ≤ ∑ _j : ι, (A * K) ^ 2 :=
                  Finset.sum_le_sum fun j _ => hψb j
              _ = _ := by simp
          have hs0 : 0 ≤ ∑ j, (heatT ε (fun z => N u z j) x) ^ 2 :=
            Finset.sum_nonneg fun j _ => sq_nonneg _
          show |Gpp (heatT ε (ρ u) x) * (∑ j, (heatT ε (fun z => N u z j) x) ^ 2) / 4| ≤ Mb
          rw [abs_div, abs_mul, abs_of_nonneg hs0, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
          simp only [Mb]
          gcongr
          · exact hMGpp _ hφb
        · rw [hrep u hu]; exact hrate u hu

end LinMild

end SharpLSI
