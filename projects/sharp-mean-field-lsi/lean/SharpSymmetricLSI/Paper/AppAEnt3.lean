import SharpSymmetricLSI.Paper.AppAEnt2

/-!
# The entropy (3): the time identity for the interaction at level `ε`

For a bounded measurable symmetric kernel `Wk` and `φ_u = e^{εΔ}ρ_u`:
`∬ Wk φ_t φ_t = ∬ Wk φ_0 φ_0 + 2 ∫_{(0,t]} ∬ Wk(x,y) (Δφ_u + ∇·e^{εΔ}N_u)(x) φ_u(y) du`
(`bilinear_eq`), from the product rule for absolutely continuous functions.
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace SharpLSI

/-- **Product rule** for `u ↦ cᵢ + ∫_a^u gᵢ`. -/
theorem product_rule_intervalIntegral {g₁ g₂ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg₁ : IntervalIntegrable g₁ volume a b) (hg₂ : IntervalIntegrable g₂ volume a b) (c₁ c₂ : ℝ) :
    (c₁ + ∫ v in a..b, g₁ v) * (c₂ + ∫ v in a..b, g₂ v) - c₁ * c₂ =
      ∫ u in a..b, (g₁ u * (c₂ + ∫ v in a..u, g₂ v) + (c₁ + ∫ v in a..u, g₁ v) * g₂ u) := by
  have hac : ∀ {g : ℝ → ℝ} (c : ℝ), IntervalIntegrable g volume a b →
      AbsolutelyContinuousOnInterval (fun u => c + ∫ v in a..u, g v) a b := fun {g} c hg => by
    have h := hg.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp [hab])
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
      (LipschitzWith.const (α := ℝ) c).lipschitzOnWith.absolutelyContinuousOnInterval
    exact hc.add h
  have hP := (hac c₁ hg₁).fun_mul (hac c₂ hg₂)
  have hint := hP.integral_deriv_eq_sub
  simp only [intervalIntegral.integral_same, add_zero] at hint
  rw [← hint]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hg₁.ae_hasDerivAt_integral, hg₂.ae_hasDerivAt_integral] with u hu₁ hu₂ hmem
  have hmem' : u ∈ uIcc a b := uIoc_subset_uIcc hmem
  have h1 := (hu₁ hmem' a (by simp [hab])).const_add c₁
  have h2 := (hu₂ hmem' a (by simp [hab])).const_add c₂
  exact (h1.mul h2).deriv

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem ae_fst_of_ae {f g : UnitAddTorus ι → ℝ} (hfg : f =ᵐ[volume] g) :
    (fun p : UnitAddTorus ι × UnitAddTorus ι => f p.1) =ᵐ[volume.prod volume] fun p => g p.1 :=
  Measure.QuasiMeasurePreserving.ae_eq (Measure.quasiMeasurePreserving_fst) hfg

theorem ae_snd_of_ae {f g : UnitAddTorus ι → ℝ} (hfg : f =ᵐ[volume] g) :
    (fun p : UnitAddTorus ι × UnitAddTorus ι => f p.2) =ᵐ[volume.prod volume] fun p => g p.2 :=
  Measure.QuasiMeasurePreserving.ae_eq (Measure.quasiMeasurePreserving_snd) hfg

theorem integrable_of_abs_le_finite {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hm : AEStronglyMeasurable f μ) {B : ℝ} (hb : ∀ p, |f p| ≤ B) :
    Integrable f μ :=
  (integrable_const B).mono' hm (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hb p)

namespace LinMild

variable {ρ₀ : UnitAddTorus ι → ℝ} {ρ : ℝ → UnitAddTorus ι → ℝ}
  {N : ℝ → UnitAddTorus ι → ι → ℝ} {A : ℝ} (h : LinMild ρ₀ ρ N A)
include h

/-- **The time identity for the interaction** at level `ε`. -/
theorem bilinear_eq {Wk : UnitAddTorus ι → UnitAddTorus ι → ℝ}
    (hWm : Measurable (Function.uncurry Wk)) {BW : ℝ} (hWb : ∀ x y, |Wk x y| ≤ BW)
    (hsym : ∀ x y, Wk x y = Wk y x)
    {ε : ℝ} (hε : 0 < ε) {T K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∫ p, Wk p.1 p.2 * (heatT ε (ρ t) p.1 * heatT ε (ρ t) p.2) ∂(volume.prod volume) =
      (∫ p, Wk p.1 p.2 * (heatT ε ρ₀ p.1 * heatT ε ρ₀ p.2) ∂(volume.prod volume)) +
      2 * ∫ u in Ioc 0 t, ∫ p, Wk p.1 p.2 *
        (forcing (ρ := ρ) (N := N) ε u p.1 * heatT ε (ρ u) p.2) ∂(volume.prod volume) := by
  have hT0 : 0 ≤ T := ht.1.trans ht.2
  obtain ⟨C, R, hC0, hR0, hFb, hfvm, hfvb, hφb⟩ := h.exists_version hε hK0 hK hT0
  set Fo := forcing (ρ := ρ) (N := N) ε with hFo
  have hFm : Measurable (Function.uncurry Fo) := h.measurable_forcing hε
  set c : UnitAddTorus ι → ℝ := heatT ε ρ₀ with hc
  set fv : ℝ → UnitAddTorus ι → ℝ := fun u x => c x + ∫ v in Ioc 0 u, Fo v x with hfv
  have hfvm' : Measurable (Function.uncurry fv) := hfvm
  have hBW0 : 0 ≤ BW := (abs_nonneg _).trans (hWb 0 0)
  have hcm : Measurable c := (measurable_heatT_joint h.meas0).comp measurable_prodMk_left
  have hcb : ∀ x, |c x| ≤ R := fun x => by simpa [hfv] using hfvb 0 ⟨le_rfl, hT0⟩ x
  have hWm2 : Measurable fun p : UnitAddTorus ι × UnitAddTorus ι => Wk p.1 p.2 := hWm
  -- (1) the product rule at each `(x, y)`
  have hgi : ∀ x, IntervalIntegrable (fun v => Fo v x) volume 0 t := fun x => by
    have hgm : Measurable fun v => Fo v x := hFm.comp (measurable_id.prodMk measurable_const)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1]
    haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) :=
      isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
    exact (integrable_const C).mono' hgm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv => by
        rw [Real.norm_eq_abs]; exact hFb v ⟨hv.1.le, hv.2.trans ht.2⟩ x))
  have hprod : ∀ x y, fv t x * fv t y - c x * c y =
      ∫ u in Ioc 0 t, (Fo u x * fv u y + fv u x * Fo u y) := by
    intro x y
    have := product_rule_intervalIntegral ht.1 (hgi x) (hgi y) (c x) (c y)
    rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1,
      intervalIntegral.integral_of_le ht.1] at this
    simp only [hfv]
    rw [this]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    rw [intervalIntegral.integral_of_le hu.1.le, intervalIntegral.integral_of_le hu.1.le]
  -- (2) Fubini
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  set H : (UnitAddTorus ι × UnitAddTorus ι) × ℝ → ℝ := fun q =>
    (Icc 0 t).indicator (fun u => Wk q.1.1 q.1.2 *
      (Fo u q.1.1 * fv u q.1.2 + fv u q.1.1 * Fo u q.1.2)) q.2 with hH
  have hHm : Measurable H := by
    have e : H = {q : (UnitAddTorus ι × UnitAddTorus ι) × ℝ | q.2 ∈ Icc 0 t}.indicator
        (fun q => Wk q.1.1 q.1.2 * (Fo q.2 q.1.1 * fv q.2 q.1.2 + fv q.2 q.1.1 * Fo q.2 q.1.2)) := by
      funext q; simp [hH, Set.indicator]
    rw [e]
    have m1 : Measurable fun q : (UnitAddTorus ι × UnitAddTorus ι) × ℝ => Fo q.2 q.1.1 :=
      hFm.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
    have m2 : Measurable fun q : (UnitAddTorus ι × UnitAddTorus ι) × ℝ => Fo q.2 q.1.2 :=
      hFm.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    have m3 : Measurable fun q : (UnitAddTorus ι × UnitAddTorus ι) × ℝ => fv q.2 q.1.1 :=
      hfvm'.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
    have m4 : Measurable fun q : (UnitAddTorus ι × UnitAddTorus ι) × ℝ => fv q.2 q.1.2 :=
      hfvm'.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    exact ((hWm2.comp measurable_fst).mul ((m1.mul m4).add (m3.mul m2))).indicator
      (measurableSet_Icc.preimage measurable_snd)
  have hHb : ∀ q, |H q| ≤ BW * (C * R + R * C) := fun q => by
    simp only [hH]
    by_cases hq : q.2 ∈ Icc 0 t
    · have hq' : q.2 ∈ Icc 0 T := ⟨hq.1, hq.2.trans ht.2⟩
      rw [indicator_of_mem hq, abs_mul]
      refine mul_le_mul (hWb _ _) ((abs_add_le _ _).trans (add_le_add ?_ ?_)) (abs_nonneg _) hBW0
      · rw [abs_mul]; exact mul_le_mul (hFb _ hq' _) (hfvb _ hq' _) (abs_nonneg _) hC0
      · rw [abs_mul]; exact mul_le_mul (hfvb _ hq' _) (hFb _ hq' _) (abs_nonneg _) hR0
    · rw [indicator_of_notMem hq, abs_zero]; positivity
  have hHi : Integrable H ((volume.prod volume).prod (volume.restrict (Ioc 0 t))) :=
    integrable_of_abs_le_finite hHm.aestronglyMeasurable hHb
  have hHp : ∀ p : UnitAddTorus ι × UnitAddTorus ι,
      Wk p.1 p.2 * (fv t p.1 * fv t p.2) = Wk p.1 p.2 * (c p.1 * c p.2) + ∫ u in Ioc 0 t, H (p, u) := by
    intro p
    have e : ∫ u in Ioc 0 t, H (p, u) =
        Wk p.1 p.2 * ∫ u in Ioc 0 t, (Fo u p.1 * fv u p.2 + fv u p.1 * Fo u p.2) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      simp only [hH, indicator_of_mem (Ioc_subset_Icc_self hu)]
    rw [e, ← hprod]; ring
  -- (3) per time: replacement and symmetry
  have hrep : ∀ u ∈ Ioc 0 t, ∫ p, H (p, u) ∂(volume.prod volume) =
      2 * ∫ p, Wk p.1 p.2 * (Fo u p.1 * heatT ε (ρ u) p.2) ∂(volume.prod volume) := by
    intro u hu
    have hu' : u ∈ Icc 0 T := ⟨hu.1.le, hu.2.trans ht.2⟩
    have hid := h.heat_time_identity hε hK0 hK hu'
    set φ := heatT ε (ρ u)
    have hφm : Measurable φ := (measurable_heatT_family h.meas).comp measurable_prodMk_left
    have hFum : Measurable (Fo u) := hFm.comp measurable_prodMk_left
    have hi1 : Integrable (fun p : UnitAddTorus ι × UnitAddTorus ι => Wk p.1 p.2 * (Fo u p.1 * φ p.2))
        (volume.prod volume) :=
      integrable_of_abs_le_finite (hWm2.mul ((hFum.comp measurable_fst).mul
        (hφm.comp measurable_snd))).aestronglyMeasurable (B := BW * (C * R)) fun p => by
        rw [abs_mul, abs_mul]
        exact mul_le_mul (hWb _ _) (mul_le_mul (hFb _ hu' _) (hφb _ hu' _) (abs_nonneg _) hC0)
          (by positivity) hBW0
    have hi2 : Integrable (fun p : UnitAddTorus ι × UnitAddTorus ι => Wk p.1 p.2 * (φ p.1 * Fo u p.2))
        (volume.prod volume) :=
      integrable_of_abs_le_finite (hWm2.mul ((hφm.comp measurable_fst).mul
        (hFum.comp measurable_snd))).aestronglyMeasurable (B := BW * (R * C)) fun p => by
        rw [abs_mul, abs_mul]
        exact mul_le_mul (hWb _ _) (mul_le_mul (hφb _ hu' _) (hFb _ hu' _) (abs_nonneg _) hR0)
          (by positivity) hBW0
    have hae : (fun p : UnitAddTorus ι × UnitAddTorus ι => H (p, u)) =ᵐ[volume.prod volume]
        fun p => Wk p.1 p.2 * (Fo u p.1 * φ p.2) + Wk p.1 p.2 * (φ p.1 * Fo u p.2) := by
      filter_upwards [ae_fst_of_ae hid, ae_snd_of_ae hid] with p h1 h2
      simp only [hH, indicator_of_mem (Ioc_subset_Icc_self hu)]
      simp only [hfv] at h1 h2 ⊢
      rw [← h1, ← h2]; ring
    rw [integral_congr_ae hae, integral_add hi1 hi2]
    have hsw : ∫ p, Wk p.1 p.2 * (φ p.1 * Fo u p.2) ∂(volume.prod volume) =
        ∫ p, Wk p.1 p.2 * (Fo u p.1 * φ p.2) ∂(volume.prod volume) := by
      rw [← integral_prod_swap]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      simp only [Prod.fst_swap, Prod.snd_swap]
      rw [hsym]; ring
    rw [hsw]; ring
  -- (4) assemble
  have hφt := h.heat_time_identity hε hK0 hK ht
  have hcc : Integrable (fun p : UnitAddTorus ι × UnitAddTorus ι => Wk p.1 p.2 * (c p.1 * c p.2))
      (volume.prod volume) :=
    integrable_of_abs_le_finite (hWm2.mul ((hcm.comp measurable_fst).mul
      (hcm.comp measurable_snd))).aestronglyMeasurable (B := BW * (R * R)) fun p => by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (hWb _ _) (mul_le_mul (hcb _) (hcb _) (abs_nonneg _) hR0) (by positivity) hBW0
  have hInt := hHi.integral_prod_left
  calc ∫ p, Wk p.1 p.2 * (heatT ε (ρ t) p.1 * heatT ε (ρ t) p.2) ∂(volume.prod volume)
      = ∫ p, Wk p.1 p.2 * (fv t p.1 * fv t p.2) ∂(volume.prod volume) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_fst_of_ae hφt, ae_snd_of_ae hφt] with p h1 h2
        simp only [hfv]; rw [h1, h2]
    _ = (∫ p, Wk p.1 p.2 * (c p.1 * c p.2) ∂(volume.prod volume)) +
          ∫ p, (∫ u in Ioc 0 t, H (p, u)) ∂(volume.prod volume) := by
        simp_rw [hHp]; rw [integral_add hcc hInt]
    _ = (∫ p, Wk p.1 p.2 * (c p.1 * c p.2) ∂(volume.prod volume)) +
          ∫ u in Ioc 0 t, ∫ p, H (p, u) ∂(volume.prod volume) := by
        rw [integral_integral_swap hHi]
    _ = _ := by
        rw [setIntegral_congr_fun measurableSet_Ioc hrep, integral_const_mul]

end LinMild

end SharpLSI
