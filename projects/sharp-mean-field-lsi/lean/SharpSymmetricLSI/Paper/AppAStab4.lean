import SharpSymmetricLSI.Paper.AppAStab3

/-!
# Lemma A.1: the Duhamel term in `L¹`

For mild solutions `ρ, η` and `t > 0`:
`‖ρ_t - η_t‖₁ ≤ ‖ρ₀ - η₀‖₁ + ∫₀ᵗ c (t-u)^{-1/2} (B_V + 2B_W) |ι| ‖ρ_u - η_u‖₁ du`
(`mild_diff_le`). The Duhamel integrand is measurable in `x` for each `u`, continuous in `u`,
hence jointly measurable (Carathéodory), and integrable in `u` with the `(t-u)^{-1/2}` bound.
-/

open MeasureTheory Set Filter Topology
open scoped Real ContDiff ENNReal

namespace SharpLSI

section Kernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem divConst_eq {s : ℝ} (hs : 0 < s) :
    divConst s = 2 * (4 * π) ^ (-(1 : ℝ) / 2) * s ^ (-(1 : ℝ) / 2) := by
  unfold divConst
  rw [Real.mul_rpow (by positivity) hs.le]
  field_simp
  ring

theorem integrableOn_divConst {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun u => divConst (t - u)) (Ioc 0 t) := by
  have h1 : IntervalIntegrable (fun x : ℝ => x ^ (-(1 : ℝ) / 2)) volume t 0 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h2 := h1.comp_sub_left t (by simp)
  simp only [sub_self, sub_zero] at h2
  have h3 := (h2.const_mul (2 * (4 * π) ^ (-(1 : ℝ) / 2)))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le] at h3
  refine h3.congr_fun (fun u hu => ?_) measurableSet_Ioc
  by_cases hut : u < t
  · rw [divConst_eq (sub_pos.2 hut)]
  · have : u = t := le_antisymm hu.2 (not_lt.1 hut)
    subst this
    simp [divConst]

theorem measurable_fderiv_heatKernel {s : ℝ} (hs : 0 < s) (k : ι) :
    Measurable fun y : ι → ℝ => fderiv ℝ (heatKernel s) y (Pi.single k 1) := by
  simp_rw [fderiv_heatKernel_single hs]
  exact ((measurable_heatKernel s).mul (measurable_pi_apply k)).div_const _ |>.neg

theorem divHeatT_congr_ae {s : ℝ} {F G : UnitAddTorus ι → ι → ℝ}
    (h : ∀ k, (fun z => F z k) =ᵐ[volume] fun z => G z k) : divHeatT s F = divHeatT s G := by
  funext x
  unfold divHeatT
  refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
  filter_upwards [(qmp_sub_liftT x).ae (h k)] with y hy
  rw [hy]

/-- `x ↦ ∇·e^{sΔ}F (x)` is measurable. -/
theorem measurable_divHeatT {s : ℝ} (hs : 0 < s) {F : UnitAddTorus ι → ι → ℝ}
    (hF : ∀ k, AEStronglyMeasurable (fun z => F z k) volume) : Measurable (divHeatT s F) := by
  set G : UnitAddTorus ι → ι → ℝ := fun z k => (hF k).mk _ z
  rw [divHeatT_congr_ae (G := G) fun k => (hF k).ae_eq_mk]
  unfold divHeatT
  refine Finset.measurable_sum _ fun k _ => ?_
  have hm : StronglyMeasurable (fun p : UnitAddTorus ι × (ι → ℝ) =>
      fderiv ℝ (heatKernel s) p.2 (Pi.single k 1) * G (p.1 - liftT p.2) k) :=
    (((measurable_fderiv_heatKernel hs k).comp measurable_snd).mul
      ((hF k).stronglyMeasurable_mk.measurable.comp
        (measurable_fst.sub (measurable_liftT.comp measurable_snd)))).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

/-- Linearity of `∇·e^{sΔ}` for bounded fields. -/
theorem divHeatT_sub {s : ℝ} (hs : 0 < s) {F G : UnitAddTorus ι → ι → ℝ} {M : ℝ}
    (hFm : ∀ k, AEStronglyMeasurable (fun z => F z k) volume)
    (hGm : ∀ k, AEStronglyMeasurable (fun z => G z k) volume)
    (hF : ∀ k, ∀ᵐ z, |F z k| ≤ M) (hG : ∀ k, ∀ᵐ z, |G z k| ≤ M) (x : UnitAddTorus ι) :
    divHeatT s (fun z k => F z k - G z k) x = divHeatT s F x - divHeatT s G x := by
  unfold divHeatT
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hint : ∀ H : UnitAddTorus ι → ι → ℝ, AEStronglyMeasurable (fun z => H z k) volume →
      (∀ᵐ z, |H z k| ≤ M) →
      Integrable fun y : ι → ℝ => fderiv ℝ (heatKernel s) y (Pi.single k 1) * H (x - liftT y) k := by
    intro H hm hb
    refine Integrable.mono' ((integrable_fderiv_heatKernel hs k).abs.mul_const M)
      ((measurable_fderiv_heatKernel hs k).aestronglyMeasurable.mul
        (hm.comp_quasiMeasurePreserving (qmp_sub_liftT x))) ?_
    filter_upwards [(qmp_sub_liftT x).ae hb] with y hy
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
  rw [← integral_sub (hint F (hFm k) (hF k)) (hint G (hGm k) (hG k))]
  congr 1; funext y; ring

end Kernel

section Mild

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem isFiniteMeasure_comap_Ioo (t : ℝ) :
    IsFiniteMeasure ((volume : Measure ℝ).comap (Subtype.val : Ioo (0 : ℝ) t → ℝ)) := by
  refine ⟨?_⟩
  rw [Measure.comap_apply _ Subtype.val_injective
    (fun s hs => measurableSet_Ioo.subtype_image hs) _ MeasurableSet.univ,
    image_univ, Subtype.range_coe]
  exact measure_Ioo_lt_top

theorem heatT_sub' {t : ℝ} (ht : 0 < t) {f g : Torus d → ℝ} (hf : Integrable f (haar d))
    (hg : Integrable g (haar d)) (x : Torus d) :
    heatT t f x - heatT t g x = heatT t (fun y => f y - g y) x := by
  rw [heatT_eq ht hf.aestronglyMeasurable, heatT_eq ht hg.aestronglyMeasurable,
    heatT_eq ht (f := fun y => f y - g y) (hf.sub hg).aestronglyMeasurable]
  refine (integral_sub (integrable_heatP_mul_sub ht hf x)
    (integrable_heatP_mul_sub ht hg x)).symm.trans ?_
  congr 1; funext z; ring

theorem lintegral_heatT_le {t : ℝ} (ht : 0 < t) {f : Torus d → ℝ} (hf : Integrable f (haar d)) :
    ∫⁻ x, ‖heatT t f x‖ₑ ∂haar d ≤ ∫⁻ x, ‖f x‖ₑ ∂haar d := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_heatT ht hf),
    ← ofReal_integral_norm_eq_lintegral_enorm hf]
  refine ENNReal.ofReal_le_ofReal ?_
  simp_rw [Real.norm_eq_abs]
  exact integral_abs_heatT_le ht hf

/-- **The Duhamel term in `L¹`.** -/
theorem mild_diff_le (hyp : Hyp V W KV KW) {BV BW : ℝ} (hBV0 : 0 ≤ BV) (hBW0 : 0 ≤ BW)
    (hBV : ∀ᵐ x ∂haar d, ∀ k, |weakGrad V x k| ≤ BV)
    (hBW : ∀ᵐ p ∂(haar d).prod (haar d), ∀ k, |bGrad W p.1 p.2 k| ≤ BW)
    {ρ₀ η₀ : Torus d → ℝ} {ρ η : ℝ → Torus d → ℝ} (hρ : AppAMild V W ρ₀ ρ)
    (hη : AppAMild V W η₀ η) {t : ℝ} (ht : 0 < t) :
    ∫⁻ x, ‖ρ t x - η t x‖ₑ ∂haar d ≤ ∫⁻ x, ‖ρ₀ x - η₀ x‖ₑ ∂haar d +
      ∫⁻ u in Ioo 0 t, ENNReal.ofReal (divConst (t - u)) *
        (∑ _k : Fin d, ENNReal.ofReal (BV + 2 * BW) * ∫⁻ x, ‖ρ u x - η u x‖ₑ ∂haar d) := by
  obtain ⟨Bρ, hBρ⟩ := hρ.bdd t
  obtain ⟨Bη, hBη⟩ := hη.bdd t
  set M := max Bρ Bη * (BV + BW) with hM
  have hρ0 : IsProbDens ρ₀ := by rw [← hρ.init]; exact hρ.probDens le_rfl
  have hη0 : IsProbDens η₀ := by rw [← hη.init]; exact hη.probDens le_rfl
  -- fluxes
  set Fρ : ℝ → Torus d → Fin d → ℝ := fun u => appAFlux V W (ρ u)
  set Fη : ℝ → Torus d → Fin d → ℝ := fun u => appAFlux V W (η u)
  have hFm : ∀ {ζ : ℝ → Torus d → ℝ} {ζ₀}, AppAMild V W ζ₀ ζ → ∀ u, 0 ≤ u → ∀ k,
      AEStronglyMeasurable (fun z => appAFlux V W (ζ u) z k) (haar d) :=
    fun h u hu k => aestronglyMeasurable_appAFlux hyp (h.probDens hu).int k
  have hFbρ : ∀ u ∈ Ioo 0 t, ∀ k, ∀ᵐ z ∂haar d, |Fρ u z k| ≤ M := by
    intro u hu k
    filter_upwards [abs_appAFlux_le hyp hBV hBW (hρ.probDens hu.1.le)
      (hBρ u ⟨hu.1.le, hu.2.le⟩)] with z hz
    exact (hz k).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  have hFbη : ∀ u ∈ Ioo 0 t, ∀ k, ∀ᵐ z ∂haar d, |Fη u z k| ≤ M := by
    intro u hu k
    filter_upwards [abs_appAFlux_le hyp hBV hBW (hη.probDens hu.1.le)
      (hBη u ⟨hu.1.le, hu.2.le⟩)] with z hz
    exact (hz k).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))
  -- the Duhamel integrands
  set φρ : ℝ → Torus d → ℝ := fun u x => divHeatT (t - u) (Fρ u) x
  set φη : ℝ → Torus d → ℝ := fun u x => divHeatT (t - u) (Fη u) x
  set D : ℝ → Torus d → ℝ := fun u x =>
    divHeatT (t - u) (fun z k => Fρ u z k - Fη u z k) x
  have hD : ∀ u ∈ Ioo 0 t, ∀ x, D u x = φρ u x - φη u x := fun u hu x =>
    divHeatT_sub (sub_pos.2 hu.2) (hFm hρ u hu.1.le) (hFm hη u hu.1.le) (hFbρ u hu) (hFbη u hu) x
  have hint : ∀ {ζ : ℝ → Torus d → ℝ} {ζ₀}, AppAMild V W ζ₀ ζ →
      (∀ u ∈ Ioo 0 t, ∀ k, ∀ᵐ z ∂haar d, |appAFlux V W (ζ u) z k| ≤ M) → ∀ x,
      IntegrableOn (fun u => divHeatT (t - u) (appAFlux V W (ζ u)) x) (Ioc 0 t) := by
    intro ζ ζ₀ h hb x
    have hcont := continuousOn_duhamel hyp hBV0 hBW0 hBV hBW h ht x
    have hmeas : AEStronglyMeasurable (fun u => divHeatT (t - u) (appAFlux V W (ζ u)) x)
        (volume.restrict (Ioc 0 t)) := by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
      exact hcont.aestronglyMeasurable measurableSet_Ioo
    refine Integrable.mono' (((integrableOn_divConst ht).const_mul (Fintype.card (Fin d) : ℝ)).mul_const M)
      hmeas ?_
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [Real.norm_eq_abs]
    exact abs_divHeatT_le (sub_pos.2 hu.2) (hb u hu) x
  -- the pointwise identity
  have hid : ∀ᵐ x ∂haar d, ρ t x - η t x =
      heatT t (fun y => ρ₀ y - η₀ y) x + ∫ u in Ioc 0 t, D u x := by
    filter_upwards [hρ.mild t ht, hη.mild t ht] with x h1 h2
    rw [h1, h2, ← heatT_sub' ht hρ0.int hη0.int x]
    have e : ∫ u in Ioc 0 t, D u x = ∫ u in Ioc 0 t, (φρ u x - φη u x) := by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
      exact setIntegral_congr_fun measurableSet_Ioo fun u hu => hD u hu x
    rw [e, integral_sub (hint hρ hFbρ x) (hint hη hFbη x)]
    unfold appAFlux
    ring
  -- joint measurability on `(0,t) × 𝕋^d`
  have hfin := isFiniteMeasure_comap_Ioo t
  set μS : Measure (Ioo (0 : ℝ) t) := (volume : Measure ℝ).comap Subtype.val with hμS
  have hDcont : ∀ x, Continuous fun u : Ioo (0 : ℝ) t => D u x := by
    intro x
    have h1 := continuousOn_duhamel hyp hBV0 hBW0 hBV hBW hρ ht x
    have h2 := continuousOn_duhamel hyp hBV0 hBW0 hBV hBW hη ht x
    have h3 : ContinuousOn (fun u => D u x) (Ioo 0 t) :=
      (h1.sub h2).congr fun u hu => hD u hu x
    exact continuousOn_iff_continuous_domRestrict.1 h3
  have hDmeas : ∀ u : Ioo (0 : ℝ) t, Measurable fun x => D u x := fun u =>
    measurable_divHeatT (sub_pos.2 u.2.2)
      (fun k => (hFm hρ u u.2.1.le k).sub (hFm hη u u.2.1.le k))
  have hjoint : Measurable (Function.uncurry fun (u : Ioo (0 : ℝ) t) (x : Torus d) => D u x) :=
    measurable_uncurry_of_continuous_of_measurable hDcont hDmeas
  have hsub : ∀ x, ∫⁻ u in Ioc 0 t, ‖D u x‖ₑ = ∫⁻ u : Ioo (0 : ℝ) t, ‖D u x‖ₑ ∂μS := by
    intro x
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc,
      lintegral_subtype_comap measurableSet_Ioo (fun u => ‖D u x‖ₑ)]
  have hper : ∀ u : Ioo (0 : ℝ) t, ∫⁻ x, ‖D u x‖ₑ ∂haar d ≤
      ENNReal.ofReal (divConst (t - u)) *
        (∑ _k : Fin d, ENNReal.ofReal (BV + 2 * BW) * ∫⁻ x, ‖ρ u x - η u x‖ₑ ∂haar d) := by
    intro u
    refine (lintegral_divHeatT_le (sub_pos.2 u.2.2)
      (fun k => (hFm hρ u u.2.1.le k).sub (hFm hη u u.2.1.le k))).trans ?_
    gcongr with k
    exact lintegral_appAFlux_sub_le hyp hBV0 hBW0 hBV hBW (hρ.probDens u.2.1.le)
      (hη.probDens u.2.1.le) k
  have hHm : AEMeasurable (fun x => ‖heatT t (fun y => ρ₀ y - η₀ y) x‖ₑ) (haar d) :=
    (integrable_heatT ht (hρ0.int.sub hη0.int)).aestronglyMeasurable.enorm
  calc ∫⁻ x, ‖ρ t x - η t x‖ₑ ∂haar d
      = ∫⁻ x, ‖heatT t (fun y => ρ₀ y - η₀ y) x + ∫ u in Ioc 0 t, D u x‖ₑ ∂haar d :=
        lintegral_congr_ae (hid.mono fun x hx => by
          show ‖ρ t x - η t x‖ₑ = _
          rw [hx])
    _ ≤ ∫⁻ x, (‖heatT t (fun y => ρ₀ y - η₀ y) x‖ₑ + ∫⁻ u in Ioc 0 t, ‖D u x‖ₑ) ∂haar d :=
        lintegral_mono fun x => (enorm_add_le _ _).trans
          (add_le_add le_rfl (enorm_integral_le_lintegral_enorm _))
    _ = ∫⁻ x, ‖heatT t (fun y => ρ₀ y - η₀ y) x‖ₑ ∂haar d +
          ∫⁻ x, ∫⁻ u : Ioo (0 : ℝ) t, ‖D u x‖ₑ ∂μS ∂haar d := by
        rw [lintegral_add_left' hHm]
        simp_rw [hsub]
    _ = ∫⁻ x, ‖heatT t (fun y => ρ₀ y - η₀ y) x‖ₑ ∂haar d +
          ∫⁻ u : Ioo (0 : ℝ) t, ∫⁻ x, ‖D u x‖ₑ ∂haar d ∂μS := by
        have hj2 : AEMeasurable (Function.uncurry fun (x : Torus d) (u : Ioo (0 : ℝ) t) =>
            ‖D u x‖ₑ) ((haar d).prod μS) := ((hjoint.comp measurable_swap).enorm).aemeasurable
        rw [lintegral_lintegral_swap hj2]
    _ ≤ ∫⁻ x, ‖ρ₀ x - η₀ x‖ₑ ∂haar d +
          ∫⁻ u : Ioo (0 : ℝ) t, ENNReal.ofReal (divConst (t - u)) *
            (∑ _k : Fin d, ENNReal.ofReal (BV + 2 * BW) * ∫⁻ x, ‖ρ u x - η u x‖ₑ ∂haar d) ∂μS :=
        add_le_add (lintegral_heatT_le ht (hρ0.int.sub hη0.int)) (lintegral_mono hper)
    _ = _ := by
        rw [lintegral_subtype_comap measurableSet_Ioo (fun u => ENNReal.ofReal (divConst (t - u)) *
          (∑ _k : Fin d, ENNReal.ofReal (BV + 2 * BW) * ∫⁻ x, ‖ρ u x - η u x‖ₑ ∂haar d))]

end Mild

end SharpLSI
