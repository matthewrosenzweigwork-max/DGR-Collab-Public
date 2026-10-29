import DGPS.Lipschitz.HeatSemigroupL2
import DGPS.Lipschitz.MeanFieldNonlinearity

/-!
# Mean-field local flow: the fixed point (LIP025c)

`L∞` bounds for the Duhamel integral and the heat flow, closedness of the a.e.-bounded ball in
`L²`, and Banach's fixed point theorem on the sup-metric space `C([0,T]; L²)`, giving
`DGPS.Lipschitz.modified_mean_field_mild_contraction`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DGPS.Lipschitz

variable {d : ℕ}

/-! ### A.e. bounds from `L∞` norms -/

theorem ae_norm_le_of_eLpNorm_top_le {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {f : α → E} {C : ℝ} (hC : 0 ≤ C)
    (h : eLpNorm f ⊤ μ ≤ ENNReal.ofReal C) : ∀ᵐ x ∂μ, ‖f x‖ ≤ C := by
  filter_upwards [enorm_ae_le_eLpNormEssSup f μ] with x hx
  have h2 : ‖f x‖ₑ ≤ ENNReal.ofReal C := hx.trans (eLpNormEssSup_le_eLpNorm_top.trans h)
  rw [← ofReal_norm] at h2
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp h2

theorem isClosed_aeBall (R : ℝ) : IsClosed (aeBall d R) := by
  refine isClosed_of_closure_subset fun v hv => ?_
  obtain ⟨w, hwS, hwt⟩ := mem_closure_iff_seq_limit.mp hv
  have hconv : Tendsto (fun n => eLpNorm (⇑(w n) - ⇑v) 2 (haar d)) atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hwt
  have hm : TendstoInMeasure (haar d) (fun n => ⇑(w n)) atTop ⇑v :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hconv
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂haar d, ∀ n, |w (ns n) x| ≤ R := ae_all_iff.mpr fun n => hwS (ns n)
  filter_upwards [hall, hae] with x hx1 hx2
  exact le_of_tendsto (hx2.abs) (Eventually.of_forall hx1)

theorem eLpNorm_le_of_ae_abs_le {f : Torus d → ℝ} {R : ℝ} (hf : AEStronglyMeasurable f (haar d))
    (h : ∀ᵐ x ∂haar d, |f x| ≤ R) {p : ℝ≥0∞} : eLpNorm f p (haar d) ≤ ENNReal.ofReal R := by
  have := eLpNorm_le_of_ae_bound (p := p) (μ := haar d) (f := f) (C := R) hf
    (h.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
  simpa using this

theorem norm_Lp_le_of_ae_norm_le {E : Type*} [NormedAddCommGroup E] {v : Lp E 2 (haar d)}
    {R : ℝ} (hv : ∀ᵐ x ∂haar d, ‖v x‖ ≤ R) : ‖v‖ ≤ R := by
  have h : eLpNorm (⇑v) 2 (haar d) ≤ ENNReal.ofReal R := by
    have := eLpNorm_le_of_ae_bound (p := 2) (μ := haar d) (f := ⇑v) (C := R)
      (Lp.aestronglyMeasurable v) hv
    simpa using this
  have hR : 0 ≤ R := by
    obtain ⟨x, hx⟩ := hv.exists
    exact (norm_nonneg _).trans hx
  rw [Lp.norm_def]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal hR] at this

theorem norm_le_of_aeBall {v : L2s d} {R : ℝ} (hv : v ∈ aeBall d R) : ‖v‖ ≤ R :=
  norm_Lp_le_of_ae_norm_le ((show ∀ᵐ x ∂haar d, |v x| ≤ R from hv).mono fun x hx => by simpa [Real.norm_eq_abs] using hx)

/-! ### `L∞` bound for `div H_τ` and for the Duhamel integral -/

theorem divHeat_ae_le {τ : ℝ} (hτ : 0 < τ) (F : L2v d) {K : ℝ} (hK : 0 ≤ K)
    (hF : ∀ᵐ x ∂haar d, ‖F x‖ ≤ K) :
    ∀ᵐ x ∂haar d, ‖divHeat τ F x‖ ≤ Real.sqrt (d / 2) * τ ^ (-(1 : ℝ) / 2) * K := by
  have hmem : MemLp (⇑F) ⊤ (haar d) := memLp_top_of_bound (Lp.aestronglyMeasurable F) K hF
  have h1 := eLpNorm_divHeatFun_le hτ le_top hmem
  have h2 : eLpNorm (⇑F) ⊤ (haar d) ≤ ENNReal.ofReal K := by
    have := eLpNorm_le_of_ae_bound (p := ⊤) (μ := haar d) (f := ⇑F) (C := K)
      (Lp.aestronglyMeasurable F) hF
    simpa using this
  have hc : 0 ≤ Real.sqrt (d / 2) * τ ^ (-(1 : ℝ) / 2) := by positivity
  have h3 : eLpNorm (divHeatFun τ ⇑F) ⊤ (haar d) ≤
      ENNReal.ofReal (Real.sqrt (d / 2) * τ ^ (-(1 : ℝ) / 2) * K) := by
    rw [ENNReal.ofReal_mul hc]
    exact h1.trans (mul_le_mul' le_rfl h2)
  have := ae_norm_le_of_eLpNorm_top_le (mul_nonneg hc hK) h3
  filter_upwards [this, coeFn_divHeat hτ F] with x hx1 hx2
  rw [hx2]; exact hx1

/-- `L∞` bound for the Duhamel integral of an `L∞`-bounded `L²` curve, by duality against
indicators of measurable sets. -/
theorem ae_norm_duhamel_le {g : ℝ → L2v d} (hg : Continuous g) {K : ℝ} (hK : 0 ≤ K)
    (hgK : ∀ r, ∀ᵐ x ∂haar d, ‖g r x‖ ≤ K) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ x ∂haar d,
      |duhamel (fun τ => (divHeat τ : L2v d →L[ℝ] L2s d)) g t x| ≤
        2 * Real.sqrt (d / 2) * K * Real.sqrt t := by
  set D : ℝ → L2v d →L[ℝ] L2s d := fun τ => divHeat τ with hD
  set c := Real.sqrt (d / 2) with hc
  have hker : DuhamelKernel D c := divHeat_duhamelKernel
  have hM : ∀ r, ‖g r‖ ≤ K := fun r => norm_Lp_le_of_ae_norm_le (hgK r)
  set w := duhamel D g t with hw
  set C := 2 * c * K * Real.sqrt t with hC
  have hC0 : 0 ≤ C := by positivity
  have key : ∀ A : Set (Torus d), MeasurableSet A →
      |∫ x in A, w x ∂haar d| ≤ C * (haar d).real A := by
    intro A hA
    have hAfin : haar d A ≠ ∞ := measure_ne_top _ _
    set ℓ : L2s d →L[ℝ] ℝ := innerSL ℝ (indicatorConstLp 2 hA hAfin (1 : ℝ)) with hℓ
    have hℓw : ∀ f : L2s d, ℓ f = ∫ x in A, f x ∂haar d := fun f => by
      rw [hℓ, innerSL_apply_apply]
      exact L2.inner_indicatorConstLp_one hA hAfin f
    have hint := intervalIntegrable_duhamel hker hg hM ht
    have e1 : ℓ w = ∫ r in (0 : ℝ)..t, ℓ (D r (g (t - r))) := by
      rw [hw, duhamel]
      exact (ℓ.intervalIntegral_comp_comm hint).symm
    have hbi : IntervalIntegrable
        (fun r : ℝ => c * K * (haar d).real A * r ^ (-(1 : ℝ) / 2)) volume 0 t :=
      (intervalIntegral.intervalIntegrable_rpow' (r := -(1 : ℝ) / 2) (a := 0) (b := t)
        (by norm_num)).const_mul (c * K * (haar d).real A)
    have e2 : ‖∫ r in (0 : ℝ)..t, ℓ (D r (g (t - r)))‖ ≤
        ∫ r in (0 : ℝ)..t, c * K * (haar d).real A * r ^ (-(1 : ℝ) / 2) := by
      refine intervalIntegral.norm_integral_le_of_norm_le ht ?_ hbi
      refine Eventually.of_forall fun r hr => ?_
      have hr0 : 0 < r := hr.1
      have hb := divHeat_ae_le hr0 (g (t - r)) hK (hgK (t - r))
      rw [hℓw]
      refine (norm_setIntegral_le_of_norm_le_const_ae' (measure_lt_top _ _)
        (hb.mono fun x hx _ => hx)).trans ?_
      have : (c * r ^ (-(1 : ℝ) / 2) * K) * (haar d).real A =
          c * K * (haar d).real A * r ^ (-(1 : ℝ) / 2) := by ring
      exact this.le
    have e3 : ∫ r in (0 : ℝ)..t, c * K * (haar d).real A * r ^ (-(1 : ℝ) / 2) =
        C * (haar d).real A := by
      rw [intervalIntegral.integral_const_mul, integral_rpow_neg_half, hC]; ring
    rw [← hℓw, ← Real.norm_eq_abs, e1]
    exact e2.trans e3.le
  have hwi : Integrable (⇑w) (haar d) := (Lp.memLp w).integrable one_le_two
  have hp : 0 ≤ᵐ[haar d] fun x => C - w x := by
    refine ae_nonneg_of_forall_setIntegral_nonneg ((integrable_const C).sub hwi) fun A hA _ => ?_
    rw [integral_sub (integrable_const C).integrableOn hwi.integrableOn,
      setIntegral_const, smul_eq_mul, mul_comm]
    linarith [(abs_le.mp (key A hA)).2]
  have hn : 0 ≤ᵐ[haar d] fun x => C + w x := by
    refine ae_nonneg_of_forall_setIntegral_nonneg ((integrable_const C).add hwi) fun A hA _ => ?_
    rw [integral_add (integrable_const C).integrableOn hwi.integrableOn,
      setIntegral_const, smul_eq_mul, mul_comm]
    linarith [(abs_le.mp (key A hA)).1]
  filter_upwards [hp, hn] with x h1 h2
  rw [abs_le]
  constructor <;> simp only [Pi.zero_apply] at h1 h2 <;> linarith

/-! ### `L∞` bound for the heat flow -/

theorem ae_abs_heatL2_le (ρ0 : L2s d) {M : ℝ} (hρ0 : ∀ᵐ x ∂haar d, |ρ0 x| ≤ M) {t : ℝ}
    (ht : 0 ≤ t) : ∀ᵐ x ∂haar d, |heatL2 ρ0 t x| ≤ M := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    rw [heatL2_zero]; exact hρ0
  have hM : 0 ≤ M := by
    obtain ⟨x, hx⟩ := hρ0.exists
    exact (abs_nonneg _).trans hx
  set f : Torus d → ℝ := fun x => max (-M) (min (ρ0 x) M) with hf
  have hfb : ∀ x, |f x| ≤ M := fun x => by
    rw [abs_le]
    refine ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hfe : f =ᵐ[haar d] ⇑ρ0 := hρ0.mono fun x hx => by
    obtain ⟨h1, h2⟩ := abs_le.mp hx
    simp only [hf]
    rw [min_eq_left h2, max_eq_right h1]
  have hconv : heatOp t ⇑ρ0 = heatOp t f := (torusConv_congr_ae _ hfe).symm
  filter_upwards [coeFn_heatL2 ρ0 hpos] with x hx
  rw [hx, hconv]
  exact abs_torusConv_le (continuous_heatKernelT hpos) (fun z => (heatKernelT_pos hpos z).le)
    (integral_heatKernelT hpos) hfb x

/-! ### The fixed-point space `C([0,T]; L²)` with the a.e. bound `R` -/

/-- The divergence-heat Duhamel kernel family `τ ↦ div H_τ`. -/
noncomputable abbrev divHeatFam (d : ℕ) : ℝ → L2v d →L[ℝ] L2s d := fun τ => divHeat τ

/-- Continuous `L²`-paths on `[0,T]` taking values in the a.e.-ball of radius `R`. -/
def ballPaths (d : ℕ) (T R : ℝ) : Set C(Icc (0 : ℝ) T, L2s d) := {w | ∀ t, w t ∈ aeBall d R}

theorem isClosed_ballPaths (T R : ℝ) : IsClosed (ballPaths d T R) := by
  have : ballPaths d T R = ⋂ t, (fun w : C(Icc (0 : ℝ) T, L2s d) => w t) ⁻¹' aeBall d R := by
    ext w; simp [ballPaths]
  rw [this]
  exact isClosed_iInter fun t => (isClosed_aeBall R).preimage
    (continuous_eval_const t)

section FixedPoint

variable {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g b : ℝ}
  (h : MeanFieldData G B g b) {T : ℝ} (hT : 0 ≤ T)

/-- Extension of a path on `[0,T]` to `ℝ` by constants. -/
noncomputable def extPath (w : C(Icc (0 : ℝ) T, L2s d)) (s : ℝ) : L2s d := w (Set.projIcc 0 T hT s)

/-- The nonlinear forcing along a path. -/
noncomputable def gpath (w : C(Icc (0 : ℝ) T, L2s d)) (s : ℝ) : L2v d :=
  Nvec h (extPath hT w s)

/-- The mild map. -/
noncomputable def Phi (ρ0 : L2s d) (w : C(Icc (0 : ℝ) T, L2s d)) (t : Icc (0 : ℝ) T) : L2s d :=
  heatL2 ρ0 t + duhamel (divHeatFam d) (gpath h hT w) t

variable {h hT}

theorem continuous_extPath (w : C(Icc (0 : ℝ) T, L2s d)) : Continuous (extPath hT w) :=
  w.continuous.comp continuous_projIcc

variable {R : ℝ} {w : C(Icc (0 : ℝ) T, L2s d)}

theorem continuous_gpath (hR : 0 ≤ R) (hw : w ∈ ballPaths d T R) : Continuous (gpath h hT w) :=
  (continuousOn_Nvec h hR).comp_continuous (continuous_extPath w) fun _ => hw _

theorem norm_gpath_le (hw : w ∈ ballPaths d T R) (s : ℝ) :
    ‖gpath h hT w s‖ ≤ (g + b) * R :=
  (norm_Nvec_le h _).trans (mul_le_mul_of_nonneg_left (norm_le_of_aeBall (hw _))
    (add_nonneg h.g_nonneg h.b_nonneg))

theorem ae_gpath_le (hw : w ∈ ballPaths d T R) (s : ℝ) :
    ∀ᵐ x ∂haar d, ‖gpath h hT w s x‖ ≤ (g + b) * R := by
  have hgb := add_nonneg h.g_nonneg h.b_nonneg
  filter_upwards [coeFn_Nvec h (extPath hT w s), hw (Set.projIcc 0 T hT s)] with x h1 h2
  have h3 := norm_meanFieldN_le h ((Lp.memLp (extPath hT w s)).integrable one_le_two) x
  change ‖(Nvec h (extPath hT w s)) x‖ ≤ _
  rw [h1]
  exact h3.trans (mul_le_mul_of_nonneg_left h2 hgb)

theorem continuous_Phi (ρ0 : L2s d) (hR : 0 ≤ R) (hw : w ∈ ballPaths d T R) :
    Continuous (Phi h hT ρ0 w) := by
  have hc1 : ContinuousOn (fun t => heatL2 ρ0 t) (Icc 0 T) :=
    (continuousOn_heatL2 ρ0).mono Icc_subset_Ici_self
  have hc2 : ContinuousOn (duhamel (divHeatFam d) (gpath h hT w)) (Icc 0 T) :=
    continuousOn_duhamel divHeat_duhamelKernel (continuous_gpath hR hw)
      (norm_gpath_le (h := h) (hT := hT) hw) hT
  exact continuousOn_iff_continuous_domRestrict.mp (hc1.add hc2)

theorem Phi_mem {ρ0 : L2s d} {M : ℝ} (hM : 0 ≤ M) (hρ0 : ∀ᵐ x ∂haar d, |ρ0 x| ≤ M)
    (hTs : 4 * Real.sqrt (d / 2) * (g + b) * Real.sqrt T ≤ 1)
    (hw : w ∈ ballPaths d T (2 * M)) (t : Icc (0 : ℝ) T) :
    Phi h hT ρ0 w t ∈ aeBall d (2 * M) := by
  have hgb := add_nonneg h.g_nonneg h.b_nonneg
  have hR : 0 ≤ 2 * M := by positivity
  have hK : 0 ≤ (g + b) * (2 * M) := by positivity
  have hd := ae_norm_duhamel_le (g := gpath h hT w) (continuous_gpath (h := h) (hT := hT) hR hw) hK
    (ae_gpath_le (h := h) (hT := hT) hw) t.2.1
  have hs : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt t.2.2
  have h1 : 4 * Real.sqrt (d / 2) * (g + b) * Real.sqrt t ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left hs (by positivity)) hTs
  have h2 := mul_le_mul_of_nonneg_left h1 hM
  filter_upwards [ae_abs_heatL2_le ρ0 hρ0 t.2.1, hd,
    Lp.coeFn_add (heatL2 ρ0 t) (duhamel (divHeatFam d) (gpath h hT w) t)] with x h1' h2' h3'
  unfold Phi
  rw [h3', Pi.add_apply]
  refine (abs_add_le _ _).trans ?_
  have : 2 * Real.sqrt (d / 2) * ((g + b) * (2 * M)) * Real.sqrt t ≤ M := by nlinarith
  linarith

theorem dist_Phi_le {ρ0 : L2s d} {w' : C(Icc (0 : ℝ) T, L2s d)} (hR : 0 ≤ R)
    (hw : w ∈ ballPaths d T R) (hw' : w' ∈ ballPaths d T R)
    (hTs : 4 * Real.sqrt (d / 2) * (g + b + 2 * b * R) * Real.sqrt T ≤ 1) :
    dist (⟨Phi h hT ρ0 w, continuous_Phi ρ0 hR hw⟩ : C(Icc (0 : ℝ) T, L2s d))
      ⟨Phi h hT ρ0 w', continuous_Phi ρ0 hR hw'⟩ ≤ (1 / 2) * dist w w' := by
  have hL : 0 ≤ g + b + 2 * b * R := by
    have := h.g_nonneg; have := h.b_nonneg; positivity
  have hd0 : 0 ≤ dist w w' := dist_nonneg
  refine (ContinuousMap.dist_le (by positivity)).mpr fun t => ?_
  have hg1 := continuous_gpath (h := h) (hT := hT) hR hw
  have hg2 := continuous_gpath (h := h) (hT := hT) hR hw'
  have hsub : ∀ r, ‖gpath h hT w r - gpath h hT w' r‖ ≤ (g + b + 2 * b * R) * dist w w' := by
    intro r
    unfold gpath
    refine (norm_Nvec_sub_le h _ _ hR (hw' _)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hL
    rw [← dist_eq_norm]
    exact ContinuousMap.dist_apply_le_dist _
  have hd := duhamel_norm_le (divHeat_duhamelKernel (d := d)) hsub t.2.1
  rw [duhamel_sub (divHeat_duhamelKernel (d := d)) hg1 hg2 (norm_gpath_le (h := h) (hT := hT) hw)
    (norm_gpath_le (h := h) (hT := hT) hw')  t.2.1] at hd
  have hs : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt t.2.2
  change dist (Phi h hT ρ0 w t) (Phi h hT ρ0 w' t) ≤ _
  rw [dist_eq_norm]
  have e : Phi h hT ρ0 w t - Phi h hT ρ0 w' t =
      duhamel (divHeatFam d) (gpath h hT w) t - duhamel (divHeatFam d) (gpath h hT w') t := by
    unfold Phi; abel
  rw [e]
  refine hd.trans ?_
  have h3 : 2 * Real.sqrt (d / 2) * ((g + b + 2 * b * R) * dist w w') * Real.sqrt t ≤
      2 * Real.sqrt (d / 2) * ((g + b + 2 * b * R) * dist w w') * Real.sqrt T :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  have h4 := mul_le_mul_of_nonneg_left hTs hd0
  nlinarith

end FixedPoint

/-! ### Banach's fixed point theorem and the main statement -/

theorem exists_mild_fixedPoint {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d}
    {g b : ℝ} (h : MeanFieldData G B g b) {T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M) (ρ0 : L2s d)
    (hρ0 : ∀ᵐ x ∂haar d, |ρ0 x| ≤ M)
    (hTs : 4 * Real.sqrt (d / 2) * (g + b + 2 * b * (2 * M)) * Real.sqrt T ≤ 1) :
    ∃ u : ℝ → L2s d, ContinuousOn u (Icc 0 T) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂haar d, |u t x| ≤ 2 * M) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        u t = heatL2 ρ0 t + duhamel (divHeatFam d) (fun s => Nvec h (u s)) t := by
  have hR : 0 ≤ 2 * M := by positivity
  have hb := h.b_nonneg
  have hTs' : 4 * Real.sqrt (d / 2) * (g + b) * Real.sqrt T ≤ 1 := by
    refine le_trans ?_ hTs
    have : g + b ≤ g + b + 2 * b * (2 * M) := by nlinarith
    have := h.g_nonneg
    gcongr
  let f : ballPaths d T (2 * M) → ballPaths d T (2 * M) := fun w =>
    ⟨⟨Phi h hT ρ0 w.1, continuous_Phi ρ0 hR w.2⟩, fun t => Phi_mem hM hρ0 hTs' w.2 t⟩
  have hf : ContractingWith (1 / 2 : ℝ≥0) f := by
    refine ⟨by rw [← NNReal.coe_lt_coe]; norm_num, LipschitzWith.of_dist_le_mul fun w w' => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq]
    simpa using dist_Phi_le (h := h) (hT := hT) (ρ0 := ρ0) hR w.2 w'.2 hTs
  have : CompleteSpace (ballPaths d T (2 * M)) := (isClosed_ballPaths T _).completeSpace_coe
  have : Nonempty (ballPaths d T (2 * M)) := by
    refine ⟨⟨0, fun t => ?_⟩⟩
    show ∀ᵐ x ∂haar d, |((0 : C(Icc (0 : ℝ) T, L2s d)) t) x| ≤ 2 * M
    filter_upwards [Lp.coeFn_zero ℝ 2 (haar d)] with x hx
    simp [hR]
  have hfix := hf.fixedPoint_isFixedPt
  set w := ContractingWith.fixedPoint f hf with hw
  have hmem : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T), extPath hT w.1 t = w.1 ⟨t, ht⟩ := by
    intro t ht
    simp [extPath, Set.projIcc_of_mem _ ht]
  refine ⟨extPath hT w.1, (continuous_extPath w.1).continuousOn, fun t ht => ?_, fun t ht => ?_⟩
  · rw [hmem t ht]
    exact w.2 _
  · rw [hmem t ht]
    have := congrArg (fun z : ballPaths d T (2 * M) => z.1 ⟨t, ht⟩) hfix
    refine this.symm.trans ?_
    rfl

/-- **Modified mean field mild contraction.** With `g = ‖∇V‖∞` and `b = ‖B‖∞` upper bounds
(so `B₀ = g + b`), the normalisation `P(u) = u⁺ / max 1 ∫u⁺` is `2`-Lipschitz in `L¹` with
`∫ P(u) ≤ 1`, the nonlinearity `𝒩(u) = u (∇V + B ∗ P(u))` satisfies the stated `L^p` bounds, and
for a bounded initial density `ρ₀` the modified heat mild map
`ρ(t) = H_t ρ₀ + ∫₀ᵗ div H_{t-s} 𝒩(ρ(s)) ds` has a local fixed point, continuous into `L²`
with `L∞` norm at most `2‖ρ₀‖∞`. -/
theorem modified_mean_field_mild_contraction {G : Torus d → Tangent d}
    {B : Torus d → Torus d → Tangent d} {g b : ℝ} (h : MeanFieldData G B g b) :
    (∀ u v : Torus d → ℝ, Integrable u (haar d) → Integrable v (haar d) →
      eLpNorm (fun x => normPos u x - normPos v x) 1 (haar d) ≤
        2 * eLpNorm (fun x => u x - v x) 1 (haar d)) ∧
    (∀ u : Torus d → ℝ, ∫ x, normPos u x ∂haar d ≤ 1) ∧
    (∀ (p : ℝ≥0∞), 1 ≤ p → ∀ u : Torus d → ℝ, MemLp u p (haar d) →
      eLpNorm (meanFieldN G B u) p (haar d) ≤ ENNReal.ofReal (g + b) * eLpNorm u p (haar d)) ∧
    (∀ (p : ℝ≥0∞), 1 ≤ p → ∀ u v : Torus d → ℝ, MemLp u p (haar d) → MemLp v p (haar d) →
      eLpNorm (fun x => meanFieldN G B u x - meanFieldN G B v x) p (haar d) ≤
        ENNReal.ofReal (g + b) * eLpNorm (fun x => u x - v x) p (haar d) +
          ENNReal.ofReal (2 * b) * eLpNorm v p (haar d) *
            eLpNorm (fun x => u x - v x) 1 (haar d)) ∧
    (∀ (ρ0 : L2s d) (M : ℝ), (∀ᵐ x ∂haar d, |ρ0 x| ≤ M) →
      ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → L2s d, ContinuousOn u (Icc 0 T) ∧
        (∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂haar d, |u t x| ≤ 2 * M) ∧
        ∀ t ∈ Icc (0 : ℝ) T,
          u t = heatL2 ρ0 t + duhamel (divHeatFam d) (fun s => Nvec h (u s)) t) := by
  refine ⟨fun u v hu hv => eLpNorm_normPos_sub_le hu hv, fun u => integral_normPos_le,
    fun p hp u hu => eLpNorm_meanFieldN_le h hp hu,
    fun p hp u v hu hv => eLpNorm_meanFieldN_sub_le h hp hu hv, fun ρ0 M hρ0 => ?_⟩
  have hM : 0 ≤ M := by
    obtain ⟨x, hx⟩ := hρ0.exists
    exact (abs_nonneg _).trans hx
  have hb := h.b_nonneg
  have hg := h.g_nonneg
  set K : ℝ := 4 * Real.sqrt (d / 2) * (g + b + 2 * b * (2 * M)) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨(1 / (K + 1)) ^ 2, by positivity, ?_⟩
  refine exists_mild_fixedPoint h (by positivity) hM ρ0 hρ0 ?_
  rw [Real.sqrt_sq (by positivity), ← hK, mul_one_div, div_le_one (by positivity)]
  linarith

end DGPS.Lipschitz
