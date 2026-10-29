import DGPS.Basic.ParabolicChainRuleFinal

/-!
# Weak chain rule on the torus (LIP030a)

If `u ∈ H¹(𝕋^d)` with weak gradient `g` and `Φ : ℝ → ℝ` is `C¹` with bounded derivative, then
`Φ ∘ u` has weak gradient `Φ'(u) g` (`isWeakGradient_comp`).  Application: for `ρ ≥ 0` a.e. in
`H¹`, `√(ρ+δ)` has weak gradient `∇ρ / (2 √(ρ+δ))` (`isWeakGradient_sqrt_add`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace DGPS.Lipschitz.WeakChainRule

open DGPS DGPS.Lipschitz.ParabolicChainRule

variable {d : ℕ}

theorem IsWeakGradient.congr_ae {u u' : Torus d → ℝ} {g g' : Torus d → Tangent d}
    (h : IsWeakGradient u g) (hu : u =ᵐ[haar d] u') (hg : g =ᵐ[haar d] g') :
    IsWeakGradient u' g' where
  memLp := h.memLp.ae_eq hu
  memLp_grad := h.memLp_grad.ae_eq hg
  ibp φ hφ j := by
    have e1 : ∫ x, u' x * coordPartial j φ x ∂haar d = ∫ x, u x * coordPartial j φ x ∂haar d :=
      integral_congr_ae (by filter_upwards [hu] with x hx; rw [hx])
    have e2 : ∫ x, (g' x).ofLp j * φ x ∂haar d = ∫ x, (g x).ofLp j * φ x ∂haar d :=
      integral_congr_ae (by filter_upwards [hg] with x hx; rw [hx])
    rw [e1, e2]
    exact h.ibp φ hφ j

theorem coordPartial_comp {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ) {v : Torus d → ℝ}
    (hv : IsC1Periodic v) (j : Fin d) (x : Torus d) :
    coordPartial j (fun y => Φ (v y)) x = deriv Φ (v x) * coordPartial j v x := by
  have hv1 : DifferentiableAt ℝ (v ∘ SharpLSI.liftT) (SharpLSI.secT x) :=
    (hv.differentiable one_ne_zero) _
  have hΦd : DifferentiableAt ℝ Φ ((v ∘ SharpLSI.liftT) (SharpLSI.secT x)) :=
    (hΦ.differentiable one_ne_zero) _
  have : ((fun y => Φ (v y)) ∘ SharpLSI.liftT) = Φ ∘ (v ∘ SharpLSI.liftT) := rfl
  unfold DGPS.coordPartial
  rw [this, fderiv_comp _ hΦd hv1, ContinuousLinearMap.comp_apply]
  have h2 : ∀ w : ℝ, fderiv ℝ Φ ((v ∘ SharpLSI.liftT) (SharpLSI.secT x)) w
      = deriv Φ (v x) * w := by
    intro w
    have : w = w • (1 : ℝ) := by simp
    rw [this, map_smul, fderiv_apply_one_eq_deriv]
    simp [SharpLSI.liftT_secT, mul_comm]
  rw [h2]

theorem isC1Periodic_comp {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ) {v : Torus d → ℝ}
    (hv : IsC1Periodic v) : IsC1Periodic (fun y => Φ (v y)) :=
  hΦ.comp hv

theorem tendsto_integral_mul_of_L2 {F : ℕ → Torus d → ℝ} {f w : Torus d → ℝ}
    (hF : ∀ n, MemLp (F n) 2 (haar d)) (hf : MemLp f 2 (haar d)) (hw : MemLp w 2 (haar d))
    (hc : Tendsto (fun n => eLpNorm (fun x => F n x - f x) 2 (haar d)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, F n x * w x ∂haar d) atTop (𝓝 (∫ x, f x * w x ∂haar d)) := by
  have hq : Tendsto (fun _ : ℕ => eLpNorm (fun x => w x - w x) 2 (haar d)) atTop (𝓝 0) := by
    simp
  have h := lip026c_tendsto_eLpNorm_mul_sub (l := atTop) (P := F) (Q := fun _ => w)
    (p := f) (q := w) (Eventually.of_forall fun _ => hw) (Eventually.of_forall hF) hf hw hc hq
  refine tendsto_integral_of_L1' _ (Eventually.of_forall fun n =>
    (hF n).integrable_mul hw) ?_
  exact h


theorem tendsto_integral_bdd_mul_sub {P Q : ℕ → Torus d → ℝ} {q : Torus d → ℝ} {C : ℝ}
    (hPC : ∀ n, ∀ᵐ x ∂haar d, |P n x| ≤ C)
    (hQ : ∀ n, MemLp (Q n) 2 (haar d)) (hq : MemLp q 2 (haar d))
    (hc : Tendsto (fun n => eLpNorm (fun x => Q n x - q x) 2 (haar d)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, P n x * (Q n x - q x) ∂haar d) atTop (𝓝 0) := by
  have hC : 0 ≤ C := by
    obtain ⟨x, hx⟩ := (hPC 0).exists
    exact (abs_nonneg _).trans hx
  have hD : ∀ n, MemLp (fun x => Q n x - q x) 2 (haar d) := fun n => (hQ n).sub hq
  have h1 : Tendsto (fun n => (eLpNorm (fun x => Q n x - q x) 2 (haar d)).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hc
    simpa [Function.comp_def] using this
  have hb : Tendsto (fun n => C * (eLpNorm (fun x => Q n x - q x) 2 (haar d)).toReal) atTop
      (𝓝 0) := by simpa using h1.const_mul C
  refine squeeze_zero_norm (fun n => ?_) hb
  have hi : Integrable (fun x => Q n x - q x) (haar d) := (hD n).integrable one_le_two
  calc ‖∫ x, P n x * (Q n x - q x) ∂haar d‖
      ≤ ∫ x, C * ‖Q n x - q x‖ ∂haar d := by
        refine norm_integral_le_of_norm_le (hi.norm.const_mul C) ?_
        filter_upwards [hPC n] with x hx
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ = C * (eLpNorm (fun x => Q n x - q x) 1 (haar d)).toReal := by
        rw [integral_const_mul, integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable,
          eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable]
    _ ≤ C * (eLpNorm (fun x => Q n x - q x) 2 (haar d)).toReal := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        exact ENNReal.toReal_mono (hD n).eLpNorm_ne_top
          (eLpNorm_le_eLpNorm_of_exponent_le one_le_two)

/-- **Weak chain rule.**  `Φ ∈ C¹(ℝ)` with bounded derivative maps `H¹(𝕋^d)` into itself,
with `∇(Φ ∘ u) = Φ'(u) ∇u`. -/
theorem isWeakGradient_comp {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ) {M : ℝ}
    (hM : ∀ y, |deriv Φ y| ≤ M) {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hg : IsWeakGradient u g) :
    IsWeakGradient (fun x => Φ (u x)) (fun x => deriv Φ (u x) • g x) := by
  classical
  have hΦc : Continuous Φ := hΦ.continuous
  have hΦ'c : Continuous (deriv Φ) := hΦ.continuous_deriv le_rfl
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hLip : ∀ a b, |Φ a - Φ b| ≤ M * |a - b| := by
    intro a b
    have := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := Φ) (s := Set.univ)
      (fun x _ => (hΦ.differentiable one_ne_zero) x) (fun x _ => by simpa using hM x)
      convex_univ (Set.mem_univ b) (Set.mem_univ a)
    simpa [Real.norm_eq_abs] using this
  have hum := hg.memLp.aestronglyMeasurable
  have hΦu : AEStronglyMeasurable (fun x => Φ (u x)) (haar d) :=
    hΦc.comp_aestronglyMeasurable hum
  have hΦ'u : AEStronglyMeasurable (fun x => deriv Φ (u x)) (haar d) :=
    hΦ'c.comp_aestronglyMeasurable hum
  have hmem : MemLp (fun x => Φ (u x)) 2 (haar d) := by
    refine MemLp.mono' ((memLp_const |Φ 0|).add (hg.memLp.norm.const_mul M)) hΦu
      (Eventually.of_forall fun x => ?_)
    show ‖Φ (u x)‖ ≤ |Φ 0| + M * ‖u x‖
    have h := hLip (u x) 0
    rw [sub_zero] at h
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := abs_le.mp h
    have h2 := neg_abs_le (Φ 0)
    have h3 := le_abs_self (Φ 0)
    exact abs_le.mpr ⟨by nlinarith [abs_nonneg (Φ 0)], by nlinarith [abs_nonneg (Φ 0)]⟩
  have hmemg : MemLp (fun x => deriv Φ (u x) • g x) 2 (haar d) := by
    refine MemLp.mono' (hg.memLp_grad.norm.const_mul M)
      (hΦ'u.smul hg.memLp_grad.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    show ‖deriv Φ (u x) • g x‖ ≤ M * ‖g x‖
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  refine ⟨hmem, hmemg, fun φ hφ j => ?_⟩
  obtain ⟨v, hvs, -, hv2, hvg⟩ := exists_smooth_tendsto_H1 hg
  -- an a.e. convergent subsequence
  have hmeas : TendstoInMeasure (haar d) v atTop u :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hv2
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  obtain ⟨Cφ, hCφ⟩ := isCompact_univ.exists_bound_of_continuousOn
    hφ.continuous_torus.continuousOn
  have hφb : ∀ x, |φ x| ≤ Cφ := fun x => by simpa using hCφ x (Set.mem_univ x)
  have hCφ0 : 0 ≤ Cφ := (abs_nonneg _).trans (hφb 0)
  have hwj : MemLp (coordPartial j φ) 2 (haar d) :=
    memLp_two_of_continuous (hφ.continuous_coordPartial j)
  have hgj : MemLp (fun x => g x j) 2 (haar d) := memLp_coord hg.memLp_grad j
  have hφm : MemLp φ 2 (haar d) := memLp_two_of_continuous hφ.continuous_torus
  -- left side
  have hL : Tendsto (fun k => ∫ x, Φ (v (ns k) x) * coordPartial j φ x ∂haar d) atTop
      (𝓝 (∫ x, Φ (u x) * coordPartial j φ x ∂haar d)) := by
    have hv2' := hv2.comp hns.tendsto_atTop
    refine (tendsto_integral_mul_of_L2 (F := fun k x => Φ (v (ns k) x)) (fun k => ?_) hmem hwj ?_)
    · exact (memLp_two_of_continuous
        (isC1Periodic_comp hΦ (isC1Periodic_of_smooth (hvs (ns k)))).continuous_torus)
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa using ENNReal.Tendsto.const_mul hv2' (Or.inr ENNReal.ofReal_ne_top) :
          Tendsto (fun k => ENNReal.ofReal M * eLpNorm (fun x => v (ns k) x - u x) 2 (haar d))
            atTop (𝓝 0))
        (fun _ => zero_le) (fun k => ?_)
      have hvm : AEStronglyMeasurable (v (ns k)) (haar d) :=
        (hvs (ns k)).isWeakGradient.memLp.aestronglyMeasurable
      have := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (μ := haar d)
        (f := fun x => Φ (v (ns k) x) - Φ (u x)) (g := fun x => v (ns k) x - u x)
        (c := M.toNNReal) ((hΦc.comp_aestronglyMeasurable hvm).sub hΦu)
        (Eventually.of_forall fun x => by
          rw [← NNReal.coe_le_coe]
          simpa [Real.norm_eq_abs, Real.coe_toNNReal _ hM0] using hLip (v (ns k) x) (u x)) 2
      exact this
  -- right side
  have hae' : ∀ᵐ x ∂haar d, Tendsto (fun k => v (ns k) x) atTop (𝓝 (u x)) := hae
  have hC1 : ∀ k, IsC1Periodic (v (ns k)) := fun k => isC1Periodic_of_smooth (hvs (ns k))
  have hsm : ∀ k, MemLp (fun x => smoothGrad (v (ns k)) x j) 2 (haar d) := fun k =>
    memLp_coord (hvs (ns k)).isWeakGradient.memLp_grad j
  have hPm : ∀ k, AEStronglyMeasurable (fun x => deriv Φ (v (ns k) x) * φ x) (haar d) := fun k =>
    ((hΦ'c.comp (hC1 k).continuous_torus).mul hφ.continuous_torus).aestronglyMeasurable
  have hX : Tendsto (fun k => ∫ x, (deriv Φ (v (ns k) x) * φ x) *
      (smoothGrad (v (ns k)) x j - g x j) ∂haar d) atTop (𝓝 0) :=
    tendsto_integral_bdd_mul_sub (P := fun k x => deriv Φ (v (ns k) x) * φ x)
      (Q := fun k x => smoothGrad (v (ns k)) x j) (q := fun x => g x j) (C := M * Cφ)
      (fun k => Eventually.of_forall fun x => by
        rw [abs_mul]; exact mul_le_mul (hM _) (hφb x) (abs_nonneg _) hM0) hsm hgj
      ((hvg j).comp hns.tendsto_atTop)
  have hGi : Integrable (fun x => g x j) (haar d) := hgj.integrable one_le_two
  have hYm : ∀ k, AEStronglyMeasurable
      (fun x => (deriv Φ (v (ns k) x) - deriv Φ (u x)) * φ x) (haar d) := fun k =>
    ((hΦ'c.comp (hC1 k).continuous_torus).aestronglyMeasurable.sub hΦ'u).mul
      hφ.continuous_torus.aestronglyMeasurable
  have hYb : ∀ k, ∀ᵐ x ∂haar d, ‖(deriv Φ (v (ns k) x) - deriv Φ (u x)) * φ x‖ ≤ 2 * M * Cφ :=
    fun k => Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 := abs_sub (deriv Φ (v (ns k) x)) (deriv Φ (u x))
      have h2 := hM (v (ns k) x)
      have h3 := hM (u x)
      calc _ ≤ (2 * M) * Cφ := mul_le_mul (by linarith) (hφb x) (abs_nonneg _) (by linarith)
        _ = _ := by ring
  have hY : Tendsto (fun k => ∫ x, ((deriv Φ (v (ns k) x) - deriv Φ (u x)) * φ x) * g x j
      ∂haar d) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := haar d)
      (F := fun k x => ((deriv Φ (v (ns k) x) - deriv Φ (u x)) * φ x) * g x j)
      (f := fun _ => 0) (fun x => 2 * M * Cφ * ‖g x j‖)
      (fun k => (hYm k).mul hgj.aestronglyMeasurable) (hGi.norm.const_mul _)
      (fun k => by
        filter_upwards [hYb k] with x hx
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hx (norm_nonneg _))
      (by
        filter_upwards [hae'] with x hx
        have h1 : Tendsto (fun k => deriv Φ (v (ns k) x)) atTop (𝓝 (deriv Φ (u x))) :=
          hΦ'c.continuousAt.tendsto.comp hx
        simpa using ((h1.sub_const (deriv Φ (u x))).mul_const (φ x)).mul_const (g x j))
    simpa using this
  have hfi : Integrable (fun x => (deriv Φ (u x) * φ x) * g x j) (haar d) :=
    hGi.bdd_mul (c := M * Cφ) ((hΦ'u.mul hφ.continuous_torus.aestronglyMeasurable))
      (Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul (hM _) (hφb x) (abs_nonneg _) hM0)
  have hXi : ∀ k, Integrable (fun x => (deriv Φ (v (ns k) x) * φ x) *
      (smoothGrad (v (ns k)) x j - g x j)) (haar d) := fun k =>
    (((hsm k).sub hgj).integrable one_le_two).bdd_mul (c := M * Cφ) (hPm k)
      (Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul (hM _) (hφb x) (abs_nonneg _) hM0)
  have hYi : ∀ k, Integrable (fun x => ((deriv Φ (v (ns k) x) - deriv Φ (u x)) * φ x) * g x j)
      (haar d) := fun k => hGi.bdd_mul (c := 2 * M * Cφ) (hYm k) (hYb k)
  have hR : Tendsto (fun k => ∫ x, (deriv Φ (v (ns k) x) * smoothGrad (v (ns k)) x j) * φ x
      ∂haar d) atTop (𝓝 (∫ x, (deriv Φ (u x) * φ x) * g x j ∂haar d)) := by
    have hsum := (hX.add hY).add (tendsto_const_nhds (x := ∫ x, (deriv Φ (u x) * φ x) * g x j
      ∂haar d))
    simp only [zero_add] at hsum
    refine hsum.congr fun k => ?_
    have hXY : Integrable (fun x => (deriv Φ (v (ns k) x) * φ x) *
        (smoothGrad (v (ns k)) x j - g x j) +
        ((deriv Φ (v (ns k) x) - deriv Φ (u x)) * φ x) * g x j) (haar d) :=
      (hXi k).add (hYi k)
    rw [← integral_add (hXi k) (hYi k), ← integral_add hXY hfi]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  have hIBP : ∀ k, ∫ x, Φ (v (ns k) x) * coordPartial j φ x ∂haar d =
      -∫ x, (deriv Φ (v (ns k) x) * smoothGrad (v (ns k)) x j) * φ x ∂haar d := by
    intro k
    rw [integral_mul_coordPartial_of_c1 (isC1Periodic_comp hΦ (hC1 k)) hφ j]
    simp_rw [coordPartial_comp hΦ (hC1 k), smoothGrad_apply]
  have h2 := hL.congr hIBP
  have h3 := tendsto_nhds_unique h2 hR.neg
  rw [h3]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [PiLp.smul_apply]
  ring

/-! ### Application: `√(ρ + δ)` -/

theorem glue_hasDerivAt (p q p' q' : ℝ → ℝ) (hp : ∀ r, 0 ≤ r → HasDerivAt p (p' r) r)
    (hq : ∀ r, r ≤ 0 → HasDerivAt q (q' r) r) (h0 : p 0 = q 0) (h0' : p' 0 = q' 0) (r : ℝ) :
    HasDerivAt (fun r => if 0 ≤ r then p r else q r) (if 0 ≤ r then p' r else q' r) r := by
  rcases lt_trichotomy r 0 with hr | hr | hr
  · have : (fun r => if 0 ≤ r then p r else q r) =ᶠ[nhds r] q := by
      filter_upwards [Iio_mem_nhds hr] with x hx
      simp [not_le.mpr (show x < 0 from hx)]
    simpa [not_le.mpr hr] using (hq r hr.le).congr_of_eventuallyEq this
  · subst hr
    have h1 : HasDerivWithinAt (fun r => if 0 ≤ r then p r else q r) (p' 0) (Ici 0) 0 := by
      refine ((hp 0 le_rfl).hasDerivWithinAt).congr (fun x hx => ?_) (by simp)
      simp [show 0 ≤ x from hx]
    have h2 : HasDerivWithinAt (fun r => if 0 ≤ r then p r else q r) (p' 0) (Iic 0) 0 := by
      rw [h0']
      refine ((hq 0 le_rfl).hasDerivWithinAt).congr (fun x hx => ?_) (by simp [h0])
      by_cases hx0 : 0 ≤ x
      · have : x = 0 := le_antisymm hx hx0
        subst this; simp [h0]
      · simp [hx0]
    have := h1.union h2
    rw [Ici_union_Iic, hasDerivWithinAt_univ] at this
    simpa using this
  · have : (fun r => if 0 ≤ r then p r else q r) =ᶠ[nhds r] p := by
      filter_upwards [Ioi_mem_nhds hr] with x hx
      simp [show 0 ≤ x from hx.le]
    simpa [hr.le] using (hp r hr.le).congr_of_eventuallyEq this

/-- The `C¹` extension to `ℝ` of `r ↦ √(r+δ)` (`r ≥ 0`) with bounded derivative. -/
noncomputable def sqrtReg (δ : ℝ) (r : ℝ) : ℝ :=
  if 0 ≤ r then Real.sqrt (r + δ) else Real.sqrt δ + r / (2 * Real.sqrt δ)

/-- Its derivative. -/
noncomputable def sqrtReg1 (δ : ℝ) (r : ℝ) : ℝ :=
  if 0 ≤ r then (2 * Real.sqrt (r + δ))⁻¹ else (2 * Real.sqrt δ)⁻¹

theorem hasDerivAt_sqrtReg {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    HasDerivAt (sqrtReg δ) (sqrtReg1 δ r) r := by
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  exact glue_hasDerivAt (fun r => Real.sqrt (r + δ))
    (fun r => Real.sqrt δ + r / (2 * Real.sqrt δ))
    (fun r => (2 * Real.sqrt (r + δ))⁻¹) (fun _ => (2 * Real.sqrt δ)⁻¹)
    (fun r hr => by
      have h1 : HasDerivAt (fun r => r + δ) 1 r := (hasDerivAt_id r).add_const δ
      have := h1.sqrt (by linarith : r + δ ≠ 0)
      simpa [one_div] using this)
    (fun r _ => by
      have := ((hasDerivAt_id r).div_const (2 * Real.sqrt δ)).const_add (Real.sqrt δ)
      simpa using this)
    (by simp) (by simp) r

theorem continuous_sqrtReg1 {δ : ℝ} (hδ : 0 < δ) : Continuous (sqrtReg1 δ) := by
  unfold sqrtReg1
  refine continuous_if_le continuous_const continuous_id ?_ ?_ ?_
  · refine continuousOn_of_forall_continuousAt fun r hr => ?_
    have hr' : (0 : ℝ) ≤ r := hr
    have : 2 * Real.sqrt (r + δ) ≠ 0 := by
      have := Real.sqrt_pos.mpr (by linarith : 0 < r + δ); positivity
    exact (continuousAt_const.mul
      (Real.continuous_sqrt.continuousAt.comp (continuousAt_id.add continuousAt_const))).inv₀ this
  · exact continuousOn_const
  · intro r hr; subst hr; simp

theorem contDiff_sqrtReg {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ 1 (sqrtReg δ) := by
  have hd : deriv (sqrtReg δ) = sqrtReg1 δ := funext fun r => (hasDerivAt_sqrtReg hδ r).deriv
  rw [contDiff_one_iff_deriv]
  exact ⟨fun r => (hasDerivAt_sqrtReg hδ r).differentiableAt, by rw [hd]; exact continuous_sqrtReg1 hδ⟩

theorem abs_deriv_sqrtReg_le {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    |deriv (sqrtReg δ) r| ≤ (2 * Real.sqrt δ)⁻¹ := by
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  rw [(hasDerivAt_sqrtReg hδ r).deriv, sqrtReg1]
  split_ifs with h
  · have h1 : Real.sqrt δ ≤ Real.sqrt (r + δ) := Real.sqrt_le_sqrt (by linarith)
    rw [abs_of_nonneg (by positivity)]
    exact inv_anti₀ (by positivity) (by linarith)
  · rw [abs_of_nonneg (by positivity)]

/-- **`√(ρ+δ) ∈ H¹`.**  For `ρ ∈ H¹` with `ρ ≥ 0` a.e. and `δ > 0`, `√(ρ+δ)` has weak gradient
`∇ρ / (2 √(ρ+δ))`. -/
theorem isWeakGradient_sqrt_add {δ : ℝ} (hδ : 0 < δ) {ρ : Torus d → ℝ} {g : Torus d → Tangent d}
    (hρ : IsWeakGradient ρ g) (hnn : ∀ᵐ x ∂haar d, 0 ≤ ρ x) :
    IsWeakGradient (fun x => Real.sqrt (ρ x + δ))
      (fun x => (2 * Real.sqrt (ρ x + δ))⁻¹ • g x) := by
  refine (isWeakGradient_comp (contDiff_sqrtReg hδ) (abs_deriv_sqrtReg_le hδ) hρ).congr_ae
    ?_ ?_
  · filter_upwards [hnn] with x hx
    simp [sqrtReg, hx]
  · filter_upwards [hnn] with x hx
    simp [(hasDerivAt_sqrtReg hδ (ρ x)).deriv, sqrtReg1, hx]

end DGPS.Lipschitz.WeakChainRule
