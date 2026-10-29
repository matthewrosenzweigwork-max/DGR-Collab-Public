import DGPS.Basic.HeatKernelBounds

/-!
# Mean-field local flow (LIP025), structured partial

Proved so far: the normalized positive part `P(u) = u⁺ / max(1, ∫ u⁺)` is `2`-Lipschitz in `L¹`
with `∫ P(u) ≤ 1`; an abstract Duhamel-integral layer (`DuhamelKernel`, norm bound
`2 c M √t`, continuity); and the continuous linear operator `divHeat τ : L²(𝕋^d;ℝ^d) → L²(𝕋^d)`,
`F ↦ div H_τ F`, with norm `≤ √(d/2) τ^{-1/2}`.  The mild-contraction fixed point
`DGPS.Lipschitz.modified_mean_field_mild_contraction` is NOT yet proved here.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- The normalized positive part `P(u) = u⁺ / max(1, ∫ u⁺)`. -/
noncomputable def normPos (u : Torus d → ℝ) (x : Torus d) : ℝ :=
  max (u x) 0 / max 1 (∫ y, max (u y) 0 ∂haar d)

/-- The modified nonlinearity `𝒩(u) = u (∇V + B ∗ P(u))`, with `G = ∇V`. -/
noncomputable def meanFieldN (G : Torus d → Tangent d) (B : Torus d → Torus d → Tangent d)
    (u : Torus d → ℝ) (x : Torus d) : Tangent d :=
  u x • (G x + ∫ y, normPos u y • B x y ∂haar d)

theorem normPos_nonneg (u : Torus d → ℝ) (x : Torus d) : 0 ≤ normPos u x :=
  div_nonneg (le_max_right _ _) (zero_le_one.trans (le_max_left _ _))

theorem integrable_normPos {u : Torus d → ℝ} (hu : Integrable u (haar d)) :
    Integrable (normPos u) (haar d) :=
  hu.pos_part.div_const _

theorem integral_normPos_le {u : Torus d → ℝ} : ∫ x, normPos u x ∂haar d ≤ 1 := by
  unfold normPos
  rw [integral_div, div_le_one (lt_of_lt_of_le one_pos (le_max_left _ _))]
  exact le_max_right _ _

theorem integral_abs_normPos_sub_le {u v : Torus d → ℝ} (hu : Integrable u (haar d))
    (hv : Integrable v (haar d)) :
    ∫ x, |normPos u x - normPos v x| ∂haar d ≤ 2 * ∫ x, |u x - v x| ∂haar d := by
  set a := max 1 (∫ y, max (u y) 0 ∂haar d) with ha
  set b := max 1 (∫ y, max (v y) 0 ∂haar d) with hb
  have ha1 : 1 ≤ a := le_max_left _ _
  have hb1 : 1 ≤ b := le_max_left _ _
  have hapos : 0 < a := by linarith
  have hbpos : 0 < b := by linarith
  have hI : Integrable (fun x => |u x - v x|) (haar d) := (hu.sub hv).abs
  set D := ∫ x, |u x - v x| ∂haar d with hD
  have hab : |a - b| ≤ D := by
    rw [ha, hb, max_comm 1, max_comm 1]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    rw [← integral_sub hu.pos_part hv.pos_part]
    refine (abs_integral_le_integral_abs).trans (integral_mono ?_ hI fun x => ?_)
    · exact (hu.pos_part.sub hv.pos_part).abs
    · exact abs_max_sub_max_le_abs _ _ _
  have key : ∀ x, |normPos u x - normPos v x| ≤ |u x - v x| + normPos v x * |a - b| := by
    intro x
    have hq : 0 ≤ max (v x) 0 := le_max_right _ _
    have e : normPos u x - normPos v x = (max (u x) 0 - max (v x) 0) / a +
        normPos v x * ((b - a) / a) := by
      unfold normPos
      rw [← ha, ← hb]
      field_simp
      ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, abs_of_pos hapos]
      exact (div_le_self (abs_nonneg _) ha1).trans (abs_max_sub_max_le_abs _ _ _)
    · rw [abs_mul, abs_div, abs_of_pos hapos, abs_of_nonneg (normPos_nonneg v x)]
      refine mul_le_mul_of_nonneg_left ?_ (normPos_nonneg v x)
      rw [abs_sub_comm]
      exact (div_le_self (abs_nonneg _) ha1)
  have hPv := integrable_normPos hv
  calc ∫ x, |normPos u x - normPos v x| ∂haar d
      ≤ ∫ x, (|u x - v x| + normPos v x * |a - b|) ∂haar d := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
          (hI.add (hPv.mul_const _)) (Eventually.of_forall key)
    _ = D + (∫ x, normPos v x ∂haar d) * |a - b| := by
        rw [integral_add hI (hPv.mul_const _), integral_mul_const]
    _ ≤ D + 1 * D := by
        refine add_le_add le_rfl ?_
        exact mul_le_mul integral_normPos_le hab (abs_nonneg _) zero_le_one
    _ = 2 * D := by ring

theorem eLpNorm_one_eq_ofReal_integral_abs {f : Torus d → ℝ} (hf : Integrable f (haar d)) :
    eLpNorm f 1 (haar d) = ENNReal.ofReal (∫ x, |f x| ∂haar d) := by
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hf]
  simp only [Real.norm_eq_abs]
  exact hf.aestronglyMeasurable

theorem eLpNorm_normPos_sub_le {u v : Torus d → ℝ} (hu : Integrable u (haar d))
    (hv : Integrable v (haar d)) :
    eLpNorm (fun x => normPos u x - normPos v x) 1 (haar d) ≤
      2 * eLpNorm (fun x => u x - v x) 1 (haar d) := by
  rw [eLpNorm_one_eq_ofReal_integral_abs (f := fun x => normPos u x - normPos v x)
      ((integrable_normPos hu).sub (integrable_normPos hv)),
    eLpNorm_one_eq_ofReal_integral_abs (f := fun x => u x - v x) (hu.sub hv)]
  have h := integral_abs_normPos_sub_le hu hv
  calc ENNReal.ofReal (∫ x, |normPos u x - normPos v x| ∂haar d)
      ≤ ENNReal.ofReal (2 * ∫ x, |u x - v x| ∂haar d) := ENNReal.ofReal_le_ofReal h
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num)]; simp


section AbstractDuhamel

open intervalIntegral

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The Duhamel integral `∫₀ᵗ D(r) g(t-r) dr` (Bochner integral in `E`). -/
noncomputable def duhamel (D : ℝ → W →L[ℝ] E) (g : ℝ → W) (t : ℝ) : E :=
  ∫ r in (0 : ℝ)..t, D r (g (t - r))

theorem integral_rpow_neg_half (t : ℝ) :
    ∫ r in (0 : ℝ)..t, r ^ (-(1 : ℝ) / 2) = 2 * Real.sqrt t := by
  rw [integral_rpow (Or.inl (by norm_num))]
  rw [Real.zero_rpow (by norm_num), Real.sqrt_eq_rpow]
  norm_num
  ring

variable {D : ℝ → W →L[ℝ] E} {c : ℝ}

/-- Hypotheses on the kernel family `D`: a `τ^{-1/2}` operator-norm bound and strong continuity
on `(0, ∞)`. -/
structure DuhamelKernel (D : ℝ → W →L[ℝ] E) (c : ℝ) : Prop where
  nonneg : 0 ≤ c
  bound : ∀ τ, 0 < τ → ∀ w, ‖D τ w‖ ≤ c * τ ^ (-(1 : ℝ) / 2) * ‖w‖
  cont : ∀ w, ContinuousOn (fun τ => D τ w) (Ioi 0)

theorem continuousOn_apply_of_bound (hc0 : 0 ≤ c)
    (hb : ∀ τ, 0 < τ → ∀ w, ‖D τ w‖ ≤ c * τ ^ (-(1 : ℝ) / 2) * ‖w‖)
    (hc : ∀ w, ContinuousOn (fun τ => D τ w) (Ioi 0))
    {h : ℝ → W} {S : Set ℝ} (hS : S ⊆ Ioi 0) (hh : ContinuousOn h S) :
    ContinuousOn (fun r => D r (h r)) S := by
  intro s hs
  have hts : 0 < s := hS hs
  have h2 : ContinuousWithinAt (fun s' => D s' (h s)) S s :=
    ((hc (h s)).continuousAt (Ioi_mem_nhds hts)).continuousWithinAt
  have h1 : ContinuousWithinAt (fun s' => D s' (h s' - h s)) S s := by
    rw [ContinuousWithinAt]
    simp only [sub_self, map_zero]
    set K := c * (s / 2) ^ (-(1 : ℝ) / 2) with hK
    have hdist : Tendsto (fun s' => ‖h s' - h s‖) (𝓝[S] s) (𝓝 0) := by
      have := ((hh s hs).tendsto.sub_const (h s))
      simpa using this.norm
    have hev : ∀ᶠ s' in 𝓝[S] s, s / 2 ≤ s' := by
      have : ∀ᶠ s' in 𝓝 s, s / 2 < s' := lt_mem_nhds (by linarith)
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun x hx => hx.le
    refine squeeze_zero_norm' ?_ (by simpa using hdist.const_mul K)
    filter_upwards [hev] with s' hs'
    have hpos : 0 < s' := by linarith
    refine (hb _ hpos _).trans ?_
    rw [hK]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by linarith) hs' (by norm_num)) hc0
  have := h1.add h2
  refine this.congr (fun x _ => ?_) (by simp)
  simp

theorem integrableOn_apply_of_bound (hc0 : 0 ≤ c)
    (hb : ∀ τ, 0 < τ → ∀ w, ‖D τ w‖ ≤ c * τ ^ (-(1 : ℝ) / 2) * ‖w‖)
    (hc : ∀ w, ContinuousOn (fun τ => D τ w) (Ioi 0))
    {h : ℝ → W} {M : ℝ} (hh : Continuous h) (hM : ∀ r, ‖h r‖ ≤ M) (a : ℝ) :
    IntegrableOn (fun r => D r (h r)) (Ioc 0 a) := by
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  have hcont : ContinuousOn (fun r => D r (h r)) (Ioo 0 a) :=
    continuousOn_apply_of_bound hc0 hb hc (fun x hx => hx.1) hh.continuousOn
  have hmeas := hcont.aestronglyMeasurable (μ := volume) (measurableSet_Ioo (a := (0 : ℝ)) (b := a))
  have hint : IntegrableOn (fun r : ℝ => c * M * r ^ (-(1 : ℝ) / 2)) (Ioo 0 a) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (r := -(1 : ℝ) / 2) (a := 0) (b := a)
      (by norm_num))
    have h2 := this.const_mul (c * M)
    rcases le_total 0 a with ha | ha
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha] at h2
      exact Iff.mp integrableOn_Ioc_iff_integrableOn_Ioo h2
    · rw [Ioo_eq_empty_of_le ha]
      exact integrableOn_empty
  refine Integrable.mono' hint hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Filter.Eventually.of_forall fun r hr => ?_
  have := hb r hr.1 (h r)
  calc ‖D r (h r)‖ ≤ c * r ^ (-(1 : ℝ) / 2) * ‖h r‖ := this
    _ ≤ c * r ^ (-(1 : ℝ) / 2) * M :=
        mul_le_mul_of_nonneg_left (hM r) (mul_nonneg hc0 (Real.rpow_nonneg hr.1.le _))
    _ = c * M * r ^ (-(1 : ℝ) / 2) := by ring

theorem intervalIntegrable_duhamel (hD : DuhamelKernel D c) {g : ℝ → W} (hg : Continuous g)
    {M : ℝ} (hM : ∀ r, ‖g r‖ ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun r => D r (g (t - r))) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
  exact integrableOn_apply_of_bound hD.nonneg hD.bound hD.cont
    (hg.comp (continuous_const.sub continuous_id)) (fun r => hM _) t

theorem duhamel_norm_le (hD : DuhamelKernel D c) {g : ℝ → W}
    {M : ℝ} (hM : ∀ r, ‖g r‖ ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    ‖duhamel D g t‖ ≤ 2 * c * M * Real.sqrt t := by
  unfold duhamel
  have hbi : IntervalIntegrable (fun r : ℝ => c * M * r ^ (-(1 : ℝ) / 2)) volume 0 t :=
    (intervalIntegral.intervalIntegrable_rpow' (r := -(1 : ℝ) / 2) (a := 0) (b := t)
      (by norm_num)).const_mul (c * M)
  refine (intervalIntegral.norm_integral_le_of_norm_le ht ?_ hbi).trans ?_
  · refine Filter.Eventually.of_forall fun r hr => ?_
    have := hD.bound r hr.1 (g (t - r))
    calc ‖D r (g (t - r))‖ ≤ c * r ^ (-(1 : ℝ) / 2) * ‖g (t - r)‖ := this
      _ ≤ c * r ^ (-(1 : ℝ) / 2) * M :=
          mul_le_mul_of_nonneg_left (hM _) (mul_nonneg hD.nonneg (Real.rpow_nonneg hr.1.le _))
      _ = c * M * r ^ (-(1 : ℝ) / 2) := by ring
  · rw [intervalIntegral.integral_const_mul, integral_rpow_neg_half]
    apply le_of_eq
    ring

theorem duhamel_sub (hD : DuhamelKernel D c) {g₁ g₂ : ℝ → W} (hg₁ : Continuous g₁)
    (hg₂ : Continuous g₂) {M₁ M₂ : ℝ} (hM₁ : ∀ r, ‖g₁ r‖ ≤ M₁) (hM₂ : ∀ r, ‖g₂ r‖ ≤ M₂)
    {t : ℝ} (ht : 0 ≤ t) :
    duhamel D (fun s => g₁ s - g₂ s) t = duhamel D g₁ t - duhamel D g₂ t := by
  unfold duhamel
  rw [← intervalIntegral.integral_sub (intervalIntegrable_duhamel hD hg₁ hM₁ ht)
    (intervalIntegrable_duhamel hD hg₂ hM₂ ht)]
  simp

theorem continuousOn_duhamel (hD : DuhamelKernel D c) {g : ℝ → W} (hg : Continuous g)
    {M : ℝ} (hM : ∀ r, ‖g r‖ ≤ M) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (duhamel D g) (Icc 0 T) := by
  intro t0 ht0
  set F : ℝ → ℝ → E := fun t r => (Iic t).indicator (fun r => D r (g (t - r))) r with hF
  have key : ∀ t ∈ Icc (0 : ℝ) T, duhamel D g t = ∫ r in Ioc 0 T, F t r := by
    intro t ht
    unfold duhamel
    rw [intervalIntegral.integral_of_le ht.1, hF]
    simp only
    rw [setIntegral_indicator measurableSet_Iic]
    congr 2
    ext r
    simp only [mem_Ioc, mem_inter_iff, mem_Iic]
    constructor
    · intro h; exact ⟨⟨h.1, h.2.trans ht.2⟩, h.2⟩
    · intro h; exact ⟨h.1.1, h.2⟩
  have hbi : IntegrableOn (fun r : ℝ => c * M * r ^ (-(1 : ℝ) / 2)) (Ioc 0 T) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (r := -(1 : ℝ) / 2) (a := 0) (b := T)
      (by norm_num)).const_mul (c * M)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp this
  have hmeas : ∀ t, AEStronglyMeasurable (F t) (volume.restrict (Ioc 0 T)) := by
    intro t
    have hcont : ContinuousOn (fun r => D r (g (t - r))) (Ioc 0 T) :=
      continuousOn_apply_of_bound hD.nonneg hD.bound hD.cont (fun x hx => hx.1)
        (hg.comp (continuous_const.sub continuous_id)).continuousOn
    exact (hcont.aestronglyMeasurable measurableSet_Ioc).indicator measurableSet_Iic
  have hbound : ∀ t, ∀ᵐ r ∂(volume.restrict (Ioc 0 T)), ‖F t r‖ ≤ c * M * r ^ (-(1 : ℝ) / 2) := by
    intro t
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun r hr => ?_
    have hnn : 0 ≤ c * M * r ^ (-(1 : ℝ) / 2) := by
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
      exact mul_nonneg (mul_nonneg hD.nonneg hM0) (Real.rpow_nonneg hr.1.le _)
    simp only [hF, indicator_apply, mem_Iic]
    split_ifs with h
    · have := hD.bound r hr.1 (g (t - r))
      calc ‖D r (g (t - r))‖ ≤ c * r ^ (-(1 : ℝ) / 2) * ‖g (t - r)‖ := this
        _ ≤ c * r ^ (-(1 : ℝ) / 2) * M :=
            mul_le_mul_of_nonneg_left (hM _)
              (mul_nonneg hD.nonneg (Real.rpow_nonneg hr.1.le _))
        _ = c * M * r ^ (-(1 : ℝ) / 2) := by ring
    · simpa using hnn
  have hlim : ∀ᵐ r ∂(volume.restrict (Ioc 0 T)),
      Tendsto (fun t => F t r) (𝓝[Icc 0 T] t0) (𝓝 (F t0 r)) := by
    have hne : ∀ᵐ r ∂(volume.restrict (Ioc 0 T)), r ∉ ({t0} : Set ℝ) :=
      ae_restrict_of_ae ((Set.countable_singleton t0).ae_notMem volume)
    filter_upwards [hne] with r hr
    have hr' : r ≠ t0 := hr
    rcases lt_or_gt_of_ne hr' with hlt | hgt
    · have hev : ∀ᶠ t in 𝓝 t0, F t r = D r (g (t - r)) := by
        have : ∀ᶠ t in 𝓝 t0, r < t := lt_mem_nhds hlt
        filter_upwards [this] with t ht
        simp only [hF]
        rw [indicator_of_mem (by simpa using ht.le)]
      have h0 : F t0 r = D r (g (t0 - r)) := by
        simp only [hF]
        rw [indicator_of_mem (by simpa using hlt.le)]
      have hcont : Continuous fun t : ℝ => D r (g (t - r)) :=
        (D r).continuous.comp (hg.comp (continuous_id.sub continuous_const))
      rw [h0]
      exact ((hcont.tendsto t0).mono_left nhdsWithin_le_nhds).congr'
        ((hev.filter_mono nhdsWithin_le_nhds).mono fun t ht => ht.symm)
    · have hev : ∀ᶠ t in 𝓝 t0, F t r = 0 := by
        have : ∀ᶠ t in 𝓝 t0, t < r := gt_mem_nhds hgt
        filter_upwards [this] with t ht
        simp only [hF]
        rw [indicator_of_notMem (by simpa using ht)]
      have h0 : F t0 r = 0 := by
        simp only [hF]
        rw [indicator_of_notMem (by simpa using hgt)]
      rw [h0]
      exact tendsto_const_nhds.congr'
        ((hev.filter_mono nhdsWithin_le_nhds).mono fun t ht => ht.symm)
  have hT' : Tendsto (fun t => ∫ r in Ioc 0 T, F t r) (𝓝[Icc 0 T] t0)
      (𝓝 (∫ r in Ioc 0 T, F t0 r)) :=
    tendsto_integral_filter_of_dominated_convergence (fun r => c * M * r ^ (-(1 : ℝ) / 2))
      (Filter.Eventually.of_forall hmeas) (Filter.Eventually.of_forall hbound) hbi hlim
  rw [ContinuousWithinAt, key t0 ht0]
  refine hT'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (key t ht).symm

end AbstractDuhamel

/-- Scalar `L²(𝕋^d)`. -/
noncomputable abbrev L2s (d : ℕ) := Lp ℝ 2 (haar d)
/-- Vector-valued `L²(𝕋^d; ℝ^d)`. -/
noncomputable abbrev L2v (d : ℕ) := Lp (Tangent d) 2 (haar d)

/-- Divergence of the componentwise periodic heat flow of a vector field. -/
noncomputable def divHeatFun (τ : ℝ) (F : Torus d → Tangent d) (y : Torus d) : ℝ :=
  ∑ j, coordPartial j (heatOp τ fun w => F w j) y

theorem divHeatFun_congr_ae (τ : ℝ) {F G : Torus d → Tangent d} (h : F =ᵐ[haar d] G) :
    divHeatFun τ F = divHeatFun τ G := by
  funext y
  unfold divHeatFun
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (fun w => F w j) =ᵐ[haar d] (fun w => G w j) := h.mono fun w hw => by simp [hw]
  have h2 : heatOp τ (fun w => F w j) = heatOp τ (fun w => G w j) := torusConv_congr_ae _ this
  rw [h2]

theorem integrable_kernel_pair {τ : ℝ} (hτ : 0 < τ) {f : Torus d → ℝ} (hf : Integrable f (haar d))
    (j : Fin d) (y : Torus d) :
    Integrable (fun w => f w *
      fderiv ℝ (Kh τ) (secE y - secE w) (EuclideanSpace.single j 1)) (haar d) := by
  have := (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1:ℝ) : Tangent d)).integrable_comp
      (integrable_smul_dKh hτ hf (secE y))
  simpa using this

theorem divHeatFun_add {τ : ℝ} (hτ : 0 < τ) {F G : Torus d → Tangent d}
    (hF : Integrable F (haar d)) (hG : Integrable G (haar d)) :
    divHeatFun τ (fun w => F w + G w) = fun y => divHeatFun τ F y + divHeatFun τ G y := by
  funext y
  unfold divHeatFun
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hFj : Integrable (fun w => F w j) (haar d) :=
    (EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).integrable_comp hF
  have hGj : Integrable (fun w => G w j) (haar d) :=
    (EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).integrable_comp hG
  have hsj : Integrable (fun w => (F w + G w) j) (haar d) := hFj.add hGj
  simp only [PiLp.add_apply] at hsj ⊢
  rw [coordPartial_heatOp hτ hsj, coordPartial_heatOp hτ hFj, coordPartial_heatOp hτ hGj,
    ← integral_add (integrable_kernel_pair hτ hFj j y) (integrable_kernel_pair hτ hGj j y)]
  congr 1; funext w; ring

theorem divHeatFun_smul {τ : ℝ} (hτ : 0 < τ) (c : ℝ) {F : Torus d → Tangent d}
    (hF : Integrable F (haar d)) :
    divHeatFun τ (fun w => c • F w) = fun y => c * divHeatFun τ F y := by
  funext y
  unfold divHeatFun
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hFj : Integrable (fun w => F w j) (haar d) :=
    (EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).integrable_comp hF
  have hsj : Integrable (fun w => (c • F w) j) (haar d) := by
    simpa using hFj.const_mul c
  simp only [PiLp.smul_apply, smul_eq_mul] at hsj ⊢
  rw [coordPartial_heatOp hτ hsj, coordPartial_heatOp hτ hFj, ← integral_const_mul]
  congr 1; funext w; ring

theorem eLpNorm_divHeatFun_le {τ : ℝ} (hτ : 0 < τ) {F : Torus d → Tangent d} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hF : MemLp F p (haar d)) :
    eLpNorm (divHeatFun τ F) p (haar d) ≤
      ENNReal.ofReal (Real.sqrt (d / 2) * τ ^ (-(1 : ℝ) / 2)) * eLpNorm F p (haar d) :=
  (periodized_heat_gradient_bounds hτ).2.2 hp hF

theorem memLp_divHeatFun {τ : ℝ} (hτ : 0 < τ) {F : Torus d → Tangent d} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hF : MemLp F p (haar d)) : MemLp (divHeatFun τ F) p (haar d) :=
  lt_of_le_of_lt (eLpNorm_divHeatFun_le hτ hp hF)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF.eLpNorm_lt_top)

/-- The bounded linear map `F ↦ div H_τ F` on `L²` (for `τ > 0`). -/
noncomputable def divHeatLin {τ : ℝ} (hτ : 0 < τ) : L2v d →ₗ[ℝ] L2s d where
  toFun F := (memLp_divHeatFun hτ one_le_two (Lp.memLp F)).toLp (divHeatFun τ F)
  map_add' F G := by
    refine Lp.ext ?_
    have h1 : divHeatFun τ ⇑(F + G) = fun y => divHeatFun τ ⇑F y + divHeatFun τ ⇑G y :=
      (divHeatFun_congr_ae τ (Lp.coeFn_add F G)).trans
        (divHeatFun_add hτ ((Lp.memLp F).integrable one_le_two)
          ((Lp.memLp G).integrable one_le_two))
    filter_upwards [MemLp.coeFn_toLp (memLp_divHeatFun hτ one_le_two (Lp.memLp (F + G))),
      Lp.coeFn_add ((memLp_divHeatFun hτ one_le_two (Lp.memLp F)).toLp (divHeatFun τ F))
        ((memLp_divHeatFun hτ one_le_two (Lp.memLp G)).toLp (divHeatFun τ G)),
      MemLp.coeFn_toLp (memLp_divHeatFun hτ one_le_two (Lp.memLp F)),
      MemLp.coeFn_toLp (memLp_divHeatFun hτ one_le_two (Lp.memLp G))] with y hy1 hy2 hy3 hy4
    rw [hy1, hy2, Pi.add_apply, hy3, hy4, h1]
  map_smul' c F := by
    refine Lp.ext ?_
    have h1 : divHeatFun τ ⇑(c • F) = fun y => c * divHeatFun τ ⇑F y :=
      (divHeatFun_congr_ae τ (Lp.coeFn_smul c F)).trans
        (divHeatFun_smul hτ c ((Lp.memLp F).integrable one_le_two))
    filter_upwards [MemLp.coeFn_toLp (memLp_divHeatFun hτ one_le_two (Lp.memLp (c • F))),
      Lp.coeFn_smul c ((memLp_divHeatFun hτ one_le_two (Lp.memLp F)).toLp (divHeatFun τ F)),
      MemLp.coeFn_toLp (memLp_divHeatFun hτ one_le_two (Lp.memLp F))] with y hy1 hy2 hy3
    rw [hy1, RingHom.id_apply, hy2, Pi.smul_apply, hy3, h1, smul_eq_mul]

theorem divHeatLin_apply {τ : ℝ} (hτ : 0 < τ) (F : L2v d) :
    divHeatLin hτ F = (memLp_divHeatFun hτ one_le_two (Lp.memLp F)).toLp (divHeatFun τ F) := rfl

theorem norm_divHeatLin_le {τ : ℝ} (hτ : 0 < τ) (F : L2v d) :
    ‖divHeatLin hτ F‖ ≤ Real.sqrt (d / 2) * τ ^ (-(1 : ℝ) / 2) * ‖F‖ := by
  rw [divHeatLin_apply, Lp.norm_toLp, Lp.norm_def]
  have h := eLpNorm_divHeatFun_le hτ one_le_two (Lp.memLp F)
  have hfin : ENNReal.ofReal (Real.sqrt (d / 2) * τ ^ (-(1 : ℝ) / 2)) * eLpNorm (⇑F) 2 (haar d) ≠ ∞ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.memLp F).eLpNorm_lt_top).ne
  have := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  exact this

/-- The continuous linear divergence-heat operator `F ↦ div H_τ F` (zero for `τ ≤ 0`). -/
noncomputable def divHeat (τ : ℝ) : L2v d →L[ℝ] L2s d :=
  if hτ : 0 < τ then
    LinearMap.mkContinuous (divHeatLin hτ) (Real.sqrt (d / 2) * τ ^ (-(1 : ℝ) / 2))
      (norm_divHeatLin_le hτ)
  else 0

theorem divHeat_apply {τ : ℝ} (hτ : 0 < τ) (F : L2v d) :
    divHeat τ F = (memLp_divHeatFun hτ one_le_two (Lp.memLp F)).toLp (divHeatFun τ F) := by
  simp only [divHeat, hτ, ↓reduceDIte]
  rfl

theorem norm_divHeat_apply_le {τ : ℝ} (hτ : 0 < τ) (F : L2v d) :
    ‖divHeat τ F‖ ≤ Real.sqrt (d / 2) * τ ^ (-(1 : ℝ) / 2) * ‖F‖ := by
  rw [divHeat_apply hτ]
  exact norm_divHeatLin_le hτ F

theorem coeFn_divHeat {τ : ℝ} (hτ : 0 < τ) (F : L2v d) :
    ⇑(divHeat τ F) =ᵐ[haar d] divHeatFun τ ⇑F := by
  rw [divHeat_apply hτ]
  exact MemLp.coeFn_toLp _

end DGPS.Lipschitz
