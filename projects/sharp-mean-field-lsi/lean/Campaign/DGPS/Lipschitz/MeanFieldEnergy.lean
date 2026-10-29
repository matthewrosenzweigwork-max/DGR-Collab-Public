import DGPS.Lipschitz.MeanFieldFlowPositivity
import DGPS.Lipschitz.MeanFieldGlobalFlow
import DGPS.Analysis.WeakConvolution

/-!
# Potential energy chain identity with weak first derivatives (LIP029)

For a weak solution `∂ₜ u = div J` (`IsWeakTimeDivergence`) with `J ∈ L²((0,T) × 𝕋^d)`:
* the weak identity extends from smooth test functions to `H¹` test functions
  (`weakForm_H1`), in particular to `V` with `∇V = G` weakly;
* for a continuous symmetric interaction `W` whose first derivative is `B` weakly, the
  quadratic interaction energy `½ ∬ W u u` satisfies the chain rule
  `d/dt ½ ∬ W u_t u_t = -∫ (B * u_t) · J_t`.
-/

open MeasureTheory Set Filter Topology
open scoped Real RealInnerProductSpace ComplexConjugate ENNReal

namespace DGPS.Lipschitz

section Part1

variable {d : ℕ}

theorem abs_integral_inner_le_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → Tangent d} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, ⟪f x, g x⟫ ∂μ| ≤ Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have e : ∫ x, ⟪f x, g x⟫ ∂μ = inner ℝ (hf.toLp f) (hg.toLp g) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [h1, h2]
  have n1 : ‖hf.toLp f‖ = Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) := by
    rw [← Real.sqrt_sq (norm_nonneg _), Lp_norm_sq_eq']
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with x h1
    rw [h1]
  have n2 : ‖hg.toLp g‖ = Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ) := by
    rw [← Real.sqrt_sq (norm_nonneg _), Lp_norm_sq_eq']
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp] with x h1
    rw [h1]
  rw [e, ← n1, ← n2]
  exact abs_real_inner_le_norm _ _

/-- The space-time test field `1_{[s,t]}(r) θ(x)`. -/
noncomputable def Wth (s t : ℝ) (θ : Torus d → Tangent d) (p : ℝ × Torus d) : Tangent d :=
  (Icc s t).indicator (fun _ => (1 : ℝ)) p.1 • θ p.2

theorem norm_Wth_le (s t : ℝ) (θ : Torus d → Tangent d) (p : ℝ × Torus d) :
    ‖Wth s t θ p‖ ≤ ‖θ p.2‖ := by
  unfold Wth
  rw [norm_smul]
  have h1 : ‖(Icc s t).indicator (fun _ => (1 : ℝ)) p.1‖ ≤ 1 := by
    by_cases hp : p.1 ∈ Icc s t <;> simp [hp]
  calc _ ≤ 1 * ‖θ p.2‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = _ := one_mul _

theorem memLp_snd_tmeas {T : ℝ} {θ : Torus d → Tangent d} (hθ : MemLp θ 2 (haar d)) :
    MemLp (fun p : ℝ × Torus d => θ p.2) 2 (tmeas d T) :=
  hθ.comp_snd (volume.restrict (Icc (0 : ℝ) T))

theorem memLp_Wth {T : ℝ} {θ : Torus d → Tangent d} (hθ : MemLp θ 2 (haar d)) (s t : ℝ) :
    MemLp (Wth s t θ) 2 (tmeas d T) := by
  refine (memLp_snd_tmeas (T := T) hθ).of_le ?_ (Eventually.of_forall fun p => norm_Wth_le s t θ p)
  unfold Wth
  exact (((measurable_const.indicator measurableSet_Icc).comp measurable_fst :
      Measurable fun p : ℝ × Torus d => (Icc s t).indicator (fun _ => (1 : ℝ)) p.1)).aestronglyMeasurable.smul
    hθ.aestronglyMeasurable.comp_snd

theorem Wth_sub (s t : ℝ) (θ ψ : Torus d → Tangent d) :
    Wth s t θ - Wth s t ψ = Wth s t (fun x => θ x - ψ x) := by
  funext p
  simp [Wth, smul_sub]

theorem integral_inner_Wth {T : ℝ} {θ : Torus d → Tangent d} (hθ : MemLp θ 2 (haar d))
    {F : ℝ × Torus d → Tangent d} (hF : MemLp F 2 (tmeas d T)) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t ≤ T) :
    IntervalIntegrable (fun r => ∫ x, ⟪F (r, x), θ x⟫ ∂haar d) volume s t ∧
    ∫ p, ⟪F p, Wth s t θ p⟫ ∂tmeas d T =
      ∫ r in s..t, ∫ x, ⟪F (r, x), θ x⟫ ∂haar d := by
  have hG : Integrable (fun p : ℝ × Torus d => ⟪F p, θ p.2⟫) (tmeas d T) :=
    integrable_inner_of_memLp_two hF (memLp_snd_tmeas hθ)
  have hI : Integrable (fun r => ∫ x, ⟪F (r, x), θ x⟫ ∂haar d)
      (volume.restrict (Icc (0 : ℝ) T)) := hG.integral_prod_left
  have hsub : Icc s t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc hs ht
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hst]
    exact hI.mono_measure (Measure.restrict_mono hsub le_rfl)
  · have e : ∀ p : ℝ × Torus d, ⟪F p, Wth s t θ p⟫ =
        (Icc s t).indicator (fun _ => (1 : ℝ)) p.1 * ⟪F p, θ p.2⟫ := by
      intro p
      unfold Wth
      rw [real_inner_smul_right]
    simp_rw [e]
    have hint : Integrable (fun p : ℝ × Torus d =>
        (Icc s t).indicator (fun _ => (1 : ℝ)) p.1 * ⟪F p, θ p.2⟫) (tmeas d T) :=
      hG.bdd_mul (c := 1) ((measurable_const.indicator measurableSet_Icc).comp
        measurable_fst).aestronglyMeasurable (Eventually.of_forall fun p => by
          by_cases hp : p.1 ∈ Icc s t <;> simp [hp])
    rw [integral_tmeas_eq hint]
    have e2 : ∀ r : ℝ, ∫ x, (Icc s t).indicator (fun _ => (1 : ℝ)) r * ⟪F (r, x), θ x⟫ ∂haar d =
        (Icc s t).indicator (fun r => ∫ x, ⟪F (r, x), θ x⟫ ∂haar d) r := by
      intro r
      by_cases hr : r ∈ Icc s t
      · simp [hr]
      · simp [hr]
    simp_rw [e2]
    rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.mpr hsub, intervalIntegral.integral_of_le hst, integral_Icc_eq_integral_Ioc]

theorem integral_sq_norm_Wth_le {T : ℝ} (hT : 0 ≤ T) {θ : Torus d → Tangent d}
    (hθ : MemLp θ 2 (haar d)) (s t : ℝ) :
    ∫ p, ‖Wth s t θ p‖ ^ 2 ∂tmeas d T ≤ T * ∫ x, ‖θ x‖ ^ 2 ∂haar d := by
  have h1 : Integrable (fun p : ℝ × Torus d => ‖Wth s t θ p‖ ^ 2) (tmeas d T) :=
      (memLp_two_iff_integrable_sq_norm (memLp_Wth (T := T) hθ s t).aestronglyMeasurable).1
        (memLp_Wth hθ s t)
  have h2 : Integrable (fun p : ℝ × Torus d => ‖θ p.2‖ ^ 2) (tmeas d T) :=
      (memLp_two_iff_integrable_sq_norm (memLp_snd_tmeas (T := T) hθ).aestronglyMeasurable).1
      (memLp_snd_tmeas hθ)
  calc ∫ p, ‖Wth s t θ p‖ ^ 2 ∂tmeas d T ≤ ∫ p : ℝ × Torus d, ‖θ p.2‖ ^ 2 ∂tmeas d T :=
        integral_mono h1 h2 fun p => by
          have := norm_Wth_le s t θ p
          exact pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = T * ∫ x, ‖θ x‖ ^ 2 ∂haar d := by
        rw [show tmeas d T = (volume.restrict (Icc (0 : ℝ) T)).prod (haar d) from rfl,
          integral_fun_snd (fun x => ‖θ x‖ ^ 2)]
        simp [Measure.real, hT]

theorem memLp_gradT {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) :
    MemLp (gradT φ) 2 (haar d) := by
  obtain ⟨C, hC⟩ := exists_bound_gradT hφ
  exact (MemLp.of_bound (continuous_gradT hφ).aestronglyMeasurable C
    (Eventually.of_forall hC))

theorem fourierCutoffGrad_eq_gradT {φ : Torus d → ℝ} {ψ : Torus d → Tangent d}
    (hφ : IsWeakGradient φ ψ) (R : ℝ) :
    fourierCutoffGrad ψ R = gradT (fourierCutoff φ R) := by
  funext x
  ext j
  rw [fourierCutoffGrad_apply hφ]
  rfl

/-- The weak form of `∂ₜ u = div J` extends from smooth to `H¹` test functions. -/
theorem weakForm_H1 {T : ℝ} {u : ℝ → Torus d → ℝ} {J : ℝ → Torus d → Tangent d}
    (hdiv : ParabolicChainRule.IsWeakTimeDivergence T u J) (hu2 : ∀ t ∈ Icc (0 : ℝ) T, MemLp (u t) 2 (haar d))
    (hJ2 : MemLp (fun p : ℝ × Torus d => J p.1 p.2) 2 (tmeas d T))
    {φ : Torus d → ℝ} {ψ : Torus d → Tangent d} (hφ : IsWeakGradient φ ψ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    IntervalIntegrable (fun r => ∫ x, ⟪J r x, ψ x⟫ ∂haar d) volume s t ∧
    ∫ x, u t x * φ x ∂haar d - ∫ x, u s x * φ x ∂haar d =
      -∫ r in s..t, ∫ x, ⟪J r x, ψ x⟫ ∂haar d := by
  have hT : 0 ≤ T := hs.trans (hst.trans ht)
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs, hst.trans ht⟩
  have htT : t ∈ Icc (0 : ℝ) T := ⟨hs.trans hst, ht⟩
  refine ⟨(integral_inner_Wth hφ.memLp_grad hJ2 hs hst ht).1, ?_⟩
  set θ : ℕ → Torus d → Tangent d := fun n => fourierCutoffGrad ψ (n : ℝ) with hθdef
  have hθ : ∀ n, θ n = gradT (fourierCutoff φ (n : ℝ)) := fun n =>
    fourierCutoffGrad_eq_gradT hφ _
  have hφn : ∀ n : ℕ, IsSmoothPeriodic (fourierCutoff φ (n : ℝ)) := fun n =>
    isSmoothPeriodic_psum _ _
  have hθL2 : ∀ n, MemLp (θ n) 2 (haar d) := fun n => by
    rw [hθ n]; exact memLp_gradT (hφn n)
  -- the identity for each cutoff
  have hn : ∀ n : ℕ, ∫ x, u t x * fourierCutoff φ (n : ℝ) x ∂haar d -
      ∫ x, u s x * fourierCutoff φ (n : ℝ) x ∂haar d =
      -∫ p, ⟪J p.1 p.2, Wth s t (θ n) p⟫ ∂tmeas d T := by
    intro n
    rw [hdiv.weak _ (hφn n) s t hs hst ht]
    have := (integral_inner_Wth (hθL2 n) hJ2 hs hst ht).2
    simp only at this
    rw [this]
    congr 2
    funext r
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show _ = ⟪J r x, θ n x⟫
    rw [hθ n, inner_gradT]
  -- left side converges
  have hL : ∀ τ ∈ Icc (0 : ℝ) T, Tendsto (fun n : ℕ => ∫ x, u τ x * fourierCutoff φ (n : ℝ) x ∂haar d)
      atTop (𝓝 (∫ x, u τ x * φ x ∂haar d)) := by
    intro τ hτ
    have := tendsto_integral_mul_of_sq (a := fun n : ℕ => fourierCutoff φ (n : ℝ)) (a0 := φ)
      (ψ := u τ) (fun n => memLp_two_of_continuous (hφn n).continuous_torus) hφ.memLp (hu2 τ hτ)
      ((tendsto_integral_sq_fourierCutoff_sub hφ.memLp).comp tendsto_natCast_atTop_atTop)
    simpa only [mul_comm] using this
  have hL' := (hL t htT).sub (hL s hsT)
  -- right side converges
  set I : ℕ → ℝ := fun n => ∫ p, ⟪J p.1 p.2, Wth s t (θ n) p⟫ ∂tmeas d T with hI
  set I0 : ℝ := ∫ p, ⟪J p.1 p.2, Wth s t ψ p⟫ ∂tmeas d T with hI0
  have hR : Tendsto I atTop (𝓝 I0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    set nJ := Real.sqrt (∫ p, ‖J p.1 p.2‖ ^ 2 ∂tmeas d T)
    have hb : Tendsto (fun n : ℕ => nJ * Real.sqrt (T * ∫ x, ‖θ n x - ψ x‖ ^ 2 ∂haar d))
        atTop (𝓝 0) := by
      have h1 := ((tendsto_integral_norm_sq_cutoffGrad_sub hφ.memLp_grad).comp
        tendsto_natCast_atTop_atTop).const_mul T
      have h2 := (Real.continuous_sqrt.tendsto _).comp h1
      simpa using h2.const_mul nJ
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hb
    have hW1 := memLp_Wth (T := T) (hθL2 n) s t
    have hW2 := memLp_Wth (T := T) hφ.memLp_grad s t
    have e : I n - I0 = ∫ p, ⟪J p.1 p.2, Wth s t (fun x => θ n x - ψ x) p⟫ ∂tmeas d T := by
      rw [hI, hI0]
      rw [← integral_sub (integrable_inner_of_memLp_two hJ2 hW1)
        (integrable_inner_of_memLp_two hJ2 hW2)]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      rw [← Wth_sub]
      simp [inner_sub_right]
    have hW3 : MemLp (Wth s t (fun x => θ n x - ψ x)) 2 (tmeas d T) :=
      memLp_Wth ((hθL2 n).sub hφ.memLp_grad) s t
    rw [e, Real.norm_eq_abs]
    refine (abs_integral_inner_le_sqrt hJ2 hW3).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
    exact integral_sq_norm_Wth_le hT ((hθL2 n).sub hφ.memLp_grad) s t
  have hI0e : I0 = ∫ r in s..t, ∫ x, ⟪J r x, ψ x⟫ ∂haar d :=
    (integral_inner_Wth hφ.memLp_grad hJ2 hs hst ht).2
  have h1 : Tendsto (fun n : ℕ => -I n) atTop (𝓝 (-I0)) := hR.neg
  have h2 : Tendsto (fun n : ℕ => -I n) atTop
      (𝓝 (∫ x, u t x * φ x ∂haar d - ∫ x, u s x * φ x ∂haar d)) := by
    refine hL'.congr fun n => ?_
    exact hn n
  rw [tendsto_nhds_unique h2 h1, hI0e]

end Part1


section Part3A

variable {d : ℕ}

/-- The convolution `x ↦ ∫ W(x,y) f(y) dm(y)`. -/
noncomputable def Wc (W : Torus d → Torus d → ℝ) (f : Torus d → ℝ) (x : Torus d) : ℝ :=
  ∫ y, W x y * f y ∂haar d

/-- The vector convolution `x ↦ ∫ f(y) B(x,y) dm(y)`. -/
noncomputable def Bc (B : Torus d → Torus d → Tangent d) (f : Torus d → ℝ) (x : Torus d) :
    Tangent d :=
  ∫ y, f y • B x y ∂haar d

/-- The quadratic interaction form `∬ W(x,y) f(x) f(y)`. -/
noncomputable def quadE (W : Torus d → Torus d → ℝ) (f : Torus d → ℝ) : ℝ :=
  ∫ p, W p.1 p.2 * (f p.1 * f p.2) ∂(haar d).prod (haar d)

theorem energy_integrable_inner_bdd {θ j : Torus d → Tangent d} {c : ℝ}
    (hθ : AEStronglyMeasurable θ (haar d)) (hbd : ∀ x, ‖θ x‖ ≤ c)
    (hj : Integrable j (haar d)) : Integrable (fun x => ⟪j x, θ x⟫) (haar d) := by
  refine Integrable.mono' (hj.norm.mul_const c) (hj.aestronglyMeasurable.inner hθ)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hbd x) (norm_nonneg _))

theorem abs_integral_inner_bdd_le {θ j : Torus d → Tangent d} {c : ℝ}
    (hbd : ∀ x, ‖θ x‖ ≤ c) (hj : Integrable j (haar d)) :
    |∫ x, ⟪j x, θ x⟫ ∂haar d| ≤ c * ∫ x, ‖j x‖ ∂haar d := by
  have := norm_integral_le_of_norm_le (μ := haar d) (f := fun x => ⟪j x, θ x⟫)
    (g := fun x => ‖j x‖ * c) (hj.norm.mul_const c) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hbd x) (norm_nonneg _)))
  rw [integral_mul_const, mul_comm] at this
  simpa [Real.norm_eq_abs] using this

variable {B : Torus d → Torus d → Tangent d} {b : ℝ}

theorem integrable_Bc_slice (hBm : Measurable fun p : Torus d × Torus d => B p.1 p.2)
    (hbB : ∀ x y, ‖B x y‖ ≤ b) {f : Torus d → ℝ} (hf : Integrable f (haar d)) (x : Torus d) :
    Integrable (fun y => f y • B x y) (haar d) :=
  integrable_smul_slice hBm hf (M := b) (Eventually.of_forall fun y => hbB x y)

theorem norm_Bc_le (hbB : ∀ x y, ‖B x y‖ ≤ b) {f : Torus d → ℝ} (hf : Integrable f (haar d))
    (x : Torus d) : ‖Bc B f x‖ ≤ b * ∫ y, |f y| ∂haar d :=
  norm_integral_smul_le hf (Eventually.of_forall fun y => hbB x y)

theorem norm_Bc_sub_le (hBm : Measurable fun p : Torus d × Torus d => B p.1 p.2)
    (hbB : ∀ x y, ‖B x y‖ ≤ b) {f g : Torus d → ℝ} (hf : Integrable f (haar d))
    (hg : Integrable g (haar d)) (x : Torus d) :
    ‖Bc B f x - Bc B g x‖ ≤ b * ∫ y, |f y - g y| ∂haar d := by
  have e : Bc B f x - Bc B g x = ∫ y, (f y - g y) • B x y ∂haar d := by
    unfold Bc
    rw [← integral_sub (integrable_Bc_slice hBm hbB hf x) (integrable_Bc_slice hBm hbB hg x)]
    simp only [sub_smul]
  rw [e]
  exact norm_integral_smul_le (hf.sub hg) (Eventually.of_forall fun y => hbB x y)

theorem Bc_add (hBm : Measurable fun p : Torus d × Torus d => B p.1 p.2)
    (hbB : ∀ x y, ‖B x y‖ ≤ b) {f g : Torus d → ℝ} (hf : Integrable f (haar d))
    (hg : Integrable g (haar d)) (x : Torus d) :
    Bc B (fun y => f y + g y) x = Bc B f x + Bc B g x := by
  unfold Bc
  rw [← integral_add (integrable_Bc_slice hBm hbB hf x) (integrable_Bc_slice hBm hbB hg x)]
  simp only [add_smul]

theorem stronglyMeasurable_Bc (hBm : Measurable fun p : Torus d × Torus d => B p.1 p.2)
    {f : Torus d → ℝ} (hf : StronglyMeasurable f) : StronglyMeasurable (Bc B f) := by
  unfold Bc
  exact ((hf.comp_measurable measurable_snd).smul hBm.stronglyMeasurable).integral_prod_right'

end Part3A


section Part3B

variable {d : ℕ} {W : Torus d → Torus d → ℝ} {B : Torus d → Torus d → Tangent d} {b : ℝ}

/-- The bilinear form `Q(f,g) = ∬ W(x,y) f(x) g(y)`. -/
noncomputable def Qf (W : Torus d → Torus d → ℝ) (f g : Torus d → ℝ) : ℝ :=
  ∫ p, W p.1 p.2 * (f p.1 * g p.2) ∂(haar d).prod (haar d)

theorem integrable_quadForm (hWc : Continuous fun p : Torus d × Torus d => W p.1 p.2)
    {f g : Torus d → ℝ} (hf : Integrable f (haar d)) (hg : Integrable g (haar d)) :
    Integrable (fun p : Torus d × Torus d => W p.1 p.2 * (f p.1 * g p.2))
      ((haar d).prod (haar d)) := by
  obtain ⟨C, hC⟩ := exists_bound_continuous_prod hWc
  exact (hf.mul_prod hg).bdd_mul hWc.aestronglyMeasurable
    (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hC _ _)

theorem Qf_eq_integral (hWc : Continuous fun p : Torus d × Torus d => W p.1 p.2)
    {f g : Torus d → ℝ} (hf : Integrable f (haar d)) (hg : Integrable g (haar d)) :
    Qf W f g = ∫ x, f x * Wc W g x ∂haar d := by
  unfold Qf Wc
  rw [integral_prod _ (integrable_quadForm hWc hf hg)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show ∫ y, W x y * (f x * g y) ∂haar d = f x * ∫ y, W x y * g y ∂haar d
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  ring

theorem Qf_comm (hsym : ∀ x y, W x y = W y x) (f g : Torus d → ℝ) :
    Qf W g f = Qf W f g := by
  unfold Qf
  rw [← integral_prod_swap (μ := haar d) (ν := haar d)
    (fun p : Torus d × Torus d => W p.1 p.2 * (f p.1 * g p.2))]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [hsym p.2 p.1]
  ring

theorem quadE_sub_eq (hWc : Continuous fun p : Torus d × Torus d => W p.1 p.2)
    (hsym : ∀ x y, W x y = W y x) {a c : Torus d → ℝ} (ha : Integrable a (haar d))
    (hc : Integrable c (haar d)) :
    quadE W c - quadE W a = ∫ x, (c x - a x) * Wc W (fun y => a y + c y) x ∂haar d := by
  have h0 := Qf_eq_integral hWc (hc.sub ha) (ha.add hc)
  have h1 : (∫ x, (c x - a x) * Wc W (fun y => a y + c y) x ∂haar d) =
      Qf W (fun x => c x - a x) (fun y => a y + c y) := h0.symm
  rw [h1]
  unfold Qf quadE
  have e : (fun p : Torus d × Torus d => W p.1 p.2 * ((c p.1 - a p.1) * (a p.2 + c p.2))) =
      fun p => (W p.1 p.2 * (c p.1 * a p.2) + W p.1 p.2 * (c p.1 * c p.2)) -
        (W p.1 p.2 * (a p.1 * a p.2) + W p.1 p.2 * (a p.1 * c p.2)) := by
    funext p; ring
  have i1 := integrable_quadForm hWc hc ha
  have i2 := integrable_quadForm hWc hc hc
  have i3 := integrable_quadForm hWc ha ha
  have i4 := integrable_quadForm hWc ha hc
  rw [e]
  have h5 := integral_sub (i1.add i2) (i3.add i4)
  have h6 := integral_add i1 i2
  have h7 := integral_add i3 i4
  simp only [Pi.add_apply] at h5 h6 h7
  rw [h5, h6, h7]
  have := Qf_comm hsym a c
  unfold Qf at this
  rw [this]
  ring

end Part3B


section Part3C

variable {d : ℕ} {W : Torus d → Torus d → ℝ} {B : Torus d → Torus d → Tangent d} {b : ℝ}
variable {T : ℝ} {u : ℝ → L2s d} {J : ℝ → Torus d → Tangent d}

theorem integrable_L2s (v : L2s d) : Integrable (⇑v) (haar d) :=
  (Lp.memLp v).integrable one_le_two

theorem isWeakGradient_Wc_Bc (hWc : Continuous fun p : Torus d × Torus d => W p.1 p.2)
    (hBm : Measurable fun p : Torus d × Torus d => B p.1 p.2) (hbB : ∀ x y, ‖B x y‖ ≤ b)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ∞ (fun x => W x y) (fun x => B x y))
    {ρ : Torus d → ℝ} (hρ : Integrable ρ (haar d)) :
    IsWeakGradient (Wc W ρ) (Bc B ρ) := by
  have hB : MemLp (fun p : Torus d × Torus d => B p.1 p.2) ∞ ((haar d).prod (haar d)) :=
    MemLp.of_bound hBm.aestronglyMeasurable b (Eventually.of_forall fun p => hbB p.1 p.2)
  have h := isWeakGradientLp_convolution hWc hBm hB hWB hρ
  exact isWeakGradient_iff_isWeakGradientLp.mpr
    ⟨h.memLp.mono_exponent le_top, h.memLp_grad.mono_exponent le_top, h.ibp⟩

/-- One step of the chain rule: for `0 ≤ a ≤ c ≤ T`. -/
theorem quad_step (hdiv : ParabolicChainRule.IsWeakTimeDivergence T (fun t => ⇑(u t)) J)
    (hJ2 : MemLp (fun p : ℝ × Torus d => J p.1 p.2) 2 (tmeas d T))
    (hWc : Continuous fun p : Torus d × Torus d => W p.1 p.2)
    (hsym : ∀ x y, W x y = W y x)
    (hBm : Measurable fun p : Torus d × Torus d => B p.1 p.2) (hbB : ∀ x y, ‖B x y‖ ≤ b)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ∞ (fun x => W x y) (fun x => B x y))
    {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ T) :
    IntervalIntegrable
      (fun r => ∫ x, ⟪J r x, Bc B (fun y => u a y + u c y) x⟫ ∂haar d) volume a c ∧
    quadE W (⇑(u c)) - quadE W (⇑(u a)) =
      -∫ r in a..c, ∫ x, ⟪J r x, Bc B (fun y => u a y + u c y) x⟫ ∂haar d := by
  have hρ : Integrable (fun y => u a y + u c y) (haar d) :=
    (integrable_L2s (u a)).add (integrable_L2s (u c))
  have hφ := isWeakGradient_Wc_Bc hWc hBm hbB hWB hρ
  obtain ⟨hint, hw⟩ := weakForm_H1 hdiv (fun t _ => Lp.memLp (u t)) hJ2 hφ ha hac hc
  refine ⟨hint, ?_⟩
  rw [← hw, quadE_sub_eq hWc hsym (integrable_L2s (u a)) (integrable_L2s (u c))]
  refine Eq.trans ?_ (integral_sub ((Lp.memLp (u c)).integrable_mul hφ.memLp)
      ((Lp.memLp (u a)).integrable_mul hφ.memLp))
  exact integral_congr_ae (Eventually.of_forall fun x => sub_mul _ _ _)

end Part3C


section Tele

theorem tele_abstract {E F m : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hF : IntervalIntegrable F volume s t) (hm : IntervalIntegrable m volume s t)
    (h : ∀ ε > 0, ∃ δ > 0, ∀ a c : ℝ, s ≤ a → a ≤ c → c ≤ t → c - a ≤ δ →
      |E c - E a + ∫ r in a..c, F r| ≤ ε * ∫ r in a..c, m r) :
    E t - E s + ∫ r in s..t, F r = 0 := by
  have key : ∀ ε > 0, |E t - E s + ∫ r in s..t, F r| ≤ ε * ∫ r in s..t, m r := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt ((t - s) / δ)
    have hN0 : (0 : ℝ) < N := by
      have : (0 : ℝ) ≤ (t - s) / δ := div_nonneg (by linarith) hδ.le
      linarith
    set a : ℕ → ℝ := fun k => s + k * ((t - s) / N) with ha
    have ha0 : a 0 = s := by simp [ha]
    have haN : a N = t := by
      simp only [ha]
      field_simp
      ring
    have hstep : ∀ k, a (k + 1) - a k = (t - s) / N := by
      intro k; simp only [ha]; push_cast; ring
    have hstep_nn : 0 ≤ (t - s) / (N : ℝ) := div_nonneg (by linarith) hN0.le
    have hstep_le : (t - s) / (N : ℝ) ≤ δ := by
      rw [div_le_iff₀ hN0]
      rw [div_lt_iff₀ hδ] at hN
      linarith
    have hmono : ∀ k, a k ≤ a (k + 1) := fun k => by linarith [hstep k]
    have hge : ∀ k, s ≤ a k := by
      intro k; simp only [ha]
      have : 0 ≤ (k : ℝ) * ((t - s) / N) := mul_nonneg (Nat.cast_nonneg _) hstep_nn
      linarith
    have hle : ∀ k, k ≤ N → a k ≤ t := by
      intro k hk
      simp only [ha]
      have h1 : (k : ℝ) * ((t - s) / N) ≤ N * ((t - s) / N) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hstep_nn
      have h2 : (N : ℝ) * ((t - s) / N) = t - s := by field_simp
      linarith
    have hsub : ∀ k, k < N → Set.uIcc (a k) (a (k + 1)) ⊆ Set.uIcc s t := by
      intro k hk
      rw [Set.uIcc_of_le (hmono k), Set.uIcc_of_le hst]
      exact Set.Icc_subset_Icc (hge k) (hle (k + 1) hk)
    have e1 : ∑ k ∈ Finset.range N, (E (a (k + 1)) - E (a k)) = E t - E s := by
      rw [Finset.sum_range_sub (fun k => E (a k))]
      rw [ha0, haN]
    have e2 : ∑ k ∈ Finset.range N, ∫ r in a k..a (k + 1), F r = ∫ r in s..t, F r := by
      have := intervalIntegral.sum_integral_adjacent_intervals (f := F) (μ := volume) (a := a)
        (n := N) (fun k hk => hF.mono_set (hsub k hk))
      rwa [ha0, haN] at this
    have e3 : ∑ k ∈ Finset.range N, ∫ r in a k..a (k + 1), m r = ∫ r in s..t, m r := by
      have := intervalIntegral.sum_integral_adjacent_intervals (f := m) (μ := volume) (a := a)
        (n := N) (fun k hk => hm.mono_set (hsub k hk))
      rwa [ha0, haN] at this
    have e4 : E t - E s + ∫ r in s..t, F r = ∑ k ∈ Finset.range N,
        (E (a (k + 1)) - E (a k) + ∫ r in a k..a (k + 1), F r) := by
      rw [Finset.sum_add_distrib, e1, e2]
    rw [e4]
    calc |∑ k ∈ Finset.range N, (E (a (k + 1)) - E (a k) + ∫ r in a k..a (k + 1), F r)|
        ≤ ∑ k ∈ Finset.range N, |E (a (k + 1)) - E (a k) + ∫ r in a k..a (k + 1), F r| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range N, ε * ∫ r in a k..a (k + 1), m r := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' := Finset.mem_range.mp hk
          refine hδ' _ _ (hge k) (hmono k) (hle (k + 1) hk') ?_
          rw [hstep k]; exact hstep_le
      _ = ε * ∫ r in s..t, m r := by rw [← Finset.mul_sum, e3]
  by_contra hX
  have hpos : 0 < |E t - E s + ∫ r in s..t, F r| := abs_pos.mpr hX
  have hM := key 1 one_pos
  have hMpos : 0 < ∫ r in s..t, m r := by linarith
  have := key (|E t - E s + ∫ r in s..t, F r| / (2 * ∫ r in s..t, m r)) (by positivity)
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
  nlinarith

end Tele

section Part4

variable {d : ℕ} {B : Torus d → Torus d → Tangent d} {b : ℝ}
variable {T : ℝ} {u : ℝ → L2s d} {J : ℝ → Torus d → Tangent d}

/-- The flux of `J_r` against `B ∗ u_τ`. -/
noncomputable def Fl (B : Torus d → Torus d → Tangent d) (u : ℝ → L2s d)
    (J : ℝ → Torus d → Tangent d) (τ r : ℝ) : ℝ :=
  ∫ x, ⟪J r x, Bc B (u τ) x⟫ ∂haar d

theorem stronglyMeasurable_Fl (hBm : Measurable fun p : Torus d × Torus d => B p.1 p.2)
    (hJm : Measurable fun p : ℝ × Torus d => J p.1 p.2) (τ : ℝ) :
    StronglyMeasurable (fun r => Fl B u J τ r) := by
  have hBc : Measurable (Bc B (u τ)) :=
    (stronglyMeasurable_Bc hBm (Lp.stronglyMeasurable (u τ))).measurable
  have : Measurable fun p : ℝ × Torus d => ⟪J p.1 p.2, Bc B (u τ) p.2⟫ :=
    hJm.inner (hBc.comp measurable_snd)
  exact this.stronglyMeasurable.integral_prod_right' (ν := haar d)

theorem abs_Fl_le (hbB : ∀ x y, ‖B x y‖ ≤ b) {r : ℝ} (hr : Integrable (J r) (haar d)) (τ : ℝ) :
    |Fl B u J τ r| ≤ (b * ∫ y, |u τ y| ∂haar d) * ∫ x, ‖J r x‖ ∂haar d :=
  abs_integral_inner_bdd_le (fun x => norm_Bc_le hbB (integrable_L2s (u τ)) x) hr

theorem abs_Fl_sub_le (hBm : Measurable fun p : Torus d × Torus d => B p.1 p.2)
    (hbB : ∀ x y, ‖B x y‖ ≤ b) {r : ℝ} (hr : Integrable (J r) (haar d)) (τ σ : ℝ) :
    |Fl B u J τ r - Fl B u J σ r| ≤
      (b * ∫ y, |u τ y - u σ y| ∂haar d) * ∫ x, ‖J r x‖ ∂haar d := by
  have hm : ∀ ρ : ℝ, AEStronglyMeasurable (Bc B (u ρ)) (haar d) := fun ρ =>
    (stronglyMeasurable_Bc hBm (Lp.stronglyMeasurable (u ρ))).aestronglyMeasurable
  have hb : ∀ ρ x, ‖Bc B (u ρ) x‖ ≤ b * ∫ y, |u ρ y| ∂haar d := fun ρ x =>
    norm_Bc_le hbB (integrable_L2s (u ρ)) x
  have i1 := energy_integrable_inner_bdd (hm τ) (hb τ) hr
  have i2 := energy_integrable_inner_bdd (hm σ) (hb σ) hr
  have e : Fl B u J τ r - Fl B u J σ r =
      ∫ x, ⟪J r x, Bc B (u τ) x - Bc B (u σ) x⟫ ∂haar d := by
    unfold Fl
    rw [← integral_sub i1 i2]
    simp only [inner_sub_right]
  rw [e]
  exact abs_integral_inner_bdd_le
    (fun x => norm_Bc_sub_le hBm hbB (integrable_L2s _) (integrable_L2s _) x) hr

/-- The dyadic-type floor approximation of `r`. -/
noncomputable def tauN (N : ℕ) (r : ℝ) : ℝ := (⌊((N : ℝ) + 1) * r⌋ : ℝ) / ((N : ℝ) + 1)

theorem tauN_le (N : ℕ) (r : ℝ) : tauN N r ≤ r := by
  unfold tauN
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hN, mul_comm]
  exact Int.floor_le _

theorem lt_tauN (N : ℕ) (r : ℝ) : r - 1 / ((N : ℝ) + 1) < tauN N r := by
  unfold tauN
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [lt_div_iff₀ hN]
  have h : (r - 1 / ((N : ℝ) + 1)) * ((N : ℝ) + 1) = ((N : ℝ) + 1) * r - 1 := by
    field_simp
  rw [h]
  have := Int.lt_floor_add_one (((N : ℝ) + 1) * r)
  linarith

theorem tauN_nonneg (N : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ tauN N r := by
  unfold tauN
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  exact div_nonneg (by exact_mod_cast Int.floor_nonneg.mpr (by positivity)) hN.le

theorem tendsto_tauN (r : ℝ) : Tendsto (fun N : ℕ => tauN N r) atTop (𝓝 r) := by
  have h1 : Tendsto (fun N : ℕ => r - 1 / ((N : ℝ) + 1)) atTop (𝓝 r) := by
    simpa using (tendsto_const_nhds (x := r)).sub tendsto_one_div_add_atTop_nhds_zero_nat
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds
    (fun N => (lt_tauN N r).le) (fun N => tauN_le N r)

theorem stronglyMeasurable_Fn (hBm : Measurable fun p : Torus d × Torus d => B p.1 p.2)
    (hJm : Measurable fun p : ℝ × Torus d => J p.1 p.2) (N : ℕ) :
    StronglyMeasurable (fun r => Fl B u J (tauN N r) r) := by
  have hG : Measurable (fun p : ℝ × ℤ => Fl B u J ((p.2 : ℝ) / ((N : ℝ) + 1)) p.1) :=
    measurable_from_prod_countable_left
      (fun k => (stronglyMeasurable_Fl hBm hJm ((k : ℝ) / ((N : ℝ) + 1))).measurable)
  have hf : Measurable fun r : ℝ => (r, ⌊((N : ℝ) + 1) * r⌋) :=
    measurable_id.prodMk (Int.measurable_floor.comp (measurable_const.mul measurable_id))
  exact (hG.comp hf).stronglyMeasurable

theorem aestronglyMeasurable_Fd (hBm : Measurable fun p : Torus d × Torus d => B p.1 p.2)
    (hbB : ∀ x y, ‖B x y‖ ≤ b) (hb0 : 0 ≤ b)
    (hJm : Measurable fun p : ℝ × Torus d => J p.1 p.2)
    (hcont : ContinuousOn u (Icc 0 T))
    (hJae : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), Integrable (J r) (haar d)) :
    AEStronglyMeasurable (fun r => Fl B u J r r) (volume.restrict (Icc (0 : ℝ) T)) := by
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun N r => Fl B u J (tauN N r) r)
    (fun N => (stronglyMeasurable_Fn hBm hJm N).aestronglyMeasurable) ?_
  filter_upwards [hJae, ae_restrict_mem measurableSet_Icc] with r hr hrI
  have hut : Tendsto (fun N : ℕ => u (tauN N r)) atTop (𝓝 (u r)) := by
    refine (hcont r hrI).tendsto.comp ?_
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_tauN r, Eventually.of_forall fun N => ?_⟩
    exact ⟨tauN_nonneg N hrI.1, (tauN_le N r).trans hrI.2⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hu' : Tendsto (fun N : ℕ => ‖u (tauN N r) - u r‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hut
  have h2 : Tendsto (fun N : ℕ => (b * ‖u (tauN N r) - u r‖) * ∫ x, ‖J r x‖ ∂haar d)
      atTop (𝓝 0) := by
    simpa using (hu'.const_mul b).mul_const (∫ x, ‖J r x‖ ∂haar d)
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) h2
  rw [Real.norm_eq_abs]
  refine (abs_Fl_sub_le hBm hbB hr _ _).trans ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hb0)
    (integral_nonneg fun x => norm_nonneg _)
  have := n1_le_norm (u (tauN N r) - u r)
  rwa [n1_sub_L2s] at this

theorem integrable_Fd (hBm : Measurable fun p : Torus d × Torus d => B p.1 p.2)
    (hbB : ∀ x y, ‖B x y‖ ≤ b) (hb0 : 0 ≤ b)
    (hdiv : ParabolicChainRule.IsWeakTimeDivergence T (fun t => ⇑(u t)) J)
    (hcont : ContinuousOn u (Icc 0 T)) :
    Integrable (fun r => Fl B u J r r) (volume.restrict (Icc (0 : ℝ) T)) := by
  have hJae : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), Integrable (J r) (haar d) :=
    hdiv.integrable_J.prod_right_ae
  have hmi : Integrable (fun r => ∫ x, ‖J r x‖ ∂haar d) (volume.restrict (Icc (0 : ℝ) T)) :=
    hdiv.integrable_J.norm.integral_prod_left
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine Integrable.mono' (hmi.const_mul (b * C))
    (aestronglyMeasurable_Fd hBm hbB hb0 hdiv.measurable_J hcont hJae) ?_
  filter_upwards [hJae, ae_restrict_mem measurableSet_Icc] with r hr hrI
  rw [Real.norm_eq_abs]
  refine (abs_Fl_le hbB hr r).trans ?_
  have h1 : ∫ y, |u r y| ∂haar d ≤ C := (n1_le_norm (u r)).trans (hC r hrI)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hb0)
    (integral_nonneg fun _ => norm_nonneg _)

end Part4

section Part5

variable {d : ℕ} {W : Torus d → Torus d → ℝ} {B : Torus d → Torus d → Tangent d} {b : ℝ}
variable {T : ℝ} {u : ℝ → L2s d} {J : ℝ → Torus d → Tangent d}

theorem int_abs_sub_le_norm (a c : L2s d) : ∫ y, |a y - c y| ∂haar d ≤ ‖a - c‖ := by
  have := n1_le_norm (a - c)
  rwa [n1_sub_L2s] at this

theorem Fl_add (hBm : Measurable fun p : Torus d × Torus d => B p.1 p.2)
    (hbB : ∀ x y, ‖B x y‖ ≤ b) {r : ℝ} (hr : Integrable (J r) (haar d)) (τ σ : ℝ) :
    ∫ x, ⟪J r x, Bc B (fun y => u τ y + u σ y) x⟫ ∂haar d = Fl B u J τ r + Fl B u J σ r := by
  have hm : ∀ ρ : ℝ, AEStronglyMeasurable (Bc B (u ρ)) (haar d) := fun ρ =>
    (stronglyMeasurable_Bc hBm (Lp.stronglyMeasurable (u ρ))).aestronglyMeasurable
  have hb : ∀ ρ x, ‖Bc B (u ρ) x‖ ≤ b * ∫ y, |u ρ y| ∂haar d := fun ρ x =>
    norm_Bc_le hbB (integrable_L2s (u ρ)) x
  have i1 := energy_integrable_inner_bdd (hm τ) (hb τ) hr
  have i2 := energy_integrable_inner_bdd (hm σ) (hb σ) hr
  unfold Fl
  rw [← integral_add i1 i2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show ⟪J r x, Bc B (fun y => u τ y + u σ y) x⟫ = ⟪J r x, Bc B (u τ) x⟫ + ⟪J r x, Bc B (u σ) x⟫
  rw [Bc_add hBm hbB (integrable_L2s (u τ)) (integrable_L2s (u σ)) x, inner_add_right]

theorem quad_chain_core
    (hdiv : ParabolicChainRule.IsWeakTimeDivergence T (fun t => ⇑(u t)) J)
    (hJ2 : MemLp (fun p : ℝ × Torus d => J p.1 p.2) 2 (tmeas d T))
    (hcont : ContinuousOn u (Icc 0 T))
    (hWc : Continuous fun p : Torus d × Torus d => W p.1 p.2)
    (hsym : ∀ x y, W x y = W y x)
    (hBm : Measurable fun p : Torus d × Torus d => B p.1 p.2) (hbB : ∀ x y, ‖B x y‖ ≤ b)
    (hb0 : 0 ≤ b)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ∞ (fun x => W x y) (fun x => B x y))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    quadE W (⇑(u t)) - quadE W (⇑(u s)) = -∫ r in s..t, 2 * Fl B u J r r := by
  have hFi := integrable_Fd hBm hbB hb0 hdiv hcont
  have hJae : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), Integrable (J r) (haar d) :=
    hdiv.integrable_J.prod_right_ae
  have hJae' := (ae_restrict_iff' measurableSet_Icc).1 hJae
  have hmi : Integrable (fun r => ∫ x, ‖J r x‖ ∂haar d) (volume.restrict (Icc (0 : ℝ) T)) :=
    hdiv.integrable_J.norm.integral_prod_left
  have toII : ∀ {f : ℝ → ℝ}, IntegrableOn f (Icc (0 : ℝ) T) → ∀ {a c : ℝ}, 0 ≤ a → a ≤ c →
      c ≤ T → IntervalIntegrable f volume a c := by
    intro f hf a c ha hac hc
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hac]
    exact IntegrableOn.mono_set hf (fun r hr => ⟨ha.trans hr.1.le, hr.2.trans hc⟩)
  have key := tele_abstract (E := fun τ => quadE W (⇑(u τ))) (F := fun r => 2 * Fl B u J r r)
    (m := fun r => ∫ x, ‖J r x‖ ∂haar d) hst
    ((toII (hFi.const_mul 2) hs hst ht)) (toII hmi hs hst ht) ?_
  · linarith
  intro ε hε
  have hε' : 0 < ε / (2 * (b + 1)) := by positivity
  obtain ⟨δ0, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hcont) _ hε'
  refine ⟨δ0 / 2, by positivity, fun a c ha hac hc hcδ => ?_⟩
  have has : 0 ≤ a := hs.trans ha
  have hcT : c ≤ T := hc.trans ht
  obtain ⟨hGi, hq⟩ := quad_step hdiv hJ2 hWc hsym hBm hbB hWB has hac hcT
  have hF' := toII hFi has hac hcT
  have hm' := toII hmi has hac hcT
  show |quadE W (⇑(u c)) - quadE W (⇑(u a)) + ∫ r in a..c, 2 * Fl B u J r r| ≤
    ε * ∫ r in a..c, ∫ x, ‖J r x‖ ∂haar d
  have e : quadE W (⇑(u c)) - quadE W (⇑(u a)) + ∫ r in a..c, 2 * Fl B u J r r =
      ∫ r in a..c, (2 * Fl B u J r r -
        ∫ x, ⟪J r x, Bc B (fun y => u a y + u c y) x⟫ ∂haar d) := by
    rw [intervalIntegral.integral_sub (hF'.const_mul 2) hGi, hq]; ring
  rw [e, ← Real.norm_eq_abs, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le hac ?_ (hm'.const_mul ε)
  filter_upwards [hJae'] with r hr hrIoc
  have hrI : r ∈ Icc (0 : ℝ) T := ⟨has.trans hrIoc.1.le, hrIoc.2.trans hcT⟩
  have hJr := hr hrI
  rw [Fl_add hBm hbB hJr, Real.norm_eq_abs]
  have h1 := abs_Fl_sub_le (u := u) hBm hbB hJr r a
  have h2 := abs_Fl_sub_le (u := u) hBm hbB hJr r c
  have hda : ‖u r - u a‖ < ε / (2 * (b + 1)) := by
    rw [← dist_eq_norm]
    refine hδ r hrI a ⟨has, hac.trans hcT⟩ ?_
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hrIoc.1, hrIoc.2]
  have hdc : ‖u r - u c‖ < ε / (2 * (b + 1)) := by
    rw [← dist_eq_norm]
    refine hδ r hrI c ⟨has.trans hac, hcT⟩ ?_
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hrIoc.1, hrIoc.2]
  have hX1 := (int_abs_sub_le_norm (u r) (u a)).trans_lt hda
  have hX2 := (int_abs_sub_le_norm (u r) (u c)).trans_lt hdc
  have hm0 : 0 ≤ ∫ x, ‖J r x‖ ∂haar d := integral_nonneg fun _ => norm_nonneg _
  have h3 : |2 * Fl B u J r r - (Fl B u J a r + Fl B u J c r)| ≤
      |Fl B u J r r - Fl B u J a r| + |Fl B u J r r - Fl B u J c r| := by
    have : 2 * Fl B u J r r - (Fl B u J a r + Fl B u J c r) =
        (Fl B u J r r - Fl B u J a r) + (Fl B u J r r - Fl B u J c r) := by ring
    rw [this]; exact abs_add_le _ _
  have hbe : b * (ε / (2 * (b + 1))) * 2 ≤ ε := by
    have : b * (ε / (2 * (b + 1))) * 2 = ε * (b / (b + 1)) := by field_simp
    rw [this]
    exact mul_le_of_le_one_right hε.le (div_le_one_of_le₀ (by linarith) (by linarith))
  have h4 : b * ∫ y, |u r y - u a y| ∂haar d + b * ∫ y, |u r y - u c y| ∂haar d ≤ ε := by
    nlinarith
  calc _ ≤ _ := h3
    _ ≤ (b * ∫ y, |u r y - u a y| ∂haar d) * ∫ x, ‖J r x‖ ∂haar d +
        (b * ∫ y, |u r y - u c y| ∂haar d) * ∫ x, ‖J r x‖ ∂haar d := add_le_add h1 h2
    _ = (b * ∫ y, |u r y - u a y| ∂haar d + b * ∫ y, |u r y - u c y| ∂haar d) *
        ∫ x, ‖J r x‖ ∂haar d := by ring
    _ ≤ ε * ∫ x, ‖J r x‖ ∂haar d := mul_le_mul_of_nonneg_right h4 hm0

end Part5

section Part6

variable {d : ℕ} {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g b : ℝ}

/-- **LIP029.** Potential energy chain identity with weak first derivatives.

For the global bounded mean-field flow `u` (`IsGlobalProbFlow`) and `T ≥ 0`, there are the flux
fields `A` (the density gradient, a weak gradient of `u r` for a.e. `r`) and `K` (the
convective part, a.e. equal to `u r • (G + B ∗ u r)`) in `L²((0,T) × 𝕋^d)` such that, with
`J = A + K` and `0 ≤ s ≤ t ≤ T`,
* `∫ V (ρ_t - ρ_s) = - ∫_s^t ∫ ∇V · J` whenever `∇V = G` weakly (`IsWeakGradient V G`);
* `½ ∬ W (ρ_t ⊗ ρ_t - ρ_s ⊗ ρ_s) = - ∫_s^t ∫ (B ∗ ρ_u) · J_u` whenever `W` is continuous and
  symmetric with weak first derivative `B` in the first variable (`IsWeakGradientLp ∞`, a.e. in
  the second variable): only weak first derivatives of `W` are used. -/
theorem potential_energy_chain_identity_with_weak_first_derivatives
    (h : MeanFieldData G B g b) {ρ0 : L2s d} {u : ℝ → L2s d} (hu : IsGlobalProbFlow h ρ0 u)
    {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ}
    (hV : IsWeakGradient V G)
    (hWc : Continuous fun p : Torus d × Torus d => W p.1 p.2)
    (hsym : ∀ x y, W x y = W y x)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ∞ (fun x => W x y) (fun x => B x y))
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ A K : ℝ × Torus d → Tangent d, Measurable A ∧ MemLp A 2 (tmeas d T) ∧
      Measurable K ∧ MemLp K 2 (tmeas d T) ∧
      (∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)),
        IsWeakGradient (⇑(u r)) (fun x => A (r, x))) ∧
      (∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)),
        (fun x => K (r, x)) =ᵐ[haar d] fun x => u r x • (G x + ∫ y, u r y • B x y ∂haar d)) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        (∫ x, V x * (u t x - u s x) ∂haar d =
          -∫ r in s..t, ∫ x, ⟪G x, A (r, x) + K (r, x)⟫ ∂haar d) ∧
        (1 / 2 * (∫ p, W p.1 p.2 * (u t p.1 * u t p.2) ∂(haar d).prod (haar d) -
            ∫ p, W p.1 p.2 * (u s p.1 * u s p.2) ∂(haar d).prod (haar d)) =
          -∫ r in s..t, ∫ x, ⟪∫ y, u r y • B x y ∂haar d, A (r, x) + K (r, x)⟫ ∂haar d) := by
  obtain ⟨M, S⟩ := hu.toMild hT
  obtain ⟨A, K, hAm, hA2, hKm, hK2, hKe, hSet⟩ := S.exists_setting
  refine ⟨A, K, hAm, hA2, hKm, hK2, hSet.grad, ?_, ?_⟩
  · filter_upwards [hKe, ae_restrict_mem measurableSet_Icc] with r hr hrI
    rw [S.uX_of_mem hrI] at hr
    exact hr.trans (nonlinearity_eq_original h (u r) (hu.nonneg r hrI.1) (hu.mass r hrI.1))
  intro s t hs hst ht
  have hdiv := hSet.div
  have hJ2 : MemLp (fun p : ℝ × Torus d => A (p.1, p.2) + K (p.1, p.2)) 2 (tmeas d T) :=
    hA2.add hK2
  refine ⟨?_, ?_⟩
  · obtain ⟨-, hw⟩ := weakForm_H1 hdiv (fun t _ => Lp.memLp (u t)) hJ2 hV hs hst ht
    have e : ∫ x, V x * (u t x - u s x) ∂haar d =
        ∫ x, u t x * V x ∂haar d - ∫ x, u s x * V x ∂haar d := by
      have h5 := integral_sub ((Lp.memLp (u t)).integrable_mul hV.memLp)
        ((Lp.memLp (u s)).integrable_mul hV.memLp)
      simp only [Pi.mul_apply] at h5
      rw [← h5]
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [e, hw]
    congr 1
    refine intervalIntegral.integral_congr fun r _ => ?_
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact real_inner_comm _ _
  · have hcore := quad_chain_core (u := u) (J := fun r x => A (r, x) + K (r, x)) hdiv hJ2 S.cont
      hWc hsym h.measurable_B h.norm_B_le h.b_nonneg hWB hs hst ht
    have e : ∫ r in s..t, 2 * Fl B (u := u) (fun r x => A (r, x) + K (r, x)) r r =
        2 * ∫ r in s..t, ∫ x, ⟪∫ y, u r y • B x y ∂haar d, A (r, x) + K (r, x)⟫ ∂haar d := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun r _ => ?_
      show 2 * ∫ x, ⟪A (r, x) + K (r, x), Bc B (u r) x⟫ ∂haar d = _
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      exact real_inner_comm _ _
    rw [e] at hcore
    unfold quadE at hcore
    linarith

end Part6

end DGPS.Lipschitz
