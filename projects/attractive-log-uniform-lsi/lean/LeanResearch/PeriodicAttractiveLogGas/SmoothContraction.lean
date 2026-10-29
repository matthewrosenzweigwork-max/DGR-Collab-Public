import LeanResearch.PeriodicAttractiveLogGas.AmbientClosure
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The smooth contraction step of source Proposition 2.6. The smooth-core
composition has its genuine ordinary chain-rule derivative. For a general
element of the closed gradient graph, scalar L2 contraction and a subsequence
with almost-everywhere convergence identify the composed scalar value.
The gradient limit is proved by splitting off the strongly convergent gradient
term and applying dominated convergence to the fixed limiting gradient.

Only finiteness of the measure is required. This file proves neither the
nonsmooth clipping/Markov step nor the inclusion of arbitrary Lipschitz
functions in the form domain.
-/

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff ENNReal

namespace PeriodicAttractiveLogGas

/-- Ordinary composition in the genuine smooth gradient graph. -/
def SmoothPair.compSmooth {N : ℕ} (f : SmoothPair N) (T : ℝ → ℝ)
    (hT : ContDiff ℝ ∞ T) : SmoothPair N where
  value := ⟨fun x ↦ T (f.value x), hT.continuous.comp f.value.continuous⟩
  gradient := ⟨fun x ↦ deriv T (f.value x) • f.gradient x,
    ((hT.continuous_deriv (by simp)).comp f.value.continuous).smul f.gradient.continuous⟩
  smooth := hT.comp f.smooth
  differential := by
    intro y
    have hd := (((hT.differentiable (by simp))
      (f.value (configurationQuotient N y))).hasDerivAt).comp_hasFDerivAt y (f.differential y)
    have hmap : innerSL ℝ (deriv T (f.value (configurationQuotient N y)) •
        f.gradient (configurationQuotient N y)) =
        deriv T (f.value (configurationQuotient N y)) •
          innerSL ℝ (f.gradient (configurationQuotient N y)) := by
      ext v
      simp [innerSL_apply_apply]
    change HasFDerivAt (fun z ↦ T (f.value (configurationQuotient N z)))
      (innerSL ℝ (deriv T (f.value (configurationQuotient N y)) •
        f.gradient (configurationQuotient N y))) y
    rw [hmap]
    exact hd

@[simp] theorem SmoothPair.compSmooth_value {N : ℕ} (f : SmoothPair N) (T : ℝ → ℝ)
    (hT : ContDiff ℝ ∞ T) (x : Configuration N) :
    (f.compSmooth T hT).value x = T (f.value x) := rfl

@[simp] theorem SmoothPair.compSmooth_gradient {N : ℕ} (f : SmoothPair N) (T : ℝ → ℝ)
    (hT : ContDiff ℝ ∞ T) (x : Configuration N) :
    (f.compSmooth T hT).gradient x = deriv T (f.value x) • f.gradient x := rfl

theorem smoothContraction_lipschitz {T : ℝ → ℝ} (hT : ContDiff ℝ ∞ T)
    (hbound : ∀ t, |deriv T t| ≤ 1) : LipschitzWith 1 T := by
  apply lipschitzWith_of_nnnorm_deriv_le (hT.differentiable (by simp))
  intro t
  exact_mod_cast (show ‖deriv T t‖ ≤ (1 : ℝ) by simpa only [Real.norm_eq_abs] using hbound t)

section L2Composition

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem memLp_smoothContraction [IsFiniteMeasure μ] {T : ℝ → ℝ}
    (hT : ContDiff ℝ ∞ T) (hbound : ∀ t, |deriv T t| ≤ 1) (f : Lp ℝ 2 μ) :
    MemLp (fun x ↦ T (f x)) 2 μ := by
  have hdom : MemLp (fun x ↦ ‖f x‖ + ‖T 0‖) 2 μ := (Lp.memLp f).norm.add (memLp_const _)
  apply hdom.mono' (hT.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
  filter_upwards with x
  have hlip := (smoothContraction_lipschitz hT hbound).norm_sub_le (f x) 0
  have ht := norm_add_le (T (f x) - T 0) (T 0)
  simp only [sub_zero, NNReal.coe_one, one_mul] at hlip
  rw [sub_add_cancel] at ht
  exact ht.trans (add_le_add hlip le_rfl)

def smoothContractionValueL2 [IsFiniteMeasure μ] (T : ℝ → ℝ)
    (hT : ContDiff ℝ ∞ T) (hbound : ∀ t, |deriv T t| ≤ 1) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (memLp_smoothContraction hT hbound f).toLp (fun x ↦ T (f x))

theorem smoothContractionValueL2_coe [IsFiniteMeasure μ] (T : ℝ → ℝ)
    (hT : ContDiff ℝ ∞ T) (hbound : ∀ t, |deriv T t| ≤ 1) (f : Lp ℝ 2 μ) :
    smoothContractionValueL2 T hT hbound f =ᵐ[μ] (fun x ↦ T (f x)) :=
  (memLp_smoothContraction hT hbound f).coeFn_toLp

theorem norm_smoothContractionValueL2_sub_le [IsFiniteMeasure μ] (T : ℝ → ℝ)
    (hT : ContDiff ℝ ∞ T) (hbound : ∀ t, |deriv T t| ≤ 1) (f g : Lp ℝ 2 μ) :
    ‖smoothContractionValueL2 T hT hbound f - smoothContractionValueL2 T hT hbound g‖ ≤
      ‖f - g‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub (smoothContractionValueL2 T hT hbound f)
      (smoothContractionValueL2 T hT hbound g),
    smoothContractionValueL2_coe T hT hbound f, smoothContractionValueL2_coe T hT hbound g,
    Lp.coeFn_sub f g] with x hs hf hg hfg
  rw [hs, hfg]
  simp only [Pi.sub_apply, hf, hg]
  simpa only [NNReal.coe_one, one_mul] using
    (smoothContraction_lipschitz hT hbound).norm_sub_le (f x) (g x)

theorem tendsto_smoothContractionValueL2 [IsFiniteMeasure μ] (T : ℝ → ℝ)
    (hT : ContDiff ℝ ∞ T) (hbound : ∀ t, |deriv T t| ≤ 1)
    {ι : Type*} {l : Filter ι} {f : ι → Lp ℝ 2 μ} {g : Lp ℝ 2 μ}
    (hfg : Tendsto f l (𝓝 g)) :
    Tendsto (fun i ↦ smoothContractionValueL2 T hT hbound (f i)) l
      (𝓝 (smoothContractionValueL2 T hT hbound g)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hfg ⊢
  exact squeeze_zero (fun i ↦ norm_nonneg _)
    (fun i ↦ norm_smoothContractionValueL2_sub_le T hT hbound (f i) g) hfg

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem memLp_unitMultiplier {a : α → ℝ} (ha : AEStronglyMeasurable a μ)
    (hab : ∀ x, |a x| ≤ 1) (G : Lp E 2 μ) : MemLp (fun x ↦ a x • G x) 2 μ := by
  apply (Lp.memLp G).mono (ha.smul (Lp.aestronglyMeasurable G))
  filter_upwards with x
  change ‖a x • G x‖ ≤ ‖G x‖
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (hab x) (norm_nonneg _)).trans_eq (one_mul _)

def unitMultiplierL2 (a : α → ℝ) (ha : AEStronglyMeasurable a μ)
    (hab : ∀ x, |a x| ≤ 1) (G : Lp E 2 μ) : Lp E 2 μ :=
  (memLp_unitMultiplier ha hab G).toLp (fun x ↦ a x • G x)

theorem unitMultiplierL2_coe (a : α → ℝ) (ha : AEStronglyMeasurable a μ)
    (hab : ∀ x, |a x| ≤ 1) (G : Lp E 2 μ) :
    unitMultiplierL2 a ha hab G =ᵐ[μ] (fun x ↦ a x • G x) :=
  (memLp_unitMultiplier ha hab G).coeFn_toLp

theorem norm_unitMultiplierL2_le (a : α → ℝ) (ha : AEStronglyMeasurable a μ)
    (hab : ∀ x, |a x| ≤ 1) (G : Lp E 2 μ) : ‖unitMultiplierL2 a ha hab G‖ ≤ ‖G‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [unitMultiplierL2_coe a ha hab G] with x hx
  rw [hx, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (hab x) (norm_nonneg _)).trans_eq (one_mul _)

theorem norm_unitMultiplierL2_sub_le (a : α → ℝ) (ha : AEStronglyMeasurable a μ)
    (hab : ∀ x, |a x| ≤ 1) (G H : Lp E 2 μ) :
    ‖unitMultiplierL2 a ha hab G - unitMultiplierL2 a ha hab H‖ ≤ ‖G - H‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub (unitMultiplierL2 a ha hab G) (unitMultiplierL2 a ha hab H),
    unitMultiplierL2_coe a ha hab G, unitMultiplierL2_coe a ha hab H, Lp.coeFn_sub G H]
    with x hs hG hH hGH
  rw [hs, hGH]
  simp only [Pi.sub_apply, hG, hH, ← smul_sub, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (hab x) (norm_nonneg _)).trans_eq (one_mul _)

theorem integral_norm_sq_eq_L2_norm_sq_real (G : Lp E 2 μ) :
    (∫ x, ‖G x‖ ^ 2 ∂μ) = ‖G‖ ^ 2 := by
  simpa only [L2.inner_def, real_inner_self_eq_norm_sq] using real_inner_self_eq_norm_sq G

/-- Dominated convergence for bounded scalar multipliers acting on one fixed
L2 vector. The dominating function is exactly four times its squared norm. -/
theorem tendsto_unitMultiplierL2_fixed
    {a : ℕ → α → ℝ} {b : α → ℝ}
    (ha : ∀ n, AEStronglyMeasurable (a n) μ) (hab : ∀ n x, |a n x| ≤ 1)
    (hb : AEStronglyMeasurable b μ) (hbb : ∀ x, |b x| ≤ 1)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n ↦ a n x) atTop (𝓝 (b x))) (G : Lp E 2 μ) :
    Tendsto (fun n ↦ unitMultiplierL2 (a n) (ha n) (hab n) G) atTop
      (𝓝 (unitMultiplierL2 b hb hbb G)) := by
  let F : ℕ → α → ℝ := fun n x ↦ ‖(a n x - b x) • G x‖ ^ 2
  have hi : Integrable (fun x ↦ 4 * ‖G x‖ ^ 2) μ :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable G)).mp (Lp.memLp G)).const_mul 4
  have hdct : Tendsto (fun n ↦ ∫ x, F n x ∂μ) atTop (𝓝 0) := by
    have hd := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := F) (f := fun _ ↦ (0 : ℝ)) (fun x ↦ 4 * ‖G x‖ ^ 2)
      (fun n ↦ (((ha n).sub hb).smul (Lp.aestronglyMeasurable G)).norm.pow 2) hi
      (fun n ↦ Eventually.of_forall (fun x ↦ by
        have habs : |a n x - b x| ≤ 2 :=
          (abs_sub (a n x) (b x)).trans (by linarith [hab n x, hbb x])
        have hsq : |a n x - b x| ^ 2 ≤ 4 := by nlinarith [abs_nonneg (a n x - b x)]
        dsimp [F]
        rw [abs_of_nonneg (sq_nonneg _), norm_smul, Real.norm_eq_abs, mul_pow]
        exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)))
      (hae.mono (fun x hx ↦ by
        have hv : Tendsto (fun n ↦ (a n x - b x) • G x) atTop
            (𝓝 ((b x - b x) • G x)) := (hx.sub tendsto_const_nhds).smul tendsto_const_nhds
        simpa only [F, sub_self, zero_smul, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
          using hv.norm.pow 2))
    simpa only [integral_zero] using hd
  have heq (n : ℕ) :
      ‖unitMultiplierL2 (a n) (ha n) (hab n) G - unitMultiplierL2 b hb hbb G‖ ^ 2 =
        ∫ x, F n x ∂μ := by
    rw [← integral_norm_sq_eq_L2_norm_sq_real]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (unitMultiplierL2 (a n) (ha n) (hab n) G)
        (unitMultiplierL2 b hb hbb G), unitMultiplierL2_coe (a n) (ha n) (hab n) G,
      unitMultiplierL2_coe b hb hbb G] with x hs ha' hb'
    simp only [hs, Pi.sub_apply, ha', hb', F, sub_smul]
  have hsq : Tendsto (fun n ↦
      ‖unitMultiplierL2 (a n) (ha n) (hab n) G - unitMultiplierL2 b hb hbb G‖ ^ 2)
      atTop (𝓝 0) := by simpa only [heq] using hdct
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt

/-- The strong gradient error is handled by L2 contraction, independently
of the dominated-convergence coefficient error. -/
theorem tendsto_unitMultiplierL2
    {a : ℕ → α → ℝ} {b : α → ℝ}
    (ha : ∀ n, AEStronglyMeasurable (a n) μ) (hab : ∀ n x, |a n x| ≤ 1)
    (hb : AEStronglyMeasurable b μ) (hbb : ∀ x, |b x| ≤ 1)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n ↦ a n x) atTop (𝓝 (b x)))
    {G : ℕ → Lp E 2 μ} {H : Lp E 2 μ} (hGH : Tendsto G atTop (𝓝 H)) :
    Tendsto (fun n ↦ unitMultiplierL2 (a n) (ha n) (hab n) (G n)) atTop
      (𝓝 (unitMultiplierL2 b hb hbb H)) := by
  have hfixed := tendsto_unitMultiplierL2_fixed ha hab hb hbb hae H
  rw [tendsto_iff_norm_sub_tendsto_zero] at hGH hfixed ⊢
  apply squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (by simpa only [add_zero] using hGH.add hfixed)
  calc
    ‖unitMultiplierL2 (a n) (ha n) (hab n) (G n) - unitMultiplierL2 b hb hbb H‖ ≤
        ‖unitMultiplierL2 (a n) (ha n) (hab n) (G n) - unitMultiplierL2 (a n) (ha n) (hab n) H‖ +
        ‖unitMultiplierL2 (a n) (ha n) (hab n) H - unitMultiplierL2 b hb hbb H‖ := by
      simpa only [dist_eq_norm] using dist_triangle
        (unitMultiplierL2 (a n) (ha n) (hab n) (G n))
        (unitMultiplierL2 (a n) (ha n) (hab n) H) (unitMultiplierL2 b hb hbb H)
    _ ≤ ‖G n - H‖ +
        ‖unitMultiplierL2 (a n) (ha n) (hab n) H - unitMultiplierL2 b hb hbb H‖ :=
      add_le_add (norm_unitMultiplierL2_sub_le (a n) (ha n) (hab n) (G n) H) le_rfl

def smoothContractionGradientL2 (T : ℝ → ℝ) (hT : ContDiff ℝ ∞ T)
    (hbound : ∀ t, |deriv T t| ≤ 1) (f : Lp ℝ 2 μ) (G : Lp E 2 μ) : Lp E 2 μ :=
  unitMultiplierL2 (fun x ↦ deriv T (f x))
    ((hT.continuous_deriv (by simp)).comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
    (fun x ↦ hbound (f x)) G

theorem smoothContractionGradientL2_coe (T : ℝ → ℝ) (hT : ContDiff ℝ ∞ T)
    (hbound : ∀ t, |deriv T t| ≤ 1) (f : Lp ℝ 2 μ) (G : Lp E 2 μ) :
    smoothContractionGradientL2 T hT hbound f G =ᵐ[μ]
      (fun x ↦ deriv T (f x) • G x) :=
  unitMultiplierL2_coe _ _ _ _

theorem norm_smoothContractionGradientL2_le (T : ℝ → ℝ) (hT : ContDiff ℝ ∞ T)
    (hbound : ∀ t, |deriv T t| ≤ 1) (f : Lp ℝ 2 μ) (G : Lp E 2 μ) :
    ‖smoothContractionGradientL2 T hT hbound f G‖ ≤ ‖G‖ :=
  norm_unitMultiplierL2_le _ _ _ _

theorem tendsto_smoothContractionGradientL2 (T : ℝ → ℝ) (hT : ContDiff ℝ ∞ T)
    (hbound : ∀ t, |deriv T t| ≤ 1)
    {f : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ} {G : ℕ → Lp E 2 μ} {H : Lp E 2 μ}
    (hf : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)))
    (hGH : Tendsto G atTop (𝓝 H)) :
    Tendsto (fun n ↦ smoothContractionGradientL2 T hT hbound (f n) (G n)) atTop
      (𝓝 (smoothContractionGradientL2 T hT hbound g H)) := by
  refine tendsto_unitMultiplierL2
    (fun n ↦ (hT.continuous_deriv (by simp)).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable (f n)))
    (fun n x ↦ hbound (f n x))
    ((hT.continuous_deriv (by simp)).comp_aestronglyMeasurable (Lp.aestronglyMeasurable g))
    (fun x ↦ hbound (g x)) ?_ hGH
  exact hf.mono (fun x hx ↦
    ((hT.continuous_deriv (by simp)).tendsto (g x)).comp hx)

end L2Composition

theorem smoothContractionValueL2_toLp {N : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (f : SmoothPair N) (T : ℝ → ℝ) (hT : ContDiff ℝ ∞ T)
    (hbound : ∀ t, |deriv T t| ≤ 1) :
    smoothContractionValueL2 T hT hbound (ContinuousMap.toLp 2 μ ℝ f.value) =
      ContinuousMap.toLp 2 μ ℝ (f.compSmooth T hT).value := by
  apply Lp.ext
  filter_upwards [smoothContractionValueL2_coe T hT hbound (ContinuousMap.toLp 2 μ ℝ f.value),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ f.value,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (f.compSmooth T hT).value] with x h1 h2 h3
  rw [h1, h2, h3, SmoothPair.compSmooth_value]

theorem smoothContractionGradientL2_toLp {N : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (f : SmoothPair N) (T : ℝ → ℝ) (hT : ContDiff ℝ ∞ T)
    (hbound : ∀ t, |deriv T t| ≤ 1) :
    smoothContractionGradientL2 T hT hbound (ContinuousMap.toLp 2 μ ℝ f.value)
      (ContinuousMap.toLp 2 μ ℝ f.gradient) =
        ContinuousMap.toLp 2 μ ℝ (f.compSmooth T hT).gradient := by
  apply Lp.ext
  filter_upwards [smoothContractionGradientL2_coe T hT hbound
      (ContinuousMap.toLp 2 μ ℝ f.value) (ContinuousMap.toLp 2 μ ℝ f.gradient),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ f.value,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ f.gradient,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (f.compSmooth T hT).gradient]
    with x h1 h2 h3 h4
  rw [h1, h2, h3, h4, SmoothPair.compSmooth_gradient]

/-- Actual closed-graph membership of the composed value and chain-rule
gradient, obtained from smooth form-norm approximations and a subsequence.
No closability or composition premise is added to the finite-measure case. -/
theorem smoothContraction_pair_mem_closedGradientGraph
    {N : ℕ} {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    (f : AmbientFormDomain N μ) (T : ℝ → ℝ) (hT : ContDiff ℝ ∞ T)
    (hbound : ∀ t, |deriv T t| ≤ 1) :
    (smoothContractionValueL2 T hT hbound (ambientValue f),
      smoothContractionGradientL2 T hT hbound (ambientValue f) (ambientGradient f)) ∈
        closedGradientGraph N μ := by
  obtain ⟨s, hs⟩ := exists_smooth_formNorm_approx f
  have hp : Tendsto (fun n ↦
      (ContinuousMap.toLp 2 μ ℝ (s n).value, ContinuousMap.toLp 2 μ ℝ (s n).gradient))
      atTop (𝓝 f.1) := tendsto_iff_graphFormNorm_sub_tendsto_zero.mpr hs
  have hv : Tendsto (fun n ↦ ContinuousMap.toLp 2 μ ℝ (s n).value) atTop
      (𝓝 (ambientValue f)) := (continuous_fst.tendsto f.1).comp hp
  have hg : Tendsto (fun n ↦ ContinuousMap.toLp 2 μ ℝ (s n).gradient) atTop
      (𝓝 (ambientGradient f)) := (continuous_snd.tendsto f.1).comp hp
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  have hvc := tendsto_smoothContractionValueL2 T hT hbound (hv.comp hns.tendsto_atTop)
  have hgc := tendsto_smoothContractionGradientL2 T hT hbound hae (hg.comp hns.tendsto_atTop)
  have hc := hvc.prodMk_nhds hgc
  have heq (n : ℕ) :
      (smoothContractionValueL2 T hT hbound (ContinuousMap.toLp 2 μ ℝ (s (ns n)).value),
        smoothContractionGradientL2 T hT hbound (ContinuousMap.toLp 2 μ ℝ (s (ns n)).value)
          (ContinuousMap.toLp 2 μ ℝ (s (ns n)).gradient)) =
      (ContinuousMap.toLp 2 μ ℝ ((s (ns n)).compSmooth T hT).value,
        ContinuousMap.toLp 2 μ ℝ ((s (ns n)).compSmooth T hT).gradient) := by
    rw [smoothContractionValueL2_toLp, smoothContractionGradientL2_toLp]
  simp only [Function.comp_def, heq] at hc
  exact mem_closure_of_tendsto hc (Eventually.of_forall (fun n ↦
    ⟨(s (ns n)).compSmooth T hT, rfl⟩))

/-- The actual composed member of the completed smooth gradient graph. -/
def ambientSmoothContraction {N : ℕ} {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    (f : AmbientFormDomain N μ) (T : ℝ → ℝ) (hT : ContDiff ℝ ∞ T)
    (hbound : ∀ t, |deriv T t| ≤ 1) : AmbientFormDomain N μ :=
  ⟨(smoothContractionValueL2 T hT hbound (ambientValue f),
    smoothContractionGradientL2 T hT hbound (ambientValue f) (ambientGradient f)),
    smoothContraction_pair_mem_closedGradientGraph f T hT hbound⟩

theorem ambientSmoothContraction_value {N : ℕ} {μ : Measure (Configuration N)}
    [IsFiniteMeasure μ] (f : AmbientFormDomain N μ) (T : ℝ → ℝ)
    (hT : ContDiff ℝ ∞ T) (hbound : ∀ t, |deriv T t| ≤ 1) :
    ambientValue (ambientSmoothContraction f T hT hbound) =ᵐ[μ]
      (fun x ↦ T (ambientValue f x)) :=
  smoothContractionValueL2_coe T hT hbound (ambientValue f)

theorem ambientSmoothContraction_gradient {N : ℕ} {μ : Measure (Configuration N)}
    [IsFiniteMeasure μ] (f : AmbientFormDomain N μ) (T : ℝ → ℝ)
    (hT : ContDiff ℝ ∞ T) (hbound : ∀ t, |deriv T t| ≤ 1) :
    ambientGradient (ambientSmoothContraction f T hT hbound) =ᵐ[μ]
      (fun x ↦ deriv T (ambientValue f x) • ambientGradient f x) :=
  smoothContractionGradientL2_coe T hT hbound (ambientValue f) (ambientGradient f)

theorem ambientSmoothContraction_energy_le {N : ℕ} {μ : Measure (Configuration N)}
    [IsFiniteMeasure μ] (f : AmbientFormDomain N μ) (T : ℝ → ℝ)
    (hT : ContDiff ℝ ∞ T) (hbound : ∀ t, |deriv T t| ≤ 1) :
    ambientEnergy (ambientSmoothContraction f T hT hbound) ≤ ambientEnergy f := by
  change ‖smoothContractionGradientL2 T hT hbound (ambientValue f) (ambientGradient f)‖ ^ 2 ≤
    ‖ambientGradient f‖ ^ 2
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (norm_smoothContractionGradientL2_le T hT hbound (ambientValue f) (ambientGradient f))

/-- The full smooth contraction assertion, with the actual scalar L2 class,
chain-rule gradient, and nonincreasing energy, for every finite measure. -/
theorem exists_ambient_smooth_contraction {N : ℕ} {μ : Measure (Configuration N)}
    [IsFiniteMeasure μ] (f : AmbientFormDomain N μ) (T : ℝ → ℝ)
    (hT : ContDiff ℝ ∞ T) (hbound : ∀ t, |deriv T t| ≤ 1) :
    ∃ g : AmbientFormDomain N μ,
      ambientValue g =ᵐ[μ] (fun x ↦ T (ambientValue f x)) ∧
      ambientGradient g =ᵐ[μ] (fun x ↦ deriv T (ambientValue f x) • ambientGradient f x) ∧
      ambientEnergy g ≤ ambientEnergy f :=
  ⟨ambientSmoothContraction f T hT hbound,
    ambientSmoothContraction_value f T hT hbound,
    ambientSmoothContraction_gradient f T hT hbound,
    ambientSmoothContraction_energy_le f T hT hbound⟩

end PeriodicAttractiveLogGas
