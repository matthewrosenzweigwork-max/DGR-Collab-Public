/-
Copyright 2026 FujiHaruka. Released under the Apache-2.0 license.
Adapted from FujiHaruka/information-theory commit95a7a76f9b45e8e58251a442c8e9b60eed48a2dd,
InformationTheory/Shannon/TimeBandLimiting/Operator.lean, lines751–1255.
Further CHANGES: finite-measure compactness and shared rectangle-density argument
replace Euclidean box exhaustion. These additions are adapted from the original proof.
Original SHA25634ac468b5391baa1b0812117e5d97e621de0266d00f07e81362701e9844df89e.
CHANGES: narrow mathlib-only dependency closure; generic measurable domain with
SFinite measure; real scalar. No upstream convenience/Fourier/sinc module imported.
Status: supporting row-operator and finite-measure compactness proofs.
Exact development receipts are in records/kernel-operator/RESULT.json.
This file does not prove a Hilbert–Schmidt norm identity or a paper result.
Original source and license preserved under workers/scout/operator-followup/original.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega

open MeasureTheory
open scoped ENNReal symmDiff

namespace DGRHS.Kernel.Operator

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
local notation "E" => Lp ℝ 2 μ
local notation "L2Kernel" => Lp ℝ 2 (μ.prod μ)

noncomputable def l2KernelApply (κ : L2Kernel) (f : E) : α → ℝ :=
  fun t ↦ ∫ s, (κ : α × α → ℝ) (t, s) * (f : α → ℝ) s ∂μ

theorem l2Kernel_slice_memLp (κ : L2Kernel) :
    ∀ᵐ t ∂μ, MemLp (fun s ↦ (κ : α × α → ℝ) (t, s)) 2 μ := by
  have hsm : AEStronglyMeasurable (κ : α × α → ℝ) (μ.prod μ) := (Lp.memLp κ).aestronglyMeasurable
  have hae := hsm.prodMk_left (ν := μ)
  have hmeas : AEMeasurable (fun p : α × α ↦ ‖(κ : α × α → ℝ) p‖ₑ ^ (2 : ℝ≥0∞).toReal)
      (μ.prod μ) := hsm.enorm.pow_const _
  have htop : (∫⁻ p, ‖(κ : α × α → ℝ) p‖ₑ ^ (2 : ℝ≥0∞).toReal ∂(μ.prod μ)) < ∞ :=
    (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num) hsm).mp
      (Lp.eLpNorm_lt_top κ)
  rw [lintegral_prod _ hmeas] at htop
  have hfin : ∀ᵐ t ∂μ,
      (∫⁻ s, ‖(κ : α × α → ℝ) (t, s)‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ) < ∞ :=
    ae_lt_top' hmeas.lintegral_prod_right' htop.ne
  filter_upwards [hae, hfin] with t ht htfin
  exact (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num) ht).mpr htfin

theorem l2Kernel_integrable (κ : L2Kernel) (f : E) :
    ∀ᵐ t ∂μ,
      Integrable (fun s ↦ (κ : α × α → ℝ) (t, s) * (f : α → ℝ) s) μ := by
  filter_upwards [l2Kernel_slice_memLp κ] with t ht
  exact ht.integrable_mul (Lp.memLp f)

theorem l2KernelApply_aestronglyMeasurable (κ : L2Kernel) (f : E) :
    AEStronglyMeasurable (l2KernelApply κ f) μ := by
  have h : AEStronglyMeasurable (fun p : α × α ↦ (κ : α × α → ℝ) p * (f : α → ℝ) p.2)
      (μ.prod μ) :=
    (Lp.memLp κ).aestronglyMeasurable.mul
      ((Lp.memLp f).aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  exact h.integral_prod_right'

theorem l2KernelApply_eLpNorm_le (κ : L2Kernel) (f : E) :
    eLpNorm (l2KernelApply κ f) 2 μ
      ≤ eLpNorm (κ : α × α → ℝ) 2 (μ.prod μ) * eLpNorm (f : α → ℝ) 2 μ := by
  set D : ℝ≥0∞ := ∫⁻ s, ‖(f : α → ℝ) s‖ₑ ^ (2 : ℝ) ∂μ with hD
  set A : α → ℝ≥0∞ := fun t ↦ ∫⁻ s, ‖(κ : α × α → ℝ) (t, s)‖ₑ ^ (2 : ℝ) ∂μ with hA
  have hfm : AEMeasurable (fun s ↦ ‖(f : α → ℝ) s‖ₑ) μ := (Lp.memLp f).aestronglyMeasurable.enorm
  have hκm : AEMeasurable (fun p : α × α ↦ ‖(κ : α × α → ℝ) p‖ₑ ^ (2 : ℝ))
      (μ.prod μ) := (Lp.memLp κ).aestronglyMeasurable.enorm.pow_const _
  -- Cauchy–Schwarz on each slice: `‖∫ k(t,s) f(s) ds‖ ≤ ‖k(t,·)‖₂ · ‖f‖₂`.
  have hpt : ∀ᵐ t ∂μ,
      ‖l2KernelApply κ f t‖ₑ ^ (2 : ℝ) ≤ A t * D := by
    filter_upwards [(Lp.memLp κ).aestronglyMeasurable.prodMk_left (ν := μ)] with t ht
    have hcs : ‖l2KernelApply κ f t‖ₑ ≤ A t ^ (1 / 2 : ℝ) * D ^ (1 / 2 : ℝ) := by
      calc ‖l2KernelApply κ f t‖ₑ
          ≤ ∫⁻ s, ‖(κ : α × α → ℝ) (t, s) * (f : α → ℝ) s‖ₑ ∂μ :=
            enorm_integral_le_lintegral_enorm _
        _ = ∫⁻ s, ((fun u ↦ ‖(κ : α × α → ℝ) (t, u)‖ₑ) * fun u ↦ ‖(f : α → ℝ) u‖ₑ) s ∂μ := by
            simp [enorm_mul]
        _ ≤ A t ^ (1 / 2 : ℝ) * D ^ (1 / 2 : ℝ) :=
            ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two ht.enorm hfm
    calc ‖l2KernelApply κ f t‖ₑ ^ (2 : ℝ)
        ≤ (A t ^ (1 / 2 : ℝ) * D ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
          exact ENNReal.rpow_le_rpow hcs (by norm_num)
      _ = A t * D := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2), ← ENNReal.rpow_mul,
            ← ENNReal.rpow_mul]
          norm_num
  -- Tonelli in the outer variable.
  have hswap : (∫⁻ t, A t ∂μ)
      = ∫⁻ p, ‖(κ : α × α → ℝ) p‖ₑ ^ (2 : ℝ) ∂(μ.prod μ) := (lintegral_prod _ hκm).symm
  have hLHS : eLpNorm (l2KernelApply κ f) 2 μ
      = (∫⁻ t, ‖l2KernelApply κ f t‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (l2KernelApply_aestronglyMeasurable κ f)]; norm_num
  have hK : eLpNorm (κ : α × α → ℝ) 2 (μ.prod μ)
      = (∫⁻ p, ‖(κ : α × α → ℝ) p‖ₑ ^ (2 : ℝ) ∂(μ.prod μ)) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (Lp.aestronglyMeasurable κ)]; norm_num
  have hF : eLpNorm (f : α → ℝ) 2 μ = D ^ (1 / 2 : ℝ) := by
    rw [hD, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (Lp.aestronglyMeasurable f)]; norm_num
  rw [hLHS, hK, hF, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2), ← hswap,
    ← lintegral_mul_const'' _ (by
      exact (hκm.lintegral_prod_right' : AEMeasurable A μ))]
  exact ENNReal.rpow_le_rpow (lintegral_mono_ae hpt) (by norm_num)

theorem l2KernelApply_memLp (κ : L2Kernel) (f : E) : MemLp (l2KernelApply κ f) 2 μ :=
  lt_of_le_of_lt (l2KernelApply_eLpNorm_le κ f)
    (ENNReal.mul_lt_top (Lp.eLpNorm_lt_top κ) (Lp.eLpNorm_lt_top f))

/-- The integral operator of a kernel, as a linear map on `L²(μ;ℝ)`. -/
noncomputable def l2KernelLin (κ : L2Kernel) : E →ₗ[ℝ] E where
  toFun f := (l2KernelApply_memLp κ f).toLp _
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [(l2KernelApply_memLp κ (f + g)).coeFn_toLp,
      Lp.coeFn_add ((l2KernelApply_memLp κ f).toLp (l2KernelApply κ f))
        ((l2KernelApply_memLp κ g).toLp (l2KernelApply κ g)),
      (l2KernelApply_memLp κ f).coeFn_toLp, (l2KernelApply_memLp κ g).coeFn_toLp,
      l2Kernel_integrable κ f, l2Kernel_integrable κ g] with t h1 h2 h3 h4 hi1 hi2
    rw [h1, h2, Pi.add_apply, h3, h4]
    simp only [l2KernelApply]
    rw [← integral_add hi1 hi2]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add f g] with s hs
    rw [hs, Pi.add_apply, mul_add]
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [(l2KernelApply_memLp κ (c • f)).coeFn_toLp,
      Lp.coeFn_smul c ((l2KernelApply_memLp κ f).toLp (l2KernelApply κ f)),
      (l2KernelApply_memLp κ f).coeFn_toLp] with t h1 h2 h3
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, smul_eq_mul]
    simp only [l2KernelApply]
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c f] with s hs
    rw [hs, Pi.smul_apply, smul_eq_mul]
    ring

theorem l2KernelLin_coeFn (κ : L2Kernel) (f : E) :
    ((l2KernelLin κ f : E) : α → ℝ) =ᵐ[μ] l2KernelApply κ f :=
  (l2KernelApply_memLp κ f).coeFn_toLp

/-- The kernel-to-operator map, as a bilinear map. -/
noncomputable def l2KernelBilin : L2Kernel →ₗ[ℝ] (E →ₗ[ℝ] E) where
  toFun := l2KernelLin
  map_add' κ κ' := by
    refine LinearMap.ext fun f ↦ ?_
    rw [LinearMap.add_apply]
    refine Lp.ext ?_
    have hae : ∀ᵐ t ∂μ, ∀ᵐ s ∂μ,
        ((κ + κ' : L2Kernel) : α × α → ℝ) (t, s)
          = (κ : α × α → ℝ) (t, s) + (κ' : α × α → ℝ) (t, s) := by
      have h0 : ∀ᵐ p ∂(μ.prod μ),
          ((κ + κ' : L2Kernel) : α × α → ℝ) p = (κ : α × α → ℝ) p + (κ' : α × α → ℝ) p := by
        filter_upwards [Lp.coeFn_add κ κ'] with p hp using by simpa using hp
      exact Measure.ae_ae_of_ae_prod h0
    filter_upwards [l2KernelLin_coeFn (κ + κ') f,
      Lp.coeFn_add (l2KernelLin κ f) (l2KernelLin κ' f),
      l2KernelLin_coeFn κ f, l2KernelLin_coeFn κ' f,
      l2Kernel_integrable κ f, l2Kernel_integrable κ' f, hae] with t h1 h2 h3 h4 hi1 hi2 hs
    rw [h1, h2, Pi.add_apply, h3, h4]
    simp only [l2KernelApply]
    rw [← integral_add hi1 hi2]
    refine integral_congr_ae ?_
    filter_upwards [hs] with s hsv
    rw [hsv, add_mul]
  map_smul' c κ := by
    refine LinearMap.ext fun f ↦ ?_
    rw [RingHom.id_apply, LinearMap.smul_apply]
    refine Lp.ext ?_
    have hae : ∀ᵐ t ∂μ, ∀ᵐ s ∂μ,
        ((c • κ : L2Kernel) : α × α → ℝ) (t, s) = c * (κ : α × α → ℝ) (t, s) := by
      have h0 : ∀ᵐ p ∂(μ.prod μ),
          ((c • κ : L2Kernel) : α × α → ℝ) p = c * (κ : α × α → ℝ) p := by
        filter_upwards [Lp.coeFn_smul c κ] with p hp using by simpa using hp
      exact Measure.ae_ae_of_ae_prod h0
    filter_upwards [l2KernelLin_coeFn (c • κ) f, Lp.coeFn_smul c (l2KernelLin κ f),
      l2KernelLin_coeFn κ f, hae] with t h1 h2 h3 hs
    rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]
    simp only [l2KernelApply]
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hs] with s hsv
    rw [hsv]
    ring

/-- The kernel-to-operator map `κ ↦ (f ↦ ∫ κ(·,s) f(s) ds)`, as a continuous linear map. Its
continuity is exactly the Hilbert–Schmidt bound `‖l2KernelOp κ‖ ≤ ‖κ‖`.
 -/
noncomputable def l2KernelOp : L2Kernel →L[ℝ] (E →L[ℝ] E) :=
  LinearMap.mkContinuous₂ l2KernelBilin 1 (by
    intro κ f
    rw [one_mul]
    calc ‖l2KernelBilin κ f‖
        = (eLpNorm (l2KernelApply κ f) 2 μ).toReal :=
          Lp.norm_toLp _ (l2KernelApply_memLp κ f)
      _ ≤ (eLpNorm (κ : α × α → ℝ) 2 (μ.prod μ)
            * eLpNorm (f : α → ℝ) 2 μ).toReal :=
          ENNReal.toReal_mono
            (ENNReal.mul_lt_top (Lp.eLpNorm_lt_top κ) (Lp.eLpNorm_lt_top f)).ne
            (l2KernelApply_eLpNorm_le κ f)
      _ = ‖κ‖ * ‖f‖ := by rw [ENNReal.toReal_mul, Lp.norm_def, Lp.norm_def])

theorem l2KernelOp_apply_ae (κ : L2Kernel) (f : E) :
    (l2KernelOp κ f : α → ℝ) =ᵐ[μ] l2KernelApply κ f :=
  l2KernelLin_coeFn κ f


section FiniteMeasure
variable [IsFiniteMeasure μ]

theorem l2KernelOp_indicator_prod_isCompact {A B : Set α}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (c : ℝ) :
    IsCompactOperator (l2KernelOp (indicatorConstLp 2 (hA.prod hB)
      (measure_ne_top (μ.prod μ) (A ×ˢ B)) c)) := by
  classical
  let hAB := measure_ne_top (μ.prod μ) (A ×ˢ B)
  have hAf := measure_ne_top μ A
  have hBf := measure_ne_top μ B
  set gA : E := indicatorConstLp 2 hA hAf (1 : ℝ) with hgA_def
  set gB : E := indicatorConstLp 2 hB hBf (1 : ℝ) with hgB_def
  set φ : E →L[ℝ] ℝ := c • (innerSL ℝ gB) with hφ_def
  set ψ : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight gA with hψ_def
  have hEq : l2KernelOp (indicatorConstLp 2 (hA.prod hB) hAB c) = ψ ∘L φ := by
    refine ContinuousLinearMap.ext fun f ↦ Lp.ext ?_
    -- The functional: `⟪𝟙_B, f⟫ = ∫_B f`.
    have hinner : (innerSL ℝ gB) f
        = ∫ s, B.indicator (fun _ ↦ (1 : ℝ)) s * (f : α → ℝ) s ∂μ := by
      simp only [coe_innerSL_apply]
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [(indicatorConstLp_coeFn : (gB : α → ℝ) =ᵐ[μ] _)] with s hs
      rw [hs, RCLike.inner_apply']
      by_cases hsB : s ∈ B <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hsB]
    -- The a.e. shape of the kernel.
    have hker : ∀ᵐ t ∂μ, ∀ᵐ s ∂μ,
        ((indicatorConstLp 2 (hA.prod hB) hAB c : L2Kernel) : α × α → ℝ) (t, s)
          = (A ×ˢ B).indicator (fun _ ↦ c) (t, s) :=
      Measure.ae_ae_of_ae_prod indicatorConstLp_coeFn
    filter_upwards [l2KernelOp_apply_ae (indicatorConstLp 2 (hA.prod hB) hAB c) f,
      Lp.coeFn_smul (φ f) gA, (indicatorConstLp_coeFn : (gA : α → ℝ) =ᵐ[μ] _), hker]
      with t h1 h2 h3 hs
    rw [h1]
    show (∫ s, ((indicatorConstLp 2 (hA.prod hB) hAB c : L2Kernel) : α × α → ℝ) (t, s)
      * (f : α → ℝ) s ∂μ) = _
    rw [ContinuousLinearMap.comp_apply, hψ_def, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply]
    rw [h2, Pi.smul_apply, h3, smul_eq_mul, hφ_def, FunLike.coe_smul,
      Pi.smul_apply, smul_eq_mul, hinner]
    have hrw : (∫ s, ((indicatorConstLp 2 (hA.prod hB) hAB c : L2Kernel) : α × α → ℝ) (t, s)
        * (f : α → ℝ) s ∂μ)
        = ∫ s, (A ×ˢ B).indicator (fun _ ↦ c) (t, s) * (f : α → ℝ) s ∂μ :=
      integral_congr_ae (by filter_upwards [hs] with s hsv using by rw [hsv])
    rw [hrw]
    by_cases htA : t ∈ A
    · rw [Set.indicator_of_mem htA, mul_one, ← MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s ↦ ?_)
      by_cases hsB : s ∈ B <;>
        simp [Set.mem_prod, htA, hsB, Set.indicator_of_mem, Set.indicator_of_notMem]
    · rw [Set.indicator_of_notMem htA, mul_zero]
      have hz : ∀ s : α, (A ×ˢ B).indicator (fun _ ↦ c) (t, s) * (f : α → ℝ) s = 0 := by
        intro s; simp [Set.mem_prod, htA, Set.indicator_of_notMem]
      simp [hz]
  rw [hEq]
  exact (isCompactOperator_of_locallyCompactSpace_dom φ).clm_comp ψ

theorem indicatorConstLp_congr_set {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s t : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (ht : MeasurableSet t) (hμt : μ t ≠ ∞)
    (h : s = t) (c : ℝ) :
    indicatorConstLp (μ := μ) 2 hs hμs c = indicatorConstLp 2 ht hμt c := by
  subst h; rfl

theorem indicatorConstLp_of_measure_zero {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (h0 : μ s = 0) (c : ℝ) :
    indicatorConstLp (μ := μ) 2 hs hμs c = 0 := by
  rw [← norm_eq_zero, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp [Measure.real, h0]

theorem indicatorConstLp_eq_smul_one {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) :
    indicatorConstLp (μ := μ) 2 hs hμs c = c • indicatorConstLp 2 hs hμs (1 : ℝ) := by
  refine Lp.ext ?_
  filter_upwards [(indicatorConstLp_coeFn : ⇑(indicatorConstLp (μ := μ) 2 hs hμs c) =ᵐ[μ] _),
    Lp.coeFn_smul c (indicatorConstLp (μ := μ) 2 hs hμs (1 : ℝ)),
    (indicatorConstLp_coeFn : ⇑(indicatorConstLp (μ := μ) 2 hs hμs (1 : ℝ)) =ᵐ[μ] _)]
    with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]
  by_cases hx : x ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]


/-- Closed submodules containing all product rectangle indicators contain every
product-L2 function. No topological assumption on the underlying measurable domain. -/
theorem mem_closedSubmodule_of_rectangles
    (V : Submodule ℝ L2Kernel) (hVclosed : IsClosed (V : Set L2Kernel))
    (hrect : ∀ (A B : Set α) (hA : MeasurableSet A) (hB : MeasurableSet B),
      indicatorConstLp 2 (hA.prod hB) (measure_ne_top (μ.prod μ) (A ×ˢ B)) (1 : ℝ) ∈ V)
    (κ : L2Kernel) : κ ∈ V := by
  classical
  have huniv : indicatorConstLp 2 (MeasurableSet.univ : MeasurableSet (Set.univ : Set (α × α)))
      (measure_ne_top (μ.prod μ) Set.univ) (1 : ℝ) ∈ V := by
    convert hrect Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ using 1 <;> simp
  have key : ∀ (u : Set (α × α)) (hu : MeasurableSet u),
      indicatorConstLp 2 hu (measure_ne_top (μ.prod μ) u) (1 : ℝ) ∈ V := by
    refine MeasurableSpace.induction_on_inter
      (C := fun u hu ↦ indicatorConstLp 2 hu (measure_ne_top (μ.prod μ) u) (1 : ℝ) ∈ V)
      generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_
    · rw [indicatorConstLp_of_measure_zero _ _ (by simp) 1]
      exact V.zero_mem
    · rintro t ⟨A, hA, B, hB, rfl⟩
      exact hrect A B hA hB
    · intro t htm ih
      have hsum : indicatorConstLp 2 MeasurableSet.univ
          (measure_ne_top (μ.prod μ) Set.univ) (1 : ℝ)
          = indicatorConstLp 2 htm.compl (measure_ne_top (μ.prod μ) tᶜ) (1 : ℝ)
            + indicatorConstLp 2 htm (measure_ne_top (μ.prod μ) t) (1 : ℝ) := by
        rw [← indicatorConstLp_disjoint_union (p := 2) htm.compl htm
          (measure_ne_top (μ.prod μ) tᶜ) (measure_ne_top (μ.prod μ) t)
          (by exact Set.disjoint_left.mpr (fun x hx hx' ↦ hx hx')) (1 : ℝ)]
        exact indicatorConstLp_congr_set _ _ _ _ (Set.compl_union_self t).symm 1
      have := V.sub_mem huniv ih
      rwa [hsum, add_sub_cancel_right] at this
    · intro f hfd hfm ih
      have hUm : ∀ n : ℕ, MeasurableSet (⋃ i ∈ Finset.range n, f i) := fun n ↦
        Finset.measurableSet_biUnion _ fun i _ ↦ hfm i
      have hpartial : ∀ n : ℕ,
          indicatorConstLp 2 (hUm n) (measure_ne_top (μ.prod μ) _) (1 : ℝ)
            = ∑ i ∈ Finset.range n, indicatorConstLp 2 (hfm i)
              (measure_ne_top (μ.prod μ) _) (1 : ℝ) := by
        intro n
        induction n with
        | zero =>
          simp only [Finset.range_zero, Finset.sum_empty]
          exact indicatorConstLp_of_measure_zero _ _ (by simp) 1
        | succ n ih2 =>
          have hdisj : Disjoint (f n) (⋃ i ∈ Finset.range n, f i) := by
            refine Set.disjoint_iUnion₂_right.mpr fun i hi ↦ ?_
            exact hfd (by simpa using (Finset.mem_range.mp hi).ne')
          have hsplit : indicatorConstLp 2 (hUm (n+1)) (measure_ne_top (μ.prod μ) _) (1 : ℝ)
              = indicatorConstLp 2 (hfm n) (measure_ne_top (μ.prod μ) _) (1 : ℝ)
                + indicatorConstLp 2 (hUm n) (measure_ne_top (μ.prod μ) _) (1 : ℝ) := by
            rw [← indicatorConstLp_disjoint_union (p := 2) (hfm n) (hUm n)
              (measure_ne_top (μ.prod μ) _) (measure_ne_top (μ.prod μ) _) hdisj (1 : ℝ)]
            refine indicatorConstLp_congr_set _ _ _ _ ?_ 1
            rw [Finset.range_add_one, Finset.set_biUnion_insert]
          rw [hsplit, Finset.sum_range_succ, ih2, add_comm]
      have hUV : ∀ n : ℕ, indicatorConstLp 2 (hUm n)
          (measure_ne_top (μ.prod μ) _) (1 : ℝ) ∈ V := by
        intro n
        rw [hpartial n]
        exact V.sum_mem fun i _ ↦ ih i
      have hsymm : ∀ n : ℕ,
          ((⋃ i ∈ Finset.range n, f i) ∆ (⋃ i, f i)) = ⋃ i ≥ n, f i := by
        intro n
        ext x
        simp only [Set.mem_symmDiff, Set.mem_iUnion, Finset.mem_range, exists_prop, ge_iff_le]
        constructor
        · rintro (⟨⟨i, hi, hxi⟩, hx⟩ | ⟨⟨i, hxi⟩, hx⟩)
          · exact absurd ⟨i, hxi⟩ hx
          · refine ⟨i, ?_, hxi⟩
            by_contra hcon
            exact hx ⟨i, not_le.mp hcon, hxi⟩
        · rintro ⟨i, hin, hxi⟩
          refine Or.inr ⟨⟨i, hxi⟩, ?_⟩
          rintro ⟨j, hj, hxj⟩
          exact Set.disjoint_left.mp (hfd (by omega : i ≠ j)) hxi hxj
      have htend : Filter.Tendsto
          (fun n ↦ (μ.prod μ) ((⋃ i ∈ Finset.range n, f i) ∆ (⋃ i, f i)))
          Filter.atTop (nhds 0) := by
        have hbase := tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
          (μ := μ.prod μ) (fun i ↦ (hfm i).nullMeasurableSet) hfd
        exact hbase.congr (fun n ↦ congrArg (μ.prod μ) (hsymm n).symm)
      have hlim : Filter.Tendsto
          (fun n ↦ indicatorConstLp (μ := μ.prod μ) 2 (hUm n)
            (measure_ne_top (μ.prod μ) _) (1 : ℝ)) Filter.atTop
          (nhds (indicatorConstLp 2 (MeasurableSet.iUnion hfm)
            (measure_ne_top (μ.prod μ) _) (1 : ℝ))) := by
        exact tendsto_indicatorConstLp_set (by norm_num) htend
      exact hVclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hUV)
  induction κ using Lp.induction (p := 2) (by norm_num) with
  | indicatorConst c hs hμs =>
      rw [Lp.simpleFunc.coe_indicatorConst, indicatorConstLp_eq_smul_one]
      exact V.smul_mem c (key _ hs)
  | add hf hg _ hfV hgV => exact V.add_mem hfV hgV
  | isClosed => exact hVclosed

theorem l2KernelOp_isCompact (κ : L2Kernel) : IsCompactOperator (l2KernelOp κ) := by
  let V : Submodule ℝ L2Kernel :=
    Submodule.comap (l2KernelOp : L2Kernel →L[ℝ] (E →L[ℝ] E)).toLinearMap
      (compactOperator (RingHom.id ℝ) E E)
  have hVclosed : IsClosed (V : Set L2Kernel) :=
    isClosed_setOfPred_isCompactOperator.preimage l2KernelOp.continuous
  exact mem_closedSubmodule_of_rectangles V hVclosed
    (fun A B hA hB ↦ l2KernelOp_indicator_prod_isCompact hA hB 1) κ

end FiniteMeasure

end DGRHS.Kernel.Operator

#print axioms DGRHS.Kernel.Operator.l2Kernel_slice_memLp
#print axioms DGRHS.Kernel.Operator.l2Kernel_integrable
#print axioms DGRHS.Kernel.Operator.l2KernelApply_memLp
#print axioms DGRHS.Kernel.Operator.l2KernelOp
#print axioms DGRHS.Kernel.Operator.l2KernelOp_apply_ae

#print axioms DGRHS.Kernel.Operator.l2KernelOp_indicator_prod_isCompact
#print axioms DGRHS.Kernel.Operator.mem_closedSubmodule_of_rectangles
#print axioms DGRHS.Kernel.Operator.l2KernelOp_isCompact

#check DGRHS.Kernel.Operator.l2Kernel_slice_memLp

#check DGRHS.Kernel.Operator.l2Kernel_integrable

#check DGRHS.Kernel.Operator.l2KernelApply_memLp

#check DGRHS.Kernel.Operator.l2KernelOp

#check DGRHS.Kernel.Operator.l2KernelOp_apply_ae

#check DGRHS.Kernel.Operator.l2KernelOp_indicator_prod_isCompact

#check DGRHS.Kernel.Operator.mem_closedSubmodule_of_rectangles

#check DGRHS.Kernel.Operator.l2KernelOp_isCompact
