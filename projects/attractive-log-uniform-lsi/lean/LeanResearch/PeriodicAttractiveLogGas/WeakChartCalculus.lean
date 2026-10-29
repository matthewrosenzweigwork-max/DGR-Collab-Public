import LeanResearch.PeriodicAttractiveLogGas.MovingPoleNumerators
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Function.L2Space

/-! Source-only candidate for the weak logarithm, quotient and Lipschitz
passage in manuscript Lemma 3.5.

This module proves a regularized-limit version of that passage. The data
are actual ordinary derivatives of approximating functions, uniform value
and derivative bounds, and pointwise convergence of values and Riesz
gradients. Neither a weak chain rule nor a limiting derivative is assumed.
Compact-test integration by parts and dominated convergence give the weak
identities. The convex mean-value theorem gives a Lipschitz bound before
the limit, hence for the actual limiting function on the entire closed
set. This is a reusable analytic lemma; constructing its data from the
moving-pole integral remains a separate instantiation.

The author has not run Lean on this source. All coordinates and norms are
the genuine Euclidean ones, including in dimension zero.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace PeriodicAttractiveLogGas.WeakChartCalculus

variable {d : Type*} [Fintype d]

abbrev ChartSpace (d : Type*) := EuclideanSpace ℝ d

/-- Actual weak gradient, with its Bochner integrability gates. Tests have
compact support contained in the chart, and can depend on every coordinate. -/
structure WeakGradientOn (S : Set (ChartSpace d)) (f : ChartSpace d → ℝ)
    (G : ChartSpace d → ChartSpace d) : Prop where
  value_integrable : IntegrableOn f S
  gradient_integrable : IntegrableOn G S
  identity : ∀ (ψ : ChartSpace d → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ S → ∀ v : ChartSpace d,
    (∫ x in S, f x * fderiv ℝ ψ x v) =
      -(∫ x in S, inner ℝ (G x) v * ψ x)

omit [Fintype d] in
theorem test_bound {ψ : ChartSpace d → ℝ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) : ∃ C : ℝ, 0 < C ∧ ∀ x, ‖ψ x‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := (hc.isCompact_range hψ).isBounded.exists_pos_norm_le
  exact ⟨C, hC, fun x ↦ hb (ψ x) (mem_range_self x)⟩

/-- The Riesz gradient is locally measurable even if the scalar function
has arbitrary behavior outside the chart. -/
theorem gradient_aestronglyMeasurable {S : Set (ChartSpace d)}
    (hS : MeasurableSet S) {f : ChartSpace d → ℝ} {G : ChartSpace d → ChartSpace d}
    (hf : ∀ x ∈ S, HasFDerivAt f (InnerProductSpace.toDual ℝ (ChartSpace d) (G x)) x) :
    AEStronglyMeasurable G (volume.restrict S) := by
  have hm : Measurable (fun x ↦ (InnerProductSpace.toDual ℝ (ChartSpace d)).symm
      (fderiv ℝ f x)) :=
    (InnerProductSpace.toDual ℝ (ChartSpace d)).symm.continuous.measurable.comp
      (measurable_fderiv ℝ f)
  apply hm.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem hS] with x hx
  rw [(hf x hx).fderiv]
  exact (InnerProductSpace.toDual ℝ (ChartSpace d)).symm_apply_apply (G x)

theorem value_aestronglyMeasurable {S : Set (ChartSpace d)}
    (hS : MeasurableSet S) {f : ChartSpace d → ℝ} {G : ChartSpace d → ChartSpace d}
    (hf : ∀ x ∈ S, HasFDerivAt f (InnerProductSpace.toDual ℝ (ChartSpace d) (G x)) x) :
    AEStronglyMeasurable f (volume.restrict S) :=
  (show ContinuousOn f S from fun x hx ↦
    (hf x hx).continuousAt.continuousWithinAt).aestronglyMeasurable (μ := volume) hS

/-- Classical differentiation implies the weak identity. The derivative
field need not be continuous, and there is no regularity assumption away
from the chart. -/
theorem weakGradientOn_of_hasFDerivAt {S : Set (ChartSpace d)}
    {f : ChartSpace d → ℝ} {G : ChartSpace d → ChartSpace d}
    (hfi : IntegrableOn f S) (hGi : IntegrableOn G S)
    (hf : ∀ x ∈ S, HasFDerivAt f (InnerProductSpace.toDual ℝ (ChartSpace d) (G x)) x) :
    WeakGradientOn S f G := by
  refine ⟨hfi, hGi, ?_⟩
  intro ψ hψ hc hψS v
  obtain ⟨C, _, hC⟩ := test_bound hψ.continuous hc
  obtain ⟨D, _, hD⟩ := test_bound
    ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    (hc.fderiv_apply ℝ v)
  have hR : Integrable (fun x ↦ inner ℝ (G x) v * ψ x) volume := by
    apply IntegrableOn.integrable_of_forall_notMem_eq_zero
      ((hGi.inner_const v).mul_bdd hψ.continuous.aestronglyMeasurable (ae_of_all _ hC))
    intro x hx
    simp only [image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (hψS hh)), mul_zero]
  have hL : Integrable (fun x ↦ f x * fderiv ℝ ψ x v) volume := by
    apply IntegrableOn.integrable_of_forall_notMem_eq_zero (hfi.mul_bdd
      ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
      (ae_of_all _ hD))
    intro x hx
    have hn : x ∉ tsupport (fun y ↦ fderiv ℝ ψ y v) :=
      fun hh ↦ hx (hψS (tsupport_fderiv_apply_subset ℝ v hh))
    simp only [image_eq_zero_of_notMem_tsupport hn, mul_zero]
  have hP : Integrable (fun x ↦ f x * ψ x) volume := by
    apply IntegrableOn.integrable_of_forall_notMem_eq_zero
      (hfi.mul_bdd hψ.continuous.aestronglyMeasurable (ae_of_all _ hC))
    intro x hx
    simp only [image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (hψS hh)), mul_zero]
  have heq (x : ChartSpace d) : fderiv ℝ f x v * ψ x = inner ℝ (G x) v * ψ x := by
    by_cases hx : x ∈ tsupport ψ
    · rw [(hf x (hψS hx)).fderiv]
      rfl
    · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hDF : Integrable (fun x ↦ fderiv ℝ f x v * ψ x) volume :=
    hR.congr (ae_of_all _ fun x ↦ (heq x).symm)
  have hI := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hDF hL hP
    (fun x hx ↦ (hf x (hψS hx)).differentiableAt)
    (fun x _ ↦ hψ.differentiable one_ne_zero x)
  have hL' : (∫ x in S, f x * fderiv ℝ ψ x v) = ∫ x, f x * fderiv ℝ ψ x v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hn : x ∉ tsupport (fun y ↦ fderiv ℝ ψ y v) :=
      fun hh ↦ hx (hψS (tsupport_fderiv_apply_subset ℝ v hh))
    simp only [image_eq_zero_of_notMem_tsupport hn, mul_zero]
  have hR' : (∫ x in S, inner ℝ (G x) v * ψ x) = ∫ x, inner ℝ (G x) v * ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp only [image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (hψS hh)), mul_zero]
  rw [hL', hR']
  simpa only [heq] using hI

/-- Genuine ordinary approximation data. The conclusion for the limiting
function is proved below, not included as a field of this structure. -/
structure BoundedGradientApproximation (S : Set (ChartSpace d))
    (f : ChartSpace d → ℝ) (G : ChartSpace d → ChartSpace d) (A C : ℝ) where
  value : ℕ → ChartSpace d → ℝ
  gradient : ℕ → ChartSpace d → ChartSpace d
  nonneg_value_bound : 0 ≤ A
  nonneg_gradient_bound : 0 ≤ C
  derivative : ∀ n x, x ∈ S → HasFDerivAt (value n)
    (InnerProductSpace.toDual ℝ (ChartSpace d) (gradient n x)) x
  value_bound : ∀ n x, x ∈ S → ‖value n x‖ ≤ A
  gradient_bound : ∀ n x, x ∈ S → ‖gradient n x‖ ≤ C
  value_limit : ∀ x ∈ S, Tendsto (fun n ↦ value n x) atTop (𝓝 (f x))
  gradient_limit : ∀ x ∈ S, Tendsto (fun n ↦ gradient n x) atTop (𝓝 (G x))

namespace BoundedGradientApproximation

variable {S : Set (ChartSpace d)} {f : ChartSpace d → ℝ}
    {G : ChartSpace d → ChartSpace d} {A C : ℝ}
    (h : BoundedGradientApproximation S f G A C)

include h

theorem limit_value_bound {x : ChartSpace d} (hx : x ∈ S) : ‖f x‖ ≤ A :=
  le_of_tendsto (h.value_limit x hx).norm (Eventually.of_forall fun n ↦ h.value_bound n x hx)

theorem limit_gradient_bound {x : ChartSpace d} (hx : x ∈ S) : ‖G x‖ ≤ C :=
  le_of_tendsto (h.gradient_limit x hx).norm (Eventually.of_forall fun n ↦ h.gradient_bound n x hx)

theorem value_measurable (hS : MeasurableSet S) (n : ℕ) :
    AEStronglyMeasurable (h.value n) (volume.restrict S) :=
  value_aestronglyMeasurable hS (h.derivative n)

theorem gradient_measurable (hS : MeasurableSet S) (n : ℕ) :
    AEStronglyMeasurable (h.gradient n) (volume.restrict S) :=
  gradient_aestronglyMeasurable hS (h.derivative n)

theorem limit_value_measurable (hS : MeasurableSet S) :
    AEStronglyMeasurable f (volume.restrict S) :=
  aestronglyMeasurable_of_tendsto_ae atTop (h.value_measurable hS)
    ((ae_restrict_mem hS).mono fun x hx ↦ h.value_limit x hx)

theorem limit_gradient_measurable (hS : MeasurableSet S) :
    AEStronglyMeasurable G (volume.restrict S) :=
  aestronglyMeasurable_of_tendsto_ae atTop (h.gradient_measurable hS)
    ((ae_restrict_mem hS).mono fun x hx ↦ h.gradient_limit x hx)

theorem limit_value_integrable (hS : IsCompact S) : IntegrableOn f S :=
  IntegrableOn.of_bound hS.measure_lt_top (h.limit_value_measurable hS.measurableSet) A
    ((ae_restrict_mem hS.measurableSet).mono fun _ hx ↦ h.limit_value_bound hx)

theorem limit_gradient_integrable (hS : IsCompact S) : IntegrableOn G S :=
  IntegrableOn.of_bound hS.measure_lt_top (h.limit_gradient_measurable hS.measurableSet) C
    ((ae_restrict_mem hS.measurableSet).mono fun _ hx ↦ h.limit_gradient_bound hx)

theorem approximant_weakGradientOn (hS : IsCompact S) (n : ℕ) :
    WeakGradientOn S (h.value n) (h.gradient n) := by
  apply weakGradientOn_of_hasFDerivAt
    (IntegrableOn.of_bound hS.measure_lt_top (h.value_measurable hS.measurableSet n) A
      ((ae_restrict_mem hS.measurableSet).mono fun x hx ↦ h.value_bound n x hx))
    (IntegrableOn.of_bound hS.measure_lt_top (h.gradient_measurable hS.measurableSet n) C
      ((ae_restrict_mem hS.measurableSet).mono fun x hx ↦ h.gradient_bound n x hx))
  exact h.derivative n

/-- Dominated convergence on the finite chart identifies the actual weak
gradient, including its norm and value integrability. -/
theorem weakGradientOn (hS : IsCompact S) : WeakGradientOn S f G := by
  let : IsFiniteMeasure ((volume : Measure (ChartSpace d)).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  refine ⟨h.limit_value_integrable hS, h.limit_gradient_integrable hS, ?_⟩
  intro ψ hψ hc hψS v
  obtain ⟨D, _, hbD⟩ := test_bound
    ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hc.fderiv_apply ℝ v)
  obtain ⟨B, _, hbB⟩ := test_bound hψ.continuous hc
  have hL : Tendsto (fun n ↦ ∫ x in S, h.value n x * fderiv ℝ ψ x v) atTop
      (𝓝 (∫ x in S, f x * fderiv ℝ ψ x v)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ A * D)
      (fun n ↦ (h.value_measurable hS.measurableSet n).mul
        ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable)
      (integrable_const _)
    · intro n
      filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
      rw [Pi.mul_apply, norm_mul]
      exact mul_le_mul (h.value_bound n x hx) (hbD x) (norm_nonneg _) h.nonneg_value_bound
    · filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
      exact (h.value_limit x hx).mul_const _
  have hR : Tendsto (fun n ↦ ∫ x in S, inner ℝ (h.gradient n x) v * ψ x) atTop
      (𝓝 (∫ x in S, inner ℝ (G x) v * ψ x)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ (C * ‖v‖) * B)
      (fun n ↦ (h.gradient_measurable hS.measurableSet n).inner_const.mul
        hψ.continuous.aestronglyMeasurable) (integrable_const _)
    · intro n
      filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
      calc
        ‖inner ℝ (h.gradient n x) v * ψ x‖ ≤
            (‖h.gradient n x‖ * ‖v‖) * ‖ψ x‖ := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
        _ ≤ (C * ‖v‖) * B := mul_le_mul
          (mul_le_mul_of_nonneg_right (h.gradient_bound n x hx) (norm_nonneg _))
          (hbB x) (norm_nonneg _) (mul_nonneg h.nonneg_gradient_bound (norm_nonneg _))
    · filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
      exact ((h.gradient_limit x hx).inner tendsto_const_nhds).mul_const _
  apply tendsto_nhds_unique hL
  exact hR.neg.congr' (Eventually.of_forall fun n ↦
    ((h.approximant_weakGradientOn hS n).identity ψ hψ hc hψS v).symm)

theorem approximant_lipschitzOnWith (hS : Convex ℝ S) (n : ℕ) :
    LipschitzOnWith ⟨C, h.nonneg_gradient_bound⟩ (h.value n) S := by
  apply hS.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x hx ↦ (h.derivative n x hx).hasFDerivWithinAt)
  intro x hx
  change ‖InnerProductSpace.toDual ℝ (ChartSpace d) (h.gradient n x)‖ ≤ C
  rw [(InnerProductSpace.toDual ℝ (ChartSpace d)).norm_map]
  exact h.gradient_bound n x hx

/-- The limiting function itself is Lipschitz on the whole convex chart.
This also treats the boundary; an a.e. representative is not substituted. -/
theorem lipschitzOnWith (hS : Convex ℝ S) :
    LipschitzOnWith ⟨C, h.nonneg_gradient_bound⟩ f S := by
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro x hx y hy
  apply le_of_tendsto ((h.value_limit x hx).sub (h.value_limit y hy)).norm
  exact Eventually.of_forall fun n ↦
    (lipschitzOnWith_iff_norm_sub_le.mp (h.approximant_lipschitzOnWith hS n)) hx hy

end BoundedGradientApproximation

def logGradient (u : ChartSpace d → ℝ) (U : ChartSpace d → ChartSpace d)
    (x : ChartSpace d) : ChartSpace d := (u x)⁻¹ • U x

def quotientGradient (u v : ChartSpace d → ℝ)
    (U V : ChartSpace d → ChartSpace d) (x : ChartSpace d) : ChartSpace d :=
  (u x)⁻¹ • V x - (v x / (u x) ^ 2) • U x

theorem hasFDerivAt_log {u : ChartSpace d → ℝ} {U : ChartSpace d → ChartSpace d}
    {x : ChartSpace d}
    (hu : HasFDerivAt u (InnerProductSpace.toDual ℝ (ChartSpace d) (U x)) x)
    (hx : u x ≠ 0) : HasFDerivAt (fun y ↦ Real.log (u y))
      (InnerProductSpace.toDual ℝ (ChartSpace d) (logGradient u U x)) x := by
  simpa only [logGradient, map_smul] using hu.log hx

theorem hasFDerivAt_quotient {u v : ChartSpace d → ℝ}
    {U V : ChartSpace d → ChartSpace d} {x : ChartSpace d}
    (hu : HasFDerivAt u (InnerProductSpace.toDual ℝ (ChartSpace d) (U x)) x)
    (hv : HasFDerivAt v (InnerProductSpace.toDual ℝ (ChartSpace d) (V x)) x)
    (hx : u x ≠ 0) : HasFDerivAt (fun y ↦ v y / u y)
      (InnerProductSpace.toDual ℝ (ChartSpace d) (quotientGradient u v U V x)) x := by
  have hi := (hasDerivAt_inv hx).comp_hasFDerivAt x hu
  have he : InnerProductSpace.toDual ℝ (ChartSpace d) (quotientGradient u v U V x) =
      v x • (-(u x ^ 2)⁻¹ • InnerProductSpace.toDual ℝ (ChartSpace d) (U x)) +
        (u x)⁻¹ • InnerProductSpace.toDual ℝ (ChartSpace d) (V x) := by
    ext z
    simp only [quotientGradient, map_sub, map_smul, sub_apply,
      add_apply, smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [he]
  convert hv.mul hi using 1 <;> rfl

theorem norm_log_le {c B t : ℝ} (hc : 0 < c) (hct : c ≤ t) (htB : t ≤ B) :
    ‖Real.log t‖ ≤ |Real.log c| + |Real.log B| := by
  rw [Real.norm_eq_abs, abs_le]
  have hl := Real.log_le_log hc hct
  have hu := Real.log_le_log (hc.trans_le hct) htB
  constructor <;> linarith [le_abs_self (Real.log B), neg_abs_le (Real.log c),
    abs_nonneg (Real.log c), abs_nonneg (Real.log B)]

theorem inv_le_of_lower {c t : ℝ} (hc : 0 < c) (hct : c ≤ t) : t⁻¹ ≤ c⁻¹ := by
  simpa only [one_div] using one_div_le_one_div_of_le hc hct

theorem norm_logGradient_le {u : ChartSpace d → ℝ} {U : ChartSpace d → ChartSpace d}
    {c C : ℝ} (hc : 0 < c) (_hC : 0 ≤ C) {x : ChartSpace d}
    (hl : c ≤ u x) (hU : ‖U x‖ ≤ C) : ‖logGradient u U x‖ ≤ c⁻¹ * C := by
  rw [logGradient, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hc.trans_le hl).le)]
  exact mul_le_mul (inv_le_of_lower hc hl) hU (norm_nonneg _)
    (inv_nonneg.mpr hc.le)

theorem norm_quotientGradient_le {u v : ChartSpace d → ℝ}
    {U V : ChartSpace d → ChartSpace d} {c A Cu Cv : ℝ}
    (hc : 0 < c) (hA : 0 ≤ A) (_hCu : 0 ≤ Cu) (_hCv : 0 ≤ Cv)
    {x : ChartSpace d} (hl : c ≤ u x) (hv : ‖v x‖ ≤ A)
    (hU : ‖U x‖ ≤ Cu) (hV : ‖V x‖ ≤ Cv) :
    ‖quotientGradient u v U V x‖ ≤ c⁻¹ * Cv + (A * (c⁻¹) ^ 2) * Cu := by
  have hp : 0 < u x := hc.trans_le hl
  have hi := inv_le_of_lower hc hl
  have hq : ‖v x / (u x) ^ 2‖ ≤ A * (c⁻¹) ^ 2 := by
    rw [div_eq_mul_inv, norm_mul, norm_inv, norm_pow, Real.norm_of_nonneg hp.le,
      ← inv_pow]
    exact mul_le_mul hv (pow_le_pow_left₀ (inv_nonneg.mpr hp.le) hi 2)
      (sq_nonneg _) hA
  calc
    ‖quotientGradient u v U V x‖ ≤ ‖(u x)⁻¹ • V x‖ + ‖(v x / (u x) ^ 2) • U x‖ :=
      norm_sub_le _ _
    _ ≤ c⁻¹ * Cv + (A * (c⁻¹) ^ 2) * Cu := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
      exact add_le_add (mul_le_mul hi hV (norm_nonneg _) (inv_nonneg.mpr hc.le))
        (mul_le_mul hq hU (norm_nonneg _) (mul_nonneg hA (sq_nonneg _)))

/-- A positive uniform lower bound permits logarithmic approximation, with
an explicit bound on its actual Riesz gradient. -/
def BoundedGradientApproximation.log {S : Set (ChartSpace d)}
    {u : ChartSpace d → ℝ} {U : ChartSpace d → ChartSpace d} {B C c : ℝ}
    (h : BoundedGradientApproximation S u U B C) (hc : 0 < c)
    (hl : ∀ n x, x ∈ S → c ≤ h.value n x) :
    BoundedGradientApproximation S (fun x ↦ Real.log (u x)) (logGradient u U)
      (|Real.log c| + |Real.log B|) (c⁻¹ * C) where
  value n x := Real.log (h.value n x)
  gradient n x := logGradient (h.value n) (h.gradient n) x
  nonneg_value_bound := add_nonneg (abs_nonneg _) (abs_nonneg _)
  nonneg_gradient_bound := mul_nonneg (inv_nonneg.mpr hc.le) h.nonneg_gradient_bound
  derivative n x hx := hasFDerivAt_log (h.derivative n x hx) (hc.trans_le (hl n x hx)).ne'
  value_bound n x hx := by
    apply norm_log_le hc (hl n x hx)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using h.value_bound n x hx)
  gradient_bound n x hx := norm_logGradient_le hc h.nonneg_gradient_bound
    (hl n x hx) (h.gradient_bound n x hx)
  value_limit x hx := by
    have hup : 0 < u x := hc.trans_le (ge_of_tendsto (h.value_limit x hx)
      (Eventually.of_forall fun n ↦ hl n x hx))
    exact (h.value_limit x hx).log hup.ne'
  gradient_limit x hx := by
    have hup : 0 < u x := hc.trans_le (ge_of_tendsto (h.value_limit x hx)
      (Eventually.of_forall fun n ↦ hl n x hx))
    exact ((h.value_limit x hx).inv₀ hup.ne').smul (h.gradient_limit x hx)

/-- Quotient approximation is derived from the ordinary product/inverse
rule and the same strictly positive lower bound. Zero numerators and zero
gradient bounds require no separate division. -/
def BoundedGradientApproximation.quotient {S : Set (ChartSpace d)}
    {u v : ChartSpace d → ℝ} {U V : ChartSpace d → ChartSpace d}
    {B A Cu Cv c : ℝ} (hu : BoundedGradientApproximation S u U B Cu)
    (hv : BoundedGradientApproximation S v V A Cv) (hc : 0 < c)
    (hl : ∀ n x, x ∈ S → c ≤ hu.value n x) :
    BoundedGradientApproximation S (fun x ↦ v x / u x) (quotientGradient u v U V)
      (A * c⁻¹) (c⁻¹ * Cv + (A * (c⁻¹) ^ 2) * Cu) where
  value n x := hv.value n x / hu.value n x
  gradient n x := quotientGradient (hu.value n) (hv.value n) (hu.gradient n) (hv.gradient n) x
  nonneg_value_bound := mul_nonneg hv.nonneg_value_bound (inv_nonneg.mpr hc.le)
  nonneg_gradient_bound := add_nonneg
    (mul_nonneg (inv_nonneg.mpr hc.le) hv.nonneg_gradient_bound)
    (mul_nonneg (mul_nonneg hv.nonneg_value_bound (sq_nonneg _)) hu.nonneg_gradient_bound)
  derivative n x hx := hasFDerivAt_quotient (hu.derivative n x hx)
    (hv.derivative n x hx) (hc.trans_le (hl n x hx)).ne'
  value_bound n x hx := by
    rw [div_eq_mul_inv, norm_mul, Real.norm_of_nonneg
      (inv_nonneg.mpr (hc.trans_le (hl n x hx)).le)]
    exact mul_le_mul (hv.value_bound n x hx) (inv_le_of_lower hc (hl n x hx))
      (inv_nonneg.mpr (hc.trans_le (hl n x hx)).le) hv.nonneg_value_bound
  gradient_bound n x hx := norm_quotientGradient_le hc hv.nonneg_value_bound
    hu.nonneg_gradient_bound hv.nonneg_gradient_bound (hl n x hx)
    (hv.value_bound n x hx) (hu.gradient_bound n x hx) (hv.gradient_bound n x hx)
  value_limit x hx := by
    have hup : 0 < u x := hc.trans_le (ge_of_tendsto (hu.value_limit x hx)
      (Eventually.of_forall fun n ↦ hl n x hx))
    exact (hv.value_limit x hx).div (hu.value_limit x hx) hup.ne'
  gradient_limit x hx := by
    have hup : 0 < u x := hc.trans_le (ge_of_tendsto (hu.value_limit x hx)
      (Eventually.of_forall fun n ↦ hl n x hx))
    exact (((hu.value_limit x hx).inv₀ hup.ne').smul (hv.gradient_limit x hx)).sub
      (((hv.value_limit x hx).div ((hu.value_limit x hx).pow 2) (pow_ne_zero 2 hup.ne')).smul
        (hu.gradient_limit x hx))

/-- Exact weak logarithm and whole-chart Lipschitz conclusions from actual
bounded approximants. The constant is quantified before the approximation
index and before every point, including every boundary point. -/
theorem logarithm_weakGradientOn_and_lipschitzOnWith {S : Set (ChartSpace d)}
    (hS : IsCompact S) (hconv : Convex ℝ S)
    {u : ChartSpace d → ℝ} {U : ChartSpace d → ChartSpace d} {B C c : ℝ}
    (h : BoundedGradientApproximation S u U B C) (hc : 0 < c)
    (hl : ∀ n x, x ∈ S → c ≤ h.value n x) :
    WeakGradientOn S (fun x ↦ Real.log (u x)) (logGradient u U) ∧
      LipschitzOnWith ⟨c⁻¹ * C, mul_nonneg (inv_nonneg.mpr hc.le) h.nonneg_gradient_bound⟩
        (fun x ↦ Real.log (u x)) S :=
  ⟨(h.log hc hl).weakGradientOn hS, (h.log hc hl).lipschitzOnWith hconv⟩

/-- Exact weak quotient and whole-chart Lipschitz conclusions. The weak
field is the ordinary quotient field, not an assumed derivative. -/
theorem quotient_weakGradientOn_and_lipschitzOnWith {S : Set (ChartSpace d)}
    (hS : IsCompact S) (hconv : Convex ℝ S)
    {u v : ChartSpace d → ℝ} {U V : ChartSpace d → ChartSpace d}
    {B A Cu Cv c : ℝ} (hu : BoundedGradientApproximation S u U B Cu)
    (hv : BoundedGradientApproximation S v V A Cv) (hc : 0 < c)
    (hl : ∀ n x, x ∈ S → c ≤ hu.value n x) :
    WeakGradientOn S (fun x ↦ v x / u x) (quotientGradient u v U V) ∧
      LipschitzOnWith ⟨c⁻¹ * Cv + (A * (c⁻¹) ^ 2) * Cu, add_nonneg
        (mul_nonneg (inv_nonneg.mpr hc.le) hv.nonneg_gradient_bound)
        (mul_nonneg (mul_nonneg hv.nonneg_value_bound (sq_nonneg _)) hu.nonneg_gradient_bound)⟩
        (fun x ↦ v x / u x) S :=
  ⟨(hu.quotient hv hc hl).weakGradientOn hS, (hu.quotient hv hc hl).lipschitzOnWith hconv⟩

end PeriodicAttractiveLogGas.WeakChartCalculus
