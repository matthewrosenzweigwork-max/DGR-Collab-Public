import DGRHS.Commutator.SourceLogStaticGenerator
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-! RECORDS-ONLY / UNCOMPILED Claude candidate (remaining-original-results
return, 2026-10-03). No compiler has evaluated this file.

The unsymmetrized LOG force term of the tested mean-field equation, read as a
principal value, equals the canceled symmetric term for EVERY probability law.

Source 3897--3903 tests the mean-field equation and "integrates by parts and
symmetrizes" the interaction term. Its unsymmetrized form pairs the test
gradient at the first particle with the literal force,
`∇g(x-y)·∇φ(x) = -⟪x-y, ∇φ(x)⟫/|x-y|²`, `g = -log|·|`. In dimension one this
integrand is in general NOT absolutely integrable even for bounded densities
(`∬|x-y|⁻¹ dx dy = ∞` on a square), so no individual pair-force L1 premise is
assumed or inferred here. Instead:

* on each symmetric truncation `{ε < |x-y|}` the unsymmetrized integral is
  proper and equals exactly one half of the truncated canceled integral
  (swap symmetry; no diagonal-null or density premise);
* as `ε → 0+` the truncated canceled integrals converge to the full canceled
  integral (dominated convergence by the gradient Lipschitz constant; the
  canceled kernel is zero on the diagonal);
* if the literal unsymmetrized integrand happens to be integrable, its integral
  equals the principal value (so the literal and canceled readings agree
  wherever the literal one is defined).

Consequently the principal-value drift `β⁻¹∫Δφ - PV∬∇g(x-y)·∇φ(x)` is literally
`sourceLogStaticMeanTestDrift`. -/
noncomputable section
open MeasureTheory Laplacian Set Filter
open scoped Topology NNReal RealInnerProductSpace
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Dynamics
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Literal unsymmetrized pairing `∇g(x-y)·v(x)` with `g = -log|·|`; its value on
the diagonal is zero (the numerator vanishes there). -/
def sourceLogForcePairing (v : E → E) (p : E × E) : ℝ :=
  -⟪p.1 - p.2, v p.1⟫ / ‖p.1 - p.2‖ ^ 2

/-- Symmetric truncation set `{ε < |x-y|}`. -/
def sourceLogTruncSet (ε : ℝ) : Set (E × E) := {p | ε < ‖p.1 - p.2‖}

/-- Principal-value truncation of the unsymmetrized force term. -/
def sourceLogTruncatedForce (μ : Measure E) (v : E → E) (ε : ℝ) : ℝ :=
  ∫ p, (sourceLogTruncSet (ι := ι) ε).indicator (sourceLogForcePairing v) p ∂μ.prod μ

lemma sourceLogForcePairing_diag (v : E → E) (p : E × E) (hp : p.1 = p.2) :
    sourceLogForcePairing v p = 0 := by
  simp [sourceLogForcePairing, hp]

/-- Off the diagonal the pairing is the literal derivative of the LOG potential. -/
lemma sourceLogForcePairing_eq_fderiv (v : E → E) (p : E × E) (hp : p.1 ≠ p.2) :
    sourceLogForcePairing v p = fderiv ℝ sourceLogPotential (p.1 - p.2) (v p.1) :=
  (sourceLogPotential_fderiv_apply (sub_ne_zero.mpr hp) (v p.1)).symm

/-- Swap symmetrization reproduces the canceled kernel. -/
lemma sourceLogForcePairing_add_swap (v : E → E) (p : E × E) :
    sourceLogForcePairing v p + sourceLogForcePairing v p.swap =
      sourceLogTransportKernel 1 v p := by
  rw [sourceLogTransportKernel_one]
  simp only [sourceLogForcePairing, Prod.fst_swap, Prod.snd_swap]
  rw [norm_sub_rev p.2 p.1, ← neg_sub p.1 p.2, inner_neg_left, inner_sub_right]
  ring

lemma measurableSet_sourceLogTruncSet (ε : ℝ) :
    MeasurableSet (sourceLogTruncSet (ι := ι) ε) :=
  (isOpen_lt continuous_const (continuous_fst.sub continuous_snd).norm).measurableSet

lemma swap_mem_sourceLogTruncSet (ε : ℝ) (p : E × E) :
    p.swap ∈ sourceLogTruncSet (ι := ι) ε ↔ p ∈ sourceLogTruncSet (ι := ι) ε := by
  simp only [sourceLogTruncSet, mem_setOf_eq, Prod.fst_swap, Prod.snd_swap, norm_sub_rev]

lemma measurable_sourceLogForcePairing {v : E → E} (hv : Continuous v) :
    Measurable (sourceLogForcePairing v) := by
  have hz : Continuous (fun p : E × E => p.1 - p.2) := continuous_fst.sub continuous_snd
  exact ((hz.inner (hv.comp continuous_fst)).measurable.neg).div
    (hz.norm.measurable.pow_const 2)

lemma abs_sourceLogForcePairing_le {v : E → E} {B : ℝ} (hB : ∀ x, ‖v x‖ ≤ B)
    {ε : ℝ} (hε : 0 < ε) (p : E × E) (hp : ε < ‖p.1 - p.2‖) :
    |sourceLogForcePairing v p| ≤ B / ε := by
  have hz : 0 < ‖p.1 - p.2‖ := hε.trans hp
  unfold sourceLogForcePairing
  rw [abs_div, abs_neg, abs_of_nonneg (sq_nonneg ‖p.1 - p.2‖), div_le_div_iff₀ (by positivity) hε]
  have hc := abs_real_inner_le_norm (p.1 - p.2) (v p.1)
  have hw := hB p.1
  have hw0 := norm_nonneg (v p.1)
  have h1 : |⟪p.1 - p.2, v p.1⟫| * ε ≤ ‖p.1 - p.2‖ * ‖v p.1‖ * ε :=
    mul_le_mul_of_nonneg_right hc hε.le
  have h2 : ‖p.1 - p.2‖ * ‖v p.1‖ * ε ≤ ‖p.1 - p.2‖ * ‖v p.1‖ * ‖p.1 - p.2‖ :=
    mul_le_mul_of_nonneg_left hp.le (mul_nonneg hz.le hw0)
  have h3 : ‖p.1 - p.2‖ * ‖v p.1‖ * ‖p.1 - p.2‖ ≤ ‖p.1 - p.2‖ * B * ‖p.1 - p.2‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hz.le) hz.le
  nlinarith

/-- The truncated unsymmetrized integrand is proper for every finite law. -/
lemma integrable_sourceLogTruncated (μ : Measure E) [IsProbabilityMeasure μ] {v : E → E}
    (hv : Continuous v) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, ‖v x‖ ≤ B) {ε : ℝ} (hε : 0 < ε) :
    Integrable ((sourceLogTruncSet (ι := ι) ε).indicator (sourceLogForcePairing v))
      (μ.prod μ) := by
  refine integrable_of_abs_bound (μ.prod μ)
    ((measurable_sourceLogForcePairing hv).indicator (measurableSet_sourceLogTruncSet ε))
    (L := B / ε) (fun p => ?_)
  by_cases hp : p ∈ sourceLogTruncSet (ι := ι) ε
  · rw [indicator_of_mem hp]
    exact abs_sourceLogForcePairing_le hB hε p hp
  · rw [indicator_of_notMem hp, abs_zero]
    exact div_nonneg hB0 hε.le

/-- Exact symmetrization on each truncation. -/
theorem sourceLogTruncatedForce_eq_half (μ : Measure E) [IsProbabilityMeasure μ]
    {v : E → E} (hv : Continuous v) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, ‖v x‖ ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    sourceLogTruncatedForce μ v ε =
      (1/2 : ℝ) * ∫ p, (sourceLogTruncSet (ι := ι) ε).indicator
        (sourceLogTransportKernel 1 v) p ∂μ.prod μ := by
  set S := sourceLogTruncSet (ι := ι) ε
  set u := S.indicator (sourceLogForcePairing v) with hu
  have hI : Integrable u (μ.prod μ) := integrable_sourceLogTruncated μ hv hB0 hB hε
  have hIs : Integrable (fun p : E × E => u p.swap) (μ.prod μ) := hI.swap
  have hswap : ∫ p, u p.swap ∂μ.prod μ = ∫ p, u p ∂μ.prod μ := integral_prod_swap u
  have hpt (p : E × E) : u p + u p.swap = S.indicator (sourceLogTransportKernel 1 v) p := by
    by_cases hp : p ∈ S
    · have hps : p.swap ∈ S := (swap_mem_sourceLogTruncSet ε p).mpr hp
      simp only [hu, indicator_of_mem hp, indicator_of_mem hps]
      exact sourceLogForcePairing_add_swap v p
    · have hps : p.swap ∉ S := fun h => hp ((swap_mem_sourceLogTruncSet ε p).mp h)
      simp only [hu, indicator_of_notMem hp, indicator_of_notMem hps, add_zero]
  have hsum : ∫ p, S.indicator (sourceLogTransportKernel 1 v) p ∂μ.prod μ =
      2 * ∫ p, u p ∂μ.prod μ := by
    rw [← integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hI hIs, hswap]
    ring
  show ∫ p, u p ∂μ.prod μ = _
  rw [hsum]
  ring

/-- Removal of the truncation in the canceled integral (dominated convergence). -/
theorem tendsto_sourceLogTruncatedKernel (μ : Measure E) [IsProbabilityMeasure μ]
    {v : E → E} {K : ℝ≥0} (hv : LipschitzWith K v) :
    Tendsto (fun ε => ∫ p, (sourceLogTruncSet (ι := ι) ε).indicator
        (sourceLogTransportKernel 1 v) p ∂μ.prod μ) (𝓝[>] 0)
      (𝓝 (∫ p, sourceLogTransportKernel 1 v p ∂μ.prod μ)) := by
  have hm := measurable_sourceLogTransportKernel_one hv
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (K : ℝ))
    (Filter.Eventually.of_forall (fun ε =>
      (hm.indicator (measurableSet_sourceLogTruncSet ε)).aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun ε => Filter.Eventually.of_forall (fun p => ?_)))
    (integrable_const _) (Filter.Eventually.of_forall (fun p => ?_))
  · rw [Real.norm_eq_abs]
    by_cases hp : p ∈ sourceLogTruncSet (ι := ι) ε
    · rw [indicator_of_mem hp]; exact abs_sourceLogTransportKernel_one_le hv p
    · rw [indicator_of_notMem hp, abs_zero]; exact K.coe_nonneg
  · by_cases hp : p.1 = p.2
    · have h0 : sourceLogTransportKernel 1 v p = 0 := by
        rw [sourceLogTransportKernel_one, hp, sub_self, inner_zero_left, neg_zero, zero_div]
      have hc : ∀ ε, (sourceLogTruncSet (ι := ι) ε).indicator
          (sourceLogTransportKernel 1 v) p = sourceLogTransportKernel 1 v p := by
        intro ε
        by_cases hpe : p ∈ sourceLogTruncSet (ι := ι) ε
        · exact indicator_of_mem hpe _
        · rw [indicator_of_notMem hpe, h0]
      simp only [hc]
      exact tendsto_const_nhds
    · have hz : 0 < ‖p.1 - p.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hp)
      apply tendsto_const_nhds.congr'
      filter_upwards [(eventually_lt_nhds hz).filter_mono nhdsWithin_le_nhds] with ε hε
      exact (indicator_of_mem (show p ∈ sourceLogTruncSet (ι := ι) ε from hε) _).symm

/-- **Principal value of the unsymmetrized LOG force term.** For every bounded C2
test and every probability law, the symmetric truncations of
`∬∇g(x-y)·∇φ(x)` converge to one half of the canceled integral. -/
theorem tendsto_sourceLogTruncatedForce (φ : E → ℝ) (hφ : SourceBoundedC2Test φ)
    (μ : Measure E) [IsProbabilityMeasure μ] :
    Tendsto (fun ε => sourceLogTruncatedForce μ (gradient φ) ε) (𝓝[>] 0)
      (𝓝 ((1/2 : ℝ) * ∫ p, sourceLogTransportKernel 1 (gradient φ) p ∂μ.prod μ)) := by
  obtain ⟨hc, C, hC, hb⟩ := (sourceBoundedC2Test_iff_classical_bounds φ).mp hφ
  let K : ℝ≥0 := ⟨C, hC⟩
  have hv : LipschitzWith K (gradient φ) :=
    sourceAdjoint_gradient_lipschitz_of_hessian_bound φ hc K (fun x => (hb x).2.2)
  have hlim := (tendsto_sourceLogTruncatedKernel (ι := ι) μ hv).const_mul (1/2 : ℝ)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (sourceLogTruncatedForce_eq_half μ hv.continuous hC (fun x => (hb x).2.1) hε).symm

/-- If the literal unsymmetrized integrand is integrable, its integral is the
principal value, hence one half of the canceled integral. -/
theorem integral_sourceLogForcePairing_eq_half (φ : E → ℝ) (hφ : SourceBoundedC2Test φ)
    (μ : Measure E) [IsProbabilityMeasure μ]
    (hint : Integrable (sourceLogForcePairing (gradient φ)) (μ.prod μ)) :
    ∫ p, sourceLogForcePairing (gradient φ) p ∂μ.prod μ =
      (1/2 : ℝ) * ∫ p, sourceLogTransportKernel 1 (gradient φ) p ∂μ.prod μ := by
  have hlit : Tendsto (fun ε => sourceLogTruncatedForce μ (gradient φ) ε) (𝓝[>] 0)
      (𝓝 (∫ p, sourceLogForcePairing (gradient φ) p ∂μ.prod μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun p => ‖sourceLogForcePairing (gradient φ) p‖)
      (Filter.Eventually.of_forall (fun ε =>
        hint.aestronglyMeasurable.indicator (measurableSet_sourceLogTruncSet ε)))
      (Filter.Eventually.of_forall (fun ε => Filter.Eventually.of_forall (fun p => ?_)))
      hint.norm (Filter.Eventually.of_forall (fun p => ?_))
    · exact norm_indicator_le_norm_self _ _
    · by_cases hp : p.1 = p.2
      · have h0 := sourceLogForcePairing_diag (gradient φ) p hp
        have hc : ∀ ε, (sourceLogTruncSet (ι := ι) ε).indicator
            (sourceLogForcePairing (gradient φ)) p = sourceLogForcePairing (gradient φ) p := by
          intro ε
          by_cases hpe : p ∈ sourceLogTruncSet (ι := ι) ε
          · exact indicator_of_mem hpe _
          · rw [indicator_of_notMem hpe, h0]
        simp only [hc]
        exact tendsto_const_nhds
      · have hz : 0 < ‖p.1 - p.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hp)
        apply tendsto_const_nhds.congr'
        filter_upwards [(eventually_lt_nhds hz).filter_mono nhdsWithin_le_nhds] with ε hε
        exact (indicator_of_mem (show p ∈ sourceLogTruncSet (ι := ι) ε from hε) _).symm
  exact tendsto_nhds_unique hlit (tendsto_sourceLogTruncatedForce φ hφ μ)

/-- Principal-value form of the source tested drift. -/
def sourceLogPVMeanTestDrift (β : ℝ) (μ : Measure E) (φ : E → ℝ) : ℝ :=
  β⁻¹ * (∫ x, laplacian φ x ∂μ) -
    limUnder (𝓝[>] (0 : ℝ)) (fun ε => sourceLogTruncatedForce μ (gradient φ) ε)

/-- The principal-value drift is the canceled drift, for every probability law. -/
theorem sourceLogPVMeanTestDrift_eq (β : ℝ) (ρ : E → ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (φ : E → ℝ) (hφ : SourceBoundedC2Test φ) :
    sourceLogPVMeanTestDrift β (gaussianRieszDensityMeasure ρ) φ =
      sourceLogStaticMeanTestDrift β ρ φ := by
  unfold sourceLogPVMeanTestDrift sourceLogStaticMeanTestDrift
  rw [(tendsto_sourceLogTruncatedForce φ hφ (gaussianRieszDensityMeasure ρ)).limUnder_eq]

end DGRHS.Commutator
