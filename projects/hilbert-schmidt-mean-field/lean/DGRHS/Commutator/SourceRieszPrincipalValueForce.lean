import DGRHS.Commutator.SourceLogPrincipalValueForce
import DGRHS.Commutator.SourceRieszStaticWeakForm
import DGRHS.Commutator.SourceRieszLocalEnergy
import DGRHS.Commutator.SourceRieszForceSymmetry
import DGRHS.Dynamics.SourceAdjointHessianLipschitz

/-! RECORDS-ONLY / UNCOMPILED Claude candidate (remaining-original-results
return, 2026-10-03). No compiler has evaluated this file.

Positive-Riesz principal value of the unsymmetrized force term
`∬⟪∇g_s(x-y), ∇φ(x)⟫`, `g_s = |·|^{-s}/s`, `0 < s`, `2s < d`.

For bounded densities the literal integrand is absolutely integrable when
`s + 1 < d`, which holds automatically if `d ≥ 2` (since `s < d/2 ≤ d-1`), but
FAILS in dimension one (`s + 1 > 1`). The principal-value reading below is
valid in every dimension; on each symmetric truncation it equals one half of the
truncated canceled integral exactly, and the truncation is removed using the
checked singular local domination `|K| ≤ A·Lip·|x-y|^{-s}/s` and square
integrability of `|x-y|^{-s}/s` under the density cap. The truncation set and
its measurability/swap invariance are shared with the LOG module. -/
noncomputable section
open MeasureTheory Laplacian Set Filter
open scoped Topology NNReal RealInnerProductSpace
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Dynamics
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Literal unsymmetrized pairing `⟪∇g_s(x-y), v x⟫`; zero on the diagonal. -/
def sourceRieszForcePairing (s : ℝ) (v : E → E) (p : E × E) : ℝ :=
  ⟪sourceRieszForce s (p.1 - p.2), v p.1⟫

/-- Principal-value truncation of the unsymmetrized Riesz force term. -/
def sourceRieszTruncatedForce (s : ℝ) (μ : Measure E) (v : E → E) (ε : ℝ) : ℝ :=
  ∫ p, (sourceLogTruncSet (ι := ι) ε).indicator (sourceRieszForcePairing s v) p ∂μ.prod μ

lemma sourceRieszForcePairing_diag (s : ℝ) (v : E → E) (p : E × E) (hp : p.1 = p.2) :
    sourceRieszForcePairing s v p = 0 := by
  simp [sourceRieszForcePairing, hp, sourceRieszForce_zero]

lemma sourceRieszForcePairing_add_swap (s : ℝ) (hs : 0 < s) (v : E → E) (p : E × E) :
    sourceRieszForcePairing s v p + sourceRieszForcePairing s v p.swap =
      sourceRieszTransportKernel 1 s v p := by
  obtain ⟨x, y⟩ := p
  rw [sourceRieszTransportKernel_force s hs]
  simp only [sourceRieszForcePairing, Prod.swap_prod_mk]
  rw [show y - x = -(x - y) by abel, sourceRieszForce_neg, inner_neg_left, inner_sub_right]
  ring

lemma measurable_sourceRieszForcePairing (s : ℝ) {v : E → E} (hv : Continuous v) :
    Measurable (sourceRieszForcePairing s v) := by
  have hz : Measurable (fun p : E × E => p.1 - p.2) := measurable_fst.sub measurable_snd
  have hF : Measurable (fun p : E × E => sourceRieszForce s (p.1 - p.2)) :=
    ((hz.norm.pow_const (-s - 2)).neg).smul hz
  have hi : Continuous (fun q : E × E => ⟪q.1, q.2⟫) :=
    continuous_fst.inner continuous_snd
  exact hi.measurable.comp (hF.prodMk (hv.measurable.comp measurable_fst))

lemma abs_sourceRieszForcePairing_le (s : ℝ) (hs : 0 < s) {v : E → E} {B : ℝ}
    (hB : ∀ x, ‖v x‖ ≤ B) {ε : ℝ} (hε : 0 < ε) (p : E × E) (hp : ε < ‖p.1 - p.2‖) :
    |sourceRieszForcePairing s v p| ≤ ε ^ (-s - 1) * B := by
  have hz : 0 < ‖p.1 - p.2‖ := hε.trans hp
  have hpow0 : 0 ≤ ‖p.1 - p.2‖ ^ (-s - 2) := Real.rpow_nonneg (norm_nonneg _) _
  have hmono : ‖p.1 - p.2‖ ^ (-s - 1) ≤ ε ^ (-s - 1) :=
    Real.rpow_le_rpow_of_nonpos hε hp.le (by linarith)
  have hsplit : ‖p.1 - p.2‖ ^ (-s - 2) * ‖p.1 - p.2‖ = ‖p.1 - p.2‖ ^ (-s - 1) := by
    rw [← Real.rpow_add_one hz.ne']
    congr 1
    ring
  unfold sourceRieszForcePairing sourceRieszForce
  rw [real_inner_smul_left, abs_mul, abs_neg, abs_of_nonneg hpow0]
  have hc := abs_real_inner_le_norm (p.1 - p.2) (v p.1)
  have hw0 := norm_nonneg (v p.1)
  have hε0 : 0 ≤ ε ^ (-s - 1) := Real.rpow_nonneg hε.le _
  calc
    ‖p.1 - p.2‖ ^ (-s - 2) * |⟪p.1 - p.2, v p.1⟫| ≤
        ‖p.1 - p.2‖ ^ (-s - 2) * (‖p.1 - p.2‖ * ‖v p.1‖) :=
      mul_le_mul_of_nonneg_left hc hpow0
    _ = ‖p.1 - p.2‖ ^ (-s - 1) * ‖v p.1‖ := by rw [← mul_assoc, hsplit]
    _ ≤ ε ^ (-s - 1) * B :=
      mul_le_mul hmono (hB p.1) hw0 hε0

lemma integrable_sourceRieszTruncated (s : ℝ) (hs : 0 < s) (μ : Measure E)
    [IsProbabilityMeasure μ] {v : E → E} (hv : Continuous v) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, ‖v x‖ ≤ B) {ε : ℝ} (hε : 0 < ε) :
    Integrable ((sourceLogTruncSet (ι := ι) ε).indicator (sourceRieszForcePairing s v))
      (μ.prod μ) := by
  refine integrable_of_abs_bound (μ.prod μ)
    ((measurable_sourceRieszForcePairing s hv).indicator (measurableSet_sourceLogTruncSet ε))
    (L := ε ^ (-s - 1) * B) (fun p => ?_)
  by_cases hp : p ∈ sourceLogTruncSet (ι := ι) ε
  · rw [indicator_of_mem hp]
    exact abs_sourceRieszForcePairing_le s hs hB hε p hp
  · rw [indicator_of_notMem hp, abs_zero]
    exact mul_nonneg (Real.rpow_nonneg hε.le _) hB0

/-- Exact symmetrization on each truncation. -/
theorem sourceRieszTruncatedForce_eq_half (s : ℝ) (hs : 0 < s) (μ : Measure E)
    [IsProbabilityMeasure μ] {v : E → E} (hv : Continuous v) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, ‖v x‖ ≤ B) {ε : ℝ} (hε : 0 < ε) :
    sourceRieszTruncatedForce s μ v ε =
      (1/2 : ℝ) * ∫ p, (sourceLogTruncSet (ι := ι) ε).indicator
        (sourceRieszTransportKernel 1 s v) p ∂μ.prod μ := by
  set S := sourceLogTruncSet (ι := ι) ε
  set u := S.indicator (sourceRieszForcePairing s v) with hu
  have hI : Integrable u (μ.prod μ) := integrable_sourceRieszTruncated s hs μ hv hB0 hB hε
  have hIs : Integrable (fun p : E × E => u p.swap) (μ.prod μ) := hI.swap
  have hswap : ∫ p, u p.swap ∂μ.prod μ = ∫ p, u p ∂μ.prod μ := integral_prod_swap u
  have hpt (p : E × E) :
      u p + u p.swap = S.indicator (sourceRieszTransportKernel 1 s v) p := by
    by_cases hp : p ∈ S
    · have hps : p.swap ∈ S := (swap_mem_sourceLogTruncSet ε p).mpr hp
      simp only [hu, indicator_of_mem hp, indicator_of_mem hps]
      exact sourceRieszForcePairing_add_swap s hs v p
    · have hps : p.swap ∉ S := fun h => hp ((swap_mem_sourceLogTruncSet ε p).mp h)
      simp only [hu, indicator_of_notMem hp, indicator_of_notMem hps, add_zero]
  have hsum : ∫ p, S.indicator (sourceRieszTransportKernel 1 s v) p ∂μ.prod μ =
      2 * ∫ p, u p ∂μ.prod μ := by
    rw [← integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hI hIs, hswap]
    ring
  show ∫ p, u p ∂μ.prod μ = _
  rw [hsum]
  ring

/-- Removal of the truncation in the canceled Riesz integral under the density cap. -/
theorem tendsto_sourceRieszTruncatedKernel (s : ℝ) (hs : 0 < s)
    (hd : 2 * s < (Fintype.card ι : ℝ)) (ρ : E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    {v : E → E} {K : ℝ≥0} (hv : LipschitzWith K v) :
    Tendsto (fun ε => ∫ p, (sourceLogTruncSet (ι := ι) ε).indicator
        (sourceRieszTransportKernel 1 s v) p
          ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) (𝓝[>] 0)
      (𝓝 (∫ p, sourceRieszTransportKernel 1 s v p
        ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) := by
  have hm := measurable_sourceRieszTransportKernel s 1 hv
  have hpair : Integrable (gaussianRieszPhysicalPair (ι := ι) s)
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) :=
    (memLp_gaussianRieszPhysicalPair s hs (by linarith) ρ M hM hρ).integrable (by norm_num)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun p => sourceRieszLocalProfileConstant (ι := ι) s 1 * (K : ℝ) ^ 1 *
      gaussianRieszPhysicalPair s p)
    (Filter.Eventually.of_forall (fun ε =>
      (hm.indicator (measurableSet_sourceLogTruncSet ε)).aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun ε => Filter.Eventually.of_forall (fun p => ?_)))
    (hpair.const_mul _) (Filter.Eventually.of_forall (fun p => ?_))
  · rw [Real.norm_eq_abs]
    refine le_trans ?_ (sourceRieszLocal_full_transport_bound s 1 hs hv p)
    by_cases hp : p ∈ sourceLogTruncSet (ι := ι) ε
    · simp only [indicator_of_mem hp, le_refl]
    · rw [indicator_of_notMem hp, abs_zero]; exact abs_nonneg _
  · by_cases hp : p.1 = p.2
    · have h0 : sourceRieszTransportKernel 1 s v p = 0 := by
        simp [sourceRieszTransportKernel, hp]
      have hc : ∀ ε, (sourceLogTruncSet (ι := ι) ε).indicator
          (sourceRieszTransportKernel 1 s v) p = sourceRieszTransportKernel 1 s v p := by
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

/-- **Principal value of the unsymmetrized Riesz force term**, for every bounded
C2 test and every probability law with density at most `M`. -/
theorem tendsto_sourceRieszTruncatedForce (s : ℝ) (hs : 0 < s)
    (hd : 2 * s < (Fintype.card ι : ℝ)) (φ : E → ℝ) (hφ : SourceBoundedC2Test φ)
    (ρ : E → ℝ) (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    Tendsto (fun ε => sourceRieszTruncatedForce s (gaussianRieszDensityMeasure ρ)
        (gradient φ) ε) (𝓝[>] 0)
      (𝓝 ((1/2 : ℝ) * ∫ p, sourceRieszTransportKernel 1 s (gradient φ) p
        ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) := by
  obtain ⟨hc, C, hC, hb⟩ := (sourceBoundedC2Test_iff_classical_bounds φ).mp hφ
  let K : ℝ≥0 := ⟨C, hC⟩
  have hv : LipschitzWith K (gradient φ) :=
    sourceAdjoint_gradient_lipschitz_of_hessian_bound φ hc K (fun x => (hb x).2.2)
  have hlim := (tendsto_sourceRieszTruncatedKernel s hs hd ρ M hM hρ hv).const_mul (1/2 : ℝ)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (sourceRieszTruncatedForce_eq_half s hs _ hv.continuous hC
    (fun x => (hb x).2.1) hε).symm

/-- If the literal unsymmetrized Riesz integrand is integrable (e.g. `d ≥ 2`), its
integral is the principal value. -/
theorem integral_sourceRieszForcePairing_eq_half (s : ℝ) (hs : 0 < s)
    (hd : 2 * s < (Fintype.card ι : ℝ)) (φ : E → ℝ) (hφ : SourceBoundedC2Test φ)
    (ρ : E → ℝ) (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hint : Integrable (sourceRieszForcePairing s (gradient φ))
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    ∫ p, sourceRieszForcePairing s (gradient φ) p
        ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ) =
      (1/2 : ℝ) * ∫ p, sourceRieszTransportKernel 1 s (gradient φ) p
        ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ) := by
  have hlit : Tendsto (fun ε => sourceRieszTruncatedForce s (gaussianRieszDensityMeasure ρ)
      (gradient φ) ε) (𝓝[>] 0)
      (𝓝 (∫ p, sourceRieszForcePairing s (gradient φ) p
        ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun p => ‖sourceRieszForcePairing s (gradient φ) p‖)
      (Filter.Eventually.of_forall (fun ε =>
        hint.aestronglyMeasurable.indicator (measurableSet_sourceLogTruncSet ε)))
      (Filter.Eventually.of_forall (fun ε => Filter.Eventually.of_forall (fun p => ?_)))
      hint.norm (Filter.Eventually.of_forall (fun p => ?_))
    · exact norm_indicator_le_norm_self _ _
    · by_cases hp : p.1 = p.2
      · have h0 := sourceRieszForcePairing_diag s (gradient φ) p hp
        have hc : ∀ ε, (sourceLogTruncSet (ι := ι) ε).indicator
            (sourceRieszForcePairing s (gradient φ)) p =
              sourceRieszForcePairing s (gradient φ) p := by
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
  exact tendsto_nhds_unique hlit (tendsto_sourceRieszTruncatedForce s hs hd φ hφ ρ M hM hρ)

/-- Principal-value form of the positive-Riesz tested drift. -/
def sourceRieszPVMeanTestDrift (s β : ℝ) (μ : Measure E) (φ : E → ℝ) : ℝ :=
  β⁻¹ * (∫ x, laplacian φ x ∂μ) -
    limUnder (𝓝[>] (0 : ℝ)) (fun ε => sourceRieszTruncatedForce s μ (gradient φ) ε)

theorem sourceRieszPVMeanTestDrift_eq (s β : ℝ) (hs : 0 < s)
    (hd : 2 * s < (Fintype.card ι : ℝ)) (ρ : E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (φ : E → ℝ) (hφ : SourceBoundedC2Test φ) :
    sourceRieszPVMeanTestDrift s β (gaussianRieszDensityMeasure ρ) φ =
      sourceRieszStaticMeanTestDrift s β ρ φ := by
  unfold sourceRieszPVMeanTestDrift sourceRieszStaticMeanTestDrift
  rw [(tendsto_sourceRieszTruncatedForce s hs hd φ hφ ρ M hM hρ).limUnder_eq]

end DGRHS.Commutator
