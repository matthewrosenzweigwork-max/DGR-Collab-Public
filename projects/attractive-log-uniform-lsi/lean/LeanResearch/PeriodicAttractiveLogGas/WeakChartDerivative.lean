import LeanResearch.PeriodicAttractiveLogGas.WeakChartCalculus
import LeanResearch.PeriodicAttractiveLogGas.MollifierDerivativeLimit
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Source-only candidate for the ordinary almost-everywhere interpretation
of the weak fields in manuscript Lemma 3.5. A Lipschitz function on a compact
convex physical Euclidean chart is extended by the proved real-valued
Lipschitz extension theorem. Actual mass-one compact smooth convolutions,
Rademacher and dominated convergence identify its ordinary gradient as a
weak gradient. Uniqueness of locally integrable distributions identifies
the supplied weak field, and the convex boundary is Lebesgue null.

No weak-gradient identity for Lipschitz functions, uniqueness conclusion,
ordinary derivative compatibility, or almost-everywhere identification is
an assumption. Behavior away from the closed chart is unrestricted. The
index type may be empty. The author performs no Lean execution. -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology ContDiff Convolution RealInnerProductSpace

namespace PeriodicAttractiveLogGas.WeakChartDerivative

open WeakChartCalculus MovingPoleNumerators

variable {d : Type*} [Fintype d]

/-- The totalized ordinary Euclidean Riesz gradient. -/
def ordinaryGradient (f : ChartSpace d → ℝ) (x : ChartSpace d) : ChartSpace d :=
  (InnerProductSpace.toDual ℝ (ChartSpace d)).symm (fderiv ℝ f x)

theorem measurable_ordinaryGradient (f : ChartSpace d → ℝ) : Measurable (ordinaryGradient f) :=
  (InnerProductSpace.toDual ℝ (ChartSpace d)).symm.continuous.measurable.comp
    (measurable_fderiv ℝ f)

theorem norm_ordinaryGradient (f : ChartSpace d → ℝ) (x : ChartSpace d) :
    ‖ordinaryGradient f x‖ = ‖fderiv ℝ f x‖ :=
  (InnerProductSpace.toDual ℝ (ChartSpace d)).symm.norm_map _

theorem hasFDerivAt_ordinaryGradient {f : ChartSpace d → ℝ} {x : ChartSpace d}
    (hx : DifferentiableAt ℝ f x) :
    HasFDerivAt f (InnerProductSpace.toDual ℝ (ChartSpace d) (ordinaryGradient f x)) x := by
  simpa only [ordinaryGradient, LinearIsometryEquiv.apply_symm_apply] using hx.hasFDerivAt

def unitBump (d : Type*) [Fintype d] : ContDiffBump (0 : ChartSpace d) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

def unitKernel (d : Type*) [Fintype d] : ChartSpace d → ℝ := (unitBump d).normed volume

theorem unitKernel_nonneg (x : ChartSpace d) : 0 ≤ unitKernel d x :=
  (unitBump d).nonneg_normed x

theorem unitKernel_smooth : ContDiff ℝ ∞ (unitKernel d) := (unitBump d).contDiff_normed

theorem unitKernel_compact : HasCompactSupport (unitKernel d) :=
  (unitBump d).hasCompactSupport_normed

theorem unitKernel_mass : (∫ x, unitKernel d x) = 1 := (unitBump d).integral_normed

theorem unitKernel_support : tsupport (unitKernel d) ⊆ closedBall (0 : ChartSpace d) 1 := by
  rw [show tsupport (unitKernel d) = closedBall (0 : ChartSpace d) (1 / 2 : ℝ) from
    (unitBump d).tsupport_normed_eq]
  exact closedBall_subset_closedBall (by norm_num)

def kernel (d : Type*) [Fintype d] (n : ℕ) : ChartSpace d → ℝ :=
  mollifierDilate (unitKernel d) (approximationScale n)

theorem kernel_compact (n : ℕ) : HasCompactSupport (kernel d n) :=
  hasCompactSupport_mollifierDilate (E := ChartSpace d) (ρ := unitKernel d)
    (unitKernel_compact (d := d)) (approximationScale_pos n)

theorem kernel_smooth (n : ℕ) : ContDiff ℝ ∞ (kernel d n) :=
  contDiff_mollifierDilate (unitKernel_smooth (d := d)) _

theorem kernel_integrable (n : ℕ) : Integrable (kernel d n) volume :=
  (kernel_smooth n).continuous.integrable_of_hasCompactSupport (kernel_compact n)

theorem kernel_nonneg (n : ℕ) (x : ChartSpace d) : 0 ≤ kernel d n x :=
  mollifierDilate_nonneg unitKernel_nonneg (approximationScale_pos n) x

theorem kernel_mass (n : ℕ) : (∫ x, kernel d n x) = 1 :=
  (integral_mollifierDilate (ρ := unitKernel d) volume (approximationScale_pos n)).trans
    (unitKernel_mass (d := d))

theorem kernel_support (n : ℕ) :
    Function.support (kernel d n) ⊆ closedBall (0 : ChartSpace d) (approximationScale n) := by
  simpa only [mul_one] using (subset_tsupport (kernel d n)).trans
    (tsupport_mollifierDilate_subset (approximationScale_pos n) (unitKernel_support (d := d)))

def mollification (f : ChartSpace d → ℝ) (n : ℕ) : ChartSpace d → ℝ :=
  kernel d n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f

theorem mollification_smooth {f : ChartSpace d → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (n : ℕ) : ContDiff ℝ ∞ (mollification f n) :=
  contDiff_mollifierDilate_convolution (E := ChartSpace d) (ρ := unitKernel d) (f := f)
    volume (unitKernel_compact (d := d)) (unitKernel_smooth (d := d))
    hf.continuous (approximationScale_pos n)

theorem mollification_gradient_bound {f : ChartSpace d → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (n : ℕ) (x : ChartSpace d) :
    ‖ordinaryGradient (mollification f n) x‖ ≤ (K : ℝ) := by
  rw [norm_ordinaryGradient]
  exact norm_fderiv_mollifierDilate_convolution_le (E := ChartSpace d) (ρ := unitKernel d)
    volume (unitKernel_compact (d := d)) (unitKernel_smooth (d := d))
    (unitKernel_nonneg (d := d)) (unitKernel_mass (d := d)) hf (approximationScale_pos n) x

theorem mollification_dist_bound {f : ChartSpace d → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (n : ℕ) (x : ChartSpace d) :
    dist (mollification f n x) (f x) ≤ (K : ℝ) * (1 / 16 : ℝ) := by
  exact (dist_probability_convolution_le (E := ChartSpace d) (ρ := kernel d n)
    (kernel_compact (d := d) n) (kernel_integrable (d := d) n)
    (kernel_nonneg (d := d) n) (kernel_mass (d := d) n) hf (approximationScale_pos n).le
    (kernel_support (d := d) n) x).trans
      (mul_le_mul_of_nonneg_left (approximationScale_small n) K.coe_nonneg)

theorem mollification_uniform_limit {f : ChartSpace d → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : TendstoUniformly (mollification f) f atTop :=
  tendstoUniformly_probability_convolution (E := ChartSpace d) (kernel d) approximationScale
    (kernel_compact (d := d)) (kernel_integrable (d := d)) (kernel_nonneg (d := d))
    (kernel_mass (d := d)) hf (fun n ↦ (approximationScale_pos n).le)
    (kernel_support (d := d)) approximationScale_tendsto

/-- Rademacher supplies the differentiability points; derivative convergence
is the separately proved ordinary convolution derivative theorem. -/
theorem mollification_gradient_limit {f : ChartSpace d → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    ∀ᵐ x ∂volume, Tendsto (fun n ↦ ordinaryGradient (mollification f n) x) atTop
      (𝓝 (ordinaryGradient f x)) := by
  filter_upwards [hf.ae_differentiableAt (μ := (volume : Measure (ChartSpace d)))] with x hx
  apply (InnerProductSpace.toDual ℝ (ChartSpace d)).symm.continuous.continuousAt.tendsto.comp
  exact tendsto_fderiv_mollifierDilate_convolution (E := ChartSpace d) (ρ := unitKernel d)
    volume approximationScale_pos approximationScale_tendsto
    (unitKernel_compact (d := d)) (unitKernel_smooth (d := d)) (unitKernel_mass (d := d))
    hf.continuous hx.hasFDerivAt

/-- The actual ordinary gradient of a globally Lipschitz real function is a
weak gradient on every compact chart. This is proved by smooth convolution,
not taken as a weak differentiation premise. -/
theorem weakGradientOn_of_lipschitz {S : Set (ChartSpace d)} (hS : IsCompact S)
    {f : ChartSpace d → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    WeakGradientOn S f (ordinaryGradient f) := by
  let : IsFiniteMeasure ((volume : Measure (ChartSpace d)).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  obtain ⟨A, hA, hb⟩ := (hS.image hf.continuous).isBounded.exists_pos_norm_le
  have hfb (x : ChartSpace d) (hx : x ∈ S) : ‖f x‖ ≤ A := hb _ ⟨x, hx, rfl⟩
  have hgb (x : ChartSpace d) : ‖ordinaryGradient f x‖ ≤ (K : ℝ) := by
    rw [norm_ordinaryGradient]
    exact norm_fderiv_le_of_lipschitz ℝ hf
  have hfi : IntegrableOn f S := IntegrableOn.of_bound hS.measure_lt_top
    hf.continuous.aestronglyMeasurable A
    ((ae_restrict_mem hS.measurableSet).mono fun x hx ↦ hfb x hx)
  have hgi : IntegrableOn (ordinaryGradient f) S := IntegrableOn.of_bound hS.measure_lt_top
    (measurable_ordinaryGradient f).aestronglyMeasurable K (ae_of_all _ hgb)
  have hfn (n : ℕ) (x : ChartSpace d) (hx : x ∈ S) :
      ‖mollification f n x‖ ≤ (K : ℝ) * (1 / 16 : ℝ) + A := by
    calc
      ‖mollification f n x‖ ≤ dist (mollification f n x) (f x) + ‖f x‖ :=
        by simpa only [dist_eq_norm] using norm_le_norm_sub_add (mollification f n x) (f x)
      _ ≤ _ := add_le_add (mollification_dist_bound hf n x) (hfb x hx)
  have hwn (n : ℕ) : WeakGradientOn S (mollification f n)
      (ordinaryGradient (mollification f n)) := by
    apply weakGradientOn_of_hasFDerivAt
      (IntegrableOn.of_bound hS.measure_lt_top
        (mollification_smooth hf n).continuous.aestronglyMeasurable _
        ((ae_restrict_mem hS.measurableSet).mono fun x hx ↦ hfn n x hx))
      (IntegrableOn.of_bound hS.measure_lt_top
        (measurable_ordinaryGradient (mollification f n)).aestronglyMeasurable K
        (ae_of_all _ (mollification_gradient_bound hf n)))
    intro x _
    exact hasFDerivAt_ordinaryGradient ((mollification_smooth hf n).differentiable (by simp) x)
  refine ⟨hfi, hgi, ?_⟩
  intro ψ hψ hc hψS v
  obtain ⟨D, _, hbD⟩ := test_bound
    ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hc.fderiv_apply ℝ v)
  obtain ⟨B, _, hbB⟩ := test_bound hψ.continuous hc
  have hL : Tendsto (fun n ↦ ∫ x in S, mollification f n x * fderiv ℝ ψ x v) atTop
      (𝓝 (∫ x in S, f x * fderiv ℝ ψ x v)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ ((K : ℝ) * (1 / 16) + A) * D)
      (fun n ↦ (mollification_smooth hf n).continuous.aestronglyMeasurable.mul
        ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable)
      (integrable_const _)
    · intro n
      filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
      rw [Pi.mul_apply, norm_mul]
      exact mul_le_mul (hfn n x hx) (hbD x) (norm_nonneg _) (by positivity)
    · exact ae_of_all _ fun x ↦ ((mollification_uniform_limit hf).tendsto_at x).mul_const _
  have hR : Tendsto (fun n ↦ ∫ x in S,
      inner ℝ (ordinaryGradient (mollification f n) x) v * ψ x) atTop
      (𝓝 (∫ x in S, inner ℝ (ordinaryGradient f x) v * ψ x)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ ((K : ℝ) * ‖v‖) * B)
      (fun n ↦ (measurable_ordinaryGradient (mollification f n)).aestronglyMeasurable.inner_const.mul
        hψ.continuous.aestronglyMeasurable) (integrable_const _)
    · intro n
      exact ae_of_all _ fun x ↦ by
        calc
          ‖inner ℝ (ordinaryGradient (mollification f n) x) v * ψ x‖ ≤
              (‖ordinaryGradient (mollification f n) x‖ * ‖v‖) * ‖ψ x‖ := by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
          _ ≤ _ := mul_le_mul
            (mul_le_mul_of_nonneg_right (mollification_gradient_bound hf n x) (norm_nonneg _))
            (hbB x) (norm_nonneg _) (mul_nonneg K.coe_nonneg (norm_nonneg _))
    · filter_upwards [ae_restrict_of_ae (mollification_gradient_limit hf)] with x hx
      exact (hx.inner tendsto_const_nhds).mul_const _
  apply tendsto_nhds_unique hL
  exact hR.neg.congr' (Eventually.of_forall fun n ↦ (hwn n).identity ψ hψ hc hψS v |>.symm)

/-- Uniqueness is local in the interior; the scalar functions only need
agree on the chart. The compact test remains fully multidimensional. -/
theorem weakGradientOn_unique_interior {S : Set (ChartSpace d)} (hS : MeasurableSet S)
    {f g : ChartSpace d → ℝ} {G H : ChartSpace d → ChartSpace d}
    (hf : WeakGradientOn S f G) (hg : WeakGradientOn S g H) (hfg : EqOn f g S) :
    ∀ᵐ x ∂volume, x ∈ interior S → G x = H x := by
  have hi : IntegrableOn (fun x ↦ G x - H x) S := hf.gradient_integrable.sub hg.gradient_integrable
  suffices hz : ∀ᵐ x ∂volume, x ∈ interior S → G x - H x = 0 by
    filter_upwards [hz] with x hx hxi
    exact sub_eq_zero.mp (hx hxi)
  apply isOpen_interior.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((IntegrableOn.locallyIntegrableOn hi).mono_set interior_subset)
  intro ψ hψ hc hψU
  have hψS : tsupport ψ ⊆ S := hψU.trans interior_subset
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  obtain ⟨B, _, hbB⟩ := test_bound hψ.continuous hc
  have hG : Integrable (fun x ↦ ψ x • G x) volume := by
    apply IntegrableOn.integrable_of_forall_notMem_eq_zero
      (hf.gradient_integrable.bdd_smul B hψ.continuous.aestronglyMeasurable (ae_of_all _ hbB))
    intro x hx
    change ψ x • G x = 0
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hψS h)), zero_smul]
  have hH : Integrable (fun x ↦ ψ x • H x) volume := by
    apply IntegrableOn.integrable_of_forall_notMem_eq_zero
      (hg.gradient_integrable.bdd_smul B hψ.continuous.aestronglyMeasurable (ae_of_all _ hbB))
    intro x hx
    change ψ x • H x = 0
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hψS h)), zero_smul]
  have hdiff : Integrable (fun x ↦ ψ x • (G x - H x)) volume := by
    have hiGH : Integrable (fun x ↦ ψ x • G x - ψ x • H x) volume := hG.sub hH
    exact hiGH.congr (ae_of_all _ fun x ↦ (smul_sub (ψ x) (G x) (H x)).symm)
  apply integral_eq_zero_of_forall_integral_inner_eq_zero ℝ _ hdiff
  intro v
  have hL : (∫ x in S, f x * fderiv ℝ ψ x v) =
      ∫ x in S, g x * fderiv ℝ ψ x v := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hS] with x hx
    rw [hfg hx]
  have hR : (∫ x in S, inner ℝ (G x) v * ψ x) =
      ∫ x in S, inner ℝ (H x) v * ψ x := by
    have he := hL
    rw [hf.identity ψ hψ1 hc hψS v, hg.identity ψ hψ1 hc hψS v] at he
    exact neg_injective he
  have hRs (V : ChartSpace d → ChartSpace d) :
      (∫ x in S, inner ℝ (V x) v * ψ x) = ∫ x, inner ℝ (V x) v * ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp only [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hψS h)), mul_zero]
  rw [hRs G, hRs H] at hR
  have hGe : Integrable (fun x ↦ inner ℝ (G x) v * ψ x) volume := by
    simpa only [inner_smul_right, real_inner_comm, mul_comm] using hG.const_inner (𝕜 := ℝ) v
  have hHe : Integrable (fun x ↦ inner ℝ (H x) v * ψ x) volume := by
    simpa only [inner_smul_right, real_inner_comm, mul_comm] using hH.const_inner (𝕜 := ℝ) v
  calc
    (∫ x, inner ℝ v (ψ x • (G x - H x))) =
        ∫ x, (inner ℝ (G x) v * ψ x - inner ℝ (H x) v * ψ x) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x ↦ by simp only [inner_smul_right, inner_sub_right,
        real_inner_comm, mul_sub, mul_comm]
    _ = (∫ x, inner ℝ (G x) v * ψ x) - ∫ x, inner ℝ (H x) v * ψ x :=
      integral_sub hGe hHe
    _ = 0 := sub_eq_zero.mpr hR

/-- Every weak Riesz field of a Lipschitz function on a compact convex
chart is its actual ordinary derivative almost everywhere on that chart.
The argument discards only the proved Lebesgue-null convex boundary. -/
theorem ae_hasFDerivAt_of_weakGradientOn {S : Set (ChartSpace d)} (hS : IsCompact S)
    (hconv : Convex ℝ S) {f : ChartSpace d → ℝ} {G : ChartSpace d → ChartSpace d}
    {K : ℝ≥0} (hw : WeakGradientOn S f G) (hl : LipschitzOnWith K f S) :
    ∀ᵐ x ∂(volume : Measure (ChartSpace d)).restrict S,
      HasFDerivAt f (InnerProductSpace.toDual ℝ (ChartSpace d) (G x)) x := by
  obtain ⟨g, hg, hfg⟩ := hl.extend_real
  have hu := weakGradientOn_unique_interior hS.measurableSet hw
    (weakGradientOn_of_lipschitz hS hg) hfg
  have hboundary : interior S =ᵐ[(volume : Measure (ChartSpace d))] S :=
    interior_ae_eq_of_null_frontier (hconv.addHaar_frontier volume)
  filter_upwards [ae_restrict_of_ae hu, ae_restrict_of_ae hg.ae_differentiableAt,
    ae_restrict_of_ae hboundary, ae_restrict_mem hS.measurableSet] with x hx hd hb hxs
  have hxi : x ∈ interior S := by rwa [hb]
  have he : f =ᶠ[𝓝 x] g := Filter.Eventually.mono (mem_interior_iff_mem_nhds.mp hxi)
    (fun y hy ↦ hfg hy)
  apply he.hasFDerivAt_iff.mpr
  rw [hx hxi]
  exact hasFDerivAt_ordinaryGradient hd

theorem ae_ordinaryGradient_eq_of_weakGradientOn {S : Set (ChartSpace d)} (hS : IsCompact S)
    (hconv : Convex ℝ S) {f : ChartSpace d → ℝ} {G : ChartSpace d → ChartSpace d}
    {K : ℝ≥0} (hw : WeakGradientOn S f G) (hl : LipschitzOnWith K f S) :
    ordinaryGradient f =ᵐ[(volume : Measure (ChartSpace d)).restrict S] G := by
  filter_upwards [ae_hasFDerivAt_of_weakGradientOn hS hconv hw hl] with x hx
  rw [ordinaryGradient, hx.fderiv]
  exact (InnerProductSpace.toDual ℝ (ChartSpace d)).symm_apply_apply (G x)

/-- This is transfer of an already proved ordinary a.e. derivative identity,
not a weighted integration-by-parts formula. The target law may have any
actual density; positivity is unnecessary for this direction of transfer. -/
theorem ae_hasFDerivAt_of_weakGradientOn_ac {S : Set (ChartSpace d)} (hS : IsCompact S)
    (hconv : Convex ℝ S) {f : ChartSpace d → ℝ} {G : ChartSpace d → ChartSpace d}
    {K : ℝ≥0} (hw : WeakGradientOn S f G) (hl : LipschitzOnWith K f S)
    {μ : Measure (ChartSpace d)} (hμ : μ ≪ (volume : Measure (ChartSpace d)).restrict S) :
    ∀ᵐ x ∂μ, HasFDerivAt f (InnerProductSpace.toDual ℝ (ChartSpace d) (G x)) x :=
  (ae_hasFDerivAt_of_weakGradientOn hS hconv hw hl).filter_mono hμ.ae_le

end PeriodicAttractiveLogGas.WeakChartDerivative
