import DGPS.Lipschitz.T01ReferenceEigenbasis
import DGPS.Lipschitz.WeakChainRule
import DGPS.Foundations.AbsoluteDensity
import SharpSymmetricLSI.Paper.Defective8
import SharpSymmetricLSI.Paper.Defective9
import SharpSymmetricLSI.Paper.Defective15

/-!
# Conditional marginal Sobolev domains

The inherited marginal differentiation theorem is independent of potential assumptions.
Here its conditional densities are placed in the campaign's absolute Sobolev domain using
the genuine square-integrable conditional gradient. No semiconvexity hypothesis is imported.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

section Conditional

variable {d N j : ℕ} (hj : j < N)
  {Q : SharpLSI.Config N d → ℝ}
  {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
  (hQm : Measurable Q)
  (hGm : ∀ a, Measurable (fun y => GQ y a))
  (hG2 : ∀ a, MemLp (fun y => GQ y a) 2 volume)

include hGm hG2 in
/-- Averaging the unrevealed coordinates preserves the square-integrable derivative.
This is Jensen on each conditional fiber, followed by Tonelli. -/
theorem conditional_gradMarg_memLp :
    ∀ᵐ p ∂(volume : Measure (SharpLSI.Config j d)), ∀ k,
      MemLp (fun x => SharpLSI.gradMarg hj GQ p x k) 2 (haar d) := by
  rw [ae_all_iff]
  intro k
  let G := fun y => GQ y (⟨j, hj⟩, k)
  have hGmeas : Measurable G := hGm _
  have hGsq : Integrable (fun y => G y ^ 2) volume := (hG2 _).integrable_sq
  have hfin : (∫⁻ y, ENNReal.ofReal (G y ^ 2)) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hGsq.hasFiniteIntegral).ne
  have hM : Measurable (Function.uncurry fun (p : SharpLSI.Config j d) (x : Torus d) =>
      SharpLSI.gradMarg hj GQ p x k) :=
    (((hGmeas.comp SharpLSI.measurable_flat).comp
      (SharpLSI.measurable_assemble hj)).stronglyMeasurable.integral_prod_right').measurable
  have hle : (∫⁻ p, ∫⁻ x, ENNReal.ofReal (SharpLSI.gradMarg hj GQ p x k ^ 2) ∂haar d)
      ≤ ∫⁻ y, ENNReal.ofReal (G y ^ 2) := by
    rw [← (SharpLSI.measurePreserving_flat' N).lintegral_comp
      ((hGmeas.pow_const 2).ennreal_ofReal),
      SharpLSI.lintegral_assemble hj (G := fun X => ENNReal.ofReal (G (SharpLSI.flat X) ^ 2))
        (((hGmeas.comp SharpLSI.measurable_flat).pow_const 2).ennreal_ofReal)]
    refine lintegral_mono fun p => lintegral_mono fun x => ?_
    exact SharpLSI.ofReal_sq_integral_le
      ((hGmeas.comp SharpLSI.measurable_flat).comp ((SharpLSI.measurable_assemble hj).comp
        ((measurable_const (a := (p, x))).prodMk measurable_id))).aestronglyMeasurable
  have hae := ae_lt_top'
    (((hM.pow_const 2).ennreal_ofReal).lintegral_prod_right').aemeasurable
    (ne_top_of_le_ne_top hfin hle)
  filter_upwards [hae] with p hp
  refine (memLp_two_iff_integrable_sq (hM.of_uncurry_left).aestronglyMeasurable).mpr ?_
  exact (lintegral_ofReal_ne_top_iff_integrable
    ((hM.of_uncurry_left).pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun x => sq_nonneg _)).mp hp.ne

include hQm hGm hG2 in
/-- Conditional marginal densities of a bounded positive joint Sobolev density have
the campaign weak gradient given by the normalized marginal derivative. -/
theorem conditional_density_isWeakGradient
    {c C : ℝ} (hc : 0 < c) (hQc : ∀ X, c ≤ Q X) (hQC : ∀ X, Q X ≤ C)
    (hQw : SharpLSI.IsWeakGrad (Q ∘ SharpLSI.unflat) GQ) :
    ∀ᵐ p ∂(volume : Measure (SharpLSI.Config j d)),
      IsWeakGradient (SharpLSI.condDens hj Q p)
        (fun x => WithLp.toLp 2 (fun k =>
          SharpLSI.gradMarg hj GQ p x k / SharpLSI.Zc hj Q p)) := by
  have hQi : Integrable (Q ∘ SharpLSI.unflat) volume := by
    refine Integrable.of_bound (hQm.comp SharpLSI.measurable_unflat).aestronglyMeasurable C
      (Eventually.of_forall fun y => ?_)
    change ‖Q (SharpLSI.unflat y)‖ ≤ C
    rw [Real.norm_eq_abs, abs_of_pos (hc.trans_le (hQc _))]
    exact hQC _
  have hGi := fun a => (hG2 a).integrable one_le_two
  have hweak := SharpLSI.ae_isWeakGrad_margQ hj hQw hQi hGi
  filter_upwards [hweak, conditional_gradMarg_memLp hj hGm hG2] with p hp hp2
  have hρm : Measurable (SharpLSI.condDens hj Q p) :=
    (SharpLSI.measurable_condDens hj hQm).of_uncurry_left
  have hC : 0 < C := hc.trans_le ((hQc (Classical.arbitrary _)).trans (hQC _))
  have hρ2 : MemLp (SharpLSI.condDens hj Q p) 2 (haar d) := by
    apply (memLp_top_of_bound hρm.aestronglyMeasurable (C / c) ?_).mono_exponent le_top
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        ((div_pos hc hC).le.trans (SharpLSI.condDens_bounds hj hQm hc hQc hQC p x).1)]
      exact (SharpLSI.condDens_bounds hj hQm hc hQc hQC p x).2
  have hρw : SharpLSI.IsWeakGrad (SharpLSI.condDens hj Q p)
      (fun x k => SharpLSI.gradMarg hj GQ p x k / SharpLSI.Zc hj Q p) := by
    convert hp.cmul (1 / SharpLSI.Zc hj Q p) using 1
    · funext x; unfold SharpLSI.condDens; ring
    · funext x k; ring
  apply isWeakGradient_of_legacy_pair hρw hρ2
  apply memLp_piLp_iff.mpr
  intro k
  change MemLp (fun x => SharpLSI.gradMarg hj GQ p x k / SharpLSI.Zc hj Q p) 2 (haar d)
  have hh := (hp2 k).const_mul (SharpLSI.Zc hj Q p)⁻¹
  simpa only [div_eq_mul_inv, mul_comm] using hh

include hQm hGm hG2 in
/-- The conditional marginals belong to the unchanged absolute admissible domain.
The lower bound is used only to apply the square-root weak chain rule. -/
theorem conditional_marginal_absolute_domain
    {c C : ℝ} (hc : 0 < c) (hQc : ∀ X, c ≤ Q X) (hQC : ∀ X, Q X ≤ C)
    (hQw : SharpLSI.IsWeakGrad (Q ∘ SharpLSI.unflat) GQ) :
    ∀ᵐ p ∂(volume : Measure (SharpLSI.Config j d)),
      ∃ ρ : AbsoluteDensity d, ∀ x, ρ.density x = SharpLSI.condDens hj Q p x := by
  have hC : 0 < C := hc.trans_le ((hQc (Classical.arbitrary _)).trans (hQC _))
  have hlo : 0 < c / C := div_pos hc hC
  have ha : 0 < (c / C) / 2 := by positivity
  obtain ⟨M, hM⟩ := SharpLSI.exists_bound_deriv_sqrtCut ha
  filter_upwards [conditional_density_isWeakGradient hj hQm hGm hG2 hc hQc hQC hQw] with p hp
  have hs := WeakChainRule.isWeakGradient_comp (SharpLSI.contDiff_sqrtCut ha) hM hp
  have hfun : (fun x => SharpLSI.sqrtCut ((c / C) / 2) (SharpLSI.condDens hj Q p x)) =
      fun x => Real.sqrt (SharpLSI.condDens hj Q p x) := by
    funext x
    apply SharpLSI.sqrtCut_eq ha
    have := (SharpLSI.condDens_bounds hj hQm hc hQc hQC p x).1
    linarith
  rw [hfun] at hs
  have hρ0 : ∀ x, 0 ≤ SharpLSI.condDens hj Q p x := fun x =>
    hlo.le.trans (SharpLSI.condDens_bounds hj hQm hc hQc hQC p x).1
  refine ⟨{
    sqrt := fun x => Real.sqrt (SharpLSI.condDens hj Q p x)
    sqrt_mem := ⟨_, hs⟩
    sqrt_nonneg := Eventually.of_forall fun x => Real.sqrt_nonneg _
    mass_one := ?_ }, ?_⟩
  · simp_rw [Real.sq_sqrt (hρ0 _)]
    exact SharpLSI.integral_condDens hj hQm hc hQc hQC p
  · intro x
    exact Real.sq_sqrt (hρ0 x)

include hQm in
/-- Conditional marginal score identity from the joint density derivative.
For the Gibbs application `F` is the particle score minus the centered force and `v`
is one coordinate of the reference potential gradient. Only integrability of `F Q`
is needed; the score need not be bounded. -/
theorem conditional_marginal_score_identity
    {c C : ℝ} (hc : 0 < c) (hQc : ∀ X, c ≤ Q X) (hQC : ∀ X, Q X ≤ C)
    (k : Fin d) (F : SharpLSI.Config N d → ℝ) (v : Torus d → ℝ)
    (hFQ : Integrable (fun X => F X * Q X) volume)
    (hscore : ∀ᵐ X ∂(volume : Measure (SharpLSI.Config N d)),
      GQ (SharpLSI.flat X) (⟨j, hj⟩, k) =
      Q X * (F X - v (X ⟨j, hj⟩))) :
    ∀ᵐ q ∂((volume : Measure (SharpLSI.Config j d)).prod (haar d)),
      SharpLSI.gradMarg hj GQ q.1 q.2 k / SharpLSI.margQ hj Q q.1 q.2 + v q.2 =
        SharpLSI.condRatio hj Q F q.1 q.2 := by
  have hslice : ∀ᵐ q ∂((volume : Measure (SharpLSI.Config j d)).prod (haar d)),
      Integrable (fun z => F (SharpLSI.assemble hj q.1 q.2 z) *
        Q (SharpLSI.assemble hj q.1 q.2 z))
        (volume : Measure (SharpLSI.Config (N - j - 1) d)) :=
    ((SharpLSI.measurePreserving_assemble (d := d) hj).integrable_comp_of_integrable
      hFQ).prod_right_ae
  have hscore_slice := Measure.ae_ae_of_ae_prod
    ((SharpLSI.measurePreserving_assemble (d := d) hj).quasiMeasurePreserving.ae hscore)
  filter_upwards [hslice, hscore_slice] with q hq hscore_q
  have hm0 : 0 < SharpLSI.margQ hj Q q.1 q.2 :=
    hc.trans_le (SharpLSI.margQ_bounds hj hQm hQc hQC q.1 q.2).1
  have hzm : Measurable fun z : SharpLSI.Config (N - j - 1) d =>
      SharpLSI.assemble hj q.1 q.2 z :=
    (SharpLSI.measurable_assemble hj).comp
      ((measurable_const (a := q)).prodMk measurable_id)
  have hQi : Integrable (fun z => Q (SharpLSI.assemble hj q.1 q.2 z))
      (volume : Measure (SharpLSI.Config (N - j - 1) d)) := by
    refine Integrable.of_bound (hQm.comp hzm).aestronglyMeasurable C
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (hc.trans_le (hQc _))]
    exact hQC _
  have hgrad : SharpLSI.gradMarg hj GQ q.1 q.2 k =
      (∫ z, F (SharpLSI.assemble hj q.1 q.2 z) * Q (SharpLSI.assemble hj q.1 q.2 z)
        ∂(volume : Measure (SharpLSI.Config (N - j - 1) d))) -
      v q.2 * SharpLSI.margQ hj Q q.1 q.2 := by
    unfold SharpLSI.gradMarg SharpLSI.margQ
    have heq : (fun z => GQ (SharpLSI.flat (SharpLSI.assemble hj q.1 q.2 z)) (⟨j, hj⟩, k))
        =ᵐ[(volume : Measure (SharpLSI.Config (N - j - 1) d))]
        fun z => F (SharpLSI.assemble hj q.1 q.2 z) * Q (SharpLSI.assemble hj q.1 q.2 z) -
          v q.2 * Q (SharpLSI.assemble hj q.1 q.2 z) := by
      filter_upwards [hscore_q] with z hz
      rw [hz, SharpLSI.cur_assemble]
      ring
    rw [integral_congr_ae heq, integral_sub hq (hQi.const_mul _), integral_const_mul]
  rw [hgrad]
  unfold SharpLSI.condRatio
  field_simp [hm0.ne']
  <;> ring

end Conditional

end DGPS.Lipschitz
