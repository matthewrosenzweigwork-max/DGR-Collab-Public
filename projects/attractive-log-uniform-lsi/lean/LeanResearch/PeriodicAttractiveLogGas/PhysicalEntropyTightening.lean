import LeanResearch.PeriodicAttractiveLogGas.LargeParticleBounds
import LeanResearch.PeriodicAttractiveLogGas.AmbientClosure

/-! Rothaus tightening for the actual physical energy, followed by the
full ambient graph closure. This isolates the final assembly without
assuming any fixed-particle estimate. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal BigOperators
namespace PeriodicAttractiveLogGas.PhysicalEntropyTightening
open ResolutionEnergy ResolutionIteration OccupationMassCutoff

theorem energy_shift {N : ℕ} (β : ℝ) (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) (c : ℝ) :
    energy β (shiftValue f c) = energy β f := by
  apply integral_congr_ae
  filter_upwards [ae_shift_gradient f hf c β] with X hX
  rw [hX]

theorem tighten {N : ℕ} {β Cpi A B : ℝ}
    (hprob : IsProbabilityMeasure (gibbsMeasure greenRealRepresentative N β))
    (hB : 0 ≤ B)
    (hPI : ∀ f : C(Configuration N, ℝ), ∀ K : ℝ≥0,
      LipschitzWith K (fun y ↦ f (configurationQuotient N y)) →
        variance f (gibbsMeasure greenRealRepresentative N β) ≤ Cpi * energy β f)
    (hD : ∀ f : C(Configuration N, ℝ), ∀ K : ℝ≥0,
      LipschitzWith K (fun y ↦ f (configurationQuotient N y)) →
        entropy (gibbsMeasure greenRealRepresentative N β) (fun X ↦ f X ^ 2) ≤
          ((A * energy β f + B * squareIntegral β f : ℝ) : EReal))
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    entropy (gibbsMeasure greenRealRepresentative N β) (fun X ↦ f X ^ 2) ≤
      (((A + (B + 2) * Cpi) * energy β f : ℝ) : EReal) := by
  let μ := gibbsMeasure greenRealRepresentative N β
  let g := shiftValue f (∫ X, f X ∂μ)
  have hg := shift_lift_lipschitz f hf (∫ X, f X ∂μ)
  have hb : ∀ X, |f X| ≤ ‖f‖ := fun X ↦ by
    simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm X
  have hr := rothaus_centering (μ := μ) f.continuous.measurable ⟨‖f‖, hb⟩
  change entropy μ (fun X ↦ f X ^ 2) ≤ entropy μ (fun X ↦ g X ^ 2) +
    ((2 * squareIntegral β g : ℝ) : EReal) at hr
  rw [continuous_entropy_eq, continuous_entropy_eq, ← EReal.coe_add] at hr
  have hd := hD g K hg
  rw [continuous_entropy_eq, energy_shift β f hf] at hd
  have hp := hPI f K hf
  rw [variance_eq_integral f.continuous.measurable.aemeasurable] at hp
  change squareIntegral β g ≤ Cpi * energy β f at hp
  have hm := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ B + 2)
  rw [continuous_entropy_eq]
  apply EReal.coe_le_coe_iff.mpr
  have hr' := EReal.coe_le_coe_iff.mp hr
  have hd' := EReal.coe_le_coe_iff.mp hd
  nlinarith only [hr', hd', hm]

theorem smooth_descended_gradient {N : ℕ} (f : SmoothPair N) (X : Configuration N) :
    descendedLiftGradient f.value X = f.gradient X := by
  obtain ⟨y, rfl⟩ := configurationQuotient_surjective N X
  rw [descendedLiftGradient_eq_riesz_differential,
    descendedLiftDifferential_configurationQuotient, (f.differential y).fderiv]
  exact (InnerProductSpace.toDual ℝ (Gradient N)).symm_apply_apply _

theorem smooth_energy {N : ℕ} (β : ℝ) (f : SmoothPair N) :
    energy β f.value = ∫ X, ∑ i : Fin N, ∑ k : Fin 2, f.gradient X (i, k) ^ 2
      ∂gibbsMeasure greenRealRepresentative N β := by
  unfold energy
  apply integral_congr_ae
  filter_upwards [] with X
  rw [smooth_descended_gradient]
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Real.norm_eq_abs, sq_abs]

theorem ambient_of_physical_bound {N : ℕ} {β C : ℝ}
    (hL : ∀ f : C(Configuration N, ℝ), ∀ K : ℝ≥0,
      LipschitzWith K (fun y ↦ f (configurationQuotient N y)) →
        entropy (gibbsMeasure greenRealRepresentative N β) (fun X ↦ f X ^ 2) ≤
          ((2 * C * energy β f : ℝ) : EReal))
    (f : GreenAmbientFormDomain N β) :
    entropy (gibbsMeasure greenRealRepresentative N β) (fun X ↦ ambientValue f X ^ 2) ≤
      ((2 * C * ambientEnergy f : ℝ) : EReal) := by
  apply ambient_entropy_le_of_smooth_bound (f := f)
  intro s
  have hh := hL s.value ‖s.gradient‖₊ s.lipschitz_configurationLift
  rw [smooth_energy β s] at hh
  exact hh

/-- Uniform full-labelled LSI on the actual ambient domain for all N above
one threshold. The finite set of smaller particle numbers remains separate. -/
theorem exists_large_particle_ambient_lsi {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ β : ℝ, 0 ≤ β → β ≤ β₀ →
        ∀ f : GreenAmbientFormDomain N β,
          entropy (gibbsMeasure greenRealRepresentative N β) (fun X ↦ ambientValue f X ^ 2) ≤
            ((2 * C * ambientEnergy f : ℝ) : EReal) := by
  obtain ⟨Cpi, A, B, hCpi, hA, hB, N₀, hN₀, hlarge⟩ :=
    LargeParticleBounds.exists_large_particle_bounds hβ₀ hsub
  let C : ℝ := (A + (B + 2) * Cpi) / 2
  have hC : 0 ≤ C := div_nonneg (add_nonneg hA (mul_nonneg (by linarith) hCpi)) (by norm_num)
  refine ⟨C, hC, N₀, hN₀, fun N hN β hβ hβle f ↦ ?_⟩
  have hb := hlarge N hN β hβ hβle
  have hp := isProbabilityMeasure_greenGibbs N (hN₀.trans hN) hβ (hβle.trans_lt hsub)
  apply ambient_of_physical_bound (f := f)
  intro F K hF
  have hh := tighten hp hB (fun F K hF ↦ (hb F K hF).1)
    (fun F K hF ↦ (hb F K hF).2) F hF
  have he : 2 * C = A + (B + 2) * Cpi := by unfold C; ring
  rw [he]
  exact hh

end PeriodicAttractiveLogGas.PhysicalEntropyTightening
