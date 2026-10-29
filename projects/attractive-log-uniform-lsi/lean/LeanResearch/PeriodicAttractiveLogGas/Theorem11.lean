import LeanResearch.PeriodicAttractiveLogGas.UniformSmoothBounds

/-! Manuscript Theorem 1.1 / thm:main. The finite- and large-particle
Poincare and defective entropy inequalities are combined before Rothaus
centering, then extended by the actual ambient smooth graph closure.
No symmetry, collision avoidance, positive lower coupling, or missing
functional-inequality hypothesis is imposed. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal BigOperators
namespace PeriodicAttractiveLogGas.Theorem11

/-- Source final centering argument on the actual periodic smooth core.
The shifted test is constructed in that same core and has the same gradient. -/
theorem smooth_tightening {N : ℕ} {μ : Measure (Configuration N)}
    [IsProbabilityMeasure μ] {Cpi A B : ℝ} (hB : 0 ≤ B)
    (hPI : ∀ s : SmoothPair N, variance s.value μ ≤ Cpi * ∫ X, ‖s.gradient X‖ ^ 2 ∂μ)
    (hD : ∀ s : SmoothPair N, entropy μ (fun X => s.value X ^ 2) ≤
      ((A * (∫ X, ‖s.gradient X‖ ^ 2 ∂μ) + B * (∫ X, s.value X ^ 2 ∂μ) : ℝ) : EReal))
    (s : SmoothPair N) :
    entropy μ (fun X => s.value X ^ 2) ≤
      (((A + (B + 2) * Cpi) * ∫ X, ‖s.gradient X‖ ^ 2 ∂μ : ℝ) : EReal) := by
  let c := ∫ X, s.value X ∂μ
  let g := s.add (SmoothPair.const N (-c))
  have hval (X : Configuration N) : g.value X = s.value X - c := by
    change s.value X + -c = s.value X - c
    ring
  have hgrad (X : Configuration N) : g.gradient X = s.gradient X := by
    change s.gradient X + 0 = s.gradient X
    exact add_zero _
  have hf := s.value.continuous.measurable
  have hsb : ∀ X, |s.value X| ≤ ‖s.value‖ := fun X => by
    simpa only [Real.norm_eq_abs] using s.value.norm_coe_le_norm X
  have hfg : Measurable (fun X => s.value X - c) := hf.sub measurable_const
  obtain ⟨K, hK⟩ := DensityMoments.bounded_sub_const ⟨‖s.value‖, hsb⟩ c
  have hr := rothaus_centering (μ := μ) hf ⟨‖s.value‖, hsb⟩
  change entropy μ (fun X => s.value X ^ 2) ≤ entropy μ (fun X => (s.value X - c) ^ 2) +
    ((2 * ∫ X, (s.value X - c) ^ 2 ∂μ : ℝ) : EReal) at hr
  rw [Rothaus.entropy_sq_eq hf hsb, Rothaus.entropy_sq_eq hfg hK, ← EReal.coe_add] at hr
  have hd := hD g
  simp_rw [hval, hgrad] at hd
  rw [Rothaus.entropy_sq_eq hfg hK] at hd
  have hp := hPI s
  rw [variance_eq_integral hf.aemeasurable] at hp
  change (∫ X, (s.value X - c) ^ 2 ∂μ) ≤ Cpi * ∫ X, ‖s.gradient X‖ ^ 2 ∂μ at hp
  have hm := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ B + 2)
  rw [Rothaus.entropy_sq_eq hf hsb]
  apply EReal.coe_le_coe_iff.mpr
  have hr' := EReal.coe_le_coe_iff.mp hr
  have hd' := EReal.coe_le_coe_iff.mp hd
  nlinarith only [hr', hd', hm]

/-- The complete full-labelled ambient-domain statement, with the
additional explicit nonnegativity of the uniform constant. -/
theorem uniform_ambient_lsi {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ β : ℝ, 0 ≤ β → β ≤ β₀ →
      ∀ f : GreenAmbientFormDomain N β,
        entropy (gibbsMeasure greenRealRepresentative N β) (fun X => ambientValue f X ^ 2) ≤
          ((2 * C * ambientEnergy f : ℝ) : EReal) := by
  obtain ⟨Cpi, A, B, hCpi, hA, hB, hb⟩ :=
    UniformSmoothBounds.exists_uniform_smooth_bounds hβ₀ hsub
  let C := (A + (B + 2) * Cpi) / 2
  have hC : 0 ≤ C := div_nonneg (add_nonneg hA (mul_nonneg (by linarith) hCpi)) (by norm_num)
  have he : 2 * C = A + (B + 2) * Cpi := by unfold C; ring
  refine ⟨C, hC, ?_⟩
  intro N hN β hβ hle f
  let μ := gibbsMeasure greenRealRepresentative N β
  let : IsProbabilityMeasure μ := isProbabilityMeasure_greenGibbs N hN hβ (hle.trans_lt hsub)
  apply ambient_entropy_le_of_smooth_bound (f := f)
  intro s
  have hh := smooth_tightening (μ := μ) hB (fun s => (hb N hN β hβ hle s).1)
    (fun s => (hb N hN β hβ hle s).2) s
  rw [he]
  simpa only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Real.norm_eq_abs, sq_abs] using hh

/-- The existing, unchanged formal target, not a replacement statement. -/
theorem theorem11 : theorem11Statement := by
  intro β₀ hβ₀ hsub
  obtain ⟨C, _, hC⟩ := uniform_ambient_lsi hβ₀ hsub
  exact ⟨C, hC⟩

/-- Nonvacuity and the full theorem together for the canonical kernel. -/
theorem theorem11_with_normalization : greenNormalizationStatement ∧ theorem11Statement :=
  ⟨green_normalization, theorem11⟩

end PeriodicAttractiveLogGas.Theorem11
