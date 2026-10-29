import DGRHS.Concentration.IidControls

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace DGRHS.Concentration

/-- Countable rational heights correctly combine height-dependent null sets. -/
lemma ae_le_of_upper_tails_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (c : ℝ)
    (hTail : ∀ u, c < u → μ {ω | u ≤ X ω} = 0) : ∀ᵐ ω ∂μ, X ω ≤ c := by
  have hq : ∀ q : ℚ, ∀ᵐ ω ∂μ, c < (q : ℝ) → X ω < q := by
    intro q
    by_cases hc : c < (q : ℝ)
    · have h := measure_eq_zero_iff_ae_notMem.mp (hTail q hc)
      exact h.mono fun ω hω _ ↦ lt_of_not_ge hω
    · exact Eventually.of_forall fun _ h ↦ (hc h).elim
  filter_upwards [ae_all_iff.mpr hq] with ω hω
  by_contra hc
  obtain ⟨q,hcq,hqx⟩ := exists_rat_btwn (lt_of_not_ge hc)
  exact (lt_asymm (hω q hcq) hqx)

/-- The master proposition's bounded particle-number branch from actual per-height
comparison and cap hypotheses. The null sets may depend on the height. -/
theorem master_bounded_branch {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : AEMeasurable X μ)
    (Q : ℝ → Ω → ℝ) (m a : ℝ → ℝ) (u₀ S : ℝ) (hu₀ : 0 ≤ u₀) (hS : 0 ≤ S)
    (ha : ∀ u, u₀ ≤ u → 0 ≤ a u)
    (hCompare : ∀ u, u₀ ≤ u → ∀ᵐ ω ∂μ, u ≤ X ω → u ≤ Q u ω)
    (hCap : ∀ u, u₀ ≤ u → ∀ᵐ ω ∂μ, Q u ω ≤ m u)
    (hSize : ∀ u, u₀ ≤ u → min u (m u)*(1+a u) ≤ S) :
    (∀ᵐ ω ∂μ, X ω ≤ max u₀ S) ∧ Integrable (fun ω ↦ Real.exp (X ω)) μ ∧
      (∫ ω, Real.exp (X ω) ∂μ) ≤ Real.exp (u₀+S) := by
  have hBound : ∀ᵐ ω ∂μ, X ω ≤ max u₀ S := by
    apply ae_le_of_upper_tails_zero
    intro u hu
    have hu0 : u₀ ≤ u := (le_max_left _ _).trans hu.le
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hCompare u hu0,hCap u hu0] with ω hcmp hcap
    intro hx
    have hum : u ≤ m u := (hcmp hx).trans hcap
    have hsz : u*(1+a u) ≤ S := by simpa only [min_eq_left hum] using hSize u hu0
    have huS : u ≤ S := by nlinarith [mul_nonneg (hu₀.trans hu0) (ha u hu0)]
    exact (not_le_of_gt ((le_max_right u₀ S).trans_lt hu)) huS
  have hExpBound : ∀ᵐ ω ∂μ, Real.exp (X ω) ≤ Real.exp (u₀+S) := by
    filter_upwards [hBound] with ω hω
    apply Real.exp_le_exp.mpr
    exact hω.trans (max_le (by linarith) (by linarith))
  have hExp : Integrable (fun ω ↦ Real.exp (X ω)) μ :=
    (integrable_const (Real.exp (u₀+S))).mono'
      (Real.measurable_exp.comp_aemeasurable hX).aestronglyMeasurable
      (hExpBound.mono fun ω hω ↦ by simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hω)
  refine ⟨hBound,hExp,?_⟩
  simpa using integral_mono_ae hExp (integrable_const (Real.exp (u₀+S))) hExpBound

#print axioms DGRHS.Concentration.ae_le_of_upper_tails_zero
#print axioms DGRHS.Concentration.master_bounded_branch
#check @DGRHS.Concentration.master_bounded_branch
end DGRHS.Concentration
