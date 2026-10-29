import DGRHS.Concentration.MasterSize

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace DGRHS.Concentration

/-- The limit-side cutoff comparison follows from the actual finite-particle
comparison and both partition limits; no determinant continuity is assumed. -/
theorem partition_limit_comparison (Z Y : ℕ → ℝ) (z y E : ℝ)
    (hZ : Tendsto Z atTop (𝓝 z)) (hY : Tendsto Y atTop (𝓝 y))
    (hComp : ∀ n, 1 ≤ n → |Z n-Y n| ≤ E) : |z-y| ≤ E := by
  apply le_of_tendsto ((hZ.sub hY).abs)
  exact (eventually_ge_atTop 1).mono fun n hn ↦ hComp n hn

/-- Actual finite-N and limit-side comparisons isolate the separate fixed-scale
Laplace error. This proves the assembly step without an assumed full rate. -/
theorem partition_error_assembly (Z Y : ℕ → ℝ) (z y E : ℝ)
    (hZ : Tendsto Z atTop (𝓝 z)) (hY : Tendsto Y atTop (𝓝 y))
    (hComp : ∀ n, 1 ≤ n → |Z n-Y n| ≤ E) (n : ℕ) (hn : 1 ≤ n) :
    |Z n-z| ≤ 2*E+|Y n-y| := by
  have hl := partition_limit_comparison Z Y z y E hZ hY hComp
  calc
    _ ≤ |Z n-Y n|+|Y n-z| := abs_sub_le _ _ _
    _ ≤ |Z n-Y n|+(|Y n-y|+|y-z|) := add_le_add le_rfl (abs_sub_le _ _ _)
    _ ≤ E+(|Y n-y|+E) := by
      rw [abs_sub_comm y z]
      exact add_le_add (hComp n hn) (add_le_add le_rfl hl)
    _ = _ := by ring

/-- The scalar exponential tangent derives the canonical partition lower bound
from the actual mean-zero exponent and its proper integrals. -/
lemma canonical_exponential_integral_one_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hXi : Integrable X μ) (hEi : Integrable (fun ω ↦ Real.exp (X ω)) μ)
    (hZero : (∫ ω,X ω ∂μ) = 0) : 1 ≤ (∫ ω,Real.exp (X ω) ∂μ) := by
  have hb := integral_mono (hXi.add (integrable_const (1 : ℝ))) hEi
    (fun ω ↦ Real.add_one_le_exp (X ω))
  simp only [Pi.add_apply] at hb
  rw [integral_add hXi (integrable_const (1 : ℝ)),hZero] at hb
  simpa using hb

/-- Log is Lipschitz with constant one on [1,infinity), proved from its scalar
sub-one bound with exact positive denominators. -/
lemma abs_log_sub_le_abs_sub_of_one_le (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |Real.log x-Real.log y| ≤ |x-y| := by
  have hSide : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → b ≤ a → Real.log a-Real.log b ≤ a-b := by
    intro a b ha hb hab
    have ha' : 0 < a := lt_of_lt_of_le zero_lt_one ha
    have hb' : 0 < b := lt_of_lt_of_le zero_lt_one hb
    have he : a/b-1 = (a-b)/b := by field_simp
    calc
      _ = Real.log (a/b) := (Real.log_div ha'.ne' hb'.ne').symm
      _ ≤ a/b-1 := Real.log_le_sub_one_of_pos (div_pos ha' hb')
      _ = (a-b)/b := he
      _ ≤ a-b := by
        apply (div_le_iff₀ hb').2
        nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hb)]
  by_cases hxy : y ≤ x
  · have hLog : Real.log y ≤ Real.log x := Real.log_le_log (lt_of_lt_of_le zero_lt_one hy) hxy
    rw [abs_of_nonneg (sub_nonneg.mpr hLog),abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact hSide x y hx hy hxy
  · have hyx : x ≤ y := le_of_not_ge hxy
    have hLog : Real.log x ≤ Real.log y := Real.log_le_log (lt_of_lt_of_le zero_lt_one hx) hyx
    rw [abs_of_nonpos (sub_nonpos.mpr hLog),abs_of_nonpos (sub_nonpos.mpr hyx)]
    simpa only [neg_sub] using hSide y x hy hx hyx

/-- Proper log-normalizer convergence and the explicit inherited error. The
positive limit is derived from the finite partition lower bounds. -/
theorem log_partition_limit_and_error (Z : ℕ → ℝ) (z : ℝ)
    (hZ : Tendsto Z atTop (𝓝 z)) (hOne : ∀ n, 1 ≤ n → 1 ≤ Z n) :
    1 ≤ z ∧ Tendsto (fun n ↦ Real.log (Z n)) atTop (𝓝 (Real.log z)) ∧
      ∀ n, 1 ≤ n → |Real.log (Z n)-Real.log z| ≤ |Z n-z| := by
  have hz : 1 ≤ z := ge_of_tendsto hZ ((eventually_ge_atTop 1).mono fun n hn ↦ hOne n hn)
  refine ⟨hz,(Real.continuousAt_log (ne_of_gt (lt_of_lt_of_le zero_lt_one hz))).tendsto.comp hZ,?_⟩
  exact fun n hn ↦ abs_log_sub_le_abs_sub_of_one_le (Z n) z (hOne n hn) hz

/-- Concrete proper exponential normalizers: mean-zero exponents give the
positive lower bound, actual finite comparison and convergence give the
limit-side comparison, and both normalizer and log errors are assembled. -/
theorem canonical_log_partition_assembly {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : (n : ℕ) → (Fin n → Ω) → ℝ)
    (hXi : ∀ n, 1 ≤ n → Integrable (X n) (Measure.pi (fun _ : Fin n ↦ μ)))
    (hEi : ∀ n, 1 ≤ n → Integrable (fun ω ↦ Real.exp (X n ω)) (Measure.pi (fun _ : Fin n ↦ μ)))
    (hZero : ∀ n, 1 ≤ n → (∫ ω,X n ω ∂Measure.pi (fun _ : Fin n ↦ μ)) = 0)
    (Y : ℕ → ℝ) (z y E : ℝ)
    (hZ : Tendsto (fun n ↦ ∫ ω,Real.exp (X n ω) ∂Measure.pi (fun _ : Fin n ↦ μ)) atTop (𝓝 z))
    (hY : Tendsto Y atTop (𝓝 y))
    (hComp : ∀ n, 1 ≤ n → |(∫ ω,Real.exp (X n ω) ∂Measure.pi (fun _ : Fin n ↦ μ))-Y n| ≤ E) :
    1 ≤ z ∧
    Tendsto (fun n ↦ Real.log (∫ ω,Real.exp (X n ω) ∂Measure.pi (fun _ : Fin n ↦ μ))) atTop (𝓝 (Real.log z)) ∧
    ∀ n, 1 ≤ n →
      |(∫ ω,Real.exp (X n ω) ∂Measure.pi (fun _ : Fin n ↦ μ))-z| ≤ 2*E+|Y n-y| ∧
      |Real.log (∫ ω,Real.exp (X n ω) ∂Measure.pi (fun _ : Fin n ↦ μ))-Real.log z| ≤ 2*E+|Y n-y| := by
  let Z := fun n ↦ ∫ ω,Real.exp (X n ω) ∂Measure.pi (fun _ : Fin n ↦ μ)
  have hOne : ∀ n, 1 ≤ n → 1 ≤ Z n := fun n hn ↦
    canonical_exponential_integral_one_le (Measure.pi (fun _ : Fin n ↦ μ)) (X n) (hXi n hn) (hEi n hn) (hZero n hn)
  obtain ⟨hz,hLog,hErr⟩ := log_partition_limit_and_error Z z hZ hOne
  refine ⟨hz,hLog,?_⟩
  intro n hn
  have hb := partition_error_assembly Z Y z y E hZ hY hComp n hn
  exact ⟨hb,(hErr n hn).trans hb⟩

#print axioms DGRHS.Concentration.partition_limit_comparison
#print axioms DGRHS.Concentration.partition_error_assembly
#print axioms DGRHS.Concentration.canonical_exponential_integral_one_le
#print axioms DGRHS.Concentration.abs_log_sub_le_abs_sub_of_one_le
#print axioms DGRHS.Concentration.log_partition_limit_and_error
#check @DGRHS.Concentration.log_partition_limit_and_error
#print axioms DGRHS.Concentration.canonical_log_partition_assembly
#check @DGRHS.Concentration.canonical_log_partition_assembly
end DGRHS.Concentration
