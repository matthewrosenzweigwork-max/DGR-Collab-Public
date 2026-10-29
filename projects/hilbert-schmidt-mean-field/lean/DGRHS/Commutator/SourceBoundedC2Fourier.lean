import DGRHS.Commutator.SourceProbabilityWeakContinuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-! UNCOMPILED static Fourier-test admissibility. Bounded C2 is expressed
with the native norms of derivative orders zero, one and two. The real and
imaginary characteristic tests belong to this class by the explicit native
trigonometric derivative bounds. Scalar static-test AC then derives narrow
continuity on the original closed horizon, rather than assuming it. -/
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology RealInnerProductSpace BigOperators
namespace DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def SourceBoundedC2Test (φ : E→ℝ) : Prop :=
  ContDiff ℝ 2 φ ∧ ∃ C:ℝ, 0≤C ∧ ∀ n:ℕ, n≤2 → ∀ x,
    ‖iteratedFDeriv ℝ n φ x‖≤C

lemma sourceBoundedC2Test_comp_linear
    (σ : ℝ→ℝ) (hσ : ∀ n:ℕ, ContDiff ℝ n σ)
    (hσb : ∀ n:ℕ, ∀ x:ℝ, |iteratedDeriv n σ x|≤1)
    (L : E→L[ℝ] ℝ) : SourceBoundedC2Test (σ ∘ L) := by
  let C : ℝ := ∑ j ∈ Finset.range 3, ‖L‖^j
  have hC : 0≤C := Finset.sum_nonneg (fun j _ => pow_nonneg (norm_nonneg L) j)
  refine ⟨(hσ 2).comp L.contDiff, C, hC, ?_⟩
  intro n hn x
  have hbase : ‖iteratedFDeriv ℝ n σ (L x)‖≤1 := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using hσb n (L x)
  have hcomp := (iteratedFDeriv ℝ n σ (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcomp
  rw [L.iteratedFDeriv_comp_right (hσ n) x le_rfl]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n σ (L x)‖*‖L‖^n := hcomp
    _ ≤ 1*‖L‖^n := mul_le_mul_of_nonneg_right hbase (pow_nonneg (norm_nonneg L) n)
    _ = ‖L‖^n := one_mul _
    _ ≤ C := Finset.single_le_sum (fun j _ => pow_nonneg (norm_nonneg L) j)
      (Finset.mem_range.mpr (by omega))

lemma sourceBoundedC2Test_character_re (ξ : E) :
    SourceBoundedC2Test (fun x => (innerProbChar ξ x).re) := by
  have he : (fun x => (innerProbChar ξ x).re) = Real.cos ∘ (innerSL ℝ ξ) := by
    funext x
    simp only [innerProbChar_apply, Complex.exp_ofReal_mul_I_re, Function.comp_apply,
      innerSL_apply_apply, real_inner_comm]
  rw [he]
  exact sourceBoundedC2Test_comp_linear Real.cos (fun _ => Real.contDiff_cos)
    Real.abs_iteratedDeriv_cos_le_one (innerSL ℝ ξ)

lemma sourceBoundedC2Test_character_im (ξ : E) :
    SourceBoundedC2Test (fun x => (innerProbChar ξ x).im) := by
  have he : (fun x => (innerProbChar ξ x).im) = Real.sin ∘ (innerSL ℝ ξ) := by
    funext x
    simp only [innerProbChar_apply, Complex.exp_ofReal_mul_I_im, Function.comp_apply,
      innerSL_apply_apply, real_inner_comm]
  rw [he]
  exact sourceBoundedC2Test_comp_linear Real.sin (fun _ => Real.contDiff_sin)
    Real.abs_iteratedDeriv_sin_le_one (innerSL ℝ ξ)

lemma continuousOn_probability_of_ac_boundedC2_tests
    (μ : ℝ→ProbabilityMeasure E) (a b : ℝ) (hab : a≤b)
    (hAC : ∀ φ:E→ℝ, SourceBoundedC2Test φ →
      AbsolutelyContinuousOnInterval (fun r => ∫ x, φ x ∂(μ r : Measure E)) a b) :
    ContinuousOn μ (Icc a b) := by
  apply continuousOn_iff_continuous_restrict.mpr
  apply continuous_probability_of_continuous_character_tests
  · intro ξ
    have h := (hAC _ (sourceBoundedC2Test_character_re ξ)).continuousOn
    rw [uIcc_of_le hab] at h
    exact continuousOn_iff_continuous_restrict.mp h
  · intro ξ
    have h := (hAC _ (sourceBoundedC2Test_character_im ξ)).continuousOn
    rw [uIcc_of_le hab] at h
    exact continuousOn_iff_continuous_restrict.mp h

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.SourceBoundedC2Test
#print axioms DGRHS.Commutator.SourceBoundedC2Test
#check @DGRHS.Commutator.sourceBoundedC2Test_comp_linear
#print axioms DGRHS.Commutator.sourceBoundedC2Test_comp_linear
#check @DGRHS.Commutator.sourceBoundedC2Test_character_re
#print axioms DGRHS.Commutator.sourceBoundedC2Test_character_re
#check @DGRHS.Commutator.sourceBoundedC2Test_character_im
#print axioms DGRHS.Commutator.sourceBoundedC2Test_character_im
#check @DGRHS.Commutator.continuousOn_probability_of_ac_boundedC2_tests
#print axioms DGRHS.Commutator.continuousOn_probability_of_ac_boundedC2_tests
