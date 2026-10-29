import DGRHS.Concentration.MasterExponential

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Concentration

lemma glzUniversalTailConstant_one_le : 1 ≤ glzUniversalTailConstant := by
  have he := Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 by norm_num)
  simp only [Real.exp_zero] at he
  have hb : 1 ≤ (221184*Real.exp 1)^2 := by nlinarith
  have hm : Real.exp 1 ≤ glzUniversalTailConstant := by
    unfold glzUniversalTailConstant
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (Real.exp_pos 1).le
  exact he.trans hm

/-- The actual finite maximum over positive particle numbers below N₀;
an empty finite range has value zero. -/
def masterUniformSmallBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : (n : ℕ) → (Fin n → Ω) → ℝ)
    (u₀ : ℝ) (N₀ : ℕ) (d : ∀ n, 1 ≤ n → MasterCutoffData μ n (X n) u₀) : ℝ :=
  ↑(Finset.univ.sup fun i : Fin N₀ ↦ if hi : 1 ≤ i.val then
    (Real.exp (u₀+masterCutoffSize μ (d i.val hi).kernel (d i.val hi).cap u₀)).toNNReal else 0)

def masterUniformConstant {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : (n : ℕ) → (Fin n → Ω) → ℝ)
    (u₀ : ℝ) (N₀ : ℕ) (d : ∀ n, 1 ≤ n → MasterCutoffData μ n (X n) u₀) : ℝ :=
  max (masterUniformSmallBound μ X u₀ N₀ d) (Real.exp u₀+glzUniversalTailConstant)

/-- Actual uniform partition-function master bound from all M1/M2/M3 cutoff
hypotheses and eventual size growth; neither tails nor moments are premises. -/
theorem master_uniform_exponential_moment {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : (n : ℕ) → (Fin n → Ω) → ℝ)
    (hX : ∀ n, 1 ≤ n → AEMeasurable (X n) (Measure.pi (fun _ : Fin n ↦ μ)))
    (u₀ : ℝ) (hu₀ : 1 ≤ u₀) (N₀ : ℕ)
    (d : ∀ n, 1 ≤ n → MasterCutoffData μ n (X n) u₀)
    (hGrowth : ∀ n (hn : 1 ≤ n), N₀ ≤ n →
      2*glzUniversalTailConstant^2*masterCutoffSize μ (d n hn).kernel (d n hn).cap u₀ ≤ (n : ℝ)) :
    ∀ n, 1 ≤ n → Integrable (fun ω ↦ Real.exp (X n ω)) (Measure.pi (fun _ : Fin n ↦ μ)) ∧
      (∫ ω,Real.exp (X n ω) ∂Measure.pi (fun _ : Fin n ↦ μ)) ≤ masterUniformConstant μ X u₀ N₀ d := by
  intro n hn
  by_cases hg : N₀ ≤ n
  · obtain ⟨hi,hb⟩ := master_exponential_moment_large μ n hn (X n) (hX n hn) u₀ hu₀ (d n hn) (hGrowth n hn hg)
    exact ⟨hi,hb.trans (le_max_right _ _)⟩
  · obtain ⟨hi,hb⟩ := master_exponential_moment_bounded μ n (X n) (hX n hn) u₀ (by linarith) (d n hn)
    have hSmall : Real.exp (u₀+masterCutoffSize μ (d n hn).kernel (d n hn).cap u₀) ≤ masterUniformSmallBound μ X u₀ N₀ d := by
      let i : Fin N₀ := ⟨n,lt_of_not_ge hg⟩
      have hs := Finset.le_sup (f := fun j : Fin N₀ ↦ if hj : 1 ≤ j.val then
        (Real.exp (u₀+masterCutoffSize μ (d j.val hj).kernel (d j.val hj).cap u₀)).toNNReal else 0) (Finset.mem_univ i)
      have he : (if hj : 1 ≤ i.val then
          (Real.exp (u₀+masterCutoffSize μ (d i.val hj).kernel (d i.val hj).cap u₀)).toNNReal else 0) =
          (Real.exp (u₀+masterCutoffSize μ (d n hn).kernel (d n hn).cap u₀)).toNNReal := by
        dsimp [i]
        rw [dite_eq_left hn]
      rw [he] at hs
      have hr := NNReal.coe_le_coe.mpr hs
      change (↑(Real.exp (u₀+masterCutoffSize μ (d n hn).kernel (d n hn).cap u₀)).toNNReal : ℝ) ≤ masterUniformSmallBound μ X u₀ N₀ d at hr
      rw [Real.coe_toNNReal _ (Real.exp_pos _).le] at hr
      exact hr
    exact ⟨hi,hb.trans (hSmall.trans (le_max_left _ _))⟩

#print axioms DGRHS.Concentration.glzUniversalTailConstant_one_le
#print axioms DGRHS.Concentration.master_uniform_exponential_moment
#check @DGRHS.Concentration.master_uniform_exponential_moment
end DGRHS.Concentration
