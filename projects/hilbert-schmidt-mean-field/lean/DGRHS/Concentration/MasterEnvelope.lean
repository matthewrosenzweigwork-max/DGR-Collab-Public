import DGRHS.Concentration.MasterUniform

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Concentration

/-- A finite explicit constant from a common deterministic cutoff-size envelope. -/
def masterEnvelopeConstant (u₀ : ℝ) (N₀ : ℕ) (S : ℕ → ℝ) : ℝ :=
  max (↑(Finset.univ.sup fun i : Fin N₀ ↦ if 1 ≤ i.val then (Real.exp (u₀+S i.val)).toNNReal else 0) : ℝ)
    (Real.exp u₀+glzUniversalTailConstant)

/-- Uniformity in additional parameters follows from a common bound on the
actual cutoff-size supremum, with all cutoff and growth hypotheses retained. -/
theorem master_uniform_exponential_envelope {I Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : I → (n : ℕ) → (Fin n → Ω) → ℝ)
    (hX : ∀ θ n, 1 ≤ n → AEMeasurable (X θ n) (Measure.pi (fun _ : Fin n ↦ μ)))
    (u₀ : ℝ) (hu₀ : 1 ≤ u₀) (N₀ : ℕ)
    (d : ∀ θ n, 1 ≤ n → MasterCutoffData μ n (X θ n) u₀)
    (S : ℕ → ℝ)
    (hSize : ∀ θ n (hn : 1 ≤ n), masterCutoffSize μ (d θ n hn).kernel (d θ n hn).cap u₀ ≤ S n)
    (hGrowth : ∀ n, 1 ≤ n → N₀ ≤ n → 2*glzUniversalTailConstant^2*S n ≤ (n : ℝ)) :
    ∀ θ n, 1 ≤ n → Integrable (fun ω ↦ Real.exp (X θ n ω)) (Measure.pi (fun _ : Fin n ↦ μ)) ∧
      (∫ ω,Real.exp (X θ n ω) ∂Measure.pi (fun _ : Fin n ↦ μ)) ≤ masterEnvelopeConstant u₀ N₀ S := by
  intro θ n hn
  by_cases hg : N₀ ≤ n
  · have hActualGrowth : 2*glzUniversalTailConstant^2*masterCutoffSize μ (d θ n hn).kernel (d θ n hn).cap u₀ ≤ (n : ℝ) :=
      (mul_le_mul_of_nonneg_left (hSize θ n hn) (by positivity)).trans (hGrowth n hn hg)
    obtain ⟨hi,hb⟩ := master_exponential_moment_large μ n hn (X θ n) (hX θ n hn) u₀ hu₀ (d θ n hn) hActualGrowth
    exact ⟨hi,hb.trans (le_max_right _ _)⟩
  · obtain ⟨hi,hb⟩ := master_exponential_moment_bounded μ n (X θ n) (hX θ n hn) u₀ (by linarith) (d θ n hn)
    have hExp : Real.exp (u₀+masterCutoffSize μ (d θ n hn).kernel (d θ n hn).cap u₀) ≤ Real.exp (u₀+S n) :=
      Real.exp_le_exp.mpr (add_le_add le_rfl (hSize θ n hn))
    have hSmall : Real.exp (u₀+S n) ≤ (↑(Finset.univ.sup fun i : Fin N₀ ↦ if 1 ≤ i.val then (Real.exp (u₀+S i.val)).toNNReal else 0) : ℝ) := by
      let i : Fin N₀ := ⟨n,lt_of_not_ge hg⟩
      have hs := Finset.le_sup (f := fun j : Fin N₀ ↦ if 1 ≤ j.val then (Real.exp (u₀+S j.val)).toNNReal else 0) (Finset.mem_univ i)
      have he : (if 1 ≤ i.val then (Real.exp (u₀+S i.val)).toNNReal else 0) = (Real.exp (u₀+S n)).toNNReal := by
        dsimp [i]
        rw [ite_eq_left hn]
      rw [he] at hs
      have hr := NNReal.coe_le_coe.mpr hs
      rw [Real.coe_toNNReal _ (Real.exp_pos _).le] at hr
      exact hr
    exact ⟨hi,hb.trans (hExp.trans (hSmall.trans (le_max_left _ _)))⟩

#print axioms DGRHS.Concentration.master_uniform_exponential_envelope
#check @DGRHS.Concentration.master_uniform_exponential_envelope
end DGRHS.Concentration
