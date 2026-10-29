import DGRHS.Concentration.MasterEnvelope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DGRHS.Concentration

/-- The source negative off-diagonal energy is exactly linear in the kernel,
including the empty and one-particle cases. -/
lemma iidNegativeStatistic_mix {Ω : Type*} (n : ℕ) (h₀ h₁ : Ω × Ω → ℝ)
    (t : ℝ) (ω : Fin n → Ω) :
    iidNegativeStatistic n (fun p ↦ (1-t)*h₀ p+t*h₁ p) ω =
      (1-t)*iidNegativeStatistic n h₀ ω+t*iidNegativeStatistic n h₁ ω := by
  have hs : iidCoupledSum n (fun p ↦ (1-t)*h₀ p+t*h₁ p) ω =
      (1-t)*iidCoupledSum n h₀ ω+t*iidCoupledSum n h₁ ω := by
    unfold iidCoupledSum DGRHS.Decoupling.offDiagonalSum
    have he : ∀ i j : Fin n,
        (if i ≠ j then (1-t)*h₀ (ω i,ω j)+t*h₁ (ω i,ω j) else 0) =
        (1-t)*(if i ≠ j then h₀ (ω i,ω j) else 0)+t*(if i ≠ j then h₁ (ω i,ω j) else 0) := by
      intro i j
      by_cases hij : i ≠ j <;> simp [hij]
    simp_rw [he,Finset.sum_add_distrib,← Finset.mul_sum]
  unfold iidNegativeStatistic
  rw [hs]
  ring


/-- Convexity of the exponential gives interpolation at both endpoints, with
integrability proved by domination from the two actual endpoint integrals. -/
lemma interpolated_exp_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hXi : Integrable (fun ω ↦ Real.exp (X ω)) μ)
    (hYi : Integrable (fun ω ↦ Real.exp (Y ω)) μ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Integrable (fun ω ↦ Real.exp ((1-t)*X ω+t*Y ω)) μ ∧
      (∫ ω,Real.exp ((1-t)*X ω+t*Y ω) ∂μ) ≤
        (1-t)*(∫ ω,Real.exp (X ω) ∂μ)+t*(∫ ω,Real.exp (Y ω) ∂μ) := by
  have ha : 0 ≤ 1-t := by linarith
  have hPoint : ∀ ω, Real.exp ((1-t)*X ω+t*Y ω) ≤ (1-t)*Real.exp (X ω)+t*Real.exp (Y ω) := by
    intro ω
    simpa only [smul_eq_mul] using convexOn_exp.2 (mem_univ _) (mem_univ _) ha ht0 (by ring : (1-t)+t=1)
  have hDom := (hXi.const_mul (1-t)).add (hYi.const_mul t)
  have hBlend : AEMeasurable (fun ω ↦ (1-t)*X ω+t*Y ω) μ :=
    (aemeasurable_const.mul hX).add (aemeasurable_const.mul hY)
  have hi : Integrable (fun ω ↦ Real.exp ((1-t)*X ω+t*Y ω)) μ :=
    hDom.mono' (Real.measurable_exp.comp_aemeasurable hBlend).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Pi.add_apply] using hPoint ω)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ ω,(1-t)*Real.exp (X ω)+t*Real.exp (Y ω) ∂μ := integral_mono hi hDom hPoint
    _ = _ := by rw [integral_add (hXi.const_mul _) (hYi.const_mul _),integral_const_mul,integral_const_mul]

/-- Genuine uniform interpolated exponential partition control from the two
actual cutoff families and deterministic size envelopes. No endpoint uniform
moment or concentration estimate is supplied as a premise. -/
theorem master_interpolated_exponential_envelope {I Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : I → (n : ℕ) → (Fin n → Ω) → ℝ)
    (hX : ∀ θ n, 1 ≤ n → AEMeasurable (X θ n) (Measure.pi (fun _ : Fin n ↦ μ)))
    (hY : ∀ θ n, 1 ≤ n → AEMeasurable (Y θ n) (Measure.pi (fun _ : Fin n ↦ μ)))
    (u₀ : ℝ) (hu₀ : 1 ≤ u₀) (N₀ : ℕ)
    (dX : ∀ θ n, 1 ≤ n → MasterCutoffData μ n (X θ n) u₀)
    (dY : ∀ θ n, 1 ≤ n → MasterCutoffData μ n (Y θ n) u₀)
    (SX SY : ℕ → ℝ)
    (hSizeX : ∀ θ n (hn : 1 ≤ n), masterCutoffSize μ (dX θ n hn).kernel (dX θ n hn).cap u₀ ≤ SX n)
    (hSizeY : ∀ θ n (hn : 1 ≤ n), masterCutoffSize μ (dY θ n hn).kernel (dY θ n hn).cap u₀ ≤ SY n)
    (hGrowthX : ∀ n, 1 ≤ n → N₀ ≤ n → 2*glzUniversalTailConstant^2*SX n ≤ (n : ℝ))
    (hGrowthY : ∀ n, 1 ≤ n → N₀ ≤ n → 2*glzUniversalTailConstant^2*SY n ≤ (n : ℝ)) :
    ∀ θ n, 1 ≤ n → ∀ t ∈ Icc (0 : ℝ) 1,
      Integrable (fun ω ↦ Real.exp ((1-t)*X θ n ω+t*Y θ n ω)) (Measure.pi (fun _ : Fin n ↦ μ)) ∧
      (∫ ω,Real.exp ((1-t)*X θ n ω+t*Y θ n ω) ∂Measure.pi (fun _ : Fin n ↦ μ)) ≤
        max (masterEnvelopeConstant u₀ N₀ SX) (masterEnvelopeConstant u₀ N₀ SY) := by
  intro θ n hn t ht
  obtain ⟨hXi,hXb⟩ := master_uniform_exponential_envelope μ X hX u₀ hu₀ N₀ dX SX hSizeX hGrowthX θ n hn
  obtain ⟨hYi,hYb⟩ := master_uniform_exponential_envelope μ Y hY u₀ hu₀ N₀ dY SY hSizeY hGrowthY θ n hn
  obtain ⟨hi,hb⟩ := interpolated_exp_integral (Measure.pi (fun _ : Fin n ↦ μ)) (X θ n) (Y θ n)
    (hX θ n hn) (hY θ n hn) hXi hYi t ht.1 ht.2
  have ha : 0 ≤ 1-t := by linarith [ht.2]
  refine ⟨hi,hb.trans ?_⟩
  calc
    _ ≤ (1-t)*masterEnvelopeConstant u₀ N₀ SX+t*masterEnvelopeConstant u₀ N₀ SY :=
      add_le_add (mul_le_mul_of_nonneg_left hXb ha) (mul_le_mul_of_nonneg_left hYb ht.1)
    _ ≤ (1-t)*max (masterEnvelopeConstant u₀ N₀ SX) (masterEnvelopeConstant u₀ N₀ SY)+
        t*max (masterEnvelopeConstant u₀ N₀ SX) (masterEnvelopeConstant u₀ N₀ SY) :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha) (mul_le_mul_of_nonneg_left (le_max_right _ _) ht.1)
    _ = _ := by ring

#print axioms DGRHS.Concentration.iidNegativeStatistic_mix
#print axioms DGRHS.Concentration.interpolated_exp_integral
#print axioms DGRHS.Concentration.master_interpolated_exponential_envelope
#check @DGRHS.Concentration.master_interpolated_exponential_envelope
end DGRHS.Concentration
