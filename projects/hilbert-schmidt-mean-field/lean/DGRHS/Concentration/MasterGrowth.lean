import DGRHS.Concentration.MasterInterpolation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal
namespace DGRHS.Concentration

/-- A sublinear power bound implies the actual master growth requirement;
the constants may be arbitrary finite reals. -/
lemma sublinear_power_envelope_growth (K C₀ C₁ p : ℝ) (hp : p < 1) :
    ∃ N₀ : ℕ, ∀ n : ℕ, 1 ≤ n → N₀ ≤ n →
      K*(C₀+C₁*(n : ℝ)^p) ≤ (n : ℝ) := by
  have hCast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hInv : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    hCast.inv_tendsto_atTop
  have hp' : 0 < 1-p := by linarith
  have hPow : Tendsto (fun n : ℕ ↦ (n : ℝ)^(p-1)) atTop (𝓝 0) := by
    have he : -(1-p) = p-1 := by ring
    simpa only [he,Function.comp_def] using (tendsto_rpow_neg_atTop hp').comp hCast
  have hRatio : Tendsto (fun n : ℕ ↦ K*(C₀*(n : ℝ)⁻¹+C₁*(n : ℝ)^(p-1))) atTop (𝓝 0) := by
    simpa using ((hInv.const_mul C₀).add (hPow.const_mul C₁)).const_mul K
  have hSmall : ∀ᶠ n : ℕ in atTop, K*(C₀*(n : ℝ)⁻¹+C₁*(n : ℝ)^(p-1)) < 1 :=
    hRatio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.1 hSmall
  refine ⟨N₀,?_⟩
  intro n hn hN
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hb := (hN₀ n hN).le
  rw [Real.rpow_sub_one hn'.ne' p] at hb
  have hm := mul_le_mul_of_nonneg_right hb hn'.le
  calc
    K*(C₀+C₁*(n : ℝ)^p) = K*(C₀*(n : ℝ)⁻¹+C₁*((n : ℝ)^p/(n : ℝ)))*(n : ℝ) := by
      field_simp [hn'.ne']
    _ ≤ 1*(n : ℝ) := hm
    _ = (n : ℝ) := one_mul _

/-- The actual size estimate supplies both the particle-number threshold and
one constant uniform in all auxiliary parameters. -/
theorem master_uniform_sublinear_exponential_envelope {I Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : I → (n : ℕ) → (Fin n → Ω) → ℝ)
    (hX : ∀ θ n, 1 ≤ n → AEMeasurable (X θ n) (Measure.pi (fun _ : Fin n ↦ μ)))
    (u₀ : ℝ) (hu₀ : 1 ≤ u₀)
    (d : ∀ θ n, 1 ≤ n → MasterCutoffData μ n (X θ n) u₀)
    (C₀ C₁ p : ℝ) (hp : p < 1)
    (hSize : ∀ θ n (hn : 1 ≤ n), masterCutoffSize μ (d θ n hn).kernel (d θ n hn).cap u₀ ≤
      C₀+C₁*(n : ℝ)^p) :
    ∃ M : ℝ, ∀ θ n, 1 ≤ n →
      Integrable (fun ω ↦ Real.exp (X θ n ω)) (Measure.pi (fun _ : Fin n ↦ μ)) ∧
      (∫ ω,Real.exp (X θ n ω) ∂Measure.pi (fun _ : Fin n ↦ μ)) ≤ M := by
  obtain ⟨N₀,hN₀⟩ := sublinear_power_envelope_growth (2*glzUniversalTailConstant^2) C₀ C₁ p hp
  exact ⟨masterEnvelopeConstant u₀ N₀ (fun n ↦ C₀+C₁*(n : ℝ)^p),
    master_uniform_exponential_envelope μ X hX u₀ hu₀ N₀ d (fun n ↦ C₀+C₁*(n : ℝ)^p) hSize hN₀⟩

/-- The physical Hilbert--Schmidt restriction gives the required sublinear
Riesz exponent, with positive dimension kept explicit. -/
lemma riesz_master_power_lt_one (d s : ℝ) (hd : 0 < d) (hs : s < d/2) :
    2*s/d < 1 := by
  apply (div_lt_iff₀ hd).2
  nlinarith

/-- Both endpoint families may use the same physical size envelope. The growth
threshold and the uniform interpolated expectation bound are derived here. -/
theorem master_sublinear_interpolated_exponential_envelope {I Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : I → (n : ℕ) → (Fin n → Ω) → ℝ)
    (hX : ∀ θ n, 1 ≤ n → AEMeasurable (X θ n) (Measure.pi (fun _ : Fin n ↦ μ)))
    (hY : ∀ θ n, 1 ≤ n → AEMeasurable (Y θ n) (Measure.pi (fun _ : Fin n ↦ μ)))
    (u₀ : ℝ) (hu₀ : 1 ≤ u₀)
    (dX : ∀ θ n, 1 ≤ n → MasterCutoffData μ n (X θ n) u₀)
    (dY : ∀ θ n, 1 ≤ n → MasterCutoffData μ n (Y θ n) u₀)
    (C₀ C₁ p : ℝ) (hp : p < 1)
    (hSizeX : ∀ θ n (hn : 1 ≤ n), masterCutoffSize μ (dX θ n hn).kernel (dX θ n hn).cap u₀ ≤
      C₀+C₁*(n : ℝ)^p)
    (hSizeY : ∀ θ n (hn : 1 ≤ n), masterCutoffSize μ (dY θ n hn).kernel (dY θ n hn).cap u₀ ≤
      C₀+C₁*(n : ℝ)^p) :
    ∃ M : ℝ, ∀ θ n, 1 ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Integrable (fun ω ↦ Real.exp ((1-t)*X θ n ω+t*Y θ n ω)) (Measure.pi (fun _ : Fin n ↦ μ)) ∧
      (∫ ω,Real.exp ((1-t)*X θ n ω+t*Y θ n ω) ∂Measure.pi (fun _ : Fin n ↦ μ)) ≤ M := by
  obtain ⟨N₀,hN₀⟩ := sublinear_power_envelope_growth (2*glzUniversalTailConstant^2) C₀ C₁ p hp
  refine ⟨masterEnvelopeConstant u₀ N₀ (fun n ↦ C₀+C₁*(n : ℝ)^p),?_⟩
  simpa only [max_self] using master_interpolated_exponential_envelope μ X Y hX hY u₀ hu₀ N₀ dX dY
    (fun n ↦ C₀+C₁*(n : ℝ)^p) (fun n ↦ C₀+C₁*(n : ℝ)^p) hSizeX hSizeY hN₀ hN₀

#print axioms DGRHS.Concentration.sublinear_power_envelope_growth
#print axioms DGRHS.Concentration.master_uniform_sublinear_exponential_envelope
#check @DGRHS.Concentration.master_uniform_sublinear_exponential_envelope
#print axioms DGRHS.Concentration.riesz_master_power_lt_one
#print axioms DGRHS.Concentration.master_sublinear_interpolated_exponential_envelope
#check @DGRHS.Concentration.master_sublinear_interpolated_exponential_envelope
end DGRHS.Concentration
