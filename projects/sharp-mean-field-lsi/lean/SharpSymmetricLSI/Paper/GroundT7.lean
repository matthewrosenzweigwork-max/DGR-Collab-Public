import SharpSymmetricLSI.Paper.GroundT6

/-!
# R30: (7.6)–(7.7) assembly, conditional on (5.14) and Proposition 2.2
-/

open MeasureTheory InformationTheory Set Filter Topology Real
open scoped ENNReal NNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {N : ℕ} (hN : 1 ≤ N)
include hyp hμ hN

omit hN in
/-- The isometry `‖Ψ‖_{L²(μ^{⊗N})} = ‖f‖_{L²(P_N)}`. -/
theorem lintegral_psi_sq (f : Config N d → ℝ) :
    ∫⁻ X, ENNReal.ofReal ((f X * Real.sqrt (rexp (-Ucentered W μ N X) / centeredPartition W μ N)) ^ 2)
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) =
      ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N := by
  rw [lintegral_gibbs_eq hyp hμ]
  refine lintegral_congr fun X => ?_
  have hp : 0 ≤ rexp (-Ucentered W μ N X) / centeredPartition W μ N :=
    div_nonneg (Real.exp_pos _).le (centeredPartition_pos hyp _ N).le
  rw [mul_pow, Real.sq_sqrt hp, ← ENNReal.ofReal_mul hp, mul_comm]

/-- The energy bound before the force estimate. -/
theorem lintegral_gradSqC_psi_le {f : Config N d → ℝ} (hf : MemH1C (gibbs V W N) f) :
    ∫⁻ X, ENNReal.ofReal (gradSqC (fun X => f X *
        Real.sqrt (rexp (-Ucentered W μ N X) / centeredPartition W μ N)) X)
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤
      ENNReal.ofReal 2 * energy V W N f + ENNReal.ofReal (1 / 2) *
        ∫⁻ X, ENNReal.ofReal (f X ^ 2 * gradSqC (Ucentered W μ N) X) ∂gibbs V W N := by
  set Q := Measure.pi (fun _ : Fin N => (μ : Measure (Torus d)))
  set p : Config N d → ℝ := fun X => rexp (-Ucentered W μ N X) / centeredPartition W μ N
  have hp : ∀ X, 0 ≤ p X := fun X =>
    div_nonneg (Real.exp_pos _).le (centeredPartition_pos hyp _ N).le
  have hpm : Measurable fun X => ENNReal.ofReal (p X) :=
    ENNReal.measurable_ofReal.comp (((measurable_Ucentered hyp _ N).neg.exp).div_const _)
  have h1 : ∫⁻ X, ENNReal.ofReal (gradSqC (fun X => f X * Real.sqrt (p X)) X) ∂Q ≤
      ∫⁻ X, (ENNReal.ofReal (p X) * ENNReal.ofReal (2 * gradSqC f X) +
        ENNReal.ofReal (p X) * ENNReal.ofReal (1 / 2 * (f X ^ 2 * gradSqC (Ucentered W μ N) X))) ∂Q := by
    refine lintegral_mono_ae ?_
    filter_upwards [gradSqC_psi_le hyp hμ hN hf] with X hX
    rw [← ENNReal.ofReal_mul (hp X), ← ENNReal.ofReal_mul (hp X), ← ENNReal.ofReal_add
      (mul_nonneg (hp X) (mul_nonneg zero_le_two (gradSqC_nonneg _ _)))
      (mul_nonneg (hp X) (mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _)
        (gradSqC_nonneg _ _))))]
    refine ENNReal.ofReal_le_ofReal (hX.trans (le_of_eq ?_))
    simp only [p]; ring
  refine h1.trans (le_of_eq ?_)
  rw [lintegral_add_left' (f := fun X => ENNReal.ofReal (p X) * ENNReal.ofReal (2 * gradSqC f X))
    (hpm.aemeasurable.mul ((aemeasurable_gradSqC_pi hyp hμ hf.1).const_mul 2).ennreal_ofReal)]
  rw [energy, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_gibbs_eq hyp hμ (fun X => ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (gradSqC f X)),
    lintegral_gibbs_eq hyp hμ (fun X => ENNReal.ofReal (1 / 2 : ℝ) *
      ENNReal.ofReal (f X ^ 2 * gradSqC (Ucentered W μ N) X))]
  congr 1
  · refine lintegral_congr fun X => ?_
    rw [ENNReal.ofReal_mul zero_le_two]
  · refine lintegral_congr fun X => ?_
    rw [ENNReal.ofReal_mul (by norm_num)]

end

end SharpLSI
