import SharpSymmetricLSI.Paper.GroundT5

/-!
# R30: (7.6)–(7.7), the ground-state transformation, conditional on (5.14) and Prop. 2.2

`ground_state_transform_of`: from the force bound of Lemma 5.3 ((5.14)) and the defective
inequality (Proposition 2.2) at one rate `r > 0`, `Ψ_N = f √p_N ∈ H¹(μ^{⊗N})`,
`‖Ψ_N‖_{L²(μ^{⊗N})} = ‖f‖_{L²(P_N)}` and `∫|∇Ψ_N|² ≤ C(ℰ_N(f) + ‖f‖²)`.
-/

open MeasureTheory InformationTheory Set Filter Topology Real
open scoped ENNReal NNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem gradSqC_eq_sqNorm {N : ℕ} (u : Config N d → ℝ) (X : Config N d) :
    gradSqC u X = sqNorm (weakGrad (u ∘ unflat) (flat X)) := by
  unfold gradSqC sqNorm weakGradC
  rw [Fintype.sum_prod_type]

section
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {N : ℕ} (hN : 1 ≤ N)
include hyp hμ hN

/-- The a.e. pointwise energy bound for `Ψ`. -/
theorem gradSqC_psi_le {f : Config N d → ℝ} (hf : MemH1C (gibbs V W N) f) :
    ∀ᵐ X ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))),
      gradSqC (fun X => f X * Real.sqrt (rexp (-Ucentered W μ N X) / centeredPartition W μ N)) X ≤
        2 * (rexp (-Ucentered W μ N X) / centeredPartition W μ N) * gradSqC f X +
          1 / 2 * (rexp (-Ucentered W μ N X) / centeredPartition W μ N) * f X ^ 2 *
            gradSqC (Ucentered W μ N) X := by
  set μm := (μ : Measure (Torus d))
  have hac := minimizer_ac hyp hμ
  have hpair := isWeakGrad_psi hyp hμ hN hf
  have h1 := weakGrad_ae_unique (isWeakGrad_weakGrad ⟨_, hpair⟩) hpair
  have hU := isWeakGrad_gsU hyp hac hN (μ := μm)
  have h2 := weakGrad_ae_unique (isWeakGrad_weakGrad ⟨_, hU⟩) hU
  filter_upwards [ae_pi_of_ae_volume hyp hμ (h1.and h2)] with X hX
  rw [gradSqC_eq_sqNorm, gradSqC_eq_sqNorm f, gradSqC_eq_sqNorm (Ucentered W μ N), hX.1, hX.2]
  exact sqNorm_gsPsiG_le f μm (centeredPartition_pos hyp μm N) (flat X)

omit hN in
theorem aestronglyMeasurable_comp_flat {G : UnitAddTorus (Fin N × Fin d) → ℝ}
    (hG : AEStronglyMeasurable G volume) :
    AEStronglyMeasurable (fun X => G (flat X)) (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) := by
  have hmp : MeasurePreserving (flat : Config N d → UnitAddTorus (Fin N × Fin d)) volume volume :=
    ⟨measurable_flat, map_flat_volume N⟩
  exact (hG.comp_measurePreserving hmp).mono_ac (pi_ac_volume (minimizer_ac hyp hμ) N)

omit hN in
theorem aemeasurable_gradSqC_pi {u : Config N d → ℝ} (hu : HasWeakGrad (u ∘ unflat)) :
    AEMeasurable (fun X => gradSqC u X) (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) := by
  have hw := isWeakGrad_weakGrad hu
  simp_rw [gradSqC_eq_sqNorm]
  unfold sqNorm
  refine (Finset.aestronglyMeasurable_fun_sum _ fun p _ => ?_).aemeasurable
  exact ((aestronglyMeasurable_comp_flat hyp hμ (hw.aestronglyMeasurable_grad p)).pow 2)

end

end SharpLSI
