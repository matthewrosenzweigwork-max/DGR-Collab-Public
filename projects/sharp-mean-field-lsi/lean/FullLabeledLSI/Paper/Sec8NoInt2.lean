import FullLabeledLSI.Paper.Sec8NoInt1
import FullLabeledLSI.Paper.Sec3Equi
import FullLabeledLSI.Paper.Sec3DiluteD
import SharpSymmetricLSI.Paper.CosineTagged
import SharpSymmetricLSI.Paper.Centering

/-!
# Section 8.5: `r_N^all = r_LS(μ)` when `W = 0`

For `W = 0` the Gibbs law is `μ^{⊗N}`.  The lower bound is the product LSI of `Sec8NoInt1`; the
upper bound uses the tagged functions `X ↦ h(X_i)`.
-/

open MeasureTheory Filter Topology SharpLSI
open scoped ENNReal

namespace SharpLSI.FL
namespace Sec8

variable {d : ℕ} {V : Torus d → ℝ} {KV KW : ℝ}

theorem gibbs_zero_eq_pi (hyp : Hyp V (fun _ _ => 0) KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V (fun _ _ => 0) μ) (N : ℕ) :
    gibbs V (fun _ _ => 0) N = Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) := by
  rw [gibbs_eq_centered_aux hyp hμ N]
  have hU : ∀ X, Ucentered (fun _ _ => (0 : ℝ)) (μ : Measure (Torus d)) N X = 0 := fun X => by
    simp [Ucentered, centeredKernel, convMeas, interE]
  have hZ : centeredPartition (fun _ _ => (0 : ℝ)) (μ : Measure (Torus d)) N = 1 := by
    simp [centeredPartition, hU]
  simp [hU, hZ]

/-- Product LSI for `H^1`: `Ent(f²) ≤ (2/a) ℰ_N(f)`. -/
theorem pi_lsi_H1 {W : Torus d → Torus d → ℝ} (hyp : Hyp V W KV KW) {N : ℕ} {μ : Measure (Torus d)}
    [IsProbabilityMeasure μ] (hgp : gibbs V W N = Measure.pi fun _ : Fin N => μ)
    (hac : μ ≪ volume) {a : ℝ} (ha : 0 < a) (hrls : ENNReal.ofReal a ≤ rLS μ)
    {f : Config N d → ℝ} (hf : MemH1C (gibbs V W N) f) :
    ent (gibbs V W N) (fun X => f X ^ 2) ≤ ENNReal.ofReal (2 / a) * energy V W N f := by
  refine (ent_le_liminf_regF hyp hf).trans ?_
  exact liminf_le_of_frequently_le' (Eventually.of_forall fun m =>
    ent_regF_le_aux hyp hgp hac ha hrls hf m).frequently

theorem rLS_le_rAll_of_pi {W : Torus d → Torus d → ℝ} (hyp : Hyp V W KV KW) {N : ℕ}
    {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hgp : gibbs V W N = Measure.pi fun _ : Fin N => μ) (hac : μ ≪ volume) :
    rLS μ ≤ rAll V W N := by
  unfold rAll
  refine le_iInf₂ fun f hf => ?_
  obtain ⟨hfH, hent⟩ := hf
  haveI : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  haveI : IsProbabilityMeasure ((gibbs V W N).map flat) :=
    ⟨by rw [Measure.map_apply measurable_flat MeasurableSet.univ]; simp⟩
  have hEfin : energy V W N f ≠ ⊤ := by
    rw [energy_eq_dirichlet hyp hfH.1]; exact (dirichlet_lt_top_gen hfH).ne
  refine le_of_forall_lt_imp_le_of_dense fun b hb => ?_
  have hbt : b ≠ ⊤ := hb.ne_top
  by_cases hb0 : b = 0
  · rw [hb0]; exact zero_le
  have ha : 0 < b.toReal := ENNReal.toReal_pos hb0 hbt
  have hba : b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hbt).symm
  have hlsi := pi_lsi_H1 hyp hgp hac ha (by rw [← hba]; exact hb.le) hfH
  have hentne : ent (gibbs V W N) (fun X => f X ^ 2) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEfin) hlsi
  rw [ENNReal.le_div_iff_mul_le (Or.inl hent.ne') (Or.inl hentne), hba]
  calc ENNReal.ofReal b.toReal * ent (gibbs V W N) (fun X => f X ^ 2)
      ≤ ENNReal.ofReal b.toReal * (ENNReal.ofReal (2 / b.toReal) * energy V W N f) :=
        mul_le_mul' le_rfl hlsi
    _ = 2 * energy V W N f := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul ha.le, mul_div_cancel₀ _ ha.ne']
        simp

end Sec8
end SharpLSI.FL
