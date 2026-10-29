import FullLabeledLSI.Paper.Sec3RecMsDiss
import FullLabeledLSI.Paper.Sec3RecLimit2

/-!
# Proposition 3.2, smooth positive case

For a family of smooth positive densities, the nonidentical products `ν_N` recover `G_θ` and `D_θ`.
-/

noncomputable section
open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem product_recovery_smooth (hyp : Hyp V W KV KW) (F : Family d)
    (hθ0 : ∀ s, 0 ≤ F.θ s) (hθ1 : ∑ s, F.θ s = 1)
    (hρ : ∀ s, IsSmoothT (F.ρ s) ∧ (∀ x, 0 < F.ρ s x) ∧ ∫ x, F.ρ s x ∂haar d = 1) :
    ∃ dens : (N : ℕ) → Fin N → Torus d → ℝ,
      (∀ N i, Measurable (dens N i) ∧ (∀ x, 0 ≤ dens N i x) ∧ ∫ x, dens N i x ∂haar d = 1) ∧
      Tendsto (fun N : ℕ => klDiv (Measure.pi fun i => densMeasure (dens N i)) (gibbs V W N) / N)
        atTop (𝓝 (msGap V W F).toENNReal) ∧
      Tendsto (fun N : ℕ =>
          fisherInfoC (Measure.pi fun i => densMeasure (dens N i)) (gibbs V W N) / N)
        atTop (𝓝 (msDiss V W F)) := by
  obtain ⟨q, θ, ρ⟩ := F
  have hne : Nonempty (Fin q) := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hθ1
  obtain ⟨s0⟩ := hne
  refine ⟨fun N i => ρ (assignOf s0 θ hθ0 hθ1 N i), fun N i => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (hρ _).1.continuous.measurable
  · exact fun x => ((hρ _).2.1 x).le
  · exact (hρ _).2.2
  · exact entropy_limit_family hyp s0 θ ρ hθ0 hθ1 hρ
  · rw [msDiss_smooth hyp θ ρ hθ0 hθ1 hρ]
    have hreal := fisher_limit_real hyp s0 θ ρ hθ0 hθ1 hρ
    refine (ENNReal.tendsto_ofReal hreal).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    obtain ⟨hne', -⟩ := fisher_counts hyp hN ρ hρ (assignOf s0 θ hθ0 hθ1 N) (groupSize s0 θ N)
      (assignOf_fiber s0 θ hθ0 hθ1 N)
    rw [ENNReal.ofReal_div_of_pos hN0, ENNReal.ofReal_toReal hne']
    simp

end SharpLSI.FL
