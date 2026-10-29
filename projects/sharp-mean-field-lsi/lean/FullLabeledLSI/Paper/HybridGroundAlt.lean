import FullLabeledLSI.Paper.HybridGroundAltH
import FullLabeledLSI.Paper.Hybrid63Defs

/-!
# The hybrid inequality (7.17) (alternative route)

`hybridInequality_alt` proves lane 3's interface `HybridInequality` (`Paper/Hybrid63Defs.lean`).

Route: flat Gaussian space `μ^{⊗N} ⊗ γ_{NJ}` (`HybridGroundAltA`-`G`): the core inequality of
`hybrid_lsi_tilted_alt`, the entropy identity (GS1), the Gaussian integration by parts (GS2), and the
energy identity `∫ (Ex0 + Σ λ_k (∂_k a)²) = Σ_j (Σ_i λ_{j_i}) c_j²` for the orthonormal monomials
(torus eigen-integration by parts and Gaussian monomial orthonormality), assembled in
`HybridGroundAltH.hybrid_core` for a `C¹` representative of the eigenbasis and transferred
back to `e` almost everywhere.  `PosIPlus` is converted to `PosTm` with `min σ 1`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace SharpLSI.FL

open SharpLSI.FL.Gross

variable {d : ℕ}

/-- **The hybrid inequality (7.17)**: lane 3's interface `HybridInequality`. -/
theorem hybridInequality_alt {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (CR : ℕ → ℕ → ℕ → ℝ) (R : ℕ) :
    HybridInequality hd hyp hr μ hμ e lam he A CR R := by
  intro σ hσ hpos hC J hJ L N Bs hB c _hc
  obtain ⟨eC, a, hac, hca, hC1, hae, ha, hrla, hlam0, -, -, -, -⟩ :=
    torus_standing hd hyp hr μ hμ e lam he
  have hrl := rLS_le_lam_one hyp hμ he
  let e' : ℕ → Torus d → ℝ := fun j => if j = 0 then (fun _ => 1) else eC j
  have hC1' : ∀ j, C1T (e' j) := fun j => by
    by_cases hj : j = 0
    · simp only [e', hj, if_true]; unfold C1T; exact contDiff_const
    · simp only [e', hj, if_false]; exact hC1 j
  have hae' : ∀ j, e' j =ᵐ[(μ : Measure (Torus d))] e j := fun j => by
    by_cases hj : j = 0
    · subst hj
      simp only [e', if_true]
      rw [he.zero]
    · simp only [e', hj, if_false]; exact hae j
  have he0 : e' 0 = fun _ => 1 := by simp [e']
  exact HLA.hybrid_core A he hac hca hC1' hae' he0 hlam0 ha hrla hrl hJ
    (lt_min hσ one_pos) (HLA.posTm_of_posIPlus A hJ hσ hpos) hC Bs hB c

end SharpLSI.FL

end
