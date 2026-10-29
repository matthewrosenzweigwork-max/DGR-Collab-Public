import FullLabeledLSI.Paper.Sec5LNH
import FullLabeledLSI.Paper.Sec5LNI

/-!
# Large-N assembly J: Proposition 2.2
-/

open MeasureTheory Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **Proposition 2.2 without symmetry**, in the unfolded form of `DefectiveConclusionAll V W` (S03
cannot be imported here; the S03 proof is `exact prop_defective_all_aux hd hyp hr`).
Proof: `(exists_minimizer hyp).1` gives `μ`; `large_N_reg_all hd hyp hr hμ hr0 hrr` gives `N₀, K`;
`prop_defective_all_of hyp hr0 hK`.  ~10 lines. -/
theorem prop_defective_all_aux (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W) :
    ∀ r : ℝ, 0 < r → ENNReal.ofReal r < rMs V W →
      ∃ B : NNReal, ∀ N : ℕ, 1 ≤ N → ∀ f : Config N d → ℝ,
        MemH1C (gibbs V W N) f →
          ent (gibbs V W N) (fun X => f X ^ 2) ≤
            ENNReal.ofReal (2 / r) * energy V W N f +
              (B : ℝ≥0∞) * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N := by
  intro r hr0 hrr
  obtain ⟨μ, hμ⟩ := (exists_minimizer hyp).1
  obtain ⟨N₀, K, hK⟩ := large_N_reg_all hd hyp hr hμ hr0 hrr
  exact prop_defective_all_of hyp hr0 hK


end SharpLSI.FL
