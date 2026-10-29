import SharpSymmetricLSI.Statements.R01_Theorem_1_1
import SharpSymmetricLSI.Statements.R03_Prop_2_2
import SharpSymmetricLSI.Statements.R04_Prop_2_3
import SharpSymmetricLSI.Statements.R34_Lemma_B_1
import SharpSymmetricLSI.Paper.R7Main

/-!
# R7: Section 2.3 (`sec:tightening`), the sharp lower bound from the three inputs

Manuscript Section 2.3, (2.13)–(2.26): assuming `r_* > 0`, Propositions 2.1–2.3 and Lemma B.1
imply (1.10) for every `0 < r < r_*` (both the positive-entropy and the vanishing-entropy
cases). The inputs enter as hypotheses (`lower_bound_of_inputs` with the concrete Proposition 2.3,
`lower_bound_of_inputs'` with its existential wording) (never as axioms); they are discharged by R2, R3, R4,
R34 in `lower_bound`.
-/

namespace SharpLSI

variable {d : ℕ}

/-- Section 2.3: the inputs imply (1.10). -/
theorem lower_bound_of_inputs {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (h21 : EquilibriumConclusion V W) (h22 : DefectiveConclusion V W)
    (h23 : CompactnessConclusion V W) (hB1 : TruncationConclusion) :
    FiniteNConclusion V W := by
  obtain ⟨μ, hμ⟩ := h21.1.exists
  obtain ⟨⟨e, lam, he⟩, h2⟩ := h23 μ hμ
  obtain ⟨⟨C, hC⟩, h3⟩ := h2 e lam he
  obtain ⟨⟨γ, hγ⟩, h4⟩ := h3 C hC
  haveI := hγ.1
  exact lower_bound_core hyp hr h22 hB1 (h4 γ hγ)

/-- Section 2.3 from the manuscript's existential Proposition 2.3 (the form actually used in
Section 2.3), instead of the concrete `CompactnessConclusion`. -/
theorem lower_bound_of_inputs' {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (h21 : EquilibriumConclusion V W) (h22 : DefectiveConclusion V W)
    (h23 : CompactnessExistsConclusion V W) (hB1 : TruncationConclusion) :
    FiniteNConclusion V W := by
  obtain ⟨C, γ, lam', hγ, -, hGI⟩ := h23
  haveI := hγ.1
  exact lower_bound_core hyp hr h22 hB1 hGI

/-- Section 2.3 with the inputs discharged. -/
theorem lower_bound {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W) : FiniteNConclusion V W :=
  lower_bound_of_inputs hd hyp hr (prop_equilibrium hd hyp hr) (prop_defective hd hyp hr)
    (prop_compactness hd hyp hr) lemma_B1

end SharpLSI
