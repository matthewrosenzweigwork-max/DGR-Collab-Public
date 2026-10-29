import SharpSymmetricLSI.Defs.D12_Cosine
import SharpSymmetricLSI.Paper.CircleLSIExt

/-!
# R10: Lemma 3.2 (`lem:cosine-circle-deficit`), quantitative circle inequality

Manuscript Lemma 3.2, (3.10), (3.11): every probability density `ρ` on `𝕋` with
`√ρ ∈ H^1(m)` satisfies `H(ρ|m) ≤ 6 log(1 + I(ρ|m)/(12a))`, and in particular
`I(ρ|m) - 2a H(ρ|m) ≥ (a/6) H(ρ|m)²`. Both quantities are finite on this domain (stated).
-/

open MeasureTheory InformationTheory

namespace SharpLSI

/-- Lemma 3.2. -/
theorem circle_quantitative_lsi {ρ : Torus 1 → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar 1 = 1) (hρ : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    klDiv (densMeasure ρ) (haar 1) ≠ ⊤ ∧ fisherInfo (densMeasure ρ) (haar 1) ≠ ⊤ ∧
    (klDiv (densMeasure ρ) (haar 1)).toReal ≤
      6 * Real.log (1 + (fisherInfo (densMeasure ρ) (haar 1)).toReal / (12 * aCos)) ∧
    aCos / 6 * (klDiv (densMeasure ρ) (haar 1)).toReal ^ 2 ≤
      (fisherInfo (densMeasure ρ) (haar 1)).toReal -
        2 * aCos * (klDiv (densMeasure ρ) (haar 1)).toReal := by
  exact circle_quantitative_lsi_aux hρ0 hρ1 hρ

end SharpLSI
