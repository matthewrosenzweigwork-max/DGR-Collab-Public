import SharpSymmetricLSI.Infra.Entropy
import SharpSymmetricLSI.Paper.ReferenceLSI

/-!
# R22: (5.18), the reference logarithmic Sobolev inequality

Manuscript (5.18): for any probability `μ` on `𝕋^d` with density `c₋ ≤ μ ≤ c₊`
(`0 < c₋ ≤ c₊ < ∞`), `Ent_μ(g²) ≤ (2/a_μ) ∫ |∇g|² dμ` for `g ∈ H^1(μ)`, and one may take
`a_μ = c₋/c₊` on the unit torus.
-/

open MeasureTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- (5.18) with `a_μ = c₋/c₊`. -/
theorem reference_lsi {p : Torus d → ℝ} {cm cp : ℝ} (hcm : 0 < cm)
    (hp : ∀ x, cm ≤ p x ∧ p x ≤ cp) (hp1 : ∫ x, p x ∂haar d = 1) (hpm : Measurable p)
    {g : Torus d → ℝ} (hg : MemH1 ((haar d).withDensity fun x => ENNReal.ofReal (p x)) g) :
    ent ((haar d).withDensity fun x => ENNReal.ofReal (p x)) (fun x => g x ^ 2) ≤
      ENNReal.ofReal (2 / (cm / cp)) *
        dirichlet ((haar d).withDensity fun x => ENNReal.ofReal (p x)) g := by
  exact reference_lsi_aux hcm hp hp1 hpm hg

end SharpLSI
