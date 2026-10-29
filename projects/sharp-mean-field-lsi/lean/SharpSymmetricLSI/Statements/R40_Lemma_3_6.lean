import SharpSymmetricLSI.Defs.D12_Cosine
import SharpSymmetricLSI.Paper.CosineCalculus
import SharpSymmetricLSI.Paper.GroundState

/-!
# R40: Lemma 3.6 (`lem:cosine-defective`), defective inequality for the cosine model

Manuscript Lemma 3.6, (3.29), (3.30):
* (3.30) `ΔU_N = aκ - 2aU_N` (classical Laplacian of the smooth function `U_N` on `𝕋^N`).
* (3.29) for every `N ≥ 1` and real `f ∈ H^1(P_{N,κ})`:
  `Ent_{P_{N,κ}}(f²) ≤ (2/a) ℰ_{N,κ}(f) + κ ∫ f² dP_{N,κ}`.
-/

open MeasureTheory
open scoped ENNReal

namespace SharpLSI

/-- (3.30). -/
theorem cosine_U_laplacian (κ : ℝ) {N : ℕ} (hN : 1 ≤ N) (X : Config N 1) :
    laplacianC (cosU κ N) X = aCos * κ - 2 * aCos * cosU κ N X := by
  exact cosine_U_laplacian_aux κ hN X

/-- Lemma 3.6, (3.29). -/
theorem cosine_defective {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N) {f : Config N 1 → ℝ}
    (hf : MemH1C (gibbs cosV (cosW κ) N) f) :
    ent (gibbs cosV (cosW κ) N) (fun X => f X ^ 2) ≤
      ENNReal.ofReal (2 / aCos) * energy cosV (cosW κ) N f +
        ENNReal.ofReal κ * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs cosV (cosW κ) N := by
  exact cosine_defective_aux hκ hN hf

end SharpLSI
