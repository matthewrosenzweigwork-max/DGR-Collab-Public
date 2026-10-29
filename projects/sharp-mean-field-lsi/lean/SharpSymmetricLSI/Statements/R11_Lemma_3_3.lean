import SharpSymmetricLSI.Defs.D12_Cosine
import SharpSymmetricLSI.Paper.CircleNear

/-!
# R11: Lemma 3.3 (`lem:cosine-near-extremizers`), first Fourier mode of near-extremizers

Manuscript Lemma 3.3, (3.15) (hypothesis), (3.16) (conclusion): let `ρ_n ≠ 1` be probability densities on `𝕋` with finite
Fisher information and `I(ρ_n|m)/(2H(ρ_n|m)) → a`. Then `H(ρ_n|m) → 0`, `I(ρ_n|m) → 0`,
`ρ_n → 1` uniformly, and `Q(ρ_n)/H(ρ_n|m) → 1`.

Encodings: `ρ_n ≠ 1` as `¬ (ρ_n =ᵐ[m] 1)`; uniform convergence of a.e.-defined densities as
`‖ρ_n - 1‖_{L^∞(m)} → 0`. REVIEW.
-/

open MeasureTheory InformationTheory Filter Topology

namespace SharpLSI

/-- Lemma 3.3. -/
theorem circle_near_extremizers {ρ : ℕ → Torus 1 → ℝ} (hρ0 : ∀ n x, 0 ≤ ρ n x)
    (hρ1 : ∀ n, ∫ x, ρ n x ∂haar 1 = 1) (hne : ∀ n, ¬ (ρ n =ᵐ[haar 1] fun _ => 1))
    (hI : ∀ n, fisherInfo (densMeasure (ρ n)) (haar 1) ≠ ⊤)
    (hlim : Tendsto (fun n => (fisherInfo (densMeasure (ρ n)) (haar 1)).toReal /
        (2 * (klDiv (densMeasure (ρ n)) (haar 1)).toReal)) atTop (𝓝 aCos)) :
    Tendsto (fun n => (klDiv (densMeasure (ρ n)) (haar 1)).toReal) atTop (𝓝 0) ∧
    Tendsto (fun n => (fisherInfo (densMeasure (ρ n)) (haar 1)).toReal) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (fun x => ρ n x - 1) ⊤ (haar 1)) atTop (𝓝 0) ∧
    Tendsto (fun n => firstMode (ρ n) / (klDiv (densMeasure (ρ n)) (haar 1)).toReal) atTop
      (𝓝 1) := by
  exact circle_near_extremizers_aux hρ0 hρ1 hne hI hlim

end SharpLSI
