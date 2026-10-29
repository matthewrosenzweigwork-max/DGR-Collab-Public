import FullLabeledLSI.Defs.F01_Species
import SharpSymmetricLSI.Defs.D09_ParticleRates
import SharpSymmetricLSI.Defs.D12_Cosine
import SharpSymmetricLSI.Infra.Classical
import FullLabeledLSI.Statements.S01_Theorem_1_1
import FullLabeledLSI.Paper.Sec8Fourier11

/-!
# S16: Corollary 8.4 (`cor:Fourier`), smooth homogeneous interactions of positive type

Manuscript Corollary 8.4, (8.17). On the unit `𝕋^d`, `V = 0`, `W(x,y) = G(x-y) - G(0)` with `G`
smooth, real and even, and `Ĝ(k) ≥ 0` for every `k ∈ ℤ^d \ {0}`. Then `r_ms = 4π²` and
`r_N^all → 4π²`.

Encodings: `Ĝ(k)` is `fourierCoeffT G k` (Infra/Classical); for real even `G` it is real, and
`Ĝ(k) ≥ 0` is written `0 ≤ (Ĝ k).re`. `d ≥ 1` (for `d = 0` there are no nonzero frequencies and the
torus is a point). The hypotheses (1.2) for this `W` are part of what the proof establishes.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- Corollary 8.4, (8.17). -/
theorem fourier_positive_type_limit (hd : 1 ≤ d) (G : Torus d → ℝ) (hGs : IsSmoothT G)
    (hGe : ∀ x, G (-x) = G x) (hGk : ∀ k : Fin d → ℤ, k ≠ 0 → 0 ≤ (fourierCoeffT G k).re) :
    rMs (fun _ => 0) (fun x y => G (x - y) - G 0) = ENNReal.ofReal aCos ∧
      Tendsto (fun N => rAll (fun _ => 0) (fun x y => G (x - y) - G 0) N) atTop
        (𝓝 (ENNReal.ofReal aCos)) := by
  exact Sec8.fourier_core hd G hGs hGe hGk (fun _ hyp => full_labeled_lsi_limit hd hyp)

end SharpLSI.FL
