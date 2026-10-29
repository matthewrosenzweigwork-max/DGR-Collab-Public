import FullLabeledLSI.Defs.F01_Species
import SharpSymmetricLSI.Defs.D09_ParticleRates
import FullLabeledLSI.Paper.Cor56

/-!
# S11: Corollary 5.6 (`cor:defective-optimal`), optimal uniform defective rate

Manuscript Corollary 5.6, (5.28). Under (1.2), `r_ms` is the supremum of the `r ≥ 0` for which there
is `C_r < ∞` with `I(ν|P_N) ≥ 2r H(ν|P_N) - C_r` for every `N ≥ 1` and every `ν`, tested on
probabilities of finite relative Fisher information.

Encodings: as in S8, "`I ≥ 2rH - C`" is `2rH ≤ I + C` in `ℝ≥0∞`; the supremum is taken in `ℝ≥0∞` over
real `r ≥ 0`. `d ≥ 1` as in S1.
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- The uniform defective rates of (5.28). -/
def UniformDefectiveRate (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ ν : Measure (Config N d), IsProbabilityMeasure ν →
    fisherInfoC ν (gibbs V W N) < ⊤ →
      ENNReal.ofReal (2 * r) * klDiv ν (gibbs V W N) ≤
        fisherInfoC ν (gibbs V W N) + ENNReal.ofReal C

/-- Corollary 5.6, (5.28). -/
theorem defective_optimal {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) :
    rMs V W = ⨆ r ∈ {r : ℝ | UniformDefectiveRate V W r}, ENNReal.ofReal r := by
  exact defective_optimal_aux hd hyp

end SharpLSI.FL
