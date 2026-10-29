import FullLabeledLSI.Defs.F01_Species
import SharpSymmetricLSI.Defs.D09_ParticleRates
import FullLabeledLSI.Paper.Sec3RecFinal

/-!
# S8: Proposition 3.2 (`prop:recovery`), products with nonidentical factors

Manuscript Proposition 3.2, (3.4). For each fixed admissible finite family with positive gap there
are product probabilities `ν_N` with `N⁻¹ H(ν_N|P_N) → G_θ(ρ)` and `N⁻¹ I(ν_N|P_N) → D_θ(ρ)`.
Moreover, if `I(ν|P_N) ≥ 2r H(ν|P_N) - C_r` for every `N, ν`, with `C_r` independent of `N`, then
`r ≤ r_ms`. ("Consequently (2.1) holds" is S2.)

Encodings: a product probability is `Measure.pi` of probability densities `dens N i` (the factors
need not be identical; the manuscript's factors are regularizations of the `ρₐ`). The limits are in
`ℝ≥0∞`, with `G_θ` (an `EReal`, positive here) read through `toENNReal`. In the last assertion `r`
is a real `r ≥ 0`, `N ≥ 1`, `ν` ranges over all probability measures, and "`I ≥ 2rH - C`" is
`2rH ≤ I + C` in `ℝ≥0∞`.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- Proposition 3.2, (3.4). -/
theorem product_recovery {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (F : Family d) (hF : MsAdmissible V W F) :
    ∃ dens : (N : ℕ) → Fin N → Torus d → ℝ,
      (∀ N i, Measurable (dens N i) ∧ (∀ x, 0 ≤ dens N i x) ∧ ∫ x, dens N i x ∂haar d = 1) ∧
      Tendsto (fun N : ℕ => klDiv (Measure.pi fun i => densMeasure (dens N i)) (gibbs V W N) / N)
        atTop (𝓝 (msGap V W F).toENNReal) ∧
      Tendsto (fun N : ℕ =>
          fisherInfoC (Measure.pi fun i => densMeasure (dens N i)) (gibbs V W N) / N)
        atTop (𝓝 (msDiss V W F)) :=
  product_recovery_aux hyp F hF.1

/-- Proposition 3.2, last assertion: every uniform defective rate is at most `r_ms`. -/
theorem le_rMs_of_uniform_defective {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (r : ℝ) (hr : 0 ≤ r) (C : ℝ)
    (h : ∀ N : ℕ, 1 ≤ N → ∀ ν : Measure (Config N d), IsProbabilityMeasure ν →
      ENNReal.ofReal (2 * r) * klDiv ν (gibbs V W N) ≤
        fisherInfoC ν (gibbs V W N) + ENNReal.ofReal C) :
    ENNReal.ofReal r ≤ rMs V W :=
  le_rMs_of_uniform_defective_aux hd hyp r C h

end SharpLSI.FL
