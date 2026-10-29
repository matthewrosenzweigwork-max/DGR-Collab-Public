import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D09_ParticleRates
import SharpSymmetricLSI.Defs.D14_Conditional
import SharpSymmetricLSI.Paper.R37Rescaling
import SharpSymmetricLSI.Paper.R37Particle

/-!
# R37: Remark 8.1 (`rem:physical-convention`), inverse-temperature rescaling

Manuscript Remark 8.1. For `β > 0` apply the theorem to `βV`, `βW`. With
`F_phys(ρ) = β^{-1}H(ρ|m) + ρ(V) + ½W(ρ,ρ)` and
`D_phys(ρ) = ∫ |β^{-1}∇log ρ + ∇(V+W*ρ)|² dρ` (written on the square-root domain as
`∫ |2β^{-1}∇√ρ + √ρ∇(V+W*ρ)|² dm`):
* `F_β = βF_phys`, `D_β = β² D_phys`;
* the infimum of `D_phys/G_phys` over the admissible densities is `2r_*/β`;
* the infimum of `β^{-1}I(ν|P_N)/H(ν|P_N)` over symmetric probabilities is `2r_N^sym/β`, and
  without symmetry `2r_N^all/β ≤ 2r_N^sym/β`.
Here `r_*`, `r_N^sym`, `r_N^all`, `P_N` are those of `βV`, `βW`. The particle infima are over
probabilities `ν ≪ P_N` with `0 < H(ν|P_N) < ⊤` (those with `H = ⊤` have `I = ⊤` at fixed `N`).
REVIEW.
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- `F_phys(ρ) = β^{-1}H(ρ|m) + ρ(V) + ½W(ρ,ρ)`. -/
noncomputable def physFreeEnergy (β : ℝ) (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ)
    (ρ : Measure (Torus d)) : EReal :=
  ((β⁻¹ : ℝ) : EReal) * ((klDiv ρ (haar d) : ENNReal) : EReal) +
    ((potE V ρ + interE W ρ ρ / 2 : ℝ) : EReal)

/-- `G_phys = F_phys - inf F_phys`. -/
noncomputable def physGap (β : ℝ) (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ)
    (ρ : Measure (Torus d)) : EReal :=
  physFreeEnergy β V W ρ - ⨅ η : ProbabilityMeasure (Torus d), physFreeEnergy β V W η

open Classical in
/-- `D_phys(ρ) = ∫ |2β^{-1}∇√ρ + √ρ ∇(V + W*ρ)|² dm` (`⊤` off `√ρ ∈ H^1(m)`). -/
noncomputable def physDiss (β : ℝ) (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ)
    (ρ : Torus d → ℝ) : ℝ≥0∞ :=
  if MemH1 (haar d) (fun x => Real.sqrt (ρ x)) ∧
      HasWeakGrad (fun x => V x + convDens W ρ x) then
    ∫⁻ x, ENNReal.ofReal (∑ k, (2 * β⁻¹ * weakGrad (fun y => Real.sqrt (ρ y)) x k +
      Real.sqrt (ρ x) * weakGrad (fun y => V y + convDens W ρ y) x k) ^ 2) ∂haar d
  else ⊤

/-- Remark 8.1. -/
theorem physical_convention {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) {β : ℝ} (hβ : 0 < β) :
    (∀ ρ : ProbabilityMeasure (Torus d),
      freeEnergy (fun x => β * V x) (fun x y => β * W x y) ρ =
        ((β : ℝ) : EReal) * physFreeEnergy β V W ρ) ∧
    (∀ ρ : Torus d → ℝ,
      dissipation (fun x => β * V x) (fun x y => β * W x y) ρ =
        ENNReal.ofReal (β ^ 2) * physDiss β V W ρ) ∧
    (⨅ ρ ∈ {ρ | Admissible (fun x => β * V x) (fun x y => β * W x y) ρ},
        physDiss β V W ρ / (physGap β V W (densMeasure ρ)).toENNReal) =
      2 * rStar (fun x => β * V x) (fun x y => β * W x y) / ENNReal.ofReal β ∧
    ∀ N : ℕ, 1 ≤ N →
      (⨅ ν ∈ {ν : Measure (Config N d) | IsProbabilityMeasure ν ∧ IsSymmetricMeasure ν ∧
          ν ≪ gibbs (fun x => β * V x) (fun x y => β * W x y) N ∧
          0 < klDiv ν (gibbs (fun x => β * V x) (fun x y => β * W x y) N) ∧
          klDiv ν (gibbs (fun x => β * V x) (fun x y => β * W x y) N) < ⊤},
        ENNReal.ofReal β⁻¹ * fisherInfoC ν (gibbs (fun x => β * V x) (fun x y => β * W x y) N) /
          klDiv ν (gibbs (fun x => β * V x) (fun x y => β * W x y) N)) =
        2 * rSym (fun x => β * V x) (fun x y => β * W x y) N / ENNReal.ofReal β ∧
      (⨅ ν ∈ {ν : Measure (Config N d) | IsProbabilityMeasure ν ∧
          ν ≪ gibbs (fun x => β * V x) (fun x y => β * W x y) N ∧
          0 < klDiv ν (gibbs (fun x => β * V x) (fun x y => β * W x y) N) ∧
          klDiv ν (gibbs (fun x => β * V x) (fun x y => β * W x y) N) < ⊤},
        ENNReal.ofReal β⁻¹ * fisherInfoC ν (gibbs (fun x => β * V x) (fun x y => β * W x y) N) /
          klDiv ν (gibbs (fun x => β * V x) (fun x y => β * W x y) N)) =
        2 * rAll (fun x => β * V x) (fun x y => β * W x y) N / ENNReal.ofReal β ∧
      2 * rAll (fun x => β * V x) (fun x y => β * W x y) N / ENNReal.ofReal β ≤
        2 * rSym (fun x => β * V x) (fun x y => β * W x y) N / ENNReal.ofReal β := by
  exact ⟨fun ρ => freeEnergy_rescale hβ V W ρ, fun ρ => dissipation_rescale hβ V W ρ,
    physical_rStar hβ V W, physical_convention_particle hyp hβ⟩

end SharpLSI
