import DGPS.Foundations.AbsoluteDensity
import DGPS.Foundations.SobolevCalculus
import DGPS.Foundations.SobolevEntropy
import DGPS.Model.Drift
import DGPS.Model.FreeEnergy

/-!
# Scalar gap, dissipation and rate (DEF010)

INTERFACES/definitions.md §2, common_lemmas.md DEF010.

For interaction data `A` and a weak-drift provider `b : AbsoluteDrift A`, and every
absolute-admissible `ρ = u²`:

* `scalarGap A ρ : ℝ≥0` is `G = F(ρ m) - F_*`. It is finite (the free energy of `ρ m` is finite,
  `freeEnergy_absoluteDensity_finite`) and nonnegative (`F_*` is the infimum, so
  `F_* ≤ F(ρ m)`); the minimizer lower bound is proved on the real level before the difference is
  converted to `ℝ≥0`.
* `scalarDissipation A b ρ : ℝ≥0∞` is `D = ∫⁻ |2∇u + u b_ρ|² dm`. It may be `⊤`; such `ρ`
  remain competitors.
* `scalarRate A b : ℝ≥0∞` is `r_* = inf_{G>0} D/(2G)`, an infimum over the subtype of positive-gap
  densities, with empty infimum `⊤`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace DGPS

variable {d : ℕ}

/-- The real free energy `F(ρ m)` of an absolute-admissible density. -/
noncomputable def densityFreeEnergy (A : InteractionData d) (ρ : AbsoluteDensity d) : ℝ :=
  freeEnergyValue A (densityMeasure ρ) (freeEnergy_absoluteDensity_finite A ρ)

theorem coe_densityFreeEnergy (A : InteractionData d) (ρ : AbsoluteDensity d) :
    ((densityFreeEnergy A ρ : ℝ) : EReal) = freeEnergy A (densityMeasure ρ) :=
  coe_freeEnergyValue A _ _

/-- Minimizer lower bound on the real level: `F_* ≤ F(ρ m)`. -/
theorem densityFreeEnergy_ge_min (A : InteractionData d) (ρ : AbsoluteDensity d) :
    freeEnergyMinimumReal A ≤ densityFreeEnergy A ρ := by
  have h : freeEnergyMinimum A ≤ freeEnergy A (densityMeasure ρ) :=
    iInf_le (fun ν : ProbabilityMeasure (Torus d) => freeEnergy A ν) (densityMeasure ρ)
  rw [← coe_freeEnergyMinimumReal, ← coe_densityFreeEnergy] at h
  exact EReal.coe_le_coe_iff.mp h

/-- DEF010: the gap `G_A(ρ) = F(ρ m) - F_* ∈ [0, ∞)`. -/
noncomputable def scalarGap (A : InteractionData d) (ρ : AbsoluteDensity d) : ℝ≥0 :=
  ⟨densityFreeEnergy A ρ - freeEnergyMinimumReal A,
    sub_nonneg.mpr (densityFreeEnergy_ge_min A ρ)⟩

theorem coe_scalarGap (A : InteractionData d) (ρ : AbsoluteDensity d) :
    ((scalarGap A ρ : ℝ≥0) : ℝ) = densityFreeEnergy A ρ - freeEnergyMinimumReal A := rfl

theorem scalarGap_pos_iff (A : InteractionData d) (ρ : AbsoluteDensity d) :
    0 < scalarGap A ρ ↔ freeEnergyMinimumReal A < densityFreeEnergy A ρ := by
  rw [← NNReal.coe_pos, coe_scalarGap, sub_pos]

/-- The scalar score `2∇u + u b_ρ` of `ρ = u²`. -/
noncomputable def scalarScore (A : InteractionData d) (b : AbsoluteDrift A)
    (ρ : AbsoluteDensity d) : Torus d → Tangent d :=
  fun x => (2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • b.force ρ x

/-- DEF010: the dissipation `D_{A,b}(ρ) = ∫⁻ |2∇u + u b_ρ|² dm ∈ [0, ∞]`. -/
noncomputable def scalarDissipation (A : InteractionData d) (b : AbsoluteDrift A)
    (ρ : AbsoluteDensity d) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖scalarScore A b ρ x‖ ^ 2) ∂haar d

/-- The quotient `D/(2G)` in `ℝ≥0∞`. -/
noncomputable def scalarQuotient (A : InteractionData d) (b : AbsoluteDrift A)
    (ρ : AbsoluteDensity d) : ℝ≥0∞ :=
  scalarDissipation A b ρ / (2 * (scalarGap A ρ : ℝ≥0∞))

/-- DEF010: `r_* = inf_{ρ, G(ρ) > 0} D(ρ)/(2 G(ρ))`, the infimum over the positive-gap subtype
(`⊤` if there is none). -/
noncomputable def scalarRate (A : InteractionData d) (b : AbsoluteDrift A) : ℝ≥0∞ :=
  ⨅ ρ : {ρ : AbsoluteDensity d // 0 < scalarGap A ρ}, scalarQuotient A b ρ.1

theorem scalarRate_le_quotient (A : InteractionData d) (b : AbsoluteDrift A)
    (ρ : AbsoluteDensity d) (hρ : 0 < scalarGap A ρ) :
    scalarRate A b ≤ scalarQuotient A b ρ :=
  iInf_le (fun ρ : {ρ : AbsoluteDensity d // 0 < scalarGap A ρ} => scalarQuotient A b ρ.1)
    ⟨ρ, hρ⟩

theorem scalarRate_eq_top_of_forall_gap_zero (A : InteractionData d) (b : AbsoluteDrift A)
    (h : ∀ ρ : AbsoluteDensity d, scalarGap A ρ = 0) : scalarRate A b = ⊤ := by
  unfold scalarRate
  have : IsEmpty {ρ : AbsoluteDensity d // 0 < scalarGap A ρ} :=
    ⟨fun ρ => by have := ρ.2; rw [h ρ.1] at this; exact lt_irrefl _ this⟩
  exact iInf_of_empty _

theorem scalarQuotient_lt_top_iff (A : InteractionData d) (b : AbsoluteDrift A)
    (ρ : AbsoluteDensity d) (hρ : 0 < scalarGap A ρ) :
    scalarQuotient A b ρ < ⊤ ↔ scalarDissipation A b ρ < ⊤ := by
  have h0 : (2 * (scalarGap A ρ : ℝ≥0∞)) ≠ 0 := by
    simpa using hρ.ne'
  have h1 : (2 * (scalarGap A ρ : ℝ≥0∞)) ≠ ⊤ := ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top
  unfold scalarQuotient
  constructor
  · intro h
    by_contra hD
    rw [not_lt, top_le_iff] at hD
    rw [hD, ENNReal.top_div_of_ne_top h1] at h
    exact lt_irrefl _ h
  · intro h
    exact ENNReal.div_lt_top h.ne h0

end DGPS
