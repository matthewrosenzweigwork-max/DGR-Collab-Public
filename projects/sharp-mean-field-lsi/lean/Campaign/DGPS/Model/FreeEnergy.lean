import DGPS.Model.Data
import DGPS.Measure.EntropyChain
import DGPS.Foundations.SobolevEntropy
import SharpSymmetricLSI.Paper.KLLsc
import SharpSymmetricLSI.Paper.FreeEnergyMin

/-!
# Extended free energy and its finite minimum (DEF008)

For continuous interaction data `A = (V, W)` (DEF007) and a Borel probability `ν` on `𝕋^d`,
`freeEnergy A ν : EReal` is
`H(ν | m) + ∫ V dν + (1/2) ∬ W(x,y) dν(x) dν(y)`,
the relative entropy (DEF005, `ℝ≥0∞`, coerced to `EReal`) plus the two real potential terms. The
potential terms are real because `V` and `W` are continuous on compact spaces, so no `∞ - ∞`
occurs and `freeEnergy A ν ≠ ⊥` always.

`freeEnergyMinimum A` is the infimum over **all** Borel probabilities.

Main results:
* `DGPS.freeEnergy_minimum_exists`: the infimum is attained.
* `DGPS.freeEnergyMinimum_finite`: the infimum is a real number, and every absolute-admissible
  density has finite free energy.

Proof route: weak lower semicontinuity of relative entropy (legacy `SharpLSI.lowerSemicontinuous_klDiv`,
transported through `Analysis.relativeEntropy_eq_klDiv`), weak continuity of the bounded continuous
potential integrals (legacy `SharpLSI.continuous_interAux`), compactness of the probabilities on
the compact torus, and the Haar competitor `F(m) = ∫ V dm + (1/2) ∬ W dm² < ⊤`.
-/

open MeasureTheory InformationTheory Topology
open scoped ENNReal

namespace DGPS

variable {d : ℕ}

/-- The one-body potential energy `∫ V dν`. -/
noncomputable def potentialEnergy (A : InteractionData d) (ν : Measure (Torus d)) : ℝ :=
  ∫ x, A.V x ∂ν

/-- The two-body interaction energy `∬ W(x,y) dν(x) dν(y)`, over the product measure `ν ⊗ ν`. -/
noncomputable def interactionEnergy (A : InteractionData d) (ν : Measure (Torus d)) : ℝ :=
  ∫ p, A.W p.1 p.2 ∂(ν.prod ν)

/-- The extended free energy (DEF008)
`F(ν) = H(ν | m) + ∫ V dν + (1/2) ∬ W dν²` in `EReal`, for every Borel probability `ν`. -/
noncomputable def freeEnergy (A : InteractionData d) (ν : ProbabilityMeasure (Torus d)) : EReal :=
  ((relativeEntropy (ν : Measure (Torus d)) (haar d) : ℝ≥0∞) : EReal) +
    ((potentialEnergy A ν : ℝ) : EReal) +
    (((1 / 2 : ℝ) * interactionEnergy A ν : ℝ) : EReal)

/-- The infimum `F_*` of the free energy over all Borel probabilities. -/
noncomputable def freeEnergyMinimum (A : InteractionData d) : EReal :=
  ⨅ ν : ProbabilityMeasure (Torus d), freeEnergy A ν

/-- `ν` has finite free energy: the value of `freeEnergy A ν` is (the embedding of) a real
number, excluding both infinities. -/
def FiniteFreeEnergy (A : InteractionData d) (ν : ProbabilityMeasure (Torus d)) : Prop :=
  ∃ r : ℝ, freeEnergy A ν = (r : EReal)

/-- The real value of a finite free energy, given the finiteness receipt. -/
noncomputable def freeEnergyValue (A : InteractionData d) (ν : ProbabilityMeasure (Torus d))
    (_h : FiniteFreeEnergy A ν) : ℝ :=
  (freeEnergy A ν).toReal

theorem coe_freeEnergyValue (A : InteractionData d) (ν : ProbabilityMeasure (Torus d))
    (h : FiniteFreeEnergy A ν) : ((freeEnergyValue A ν h : ℝ) : EReal) = freeEnergy A ν := by
  obtain ⟨r, hr⟩ := h
  simp [freeEnergyValue, hr]

/-! ### The interaction energy in iterated form -/

theorem integrable_W_prod (A : InteractionData d) (ν : ProbabilityMeasure (Torus d)) :
    Integrable (fun p : Torus d × Torus d => A.W p.1 p.2)
      ((ν : Measure (Torus d)).prod ν) :=
  A.W_continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Iterated form of the interaction energy (Fubini), `∫ ∫ W(x,y) dν(x) dν(y)`. -/
theorem interactionEnergy_eq_iterated (A : InteractionData d) (ν : ProbabilityMeasure (Torus d)) :
    interactionEnergy A ν = ∫ y, ∫ x, A.W x y ∂(ν : Measure (Torus d)) ∂(ν : Measure (Torus d)) :=
  integral_prod_symm (fun p : Torus d × Torus d => A.W p.1 p.2) (integrable_W_prod A ν)

theorem continuous_potentialEnergy (A : InteractionData d) :
    Continuous fun ν : ProbabilityMeasure (Torus d) => potentialEnergy A ν :=
  ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.mkOfCompact ⟨A.V, A.V_continuous⟩)

theorem continuous_interactionEnergy (A : InteractionData d) :
    Continuous fun ν : ProbabilityMeasure (Torus d) => interactionEnergy A ν := by
  have h := SharpLSI.continuous_interAux (α := Torus d) (W := A.W) A.W_continuous
  simpa only [interactionEnergy_eq_iterated] using h

/-- The real part of the free energy: `∫ V dν + (1/2) ∬ W dν²`. -/
theorem continuous_potentialPart (A : InteractionData d) :
    Continuous fun ν : ProbabilityMeasure (Torus d) =>
      potentialEnergy A ν + (1 / 2 : ℝ) * interactionEnergy A ν :=
  (continuous_potentialEnergy A).add (continuous_const.mul (continuous_interactionEnergy A))

/-! ### Basic properties -/

theorem freeEnergy_eq_klDiv (A : InteractionData d) (ν : ProbabilityMeasure (Torus d)) :
    freeEnergy A ν = ((klDiv (ν : Measure (Torus d)) (haar d) : ℝ≥0∞) : EReal) +
      ((potentialEnergy A ν + (1 / 2 : ℝ) * interactionEnergy A ν : ℝ) : EReal) := by
  rw [freeEnergy, Analysis.relativeEntropy_eq_klDiv, add_assoc, ← EReal.coe_add]

theorem freeEnergy_ne_bot (A : InteractionData d) (ν : ProbabilityMeasure (Torus d)) :
    freeEnergy A ν ≠ ⊥ := by
  rw [freeEnergy_eq_klDiv]
  simp only [ne_eq, EReal.add_eq_bot_iff, not_or]
  exact ⟨EReal.coe_ennreal_ne_bot _, EReal.coe_ne_bot _⟩

/-- A probability has finite free energy iff its relative entropy to Haar measure is finite. -/
theorem finiteFreeEnergy_iff (A : InteractionData d) (ν : ProbabilityMeasure (Torus d)) :
    FiniteFreeEnergy A ν ↔ relativeEntropy (ν : Measure (Torus d)) (haar d) ≠ ⊤ := by
  constructor
  · rintro ⟨r, hr⟩ hH
    rw [freeEnergy_eq_klDiv, ← Analysis.relativeEntropy_eq_klDiv, hH, EReal.coe_ennreal_top,
      EReal.top_add_coe] at hr
    exact EReal.coe_ne_top r hr.symm
  · intro hH
    refine ⟨(freeEnergy A ν).toReal, ?_⟩
    refine (EReal.coe_toReal ?_ (freeEnergy_ne_bot A ν)).symm
    rw [freeEnergy_eq_klDiv, ← Analysis.relativeEntropy_eq_klDiv]
    simp only [ne_eq, EReal.add_eq_top_iff, EReal.coe_ne_top, and_false, or_false]
    exact fun h => hH (EReal.coe_ennreal_eq_top_iff.mp h.1)

/-- `ν ↦ F(ν)` is weakly lower semicontinuous on the probabilities. -/
theorem lowerSemicontinuous_freeEnergy (A : InteractionData d) :
    LowerSemicontinuous fun ν : ProbabilityMeasure (Torus d) => freeEnergy A ν := by
  simp only [freeEnergy_eq_klDiv]
  refine LowerSemicontinuous.add' (SharpLSI.lowerSemicontinuous_klDiv (haar d))
    (continuous_coe_real_ereal.comp (continuous_potentialPart A)).lowerSemicontinuous
    fun ρ => ?_
  exact EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))

/-- The Haar probability measure. -/
noncomputable def haarProbability (d : ℕ) : ProbabilityMeasure (Torus d) :=
  ⟨haar d, inferInstance⟩

/-- The Haar competitor has finite free energy. -/
theorem finiteFreeEnergy_haar (A : InteractionData d) : FiniteFreeEnergy A (haarProbability d) := by
  rw [finiteFreeEnergy_iff]
  show relativeEntropy (haar d) (haar d) ≠ ⊤
  rw [relativeEntropy_self]
  exact ENNReal.zero_ne_top

/-- Every absolute-admissible density has finite free energy. -/
theorem freeEnergy_absoluteDensity_finite (A : InteractionData d) (ρ : AbsoluteDensity d) :
    FiniteFreeEnergy A (densityMeasure ρ) := by
  rw [finiteFreeEnergy_iff]
  exact (absoluteDensity_entropy_finite ρ).2.2.1

/-! ### Existence of a minimizer and finiteness of the minimum (DEF008) -/

/-- DEF008: the free energy attains its infimum over all Borel probabilities. -/
theorem freeEnergy_minimum_exists (A : InteractionData d) :
    ∃ μ : ProbabilityMeasure (Torus d), freeEnergy A μ = freeEnergyMinimum A := by
  have hne : (Set.univ : Set (ProbabilityMeasure (Torus d))).Nonempty :=
    ⟨haarProbability d, Set.mem_univ _⟩
  obtain ⟨μ, -, hμ⟩ :=
    ((lowerSemicontinuous_freeEnergy A).lowerSemicontinuousOn Set.univ).exists_isMinOn
      hne isCompact_univ
  exact ⟨μ, le_antisymm (le_iInf fun ρ => hμ (Set.mem_univ ρ)) (iInf_le _ μ)⟩

/-- DEF008: `F_*` is a finite real number, and every absolute-admissible density has finite
free energy. -/
theorem freeEnergyMinimum_finite (A : InteractionData d) :
    (∃ r : ℝ, freeEnergyMinimum A = (r : EReal)) ∧
      ∀ ρ : AbsoluteDensity d, FiniteFreeEnergy A (densityMeasure ρ) := by
  refine ⟨?_, freeEnergy_absoluteDensity_finite A⟩
  obtain ⟨μ, hμ⟩ := freeEnergy_minimum_exists A
  obtain ⟨r, hr⟩ := finiteFreeEnergy_haar A
  have hle : freeEnergy A μ ≤ freeEnergy A (haarProbability d) := by
    rw [hμ]; exact iInf_le _ _
  have hlt : freeEnergy A μ ≠ ⊤ := ne_top_of_le_ne_top (by rw [hr]; exact EReal.coe_ne_top r) hle
  refine ⟨(freeEnergy A μ).toReal, ?_⟩
  rw [← hμ]
  exact (EReal.coe_toReal hlt (freeEnergy_ne_bot A μ)).symm

/-- The real value of the free-energy minimum `F_*` (finite by `freeEnergyMinimum_finite`). -/
noncomputable def freeEnergyMinimumReal (A : InteractionData d) : ℝ :=
  (freeEnergyMinimum A).toReal

theorem coe_freeEnergyMinimumReal (A : InteractionData d) :
    ((freeEnergyMinimumReal A : ℝ) : EReal) = freeEnergyMinimum A := by
  obtain ⟨r, hr⟩ := (freeEnergyMinimum_finite A).1
  simp [freeEnergyMinimumReal, hr]

end DGPS
