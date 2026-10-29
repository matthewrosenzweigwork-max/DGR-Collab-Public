import DGPS.Foundations.Entropy

/-!
# Relative entropy (DEF005)

`relativeEntropy ν P : ℝ≥0∞` is `⊤` unless `ν ≪ P`; when `ν ≪ P` it is the homogeneous entropy
(DEF004) of the Radon–Nikodym density `dν/dP` (INTERFACES/definitions.md §2). Nonnegativity
is built into the codomain. No subtraction of extended integrals occurs.

Main results:
* `DGPS.relativeEntropy_zero_iff`: for probability measures, `H(ν | P) = 0 ↔ ν = P`.
* `DGPS.relativeEntropy_withDensity`: `H(vP | P) = Ent_P(v)` for measurable `v ≥ 0` a.e.
  (with `entropy_mass_one`, this is the mass-one clause of DEF004).
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS

variable {α : Type*} [MeasurableSpace α]

open Classical in
/-- Relative entropy `H(ν | P)` (DEF005): `⊤` unless `ν ≪ P`, otherwise the homogeneous entropy
of `dν/dP`. -/
noncomputable def relativeEntropy (ν P : Measure α) : ℝ≥0∞ :=
  if ν ≪ P then homogeneousEntropy P (fun x => (ν.rnDeriv P x).toReal) else ⊤

theorem relativeEntropy_of_not_absolutelyContinuous {ν P : Measure α} (h : ¬ ν ≪ P) :
    relativeEntropy ν P = ⊤ := by
  simp [relativeEntropy, h]

theorem relativeEntropy_of_absolutelyContinuous {ν P : Measure α} (h : ν ≪ P) :
    relativeEntropy ν P = homogeneousEntropy P (fun x => (ν.rnDeriv P x).toReal) := by
  simp [relativeEntropy, h]

theorem relativeEntropy_self (P : Measure α) [IsProbabilityMeasure P] :
    relativeEntropy P P = 0 := by
  rw [relativeEntropy_of_absolutelyContinuous Measure.AbsolutelyContinuous.rfl]
  have h1 : (fun x => (P.rnDeriv P x).toReal) =ᵐ[P] fun _ => (1 : ℝ) := by
    filter_upwards [Measure.rnDeriv_self P] with x hx
    simp [hx]
  rw [homogeneousEntropy_congr_ae h1, entropy_mass_one (by simp)]
  simp

/-- DEF005: for probability measures, `H(ν | P) = 0` iff `ν = P`. -/
theorem relativeEntropy_zero_iff {ν P : Measure α} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure P] : relativeEntropy ν P = 0 ↔ ν = P := by
  constructor
  · intro h
    by_cases hac : ν ≪ P
    swap
    · simp [relativeEntropy_of_not_absolutelyContinuous hac] at h
    rw [relativeEntropy_of_absolutelyContinuous hac] at h
    have hmass : ∫ x, (ν.rnDeriv P x).toReal ∂P = 1 := by
      rw [Measure.integral_toReal_rnDeriv hac]; simp
    have hae := (homogeneousEntropy_eq_zero_iff
      (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
      (Measure.measurable_rnDeriv ν P).ennreal_toReal.aemeasurable
      (by rw [hmass]; exact one_pos)).mp h
    rw [hmass] at hae
    have h1 : ν.rnDeriv P =ᵐ[P] 1 := by
      filter_upwards [hae, Measure.rnDeriv_lt_top ν P] with x hx hlt
      rw [Pi.one_apply, ← ENNReal.ofReal_toReal hlt.ne, hx, ENNReal.ofReal_one]
    calc ν = P.withDensity (ν.rnDeriv P) := (Measure.withDensity_rnDeriv_eq ν P hac).symm
      _ = P.withDensity 1 := withDensity_congr_ae h1
      _ = P := withDensity_one
  · rintro rfl
    exact relativeEntropy_self ν

/-- `H(vP | P) = Ent_P(v)` for an a.e. nonnegative, a.e.-measurable `v`. When `∫ v dP = 1`,
`vP` is a probability and `entropy_mass_one` gives `∫ (v log v - v + 1) dP`. -/
theorem relativeEntropy_withDensity {P : Measure α} [SigmaFinite P] {v : α → ℝ}
    (hv : 0 ≤ᵐ[P] v) (hmeas : AEMeasurable v P) :
    relativeEntropy (P.withDensity fun x => ENNReal.ofReal (v x)) P = homogeneousEntropy P v := by
  rw [relativeEntropy_of_absolutelyContinuous (withDensity_absolutelyContinuous _ _)]
  apply homogeneousEntropy_congr_ae
  have hf : AEMeasurable (fun x => ENNReal.ofReal (v x)) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable hmeas
  filter_upwards [Measure.rnDeriv_withDensity₀ P hf, hv] with x hx hx0
  rw [hx, ENNReal.toReal_ofReal hx0]

end DGPS
