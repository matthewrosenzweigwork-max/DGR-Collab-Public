import DGPS.Frontier.LIP032.T44

/-!
# LIP032.46: Half-period translation preserves energy and reverses sign

Task id and title: LIP032.46, "Half-period translation preserves energy and reverses sign" (node
LIP032, contractibility of the minimizer set; leaf formalization on the explicit model `A_*`; no
positive-rate or flow hypothesis occurs in the statement and none is used).

## Provides
* `DGPS.Frontier.LIP032.halfPoint_LIP03246`, `halfShift_LIP03246` (definitions): the half period
  `1/2 ∈ 𝕋¹` (the lift of the constant `1/2`) and the translation `T(x) = x + 1/2`.
* `DGPS.Frontier.LIP032.lip032_46_half_period_translation_preserves_energy_reverses`: MAIN. For
  `ν ∈ S_*` (`minimizerSetStar_LIP03244`, the free-energy minimizers of `A_*`), the translated
  probability `T_#ν` (`ProbabilityMeasure.map ν T`) belongs to `S_*` and
  `M(T_#ν) = -M(ν)` for the moment `M = momentStar_LIP03241`.
* `DGPS.Frontier.LIP032.lip032_46_half_period_translation_preserves_energy_reverses_moment`: for
  every measure `μ` on `𝕋¹`, `M(T_# μ) = -M(μ)`.
* `DGPS.Frontier.LIP032.lip032_46_half_period_translation_preserves_energy_reverses_entropy`: for
  every probability `ν`, `H(T_#ν | m) = H(ν | m)`.
* `DGPS.Frontier.LIP032.lip032_46_half_period_translation_preserves_energy_reverses_energy`: for
  every probability `ν`, `F_{A_*}(T_#ν) = F_{A_*}(ν)` in `EReal`.

## R5 notes
* `T(x) = x + 1/2` is the map `x ↦ x + torusLift (fun _ => 1/2)` on `Torus 1 = Fin 1 → AddCircle 1`
  (`halfShift_LIP03246` unfolds to it by `rfl`). `T_#ν` is `ProbabilityMeasure.map ν T`, whose
  underlying measure is `Measure.map T ν` (`rfl`).
* `S_*` is the campaign set `minimizerSetStar_LIP03244` of probabilities `ν` with
  `freeEnergy A_* ν = freeEnergyMinimum A_*`, with `A_*` the explicit data
  `interactionDataStar_LIP03241`. The moment is `momentStar_LIP03241`, the integral of the cosine
  mode against the underlying measure.
* Proof route. The specification writes `ν = μ_f` with the density `f = P_a` of Task 44 and
  changes variables in the entropy integral. Here the entropy invariance is obtained for every
  probability measure at once, without densities: `T` is a Haar-preserving involution, so the data
  processing inequality `InformationTheory.klDiv_map_le` applied to `T` and again to `T = T⁻¹`
  gives `KL(T_#ν | m) = KL(ν | m)`, and the campaign relative entropy is the Kullback-Leibler
  divergence for probabilities (`Analysis.relativeEntropy_eq_klDiv`). The moment identity is the
  change of variables `∫ γ d(T_#ν) = ∫ γ ∘ T dν` together with the cosine identity `γ ∘ T = -γ`.
  The energy then follows from the Task 41 formula `F_{A_*}(ν) = H(ν | m) - 4 M(ν)²`, as in the
  specification. The densities of Tasks 18 and 44 are not used in the argument, only the
  definition of `S_*`.
* The entropy, moment and energy invariances are proved for all probability measures, a stronger
  form than the membership statement; the main declaration itself is the literal statement.
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS.Frontier.LIP032

/-- The half period `1/2` of the unit circle, as a point of `𝕋¹`. -/
noncomputable def halfPoint_LIP03246 : Torus 1 :=
  torusLift (fun _ => (1 / 2 : ℝ))

/-- The half-period translation `T(x) = x + 1/2` of `𝕋¹`. -/
noncomputable def halfShift_LIP03246 (x : Torus 1) : Torus 1 :=
  x + halfPoint_LIP03246

/-! ### The translation `T` -/

theorem halfShift_eq_LIP03246 (x : Torus 1) :
    halfShift_LIP03246 x = x + torusLift (fun _ => (1 / 2 : ℝ)) :=
  rfl

theorem halfPoint_add_self_LIP03246 : halfPoint_LIP03246 + halfPoint_LIP03246 = 0 := by
  ext i
  have h : (((1 / 2 : ℝ) : UnitAddCircle)) + ((1 / 2 : ℝ) : UnitAddCircle) = 0 := by
    rw [← AddCircle.coe_add]
    have h2 : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
    rw [h2]
    exact AddCircle.coe_period 1
  exact h

theorem halfShift_halfShift_LIP03246 (x : Torus 1) :
    halfShift_LIP03246 (halfShift_LIP03246 x) = x := by
  unfold halfShift_LIP03246
  rw [add_assoc, halfPoint_add_self_LIP03246, add_zero]

theorem halfShift_comp_LIP03246 : halfShift_LIP03246 ∘ halfShift_LIP03246 = id :=
  funext halfShift_halfShift_LIP03246

theorem continuous_halfShift_LIP03246 : Continuous halfShift_LIP03246 :=
  continuous_id.add continuous_const

theorem measurable_halfShift_LIP03246 : Measurable halfShift_LIP03246 :=
  continuous_halfShift_LIP03246.measurable

/-- Haar measure on `𝕋¹` is invariant under `T`. -/
theorem measurePreserving_halfShift_LIP03246 :
    MeasurePreserving halfShift_LIP03246 (haar 1) (haar 1) :=
  measurePreserving_add_right (haar 1) halfPoint_LIP03246

/-! ### The cosine identity `γ ∘ T = -γ` -/

theorem torusLift_add_LIP03246 (a b : Fin 1 → ℝ) :
    torusLift (a + b) = torusLift a + torusLift b := by
  ext i
  exact AddCircle.coe_add 1 (a i) (b i)

/-- The periodic cosine identity `γ(x + 1/2) = -γ(x)`. -/
theorem gammaStar_halfShift_LIP03246 (x : Torus 1) :
    gammaStar_LIP03241 (halfShift_LIP03246 x) = -gammaStar_LIP03241 x := by
  obtain ⟨a, rfl⟩ := exists_lift_LIP03241 x
  have h : halfShift_LIP03246 (torusLift a) = torusLift (a + fun _ => (1 / 2 : ℝ)) := by
    rw [torusLift_add_LIP03246]
    rfl
  have h2 : 2 * Real.pi * (a 0 + 1 / 2) = 2 * Real.pi * a 0 + Real.pi := by
    ring
  rw [h, gammaStar_lift_LIP03241, gammaStar_lift_LIP03241]
  simp only [Pi.add_apply]
  rw [h2, Real.cos_add_pi]

/-! ### Moment, entropy and energy -/

/-- The moment reverses sign: `M(T_# μ) = -M(μ)`. -/
theorem moment_map_halfShift_LIP03246 (μ : Measure (Torus 1)) :
    momentStar_LIP03241 (μ.map halfShift_LIP03246) = -momentStar_LIP03241 μ := by
  unfold momentStar_LIP03241
  rw [integral_map measurable_halfShift_LIP03246.aemeasurable
    continuous_gammaStar_LIP03241.aestronglyMeasurable]
  simp only [gammaStar_halfShift_LIP03246]
  exact integral_neg _

/-- One direction of the invariance of Kullback-Leibler divergence under `T`, from the data
processing inequality and the invariance of Haar measure. -/
theorem klDiv_map_halfShift_le_LIP03246 (μ : Measure (Torus 1)) [IsFiniteMeasure μ] :
    InformationTheory.klDiv (μ.map halfShift_LIP03246) (haar 1) ≤
      InformationTheory.klDiv μ (haar 1) := by
  have h := InformationTheory.klDiv_map_le μ (haar 1) measurable_halfShift_LIP03246
  rwa [measurePreserving_halfShift_LIP03246.map_eq] at h

/-- Kullback-Leibler divergence to Haar measure is invariant under `T`, since `T` is an involution. -/
theorem klDiv_map_halfShift_LIP03246 (μ : Measure (Torus 1)) [IsFiniteMeasure μ] :
    InformationTheory.klDiv (μ.map halfShift_LIP03246) (haar 1) =
      InformationTheory.klDiv μ (haar 1) := by
  refine le_antisymm (klDiv_map_halfShift_le_LIP03246 μ) ?_
  have h := klDiv_map_halfShift_le_LIP03246 (μ.map halfShift_LIP03246)
  rwa [Measure.map_map measurable_halfShift_LIP03246 measurable_halfShift_LIP03246,
    halfShift_comp_LIP03246, Measure.map_id] at h

theorem coe_map_halfShift_LIP03246 (ν : ProbabilityMeasure (Torus 1)) :
    ((ν.map halfShift_LIP03246 : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)) =
      (ν : Measure (Torus 1)).map halfShift_LIP03246 :=
  rfl

/-- The relative entropy to Haar measure is invariant under `T`. -/
theorem relativeEntropy_map_halfShift_LIP03246 (ν : ProbabilityMeasure (Torus 1)) :
    relativeEntropy ((ν : Measure (Torus 1)).map halfShift_LIP03246) (haar 1) =
      relativeEntropy (ν : Measure (Torus 1)) (haar 1) := by
  rw [← coe_map_halfShift_LIP03246, Analysis.relativeEntropy_eq_klDiv,
    Analysis.relativeEntropy_eq_klDiv, coe_map_halfShift_LIP03246]
  exact klDiv_map_halfShift_LIP03246 _

/-- The free energy of `A_*` is invariant under `T`. -/
theorem freeEnergy_map_halfShift_LIP03246 (ν : ProbabilityMeasure (Torus 1)) :
    freeEnergy interactionDataStar_LIP03241 (ν.map halfShift_LIP03246) =
      freeEnergy interactionDataStar_LIP03241 ν := by
  rw [energy_LIP03241, energy_LIP03241, coe_map_halfShift_LIP03246,
    relativeEntropy_map_halfShift_LIP03246, moment_map_halfShift_LIP03246, neg_sq]

/-! ### Public statements -/

/-- For every measure on `𝕋¹`, the moment of the translated measure is the negative of the
moment. -/
theorem lip032_46_half_period_translation_preserves_energy_reverses_moment
    (μ : Measure (Torus 1)) :
    momentStar_LIP03241 (μ.map halfShift_LIP03246) = -momentStar_LIP03241 μ :=
  moment_map_halfShift_LIP03246 μ

/-- For every probability on `𝕋¹`, the relative entropy to Haar measure is unchanged by `T`. -/
theorem lip032_46_half_period_translation_preserves_energy_reverses_entropy
    (ν : ProbabilityMeasure (Torus 1)) :
    relativeEntropy
        ((ν.map halfShift_LIP03246 : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)) (haar 1) =
      relativeEntropy (ν : Measure (Torus 1)) (haar 1) :=
  relativeEntropy_map_halfShift_LIP03246 ν

/-- For every probability on `𝕋¹`, the free energy of `A_*` is unchanged by `T`. -/
theorem lip032_46_half_period_translation_preserves_energy_reverses_energy
    (ν : ProbabilityMeasure (Torus 1)) :
    freeEnergy interactionDataStar_LIP03241 (ν.map halfShift_LIP03246) =
      freeEnergy interactionDataStar_LIP03241 ν :=
  freeEnergy_map_halfShift_LIP03246 ν

/-- **LIP032.46.** Let `T(x) = x + 1/2` on the unit circle. If `ν ∈ S_*`, then the translated
probability `T_#ν` also belongs to `S_*` and `M(T_#ν) = -M(ν)`. -/
theorem lip032_46_half_period_translation_preserves_energy_reverses
    (ν : ProbabilityMeasure (Torus 1)) (hν : ν ∈ minimizerSetStar_LIP03244) :
    ν.map halfShift_LIP03246 ∈ minimizerSetStar_LIP03244 ∧
      momentStar_LIP03241
          ((ν.map halfShift_LIP03246 : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)) =
        -momentStar_LIP03241 (ν : Measure (Torus 1)) := by
  refine ⟨?_, moment_map_halfShift_LIP03246 (ν : Measure (Torus 1))⟩
  have hν' : freeEnergy interactionDataStar_LIP03241 ν =
      freeEnergyMinimum interactionDataStar_LIP03241 := hν
  show freeEnergy interactionDataStar_LIP03241 (ν.map halfShift_LIP03246) =
    freeEnergyMinimum interactionDataStar_LIP03241
  exact (freeEnergy_map_halfShift_LIP03246 ν).trans hν'

end DGPS.Frontier.LIP032
