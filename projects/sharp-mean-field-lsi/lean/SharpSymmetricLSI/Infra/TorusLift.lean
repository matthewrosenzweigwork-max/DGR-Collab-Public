import SharpSymmetricLSI.Infra.Torus

/-!
# The periodic lift and almost-everywhere statements (Phase 1 infrastructure)

`liftT : ℝ^ι → 𝕋^ι` maps Lebesgue measure on the box `(0,1]^ι` to the Haar probability measure
of `𝕋^ι` (`measurePreserving_liftT`), and has the measurable section `secT` (coordinatewise
representatives in `(0,1]`). Consequently a property that holds Lebesgue-a.e. along the lift holds
Haar-a.e. on the torus (`ae_of_ae_liftT`), without any measurability assumption.
-/

open MeasureTheory Set

namespace SharpLSI

variable {ι : Type*}

/-- The box `(0,1]^ι`. -/
def unitBox (ι : Type*) : Set (ι → ℝ) := univ.pi fun _ => Ioc 0 1

/-- The measurable section of `liftT` with values in `(0,1]^ι`. -/
noncomputable def secT (y : UnitAddTorus ι) : ι → ℝ :=
  fun i => ((AddCircle.measurableEquivIoc 1 0) (y i) : ℝ)

theorem measurable_secT : Measurable (secT (ι := ι)) :=
  measurable_pi_iff.mpr fun i =>
    measurable_subtype_coe.comp ((AddCircle.measurableEquivIoc 1 0).measurable.comp
      (measurable_pi_apply (X := fun _ : ι => UnitAddCircle) i))

theorem liftT_secT (y : UnitAddTorus ι) : liftT (secT y) = y := by
  funext i
  exact AddCircle.coe_equivIoc

theorem secT_liftT {x : ι → ℝ} (hx : x ∈ unitBox ι) : secT (liftT x) = x := by
  funext i
  have hi : x i ∈ Ioc (0 : ℝ) (0 + 1) := by simpa using hx i (mem_univ i)
  exact AddCircle.equivIoc_coe_of_mem (p := (1 : ℝ)) (a := (0 : ℝ)) hi

theorem measurable_liftT : Measurable (liftT (ι := ι)) :=
  measurable_pi_iff.mpr fun i => AddCircle.measurable_mk'.comp (measurable_pi_apply i)

variable [Fintype ι]

/-- `liftT` maps Lebesgue measure on `(0,1]^ι` to the Haar probability measure on `𝕋^ι`. -/
theorem measurePreserving_liftT :
    MeasurePreserving (liftT (ι := ι)) ((volume : Measure (ι → ℝ)).restrict (unitBox ι))
      (volume : Measure (UnitAddTorus ι)) := by
  have h := measurePreserving_pi (fun _ : ι => (volume : Measure ℝ).restrict (Ioc 0 (0 + 1)))
    (fun _ : ι => (volume : Measure UnitAddCircle)) (fun _ => UnitAddCircle.measurePreserving_mk 0)
  rw [← Measure.restrict_pi_pi] at h
  simp only [zero_add] at h
  exact h

/-- `secT` does not charge Lebesgue-null sets. -/
theorem quasiMeasurePreserving_secT :
    Measure.QuasiMeasurePreserving (secT (ι := ι)) (volume : Measure (UnitAddTorus ι))
      (volume : Measure (ι → ℝ)) := by
  refine ⟨measurable_secT, ?_⟩
  rw [← (measurePreserving_liftT (ι := ι)).map_eq,
    Measure.map_map measurable_secT measurable_liftT]
  have : (secT ∘ liftT : (ι → ℝ) → ι → ℝ) =ᵐ[(volume : Measure (ι → ℝ)).restrict (unitBox ι)]
      id := by
    filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
      with x hx
    exact secT_liftT hx
  rw [Measure.map_congr this, Measure.map_id]
  exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self

/-- A property holding Lebesgue-a.e. along the lift holds Haar-a.e. on the torus. -/
theorem ae_of_ae_liftT {p : UnitAddTorus ι → Prop} (h : ∀ᵐ x ∂(volume : Measure (ι → ℝ)),
    p (liftT x)) : ∀ᵐ y ∂(volume : Measure (UnitAddTorus ι)), p y := by
  filter_upwards [quasiMeasurePreserving_secT.ae h] with y hy
  rwa [liftT_secT] at hy

end SharpLSI
