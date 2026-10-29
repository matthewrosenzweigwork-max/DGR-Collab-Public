import LeanResearch.PeriodicAttractiveLogGas.GreenEquation
import LeanResearch.PeriodicAttractiveLogGas.LogKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Exact volume normalization on fundamental boxes and local integrability
of lifted torus functions. The domain volume is ordinary Euclidean Lebesgue
measure; the torus measure is the specified probability Haar measure. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace PeriodicAttractiveLogGas

def euclideanFundamentalBox (a : PlanarSpace) : Set PlanarSpace :=
  WithLp.ofLp ⁻¹' Set.pi Set.univ (fun j : Fin 2 ↦ Ioc (a j) (a j + 1))

theorem unitCircle_volume_eq_haar :
    (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
  simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))

theorem measurePreserving_torusQuotient_box (a : PlanarSpace) :
    MeasurePreserving torusQuotient (volume.restrict (euclideanFundamentalBox a))
      torusMeasure := by
  have hcoord (j : Fin 2) : MeasurePreserving (fun t : ℝ ↦ (t : UnitAddCircle))
      (volume.restrict (Ioc (a j) (a j + 1))) AddCircle.haarAddCircle := by
    simpa only [unitCircle_volume_eq_haar] using (UnitAddCircle.measurePreserving_mk (a j))
  have hpi := measurePreserving_pi
    (fun j : Fin 2 ↦ volume.restrict (Ioc (a j) (a j + 1)))
    (fun _ : Fin 2 ↦ AddCircle.haarAddCircle) hcoord
  have he := (PiLp.volume_preserving_ofLp (Fin 2)).restrict_preimage
    (s := Set.pi Set.univ (fun j : Fin 2 ↦ Ioc (a j) (a j + 1)))
    (MeasurableSet.univ_pi (fun _ ↦ measurableSet_Ioc))
  rw [show (volume : Measure (Fin 2 → ℝ)) = Measure.pi (fun _ ↦ volume) from rfl,
    Measure.restrict_pi_pi] at he
  exact hpi.comp he

theorem integrable_torus_lift_on_box {f : Torus → ℝ} (hf : Integrable f torusMeasure)
    (a : PlanarSpace) : IntegrableOn (fun x ↦ f (torusQuotient x))
      (euclideanFundamentalBox a) volume :=
  (measurePreserving_torusQuotient_box a).integrable_comp_of_integrable hf

theorem integral_torus_lift_on_box {f : Torus → ℝ} (hf : Integrable f torusMeasure)
    (a : PlanarSpace) :
    ∫ x in euclideanFundamentalBox a, f (torusQuotient x) = ∫ y, f y ∂torusMeasure := by
  have hmp := measurePreserving_torusQuotient_box a
  rw [← hmp.map_eq]
  exact (integral_map hmp.aemeasurable (by simpa only [hmp.map_eq] using hf.aestronglyMeasurable)).symm

theorem euclideanFundamentalBox_mem_nhds (a x : PlanarSpace)
    (ha : ∀ j, a j < x j) (hb : ∀ j, x j < a j + 1) :
    euclideanFundamentalBox a ∈ 𝓝 x :=
  (EuclideanSpace.equiv (Fin 2) ℝ).continuous.continuousAt.preimage_mem_nhds
    (set_pi_mem_nhds Set.finite_univ (fun j _ ↦ Ioc_mem_nhds (ha j) (hb j)))

theorem locallyIntegrable_torus_lift {f : Torus → ℝ} (hf : Integrable f torusMeasure) :
    LocallyIntegrable (fun x : PlanarSpace ↦ f (torusQuotient x)) volume := by
  intro x
  let a : PlanarSpace := WithLp.toLp 2 (fun j ↦ x j - 1 / 2)
  refine ⟨euclideanFundamentalBox a, euclideanFundamentalBox_mem_nhds a x ?_ ?_,
    integrable_torus_lift_on_box hf a⟩
  · intro j
    change x j - 1 / 2 < x j
    linarith
  · intro j
    change x j < x j - 1 / 2 + 1
    linarith

theorem locallyIntegrable_greenRealRepresentative_lift :
    LocallyIntegrable (fun x : PlanarSpace ↦ greenRealRepresentative (torusQuotient x)) volume :=
  locallyIntegrable_torus_lift greenRealRepresentative_integrable

end PeriodicAttractiveLogGas
