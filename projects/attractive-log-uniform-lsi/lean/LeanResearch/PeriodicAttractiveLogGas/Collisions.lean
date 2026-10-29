import LeanResearch.PeriodicAttractiveLogGas.Ensemble
import Mathlib.Probability.Independence.Basic

/-! Pair diagonals and the collision set are null for the reference product
measure and every absolutely continuous Gibbs construction. Source: lines
258–262. This is nullity, not a claim that the collision set has zero capacity. -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace PeriodicAttractiveLogGas

instance unitCircleHaarNullSingleton : NullSingletonClass (@AddCircle.haarAddCircle (1 : ℝ) _) := by
  refine ⟨fun x ↦ ?_⟩
  have hv : (volume : Measure UnitAddCircle) {x} = 0 := by
    let e := AddCircle.measurableEquivIoc (1 : ℝ) 0
    have hmap := (AddCircle.measurePreserving_equivIoc (1 : ℝ) (a := 0)).map_eq
    have heq := congrArg (fun ν : Measure (Set.Ioc (0 : ℝ) (0 + 1)) ↦ ν {e x}) hmap
    change (Measure.map e (volume : Measure UnitAddCircle)) {e x} = _ at heq
    rw [Measure.map_apply e.measurable (measurableSet_singleton _)] at heq
    have hpre : e ⁻¹' {e x} = {x} := by ext y; simp
    change (volume : Measure UnitAddCircle) (e ⁻¹' {e x}) = _ at heq
    rw [hpre] at heq
    rw [heq, Measure.comap_apply _ Subtype.val_injective
      (fun _ ↦ measurableSet_Ioc.subtype_image) _ (measurableSet_singleton _)]
    simp
  simpa only [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul] using hv

instance : NullSingletonClass torusMeasure := by
  unfold torusMeasure
  infer_instance

theorem torus_diagonal_null :
    (torusMeasure.prod torusMeasure) {p : Torus × Torus | p.1 = p.2} = 0 := by
  rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
  have heq (x : Torus) : Prod.mk x ⁻¹' {p : Torus × Torus | p.1 = p.2} = {x} := by
    ext y
    simp [eq_comm]
  simp only [heq, measure_singleton, lintegral_zero]

theorem pair_diagonal_null (N : ℕ) {i j : Fin N} (hij : i ≠ j) :
    referenceMeasure N {x | x i = x j} = 0 := by
  have hind := (iIndepFun_pi (μ := fun _ : Fin N ↦ torusMeasure)
    (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)).indepFun hij
  have hmap := hind.map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  rw [(measurePreserving_eval (fun _ : Fin N ↦ torusMeasure) i).map_eq,
    (measurePreserving_eval (fun _ : Fin N ↦ torusMeasure) j).map_eq] at hmap
  have heq := congrArg (fun ν : Measure (Torus × Torus) ↦ ν {p | p.1 = p.2}) hmap
  rw [Measure.map_apply ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
    (measurableSet_eq_fun measurable_fst measurable_snd)] at heq
  exact heq.trans torus_diagonal_null

def collisionSet (N : ℕ) : Set (Configuration N) := {x | ∃ i j, i ≠ j ∧ x i = x j}

theorem collisionSet_null (N : ℕ) : referenceMeasure N (collisionSet N) = 0 := by
  have heq : collisionSet N = ⋃ i : Fin N, ⋃ j : Fin N, ⋃ (_ : i ≠ j), {x | x i = x j} := by
    ext x
    simp [collisionSet]
  rw [heq]
  exact measure_iUnion_null fun i ↦ measure_iUnion_null fun j ↦
    measure_iUnion_null fun h ↦ pair_diagonal_null N h

theorem gibbs_collisionSet_null (g : Torus → ℝ) (N : ℕ) (β : ℝ) :
    gibbsMeasure g N β (collisionSet N) = 0 :=
  gibbsMeasure_absolutelyContinuous g N β (collisionSet_null N)

theorem gibbsWeight_congr_off_origin {g h : Torus → ℝ}
    (hgh : ∀ x ≠ 0, g x = h x) (N : ℕ) (β : ℝ) :
    gibbsWeight g N β =ᵐ[referenceMeasure N] gibbsWeight h N β := by
  have hae : ∀ᵐ x ∂referenceMeasure N, x ∉ collisionSet N := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using collisionSet_null N
  apply hae.mono
  intro x hx
  have hp : pairEnergy g N x = pairEnergy h N x := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j hj
    apply hgh
    rw [sub_ne_zero]
    intro heq
    exact hx ⟨i, j, (Finset.mem_Ioi.mp hj).ne, heq⟩
  simp only [gibbsWeight, hp]

theorem partitionFunction_congr_off_origin {g h : Torus → ℝ}
    (hgh : ∀ x ≠ 0, g x = h x) (N : ℕ) (β : ℝ) :
    partitionFunction g N β = partitionFunction h N β :=
  lintegral_congr_ae ((gibbsWeight_congr_off_origin hgh N β).mono fun _ hx ↦ congrArg _ hx)

theorem gibbsMeasure_congr_off_origin {g h : Torus → ℝ}
    (hgh : ∀ x ≠ 0, g x = h x) (N : ℕ) (β : ℝ) :
    gibbsMeasure g N β = gibbsMeasure h N β := by
  unfold gibbsMeasure
  rw [partitionFunction_congr_off_origin hgh N β]
  congr 1
  exact withDensity_congr_ae
    ((gibbsWeight_congr_off_origin hgh N β).mono fun _ hx ↦ congrArg _ hx)

end PeriodicAttractiveLogGas
