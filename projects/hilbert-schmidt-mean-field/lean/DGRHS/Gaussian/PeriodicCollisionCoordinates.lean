import DGRHS.Gaussian.PeriodicCollisionAnchoring
import DGRHS.Gaussian.PeriodicGreenExponentialIntegrability

/-! The actual real fundamental-cube law and its finite product. Collisions,
including collisions with the distinguished origin, are explicitly null. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Classical BigOperators ENNReal
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local instance periodicCollisionCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def periodicCubeMeasure (ι : Type u) [Fintype ι] : Measure (ι → ℝ) :=
  volume.restrict (periodicFundamentalCube ι)

lemma periodicCubeMeasure_pi : periodicCubeMeasure ι=
    Measure.pi (fun _ : ι => volume.restrict (Ioc (-1/2:ℝ) (-1/2+1))) := by
  simpa [periodicCubeMeasure,periodicFundamentalCube,Set.pi,volume_pi] using Measure.restrict_pi_pi (fun _ : ι => (volume:Measure ℝ)) (fun _ => Ioc (-1/2:ℝ) (-1/2+1))

instance periodicCubeMeasure_probability : IsProbabilityMeasure (periodicCubeMeasure ι) := by
  constructor
  rw [periodicCubeMeasure_pi,Measure.pi_univ]
  simp

instance periodicCubeMeasure_nullSingleton : NullSingletonClass (periodicCubeMeasure ι) := by
  unfold periodicCubeMeasure
  infer_instance

lemma periodicCubeQuotient_measurePreserving :
    MeasurePreserving (fun x : ι → ℝ => (fun i => (x i:UnitAddCircle)))
      (periodicCubeMeasure ι) (periodicHaar ι) := by
  rw [periodicCubeMeasure_pi]
  unfold periodicHaar
  apply measurePreserving_pi
  intro i
  convert AddCircle.measurePreserving_mk 1 (-1/2) using 1 <;> simp [volume,AddCircle.haarAddCircle]

def periodicRelativeCube (n : ℕ) (ι : Type u) [Fintype ι] : Set (Fin n → ι → ℝ) :=
  {x | ∀ j,x j∈periodicFundamentalCube ι}

lemma periodicRelativeCube_measurable (n : ℕ) : MeasurableSet (periodicRelativeCube n ι) :=
  MeasurableSet.univ_pi' (fun _ => periodicFundamentalCube_measurable)

lemma periodicRelativeCube_measure (n : ℕ) :
    volume.restrict (periodicRelativeCube n ι)=Measure.pi (fun _ : Fin n => periodicCubeMeasure ι) := by
  simpa [periodicRelativeCube,periodicCubeMeasure,Set.pi,volume_pi] using Measure.restrict_pi_pi (fun _ : Fin n => (volume:Measure (ι → ℝ))) (fun _ => periodicFundamentalCube ι)

lemma periodicRelativeCubeQuotient_measurePreserving (n : ℕ) :
    MeasurePreserving (fun x : Fin n → ι → ℝ => (fun j i => (x j i:UnitAddCircle)))
      (volume.restrict (periodicRelativeCube n ι)) (Measure.pi (fun _ : Fin n => periodicHaar ι)) := by
  rw [periodicRelativeCube_measure]
  exact measurePreserving_pi _ _ (fun _ => periodicCubeQuotient_measurePreserving)

lemma periodicCubeSamples_pair_ne (n : ℕ) (i j : Fin n) (hij : i≠j) :
    ∀ᵐ x : Fin n → ι → ℝ ∂Measure.pi (fun _ : Fin n => periodicCubeMeasure ι),x i≠x j := by
  have hp : ∀ᵐ p : (ι → ℝ) × (ι → ℝ) ∂(periodicCubeMeasure ι).prod (periodicCubeMeasure ι),p.1≠p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
    exact Eventually.of_forall (fun x => (Measure.ae_ne (periodicCubeMeasure ι) x).mono (fun _ h => h.symm))
  exact (DGRHS.Decoupling.pair_eval_measurePreserving (periodicCubeMeasure ι) i j hij).quasiMeasurePreserving.ae hp

lemma periodicCubeSamples_cons_injective_ae (n : ℕ) :
    ∀ᵐ x : Fin n → ι → ℝ ∂volume.restrict (periodicRelativeCube n ι),
      Function.Injective (Fin.cons (0:ι → ℝ) x) := by
  rw [periodicRelativeCube_measure]
  have hzero : ∀ᵐ x : Fin n → ι → ℝ ∂Measure.pi (fun _ : Fin n => periodicCubeMeasure ι),∀ j,x j≠0 :=
    ae_all_iff.mpr (fun j => Measure.ae_eval_ne (fun _ : Fin n => periodicCubeMeasure ι) j 0)
  have hp : ∀ᵐ x : Fin n → ι → ℝ ∂Measure.pi (fun _ : Fin n => periodicCubeMeasure ι),∀ i j,i≠j → x i≠x j := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i=j
    · exact Eventually.of_forall (fun _ h => False.elim (h hij))
    · exact (periodicCubeSamples_pair_ne n i j hij).mono (fun _ h _ => h)
  filter_upwards [hzero,hp] with x hz hp
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · intro j
    refine Fin.cases ?_ (fun l => ?_) j
    · intro _;rfl
    · intro he
      exact False.elim (hz l (by simpa using he.symm))
  · intro j
    refine Fin.cases ?_ (fun l => ?_) j
    · intro he
      exact False.elim (hz k (by simpa using he))
    · intro he
      have hkl : k=l := by
        by_contra hn
        exact hp k l hn (by simpa using he)
      exact congrArg Fin.succ hkl

/-- Exact actual partition in Euclidean relative coordinates, with normalized
Lebesgue measure on the fundamental cube and no unproved density factor. -/
theorem periodicAttractivePartition_eq_relativeCube (β : ℝ) (n : ℕ) :
    periodicAttractivePartition (ι := ι) β (n+1)=
      ∫⁻ x : Fin n → ι → ℝ in periodicRelativeCube n ι,
        periodicAnchoredDensity β n (fun j i => (x j i:UnitAddCircle)) := by
  rw [periodicAttractivePartition_eq_anchored]
  have hp := periodicRelativeCubeQuotient_measurePreserving (ι := ι) n
  have h := lintegral_map (μ := volume.restrict (periodicRelativeCube n ι))
    (periodicAnchoredDensity_measurable β n) hp.measurable
  rw [hp.map_eq] at h
  exact h

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicCubeSamples_cons_injective_ae
#print axioms DGRHS.Periodic.periodicAttractivePartition_eq_relativeCube
#check @DGRHS.Periodic.periodicAttractivePartition_eq_relativeCube
