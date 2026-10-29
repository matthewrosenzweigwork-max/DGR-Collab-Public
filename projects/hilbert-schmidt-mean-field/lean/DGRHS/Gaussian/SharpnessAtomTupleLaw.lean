import DGRHS.Gaussian.SharpnessParticleJensen

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Classical
namespace DGRHS.Gaussian
variable {X α J : Type*} [MeasurableSpace X] [Fintype J]

lemma sharpness_atom_reconstruct (μ : Measure X) [IsFiniteMeasure μ]
    (A : Set X) (hm : 0 < (μ A).toReal) :
    μ A • sharpnessNormalizedAtom μ A = μ.restrict A := by
  have hz : μ A ≠ 0 := by intro h; simp [h] at hm
  unfold sharpnessNormalizedAtom
  rw [smul_smul,ENNReal.mul_inv_cancel hz (measure_ne_top μ A),one_smul]

/-- Actual law on a particle atom rectangle: its mass times the genuine
product of normalized atom laws. No conditional-law premise is supplied. -/
theorem sharpness_atom_tuple_law (μ : Measure X) [IsFiniteMeasure μ]
    (A : α → Set X) (hm : ∀ i,0 < (μ (A i)).toReal) (l : J → α) :
    (Measure.pi (fun _ : J => μ)).restrict (Set.univ.pi (fun i => A (l i))) =
      (∏ i, μ (A (l i))) • Measure.pi (fun i => sharpnessNormalizedAtom μ (A (l i))) := by
  let ν := fun i : J => sharpnessNormalizedAtom μ (A (l i))
  haveI : ∀ i,IsProbabilityMeasure (ν i) := fun i => sharpnessNormalizedAtom_probability μ _ (hm _)
  rw [Measure.restrict_pi_pi]
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply,Measure.pi_pi]
  simp only [smul_eq_mul]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  change μ (A (l i)) • ν i (s i) = (μ.restrict (A (l i))) (s i)
  change μ (A (l i)) • (sharpnessNormalizedAtom μ (A (l i))) (s i) = _
  rw [← Measure.smul_apply,sharpness_atom_reconstruct μ (A (l i)) (hm (l i))]

lemma sharpness_atom_tuple_measurable (A : α → Set X) (hA : ∀ i,MeasurableSet (A i))
    (l : J → α) : MeasurableSet (Set.univ.pi (fun i => A (l i))) :=
  MeasurableSet.pi countable_univ (fun i _ => hA (l i))

lemma sharpness_atom_tuple_disjoint (A : α → Set X) (hA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (l k : J → α) (hne : l ≠ k) :
    Disjoint (Set.univ.pi (fun i => A (l i))) (Set.univ.pi (fun i => A (k i))) := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hne
  rw [Set.disjoint_left]
  intro x hx hy
  exact Set.disjoint_left.mp (hA hi) (hx i (Set.mem_univ i)) (hy i (Set.mem_univ i))

lemma sharpness_atom_tuple_cover [Fintype α] (A : α → Set X) (hA : ⋃ i,A i = Set.univ) :
    (⋃ l : J → α, Set.univ.pi (fun i => A (l i))) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx (i : J) : ∃ a,x i ∈ A a := by
    have hh : x i ∈ ⋃ a,A a := by rw [hA]; trivial
    exact Set.mem_iUnion.mp hh
  choose l hl using hx
  exact Set.mem_iUnion.mpr ⟨l,fun i _ => hl i⟩

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_atom_tuple_law
#check @DGRHS.Gaussian.sharpness_atom_tuple_law
