import DGRHS.Gaussian.SharpnessAtomTupleLaw

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Classical
namespace DGRHS.Gaussian
variable {X α : Type*} [MeasurableSpace X] [Fintype α]

lemma sharpnessNormalizedAtom_univ (μ : Measure X) [IsProbabilityMeasure μ] :
    sharpnessNormalizedAtom μ Set.univ = μ := by
  simp [sharpnessNormalizedAtom]

lemma sharpness_particle_integrable (μ : Measure X) [IsProbabilityMeasure μ]
    (H : X × X → ℝ) (hH : Integrable H (μ.prod μ)) (N : ℕ) :
    Integrable (sourceKernelParticleStatistic H N) (Measure.pi (fun _ : Fin N => μ)) := by
  have hh := (sharpness_conditional_particle_mean μ H hH (fun _ : Unit => Set.univ)
    (fun _ => MeasurableSet.univ) (fun _ => by simp) N (fun _ => ())).1
  simpa only [sharpnessNormalizedAtom_univ] using hh

lemma sharpness_compression_particle_on_tuple (μ : Measure X) (H : X × X → ℝ)
    (A : α → Set X) (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (N : ℕ) (l : Fin N → α) (x : Fin N → X)
    (hx : x ∈ Set.univ.pi (fun i => A (l i))) :
    sourceKernelParticleStatistic (sharpnessCompression μ H A) N x =
      sourceKernelParticleStatistic (fun p : α × α => sharpnessAtomAverage μ H (A p.1) (A p.2)) N l := by
  unfold sourceKernelParticleStatistic
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij,ite_false]
    exact sharpnessCompression_on_atom μ H A hd (hx i (Set.mem_univ i)) (hx j (Set.mem_univ j))

/-- Genuine iid finite-particle conditional Jensen for the actual block
averaging kernel. Both exponential integrability conclusions are derived. -/
theorem sharpness_particle_compression_comparison (μ : Measure X) [IsProbabilityMeasure μ]
    (H : X × X → ℝ) (hH : Integrable H (μ.prod μ))
    (B : ℝ) (hB : 0 ≤ B) (hlo : ∀ p,-B ≤ H p)
    (A : α → Set X) (hA : ∀ i,MeasurableSet (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (hu : ⋃ i,A i = Set.univ)
    (hm : ∀ i,0 < (μ (A i)).toReal) (N : ℕ) (hN : 1 ≤ N) (β : ℝ) (hβ : 0 ≤ β) :
    Integrable (fun x => Real.exp (-β/2*sourceKernelParticleStatistic H N x)) (Measure.pi (fun _ => μ)) ∧
    Integrable (fun x => Real.exp (-β/2*sourceKernelParticleStatistic (sharpnessCompression μ H A) N x))
      (Measure.pi (fun _ => μ)) ∧
    (∫ x,Real.exp (-β/2*sourceKernelParticleStatistic (sharpnessCompression μ H A) N x)
      ∂Measure.pi (fun _ => μ)) ≤
      ∫ x,Real.exp (-β/2*sourceKernelParticleStatistic H N x) ∂Measure.pi (fun _ => μ) := by
  let ν := Measure.pi (fun _ : Fin N => μ)
  let κ := sharpnessCompression μ H A
  let f := fun x : Fin N → X => Real.exp (-β/2*sourceKernelParticleStatistic H N x)
  let g := fun x : Fin N → X => Real.exp (-β/2*sourceKernelParticleStatistic κ N x)
  let S := fun l : Fin N → α => Set.univ.pi (fun i => A (l i))
  have hf : Integrable f ν := sharpness_particle_exponential_integrable H
    (sharpness_particle_integrable μ H hH N) B hB hlo hN β hβ
  let K := ∑ ij : α × α, |sharpnessAtomAverage μ H (A ij.1) (A ij.2)|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hκlo (p : X × X) : -K ≤ κ p := by
    have hh := norm_sharpnessAtomStep_le (fun ij : α × α => A ij.1 ×ˢ A ij.2)
      (fun ij => sharpnessAtomAverage μ H (A ij.1) (A ij.2)) p
    have hh' : |κ p| ≤ K := hh
    exact (abs_le.mp hh').1
  have hκ : Integrable κ (μ.prod μ) := (sharpnessCompression_memLp μ H A hA).integrable (by norm_num)
  have hg : Integrable g ν := sharpness_particle_exponential_integrable κ
    (sharpness_particle_integrable μ κ hκ N) K hK hκlo hN β hβ
  refine ⟨hf,hg,?_⟩
  have hS : ∀ l,MeasurableSet (S l) := fun l => sharpness_atom_tuple_measurable A hA l
  have hdS : Pairwise (fun l k => Disjoint (S l) (S k)) :=
    fun l k hne => sharpness_atom_tuple_disjoint A hd l k hne
  have huS : (⋃ l,S l) = Set.univ := sharpness_atom_tuple_cover A hu
  have heF := integral_iUnion_fintype hS hdS (fun _ => hf.restrict)
  have heG := integral_iUnion_fintype hS hdS (fun _ => hg.restrict)
  rw [huS,Measure.restrict_univ] at heF heG
  rw [heG,heF]
  apply Finset.sum_le_sum
  intro l _
  have hj := sharpness_conditional_particle_jensen μ H hH B hB hlo A hA hm N hN l β hβ
  rw [sharpness_atom_tuple_law μ A hm l,
    integral_smul_measure,integral_smul_measure]
  simp only [smul_eq_mul]
  haveI : ∀ i : Fin N,IsProbabilityMeasure (sharpnessNormalizedAtom μ (A (l i))) :=
    fun i => sharpnessNormalizedAtom_probability μ _ (hm _)
  have hae : ∀ᵐ x ∂Measure.pi (fun i => sharpnessNormalizedAtom μ (A (l i))),x ∈ S l := by
    simp only [S,Set.mem_univ_pi]
    exact ae_all_iff.mpr (fun i => (measurePreserving_eval
      (fun i => sharpnessNormalizedAtom μ (A (l i))) i).quasiMeasurePreserving.ae
        (sharpnessNormalizedAtom_ae_mem μ _ (hA _)))
  have heg : (∫ x,g x ∂Measure.pi (fun i => sharpnessNormalizedAtom μ (A (l i)))) =
      Real.exp (-β/2*sourceKernelParticleStatistic
        (fun p : α × α => sharpnessAtomAverage μ H (A p.1) (A p.2)) N l) := by
    calc
      _ = ∫ _ : Fin N → X,Real.exp (-β/2*sourceKernelParticleStatistic
          (fun p : α × α => sharpnessAtomAverage μ H (A p.1) (A p.2)) N l)
          ∂Measure.pi (fun i => sharpnessNormalizedAtom μ (A (l i))) := by
        apply integral_congr_ae
        filter_upwards [hae] with x hx
        dsimp [g,κ]
        rw [sharpness_compression_particle_on_tuple μ H A hd N l x hx]
      _ = _ := by simp
  rw [heg]
  exact mul_le_mul_of_nonneg_left hj ENNReal.toReal_nonneg

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_particle_compression_comparison
#check @DGRHS.Gaussian.sharpness_particle_compression_comparison
