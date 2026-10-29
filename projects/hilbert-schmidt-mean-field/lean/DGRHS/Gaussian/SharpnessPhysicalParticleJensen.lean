import DGRHS.Gaussian.SharpnessParticleComparison
import DGRHS.Gaussian.SharpnessDyadicFeature

noncomputable section
open MeasureTheory Set Filter BoxIntegral
open scoped ENNReal Classical
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma sharpness_centered_riesz_pointwise_lower (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    -2*gaussianRieszPhysicalPotentialConstant s M ι ≤
      hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s) p := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun x y : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (x,y)
  have hx := sharpness_riesz_potential_bound s hs ha ρ M hM hρ p.1
  have hy := sharpness_riesz_potential_bound s hs ha ρ M hM hρ p.2
  have hm := sharpness_riesz_pair_mean_bound s hs ha ρ M hM hρ
  have hw : 0 ≤ W p.1 p.2 := by unfold W gaussianRieszPhysicalPair; positivity
  change _ ≤ W p.1 p.2-DGRHS.potential μ W p.1-DGRHS.secondPotential μ W p.2+_
  rw [DGRHS.secondPotential_eq_potential μ W (sharpness_riesz_pair_symmetric s)]
  dsimp [W,μ,DGRHS.potential] at *
  linarith [hx.2.2,hy.2.2,hm.1]

/-- True full-versus-dyadic partition comparison throughout 0<s<d, including
the HS-critical and supercritical ranges. No full-kernel L2 or exponential
moment conclusion is used as an input. -/
theorem sharpness_physical_dyadic_particle_comparison (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρm : Measurable ρ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) (a : ℝ) (ha0 : 0 < a)
    (I : Box ι) (L : ℝ) (hL : 0 < L) (hw : ∀ i,I.upper i-I.lower i = L)
    (hI : gaussianRieszDensityMeasure ρ (WithLp.ofLp ⁻¹' (I : Set (ι → ℝ))) ≤ ENNReal.ofReal (1/2:ℝ))
    (m N : ℕ) (hN : 1 ≤ N) (β : ℝ) (hβ : 0 ≤ β) :
    let μ := gaussianRieszDensityMeasure ρ
    let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    let A := sharpnessPartitionAtom ρ a (sharpnessDyadicPartition I m)
    Integrable (fun x => Real.exp (-β/2*sourceKernelParticleStatistic H N x)) (Measure.pi (fun _ => μ)) ∧
    Integrable (fun x => Real.exp (-β/2*sourceKernelParticleStatistic (sharpnessCompression μ H A) N x))
      (Measure.pi (fun _ => μ)) ∧
    (∫ x,Real.exp (-β/2*sourceKernelParticleStatistic (sharpnessCompression μ H A) N x)
      ∂Measure.pi (fun _ => μ)) ≤
      ∫ x,Real.exp (-β/2*sourceKernelParticleStatistic H N x) ∂Measure.pi (fun _ => μ) := by
  let P := sharpnessDyadicPartition I m
  let A := sharpnessPartitionAtom ρ a P
  let μ := gaussianRieszDensityMeasure ρ
  let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  have hB : 0 ≤ gaussianRieszPhysicalPotentialConstant s M ι :=
    ((sharpness_riesz_potential_bound s hs ha ρ M hM hρ 0).2.1).trans
      (sharpness_riesz_potential_bound s hs ha ρ M hM hρ 0).2.2
  apply sharpness_particle_compression_comparison μ H
    (sharpness_centered_riesz_integrable s hs ha ρ M hM hρ) (2*gaussianRieszPhysicalPotentialConstant s M ι)
    (by positivity) (fun p => by simpa only [neg_mul] using sharpness_centered_riesz_pointwise_lower s hs ha ρ M hM hρ p)
    A (measurableSet_sharpnessPartitionAtom ρ hρm a P)
    (sharpnessPartitionAtom_pairwise_disjoint ρ a P)
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i,hi⟩ := sharpnessPartitionAtom_covers ρ a P x
    exact Set.mem_iUnion.mpr ⟨i,hi⟩
  · exact sharpnessPartitionAtom_mass_pos ρ hρm a ha0 I L hL hw m hI
  · exact hN
  · exact hβ

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_physical_dyadic_particle_comparison
#check @DGRHS.Gaussian.sharpness_physical_dyadic_particle_comparison
