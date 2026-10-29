import DGRHS.Gaussian.SharpnessPhysicalParticleJensen
import DGRHS.Gaussian.SharpnessDyadicLaplace
import DGRHS.Gaussian.SharpnessDeterminantLower

noncomputable section
open MeasureTheory Set Filter BoxIntegral
open scoped ENNReal Classical
namespace DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι]

/-- Proper full singular partition has a finite-compression spectral square
lower bound with an actual explicit finite-particle error. The full singular
kernel is only L1; the spectrum and HS identity belong to the constructed
finite compression. -/
theorem sharpness_physical_finite_particle_lower (s : ℝ) (hs : 0 < s)
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
    let κ := sharpnessCompression μ H A
    let B := gaussianRieszPhysicalPotentialConstant s M ι
    let D := sharpnessGoodDiagonalCoefficient s M a ι*(L/(2:ℝ)^m)^(-s)+8*B
    Integrable (fun x => Real.exp (-β/2*sourceKernelParticleStatistic H N x)) (Measure.pi (fun _ => μ)) ∧
      Real.exp (β^2/(8*(1+β*(4*B)))*(∫ p,κ p^2 ∂μ.prod μ))-
        (26*β^2+12*β^3)*(Real.exp (β*D/2)*(1+D^4))^2/(N:ℝ) ≤
      ∫ x,Real.exp (-β/2*sourceKernelParticleStatistic H N x) ∂Measure.pi (fun _ => μ) := by
  let μ := gaussianRieszDensityMeasure ρ
  let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  let P := sharpnessDyadicPartition I m
  let A := sharpnessPartitionAtom ρ a P
  let κ := sharpnessCompression μ H A
  let hk := sharpnessCompression_memLp μ H A (measurableSet_sharpnessPartitionAtom ρ hρm a P)
  let B := gaussianRieszPhysicalPotentialConstant s M ι
  have hj := sharpness_physical_dyadic_particle_comparison s hs ha ρ hρm M hM hρ a ha0 I L hL hw hI m N hN β hβ
  obtain ⟨j,eig,e,hjcount,he,hpos,hsum,htrace,hRate⟩ :=
    sharpness_dyadic_laplace_rate s hs ha ρ hρm M hM hρ a ha0 I L hL hw hI m β hβ
  letI := hjcount
  have hB : 0 ≤ B := ((sharpness_riesz_potential_bound s hs ha ρ M hM hρ 0).2.1).trans
    (sharpness_riesz_potential_bound s hs ha ρ M hM hρ 0).2.2
  have hop := sharpness_physical_compression_operator_bound s hs ha ρ M hM hρ A
    (measurableSet_sharpnessPartitionAtom ρ hρm a P)
    (sharpnessPartitionAtom_pairwise_disjoint ρ a P) (sharpnessPartitionAtom_covers ρ a P)
    (fun i => ne_of_gt (sharpnessPartitionAtom_mass_pos ρ hρm a ha0 I L hL hw m hI i))
  have heL (i : j) : eig i ≤ 4*B := by
    have hn := (DGRHS.Kernel.integralOperator κ hk).le_opNorm (e i)
    rw [he i,norm_smul,e.orthonormal.1 i,mul_one,mul_one,Real.norm_eq_abs,abs_of_nonneg (hpos i)] at hn
    exact hn.trans hop
  have hsquare := DGRHS.Kernel.summable_integralOperator_eigenvalue_sq κ hk eig e he
  have hsq := DGRHS.Kernel.tsum_integralOperator_eigenvalue_sq κ hk eig e he
  have hdet := sharpness_inv_sqrt_det_lower eig hsquare hpos (4*B) (by positivity) heL β hβ
  rw [hsq] at hdet
  have hr := (abs_le.mp (hRate N hN).2).1
  refine ⟨hj.1,?_⟩
  exact (by linarith [hdet] : _ ≤ ∫ x,Real.exp (-β/2*sourceKernelParticleStatistic κ N x)
    ∂Measure.pi (fun _ => μ)).trans hj.2.2

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_physical_finite_particle_lower
#check @DGRHS.Gaussian.sharpness_physical_finite_particle_lower
