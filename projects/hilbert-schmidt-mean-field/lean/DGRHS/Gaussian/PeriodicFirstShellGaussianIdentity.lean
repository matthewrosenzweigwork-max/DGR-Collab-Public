import DGRHS.Gaussian.PeriodicFirstShellTiltProduct
import DGRHS.Gaussian.PeriodicFirstShellAtomBound
import DGRHS.Gaussian.PeriodicFiniteGramRemoval

/-! Actual bounded torus first-shell finite Gaussian identity, with its
constant diagonal and exact source beta/(2N) ordered-pair coefficient. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Classical BigOperators
namespace DGRHS.Periodic
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicFirstShellSpatialFeature (x : PeriodicTorus ι) (q : ι × Bool) : ℝ :=
  Real.sqrt (2*(periodicStabilityThreshold ι)⁻¹)*periodicFirstShellMode q x

lemma periodicFirstShellSpatialFeature_gram (x y : PeriodicTorus ι) :
    (∑ q : ι × Bool,periodicFirstShellSpatialFeature x q*periodicFirstShellSpatialFeature y q)=
      periodicFirstShellKernel x y := by
  unfold periodicFirstShellSpatialFeature periodicFirstShellKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  have hc : 0≤2*(periodicStabilityThreshold ι)⁻¹ :=
    mul_nonneg (by norm_num) (inv_nonneg.mpr periodicStabilityThreshold_pos.le)
  calc
    _ = Real.sqrt (2*(periodicStabilityThreshold ι)⁻¹)^2*(periodicFirstShellMode q x*periodicFirstShellMode q y) := by ring
    _ = _ := by rw [Real.sq_sqrt hc]

lemma periodicFirstShellSpatialFeature_diagonal (x : PeriodicTorus ι) :
    (∑ q : ι × Bool,periodicFirstShellSpatialFeature x q^2)=
      2*(periodicStabilityThreshold ι)⁻¹*(Fintype.card ι : ℝ) := by
  unfold periodicFirstShellSpatialFeature
  have hc : 0≤2*(periodicStabilityThreshold ι)⁻¹ :=
    mul_nonneg (by norm_num) (inv_nonneg.mpr periodicStabilityThreshold_pos.le)
  simp_rw [mul_pow,Real.sq_sqrt hc]
  rw [←Finset.mul_sum,periodicFirstShellMode_square_sum]

lemma periodicFirstShellWeight_product_exp (t : ℝ) (N : ℕ)
    (x : Fin N → PeriodicTorus ι) (z : ι × Bool → ℝ) :
    (∏ i,periodicFirstShellWeight t z (x i)) =
      Real.exp (∑ q : ι × Bool,(t*∑ i,periodicFirstShellSpatialFeature (x i) q)*z q) := by
  unfold periodicFirstShellWeight
  rw [←Real.exp_sum]
  congr 1
  unfold periodicFirstShellField periodicFirstShellSpatialFeature
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma periodic_firstShell_weight_particle_gaussian (t : ℝ) (N : ℕ)
    (x : Fin N → PeriodicTorus ι) :
    Integrable (fun z => ∏ i,periodicFirstShellWeight t z (x i)) (finiteStandardGaussian (ι × Bool)) ∧
    (∫ z,∏ i,periodicFirstShellWeight t z (x i) ∂finiteStandardGaussian (ι × Bool)) =
      Real.exp (t^2/2*∑ q : ι × Bool,(∑ i,periodicFirstShellSpatialFeature (x i) q)^2) := by
  have h := periodic_finiteGaussian_linear_exp (fun q : ι × Bool => t*∑ i,periodicFirstShellSpatialFeature (x i) q)
  constructor
  · exact h.1.congr (Eventually.of_forall fun z => (periodicFirstShellWeight_product_exp t N x z).symm)
  · simp_rw [periodicFirstShellWeight_product_exp]
    rw [h.2]
    congr 1
    simp_rw [mul_pow]
    rw [←Finset.mul_sum]
    ring

lemma periodic_firstShell_particle_covariance (N : ℕ) (x : Fin N → PeriodicTorus ι) :
    (∑ q : ι × Bool,(∑ i,periodicFirstShellSpatialFeature (x i) q)^2) =
      (∑ i : Fin N,∑ j : Fin N,if i=j then 0 else periodicFirstShellKernel (x i) (x j))+
        (N:ℝ)*(2*(periodicStabilityThreshold ι)⁻¹*(Fintype.card ι : ℝ)) := by
  have h := periodic_Gram_square_offDiagonal (fun i : Fin N => periodicFirstShellSpatialFeature (x i))
  simp_rw [periodicFirstShellSpatialFeature_gram,periodicFirstShellSpatialFeature_diagonal] at h
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  linarith

lemma periodic_firstShell_gaussian_source_coefficient (β : ℝ) (hβ : 0≤β) (N : ℕ)
    (hN : 1≤N) (x : Fin N → PeriodicTorus ι) :
    (∫ z,∏ i,periodicFirstShellWeight (Real.sqrt (β/N)) z (x i)
      ∂finiteStandardGaussian (ι × Bool)) =
      Real.exp (β*(periodicStabilityThreshold ι)⁻¹*(Fintype.card ι : ℝ))*
        Real.exp (β/(2*(N:ℝ))*∑ i : Fin N,∑ j : Fin N,if i=j then 0 else periodicFirstShellKernel (x i) (x j)) := by
  rw [(periodic_firstShell_weight_particle_gaussian _ N x).2,
    Real.sq_sqrt (div_nonneg hβ (Nat.cast_nonneg N)),periodic_firstShell_particle_covariance,←Real.exp_add]
  congr 1
  have hn : (N:ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  field_simp
  ring

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicFirstShellSpatialFeature_gram
#print axioms DGRHS.Periodic.periodicFirstShellSpatialFeature_diagonal
#print axioms DGRHS.Periodic.periodicFirstShellWeight_product_exp
#print axioms DGRHS.Periodic.periodic_firstShell_weight_particle_gaussian
#print axioms DGRHS.Periodic.periodic_firstShell_particle_covariance
#print axioms DGRHS.Periodic.periodic_firstShell_gaussian_source_coefficient
#check @DGRHS.Periodic.periodic_firstShell_gaussian_source_coefficient
