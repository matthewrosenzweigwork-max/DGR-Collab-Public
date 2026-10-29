import DGRHS.Gaussian.PeriodicCollisionRadial
import DGRHS.Gaussian.PeriodicCollisionLowerBound

/-! Actual fixed-particle divergence at and above beta=2d. The lower comparison
is on the genuine Euclidean relative-coordinate cube, all off-diagonal
collisions are null, and the equality case is the radial logarithmic endpoint. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Classical BigOperators ENNReal
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicCollision_injective_ae_ball (n : ℕ) :
    ∀ᵐ x : Fin n → ι → ℝ ∂volume.restrict (ball 0 (periodicCollisionRadius ι)),
      Function.Injective (Fin.cons (0:ι → ℝ) x) := by
  have h := (ae_restrict_iff' (periodicRelativeCube_measurable (ι := ι) n)).mp
    (periodicCubeSamples_cons_injective_ae (ι := ι) n)
  filter_upwards [ae_restrict_of_ae h,ae_restrict_mem measurableSet_ball] with x hx hxb
  exact hx (periodicCollisionBall_subset_cube n hxb)

lemma periodic_collision_partition_succ (β : ℝ) (hβ : 2*(Fintype.card ι:ℝ)≤β)
    (n : ℕ) (hn : 1≤n) : periodicAttractivePartition (ι := ι) β (n+1)=∞ := by
  letI : NeZero n := ⟨by omega⟩
  have hβ0 : 0≤β := (by positivity : (0:ℝ)≤2*(Fintype.card ι:ℝ)).trans hβ
  have hdim : Module.finrank ℝ (Fin n → ι → ℝ)=n*Fintype.card ι := by
    rw [Module.finrank_pi_fintype]
    simp [Module.finrank_pi]
  have hd : 1≤Module.finrank ℝ (Fin n → ι → ℝ) := by
    rw [hdim]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) Fintype.card_ne_zero)
  have ha : (Module.finrank ℝ (Fin n → ι → ℝ):ℝ)≤β*(n:ℝ)/2 := by
    rw [hdim,Nat.cast_mul]
    nlinarith [mul_le_mul_of_nonneg_right hβ (Nat.cast_nonneg n)]
  have hrad := lintegral_norm_rpow_ball_eq_top (volume:Measure (Fin n → ι → ℝ)) hd
    (β*(n:ℝ)/2) (periodicCollisionRadius ι) ha periodicCollisionRadius_pos
  have htop : (∫⁻ x : Fin n → ι → ℝ in ball 0 (periodicCollisionRadius ι),
      ENNReal.ofReal (Real.exp (β*(n:ℝ)/2*periodicCollisionLowerConstant ι))*
        ENNReal.ofReal (‖x‖^(-(β*(n:ℝ)/2))))=∞ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,hrad]
    exact ENNReal.mul_top (by positivity)
  have hlo : (∫⁻ x : Fin n → ι → ℝ in ball 0 (periodicCollisionRadius ι),
      ENNReal.ofReal (Real.exp (β*(n:ℝ)/2*periodicCollisionLowerConstant ι))*
        ENNReal.ofReal (‖x‖^(-(β*(n:ℝ)/2))))≤
      ∫⁻ x : Fin n → ι → ℝ in ball 0 (periodicCollisionRadius ι),
        periodicAnchoredDensity β n (fun j k => (x j k:UnitAddCircle)) := by
    apply lintegral_mono_ae
    filter_upwards [periodicCollision_injective_ae_ball (ι := ι) n,
      ae_restrict_of_ae (Measure.ae_ne (volume:Measure (Fin n → ι → ℝ)) 0),
      ae_restrict_mem measurableSet_ball] with x hi hx0 hx
    exact periodicCollision_density_lower β hβ0 n x hx hx0 hi
  apply top_unique
  rw [periodicAttractivePartition_eq_relativeCube]
  rw [htop] at hlo
  exact hlo.trans (lintegral_mono_set (periodicCollisionBall_subset_cube n))

/-- The exact original collision clause, including beta=2d and every N>=2. -/
theorem periodic_collision_partition (β : ℝ) (hβ : 2*(Fintype.card ι:ℝ)≤β)
    (N : ℕ) (hN : 2≤N) : periodicAttractivePartition (ι := ι) β N=∞ := by
  cases N with
  | zero => omega
  | succ n => exact periodic_collision_partition_succ β hβ n (by omega)

/-- The original dimension range and all of its endpoint quantifiers. -/
theorem periodic_collision_partition_source (d : ℕ) (hd : 11≤d) (β : ℝ) (hβ : 2*(d:ℝ)≤β)
    (N : ℕ) (hN : 2≤N) :
    letI : NeZero d := ⟨by omega⟩
    periodicAttractivePartition (ι := Fin d) β N=∞ := by
  letI : NeZero d := ⟨by omega⟩
  exact periodic_collision_partition β (by simpa only [Fintype.card_fin] using hβ) N hN

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_collision_partition
#print axioms DGRHS.Periodic.periodic_collision_partition_source
#check @DGRHS.Periodic.periodic_collision_partition_source
