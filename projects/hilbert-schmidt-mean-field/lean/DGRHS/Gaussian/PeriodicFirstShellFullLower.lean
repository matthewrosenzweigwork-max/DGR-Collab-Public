import DGRHS.Gaussian.PeriodicFirstShellGaussianIdentity
import DGRHS.Gaussian.PeriodicSupercriticalPartition

/-! Direct first-shell lower bound for the actual extended full partition.
Tonelli applies to the nonnegative joint integrand, without any assumption
that the singular full partition is finite. This is an alternative to the
source heat-regularization argument, retaining the exact same coefficient. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Classical BigOperators
namespace DGRHS.Periodic
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicParticleExponent_firstShell_residual (β : ℝ) (N : ℕ)
    (x : Fin N → PeriodicTorus ι) :
    periodicParticleExponent β N x =
      β/(2*(N:ℝ))*(∑ i : Fin N,∑ j : Fin N,if i=j then 0 else periodicFirstShellKernel (x i) (x j))+
        periodicResidualParticleExponent β N x := by
  unfold periodicParticleExponent periodicResidualParticleExponent periodicFirstShellResidualPair
  rw [←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma periodicFirstShellWeight_joint_continuous (t : ℝ) :
    Continuous (fun p : (ι × Bool → ℝ) × PeriodicTorus ι => periodicFirstShellWeight t p.1 p.2) := by
  unfold periodicFirstShellWeight periodicFirstShellField
  apply Real.continuous_exp.comp
  apply continuous_finset_sum
  intro q _
  exact ((continuous_const.mul ((continuous_apply q).comp continuous_fst)).mul
    ((periodicFirstShellMode_continuous q).comp continuous_snd))

lemma periodic_firstShell_full_pointwise (β : ℝ) (hβ : 0≤β) (N : ℕ) (hN : 1≤N)
    (x : Fin N → PeriodicTorus ι) :
    ENNReal.ofReal (Real.exp (periodicParticleExponent β N x)) =
      ENNReal.ofReal (Real.exp (-β*(periodicStabilityThreshold ι)⁻¹*(Fintype.card ι:ℝ)))*
        ∫⁻ z,ENNReal.ofReal ((∏ i,periodicFirstShellWeight (Real.sqrt (β/N)) z (x i))*
          Real.exp (periodicResidualParticleExponent β N x)) ∂finiteStandardGaussian (ι × Bool) := by
  have hi := (periodic_firstShell_weight_particle_gaussian (Real.sqrt (β/N)) N x).1
  rw [←ofReal_integral_eq_lintegral_ofReal (hi.mul_const _)
    (Eventually.of_forall fun z => mul_nonneg (Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le)) (Real.exp_pos _).le),
    integral_mul_const,periodic_firstShell_gaussian_source_coefficient β hβ N hN,
    ←ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  rw [periodicParticleExponent_firstShell_residual]
  simp only [←Real.exp_add]
  congr 1
  ring

/-- The source full partition dominates the genuine first-shell Gaussian
normalizer moment. No residual mean, comparison, or finiteness input. -/
theorem periodic_firstShell_full_partition_lower (β : ℝ) (hβ : 0≤β) (N : ℕ) (hN : 1≤N) :
    ENNReal.ofReal (Real.exp (-β*(periodicStabilityThreshold ι)⁻¹*(Fintype.card ι:ℝ)))*
      (∫⁻ z,ENNReal.ofReal (periodicFirstShellNormalizer (Real.sqrt (β/N)) z^N)
        ∂finiteStandardGaussian (ι × Bool)) ≤ periodicAttractivePartition (ι := ι) β N := by
  let μ := Measure.pi (fun _ : Fin N => periodicHaar ι)
  let γ := finiteStandardGaussian (ι × Bool)
  let W := fun (z : ι × Bool → ℝ) (x : Fin N → PeriodicTorus ι) =>
    ENNReal.ofReal ((∏ i,periodicFirstShellWeight (Real.sqrt (β/N)) z (x i))*
      Real.exp (periodicResidualParticleExponent β N x))
  have hW : Measurable (Function.uncurry W) := by
    apply Measurable.ennreal_ofReal
    apply Measurable.mul
    · apply Finset.measurable_prod
      intro i _
      exact (periodicFirstShellWeight_joint_continuous _).measurable.comp
        (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
    · exact ((periodicResidualParticleExponent_measurable β N).comp measurable_snd).exp
  have hswap : (∫⁻ z,∫⁻ x,W z x ∂μ ∂γ)=(∫⁻ x,∫⁻ z,W z x ∂γ ∂μ) :=
    lintegral_lintegral_swap hW.aemeasurable
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-β*(periodicStabilityThreshold ι)⁻¹*(Fintype.card ι:ℝ)))*
        (∫⁻ z,∫⁻ x,W z x ∂μ ∂γ) := by
      apply mul_le_mul_of_nonneg_left _ zero_le
      apply lintegral_mono
      intro z
      exact periodic_firstShell_weighted_residual_lower _ z β hβ N hN
    _ = ∫⁻ x,ENNReal.ofReal (Real.exp (-β*(periodicStabilityThreshold ι)⁻¹*(Fintype.card ι:ℝ)))*
        (∫⁻ z,W z x ∂γ) ∂μ := by
      rw [hswap,lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
    _ = _ := by
      apply lintegral_congr
      intro x
      exact (periodic_firstShell_full_pointwise β hβ N hN x).symm

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicParticleExponent_firstShell_residual
#print axioms DGRHS.Periodic.periodicFirstShellWeight_joint_continuous
#print axioms DGRHS.Periodic.periodic_firstShell_full_pointwise
#print axioms DGRHS.Periodic.periodic_firstShell_full_partition_lower
#check @DGRHS.Periodic.periodic_firstShell_full_partition_lower
