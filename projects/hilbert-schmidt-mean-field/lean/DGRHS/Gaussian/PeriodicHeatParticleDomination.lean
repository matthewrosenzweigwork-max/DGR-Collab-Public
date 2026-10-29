import DGRHS.Gaussian.PeriodicHeatRegularizationComparison
import DGRHS.Gaussian.PeriodicPartitionFinite
import DGRHS.Gaussian.PeriodicCollisionLowerBound

/-! Exact off-diagonal particle comparison and a proper, time-independent
Gibbs-density dominator below the collision threshold. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicHeatParticleExponent (β τ : ℝ) (N : ℕ) (x : Fin N → PeriodicTorus ι) : ℝ :=
  β/(2*(N:ℝ))*∑ i : Fin N,∑ j : Fin N,if i=j then 0 else periodicHeatRegularizedGreen τ (x i-x j)

lemma periodicHeatParticleExponent_measurable (β τ : ℝ) (N : ℕ) :
    Measurable (periodicHeatParticleExponent (ι := ι) β τ N) := by
  unfold periodicHeatParticleExponent
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  by_cases hij : i=j
  · simp only [hij,ite_true];exact measurable_const
  · simp only [hij,ite_false]
    exact (periodicHeatRegularizedGreen_measurable τ).comp ((measurable_pi_apply i).sub (measurable_pi_apply j))

lemma periodicHeatParticleExponent_le (β τ : ℝ) (hβ : 0≤β) (N : ℕ) (hN : 1≤N)
    (x : Fin N → PeriodicTorus ι)
    (hx : ∀ i j : Fin N,i≠j → periodicHeatRegularizedGreen τ (x i-x j)≤
      periodicLogKernel (x i-x j)+periodicHeatComparisonConstant ι) :
    periodicHeatParticleExponent β τ N x≤periodicParticleExponent β N x+
      β*((N:ℝ)-1)/2*periodicHeatComparisonConstant ι := by
  have hs : (∑ i : Fin N,∑ j : Fin N,if i=j then 0 else periodicHeatRegularizedGreen τ (x i-x j))≤
      ∑ i : Fin N,∑ j : Fin N,
        ((if i=j then 0 else periodicLogKernel (x i-x j))+(if i=j then 0 else periodicHeatComparisonConstant ι)) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i=j
    · simp [hij]
    · simpa only [if_neg hij] using hx i j hij
  simp_rw [Finset.sum_add_distrib] at hs
  rw [periodic_offdiagonal_constant_sum] at hs
  have h := mul_le_mul_of_nonneg_left hs (show 0≤β/(2*(N:ℝ)) by positivity)
  unfold periodicHeatParticleExponent periodicParticleExponent
  have hn : (N:ℝ)≠0 := by exact_mod_cast (by omega : N≠0)
  convert h using 1
  field_simp
  <;> ring

/-- One proper dominator, valid for every nonnegative heat parameter. -/
theorem periodicHeatParticleDensity_domination (hd : 2≤Fintype.card ι) (β : ℝ) (hβ : 0≤β)
    (hβd : β<2*(Fintype.card ι:ℝ)) (N : ℕ) (hN : 1≤N) :
    Integrable (fun x : Fin N → PeriodicTorus ι =>
      Real.exp (β*((N:ℝ)-1)/2*periodicHeatComparisonConstant ι)*Real.exp (periodicParticleExponent β N x))
      (Measure.pi (fun _ : Fin N => periodicHaar ι)) ∧
    ∀ᵐ x : Fin N → PeriodicTorus ι ∂Measure.pi (fun _ : Fin N => periodicHaar ι),
      ∀ τ : ℝ,0≤τ → ‖Real.exp (periodicHeatParticleExponent β τ N x)‖≤
        Real.exp (β*((N:ℝ)-1)/2*periodicHeatComparisonConstant ι)*Real.exp (periodicParticleExponent β N x) := by
  refine ⟨(periodicParticleDensity_integrable_upper β hβ hβd N hN).1.const_mul _,?_⟩
  filter_upwards [periodicHeatRegularizedGreen_particle_good_ae hd N] with x hx
  intro τ hτ
  rw [Real.norm_of_nonneg (Real.exp_pos _).le,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simpa only [add_comm] using periodicHeatParticleExponent_le β τ hβ N hN x (fun i j hij => (hx i j hij).1 τ hτ)

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicHeatParticleExponent_le
#print axioms DGRHS.Periodic.periodicHeatParticleDensity_domination
#check @DGRHS.Periodic.periodicHeatParticleDensity_domination
