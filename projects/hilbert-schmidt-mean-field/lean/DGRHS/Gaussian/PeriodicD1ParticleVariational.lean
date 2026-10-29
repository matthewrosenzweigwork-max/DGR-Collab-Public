import DGRHS.Gaussian.PeriodicD1ProductKL
import DGRHS.Gaussian.PeriodicPartitionFinite
import DGRHS.Gaussian.PeriodicGlobalMinimization
import DGRHS.Entropy.ExponentialTransfer

/-! UNCOMPILED CANDIDATE (Claude complete physical d1 return, 2026-10-03).
Finite-particle Gibbs variational bound for an ARBITRARY finite-KL competitor
law, on the literal source particle exponent. It is generic in the torus
coordinate type and therefore contains no Dyson formula.

The proof applies the already checked `entropy_two_signs_of_exponential`
(ExponentialTransfer) with reference `Haar^N`, competitor `ν^N` and the actual
exponent `U_N = β/(2N) Σ_{i≠j} G(x_i-x_j)`:
* `exp U_N` is proper by the checked `periodicParticleDensity_integrable_upper`
  (0 ≤ β < 2·card ι);
* `exp (-U_N)` is AE bounded, from the checked AE global Green lower bound
  transported to every ordered distinct pair (finite intersection of
  Haar-null exceptional events);
* `KL(ν^N | Haar^N) = N · KL(ν | Haar)` by `klDiv_pi_iid`.
Competitor integrability of `U_N` is DERIVED, not assumed. The two-particle
identity `U_2(x) = (β/2) G(x 0 - x 1)` then gives proper pair energy for every
finite-KL law at any fixed positive β, and the checked iid off-diagonal mean
gives the exact coefficient `β (N-1)/2`. No density bound, L2 hypothesis,
finite energy, or desired entropy-energy inequality is a premise. -/
noncomputable section
open MeasureTheory InformationTheory Filter
open scoped ENNReal BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Every ordered distinct pair satisfies the checked Green lower bound, on one
common full-measure event of the product Haar law. -/
lemma periodicParticle_pairs_lower_ae (N : ℕ) :
    ∀ᵐ x : Fin N → PeriodicTorus ι ∂Measure.pi (fun _ : Fin N => periodicHaar ι),
      ∀ i j : Fin N, i ≠ j → -periodicGreenLowerConstant ι ≤ periodicLogKernel (x i - x j) := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  by_cases hij : i = j
  · exact Eventually.of_forall fun _ h => absurd hij h
  · have hp := (periodicHaar_preserving_difference (ι := ι)).comp
      (DGRHS.Decoupling.pair_eval_measurePreserving (periodicHaar ι) i j hij)
    exact (hp.quasiMeasurePreserving.ae periodicLogKernel_lower_ae).mono fun x hx _ => hx

/-- The negative particle exponential is bounded, hence proper, under `Haar^N`. -/
lemma periodicParticleExponent_neg_exp_integrable (β : ℝ) (hβ0 : 0 ≤ β) (N : ℕ) :
    Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (-periodicParticleExponent β N x))
      (Measure.pi (fun _ : Fin N => periodicHaar ι)) := by
  have ha : 0 ≤ β/(2*(N:ℝ)) := div_nonneg hβ0 (by positivity)
  let T : ℝ := ∑ _i : Fin N, ∑ _j : Fin N, -periodicGreenLowerConstant ι
  apply (integrable_const (Real.exp (-(β/(2*(N:ℝ))*T)))).mono'
    (Real.continuous_exp.measurable.comp
      (periodicParticleExponent_measurable (ι := ι) β N).neg).aestronglyMeasurable
  filter_upwards [periodicParticle_pairs_lower_ae (ι := ι) N] with x hx
  change ‖Real.exp (-periodicParticleExponent β N x)‖ ≤ Real.exp (-(β/(2*(N:ℝ))*T))
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  have hTS : T ≤ ∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else periodicLogKernel (x i - x j) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i = j
    · rw [if_pos hij]
      exact neg_nonpos.mpr periodicGreenLowerConstant_nonneg
    · rw [if_neg hij]
      exact hx i j hij
  have hm := mul_le_mul_of_nonneg_left hTS ha
  change -(β/(2*(N:ℝ))*∑ i : Fin N, ∑ j : Fin N,
    if i = j then 0 else periodicLogKernel (x i - x j)) ≤ -(β/(2*(N:ℝ))*T)
  linarith

/-- Sharp finite-N Gibbs variational bound for every finite-KL competitor law.
The competitor expectation of the literal exponent is proved proper. -/
theorem periodicParticle_entropy_variational (β : ℝ) (hβ0 : 0 ≤ β)
    (hβd : β < 2*(Fintype.card ι:ℝ)) (N : ℕ) (hN : 1 ≤ N)
    (ν : Measure (PeriodicTorus ι)) [IsProbabilityMeasure ν]
    (hKL : klDiv ν (periodicHaar ι) ≠ ∞) :
    Integrable (periodicParticleExponent (ι := ι) β N) (Measure.pi fun _ : Fin N => ν) ∧
      (∫ x, periodicParticleExponent β N x ∂Measure.pi fun _ : Fin N => ν) ≤
        (N:ℝ)*(klDiv ν (periodicHaar ι)).toReal +
          Real.log (∫ x, Real.exp (periodicParticleExponent β N x)
            ∂Measure.pi fun _ : Fin N => periodicHaar ι) := by
  have hKLN := klDiv_pi_iid_ne_top ν (periodicHaar ι) N hKL
  obtain ⟨hi, hp, -⟩ := DGRHS.Entropy.entropy_two_signs_of_exponential
    (Measure.pi fun _ : Fin N => periodicHaar ι) (Measure.pi fun _ : Fin N => ν)
    (periodicParticleExponent (ι := ι) β N)
    (periodicParticleExponent_measurable β N).stronglyMeasurable
    (periodicParticleDensity_integrable_upper β hβ0 hβd N hN).1
    (periodicParticleExponent_neg_exp_integrable β hβ0 N) hKLN
  refine ⟨hi, ?_⟩
  rw [klDiv_pi_iid_toReal] at hp
  exact hp

/-- The literal two-particle exponent is half the inverse temperature times one
pair, using only the everywhere evenness of the chosen representative. -/
lemma periodicParticleExponent_two (β : ℝ) (x : Fin 2 → PeriodicTorus ι) :
    periodicParticleExponent β 2 x = β/2 * periodicLogKernel (x 0 - x 1) := by
  have h10 : x 1 - x 0 = -(x 0 - x 1) := (neg_sub (x 0) (x 1)).symm
  unfold periodicParticleExponent
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two,
    if_pos rfl, if_neg (by decide : (0:Fin 2) ≠ 1), if_neg (by decide : (1:Fin 2) ≠ 0),
    if_pos rfl, h10, periodicLogKernel_even]
  push_cast
  ring

/-- Proper pair energy of every finite-KL law, derived at N = 2 for one fixed
positive subcollision temperature. -/
theorem periodicGreen_pair_integrable_of_finite_klDiv (β : ℝ) (hβ : 0 < β)
    (hβd : β < 2*(Fintype.card ι:ℝ))
    (ν : Measure (PeriodicTorus ι)) [IsProbabilityMeasure ν]
    (hKL : klDiv ν (periodicHaar ι) ≠ ∞) :
    Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (p.1 - p.2))
      (ν.prod ν) := by
  have hi2 := (periodicParticle_entropy_variational β hβ.le hβd 2 (by norm_num) ν hKL).1
  have hb : β/2 ≠ 0 := (div_pos hβ two_pos).ne'
  have hg2 : Integrable (fun x : Fin 2 → PeriodicTorus ι => periodicLogKernel (x 0 - x 1))
      (Measure.pi fun _ : Fin 2 => ν) := by
    refine (hi2.const_mul (β/2)⁻¹).congr (Eventually.of_forall fun x => ?_)
    change (β/2)⁻¹ * periodicParticleExponent β 2 x = periodicLogKernel (x 0 - x 1)
    rw [periodicParticleExponent_two, inv_mul_cancel_left₀ hb]
  have he := (measurePreserving_finTwoArrow ν).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)
    (g := fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (p.1 - p.2))
  exact he.mp hg2

/-- Exact finite-N iid inequality with the literal coefficient `β (N-1)/2`. -/
theorem periodicParticle_pair_energy_bound (β : ℝ) (hβ : 0 < β)
    (hβd : β < 2*(Fintype.card ι:ℝ)) (N : ℕ) (hN : 1 ≤ N)
    (ν : Measure (PeriodicTorus ι)) [IsProbabilityMeasure ν]
    (hKL : klDiv ν (periodicHaar ι) ≠ ∞) :
    β/(2*(N:ℝ))*((N:ℝ)*((N:ℝ)-1)*
        (∫ p, periodicLogKernel (p.1 - p.2) ∂ν.prod ν)) ≤
      (N:ℝ)*(klDiv ν (periodicHaar ι)).toReal +
        Real.log (∫ x, Real.exp (periodicParticleExponent β N x)
          ∂Measure.pi fun _ : Fin N => periodicHaar ι) := by
  have hH := periodicGreen_pair_integrable_of_finite_klDiv β hβ hβd ν hKL
  have hmean := (iid_offdiagonal_sum_mean ν
    (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (p.1 - p.2)) hH N).2
  have hv := (periodicParticle_entropy_variational β hβ.le hβd N hN ν hKL).2
  have hU : (∫ x, periodicParticleExponent β N x ∂Measure.pi fun _ : Fin N => ν) =
      β/(2*(N:ℝ))*((N:ℝ)*((N:ℝ)-1)*(∫ p, periodicLogKernel (p.1 - p.2) ∂ν.prod ν)) := by
    unfold periodicParticleExponent
    rw [integral_const_mul]
    exact congrArg (fun a : ℝ => β/(2*(N:ℝ))*a) hmean
  rw [hU] at hv
  exact hv

end DGRHS.Periodic
