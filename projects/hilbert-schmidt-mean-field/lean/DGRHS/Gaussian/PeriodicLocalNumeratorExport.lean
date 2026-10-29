import DGRHS.Gaussian.PeriodicRieszTransportGibbs
import DGRHS.Gaussian.PeriodicLogTransportMoments

/-!
Packet P11a, unit 1: Lemma 7.2 (`lem:localNumeratorComm`, TeX 3307-3318) on the flat torus
(Remark 2.1, TeX 492-496), both kernels, in the exact shape of the Euclidean exports
`exists_sourceRieszTransport_local_numerator` and `exists_sourceLogTransport_local_numerator`.

* Riesz `0 < s < d/2`: `Csr` is the torus profile constant `periodicRieszProfileC`, the coefficient
  is the printed `γ/(4 C_{sr,n} K^n)`, the bound is the printed `e + L` with
  `L = glzUniversalTailConstant`, and `β_loc` is `periodicRieszLocalBeta s hs2 M`.
* LOG: the bound is `e` (as in the Euclidean LOG export), `β_loc` depends on the density through the
  `β = 1` partition bound; the exponent is `-γ N F_N + σ ε N A_n` with the smooth torus
  representatives of the kernel.  The Euclidean hypotheses `0 < d` (instance `[Nonempty ι]`) and the
  pair integrability `eq:logEnergyAssumption` are automatic on the torus and are not assumed.

`K` is a Lipschitz constant of `v` for the sup torus metric, in place of `‖∇v‖_{L^∞}`
(Remark A.1, TeX 4166-4172).
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Lemma 7.2 on the torus, positive Riesz kernel `0 < s < d/2`, printed bound `e + L`. -/
theorem exists_periodicRieszTransport_local_numerator (n : ℕ) (hn : 0 < n) (s : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    ∃ Csr : ℝ, 0 < Csr ∧ ∀ {K : ℝ≥0} {v : PeriodicTorus ι → E}, LipschitzWith K v →
      0 < (K : ℝ) →
      ∀ (ρ : PeriodicTorus ι → ℝ) (M : ℝ), 0 ≤ M →
      ∀ [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      ∃ βloc : ℝ, 0 < βloc ∧ ∀ γ : ℝ, 0 ≤ γ → γ ≤ βloc →
      ∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 0 < N →
      Integrable (fun x : Fin N → PeriodicTorus ι =>
        Real.exp (σ * (γ / (4 * Csr * (K : ℝ) ^ n)) *
            ((N : ℝ) * periodicRieszTransportEnergy s n v ρ N x) +
          periodicRieszParticleExponent s ρ γ N x))
        (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
      (∫ x : Fin N → PeriodicTorus ι,
        Real.exp (σ * (γ / (4 * Csr * (K : ℝ) ^ n)) *
            ((N : ℝ) * periodicRieszTransportEnergy s n v ρ N x) +
          periodicRieszParticleExponent s ρ γ N x)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤
          Real.exp 1 + glzUniversalTailConstant := by
  have hn1 : 1 ≤ n := hn
  refine ⟨periodicRieszProfileC ι s n,
    by linarith [(periodicRieszProfileC_ge (ι := ι) s hs n).2.2], ?_⟩
  intro K v hv hK ρ M hM hprob hρ
  have hloc := (periodicRieszLocalBeta_properties (ι := ι) s hs hs2 M hM).1
  refine ⟨periodicRieszLocalBeta s hs2 M, hloc, ?_⟩
  intro γ hγ hγb σ hσ N hN
  have hL := glzUniversalTailConstant_pos
  have hexp : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  rcases hγ.eq_or_lt with h0 | hpos
  · subst h0
    have hz : (fun x : Fin N → PeriodicTorus ι =>
        Real.exp (σ * ((0 : ℝ) / (4 * periodicRieszProfileC ι s n * (K : ℝ) ^ n)) *
            ((N : ℝ) * periodicRieszTransportEnergy s n v ρ N x) +
          periodicRieszParticleExponent s ρ 0 N x)) = fun _ => 1 := by
      funext x
      simp [periodicRieszParticleExponent]
    rw [hz]
    refine ⟨integrable_const 1, ?_⟩
    have h1 : (∫ _x : Fin N → PeriodicTorus ι, (1 : ℝ)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) = 1 := by simp
    rw [h1]
    linarith
  · obtain ⟨hi, hb⟩ := periodicRieszLocal_numerator s n hn1 hs hs2 γ σ hpos hσ.le hv ρ M hM hρ N
      hN hγb
    have he : (fun x : Fin N → PeriodicTorus ι =>
        Real.exp (σ * (γ / (4 * periodicRieszProfileC ι s n * (K : ℝ) ^ n)) *
            ((N : ℝ) * periodicRieszTransportEnergy s n v ρ N x) +
          periodicRieszParticleExponent s ρ γ N x)) =
        fun x => Real.exp (periodicRieszNumeratorExponent s n γ σ K v ρ N x) := by
      funext x
      congr 1
      unfold periodicRieszNumeratorExponent periodicRieszCoefficient
      ring
    rw [he]
    exact ⟨hi, hb⟩

/-- Lemma 7.2 on the torus, LOG kernel, bound `e`. -/
theorem exists_periodicLogTransport_local_numerator (n : ℕ) (hn : 0 < n) :
    ∃ Csr : ℝ, 0 < Csr ∧ ∀ {K : ℝ≥0} {v : PeriodicTorus ι → E}, LipschitzWith K v →
      0 < (K : ℝ) →
      ∀ (ρ : PeriodicTorus ι → ℝ) (M : ℝ), 0 ≤ M →
      ∀ [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      ∃ βloc : ℝ, 0 < βloc ∧ ∀ γ : ℝ, 0 ≤ γ → γ ≤ βloc →
      ∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 0 < N →
      Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (periodicLogParticleExponent ρ γ N x +
          (σ * (γ / (4 * Csr * (K : ℝ) ^ n))) * periodicLogA ρ n v N x))
        (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
      (∫ x : Fin N → PeriodicTorus ι, Real.exp (periodicLogParticleExponent ρ γ N x +
          (σ * (γ / (4 * Csr * (K : ℝ) ^ n))) * periodicLogA ρ n v N x)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ Real.exp 1 :=
  periodicLog_local_numerator n hn

end DGRHS.Periodic
#print axioms DGRHS.Periodic.exists_periodicRieszTransport_local_numerator
#print axioms DGRHS.Periodic.exists_periodicLogTransport_local_numerator
