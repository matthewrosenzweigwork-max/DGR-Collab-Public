/- Actual uniform logarithmic entropic commutators. All constants are
chosen before the velocity, density, particle number and competitor.
The common interaction-energy lower bound retains its exact prefactor. -/
import DGRHS.Commutator.SourceLogFamilyGibbsMoments
import DGRHS.Commutator.SourceLogTransportAllLaws
import DGRHS.Entropy.SourceLogEntropicAllLaws
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy
variable {ι : Type*} [Fintype ι]

theorem exists_log_transport_family_entropic_commutator (n : ℕ) (hn : 0 < n) :
    ∃ Csr : ℝ, 0 < Csr ∧ ∀ K : ℝ≥0, 0 < (K : ℝ) →
      ∀ M : ℝ, 0 ≤ M → 0 < (Fintype.card ι : ℝ) →
      ∃ βloc : ℝ, 0 < βloc ∧ ∀ β : ℝ≥0, 0 < (β : ℝ) → ∀ J : ℝ,
      ∃ Cub Cpf : ℝ, 1 ≤ Cub ∧ 1 ≤ Cpf ∧
      let ε := sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ)^n)
      let Cem := sourceLogTransportCem (β : ℝ) βloc (-J)
        DGRHS.Concentration.glzUniversalTailConstant Cub
      0 < ε ∧ 0 < Cem ∧ 0 ≤ Real.log Cpf + Real.log Cem ∧
      ∀ v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι, LipschitzWith K v →
      ∀ ρ : EuclideanSpace ℝ ι → ℝ,
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume, ρ x ≤ M) →
      Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
        (gaussianRieszDensityMeasure ρ)) →
      -J ≤ DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
        (fun a b => logPhysicalPair (a,b)) →
      ∀ N : ℕ, 1 ≤ N → ∀ (ν : Measure (Fin N → EuclideanSpace ℝ ι))
        [IsProbabilityMeasure ν],
      Integrable (fun x => (N : ℝ)*sourceTransportEnergy
        (gaussianRieszDensityMeasure ρ) (sourceLogTransportKernel n v) N x) ν ∧
      ((|∫ x, (N : ℝ)*sourceTransportEnergy (gaussianRieszDensityMeasure ρ)
        (sourceLogTransportKernel n v) N x ∂ν| : ℝ) : EReal) ≤
        (((β : ℝ)/ε)*(N : ℝ) : ℝ)*sourceLogCollisionFreeEnergy β ρ M N ν +
          (ε⁻¹*(Real.log Cpf+Real.log Cem) : ℝ) := by
  obtain ⟨Csr, hC, hfactory⟩ := exists_log_transport_family_gibbs_moments (ι := ι) n hn
  refine ⟨Csr, hC, ?_⟩
  intro K hK M hM hd
  obtain ⟨βloc, hloc, hβfactory⟩ := hfactory K hK M hM hd
  refine ⟨βloc, hloc, ?_⟩
  intro β hβ J
  obtain ⟨Cub, Cpf, hCub, hCpf, hε, hCem, hforcing, hfamily⟩ := hβfactory β hβ J
  refine ⟨Cub, Cpf, hCub, hCpf, hε, hCem, hforcing, ?_⟩
  intro v hv ρ hμ hρ hpair hI N hN ν hν
  obtain ⟨hcap, hmom⟩ := hfamily v hv ρ hρ hpair hI
  obtain ⟨ha, A, hA, _⟩ := sourceLogTransport_all_law_proper n hn hv
    (gaussianRieszDensityMeasure ρ) N (by omega)
  have hp := hmom 1 (by norm_num) N hN
  have hm := hmom (-1) (by norm_num) N hN
  exact sourceLog_entropic_collision_all_laws β hβ hd ρ M hM hρ hpair N hN ν
    (fun x => (N : ℝ)*sourceTransportEnergy (gaussianRieszDensityMeasure ρ)
      (sourceLogTransportKernel n v) N x) ha A hA
    (sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ)^n)) hε
    (by simpa only [one_mul] using hp.1)
    (by simpa only [neg_one_mul, neg_mul, one_mul] using hm.1)
    Cpf (sourceLogTransportCem (β : ℝ) βloc (-J)
      DGRHS.Concentration.glzUniversalTailConstant Cub) (hcap N hN)
    (by simpa only [one_mul] using hp.2)
    (by simpa only [neg_one_mul, neg_mul, one_mul] using hm.2)

end DGRHS.Commutator
#check @DGRHS.Commutator.exists_log_transport_family_entropic_commutator
#print axioms DGRHS.Commutator.exists_log_transport_family_entropic_commutator
