import DGRHS.Gaussian.PeriodicLogEntropicTransfer
import DGRHS.Entropy.SourceLogForcingNormalization
import DGRHS.Commutator.SourceLogTransportAllLaws

/-!
Packet P9h, unit 3 (LOG, final): Theorem 2.8 (`thm:entropicCommutator`, TeX 691-736) on the flat
torus (Remark 2.1, TeX 492-496), logarithmic branch, with the printed constants of Remark A.1
(`eq:CemLargeBetaDef`, TeX 4144-4156):
`C_em = e^{-β I_μ}(e + L)` for `β ≤ β_loc` and
`C_em = e^{-β I_μ} (e + L)^{1/2} C_ub(2β - β_loc, μ)^{1/2}` for `β > β_loc`,
with the printed piecewise transport parameter `ε_{β,n}`.

Torus version of `DGRHS.Commutator.exists_sourceLog_entropic_commutator`: same quantifier order,
every probability competitor `ν` (the extended free energy keeps `+∞`), and `K` a global Lipschitz
constant of `v` for the sup torus metric.
-/

noncomputable section
open MeasureTheory InformationTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration DGRHS.Entropy
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Theorem 2.8 (`thm:entropicCommutator`, TeX 691-736) on the torus, logarithmic branch, with the printed
constants of Remark A.1.  Every probability competitor `ν` is allowed: the free energy is the extended one
(value `⊤` where the printed `Er_N(f_N, μ)` is `+∞`) with the finite smooth representative of the torus pair
kernel, in place of the collision-gated form of the Euclidean export; this is equivalent to the printed
inequality `eq:entropicCommutatorEstimate` for every `f_N` (packet P9h review, section 5.2 (d)). -/
theorem exists_periodicLog_entropic_commutator (n : ℕ) (hn : 0 < n) :
    ∃ Csr : ℝ, 0 < Csr ∧ ∀ {K : ℝ≥0} {v : PeriodicTorus ι → E}, LipschitzWith K v →
      0 < (K : ℝ) →
      ∀ (ρ : PeriodicTorus ι → ℝ) (M : ℝ), 0 ≤ M →
      ∀ [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      ∃ βloc : ℝ, 0 < βloc ∧ ∀ β : ℝ≥0, 0 < (β : ℝ) →
      ∃ Cub Cpf : ℝ, 1 ≤ Cub ∧ 1 ≤ Cpf ∧
      (∀ N : ℕ, 1 ≤ N → βloc < (β : ℝ) →
        (periodicLogSingularPartition (2 * (β : ℝ) - βloc) ρ N).toReal ≤ Cub) ∧
      let μ := periodicCappedDensityMeasure ρ
      let I := DGRHS.interactionEnergy μ (fun a b : PeriodicTorus ι => periodicLogKernel (a - b))
      let ε := sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ n)
      let Cem := sourceLogTransportCem (β : ℝ) βloc I glzUniversalTailConstant Cub
      0 < ε ∧ 0 < Cem ∧
      (∀ N : ℕ, 1 ≤ N → Real.exp ((β : ℝ) * I) ≤ (periodicLogSingularPartition (β : ℝ) ρ N).toReal ∧
        (periodicLogSingularPartition (β : ℝ) ρ N).toReal ≤ Cpf) ∧
      0 ≤ Real.log Cpf + Real.log Cem ∧
      (∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x => Real.exp (σ * ε * ((N : ℝ) *
          sourceTransportEnergy μ (periodicLogTransportKernel n v) N x)))
          (periodicLogSingularGibbs (β : ℝ) ρ N) ∧
        (∫ x, Real.exp (σ * ε * ((N : ℝ) * sourceTransportEnergy μ
          (periodicLogTransportKernel n v) N x)) ∂periodicLogSingularGibbs (β : ℝ) ρ N) ≤ Cem) ∧
      ∀ N : ℕ, 1 ≤ N → ∀ (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν],
      Integrable (fun x => (N : ℝ) * sourceTransportEnergy μ
        (periodicLogTransportKernel n v) N x) ν ∧
      ((|∫ x, (N : ℝ) * sourceTransportEnergy μ (periodicLogTransportKernel n v) N x ∂ν| : ℝ) :
        EReal) ≤ (((β : ℝ) / ε * (N : ℝ) : ℝ) : EReal) *
            periodicLogTransportExtendedFreeEnergy ρ M (β : ℝ) N ν +
          ((ε⁻¹ * (Real.log Cpf + Real.log Cem) : ℝ) : EReal) := by
  have hn1 : 1 ≤ n := hn
  obtain ⟨Csr, hC, hfactory⟩ := periodicLog_gibbs_moments (ι := ι) n hn1
  obtain ⟨CK, hCK, hbd⟩ := periodicLogTransportKernel_bound (ι := ι) n hn1
  refine ⟨Csr, hC, ?_⟩
  intro K v hv hK ρ M hM hprob hρ
  obtain ⟨βloc, hloc, hβfactory⟩ := hfactory hv hK ρ M hM hρ
  refine ⟨βloc, hloc, ?_⟩
  intro β hβ
  obtain ⟨Cub, hCub, hremaining, hmom⟩ := hβfactory β hβ
  have hβ' : 0 < (β : ℝ) := hβ
  obtain ⟨Cp, hCp, hPf⟩ := periodicLogParticleWeight_uniform (β : ℝ) β.coe_nonneg ρ M hM hρ
  let μ := periodicCappedDensityMeasure ρ
  let I := DGRHS.interactionEnergy μ (fun a b : PeriodicTorus ι => periodicLogKernel (a - b))
  let ε := sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ n)
  let Cem := sourceLogTransportCem (β : ℝ) βloc I glzUniversalTailConstant Cub
  let Cpf := max Cp 1
  have hε : 0 < ε := sourceLogTransportEpsilon_pos _ _ _ _ hβ' hloc hC (pow_pos hK n)
  have hL := glzUniversalTailConstant_pos.le
  have hCem : 0 < Cem := sourceLogTransportCem_pos _ _ _ _ _ hL hCub
  have hcap : ∀ N : ℕ, 1 ≤ N → Real.exp ((β : ℝ) * I) ≤
      (periodicLogSingularPartition (β : ℝ) ρ N).toReal ∧
      (periodicLogSingularPartition (β : ℝ) ρ N).toReal ≤ Cpf := by
    intro N hN
    rw [periodicLogSingularPartition_toReal_eq (β : ℝ) β.coe_nonneg ρ M hM hρ N hN]
    have h := hPf N hN
    exact ⟨h.2.1, h.2.2.trans (le_max_left _ _)⟩
  have hJ : Real.exp ((β : ℝ) * I) ≤ Cpf := (hcap 1 le_rfl).1.trans (hcap 1 le_rfl).2
  have hforcing : 0 ≤ Real.log Cpf + Real.log Cem := by
    dsimp only [Cem, sourceLogTransportCem]
    split_ifs
    · simpa only [neg_mul] using log_small_Cem_forcing_nonnegative ((β : ℝ) * I) Cpf _ hJ hL
    · simpa only [neg_mul] using
        log_large_Cem_forcing_nonnegative ((β : ℝ) * I) Cpf _ Cub hJ hL hCub
  refine ⟨Cub, Cpf, hCub, le_max_right _ _, hremaining, hε, hCem, hcap, hforcing, hmom, ?_⟩
  intro N hN ν hν
  have hn' : 0 < N := by omega
  have hm := periodicLogTransportKernel_measurable (ι := ι) n hv
  have hsa : StronglyMeasurable (fun x : Fin N → PeriodicTorus ι => (N : ℝ) *
      sourceTransportEnergy μ (periodicLogTransportKernel n v) N x) :=
    (stronglyMeasurable_sourceTransportEnergy μ _ hm N).const_mul (N : ℝ)
  let A := (N : ℝ) * (4 * (CK * (K : ℝ) ^ n))
  have hA : ∀ x : Fin N → PeriodicTorus ι, |(N : ℝ) * sourceTransportEnergy μ
      (periodicLogTransportKernel n v) N x| ≤ A := by
    intro x
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
    exact abs_sourceTransportEnergy_le μ _ hm _ (hbd hv)
      (fun a b => (periodicLogTransportKernel_symm n v (a, b)).symm)
      (fun a => by simp [periodicLogTransportKernel]) N hn' x
  have hp := hmom 1 (by norm_num) N hN
  have hmn := hmom (-1) (by norm_num) N hN
  have hp' : Integrable (fun x => Real.exp (ε * ((N : ℝ) * sourceTransportEnergy μ
      (periodicLogTransportKernel n v) N x))) (periodicLogSingularGibbs (β : ℝ) ρ N) := by
    simpa only [one_mul] using hp.1
  have hm' : Integrable (fun x => Real.exp (-(ε * ((N : ℝ) * sourceTransportEnergy μ
      (periodicLogTransportKernel n v) N x)))) (periodicLogSingularGibbs (β : ℝ) ρ N) := by
    simpa only [neg_one_mul, neg_mul, one_mul] using hmn.1
  exact periodicLog_entropic_all_laws M hM (β : ℝ) hβ' ρ hρ N hN ν
    (fun x => (N : ℝ) * sourceTransportEnergy μ (periodicLogTransportKernel n v) N x) hsa A hA ε hε
    hp' hm' Cpf Cem (hcap N hN).2 (by simpa only [one_mul] using hp.2)
    (by simpa only [neg_one_mul, neg_mul, one_mul] using hmn.2)

end DGRHS.Periodic
#print axioms DGRHS.Periodic.exists_periodicLog_entropic_commutator
