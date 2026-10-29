import DGRHS.Commutator.SourceLogGaussianCommonControl
import DGRHS.Commutator.SourceLogEntropicCommutator

/-! The same checked Gaussian short/long/centering coefficient is used in
local Gibbs moments and the physical all-law entropic estimate. The named
source partition constant is literally max(exp 1, Cpart), with Cpart a
uniform actual partition bound. Background-family uniformity, weak-gradient
identification and the complete Appendix layer-cake recipe remain separate. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy
variable {ι : Type*} [Fintype ι]

theorem exists_sourceLogGaussian_common_named_entropic_commutator (n : ℕ) (hn : 0 < n) :
    ∃ Csr : ℝ, 0 < Csr ∧
      (∀ (η : ℝ), 0 < η → ∀ {K : ℝ≥0}
        {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}, LipschitzWith K v → ∀ p,
        |sourceLogGaussianShortTransportKernel n η v p| ≤
          Csr * (K : ℝ)^n * gaussianLogShortRange (2 * η) (p.1 - p.2)) ∧
      (∀ (η : ℝ), 0 < η → ∀ (K : ℝ≥0)
        (v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι), LipschitzWith K v → ∀ p,
        |sourceLogGaussianLongTransportKernel n η v p| ≤ Csr * (K : ℝ)^n) ∧
      (∀ (η : ℝ), 0 < η → 0 < (Fintype.card ι : ℝ) → ∀ {K : ℝ≥0}
        {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}, LipschitzWith K v →
        ∀ (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ), 0 ≤ M →
        ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
        (∀ᵐ x ∂volume, ρ x ≤ M) → ∀ p,
        |hoeffdingCentered (gaussianRieszDensityMeasure ρ)
          (sourceLogGaussianShortTransportKernel n η v) p| ≤
          Csr * (K : ℝ)^n *
            (gaussianLogShortRange (2 * η) (p.1 - p.2) + M * η^(Fintype.card ι : ℝ))) ∧
      ∀ {K : ℝ≥0}
      {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}, LipschitzWith K v →
      0 < (K : ℝ) → 0 < (Fintype.card ι : ℝ) →
      ∀ (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ), 0 ≤ M →
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume, ρ x ≤ M) →
      Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
        (gaussianRieszDensityMeasure ρ)) →
      ∃ βloc : ℝ, 0 < βloc ∧ ∀ β : ℝ≥0, 0 < (β : ℝ) →
      ∃ Cub Cpart Cpf : ℝ, 1 ≤ Cub ∧ 1 ≤ Cpart ∧
      Cpf = max (Real.exp 1) Cpart ∧ 1 ≤ Cpf ∧
      (∀ N : ℕ, 1 ≤ N → (sourceLogSingularPartition β ρ N).toReal ≤ Cpart) ∧
      (∀ N : ℕ, 1 ≤ N → ∀ hlarge : βloc < (β : ℝ),
        (sourceLogSingularPartition
          (⟨2*(β : ℝ)-βloc, by linarith [hlarge, β.coe_nonneg]⟩ : ℝ≥0) ρ N).toReal ≤ Cub) ∧
      let μ := gaussianRieszDensityMeasure ρ
      let I := DGRHS.interactionEnergy μ (fun a b => logPhysicalPair (a,b))
      let ε := sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ)^n)
      let Cem := sourceLogTransportCem (β : ℝ) βloc I
        DGRHS.Concentration.glzUniversalTailConstant Cub
      0 < ε ∧ 0 < Cem ∧
      (∀ N : ℕ, 1 ≤ N → Real.exp ((β : ℝ)*I) ≤
        (sourceLogSingularPartition β ρ N).toReal ∧
        (sourceLogSingularPartition β ρ N).toReal ≤ Cpf) ∧
      0 ≤ Real.log Cpf + Real.log Cem ∧
      (∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x => Real.exp (σ * ε * ((N : ℝ) *
          sourceTransportEnergy μ (sourceLogTransportKernel n v) N x)))
          (sourceLogSingularGibbs β ρ N) ∧
        (∫ x, Real.exp (σ * ε * ((N : ℝ) * sourceTransportEnergy μ
          (sourceLogTransportKernel n v) N x)) ∂sourceLogSingularGibbs β ρ N) ≤ Cem) ∧
      ∀ N : ℕ, 1 ≤ N → ∀ (ν : Measure (Fin N → EuclideanSpace ℝ ι))
        [IsProbabilityMeasure ν],
      Integrable (fun x => (N : ℝ) * sourceTransportEnergy μ
        (sourceLogTransportKernel n v) N x) ν ∧
      ((|∫ x, (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x ∂ν| : ℝ) : EReal) ≤
        (((β : ℝ)/ε)*(N : ℝ) : ℝ) * sourceLogCollisionFreeEnergy β ρ M N ν +
          (ε⁻¹ * (Real.log Cpf + Real.log Cem) : ℝ) := by
  obtain ⟨Csr, hC, hshort, hlong, hcentered, hfactory⟩ :=
    exists_sourceLogGaussian_common_gibbs_moments (ι := ι) n hn
  refine ⟨Csr, hC, hshort, hlong, hcentered, ?_⟩
  intro K v hv hK hd ρ M hM hμ hρ hpair
  obtain ⟨βloc, hloc, hβfactory⟩ := hfactory hv hK hd ρ M hM hρ hpair
  refine ⟨βloc, hloc, ?_⟩
  intro β hβ
  obtain ⟨Cub, hCub, hremaining, hmom⟩ := hβfactory β hβ
  obtain ⟨Cpart, hCpart, hcapPart⟩ := sourceLogPartition_original_bounds_one_le β hd ρ M hM hρ hpair
  let Cpf := max (Real.exp 1) Cpart
  have hPartCpf : Cpart ≤ Cpf := le_max_right _ _
  have hCpf : 1 ≤ Cpf := hCpart.trans hPartCpf
  have hcap : ∀ N : ℕ, 1 ≤ N → Real.exp ((β : ℝ) *
      DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b))) ≤
      (sourceLogSingularPartition β ρ N).toReal ∧
      (sourceLogSingularPartition β ρ N).toReal ≤ Cpf := by
    intro N hN
    exact ⟨(hcapPart N hN).1, (hcapPart N hN).2.trans hPartCpf⟩
  let μ := gaussianRieszDensityMeasure ρ
  let I := DGRHS.interactionEnergy μ (fun a b => logPhysicalPair (a,b))
  let ε := sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ)^n)
  let Cem := sourceLogTransportCem (β : ℝ) βloc I
    DGRHS.Concentration.glzUniversalTailConstant Cub
  have hε : 0 < ε := sourceLogTransportEpsilon_pos _ _ _ _ hβ hloc hC (pow_pos hK n)
  have hL := DGRHS.Concentration.glzUniversalTailConstant_pos.le
  have hCem : 0 < Cem := sourceLogTransportCem_pos _ _ _ _ _ hL hCub
  have hJ : Real.exp ((β : ℝ)*I) ≤ Cpf := (hcap 1 le_rfl).1.trans (hcap 1 le_rfl).2
  have hforcing : 0 ≤ Real.log Cpf + Real.log Cem := by
    dsimp only [Cem, sourceLogTransportCem]
    split_ifs
    · simpa only [neg_mul] using log_small_Cem_forcing_nonnegative ((β : ℝ)*I) Cpf _ hJ hL
    · simpa only [neg_mul] using log_large_Cem_forcing_nonnegative ((β : ℝ)*I) Cpf _ Cub hJ hL hCub
  refine ⟨Cub, Cpart, Cpf, hCub, hCpart, rfl, hCpf,
    (fun N hN => (hcapPart N hN).2), hremaining, hε, hCem, hcap, hforcing, hmom, ?_⟩
  intro N hN ν hν
  obtain ⟨ha, A, hA, _⟩ := sourceLogTransport_all_law_proper n hn hv μ N (by omega)
  have hp := hmom 1 (by norm_num) N hN
  have hm := hmom (-1) (by norm_num) N hN
  have hp' : Integrable (fun x => Real.exp (ε * ((N : ℝ) * sourceTransportEnergy μ
      (sourceLogTransportKernel n v) N x))) (sourceLogSingularGibbs β ρ N) := by
    simpa only [one_mul] using hp.1
  have hm' : Integrable (fun x => Real.exp (-(ε * ((N : ℝ) * sourceTransportEnergy μ
      (sourceLogTransportKernel n v) N x)))) (sourceLogSingularGibbs β ρ N) := by
    simpa only [neg_one_mul, neg_mul, one_mul] using hm.1
  exact sourceLog_entropic_collision_all_laws β hβ hd ρ M hM hρ hpair N hN ν
    (fun x => (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x)
    ha A hA ε hε hp' hm' Cpf Cem (hcap N hN).2
      (by simpa only [one_mul] using hp.2) (by simpa only [neg_one_mul, neg_mul, one_mul] using hm.2)

end DGRHS.Commutator
