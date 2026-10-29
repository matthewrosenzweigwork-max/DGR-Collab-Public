/- Physical logarithmic entropic commutator, using the actual contracted
derivative and collision free energy for every probability competitor.
K denotes a verified global Lipschitz bound; no unproved identification
with a weak-gradient essential supremum is used. -/
import DGRHS.Commutator.SourceLogTransportAllLaws
import DGRHS.Commutator.SourceLogTransportGibbsMoments
import DGRHS.Entropy.SourceLogEntropicAllLaws
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy
variable {ι : Type*} [Fintype ι]

theorem exists_sourceLog_entropic_commutator (n : ℕ) (hn : 0 < n) :
    ∃ Csr : ℝ, 0 < Csr ∧ ∀ {K : ℝ≥0}
      {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}, LipschitzWith K v →
      0 < (K : ℝ) → 0 < (Fintype.card ι : ℝ) →
      ∀ (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ), 0 ≤ M →
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume, ρ x ≤ M) →
      Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
        (gaussianRieszDensityMeasure ρ)) →
      ∃ βloc : ℝ, 0 < βloc ∧ ∀ β : ℝ≥0, 0 < (β : ℝ) →
      ∃ Cub Cpf : ℝ, 1 ≤ Cub ∧ 1 ≤ Cpf ∧
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
  obtain ⟨Csr, hC, hfactory⟩ := exists_sourceLogTransport_gibbs_moments (ι := ι) n hn
  refine ⟨Csr, hC, ?_⟩
  intro K v hv hK hd ρ M hM hμ hρ hpair
  obtain ⟨βloc, hloc, hβfactory⟩ := hfactory hv hK hd ρ M hM hρ hpair
  refine ⟨βloc, hloc, ?_⟩
  intro β hβ
  obtain ⟨Cub, hCub, hremaining, hmom⟩ := hβfactory β hβ
  obtain ⟨Cpf, hCpf, hcap⟩ := sourceLogPartition_original_bounds_one_le β hd ρ M hM hρ hpair
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
  refine ⟨Cub, Cpf, hCub, hCpf, hremaining, hε, hCem, hcap, hforcing, hmom, ?_⟩
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

/-- Zero Lipschitz seminorm: actual observable is zero and every positive
epsilon is admissible, with Cem=1 and the genuine infinite-entropy branch. -/
theorem sourceLog_entropic_commutator_zero (n : ℕ) (hn : 0 < n)
    {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hv : LipschitzWith 0 v)
    (β : ℝ≥0) (hβ : 0 < (β : ℝ)) (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
      (gaussianRieszDensityMeasure ρ))) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cpf : ℝ, 1 ≤ Cpf ∧ ∀ N : ℕ, 1 ≤ N →
      (∀ σ : ℝ, Integrable (fun x => Real.exp (σ * ε * ((N : ℝ) *
        sourceTransportEnergy (gaussianRieszDensityMeasure ρ) (sourceLogTransportKernel n v) N x)))
        (sourceLogSingularGibbs β ρ N) ∧
        (∫ x, Real.exp (σ * ε * ((N : ℝ) * sourceTransportEnergy (gaussianRieszDensityMeasure ρ)
          (sourceLogTransportKernel n v) N x)) ∂sourceLogSingularGibbs β ρ N) = 1) ∧
      ∀ (ν : Measure (Fin N → EuclideanSpace ℝ ι)) [IsProbabilityMeasure ν],
      Integrable (fun x => (N : ℝ) * sourceTransportEnergy (gaussianRieszDensityMeasure ρ)
        (sourceLogTransportKernel n v) N x) ν ∧
      ((|∫ x, (N : ℝ) * sourceTransportEnergy (gaussianRieszDensityMeasure ρ)
        (sourceLogTransportKernel n v) N x ∂ν| : ℝ) : EReal) ≤
        (((β : ℝ)/ε)*(N : ℝ) : ℝ) * sourceLogCollisionFreeEnergy β ρ M N ν +
          (ε⁻¹ * (Real.log Cpf + Real.log 1) : ℝ) := by
  obtain ⟨Cpf, hCpf, hcap⟩ := sourceLogPartition_original_bounds_one_le β hd ρ M hM hρ hpair
  refine ⟨Cpf, hCpf, ?_⟩
  intro N hN
  let μ := gaussianRieszDensityMeasure ρ
  let a := fun x : Fin N → EuclideanSpace ℝ ι =>
    (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x
  have ha0 : a = fun _ => 0 := by
    funext x
    simp only [a, sourceTransportEnergy_zero_lipschitz μ n hn hv, mul_zero]
  have hQ : IsProbabilityMeasure (sourceLogSingularGibbs β ρ N) :=
    sourceLogSingularGibbs_probability β hd ρ M hM hρ hpair N
  have hmom (σ : ℝ) : Integrable (fun x => Real.exp (σ * ε * a x))
      (sourceLogSingularGibbs β ρ N) ∧
      (∫ x, Real.exp (σ * ε * a x) ∂sourceLogSingularGibbs β ρ N) = 1 := by
    rw [ha0]
    simp
  refine ⟨hmom, ?_⟩
  intro ν hν
  have hstrong : StronglyMeasurable a := by rw [ha0]; exact stronglyMeasurable_const
  have hbound : ∀ x, |a x| ≤ 0 := by simp [ha0]
  have hp := hmom 1
  have hm := hmom (-1)
  exact sourceLog_entropic_collision_all_laws β hβ hd ρ M hM hρ hpair N hN ν a hstrong
    0 hbound ε hε (by simpa only [one_mul] using hp.1)
    (by simpa only [neg_one_mul, neg_mul, one_mul] using hm.1) Cpf 1 (hcap N hN).2
    (by simpa only [one_mul] using hp.2.le) (by simpa only [neg_one_mul, neg_mul, one_mul] using hm.2.le)

end DGRHS.Commutator
#check @DGRHS.Commutator.exists_sourceLog_entropic_commutator
#check @DGRHS.Commutator.sourceLog_entropic_commutator_zero
#print axioms DGRHS.Commutator.exists_sourceLog_entropic_commutator
#print axioms DGRHS.Commutator.sourceLog_entropic_commutator_zero
