import DGRHS.Commutator.SourceLogGaussianNamedEntropic
import DGRHS.Commutator.SourceLogFamilyEntropicCommutator

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy
variable {ι : Type*} [Fintype ι]

/-- Exact two-endpoint interpolation on an arbitrary measure. -/
private lemma commonCsr_signed_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → ℝ)
    (β βloc Cold Cnew L Cem : ℝ) (hβ : 0 < β) (hloc : 0 < βloc)
    (hCold : 0 < Cold) (hC : Cold ≤ Cnew) (hL : 0 < L)
    (hmom : ∀ σ : ℝ, |σ| = 1 →
      Integrable (fun x => Real.exp (σ * sourceLogTransportEpsilon β βloc Cold L * a x)) P ∧
      (∫ x, Real.exp (σ * sourceLogTransportEpsilon β βloc Cold L * a x) ∂P) ≤ Cem) :
    ∀ σ : ℝ, |σ| = 1 →
      Integrable (fun x => Real.exp (σ * sourceLogTransportEpsilon β βloc Cnew L * a x)) P ∧
      (∫ x, Real.exp (σ * sourceLogTransportEpsilon β βloc Cnew L * a x) ∂P) ≤ Cem := by
  have hCnew : 0 < Cnew := hCold.trans_le hC
  have heps := sourceLogTransportEpsilon_pos β βloc Cold L hβ hloc hCold hL
  have hdelta := sourceLogTransportEpsilon_pos β βloc Cnew L hβ hloc hCnew hL
  have hle : sourceLogTransportEpsilon β βloc Cnew L ≤
      sourceLogTransportEpsilon β βloc Cold L := by
    unfold sourceLogTransportEpsilon
    split_ifs
    · exact div_le_div_of_nonneg_left hβ.le (by positivity)
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 4)) hL.le)
    · exact div_le_div_of_nonneg_left hloc.le (by positivity)
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 8)) hL.le)
  have hm := hmom (-1) (by norm_num)
  have hp := hmom 1 (by norm_num)
  intro σ hσ
  have ht : |σ * sourceLogTransportEpsilon β βloc Cnew L| ≤
      sourceLogTransportEpsilon β βloc Cold L := by
    rw [abs_mul, hσ, one_mul, abs_of_pos hdelta]
    exact hle
  simpa only [zero_add] using
    smaller_parameter_numerator P (fun _ => 0) a
      (sourceLogTransportEpsilon β βloc Cold L) heps Cem
      (by simpa only [zero_sub, neg_one_mul, neg_mul, one_mul] using hm.1)
      (by simpa only [zero_add, one_mul] using hp.1)
      (by simpa only [zero_sub, neg_one_mul, neg_mul, one_mul] using hm.2)
      (by simpa only [zero_add, one_mul] using hp.2)
      (σ * sourceLogTransportEpsilon β βloc Cnew L) ht

abbrev SourceLogFamilyAt (n : ℕ) (Csr : ℝ) : Prop :=
    0 < Csr ∧ ∀ K : ℝ≥0, 0 < (K : ℝ) →
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
          (ε⁻¹*(Real.log Cpf+Real.log Cem) : ℝ)

abbrev SourceLogNamedAt (n : ℕ) (Csr : ℝ) : Prop :=
    0 < Csr ∧
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
          (ε⁻¹ * (Real.log Cpf + Real.log Cem) : ℝ)

theorem exists_sourceLog_common_named_family_entropic_commutator (n : ℕ) (hn : 0 < n) :
    ∃ Csr : ℝ, 0 < Csr ∧ SourceLogFamilyAt (ι := ι) n Csr ∧
      SourceLogNamedAt (ι := ι) n Csr := by
  obtain ⟨Cnamed, hCn, hshort, hlong, hcentered, hnamed⟩ :=
    exists_sourceLogGaussian_common_named_entropic_commutator (ι := ι) n hn
  obtain ⟨Cfamily, hCf, hfamily⟩ :=
    exists_log_transport_family_gibbs_moments (ι := ι) n hn
  let Csr := max Cnamed Cfamily
  have hC : 0 < Csr := hCn.trans_le (le_max_left _ _)
  have hnC : Cnamed ≤ Csr := le_max_left _ _
  have hfC : Cfamily ≤ Csr := le_max_right _ _
  refine ⟨Csr, hC, ?_, ?_⟩
  · refine ⟨hC, ?_⟩
    intro K hK M hM hd
    obtain ⟨βloc, hloc, hβfamily⟩ := hfamily K hK M hM hd
    refine ⟨βloc, hloc, ?_⟩
    intro β hβ J
    obtain ⟨Cub, Cpf, hCub, hCpf, hepsOld, hCem, hforcing, hdata⟩ := hβfamily β hβ J
    have heps := sourceLogTransportEpsilon_pos (β : ℝ) βloc Csr ((K : ℝ)^n)
      hβ hloc hC (pow_pos hK n)
    refine ⟨Cub, Cpf, hCub, hCpf, heps, hCem, hforcing, ?_⟩
    intro v hv ρ hμ hρ hpair hI N hN ν hν
    obtain ⟨hcap, hmom⟩ := hdata v hv ρ hρ hpair hI
    let a := fun x : Fin N → EuclideanSpace ℝ ι =>
      (N : ℝ) * sourceTransportEnergy (gaussianRieszDensityMeasure ρ)
        (sourceLogTransportKernel n v) N x
    have hnew := commonCsr_signed_moments (sourceLogSingularGibbs β ρ N) a
      (β : ℝ) βloc Cfamily Csr ((K : ℝ)^n)
      (sourceLogTransportCem (β : ℝ) βloc (-J)
        DGRHS.Concentration.glzUniversalTailConstant Cub)
      hβ hloc hCf hfC (pow_pos hK n) (fun σ hσ => hmom σ hσ N hN)
    have hp := hnew 1 (by norm_num)
    have hm := hnew (-1) (by norm_num)
    obtain ⟨ha, A, hA, _⟩ := sourceLogTransport_all_law_proper n hn hv
      (gaussianRieszDensityMeasure ρ) N (by omega)
    exact sourceLog_entropic_collision_all_laws β hβ hd ρ M hM hρ hpair N hN ν
      a ha A hA (sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ)^n)) heps
      (by simpa only [one_mul] using hp.1)
      (by simpa only [neg_one_mul, neg_mul, one_mul] using hm.1)
      Cpf (sourceLogTransportCem (β : ℝ) βloc (-J)
        DGRHS.Concentration.glzUniversalTailConstant Cub) (hcap N hN)
      (by simpa only [one_mul] using hp.2)
      (by simpa only [neg_one_mul, neg_mul, one_mul] using hm.2)
  · refine ⟨hC, ?_, ?_, ?_, ?_⟩
    · intro η hη K v hv p
      exact (hshort η hη hv p).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hnC (pow_nonneg K.coe_nonneg n))
          (gaussianLogShortRange_nonneg _ _))
    · intro η hη K v hv p
      exact (hlong η hη K v hv p).trans
        (mul_le_mul_of_nonneg_right hnC (pow_nonneg K.coe_nonneg n))
    · intro η hη hd K v hv ρ M hM hμ hρ p
      exact (hcentered η hη hd hv ρ M hM hρ p).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hnC (pow_nonneg K.coe_nonneg n))
          (add_nonneg (gaussianLogShortRange_nonneg _ _)
            (mul_nonneg hM (Real.rpow_nonneg hη.le _))))
    intro K v hv hK hd ρ M hM hμ hρ hpair
    obtain ⟨βloc, hloc, hβnamed⟩ := hnamed hv hK hd ρ M hM hρ hpair
    refine ⟨βloc, hloc, ?_⟩
    intro β hβ
    obtain ⟨Cub, Cpart, Cpf, hCub, hCpart, hCpfEq, hCpf,
      hpart, hremaining, hepsOld, hCem, hcap, hforcing, hmomOld, hentropicOld⟩ := hβnamed β hβ
    let μ := gaussianRieszDensityMeasure ρ
    let I := DGRHS.interactionEnergy μ (fun a b => logPhysicalPair (a,b))
    let ε := sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ)^n)
    let Cem := sourceLogTransportCem (β : ℝ) βloc I
      DGRHS.Concentration.glzUniversalTailConstant Cub
    have heps : 0 < ε := sourceLogTransportEpsilon_pos _ _ _ _ hβ hloc hC (pow_pos hK n)
    have hmom : ∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x => Real.exp (σ * ε * ((N : ℝ) *
          sourceTransportEnergy μ (sourceLogTransportKernel n v) N x)))
          (sourceLogSingularGibbs β ρ N) ∧
        (∫ x, Real.exp (σ * ε * ((N : ℝ) *
          sourceTransportEnergy μ (sourceLogTransportKernel n v) N x))
          ∂sourceLogSingularGibbs β ρ N) ≤ Cem := by
      intro σ hσ N hN
      exact commonCsr_signed_moments (sourceLogSingularGibbs β ρ N)
        (fun x => (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x)
        (β : ℝ) βloc Cnamed Csr ((K : ℝ)^n) Cem
        hβ hloc hCn hnC (pow_pos hK n) (fun τ hτ => hmomOld τ hτ N hN) σ hσ
    refine ⟨Cub, Cpart, Cpf, hCub, hCpart, hCpfEq, hCpf, hpart,
      hremaining, heps, hCem, hcap, hforcing, hmom, ?_⟩
    intro N hN ν hν
    obtain ⟨ha, A, hA, _⟩ := sourceLogTransport_all_law_proper n hn hv μ N (by omega)
    have hp := hmom 1 (by norm_num) N hN
    have hm := hmom (-1) (by norm_num) N hN
    exact sourceLog_entropic_collision_all_laws β hβ hd ρ M hM hρ hpair N hN ν
      (fun x => (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x)
      ha A hA ε heps
      (by simpa only [one_mul] using hp.1)
      (by simpa only [neg_one_mul, neg_mul, one_mul] using hm.1)
      Cpf Cem (hcap N hN).2
      (by simpa only [one_mul] using hp.2)
      (by simpa only [neg_one_mul, neg_mul, one_mul] using hm.2)

end DGRHS.Commutator
