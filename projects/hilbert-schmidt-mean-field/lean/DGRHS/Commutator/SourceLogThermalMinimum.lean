/- Original explicitly conditional thermal minimum corollary. The signed
Gibbs moments and first entropic branch are derived here from the actual
physical kernel. Only the paper's stated pointwise premise is retained.
The estimate constant Cpw is explicitly nonnegative. -/
import DGRHS.Commutator.SourceLogEntropicCommutator
import DGRHS.Entropy.SourceLogPointwiseTransfer
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy
variable {ι : Type*} [Fintype ι]

theorem exists_sourceLog_thermal_minimum (n : ℕ) (hn : 0 < n) :
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
      let μ := gaussianRieszDensityMeasure ρ
      let W := fun a b => logPhysicalPair (a,b)
      let I := DGRHS.interactionEnergy μ W
      let ε := sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ)^n)
      let Cem := sourceLogTransportCem (β : ℝ) βloc I
        DGRHS.Concentration.glzUniversalTailConstant Cub
      0 < ε ∧ 0 < Cem ∧
      ∀ Cpw Cpt : ℝ, 0 ≤ Cpw →
      (∀ N : ℕ, 1 ≤ N → ∀ x : Fin N → EuclideanSpace ℝ ι,
        |sourceTransportEnergy μ (sourceLogTransportKernel n v) N x| ≤
          Cpw*(sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
            (DGRHS.potential μ W) I N x +
            Cpt*Real.log (Real.exp 1+(N : ℝ))/(N : ℝ))) →
      ∀ N : ℕ, 1 ≤ N → ∀ (ν : Measure (Fin N → EuclideanSpace ℝ ι))
        [IsProbabilityMeasure ν],
      Integrable (fun x => (N : ℝ)*sourceTransportEnergy μ
        (sourceLogTransportKernel n v) N x) ν ∧
      ((|∫ x, (N : ℝ)*sourceTransportEnergy μ (sourceLogTransportKernel n v) N x ∂ν| : ℝ) : EReal) ≤
        min ((((β : ℝ)/ε)*(N : ℝ) : ℝ)*sourceLogCollisionFreeEnergy β ρ M N ν +
          (ε⁻¹*(Real.log Cpf+Real.log Cem) : ℝ))
          ((Cpw*(N : ℝ) : ℝ)*sourceLogCollisionFreeEnergy β ρ M N ν +
            (Cpw*Cpt*Real.log (Real.exp 1+(N : ℝ)) : ℝ)) := by
  obtain ⟨Csr, hC, hfactory⟩ := exists_sourceLog_entropic_commutator (ι := ι) n hn
  refine ⟨Csr, hC, ?_⟩
  intro K v hv hK hd ρ M hM hμ hρ hpair
  obtain ⟨βloc, hloc, hβfactory⟩ := hfactory hv hK hd ρ M hM hρ hpair
  refine ⟨βloc, hloc, ?_⟩
  intro β hβ
  obtain ⟨Cub, Cpf, hCub, hCpf, _, hε, hCem, _, _, _, hent⟩ := hβfactory β hβ
  refine ⟨Cub, Cpf, hCub, hCpf, hε, hCem, ?_⟩
  intro Cpw Cpt hCpw hpoint N hN ν hν
  obtain ⟨ha, A, hA, _⟩ := sourceLogTransport_all_law_proper n hn hv
    (gaussianRieszDensityMeasure ρ) N (by omega)
  obtain ⟨hi, hb1⟩ := hent N hN ν
  have hnr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hscaled (x : Fin N → EuclideanSpace ℝ ι) :
      |(N : ℝ)*sourceTransportEnergy (gaussianRieszDensityMeasure ρ)
        (sourceLogTransportKernel n v) N x| ≤
      Cpw*((N : ℝ)*sourceCanonicalModulatedEnergy
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair)
        (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b)))
        (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b))) N x +
        Cpt*Real.log (Real.exp 1+(N : ℝ))) := by
    have hm := mul_le_mul_of_nonneg_left (hpoint N hN x) (Nat.cast_nonneg N)
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    convert hm using 1 <;> field_simp <;> ring
  obtain ⟨_, hb2⟩ := sourceLog_bounded_pointwise_transfer β hβ hd ρ M hM hρ hpair N hN ν
    (fun x => (N : ℝ)*sourceTransportEnergy (gaussianRieszDensityMeasure ρ)
      (sourceLogTransportKernel n v) N x) ha A hA Cpw Cpt
      (Real.log (Real.exp 1+(N : ℝ))) hCpw hscaled
  rw [←sourceLogCollisionFreeEnergy_eq β hβ hd ρ M N hN ν] at hb2
  exact ⟨hi, le_min hb1 hb2⟩

end DGRHS.Commutator
#check @DGRHS.Commutator.exists_sourceLog_thermal_minimum
#print axioms DGRHS.Commutator.exists_sourceLog_thermal_minimum
