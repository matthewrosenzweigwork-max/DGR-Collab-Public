import DGRHS.Commutator.SourceLogThermalSign

/-! Original logarithmic thermal multiplier hypotheses, source3547–3583.
The source every-configuration bound itself forces Cpw>=0; the actual
positive and zero Lipschitz branches therefore need no extra sign premise.
All original proper log-density and genuine extended objective qualifications
from the preceding thermal estimates are retained. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy
variable {ι : Type*} [Fintype ι]

theorem exists_sourceLog_thermal_minimum_source (n : ℕ) (hn : 0 < n) :
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
      ∀ Cpw Cpt : ℝ, 
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
  obtain ⟨Csr,hC,hfactory⟩ := exists_sourceLog_thermal_minimum (ι:=ι) n hn
  refine ⟨Csr,hC,?_⟩
  intro K v hv hK hd ρ M hM hμ hρ hpair
  obtain ⟨βloc,hloc,hβfactory⟩ := hfactory hv hK hd ρ M hM hρ hpair
  refine ⟨βloc,hloc,?_⟩
  intro β hβ
  obtain ⟨Cub,Cpf,hCub,hCpf,hε,hCem,hFam⟩ := hβfactory β hβ
  refine ⟨Cub,Cpf,hCub,hCpf,hε,hCem,?_⟩
  intro Cpw Cpt hpoint
  have hCpw := sourceLog_thermal_pointwise_constant_nonneg hd ρ M hM hρ hpair n v Cpw Cpt hpoint
  exact hFam Cpw Cpt hCpw hpoint

theorem sourceLog_thermal_minimum_zero_source (n : ℕ) (hn : 0 < n)
    {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hv : LipschitzWith 0 v)
    (β : ℝ≥0) (hβ : 0 < (β : ℝ)) (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
      (gaussianRieszDensityMeasure ρ))) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cpf : ℝ, 1 ≤ Cpf ∧ ∀ Cpw Cpt : ℝ, 
      (∀ N : ℕ, 1 ≤ N → ∀ x : Fin N → EuclideanSpace ℝ ι,
        |sourceTransportEnergy (gaussianRieszDensityMeasure ρ) (sourceLogTransportKernel n v) N x| ≤
          Cpw*(sourceCanonicalModulatedEnergy
            (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair)
            (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b)))
            (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b))) N x +
            Cpt*Real.log (Real.exp 1+(N : ℝ))/(N : ℝ))) →
      ∀ N : ℕ, 1 ≤ N → ∀ (ν : Measure (Fin N → EuclideanSpace ℝ ι))
        [IsProbabilityMeasure ν],
      Integrable (fun x => (N : ℝ)*sourceTransportEnergy (gaussianRieszDensityMeasure ρ)
        (sourceLogTransportKernel n v) N x) ν ∧
      ((|∫ x, (N : ℝ)*sourceTransportEnergy (gaussianRieszDensityMeasure ρ)
        (sourceLogTransportKernel n v) N x ∂ν| : ℝ) : EReal) ≤
        min ((((β : ℝ)/ε)*(N : ℝ) : ℝ)*sourceLogCollisionFreeEnergy β ρ M N ν +
          (ε⁻¹*(Real.log Cpf+Real.log 1) : ℝ))
          ((Cpw*(N : ℝ) : ℝ)*sourceLogCollisionFreeEnergy β ρ M N ν +
            (Cpw*Cpt*Real.log (Real.exp 1+(N : ℝ)) : ℝ)) := by
  obtain ⟨Cpf,hCpf,hFam⟩ := sourceLog_thermal_minimum_zero n hn hv β hβ hd ρ M hM hρ hpair ε hε
  refine ⟨Cpf,hCpf,?_⟩
  intro Cpw Cpt hpoint
  have hCpw := sourceLog_thermal_pointwise_constant_nonneg hd ρ M hM hρ hpair n v Cpw Cpt hpoint
  exact hFam Cpw Cpt hCpw hpoint

end DGRHS.Commutator
#check @DGRHS.Commutator.exists_sourceLog_thermal_minimum_source
#print axioms DGRHS.Commutator.exists_sourceLog_thermal_minimum_source
#check @DGRHS.Commutator.sourceLog_thermal_minimum_zero_source
#print axioms DGRHS.Commutator.sourceLog_thermal_minimum_zero_source
