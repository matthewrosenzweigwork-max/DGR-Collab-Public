import DGRHS.Commutator.SourceRieszThermalSign
import DGRHS.Commutator.SourceRieszThermalAbsolute

/-! Source-exact multiplier hypotheses for the positive Riesz thermal minimum.
Nonnegativity is derived from the original every-configuration estimate.
The finite-KL signed and every-law extended absolute domains remain distinct;
the latter retains the honest log(2 Cem) constant. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal BigOperators
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Concentration
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem sourceRieszCommon_thermal_minimum_source (s M : ℝ) (n : ℕ) (hn : 1≤n)
    (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β) :
    ∃ Cpf Cem : ℝ,1≤Cpf ∧ 1≤Cem ∧ ∀ (K : ℝ≥0) (v : E→E),LipschitzWith K v →
      0<sourceRieszPositiveTransportParameter (ι:=ι) s M n K β ∧
      ∀ ρ : E→ℝ,IsProbabilityMeasure (gaussianRieszDensityMeasure ρ) →
      (∀ᵐ x ∂volume,ρ x≤M) → ∀ Cpw Cpt : ℝ,
      (∀ N : ℕ,1≤N → ∀ ω : Fin N→E,
        |sourceRieszLocalTransportEnergy ρ s n v N ω|≤Cpw*
          (DGRHS.CLT.sourceCanonicalModulatedEnergy
            (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
            (sourceRieszLocalPhysicalPotential ρ s) (sourceRieszLocalPhysicalEnergy ρ s) N ω+
            Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))/(N:ℝ))) →
      ∀ N : ℕ,1≤N → ∀ (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν],
      klDiv ν (DGRHS.CLT.sourceRieszSingularGibbs s β ρ N)≠∞ →
      Integrable (fun ω=>(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω) ν ∧
      |∫ ω,(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω ∂ν|≤
        min ((β/sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)*(N:ℝ)*
          sourceRieszTransportProperFreeEnergy ρ s β N ν+
          (sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)⁻¹*(Real.log Cpf+Real.log Cem))
          (Cpw*(N:ℝ)*sourceRieszTransportProperFreeEnergy ρ s β N ν+
            Cpw*Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))) := by
  obtain ⟨Cpf,Cem,hCpf,hCem,hFamily⟩ := sourceRieszCommon_thermal_minimum (ι:=ι) s M n hn hs hd hM β hβ
  refine ⟨Cpf,Cem,hCpf,hCem,?_⟩
  intro K v hv
  obtain ⟨hε,hFam⟩ := hFamily K v hv
  refine ⟨hε,?_⟩
  intro ρ hprob hρ Cpw Cpt hpoint
  letI := hprob
  have hCpw := sourceRiesz_thermal_pointwise_constant_nonneg s M n hs (by linarith) hM
    ρ hρ v Cpw Cpt hpoint
  exact hFam ρ hprob hρ Cpw Cpt hCpw hpoint

theorem sourceRieszCommon_allLaw_thermal_absolute_source (s M : ℝ) (n : ℕ) (hn : 1≤n)
    (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β) :
    ∃ Cpf Cem : ℝ,1≤Cpf ∧ 1≤Cem ∧ ∀ (K : ℝ≥0) (v : E→E),LipschitzWith K v →
      0<sourceRieszPositiveTransportParameter (ι:=ι) s M n K β ∧
      ∀ ρ : E→ℝ,IsProbabilityMeasure (gaussianRieszDensityMeasure ρ) →
      (∀ᵐ x ∂volume,ρ x≤M) → ∀ Cpw Cpt : ℝ,
      (∀ N : ℕ,1≤N → ∀ ω : Fin N→E,
        |sourceRieszLocalTransportEnergy ρ s n v N ω|≤Cpw*
          (DGRHS.CLT.sourceCanonicalModulatedEnergy
            (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
            (sourceRieszLocalPhysicalPotential ρ s) (sourceRieszLocalPhysicalEnergy ρ s) N ω+
            Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))/(N:ℝ))) →
      ∀ N : ℕ,1≤N → ∀ (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν],
      ((∫⁻ ω,ENNReal.ofReal |(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω| ∂ν):EReal)≤
        min (((β/sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)*(N:ℝ):ℝ)*
          sourceRieszTransportExtendedFreeEnergy ρ s M β N ν+
          ((sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)⁻¹*(Real.log Cpf+Real.log (2*Cem)):ℝ))
          ((Cpw*(N:ℝ):ℝ)*sourceRieszTransportExtendedFreeEnergy ρ s M β N ν+
            (Cpw*Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ)):ℝ)) := by
  obtain ⟨Cpf,Cem,hCpf,hCem,hFamily⟩ := sourceRieszCommon_allLaw_thermal_absolute (ι:=ι) s M n hn hs hd hM β hβ
  refine ⟨Cpf,Cem,hCpf,hCem,?_⟩
  intro K v hv
  obtain ⟨hε,hFam⟩ := hFamily K v hv
  refine ⟨hε,?_⟩
  intro ρ hprob hρ Cpw Cpt hpoint
  letI := hprob
  have hCpw := sourceRiesz_thermal_pointwise_constant_nonneg s M n hs (by linarith) hM
    ρ hρ v Cpw Cpt hpoint
  exact hFam ρ hprob hρ Cpw Cpt hCpw hpoint

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszCommon_thermal_minimum_source
#print axioms DGRHS.Commutator.sourceRieszCommon_thermal_minimum_source
#check @DGRHS.Commutator.sourceRieszCommon_allLaw_thermal_absolute_source
#print axioms DGRHS.Commutator.sourceRieszCommon_allLaw_thermal_absolute_source
