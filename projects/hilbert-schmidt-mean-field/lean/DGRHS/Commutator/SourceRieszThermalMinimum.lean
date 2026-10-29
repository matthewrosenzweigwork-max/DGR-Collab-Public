import DGRHS.Commutator.SourceRieszCommonFiniteEnergy

/-! Original explicitly conditional positive-Riesz thermal minimum. The sharp
pointwise premise is EVERY configuration, not a product-a.e. assertion.
Cpw>=0 is material. Proper signed expectations are on the derived finite-KL domain. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal BigOperators
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Concentration
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem sourceRieszCommon_thermal_minimum (s M : ℝ) (n : ℕ) (hn : 1≤n)
    (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β) :
    ∃ Cpf Cem : ℝ,1≤Cpf ∧ 1≤Cem ∧ ∀ (K : ℝ≥0) (v : E→E),LipschitzWith K v →
      0<sourceRieszPositiveTransportParameter (ι:=ι) s M n K β ∧
      ∀ ρ : E→ℝ,IsProbabilityMeasure (gaussianRieszDensityMeasure ρ) →
      (∀ᵐ x ∂volume,ρ x≤M) → ∀ Cpw Cpt : ℝ,0≤Cpw →
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
  obtain ⟨Cpf,Cem,hCpf,hCem,hFamily⟩ := sourceRieszCommon_finiteKL_entropic (ι:=ι) s M n hn hs hd hM β hβ
  refine ⟨Cpf,Cem,hCpf,hCem,?_⟩
  intro K v hv
  obtain ⟨hε,hFam⟩ := hFamily K v hv
  refine ⟨hε,?_⟩
  intro ρ hprob hρ Cpw Cpt hCpw hpoint N hN ν hν hKL
  let _ := hprob
  obtain ⟨hac,hbg,hllr,ha,hent⟩ := hFam ρ hprob hρ N hN ν hKL
  have hNr : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  let a := fun ω : Fin N→E=>(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω
  have hscaled (ω : Fin N→E) : |a ω|≤Cpw*(sourceRieszTransportBackgroundEnergy ρ s N ω+
      Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))) := by
    have hm := mul_le_mul_of_nonneg_left (hpoint N hN ω) (Nat.cast_nonneg N)
    dsimp only [a]
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg N)]
    dsimp only [sourceRieszTransportBackgroundEnergy]
    convert hm using 1 <;> field_simp <;> ring
  have hi := integral_mono ha.abs
    ((hbg.add (integrable_const (Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))))).const_mul Cpw) hscaled
  have hbpoint : (∫ ω,|a ω| ∂ν)≤Cpw*((∫ ω,sourceRieszTransportBackgroundEnergy ρ s N ω ∂ν)+
      Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))) := by
    rw [integral_const_mul] at hi
    simp only [Pi.add_apply] at hi
    rw [integral_add hbg (integrable_const _)] at hi
    simpa [a] using hi
  have hex : (N:ℝ)*sourceRieszTransportProperFreeEnergy ρ s β N ν=
      (klDiv ν (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))).toReal/β+
      (∫ ω,sourceRieszTransportBackgroundEnergy ρ s N ω ∂ν) := by
    unfold sourceRieszTransportProperFreeEnergy
    field_simp [hNr,hβ.ne']
    <;> ring
  have henergy : (∫ ω,sourceRieszTransportBackgroundEnergy ρ s N ω ∂ν)≤
      (N:ℝ)*sourceRieszTransportProperFreeEnergy ρ s β N ν := by
    rw [hex]
    exact le_add_of_nonneg_left (div_nonneg ENNReal.toReal_nonneg hβ.le)
  have hpointbound : |∫ ω,a ω ∂ν|≤Cpw*(N:ℝ)*sourceRieszTransportProperFreeEnergy ρ s β N ν+
      Cpw*Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ)) := by
    calc
      _ ≤ ∫ ω,|a ω| ∂ν := abs_integral_le_integral_abs
      _ ≤ Cpw*((∫ ω,sourceRieszTransportBackgroundEnergy ρ s N ω ∂ν)+
          Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))) := hbpoint
      _ ≤ Cpw*((N:ℝ)*sourceRieszTransportProperFreeEnergy ρ s β N ν+
          Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))) :=
        mul_le_mul_of_nonneg_left (add_le_add henergy le_rfl) hCpw
      _ = _ := by ring
  exact ⟨ha,le_min hent hpointbound⟩

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszCommon_thermal_minimum
#print axioms DGRHS.Commutator.sourceRieszCommon_thermal_minimum
