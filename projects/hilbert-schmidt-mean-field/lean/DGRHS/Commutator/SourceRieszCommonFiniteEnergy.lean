import DGRHS.Commutator.SourceRieszCommonEntropy

/-! Finite actual extended physical objective derives finite Gibbs KL and the
proper original energy domain; no totalized finite formula is used as a premise. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma sourceRiesz_finiteObjective_GibbsKL (s M : ℝ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β)
    (ρ : E→ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (N : ℕ) (hN : 1≤N)
    (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν] (e : ℝ)
    (he : sourceRieszTransportExtendedFreeEnergy ρ s M β N ν=(e:EReal)) :
    klDiv ν (DGRHS.CLT.sourceRieszSingularGibbs s β ρ N)≠∞ := by
  intro htop
  have hb : 0<β*(N:ℝ) := mul_pos hβ (by exact_mod_cast (by omega : 0<N))
  rw [sourceRieszTransportExtendedFreeEnergy_rewrite s M hs hd hM β hβ ρ hρ N hN ν,
    htop,EReal.coe_ennreal_top,EReal.top_sub_coe,EReal.top_mul_coe_of_pos (inv_pos.mpr hb)] at he
  exact EReal.top_ne_coe e he

/-- Physical first or higher-order estimate on a finite actual objective. -/
theorem sourceRieszCommon_finiteObjective_transport (s M : ℝ) (n : ℕ) (hn : 1≤n)
    (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β) :
    ∃ Cpf Cem : ℝ,1≤Cpf ∧ 1≤Cem ∧ ∀ (K : ℝ≥0) (v : E→E),LipschitzWith K v →
      0<sourceRieszPositiveTransportParameter (ι:=ι) s M n K β ∧
      ∀ ρ : E→ℝ,IsProbabilityMeasure (gaussianRieszDensityMeasure ρ) →
      (∀ᵐ x ∂volume,ρ x≤M) → ∀ N : ℕ,1≤N →
      ∀ (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν] (e : ℝ),
      sourceRieszTransportExtendedFreeEnergy ρ s M β N ν=(e:EReal) →
      Integrable (fun ω=>(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω) ν ∧
      sourceRieszTransportProperFreeEnergy ρ s β N ν=e ∧
      |∫ ω,(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω ∂ν|≤
        (β/sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)*(N:ℝ)*e+
        (sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)⁻¹*(Real.log Cpf+Real.log Cem) := by
  obtain ⟨Cpf,Cem,hCpf,hCem,hFamily⟩ := sourceRieszCommon_finiteKL_entropic (ι:=ι) s M n hn hs hd hM β hβ
  refine ⟨Cpf,Cem,hCpf,hCem,?_⟩
  intro K v hv
  obtain ⟨hε,hFam⟩ := hFamily K v hv
  refine ⟨hε,?_⟩
  intro ρ hprob hρ N hN ν hν e he
  let _ := hprob
  have hKL := sourceRiesz_finiteObjective_GibbsKL s M hs hd hM β hβ ρ hρ N hN ν e he
  obtain ⟨hac,hbg,hllr,ha,hbound⟩ := hFam ρ hprob hρ N hN ν hKL
  have hi := sourceRieszTransportExtendedFreeEnergy_eq_proper s M hs hd hM β hβ ρ hρ N hN ν hac hbg hllr
  have hproper : sourceRieszTransportProperFreeEnergy ρ s β N ν=e := by
    apply EReal.coe_injective
    exact hi.symm.trans he
  exact ⟨ha,hproper,by simpa only [hproper] using hbound⟩

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_finiteObjective_GibbsKL
#print axioms DGRHS.Commutator.sourceRiesz_finiteObjective_GibbsKL
#check @DGRHS.Commutator.sourceRieszCommon_finiteObjective_transport
#print axioms DGRHS.Commutator.sourceRieszCommon_finiteObjective_transport
