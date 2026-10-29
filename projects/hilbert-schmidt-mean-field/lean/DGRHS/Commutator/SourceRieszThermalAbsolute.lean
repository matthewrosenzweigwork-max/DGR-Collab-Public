import DGRHS.Commutator.SourceRieszThermalMinimum

/-! Every-law ABSOLUTE thermal minimum, using nonnegative Lebesgue integration.
Infinity is retained. The sharp signed finite-KL bound has logCem; this stronger
absolute-expectation estimate honestly keeps log(2Cem). -/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal BigOperators
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem sourceRieszCommon_allLaw_thermal_absolute (s M : ℝ) (n : ℕ) (hn : 1≤n)
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
      ((∫⁻ ω,ENNReal.ofReal |(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω| ∂ν):EReal)≤
        min (((β/sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)*(N:ℝ):ℝ)*
          sourceRieszTransportExtendedFreeEnergy ρ s M β N ν+
          ((sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)⁻¹*(Real.log Cpf+Real.log (2*Cem)):ℝ))
          ((Cpw*(N:ℝ):ℝ)*sourceRieszTransportExtendedFreeEnergy ρ s M β N ν+
            (Cpw*Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ)):ℝ)) := by
  obtain ⟨Cpf,Cem,hCpf,hCem,hFamily⟩ := sourceRieszCommon_allLaw_extendedFreeEnergy (ι:=ι) s M n hn hs hd hM β hβ
  obtain ⟨Cpd,Cmd,hCpd,hCmd,hDomain⟩ := sourceRieszCommon_finiteKL_entropic (ι:=ι) s M n hn hs hd hM β hβ
  refine ⟨Cpf,Cem,hCpf,hCem,?_⟩
  intro K v hv
  obtain ⟨hε,hFam⟩ := hFamily K v hv
  refine ⟨hε,?_⟩
  intro ρ hprob hρ Cpw Cpt hCpw hpoint N hN ν hν
  let _ := hprob
  have hent := hFam ρ hprob hρ N hN ν
  apply le_min hent
  by_cases hc0 : Cpw=0
  · have haz (ω : Fin N→E) : sourceRieszLocalTransportEnergy ρ s n v N ω=0 := by
      have h := hpoint N hN ω
      rw [hc0,zero_mul] at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    simp only [haz,mul_zero,abs_zero,ENNReal.ofReal_zero,lintegral_zero,
      EReal.coe_ennreal_zero,hc0,zero_mul,EReal.coe_zero,EReal.zero_mul,add_zero]
    exact le_rfl
  · have hcp : 0<Cpw*(N:ℝ) := mul_pos (lt_of_le_of_ne hCpw (Ne.symm hc0))
      (by exact_mod_cast (by omega : 0<N))
    by_cases hKL : klDiv ν (DGRHS.CLT.sourceRieszSingularGibbs s β ρ N)=∞
    · have heTop : sourceRieszTransportExtendedFreeEnergy ρ s M β N ν=⊤ := by
        rw [sourceRieszTransportExtendedFreeEnergy_rewrite s M hs hd hM β hβ ρ hρ N hN ν,
          hKL,EReal.coe_ennreal_top,EReal.top_sub_coe,
          EReal.top_mul_coe_of_pos (inv_pos.mpr (mul_pos hβ (by exact_mod_cast (by omega : 0<N))))]
      rw [heTop,EReal.coe_mul_top_of_pos hcp,EReal.top_add_coe]
      exact le_top
    · obtain ⟨hac,hbg,hllr,ha,_⟩ := (hDomain K v hv).2 ρ hprob hρ N hN ν hKL
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
      have hpointbound : (∫ ω,|a ω| ∂ν)≤Cpw*(N:ℝ)*sourceRieszTransportProperFreeEnergy ρ s β N ν+
          Cpw*Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ)) := by
        calc
          (∫ ω,|a ω| ∂ν) ≤ Cpw*((∫ ω,sourceRieszTransportBackgroundEnergy ρ s N ω ∂ν)+
              Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))) := hbpoint
          _ ≤ Cpw*((N:ℝ)*sourceRieszTransportProperFreeEnergy ρ s β N ν+
              Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))) :=
            mul_le_mul_of_nonneg_left (add_le_add henergy le_rfl) hCpw
          _ = _ := by ring
      have heq := sourceRieszTransportExtendedFreeEnergy_eq_proper s M hs hd hM β hβ ρ hρ N hN ν hac hbg hllr
      rw [heq,←ofReal_integral_eq_lintegral_ofReal ha.abs (ae_of_all _ fun ω=>abs_nonneg _),
        EReal.coe_ennreal_ofReal,max_eq_left (integral_nonneg (fun ω=>abs_nonneg _)),
        ←EReal.coe_mul,←EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by simpa only [mul_assoc] using hpointbound)

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszCommon_allLaw_thermal_absolute
#print axioms DGRHS.Commutator.sourceRieszCommon_allLaw_thermal_absolute
