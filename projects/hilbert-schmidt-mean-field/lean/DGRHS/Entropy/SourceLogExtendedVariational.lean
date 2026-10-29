/- Original unrestricted REPULSIVE logarithmic free-energy floor.
All probability competitors are included; entropy retains infinity and the
bounded-below energy expectation is its shifted nonnegative Lebesgue integral. -/
import DGRHS.Entropy.GibbsBoundedEnergy
import DGRHS.Entropy.SourceLogEnergyLowerBound
import DGRHS.CLT.SourceLogSingularIdentification
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace DGRHS.Entropy
open DGRHS.Gaussian DGRHS.CLT
variable {ι : Type*} [Fintype ι]

def sourceLogEnergyFloor (ρ : EuclideanSpace ℝ ι→ℝ) (M : ℝ) : ℝ :=
  let μ := gaussianRieszDensityMeasure ρ
  DGRHS.interactionEnergy μ (fun a b=>logPhysicalPair (a,b))-
    (gaussianRieszPhysicalPotentialConstant ((Fintype.card ι:ℝ)/4) M ι+
      logPhysicalTailIntegral μ+Real.log 2)

def sourceLogExtendedFreeEnergy (β : ℝ≥0) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (N : ℕ) (ν : Measure (Fin N→EuclideanSpace ℝ ι)) : EReal :=
  let μ := gaussianRieszDensityMeasure ρ
  let P := Measure.pi (fun _ : Fin N=>μ)
  let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
  let E := sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
    (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N
  boundedEnergyFreeEnergy P ν E (sourceLogEnergyFloor ρ M) ((β:ℝ)*(N:ℝ))

def sourceLogExtendedFreeEnergyValues (β : ℝ≥0) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (N : ℕ) : Set EReal :=
  {r | ∃ ν : Measure (Fin N→EuclideanSpace ℝ ι), IsProbabilityMeasure ν ∧
    r=sourceLogExtendedFreeEnergy β ρ M N ν}

theorem sourceLogExtendedFreeEnergy_isLeast (β : ℝ≥0) (hβ : 0<(β:ℝ))
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (N : ℕ) (hN : 1≤N) :
    IsLeast (sourceLogExtendedFreeEnergyValues β ρ M N)
      ((-Real.log (sourceLogSingularPartition β ρ N).toReal/((β:ℝ)*(N:ℝ)) : ℝ):EReal) := by
  let μ := gaussianRieszDensityMeasure ρ
  let P := Measure.pi (fun _ : Fin N=>μ)
  let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
  let E := sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
    (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N
  let b := (β:ℝ)*(N:ℝ)
  have hb : 0<b := mul_pos hβ (by exact_mod_cast (by omega : 0<N))
  have hL : ∀ x,sourceLogEnergyFloor ρ M≤E x :=
    fun x=>sourceLogEnergy_uniform_lower_bound hd ρ M hM hρ hpair N (by omega) x
  have hexp : Integrable (fun x=>Real.exp (-b*E x)) P := by
    convert sourceLogEnergyWeight_integrable (β:ℝ) β.coe_nonneg hd ρ M hM hρ hpair N using 1
    funext x
    congr 1
    dsimp only [b,E,μ,W]
    ring
  have hK : (sourceLogSingularPartition β ρ N).toReal=
      ∫ x,Real.exp (-b*E x) ∂P := by
    rw [sourceLogSingularPartition_eq_integral β hd ρ M hM hρ hpair N,
      ENNReal.toReal_ofReal (integral_nonneg fun x=>(Real.exp_pos _).le)]
    congr 1
    funext x
    congr 1
    dsimp only [b,E,μ,W]
    ring
  change IsLeast (boundedEnergyValues P E (sourceLogEnergyFloor ρ M) b) _
  rw [hK]
  exact boundedEnergyFreeEnergy_isLeast P E (sourceLogEnergyFloor ρ M) b hb hL hexp

theorem sourceLogExtendedFreeEnergy_inf (β : ℝ≥0) (hβ : 0<(β:ℝ))
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (N : ℕ) (hN : 1≤N) :
    sInf (sourceLogExtendedFreeEnergyValues β ρ M N)=
      ((-Real.log (sourceLogSingularPartition β ρ N).toReal/((β:ℝ)*(N:ℝ)) : ℝ):EReal) :=
  (sourceLogExtendedFreeEnergy_isLeast β hβ hd ρ M hM hρ hpair N hN).csInf_eq

theorem sourceLogExtendedFreeEnergy_rewrite (β : ℝ≥0) (hβ : 0<(β:ℝ))
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (N : ℕ) (hN : 1≤N) (ν : Measure (Fin N→EuclideanSpace ℝ ι)) [IsProbabilityMeasure ν] :
    sourceLogExtendedFreeEnergy β ρ M N ν=
      (klDiv ν (sourceLogSingularGibbs β ρ N):EReal)*(((β:ℝ)*(N:ℝ))⁻¹ : ℝ)-
      ((Real.log (sourceLogSingularPartition β ρ N).toReal/((β:ℝ)*(N:ℝ)) : ℝ):EReal) := by
  let μ := gaussianRieszDensityMeasure ρ
  let P := Measure.pi (fun _ : Fin N=>μ)
  let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
  let E := sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
    (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N
  let b := (β:ℝ)*(N:ℝ)
  have hb : 0<b := mul_pos hβ (by exact_mod_cast (by omega : 0<N))
  have hL : ∀ x,sourceLogEnergyFloor ρ M≤E x :=
    fun x=>sourceLogEnergy_uniform_lower_bound hd ρ M hM hρ hpair N (by omega) x
  have hexp : Integrable (fun x=>Real.exp (-b*E x)) P := by
    convert sourceLogEnergyWeight_integrable (β:ℝ) β.coe_nonneg hd ρ M hM hρ hpair N using 1
    funext x
    congr 1
    dsimp only [b,E,μ,W]
    ring
  have hK : (sourceLogSingularPartition β ρ N).toReal=
      ∫ x,Real.exp (-b*E x) ∂P := by
    rw [sourceLogSingularPartition_eq_integral β hd ρ M hM hρ hpair N,
      ENNReal.toReal_ofReal (integral_nonneg fun x=>(Real.exp_pos _).le)]
    congr 1
    funext x
    congr 1
    dsimp only [b,E,μ,W]
    ring
  let u := fun x=>-b*E x
  have hcap : ∀ x,u x≤-b*sourceLogEnergyFloor ρ M :=
    fun x=>mul_le_mul_of_nonpos_left (hL x) (by linarith)
  have hQ : sourceLogSingularGibbs β ρ N=P.tilted u := by
    rw [sourceLogSingularGibbs_eq β hd ρ M hM hρ hpair N,←sourceEnergyTilt_eq _ _ _ (β:ℝ) N]
    congr 1
    funext x
    dsimp only [u,b,E,μ,W]
    ring
  change boundedEnergyFreeEnergy P ν E (sourceLogEnergyFloor ρ M) b=_
  rw [boundedEnergyFreeEnergy_eq_scaledGibbs P ν E (sourceLogEnergyFloor ρ M) b hb,
    gibbsExtendedFreeEnergy_rewrite P ν u (-b*sourceLogEnergyFloor ρ M) hcap hexp,
    ←hQ,←hK,EReal.sub_mul_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr (inv_nonneg.mpr hb.le)) (EReal.coe_ne_top _),
    ←EReal.coe_mul]
  simp only [div_eq_mul_inv,b]


theorem sourceLogExtendedFreeEnergy_optimizer (β : ℝ≥0) (hβ : 0<(β:ℝ))
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (N : ℕ) (hN : 1≤N) :
    IsProbabilityMeasure (sourceLogSingularGibbs β ρ N) ∧
      sourceLogExtendedFreeEnergy β ρ M N (sourceLogSingularGibbs β ρ N)=
        ((-Real.log (sourceLogSingularPartition β ρ N).toReal/((β:ℝ)*(N:ℝ)) : ℝ):EReal) := by
  have hQ := sourceLogSingularGibbs_probability β hd ρ M hM hρ hpair N
  letI := hQ
  refine ⟨hQ,?_⟩
  rw [sourceLogExtendedFreeEnergy_rewrite β hβ hd ρ M hM hρ hpair N hN
    (sourceLogSingularGibbs β ρ N),klDiv_self]
  simp only [EReal.coe_ennreal_zero,zero_mul,zero_sub,←EReal.coe_neg]
  congr 1
  ring

theorem sourceLogExtendedFreeEnergy_bound_independent (β : ℝ≥0) (hβ : 0<(β:ℝ))
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M D : ℝ) (hM : 0≤M) (hD : 0≤D) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρM : ∀ᵐ x ∂volume,ρ x≤M) (hρD : ∀ᵐ x ∂volume,ρ x≤D)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (N : ℕ) (hN : 1≤N) (ν : Measure (Fin N→EuclideanSpace ℝ ι)) [IsProbabilityMeasure ν] :
    sourceLogExtendedFreeEnergy β ρ M N ν=sourceLogExtendedFreeEnergy β ρ D N ν := by
  rw [sourceLogExtendedFreeEnergy_rewrite β hβ hd ρ M hM hρM hpair N hN ν,
    sourceLogExtendedFreeEnergy_rewrite β hβ hd ρ D hD hρD hpair N hN ν]

theorem sourceLogExtendedFreeEnergy_eq_proper (β : ℝ≥0) (hβ : 0<(β:ℝ))
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (N : ℕ) (hN : 1≤N) (ν : Measure (Fin N→EuclideanSpace ℝ ι)) [IsProbabilityMeasure ν] :
    let μ := gaussianRieszDensityMeasure ρ
    let P := Measure.pi (fun _ : Fin N=>μ)
    let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
    let E := sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
      (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N
    ν ≪ P → Integrable E ν → Integrable (llr ν P) ν →
      sourceLogExtendedFreeEnergy β ρ M N ν=
        (((klDiv ν P).toReal/((β:ℝ)*(N:ℝ))+(∫ x,E x ∂ν) : ℝ):EReal) := by
  dsimp only
  intro hac hE hllr
  apply boundedEnergyFreeEnergy_eq_proper
  · intro x
    exact sourceLogEnergy_uniform_lower_bound hd ρ M hM hρ hpair N (by omega) x
  · exact hE
  · exact klDiv_ne_top_iff.mpr ⟨hac,hllr⟩

end DGRHS.Entropy
#check @DGRHS.Entropy.sourceLogExtendedFreeEnergy_isLeast
#print axioms DGRHS.Entropy.sourceLogExtendedFreeEnergy_isLeast
#check @DGRHS.Entropy.sourceLogExtendedFreeEnergy_inf
#print axioms DGRHS.Entropy.sourceLogExtendedFreeEnergy_inf

#check @DGRHS.Entropy.sourceLogExtendedFreeEnergy_rewrite
#print axioms DGRHS.Entropy.sourceLogExtendedFreeEnergy_rewrite
#check @DGRHS.Entropy.sourceLogExtendedFreeEnergy_optimizer
#print axioms DGRHS.Entropy.sourceLogExtendedFreeEnergy_optimizer
#print axioms DGRHS.Entropy.sourceLogExtendedFreeEnergy_bound_independent

#check @DGRHS.Entropy.sourceLogExtendedFreeEnergy_eq_proper
#print axioms DGRHS.Entropy.sourceLogExtendedFreeEnergy_eq_proper
