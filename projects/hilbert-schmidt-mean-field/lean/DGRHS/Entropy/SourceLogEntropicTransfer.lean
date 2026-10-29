/- Source final logarithmic entropic reduction with the literal singular
Gibbs measure and exact beta/epsilon times N free-energy normalization.
Energy/base-entropy properness is derived from finite entropy against Gibbs.
The physical commutator moments are upstream inputs awaiting instantiation. -/
import DGRHS.Entropy.GibbsEntropicTransfer
import DGRHS.Entropy.SourceLogExtendedVariational
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace DGRHS.Entropy
open DGRHS.Gaussian DGRHS.CLT
variable {ι : Type*} [Fintype ι]

theorem sourceLog_entropic_transfer (β : ℝ≥0) (hβ : 0<(β:ℝ))
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (N : ℕ) (hN : 1≤N) (ν : Measure (Fin N→EuclideanSpace ℝ ι)) [IsProbabilityMeasure ν]
    (a : (Fin N→EuclideanSpace ℝ ι)→ℝ) (ha : StronglyMeasurable a)
    (ε : ℝ) (hε : 0<ε)
    (hp : Integrable (fun x=>Real.exp (ε*a x)) (sourceLogSingularGibbs β ρ N))
    (hm : Integrable (fun x=>Real.exp (-(ε*a x))) (sourceLogSingularGibbs β ρ N))
    (hKL : klDiv ν (sourceLogSingularGibbs β ρ N)≠∞)
    (Cpf Cem : ℝ) (hCpf : (sourceLogSingularPartition β ρ N).toReal≤Cpf)
    (hCp : (∫ x,Real.exp (ε*a x) ∂sourceLogSingularGibbs β ρ N)≤Cem)
    (hCm : (∫ x,Real.exp (-(ε*a x)) ∂sourceLogSingularGibbs β ρ N)≤Cem) :
    let μ := gaussianRieszDensityMeasure ρ
    let P := Measure.pi (fun _ : Fin N=>μ)
    let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
    let E := sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
      (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N
    ν ≪ P ∧ Integrable E ν ∧ Integrable (llr ν P) ν ∧ Integrable a ν ∧
      |∫ x,a x ∂ν|≤((β:ℝ)/ε)*(N:ℝ)*
        ((klDiv ν P).toReal/((β:ℝ)*(N:ℝ))+(∫ x,E x ∂ν))+
        ε⁻¹*(Real.log Cpf+Real.log Cem) := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let P := Measure.pi (fun _ : Fin N=>μ)
  let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
  let E := sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
    (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N
  let b := (β:ℝ)*(N:ℝ)
  let u := fun x=>-b*E x
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
  have hQ : sourceLogSingularGibbs β ρ N=P.tilted u := by
    rw [sourceLogSingularGibbs_eq β hd ρ M hM hρ hpair N,←sourceEnergyTilt_eq _ _ _ (β:ℝ) N]
    congr 1
    funext x
    dsimp only [u,b,E,μ,W]
    ring
  rw [hK] at hCpf
  rw [hQ] at hp hm hKL hCp hCm
  obtain ⟨hac,hE,hllr,hai,hbound⟩ := gibbs_entropic_transfer P ν E (sourceLogEnergyFloor ρ M)
    b hb hL hexp a ha ε hε hp hm hKL Cpf Cem hCpf hCp hCm
  refine ⟨hac,hE,hllr,hai,?_⟩
  convert hbound using 1
  dsimp only [b]
  field_simp [hβ.ne',hε.ne',Nat.cast_ne_zero.mpr (by omega : N≠0)]
  <;> ring

end DGRHS.Entropy
#check @DGRHS.Entropy.sourceLog_entropic_transfer
#print axioms DGRHS.Entropy.sourceLog_entropic_transfer
