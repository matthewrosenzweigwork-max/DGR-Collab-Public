/- Bounded observables are proper for every probability competitor. The
literal REP logarithmic entropic reduction includes infinite Gibbs entropy,
using genuine extended free energy instead of an infinity-to-real conversion.
Physical commutator exponential moments are upstream, not assumed proved. -/
import DGRHS.Entropy.SourceLogEntropicTransfer
import DGRHS.Entropy.SourceLogCollisionVariational
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace DGRHS.Entropy
open DGRHS.Gaussian DGRHS.CLT
variable {ι : Type*} [Fintype ι]

theorem sourceLog_entropic_all_laws (β : ℝ≥0) (hβ : 0<(β:ℝ))
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (N : ℕ) (hN : 1≤N) (ν : Measure (Fin N→EuclideanSpace ℝ ι)) [IsProbabilityMeasure ν]
    (a : (Fin N→EuclideanSpace ℝ ι)→ℝ) (ha : StronglyMeasurable a)
    (A : ℝ) (hA : ∀ x,|a x|≤A) (ε : ℝ) (hε : 0<ε)
    (hp : Integrable (fun x=>Real.exp (ε*a x)) (sourceLogSingularGibbs β ρ N))
    (hm : Integrable (fun x=>Real.exp (-(ε*a x))) (sourceLogSingularGibbs β ρ N))
    (Cpf Cem : ℝ) (hCpf : (sourceLogSingularPartition β ρ N).toReal≤Cpf)
    (hCp : (∫ x,Real.exp (ε*a x) ∂sourceLogSingularGibbs β ρ N)≤Cem)
    (hCm : (∫ x,Real.exp (-(ε*a x)) ∂sourceLogSingularGibbs β ρ N)≤Cem) :
    Integrable a ν ∧
      ((|∫ x,a x ∂ν| : ℝ) : EReal)≤(((β:ℝ)/ε)*(N:ℝ) : ℝ)*
        sourceLogExtendedFreeEnergy β ρ M N ν+
        (ε⁻¹*(Real.log Cpf+Real.log Cem) : ℝ) := by
  have hai : Integrable a ν := (integrable_const A).mono' ha.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x=>by simpa only [Real.norm_eq_abs] using hA x)
  refine ⟨hai,?_⟩
  have hb : 0<(β:ℝ)*(N:ℝ) := mul_pos hβ (by exact_mod_cast (by omega : 0<N))
  have hc : 0<((β:ℝ)/ε)*(N:ℝ) := mul_pos (div_pos hβ hε)
    (by exact_mod_cast (by omega : 0<N))
  by_cases hKL : klDiv ν (sourceLogSingularGibbs β ρ N)=∞
  · rw [sourceLogExtendedFreeEnergy_rewrite β hβ hd ρ M hM hρ hpair N hN ν,hKL]
    simp only [EReal.coe_ennreal_top,EReal.top_mul_coe_of_pos (inv_pos.mpr hb),
      EReal.top_sub_coe,EReal.coe_mul_top_of_pos hc,EReal.top_add_coe]
    exact le_top
  · obtain ⟨hac,hE,hllr,_,hbound⟩ := sourceLog_entropic_transfer β hβ hd ρ M hM hρ
      hpair N hN ν a ha ε hε hp hm hKL Cpf Cem hCpf hCp hCm
    rw [sourceLogExtendedFreeEnergy_eq_proper β hβ hd ρ M hM hρ hpair N hN ν hac hE hllr,
      ←EReal.coe_mul,←EReal.coe_add,EReal.coe_le_coe_iff]
    exact hbound

theorem sourceLog_entropic_collision_all_laws (β : ℝ≥0) (hβ : 0<(β:ℝ))
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (N : ℕ) (hN : 1≤N) (ν : Measure (Fin N→EuclideanSpace ℝ ι)) [IsProbabilityMeasure ν]
    (a : (Fin N→EuclideanSpace ℝ ι)→ℝ) (ha : StronglyMeasurable a)
    (A : ℝ) (hA : ∀ x,|a x|≤A) (ε : ℝ) (hε : 0<ε)
    (hp : Integrable (fun x=>Real.exp (ε*a x)) (sourceLogSingularGibbs β ρ N))
    (hm : Integrable (fun x=>Real.exp (-(ε*a x))) (sourceLogSingularGibbs β ρ N))
    (Cpf Cem : ℝ) (hCpf : (sourceLogSingularPartition β ρ N).toReal≤Cpf)
    (hCp : (∫ x,Real.exp (ε*a x) ∂sourceLogSingularGibbs β ρ N)≤Cem)
    (hCm : (∫ x,Real.exp (-(ε*a x)) ∂sourceLogSingularGibbs β ρ N)≤Cem) :
    Integrable a ν ∧
      ((|∫ x,a x ∂ν| : ℝ) : EReal)≤(((β:ℝ)/ε)*(N:ℝ) : ℝ)*
        sourceLogCollisionFreeEnergy β ρ M N ν+
        (ε⁻¹*(Real.log Cpf+Real.log Cem) : ℝ) := by
  rw [sourceLogCollisionFreeEnergy_eq β hβ hd ρ M N hN ν]
  exact sourceLog_entropic_all_laws β hβ hd ρ M hM hρ hpair N hN ν a ha A hA ε hε
    hp hm Cpf Cem hCpf hCp hCm

end DGRHS.Entropy
#check @DGRHS.Entropy.sourceLog_entropic_all_laws
#print axioms DGRHS.Entropy.sourceLog_entropic_all_laws

#check @DGRHS.Entropy.sourceLog_entropic_collision_all_laws
#print axioms DGRHS.Entropy.sourceLog_entropic_collision_all_laws
