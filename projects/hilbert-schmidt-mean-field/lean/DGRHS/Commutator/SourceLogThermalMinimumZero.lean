/- Zero-Lipschitz branch of the original conditional thermal-minimum bound.
The actual observable vanishes; every positive epsilon is admissible, Cem=1.
Only the source's pointwise premise remains, with its estimate constant nonnegative. -/
import DGRHS.Commutator.SourceLogThermalMinimum
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy
variable {ι : Type*} [Fintype ι]

theorem sourceLog_thermal_minimum_zero (n : ℕ) (hn : 0 < n)
    {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hv : LipschitzWith 0 v)
    (β : ℝ≥0) (hβ : 0 < (β : ℝ)) (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
      (gaussianRieszDensityMeasure ρ))) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cpf : ℝ, 1 ≤ Cpf ∧ ∀ Cpw Cpt : ℝ, 0 ≤ Cpw →
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
  obtain ⟨Cpf, hCpf, hent⟩ := sourceLog_entropic_commutator_zero n hn hv β hβ hd ρ M hM hρ hpair ε hε
  refine ⟨Cpf, hCpf, ?_⟩
  intro Cpw Cpt hCpw hpoint N hN ν hν
  obtain ⟨hi, hb1⟩ := (hent N hN).2 ν
  let a := fun x : Fin N → EuclideanSpace ℝ ι => (N : ℝ)*sourceTransportEnergy
    (gaussianRieszDensityMeasure ρ) (sourceLogTransportKernel n v) N x
  have ha0 : a = fun _ => 0 := by
    funext x
    simp only [a, sourceTransportEnergy_zero_lipschitz (gaussianRieszDensityMeasure ρ) n hn hv, mul_zero]
  have ha : StronglyMeasurable a := by rw [ha0]; exact stronglyMeasurable_const
  have hbound : ∀ x, |a x| ≤ 0 := by simp [ha0]
  have hnr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hscaled (x : Fin N → EuclideanSpace ℝ ι) :
      |a x| ≤ Cpw*((N : ℝ)*sourceCanonicalModulatedEnergy
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair)
        (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b)))
        (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b))) N x +
        Cpt*Real.log (Real.exp 1+(N : ℝ))) := by
    have hm := mul_le_mul_of_nonneg_left (hpoint N hN x) (Nat.cast_nonneg N)
    dsimp only [a]
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    convert hm using 1 <;> field_simp <;> ring
  obtain ⟨_, hb2⟩ := sourceLog_bounded_pointwise_transfer β hβ hd ρ M hM hρ hpair N hN ν
    a ha 0 hbound Cpw Cpt (Real.log (Real.exp 1+(N : ℝ))) hCpw hscaled
  rw [←sourceLogCollisionFreeEnergy_eq β hβ hd ρ M N hN ν] at hb2
  exact ⟨hi, le_min hb1 hb2⟩

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceLog_thermal_minimum_zero
#print axioms DGRHS.Commutator.sourceLog_thermal_minimum_zero
