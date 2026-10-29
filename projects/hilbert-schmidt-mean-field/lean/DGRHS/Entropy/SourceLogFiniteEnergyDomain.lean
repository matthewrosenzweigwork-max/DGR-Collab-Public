/- Actual logarithmic physical finite-energy domain. The physical reference
assumptions validate the shift; a finite upper bound then derives finite Gibbs
entropy and the proper original unshifted energy/base likelihood. -/
import DGRHS.Entropy.SourceLogCollisionVariational
import DGRHS.Entropy.GibbsFiniteDomain
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace DGRHS.Entropy
open DGRHS.Gaussian DGRHS.CLT
variable {ι : Type*} [Fintype ι]

theorem sourceLogCollisionFreeEnergy_finite_gibbsKL (β : ℝ≥0) (hβ : 0<(β:ℝ))
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (N : ℕ) (hN : 1≤N) (ν : Measure (Fin N→EuclideanSpace ℝ ι)) [IsProbabilityMeasure ν]
    (C : ℝ) (hC : sourceLogCollisionFreeEnergy β ρ M N ν≤(C:EReal)) :
    klDiv ν (sourceLogSingularGibbs β ρ N)≠∞ := by
  rw [sourceLogCollisionFreeEnergy_eq β hβ hd ρ M N hN ν,
    sourceLogExtendedFreeEnergy_rewrite β hβ hd ρ M hM hρ hpair N hN ν] at hC
  intro ht
  have hb : 0<(β:ℝ)*(N:ℝ) := mul_pos hβ (by exact_mod_cast (by omega : 0<N))
  rw [ht,EReal.coe_ennreal_top,EReal.top_mul_coe_of_pos (inv_pos.mpr hb),
    EReal.top_sub_coe] at hC
  exact EReal.coe_ne_top C (top_le_iff.mp hC)

theorem sourceLogCollisionFreeEnergy_finite_domain (β : ℝ≥0) (hβ : 0<(β:ℝ))
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (N : ℕ) (hN : 1≤N) (ν : Measure (Fin N→EuclideanSpace ℝ ι)) [IsProbabilityMeasure ν]
    (C : ℝ) (hC : sourceLogCollisionFreeEnergy β ρ M N ν≤(C:EReal)) :
    let μ := gaussianRieszDensityMeasure ρ
    let P := Measure.pi (fun _ : Fin N=>μ)
    let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
    let E := sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
      (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N
    ν ≪ P ∧ Integrable E ν ∧ Integrable (llr ν P) ν ∧
      sourceLogCollisionFreeEnergy β ρ M N ν=
        (((klDiv ν P).toReal/((β:ℝ)*(N:ℝ))+(∫ x,E x ∂ν) : ℝ):EReal) := by
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
  have hexp : Integrable (fun x=>Real.exp (u x)) P := by
    convert sourceLogEnergyWeight_integrable (β:ℝ) β.coe_nonneg hd ρ M hM hρ hpair N using 1
    funext x
    congr 1
    dsimp only [u,b,E,μ,W]
    ring
  have hQ : sourceLogSingularGibbs β ρ N=P.tilted u := by
    rw [sourceLogSingularGibbs_eq β hd ρ M hM hρ hpair N,←sourceEnergyTilt_eq _ _ _ (β:ℝ) N]
    congr 1
    funext x
    dsimp only [u,b,E,μ,W]
    ring
  have hKL := sourceLogCollisionFreeEnergy_finite_gibbsKL β hβ hd ρ M hM hρ hpair N hN ν C hC
  rw [hQ] at hKL
  have hcap : ∀ x,u x≤-b*sourceLogEnergyFloor ρ M :=
    fun x=>mul_le_mul_of_nonpos_left (hL x) (by linarith)
  obtain ⟨hac,hu,hllr⟩ := (gibbsKL_finite_domain P ν u (-b*sourceLogEnergyFloor ρ M) hcap hexp).mp hKL
  have hE : Integrable E ν := by
    have hi := hu.const_mul (-b)⁻¹
    convert hi using 1
    funext x
    dsimp only [u]
    field_simp [hb.ne']
  refine ⟨hac,hE,hllr,?_⟩
  rw [sourceLogCollisionFreeEnergy_eq β hβ hd ρ M N hN ν]
  exact sourceLogExtendedFreeEnergy_eq_proper β hβ hd ρ M hM hρ hpair N hN ν hac hE hllr
end DGRHS.Entropy
#check @DGRHS.Entropy.sourceLogCollisionFreeEnergy_finite_gibbsKL
#print axioms DGRHS.Entropy.sourceLogCollisionFreeEnergy_finite_gibbsKL
#check @DGRHS.Entropy.sourceLogCollisionFreeEnergy_finite_domain
#print axioms DGRHS.Entropy.sourceLogCollisionFreeEnergy_finite_domain
