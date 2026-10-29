/- Original repulsive-log source weights, all higher powers without an extra
one-body exponential tail. The actual physical uniform bound is instantiated
at p*beta; a direct N=0 clause completes the native CLT factory interface. -/
import DGRHS.CLT.SourceLogUniform
noncomputable section
open MeasureTheory
namespace DGRHS.CLT
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι]

theorem sourceLogWeight_uniform (γ : ℝ) (hγ : 0≤γ)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun (x y : EuclideanSpace ℝ ι)=>logPhysicalPair (x,y)
    let h := hoeffdingCentered μ logPhysicalPair
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    Integrable F μ ∧ ∃ C : ℝ,∀ N,
      Integrable (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp
        (sourceParticleExponent h F I γ N x)) (Measure.pi (fun _ : Fin N=>μ)) ∧
      (∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp (sourceParticleExponent h F I γ N x)
        ∂Measure.pi (fun _ : Fin N=>μ))≤C := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun (x y : EuclideanSpace ℝ ι)=>logPhysicalPair (x,y)
  let h := hoeffdingCentered μ logPhysicalPair
  let F := DGRHS.potential μ W
  let I := DGRHS.interactionEnergy μ W
  have hF : Integrable F μ := DGRHS.integrable_potential μ W hpair
  obtain ⟨C,hCpos,hC⟩ := sourceLogPartition_uniform γ hγ hd ρ M hM hρ hpair
  have hz (x : Fin 0→EuclideanSpace ℝ ι) : sourceParticleExponent h F I γ 0 x=-γ*I := by
    simp [sourceParticleExponent,DGRHS.CanonicalVariance.normalizedOffDiagonalSum,
      DGRHS.Decoupling.offDiagonalSum]
  refine ⟨hF,C+Real.exp (-γ*I),fun N=>?_⟩
  by_cases hn : N=0
  · subst N
    change Integrable (fun x : Fin 0→EuclideanSpace ℝ ι=>Real.exp
        (sourceParticleExponent h F I γ 0 x)) (Measure.pi (fun _ : Fin 0=>μ)) ∧
      (∫ x : Fin 0→EuclideanSpace ℝ ι,Real.exp (sourceParticleExponent h F I γ 0 x)
        ∂Measure.pi (fun _ : Fin 0=>μ))≤C+Real.exp (-γ*I)
    constructor
    · simpa only [hz] using (integrable_const (μ := Measure.pi (fun _ : Fin 0=>μ)) (Real.exp (-γ*I)))
    · simp only [hz,integral_const,probReal_univ,one_smul]
      exact le_add_of_nonneg_left hCpos.le
  · have hn' : 0<N := Nat.pos_of_ne_zero hn
    obtain ⟨hi,hb⟩ := hC N (by omega)
    rw [show (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp
      (-γ*(N:ℝ)*sourceCanonicalModulatedEnergy h F I N x))=
      (fun x=>Real.exp (sourceParticleExponent h F I γ N x)) from
      funext fun x=>congrArg Real.exp (sourceCanonicalModulatedEnergy_exponent h F I γ hn' x)] at hi hb
    exact ⟨hi,hb.trans (le_add_of_nonneg_right (Real.exp_pos _).le)⟩

theorem sourceLogWeight_higher (β p : ℝ) (hβ : 0≤β) (hp : 0≤p)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun (x y : EuclideanSpace ℝ ι)=>logPhysicalPair (x,y)
    let h := hoeffdingCentered μ logPhysicalPair
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    Integrable F μ ∧ ∃ C : ℝ,∀ N,
      Integrable (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp
        (p*sourceParticleExponent h F I β N x)) (Measure.pi (fun _ : Fin N=>μ)) ∧
      (∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp (p*sourceParticleExponent h F I β N x)
        ∂Measure.pi (fun _ : Fin N=>μ))≤C := by
  simpa only [sourceParticleExponent_mul_parameter] using
    sourceLogWeight_uniform (p*β) (mul_nonneg hp hβ) hd ρ M hM hρ hpair
end DGRHS.CLT
#check @DGRHS.CLT.sourceLogWeight_uniform
#check @DGRHS.CLT.sourceLogWeight_higher
#print axioms DGRHS.CLT.sourceLogWeight_uniform
#print axioms DGRHS.CLT.sourceLogWeight_higher
