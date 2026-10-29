/- The actual collision-zero ENNReal partition and normalized source Gibbs
measure, identified with proper real representatives under original logarithmic
hypotheses. beta=0 and N=0 are retained. No spatial-diagonal identity is used. -/
import DGRHS.CLT.SourceLogSingularWeight
import DGRHS.CLT.SourceLogWeight
import DGRHS.CLT.SourceEnergyTilt
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
namespace DGRHS.CLT
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def sourceLogSingularGibbs (β : ℝ≥0) (ρ : EuclideanSpace ℝ ι→ℝ) (N : ℕ) :
    Measure (Fin N→EuclideanSpace ℝ ι) :=
  (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)).withDensity
    (fun x=>sourceLogSingularWeight β ρ N x/sourceLogSingularPartition β ρ N)

lemma sourceLogEnergyWeight_integrable (β : ℝ) (hβ : 0≤β)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) (N : ℕ) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
    Integrable (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp (-β*(N:ℝ)*
      sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x))
      (Measure.pi (fun _ : Fin N=>μ)) := by
  dsimp only
  by_cases hN : N=0
  · subst N
    simpa only [Nat.cast_zero,mul_zero,zero_mul,neg_zero,Real.exp_zero] using
      (integrable_const (1:ℝ) : Integrable (fun _ : Fin 0→EuclideanSpace ℝ ι=>(1:ℝ))
        (Measure.pi (fun _ : Fin 0=>gaussianRieszDensityMeasure ρ)))
  · obtain ⟨_,C,hC⟩ := sourceLogWeight_uniform β hβ hd ρ M hM hρ hpair
    simp_rw [sourceCanonicalModulatedEnergy_exponent _ _ _ β (Nat.pos_of_ne_zero hN)]
    exact (hC N).1

lemma sourceLogSingularPartition_eq_integral (β : ℝ≥0)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) (N : ℕ) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
    sourceLogSingularPartition β ρ N=ENNReal.ofReal
      (∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp (-(β:ℝ)*(N:ℝ)*
        sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
          (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x)
        ∂Measure.pi (fun _ : Fin N=>μ)) := by
  dsimp only
  have hi := sourceLogEnergyWeight_integrable (β:ℝ) β.coe_nonneg hd ρ M hM hρ hpair N
  unfold sourceLogSingularPartition
  rw [lintegral_congr_ae (sourceLogSingularWeight_ae β hd ρ N)]
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun x=>(Real.exp_pos _).le)).symm

lemma sourceLogSingularPartition_pos_finite (β : ℝ≥0)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) (N : ℕ) :
    0<sourceLogSingularPartition β ρ N ∧ sourceLogSingularPartition β ρ N<∞ := by
  rw [sourceLogSingularPartition_eq_integral β hd ρ M hM hρ hpair N]
  refine ⟨ENNReal.ofReal_pos.mpr ?_,ENNReal.ofReal_lt_top⟩
  exact integral_exp_pos
    (sourceLogEnergyWeight_integrable (β:ℝ) β.coe_nonneg hd ρ M hM hρ hpair N)

lemma sourceLogSingularGibbs_eq (β : ℝ≥0)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) (N : ℕ) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
    sourceLogSingularGibbs β ρ N=(Measure.pi (fun _ : Fin N=>μ)).tilted
      (sourceParticleExponent (hoeffdingCentered μ logPhysicalPair)
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) (β:ℝ) N) := by
  dsimp only
  rw [←sourceEnergyTilt_eq _ _ _ (β:ℝ) N]
  have hi := sourceLogEnergyWeight_integrable (β:ℝ) β.coe_nonneg hd ρ M hM hρ hpair N
  unfold sourceLogSingularGibbs Measure.tilted
  apply withDensity_congr_ae
  filter_upwards [sourceLogSingularWeight_ae β hd ρ N] with x hx
  rw [hx,sourceLogSingularPartition_eq_integral β hd ρ M hM hρ hpair N]
  exact (ENNReal.ofReal_div_of_pos (integral_exp_pos hi)).symm

lemma sourceLogSingularGibbs_probability (β : ℝ≥0)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) (N : ℕ) :
    IsProbabilityMeasure (sourceLogSingularGibbs β ρ N) := by
  rw [sourceLogSingularGibbs_eq β hd ρ M hM hρ hpair N,←sourceEnergyTilt_eq _ _ _ (β:ℝ) N]
  exact isProbabilityMeasure_tilted
    (sourceLogEnergyWeight_integrable (β:ℝ) β.coe_nonneg hd ρ M hM hρ hpair N)

lemma sourceLogSingularPartition_real_tendsto (β : ℝ≥0)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) (z : ℝ)
    (hz : let μ := gaussianRieszDensityMeasure ρ
      let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
      Tendsto (fun N=>∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp (-(β:ℝ)*(N:ℝ)*
        sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
          (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x)
        ∂Measure.pi (fun _ : Fin N=>μ)) atTop (𝓝 z)) :
    Tendsto (fun N=>(sourceLogSingularPartition β ρ N).toReal) atTop (𝓝 z) := by
  apply hz.congr'
  apply Filter.Eventually.of_forall
  intro N
  dsimp only
  rw [sourceLogSingularPartition_eq_integral β hd ρ M hM hρ hpair N,
    ENNReal.toReal_ofReal (integral_nonneg fun x=>(Real.exp_pos _).le)]

end DGRHS.CLT
#check @DGRHS.CLT.sourceLogSingularGibbs_eq
#print axioms DGRHS.CLT.sourceLogEnergyWeight_integrable
#print axioms DGRHS.CLT.sourceLogSingularPartition_eq_integral
#print axioms DGRHS.CLT.sourceLogSingularPartition_pos_finite
#print axioms DGRHS.CLT.sourceLogSingularGibbs_eq
#print axioms DGRHS.CLT.sourceLogSingularGibbs_probability
#print axioms DGRHS.CLT.sourceLogSingularPartition_real_tendsto
