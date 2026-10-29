import DGRHS.Commutator.SourceRieszLocalEmpirical
import DGRHS.Concentration.SourceRieszRate

/-! Actual positive-Riesz source particle weights: proper all-temperature
uniform moments and the genuine Jensen lower bound, derived from physical
data. This is the partition ingredient for the local Hölder bootstrap. -/
noncomputable section
open MeasureTheory
open scoped NNReal BigOperators
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Concentration
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def sourceRieszLocalParticleExponent (ρ : E→ℝ) (s β : ℝ) (N : ℕ) (ω : Fin N→E) : ℝ :=
  -β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy
    (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
    (sourceRieszLocalPhysicalPotential ρ s) (sourceRieszLocalPhysicalEnergy ρ s) N ω

lemma sourceRieszLocalParticleExponent_eq (ρ : E→ℝ) (s β : ℝ) (N : ℕ) (hN : 0<N) (ω : Fin N→E) :
    sourceRieszLocalParticleExponent ρ s β N ω=
      DGRHS.CLT.sourceParticleExponent (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
        (sourceRieszLocalPhysicalPotential ρ s) (sourceRieszLocalPhysicalEnergy ρ s) β N ω :=
  DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent _ _ _ β hN ω

lemma measurable_sourceRieszLocalParticleExponent (ρ : E→ℝ) (s β : ℝ) (N : ℕ) (hN : 0<N)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    Measurable (sourceRieszLocalParticleExponent ρ s β N) := by
  let μ := gaussianRieszDensityMeasure ρ
  have hE := measurable_physical_iidNegativeStatistic N _
    (stronglyMeasurable_hoeffdingCentered μ _ (stronglyMeasurable_gaussianRieszPhysicalPair s)).measurable
  have hF : Measurable (sourceRieszLocalPhysicalPotential ρ s) :=
    (stronglyMeasurable_gaussianRieszPhysicalPair s).integral_prod_right'.measurable
  have hSum : Measurable (fun ω : Fin N→E=>∑ i : Fin N,sourceRieszLocalPhysicalPotential ρ s (ω i)) :=
    Finset.measurable_sum _ (fun i _=>hF.comp (measurable_pi_apply i))
  have hm : Measurable (fun ω : Fin N→E=>β*iidNegativeStatistic N (hoeffdingCentered μ (gaussianRieszPhysicalPair s)) ω+
      β*((N:ℝ)⁻¹*∑ i : Fin N,sourceRieszLocalPhysicalPotential ρ s (ω i))-β*sourceRieszLocalPhysicalEnergy ρ s) :=
    ((hE.const_mul β).add ((hSum.const_mul (N:ℝ)⁻¹).const_mul β)).sub_const _
  convert hm using 1
  funext ω
  rw [sourceRieszLocalParticleExponent_eq ρ s β N hN]
  unfold DGRHS.CLT.sourceParticleExponent
  rw [←sourceRieszLocal_energy_normalization β]

/-- Genuine source lower normalizer bound. No lower partition premise. -/
lemma sourceRieszLocalParticleWeight_lower (s β : ℝ) (hs : 0<s) (hβ : 0≤β)
    (hd : 2*s<(Fintype.card ι:ℝ)) (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (N : ℕ) (hN : 1≤N)
    (hi : Integrable (fun ω=>Real.exp (sourceRieszLocalParticleExponent ρ s β N ω))
      (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))) :
    1≤∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
      ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ) := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun x y : E=>gaussianRieszPhysicalPair s (x,y)
  let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  let F := sourceRieszLocalPhysicalPotential ρ s
  let I := sourceRieszLocalPhysicalEnergy ρ s
  have hn : 0<N := lt_of_lt_of_le (by norm_num : (0:ℕ)<1) hN
  have hpair := (memLp_gaussianRieszPhysicalPair s hs (by linarith) ρ M hM hρ).integrable (by norm_num)
  have hh := memLp_gaussianRieszCenteredPhysicalPair s hs (by linarith) ρ M hM hρ
  have hc := DGRHS.integral_centeredKernel_right μ W hpair
  have hF := memLp_gaussianRieszPhysicalPotential s hs (by linarith) ρ M hM hρ
  have hX : Integrable (fun ω : Fin N→E=>Real.exp (DGRHS.CLT.sourceParticleExponent h F I β N ω))
      (Measure.pi (fun _ : Fin N=>μ)) := by
    convert hi using 1
    funext ω
    rw [sourceRieszLocalParticleExponent_eq ρ s β N hn]
  have hl := sourceAffinePartition_lower μ β I h hh hc F hF N hN hX
  have hmean : β*(∫ x,F x ∂μ)-β*I=β*I := by
    change β*(∫ x,DGRHS.potential μ W x ∂μ)-β*DGRHS.interactionEnergy μ W=β*DGRHS.interactionEnergy μ W
    rw [DGRHS.integral_potential μ W hpair]
    ring
  rw [hmean] at hl
  have hI : 0≤I := by dsimp[I,sourceRieszLocalPhysicalEnergy];apply mul_nonneg (by norm_num);exact integral_nonneg (fun p=>by unfold gaussianRieszPhysicalPair;positivity)
  have h1 : 1≤Real.exp (β*I) := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (mul_nonneg hβ hI)
  have hb := h1.trans hl
  change 1≤∫ ω : Fin N→E,Real.exp (DGRHS.CLT.sourceParticleExponent h F I β N ω) ∂Measure.pi (fun _ : Fin N=>μ) at hb
  convert hb using 1
  congr 1
  funext ω
  rw [sourceRieszLocalParticleExponent_eq ρ s β N hn]

/-- A real finite constant, common to all positive N, at each actual β≥0. -/
theorem sourceRieszLocalParticleWeight_uniform (s β : ℝ) (hs : 0<s) (hβ : 0≤β)
    (hd : 2*s<(Fintype.card ι:ℝ)) (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,1≤N→
      Integrable (fun ω=>Real.exp (sourceRieszLocalParticleExponent ρ s β N ω))
        (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) ∧
      1≤(∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))≤C := by
  obtain ⟨C,hC⟩ := gaussianRieszPhysical_uniform_exponential s β hs hβ (by linarith) ρ M hM hρ
  let B := Real.exp (β*gaussianRieszPhysicalPotentialConstant s M ι)
  refine ⟨B*max C 1,by dsimp[B];positivity,?_⟩
  intro N hN
  have hn : 0<N := lt_of_lt_of_le (by norm_num : (0:ℕ)<1) hN
  obtain ⟨hi,hb⟩ := hC N hN
  have hpoint (ω : Fin N→E) : Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)≤
      B*Real.exp (β*iidNegativeStatistic N (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s)) ω) := by
    dsimp[B]
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [sourceRieszLocalParticleExponent_eq ρ s β N hn]
    unfold DGRHS.CLT.sourceParticleExponent
    rw [←sourceRieszLocal_energy_normalization β]
    have hbody := sourceRieszLocal_oneBody_bound ρ s M β hs (by linarith) hM hβ hρ N hN ω
    linarith
  have hiW : Integrable (fun ω=>Real.exp (sourceRieszLocalParticleExponent ρ s β N ω))
      (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) :=
    (hi.const_mul B).mono' (Real.measurable_exp.comp (measurable_sourceRieszLocalParticleExponent ρ s β N hn)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω=>by rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)];exact hpoint ω))
  refine ⟨hiW,sourceRieszLocalParticleWeight_lower s β hs hβ hd ρ M hM hρ N hN hiW,?_⟩
  calc
    _ ≤ ∫ ω,B*Real.exp (β*iidNegativeStatistic N (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s)) ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ) := integral_mono_ae hiW (hi.const_mul B) (Filter.Eventually.of_forall hpoint)
    _ = B*(∫ ω,Real.exp (β*iidNegativeStatistic N (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s)) ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) := integral_const_mul _ _
    _ ≤ B*C := mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left C 1) (Real.exp_pos _).le

end DGRHS.Commutator

#check DGRHS.Commutator.sourceRieszLocalParticleExponent
#print axioms DGRHS.Commutator.sourceRieszLocalParticleExponent

#check DGRHS.Commutator.sourceRieszLocalParticleExponent_eq
#print axioms DGRHS.Commutator.sourceRieszLocalParticleExponent_eq

#check DGRHS.Commutator.measurable_sourceRieszLocalParticleExponent
#print axioms DGRHS.Commutator.measurable_sourceRieszLocalParticleExponent

#check DGRHS.Commutator.sourceRieszLocalParticleWeight_lower
#print axioms DGRHS.Commutator.sourceRieszLocalParticleWeight_lower

#check DGRHS.Commutator.sourceRieszLocalParticleWeight_uniform
#print axioms DGRHS.Commutator.sourceRieszLocalParticleWeight_uniform
