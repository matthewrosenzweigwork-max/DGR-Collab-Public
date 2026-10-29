import DGRHS.Commutator.SourceRieszLocalEnergy

/-! Actual signed local numerator: literal transport energy and actual source
modulated energy, with the one-body correction derived rather than supplied.
The empirical offcollision integral adapter is a separate exact identity. -/
noncomputable section
open MeasureTheory
open scoped NNReal BigOperators
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Concentration
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def sourceRieszLocalNumeratorExponent (ρ : E→ℝ) (s : ℝ) (n : ℕ) (γ σ : ℝ)
    (K : ℝ≥0) (v : E→E) (N : ℕ) (ω : Fin N→E) : ℝ :=
  σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ*(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω-
    γ*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
      (sourceRieszLocalPhysicalPotential ρ s) (sourceRieszLocalPhysicalEnergy ρ s) N ω

lemma sourceRieszLocalNumeratorExponent_eq (ρ : E→ℝ) (s M : ℝ) (n : ℕ) (γ σ : ℝ)
    (K : ℝ≥0) (v : E→E) (N : ℕ) (hN : 0<N) (ω : Fin N→E) :
    sourceRieszLocalNumeratorExponent ρ s n γ σ K v N ω=
      sourceRieszLocalExponent ρ s M n γ σ K v N ω-
      (3/4:ℝ)*γ*gaussianRieszPhysicalPotentialConstant s M ι+
      σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ*sourceRieszLocalTransportCorrection ρ s n v N ω := by
  have hE := DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent
    (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
    (sourceRieszLocalPhysicalPotential ρ s) (sourceRieszLocalPhysicalEnergy ρ s) γ hN ω
  unfold sourceRieszLocalNumeratorExponent
  rw [show σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ*(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω=
    σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ*((N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω) by ring,
    sourceRieszLocalTransportEnergy_scaled ρ s n v N hN]
  unfold sourceRieszLocalExponent DGRHS.CLT.sourceParticleExponent
  nlinarith [hE]

lemma measurable_sourceRieszLocalTransportCorrection (ρ : E→ℝ) (s : ℝ) (n : ℕ)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) (N : ℕ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    Measurable (sourceRieszLocalTransportCorrection ρ s n v N) := by
  have hF : Measurable (fun x : E=>∫ y,sourceRieszTransportKernel n s v (x,y) ∂gaussianRieszDensityMeasure ρ) :=
    (measurable_sourceRieszTransportKernel s n hv).stronglyMeasurable.integral_prod_right'.measurable
  have hSum : Measurable (fun ω : Fin N→E=>∑ i : Fin N,∫ y,sourceRieszTransportKernel n s v (ω i,y) ∂gaussianRieszDensityMeasure ρ) :=
    Finset.measurable_sum _ (fun i _=>hF.comp (measurable_pi_apply i))
  exact (hSum.const_mul _).add_const _

lemma measurable_sourceRieszLocalNumeratorExponent (ρ : E→ℝ) (s : ℝ) (n : ℕ) (γ σ : ℝ)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) (N : ℕ) (hN : 0<N)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    Measurable (sourceRieszLocalNumeratorExponent ρ s n γ σ K v N) := by
  have hm := ((measurable_sourceRieszLocalExponent ρ s 0 n γ σ hv N).sub_const
    ((3/4:ℝ)*γ*gaussianRieszPhysicalPotentialConstant s 0 ι)).add
      ((measurable_sourceRieszLocalTransportCorrection ρ s n hv N).const_mul (σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ))
  convert hm using 1
  funext ω
  exact sourceRieszLocalNumeratorExponent_eq ρ s 0 n γ σ K v N hN ω

lemma sourceRieszLocalNumeratorExponent_le (s : ℝ) (n : ℕ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) (γ σ : ℝ) (hγ : 0≤γ) (hσ : |σ|≤1)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (N : ℕ) (hN : 0<N) (ω : Fin N→E) :
    sourceRieszLocalNumeratorExponent ρ s n γ σ K v N ω≤sourceRieszLocalExponent ρ s M n γ σ K v N ω := by
  rw [sourceRieszLocalNumeratorExponent_eq ρ s M n γ σ K v N hN ω]
  have hb := sourceRieszLocalTransportCorrection_scaled_bound s n hs hd γ σ hγ hσ hv ρ M hM hρ N hN ω
  linarith

/-- Source local numerator, proper and uniform in every N≥1, with all
physical hypotheses only. The explicit sign parameter also covers even n. -/
theorem sourceRieszLocal_numerator (s : ℝ) (n : ℕ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) (γ σ : ℝ) (hγ : 0<γ) (hσ : |σ|≤1)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (N : ℕ) (hN : 1≤N)
    (hγb : γ≤sourceRieszLocalBeta (ι:=ι) s M) :
    Integrable (fun ω=>Real.exp (sourceRieszLocalNumeratorExponent ρ s n γ σ K v N ω))
      (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) ∧
    (∫ ω,Real.exp (sourceRieszLocalNumeratorExponent ρ s n γ σ K v N ω)
      ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))≤Real.exp 1+glzUniversalTailConstant := by
  obtain ⟨hXi,hBound⟩ := sourceRieszLocal_exponential_moment s n hs hd γ σ hγ hσ hv ρ M hM hρ N hN hγb
  have hn : 0<N := lt_of_lt_of_le (by norm_num : (0:ℕ)<1) hN
  have hpoint (ω : Fin N→E) : Real.exp (sourceRieszLocalNumeratorExponent ρ s n γ σ K v N ω)≤
      Real.exp (sourceRieszLocalExponent ρ s M n γ σ K v N ω) :=
    Real.exp_le_exp.mpr (sourceRieszLocalNumeratorExponent_le s n hs hd γ σ hγ.le hσ hv ρ M hM hρ N hn ω)
  have hi : Integrable (fun ω=>Real.exp (sourceRieszLocalNumeratorExponent ρ s n γ σ K v N ω))
      (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) :=
    hXi.mono' (Real.measurable_exp.comp (measurable_sourceRieszLocalNumeratorExponent ρ s n γ σ hv N hn)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω=>by rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)];exact hpoint ω))
  exact ⟨hi,(integral_mono_ae hi hXi (Filter.Eventually.of_forall hpoint)).trans hBound⟩

end DGRHS.Commutator

#check DGRHS.Commutator.sourceRieszLocalNumeratorExponent
#print axioms DGRHS.Commutator.sourceRieszLocalNumeratorExponent

#check DGRHS.Commutator.sourceRieszLocalNumeratorExponent_eq
#print axioms DGRHS.Commutator.sourceRieszLocalNumeratorExponent_eq

#check DGRHS.Commutator.measurable_sourceRieszLocalTransportCorrection
#print axioms DGRHS.Commutator.measurable_sourceRieszLocalTransportCorrection

#check DGRHS.Commutator.measurable_sourceRieszLocalNumeratorExponent
#print axioms DGRHS.Commutator.measurable_sourceRieszLocalNumeratorExponent

#check DGRHS.Commutator.sourceRieszLocalNumeratorExponent_le
#print axioms DGRHS.Commutator.sourceRieszLocalNumeratorExponent_le

#check DGRHS.Commutator.sourceRieszLocal_numerator
#print axioms DGRHS.Commutator.sourceRieszLocal_numerator
