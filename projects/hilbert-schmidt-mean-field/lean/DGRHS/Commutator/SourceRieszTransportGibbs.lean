import DGRHS.Commutator.SourceRieszAllBetaBootstrap
import DGRHS.CLT.SourceRieszSingularGibbs

/-! Original positive-Riesz transport exponential moment under the literal
singular Gibbs law. The all-temperature numerator and the Jensen lower
normalizer are proved physical inputs, not hypotheses. Source3318–3546,
original source SHA2566f52778d92aa534e2b5851ca0f6b0712dc56470259cb3efcb7146ac2384dac0c.
The entropy transfer is a separate downstream unit. -/
noncomputable section
open MeasureTheory
open scoped NNReal BigOperators
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Concentration
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma sourceRieszLocalParticleGibbs_eq (s β : ℝ) (hs : 0<s) (hβ : 0≤β)
    (hd : 2*s<(Fintype.card ι:ℝ)) (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (N : ℕ) (hN : 1≤N) :
    DGRHS.CLT.sourceRieszSingularGibbs s β ρ N=
      (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)).tilted
        (sourceRieszLocalParticleExponent ρ s β N) := by
  rw [DGRHS.CLT.sourceRieszSingularGibbs_eq s β hs hβ (by linarith) ρ M hM hρ N]
  congr 1
  funext ω
  exact (sourceRieszLocalParticleExponent_eq ρ s β N (by omega) ω).symm

/-- Both signs and every positive particle number, with the exact source
piecewise coefficient and the actual literal singular Gibbs law. -/
theorem sourceRieszTransport_Gibbs_moment (s M : ℝ) (n : ℕ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    ∃ C : ℝ,0<C ∧ ∀ σ : ℝ,|σ|≤1→∀ N : ℕ,1≤N→
      Integrable (fun ω=>Real.exp (σ*sourceRieszTransportEpsilon (ι:=ι) s M n K β*(N:ℝ)*
        sourceRieszLocalTransportEnergy ρ s n v N ω)) (DGRHS.CLT.sourceRieszSingularGibbs s β ρ N) ∧
      (∫ ω,Real.exp (σ*sourceRieszTransportEpsilon (ι:=ι) s M n K β*(N:ℝ)*
        sourceRieszLocalTransportEnergy ρ s n v N ω) ∂DGRHS.CLT.sourceRieszSingularGibbs s β ρ N)≤C := by
  obtain ⟨C,hC,hNum⟩ := sourceRieszTransport_allBeta_numerator s M n hs hd hM β hβ hv ρ hρ
  obtain ⟨Cp,hCp,hPart⟩ := sourceRieszLocalParticleWeight_uniform s β hs hβ.le hd ρ M hM hρ
  refine ⟨C,hC,?_⟩
  intro σ hσ N hN
  have hi := hNum σ hσ N hN
  have hp := hPart N hN
  rw [sourceRieszLocalParticleGibbs_eq s β hs hβ.le hd ρ M hM hρ N hN]
  let A := fun ω : Fin N→E=>σ*sourceRieszTransportEpsilon (ι:=ι) s M n K β*(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω
  have hSum (ω : Fin N→E) : sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω=
      sourceRieszLocalParticleExponent ρ s β N ω+A ω := by
    dsimp [sourceRieszTransportAllBetaExponent,A]
    ring
  have ht : Integrable (fun ω=>Real.exp (A ω))
      ((Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)).tilted (sourceRieszLocalParticleExponent ρ s β N)) := by
    apply (integrable_tilted_iff hp.1 _).mpr
    apply hi.1.congr
    exact ae_of_all _ fun ω=>by
      change Real.exp (sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω)=
        Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)*Real.exp (A ω)
      rw [hSum,Real.exp_add]
  refine ⟨ht,?_⟩
  change (∫ ω,Real.exp (A ω) ∂(Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)).tilted
    (sourceRieszLocalParticleExponent ρ s β N))≤C
  rw [integral_exp_tilted]
  change (∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω+A ω)
    ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))/(∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
    ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))≤C
  simp_rw [←hSum]
  have hdpos : 0<(∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
      ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) := by linarith [hp.2.1]
  apply (div_le_iff₀ hdpos).mpr
  exact hi.2.trans (le_mul_of_one_le_right hC.le hp.2.1)

lemma sourceRieszLocalTransportEnergy_eq_zero (ρ : E→ℝ) (s : ℝ) (n : ℕ)
    (hn : 1≤n) {v : E→E} (hv : LipschitzWith 0 v) (N : ℕ) (ω : Fin N→E) :
    sourceRieszLocalTransportEnergy ρ s n v N ω=0 := by
  have he : sourceRieszTransportKernel n s v=(fun _ : E×E=>0) := by
    funext p
    exact sourceRieszTransportKernel_eq_zero_of_lipschitz_zero s n (by omega) hv p
  simp [sourceRieszLocalTransportEnergy,he,hoeffdingCentered,DGRHS.centeredKernel,
    DGRHS.potential,DGRHS.secondPotential,DGRHS.interactionEnergy,
    DGRHS.CLT.sourceCanonicalModulatedEnergy,DGRHS.CanonicalVariance.normalizedOffDiagonalSum,
    DGRHS.CanonicalVariance.offDiagonalSum]

/-- Positive transport parameter including constant velocity. For K>0 the
parameter is precisely the original piecewise expression; K=0 uses one. -/
def sourceRieszPositiveTransportParameter (s M : ℝ) (n : ℕ) (K : ℝ≥0) (β : ℝ) : ℝ :=
  if K=0 then 1 else sourceRieszTransportEpsilon (ι:=ι) s M n K β

lemma sourceRieszPositiveTransportParameter_pos (s M : ℝ) (n : ℕ) (K : ℝ≥0)
    (β : ℝ) (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (hβ : 0<β) :
    0<sourceRieszPositiveTransportParameter (ι:=ι) s M n K β := by
  unfold sourceRieszPositiveTransportParameter
  split_ifs with hk
  · norm_num
  · exact sourceRieszTransportEpsilon_pos s M n K β hs (by linarith) hM
      (NNReal.coe_pos.mpr (lt_of_le_of_ne (show (0:ℝ≥0)≤K from bot_le) (Ne.symm hk))) hβ

theorem sourceRieszTransport_positive_Gibbs_moment (s M : ℝ) (n : ℕ) (hn : 1≤n)
    (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    0<sourceRieszPositiveTransportParameter (ι:=ι) s M n K β ∧
    ∃ C : ℝ,0<C ∧ ∀ σ : ℝ,|σ|≤1→∀ N : ℕ,1≤N→
      Integrable (fun ω=>Real.exp (σ*sourceRieszPositiveTransportParameter (ι:=ι) s M n K β*(N:ℝ)*
        sourceRieszLocalTransportEnergy ρ s n v N ω)) (DGRHS.CLT.sourceRieszSingularGibbs s β ρ N) ∧
      (∫ ω,Real.exp (σ*sourceRieszPositiveTransportParameter (ι:=ι) s M n K β*(N:ℝ)*
        sourceRieszLocalTransportEnergy ρ s n v N ω) ∂DGRHS.CLT.sourceRieszSingularGibbs s β ρ N)≤C := by
  refine ⟨sourceRieszPositiveTransportParameter_pos s M n K β hs hd hM hβ,?_⟩
  by_cases hk : K=0
  · have hv0 : LipschitzWith 0 v := by simpa only [hk] using hv
    refine ⟨1,by norm_num,?_⟩
    intro σ hσ N hN
    letI := DGRHS.CLT.sourceRieszSingularGibbs_probability s β hs hβ.le (by linarith) ρ M hM hρ N
    simp only [sourceRieszLocalTransportEnergy_eq_zero ρ s n hn hv0, mul_zero,Real.exp_zero]
    exact ⟨integrable_const 1,by simp⟩
  · simpa only [sourceRieszPositiveTransportParameter,ite_eq_right hk] using
      sourceRieszTransport_Gibbs_moment s M n hs hd hM β hβ hv ρ hρ

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszLocalParticleGibbs_eq
#print axioms DGRHS.Commutator.sourceRieszLocalParticleGibbs_eq
#check @DGRHS.Commutator.sourceRieszTransport_Gibbs_moment
#print axioms DGRHS.Commutator.sourceRieszTransport_Gibbs_moment
#check @DGRHS.Commutator.sourceRieszLocalTransportEnergy_eq_zero
#print axioms DGRHS.Commutator.sourceRieszLocalTransportEnergy_eq_zero
#check @DGRHS.Commutator.sourceRieszPositiveTransportParameter
#print axioms DGRHS.Commutator.sourceRieszPositiveTransportParameter
#check @DGRHS.Commutator.sourceRieszPositiveTransportParameter_pos
#print axioms DGRHS.Commutator.sourceRieszPositiveTransportParameter_pos
#check @DGRHS.Commutator.sourceRieszTransport_positive_Gibbs_moment
#print axioms DGRHS.Commutator.sourceRieszTransport_positive_Gibbs_moment
