import DGRHS.Commutator.SourceRieszExtendedTransport
import DGRHS.Entropy.GibbsExtendedRewrite

/-! Genuine extended physical positive-Riesz free energy and an all-law
absolute transport bound. Infinity in KL or shifted energy is retained.
The physical source exponent and literal singular Gibbs law are the SAME
objects as in the finite-domain sharp entropic commutator. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def sourceRieszTransportExtendedFreeEnergy (ρ : E→ℝ) (s M β : ℝ) (N : ℕ)
    (ν : Measure (Fin N→E)) : EReal :=
  DGRHS.Entropy.gibbsExtendedFreeEnergy
    (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) ν
    (sourceRieszLocalParticleExponent ρ s β N)
    (β*(N:ℝ)*gaussianRieszPhysicalPotentialConstant s M ι)*((β*(N:ℝ))⁻¹:ℝ)

lemma sourceRieszTransportExtendedFreeEnergy_rewrite (s M : ℝ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β)
    (ρ : E→ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (N : ℕ) (hN : 1≤N)
    (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν] :
    sourceRieszTransportExtendedFreeEnergy ρ s M β N ν=
      ((klDiv ν (DGRHS.CLT.sourceRieszSingularGibbs s β ρ N):EReal)-
        (Real.log (∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
          ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)):ℝ))*((β*(N:ℝ))⁻¹:ℝ) := by
  obtain ⟨Cpf,hCpf,hPart⟩ := sourceRieszLocalParticleWeight_uniform s β hs hβ.le hd ρ M hM hρ
  have hcap (ω : Fin N→E) : sourceRieszLocalParticleExponent ρ s β N ω≤
      β*(N:ℝ)*gaussianRieszPhysicalPotentialConstant s M ι := by
    rw [sourceRieszLocalParticleExponent_background]
    have h := sourceRieszTransportBackgroundEnergy_lower s M hs hd hM ρ hρ N hN ω
    nlinarith [mul_le_mul_of_nonpos_left h (show -β≤0 by linarith)]
  unfold sourceRieszTransportExtendedFreeEnergy
  rw [DGRHS.Entropy.gibbsExtendedFreeEnergy_rewrite _ ν _ _ hcap (hPart N hN).1,
    ←sourceRieszLocalParticleGibbs_eq s β hs hβ.le hd ρ M hM hρ N hN]

/-- Every probability competitor, including infinite Gibbs KL, with a
nonnegative Lebesgue integral. The absolute observable costs log2, whereas
sourceRieszTransport_finiteKL_entropic keeps the sharp signed constant. -/
theorem sourceRieszTransport_allLaw_extendedFreeEnergy (s M : ℝ) (n : ℕ) (hn : 1≤n)
    (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    0<sourceRieszPositiveTransportParameter (ι:=ι) s M n K β ∧
    ∃ Cpf Cem : ℝ,1≤Cpf ∧ 1≤Cem ∧ ∀ N : ℕ,1≤N→
      ∀ (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν],
      ((∫⁻ ω,ENNReal.ofReal |(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω| ∂ν):EReal)≤
        ((β/sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)*(N:ℝ):ℝ)*
          sourceRieszTransportExtendedFreeEnergy ρ s M β N ν+
        ((sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)⁻¹*(Real.log Cpf+Real.log (2*Cem)):ℝ) := by
  obtain ⟨hε,Cem,hCem,hAbs⟩ := sourceRieszTransport_allLaw_absolute s M n hn hs hd hM β hβ hv ρ hρ
  obtain ⟨Cpf,hCpf,hPart⟩ := sourceRieszLocalParticleWeight_uniform s β hs hβ.le hd ρ M hM hρ
  refine ⟨hε,max Cpf 1,Cem,le_max_right _ _,hCem,?_⟩
  intro N hN ν hν
  let ε := sourceRieszPositiveTransportParameter (ι:=ι) s M n K β
  have hεlocal : 0<ε := hε
  have hb : 0<β*(N:ℝ) := mul_pos hβ (by exact_mod_cast (by omega : 0<N))
  have hc : 0<(β/ε)*(N:ℝ) := mul_pos (div_pos hβ hεlocal) (by exact_mod_cast (by omega : 0<N))
  have hcsource : 0<(β/sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)*(N:ℝ) := hc
  rw [sourceRieszTransportExtendedFreeEnergy_rewrite s M hs hd hM β hβ ρ hρ N hN ν]
  by_cases hKL : klDiv ν (DGRHS.CLT.sourceRieszSingularGibbs s β ρ N)=∞
  · simpa only [hKL,EReal.coe_ennreal_top,EReal.top_sub_coe,
      EReal.top_mul_coe_of_pos (inv_pos.mpr hb),EReal.coe_mul_top_of_pos hcsource,EReal.top_add_coe] using
      (le_top : ((∫⁻ ω,ENNReal.ofReal |(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω| ∂ν):EReal)≤(⊤:EReal))
  · have ha := hAbs N hN ν
    rw [←EReal.coe_ennreal_toReal hKL,←EReal.coe_mul,←EReal.coe_add] at ha
    rw [←EReal.coe_ennreal_toReal hKL,←EReal.coe_sub,←EReal.coe_mul,←EReal.coe_mul,←EReal.coe_add]
    apply ha.trans
    apply EReal.coe_le_coe_iff.mpr
    let Z := ∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
      ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)
    have hZpos : 0<Z := by dsimp only [Z];linarith [(hPart N hN).2.1]
    have hZcap : Z≤max Cpf 1 := (hPart N hN).2.2.trans (le_max_left _ _)
    have hlog := Real.log_le_log hZpos hZcap
    have halgebra : (β/ε)*(N:ℝ)*
        (((klDiv ν (DGRHS.CLT.sourceRieszSingularGibbs s β ρ N)).toReal-Real.log Z)*(β*(N:ℝ))⁻¹)+
          ε⁻¹*(Real.log (max Cpf 1)+Real.log (2*Cem))=
        ε⁻¹*(klDiv ν (DGRHS.CLT.sourceRieszSingularGibbs s β ρ N)).toReal+
          ε⁻¹*Real.log (2*Cem)+ε⁻¹*(Real.log (max Cpf 1)-Real.log Z) := by
      field_simp [hβ.ne',hεlocal.ne',(show (N:ℝ)≠0 by exact_mod_cast (by omega : N≠0))]
      <;> ring
    change ε⁻¹*(klDiv ν (DGRHS.CLT.sourceRieszSingularGibbs s β ρ N)).toReal+ε⁻¹*Real.log (2*Cem)≤_
    rw [halgebra]
    exact le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr hεlocal.le) (sub_nonneg.mpr hlog))

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszTransportExtendedFreeEnergy
#print axioms DGRHS.Commutator.sourceRieszTransportExtendedFreeEnergy
#check @DGRHS.Commutator.sourceRieszTransportExtendedFreeEnergy_rewrite
#print axioms DGRHS.Commutator.sourceRieszTransportExtendedFreeEnergy_rewrite
#check @DGRHS.Commutator.sourceRieszTransport_allLaw_extendedFreeEnergy
#print axioms DGRHS.Commutator.sourceRieszTransport_allLaw_extendedFreeEnergy
