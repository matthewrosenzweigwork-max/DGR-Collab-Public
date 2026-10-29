import DGRHS.Commutator.SourceRieszCommonGibbs
import DGRHS.Commutator.SourceRieszTransportFreeEnergyIdentification

/-! Common-family finite-KL and extended absolute Riesz entropic estimates.
Constants are selected before the velocity, density, sign, N or competitor.
Finite Gibbs KL derives properness; infinite KL is retained in EReal. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Sharp signed forcing uses logCem, with genuine finite-KL properness. -/
theorem sourceRieszCommon_finiteKL_entropic (s M : ℝ) (n : ℕ) (hn : 1≤n)
    (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β) :
    ∃ Cpf Cem : ℝ,1≤Cpf ∧ 1≤Cem ∧ ∀ (K : ℝ≥0) (v : E→E),LipschitzWith K v →
      0<sourceRieszPositiveTransportParameter (ι:=ι) s M n K β ∧
      ∀ ρ : E→ℝ,IsProbabilityMeasure (gaussianRieszDensityMeasure ρ) →
      (∀ᵐ x ∂volume,ρ x≤M) → ∀ N : ℕ,1≤N→
      ∀ (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν],
      klDiv ν (DGRHS.CLT.sourceRieszSingularGibbs s β ρ N)≠∞→
      ν ≪ Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ) ∧
      Integrable (sourceRieszTransportBackgroundEnergy ρ s N) ν ∧
      Integrable (llr ν (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))) ν ∧
      Integrable (fun ω=>(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω) ν ∧
      |∫ ω,(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω ∂ν|≤
        (β/sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)*(N:ℝ)*
          sourceRieszTransportProperFreeEnergy ρ s β N ν+
        (sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)⁻¹*(Real.log Cpf+Real.log Cem) := by
  obtain ⟨Cem,hCem,hFamily⟩ := sourceRieszCommon_Gibbs_moment (ι:=ι) s M n hn hs hd hM β hβ
  obtain ⟨Cpf,hCpf,hPartFamily⟩ := sourceRieszCommon_particle_moment (ι:=ι) s β M hs hβ.le hM hd
  refine ⟨max Cpf 1,max Cem 1,le_max_right _ _,le_max_right _ _,?_⟩
  intro K v hv
  obtain ⟨hε,hFam⟩ := hFamily K v hv
  refine ⟨hε,?_⟩
  intro ρ hprob hρ
  let _ := hprob
  have hMom := hFam ρ hprob hρ
  have hPart := hPartFamily ρ hprob hρ
  intro N hN ν hν hKL
  let P := Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)
  let Ebg := sourceRieszTransportBackgroundEnergy ρ s N
  let a := fun ω : Fin N→E=>(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω
  let ε := sourceRieszPositiveTransportParameter (ι:=ι) s M n K β
  have hQ : DGRHS.CLT.sourceRieszSingularGibbs s β ρ N=P.tilted (fun ω=>-β*Ebg ω) := by
    rw [sourceRieszLocalParticleGibbs_eq s β hs hβ.le hd ρ M hM hρ N hN]
    congr 1
    funext ω
    exact sourceRieszLocalParticleExponent_background ρ s β N ω
  have hp := hMom 1 (by norm_num) N hN
  have hm := hMom (-1) (by norm_num) N hN
  rw [hQ] at hp hm hKL
  have hp' : Integrable (fun ω=>Real.exp (ε*a ω)) (P.tilted (fun ω=>-β*Ebg ω)) := by
    convert hp.1 using 1
    funext ω
    dsimp [ε,a]
    ring_nf
  have hm' : Integrable (fun ω=>Real.exp (-(ε*a ω))) (P.tilted (fun ω=>-β*Ebg ω)) := by
    convert hm.1 using 1
    funext ω
    dsimp [ε,a]
    ring_nf
  have hpbound : (∫ ω,Real.exp (ε*a ω) ∂P.tilted (fun ω=>-β*Ebg ω))≤max Cem 1 := by
    convert hp.2.trans (le_max_left _ _) using 1
    congr 1
    funext ω
    dsimp [ε,a]
    ring_nf
  have hmbound : (∫ ω,Real.exp (-(ε*a ω)) ∂P.tilted (fun ω=>-β*Ebg ω))≤max Cem 1 := by
    convert hm.2.trans (le_max_left _ _) using 1
    congr 1
    funext ω
    dsimp [ε,a]
    ring_nf
  have hz : Integrable (fun ω=>Real.exp (-β*Ebg ω)) P := by
    simpa only [sourceRieszLocalParticleExponent_background] using (hPart N hN).1
  have hzb : (∫ ω,Real.exp (-β*Ebg ω) ∂P)≤max Cpf 1 := by
    simpa only [sourceRieszLocalParticleExponent_background] using (hPart N hN).2.2.trans (le_max_left _ _)
  obtain ⟨hac,he,hllr,ha,hb⟩ := DGRHS.Entropy.gibbs_entropic_transfer P ν Ebg
    (-(N:ℝ)*gaussianRieszPhysicalPotentialConstant s M ι) β hβ
    (sourceRieszTransportBackgroundEnergy_lower s M hs hd hM ρ hρ N hN) hz a
    (measurable_sourceRieszScaledTransportEnergy ρ s n hv N hN).stronglyMeasurable ε hε
    hp' hm' hKL (max Cpf 1) (max Cem 1) hzb hpbound hmbound
  refine ⟨hac,he,hllr,ha,?_⟩
  have hNreal : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have halgebra : (β/ε)*(N:ℝ)*sourceRieszTransportProperFreeEnergy ρ s β N ν=
      ε⁻¹*((klDiv ν P).toReal+β*(∫ ω,Ebg ω ∂ν)) := by
    unfold sourceRieszTransportProperFreeEnergy
    dsimp only [P,Ebg]
    field_simp [hβ.ne',hε.ne',hNreal]
  rw [halgebra]
  exact hb


/-- Genuine all-law absolute Lebesgue integral; log2 is kept separately. -/
theorem sourceRieszCommon_allLaw_absolute (s M : ℝ) (n : ℕ) (hn : 1≤n)
    (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β) :
    ∃ C : ℝ,1≤C ∧ ∀ (K : ℝ≥0) (v : E→E),LipschitzWith K v →
      0<sourceRieszPositiveTransportParameter (ι:=ι) s M n K β ∧
      ∀ ρ : E→ℝ,IsProbabilityMeasure (gaussianRieszDensityMeasure ρ) →
      (∀ᵐ x ∂volume,ρ x≤M) → ∀ N : ℕ,1≤N→
      ∀ (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν],
      ((∫⁻ ω,ENNReal.ofReal |(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω| ∂ν):EReal)≤
        ((sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)⁻¹:ℝ)*
          (klDiv ν (DGRHS.CLT.sourceRieszSingularGibbs s β ρ N):EReal)+
        ((sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)⁻¹*Real.log (2*C):ℝ) := by
  obtain ⟨C,hC,hFamily⟩ := sourceRieszCommon_Gibbs_moment (ι:=ι) s M n hn hs hd hM β hβ
  refine ⟨max C 1,le_max_right _ _,?_⟩
  intro K v hv
  obtain ⟨hε,hFam⟩ := hFamily K v hv
  refine ⟨hε,?_⟩
  intro ρ hprob hρ
  let _ := hprob
  have hMom := hFam ρ hprob hρ
  intro N hN ν hν
  let ε := sourceRieszPositiveTransportParameter (ι:=ι) s M n K β
  have hεlocal : 0<ε := hε
  let Q := DGRHS.CLT.sourceRieszSingularGibbs s β ρ N
  let a := fun ω : Fin N→E=>(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω
  let u := fun ω=>ε*a ω
  change ((∫⁻ ω,ENNReal.ofReal |a ω| ∂ν):EReal)≤
    (ε⁻¹:ℝ)*(klDiv ν Q:EReal)+(ε⁻¹*Real.log (2*max C 1):ℝ)
  by_cases hfinite : klDiv ν Q≠∞
  · letI := DGRHS.CLT.sourceRieszSingularGibbs_probability s β hs hβ.le (by linarith) ρ M hM hρ N
    have hu : StronglyMeasurable u :=
      (measurable_sourceRieszScaledTransportEnergy ρ s n hv N hN).stronglyMeasurable.const_mul ε
    have hp := hMom 1 (by norm_num) N hN
    have hm := hMom (-1) (by norm_num) N hN
    have heP (ω : Fin N→E) :
        1*sourceRieszPositiveTransportParameter (ι:=ι) s M n K β*(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω=u ω := by dsimp [u,a,ε];ring
    have heM (ω : Fin N→E) :
        (-1)*sourceRieszPositiveTransportParameter (ι:=ι) s M n K β*(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω= -u ω := by dsimp [u,a,ε];ring
    simp_rw [heP] at hp
    simp_rw [heM] at hm
    have hx := DGRHS.Entropy.integrable_exp_abs_of_two_signs Q u hu hp.1 hm.1
    have hpoint (ω : Fin N→E) : Real.exp |u ω|≤Real.exp (u ω)+Real.exp (-u ω) := by
      by_cases h : 0≤u ω
      · rw [abs_of_nonneg h]
        exact le_add_of_nonneg_right (Real.exp_pos _).le
      · rw [abs_of_neg (lt_of_not_ge h)]
        exact le_add_of_nonneg_left (Real.exp_pos _).le
    have hb : (∫ ω,Real.exp |u ω| ∂Q)≤2*max C 1 := by
      calc
        _ ≤ ∫ ω,Real.exp (u ω)+Real.exp (-u ω) ∂Q := integral_mono hx (hp.1.add hm.1) hpoint
        _ = (∫ ω,Real.exp (u ω) ∂Q)+(∫ ω,Real.exp (-u ω) ∂Q) := integral_add hp.1 hm.1
        _ ≤ 2*max C 1 := by linarith [hp.2,hm.2,le_max_left C 1]
    obtain ⟨hi,hbound⟩ := DGRHS.Entropy.entropy_integrable_abs_of_exponential Q ν u hu hx hfinite
    have hia : Integrable a ν := by
      have h := hi.const_mul ε⁻¹
      simpa only [u,←mul_assoc,inv_mul_cancel₀ hεlocal.ne',one_mul] using h
    have huabs (ω : Fin N→E) : |u ω|=ε*|a ω| := by
      dsimp only [u]
      rw [abs_mul,abs_of_pos hε]
    have hInt : (∫ ω,|u ω| ∂ν)=ε*(∫ ω,|a ω| ∂ν) := by
      simp_rw [huabs]
      exact integral_const_mul _ _
    rw [hInt] at hbound
    have hlog := Real.log_le_log (integral_exp_pos hx) hb
    have hbound' : (∫ ω,|a ω| ∂ν)≤ε⁻¹*((klDiv ν Q).toReal+Real.log (2*max C 1)) := by
      have ht := hbound.trans (add_le_add le_rfl hlog)
      have h : (∫ ω,|a ω| ∂ν)≤((klDiv ν Q).toReal+Real.log (2*max C 1))/ε :=
        (le_div_iff₀ hεlocal).mpr (by simpa only [mul_comm] using ht)
      simpa only [div_eq_mul_inv,mul_comm] using h
    rw [←ofReal_integral_eq_lintegral_ofReal hia.abs (ae_of_all _ fun ω=>abs_nonneg _),
      EReal.coe_ennreal_ofReal,max_eq_left (integral_nonneg (fun ω=>abs_nonneg _)),
      ←EReal.coe_ennreal_toReal hfinite,←EReal.coe_mul,←EReal.coe_add]
    apply EReal.coe_le_coe_iff.mpr
    simpa only [mul_add] using hbound'
  · have htop : klDiv ν Q=∞ := not_ne_iff.mp hfinite
    rw [htop,EReal.coe_ennreal_top,EReal.coe_mul_top_of_pos (inv_pos.mpr hε),EReal.top_add_coe]
    exact le_top


/-- Same physical extended free energy, for every probability competitor. -/
theorem sourceRieszCommon_allLaw_extendedFreeEnergy (s M : ℝ) (n : ℕ) (hn : 1≤n)
    (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β) :
    ∃ Cpf Cem : ℝ,1≤Cpf ∧ 1≤Cem ∧ ∀ (K : ℝ≥0) (v : E→E),LipschitzWith K v →
      0<sourceRieszPositiveTransportParameter (ι:=ι) s M n K β ∧
      ∀ ρ : E→ℝ,IsProbabilityMeasure (gaussianRieszDensityMeasure ρ) →
      (∀ᵐ x ∂volume,ρ x≤M) → ∀ N : ℕ,1≤N→
      ∀ (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν],
      ((∫⁻ ω,ENNReal.ofReal |(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω| ∂ν):EReal)≤
        ((β/sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)*(N:ℝ):ℝ)*
          sourceRieszTransportExtendedFreeEnergy ρ s M β N ν+
        ((sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)⁻¹*(Real.log Cpf+Real.log (2*Cem)):ℝ) := by
  obtain ⟨Cem,hCem,hAbsFamily⟩ := sourceRieszCommon_allLaw_absolute (ι:=ι) s M n hn hs hd hM β hβ
  obtain ⟨Cpf,hCpf,hPartFamily⟩ := sourceRieszCommon_particle_moment (ι:=ι) s β M hs hβ.le hM hd
  refine ⟨max Cpf 1,Cem,le_max_right _ _,hCem,?_⟩
  intro K v hv
  obtain ⟨hε,hFam⟩ := hAbsFamily K v hv
  refine ⟨hε,?_⟩
  intro ρ hprob hρ
  let _ := hprob
  have hAbs := hFam ρ hprob hρ
  have hPart := hPartFamily ρ hprob hρ
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
#check @DGRHS.Commutator.sourceRieszCommon_finiteKL_entropic
#print axioms DGRHS.Commutator.sourceRieszCommon_finiteKL_entropic
#check @DGRHS.Commutator.sourceRieszCommon_allLaw_absolute
#print axioms DGRHS.Commutator.sourceRieszCommon_allLaw_absolute
#check @DGRHS.Commutator.sourceRieszCommon_allLaw_extendedFreeEnergy
#print axioms DGRHS.Commutator.sourceRieszCommon_allLaw_extendedFreeEnergy
