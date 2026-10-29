import DGRHS.Commutator.SourceRieszCommonFiniteEnergy

/-! Source Theorem 2.8 (entropic commutator), positive Riesz branch `0<s<d/2`.

The exponential moment (2.21) holds for both signs with the printed
`Cem` of Remark A.1 (`e+L` for `β ≤ β_loc`, `(e+L)^{1/2} Cub^{1/2}` for
`β > β_loc`; the factor `e^{-β I_μ}` occurs only for `s=0`).  The entropic
inequality (2.22) is asserted for every probability law `ν` with finite
relative entropy to the literal Riesz Gibbs law (owner convention for
`0<s<d/2`; other laws are vacuous).  No totalized integral is used.
All providers are the checked common Riesz modules. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Concentration
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Printed constant `C_em` (Remark A.1, `0<s<d/2`). -/
def sourceRieszTransportCem (β βloc L Cub : ℝ) : ℝ :=
  if β ≤ βloc then Real.exp 1 + L else Real.sqrt (Real.exp 1 + L) * Real.sqrt Cub

lemma one_le_sourceRieszTransportCem (β βloc L Cub : ℝ) (hL : 0 ≤ L) (hCub : 1 ≤ Cub) :
    1 ≤ sourceRieszTransportCem β βloc L Cub := by
  have he : (2:ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1:ℝ)
    linarith
  unfold sourceRieszTransportCem
  split_ifs with h
  · linarith
  · have h1 : (1:ℝ) ≤ Real.sqrt (Real.exp 1 + L) := by
      calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt (Real.exp 1 + L) := Real.sqrt_le_sqrt (by linarith)
    have h2 : (1:ℝ) ≤ Real.sqrt Cub := by
      calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt Cub := Real.sqrt_le_sqrt hCub
    nlinarith [h1, h2]

/-- The literal singular partition at inverse temperature `β` equals the
physical particle integral (upper bound transfer). -/
lemma sourceRieszSingularPartition_toReal_le (s β : ℝ) (hs : 0<s) (hβ : 0≤β)
    (hd : 2*s<(Fintype.card ι:ℝ)) (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (N : ℕ) (C : ℝ)
    (h : (∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
      ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))≤C) :
    (DGRHS.CLT.sourceRieszSingularPartition s β ρ N).toReal≤C := by
  have hnonneg : 0≤DGRHS.Concentration.physicalRieszSourcePartition s β ρ N :=
    integral_nonneg fun _=>(Real.exp_pos _).le
  rw [DGRHS.CLT.sourceRieszSingularPartition_eq_integral s β hs hβ (by linarith) ρ M hM hρ N,
    ENNReal.toReal_ofReal hnonneg]
  exact h

lemma sourceRieszSingularPartition_toReal_ge (s β : ℝ) (hs : 0<s) (hβ : 0≤β)
    (hd : 2*s<(Fintype.card ι:ℝ)) (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (N : ℕ) (C : ℝ)
    (h : C≤(∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
      ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))) :
    C≤(DGRHS.CLT.sourceRieszSingularPartition s β ρ N).toReal := by
  have hnonneg : 0≤DGRHS.Concentration.physicalRieszSourcePartition s β ρ N :=
    integral_nonneg fun _=>(Real.exp_pos _).le
  rw [DGRHS.CLT.sourceRieszSingularPartition_eq_integral s β hs hβ (by linarith) ρ M hM hρ N,
    ENNReal.toReal_ofReal hnonneg]
  exact h

/-- Unnormalized all-temperature numerator with the printed `Cem`; the large
temperature remaining factor is the partition bound `Cub` at `2β-β_loc`. -/
theorem sourceRieszTransport_numerator_explicit (s M : ℝ) (n : ℕ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β) (Cub : ℝ)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpart : sourceRieszLocalBeta (ι:=ι) s M<β → ∀ N : ℕ,1≤N→
      Integrable (fun ω=>Real.exp (sourceRieszLocalParticleExponent ρ s
        (2*β-sourceRieszLocalBeta (ι:=ι) s M) N ω))
        (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s
        (2*β-sourceRieszLocalBeta (ι:=ι) s M) N ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))≤Cub) :
    ∀ σ : ℝ,|σ|≤1→∀ N : ℕ,1≤N→
      Integrable (fun ω=>Real.exp (sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω))
        (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))≤
        sourceRieszTransportCem β (sourceRieszLocalBeta (ι:=ι) s M) glzUniversalTailConstant Cub := by
  have hloc := (sourceRieszLocalBeta_properties (ι:=ι) s M hs (by linarith) hM).1
  intro σ hσ N hN
  by_cases hsmall : β≤sourceRieszLocalBeta (ι:=ι) s M
  · have he : sourceRieszTransportAllBetaExponent ρ s M n β σ K v N=
        sourceRieszLocalNumeratorExponent ρ s n β σ K v N := by
      funext ω
      simp only [sourceRieszTransportAllBetaExponent,sourceRieszTransportEpsilon,ite_eq_left hsmall]
      unfold sourceRieszLocalNumeratorExponent sourceRieszLocalParticleExponent
      ring
    have hc : sourceRieszTransportCem β (sourceRieszLocalBeta (ι:=ι) s M) glzUniversalTailConstant Cub=
        Real.exp 1+glzUniversalTailConstant := by
      unfold sourceRieszTransportCem
      exact ite_eq_left hsmall
    rw [he, hc]
    exact sourceRieszLocal_numerator s n hs hd β σ hβ hσ hv ρ M hM hρ N hN hsmall
  · have hlarge := lt_of_not_ge hsmall
    obtain ⟨hyi0,hyb0⟩ := hpart hlarge N hN
    have hn : 0<N := lt_of_lt_of_le (by norm_num : (0:ℕ)<1) hN
    let X := fun ω : Fin N→E=>sourceRieszLocalNumeratorExponent ρ s n
      (sourceRieszLocalBeta (ι:=ι) s M) σ K v N ω/2
    let Y := sourceRieszLocalParticleExponent ρ s (β-sourceRieszLocalBeta (ι:=ι) s M/2) N
    have hX : Measurable X := (measurable_sourceRieszLocalNumeratorExponent ρ s n
      (sourceRieszLocalBeta (ι:=ι) s M) σ hv N hn).div_const 2
    have hY : Measurable Y := measurable_sourceRieszLocalParticleExponent ρ s _ N hn
    have hXX (ω : Fin N→E) : 2*X ω=sourceRieszLocalNumeratorExponent ρ s n
        (sourceRieszLocalBeta (ι:=ι) s M) σ K v N ω := by dsimp[X];ring
    have hYY (ω : Fin N→E) : 2*Y ω=sourceRieszLocalParticleExponent ρ s
        (2*β-sourceRieszLocalBeta (ι:=ι) s M) N ω := by
      unfold Y sourceRieszLocalParticleExponent
      ring
    have hx := sourceRieszLocal_numerator s n hs hd (sourceRieszLocalBeta (ι:=ι) s M) σ hloc hσ hv
      ρ M hM hρ N hN le_rfl
    have hxi : Integrable (fun ω=>Real.exp (2*X ω))
        (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) := by
      simpa only [hXX] using hx.1
    have hyi : Integrable (fun ω=>Real.exp (2*Y ω))
        (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) := by
      simpa only [hYY] using hyi0
    obtain ⟨hi,hb⟩ := DGRHS.CLT.exponential_sum_integral_cs X Y hX.aemeasurable hY.aemeasurable hxi hyi
    have hSum (ω : Fin N→E) : X ω+Y ω=sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω := by
      exact (sourceRieszTransportAllBetaExponent_large ρ s M n β σ K v N hlarge ω).symm
    simp_rw [hSum] at hi hb
    simp_rw [hXX,hYY] at hb
    have hc : sourceRieszTransportCem β (sourceRieszLocalBeta (ι:=ι) s M) glzUniversalTailConstant Cub=
        Real.sqrt (Real.exp 1+glzUniversalTailConstant)*Real.sqrt Cub := by
      unfold sourceRieszTransportCem
      exact ite_eq_right hsmall
    rw [hc]
    exact ⟨hi,hb.trans (mul_le_mul (Real.sqrt_le_sqrt hx.2) (Real.sqrt_le_sqrt hyb0)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))⟩

/-- Gibbs moments, both signs, from any numerator bound `Cem ≥ 1`; includes the
zero Lipschitz constant (parameter `1`, observable identically zero). -/
theorem sourceRieszTransport_Gibbs_moment_of_numerator (s M : ℝ) (n : ℕ) (hn : 1≤n)
    (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β) (Cem : ℝ)
    (hCem : 1≤Cem)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hNum : ∀ σ : ℝ,|σ|≤1→∀ N : ℕ,1≤N→
      Integrable (fun ω=>Real.exp (sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω))
        (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))≤Cem) :
    ∀ σ : ℝ,|σ|≤1→∀ N : ℕ,1≤N→
      Integrable (fun ω=>Real.exp (σ*sourceRieszPositiveTransportParameter (ι:=ι) s M n K β*(N:ℝ)*
        sourceRieszLocalTransportEnergy ρ s n v N ω)) (DGRHS.CLT.sourceRieszSingularGibbs s β ρ N) ∧
      (∫ ω,Real.exp (σ*sourceRieszPositiveTransportParameter (ι:=ι) s M n K β*(N:ℝ)*
        sourceRieszLocalTransportEnergy ρ s n v N ω) ∂DGRHS.CLT.sourceRieszSingularGibbs s β ρ N)≤Cem := by
  intro σ hσ N hN
  obtain ⟨Cp,hCp,hPart⟩ := sourceRieszLocalParticleWeight_uniform s β hs hβ.le hd ρ M hM hρ
  have hp := hPart N hN
  by_cases hk : K=0
  · have hv0 : LipschitzWith 0 v := by simpa only [hk] using hv
    haveI := DGRHS.CLT.sourceRieszSingularGibbs_probability s β hs hβ.le (by linarith) ρ M hM hρ N
    simp only [sourceRieszLocalTransportEnergy_eq_zero ρ s n hn hv0,mul_zero,Real.exp_zero]
    exact ⟨integrable_const 1,by simpa using hCem⟩
  · simp only [sourceRieszPositiveTransportParameter,ite_eq_right hk]
    have hi := hNum σ hσ N hN
    rw [sourceRieszLocalParticleGibbs_eq s β hs hβ.le hd ρ M hM hρ N hN]
    let A := fun ω : Fin N→E=>σ*sourceRieszTransportEpsilon (ι:=ι) s M n K β*(N:ℝ)*
      sourceRieszLocalTransportEnergy ρ s n v N ω
    have hSum (ω : Fin N→E) : sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω=
        sourceRieszLocalParticleExponent ρ s β N ω+A ω := by
      dsimp [sourceRieszTransportAllBetaExponent,A]
      ring
    have ht : Integrable (fun ω=>Real.exp (A ω))
        ((Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)).tilted
          (sourceRieszLocalParticleExponent ρ s β N)) := by
      apply (integrable_tilted_iff hp.1 _).mpr
      apply hi.1.congr
      exact ae_of_all _ fun ω=>by
        change Real.exp (sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω)=
          Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)*Real.exp (A ω)
        rw [hSum,Real.exp_add]
    refine ⟨ht,?_⟩
    change (∫ ω,Real.exp (A ω) ∂(Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)).tilted
      (sourceRieszLocalParticleExponent ρ s β N))≤Cem
    rw [integral_exp_tilted]
    change (∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω+A ω)
      ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))/(∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
      ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))≤Cem
    simp_rw [←hSum]
    have hdpos : 0<(∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) := by linarith [hp.2.1]
    apply (div_le_iff₀ hdpos).mpr
    exact hi.2.trans (le_mul_of_one_le_right (by linarith) hp.2.1)

/-- Finite-relative-entropy entropic estimate (2.22) with the printed `Cem` and
a supplied partition cap `Cpf`. -/
theorem sourceRieszTransport_finiteKL_entropic_of_caps (s M : ℝ) (n : ℕ) (hn : 1≤n)
    (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β)
    (Cpf Cem : ℝ) (hCem : 1≤Cem)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hNum : ∀ σ : ℝ,|σ|≤1→∀ N : ℕ,1≤N→
      Integrable (fun ω=>Real.exp (sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω))
        (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))≤Cem)
    (hZ : ∀ N : ℕ,1≤N→
      (∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))≤Cpf)
    (N : ℕ) (hN : 1≤N) (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν]
    (hKL : klDiv ν (DGRHS.CLT.sourceRieszSingularGibbs s β ρ N)≠∞) :
    ν ≪ Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ) ∧
    Integrable (sourceRieszTransportBackgroundEnergy ρ s N) ν ∧
    Integrable (llr ν (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))) ν ∧
    Integrable (fun ω=>(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω) ν ∧
    |∫ ω,(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω ∂ν|≤
      (β/sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)*(N:ℝ)*
        sourceRieszTransportProperFreeEnergy ρ s β N ν+
      (sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)⁻¹*(Real.log Cpf+Real.log Cem) := by
  obtain ⟨Cp,hCp,hPart⟩ := sourceRieszLocalParticleWeight_uniform s β hs hβ.le hd ρ M hM hρ
  have hMom := sourceRieszTransport_Gibbs_moment_of_numerator s M n hn hs hd hM β hβ Cem hCem hv ρ hρ hNum
  let P := Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)
  let Ebg := sourceRieszTransportBackgroundEnergy ρ s N
  let a := fun ω : Fin N→E=>(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω
  let ε := sourceRieszPositiveTransportParameter (ι:=ι) s M n K β
  have hε : 0<ε := sourceRieszPositiveTransportParameter_pos s M n K β hs hd hM hβ
  have hQ : DGRHS.CLT.sourceRieszSingularGibbs s β ρ N=P.tilted (fun ω=>-β*Ebg ω) := by
    rw [sourceRieszLocalParticleGibbs_eq s β hs hβ.le hd ρ M hM hρ N hN]
    congr 1
    funext ω
    exact sourceRieszLocalParticleExponent_background ρ s β N ω
  have hp := hMom 1 (by norm_num) N hN
  have hm := hMom (-1) (by norm_num) N hN
  rw [hQ] at hp hm hKL
  have heP (ω : Fin N→E) :
      1*sourceRieszPositiveTransportParameter (ι:=ι) s M n K β*(N:ℝ)*
        sourceRieszLocalTransportEnergy ρ s n v N ω=ε*a ω := by dsimp [ε,a];ring
  have heM (ω : Fin N→E) :
      (-1)*sourceRieszPositiveTransportParameter (ι:=ι) s M n K β*(N:ℝ)*
        sourceRieszLocalTransportEnergy ρ s n v N ω= -(ε*a ω) := by dsimp [ε,a];ring
  simp_rw [heP] at hp
  simp_rw [heM] at hm
  have hz : Integrable (fun ω=>Real.exp (-β*Ebg ω)) P := by
    simpa only [sourceRieszLocalParticleExponent_background] using (hPart N hN).1
  have hzb : (∫ ω,Real.exp (-β*Ebg ω) ∂P)≤Cpf := by
    simpa only [sourceRieszLocalParticleExponent_background] using hZ N hN
  obtain ⟨hac,he,hllr,ha,hb⟩ := DGRHS.Entropy.gibbs_entropic_transfer P ν Ebg
    (-(N:ℝ)*gaussianRieszPhysicalPotentialConstant s M ι) β hβ
    (sourceRieszTransportBackgroundEnergy_lower s M hs hd hM ρ hρ N hN) hz a
    (measurable_sourceRieszScaledTransportEnergy ρ s n hv N hN).stronglyMeasurable ε hε
    hp.1 hm.1 hKL Cpf Cem hzb hp.2 hm.2
  refine ⟨hac,he,hllr,ha,?_⟩
  have hNreal : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have halgebra : (β/ε)*(N:ℝ)*sourceRieszTransportProperFreeEnergy ρ s β N ν=
      ε⁻¹*((klDiv ν P).toReal+β*(∫ ω,Ebg ω ∂ν)) := by
    unfold sourceRieszTransportProperFreeEnergy
    dsimp only [P,Ebg]
    field_simp [hβ.ne',hε.ne',hNreal]
  rw [halgebra]
  exact hb

/-- Source Theorem 2.8, positive Riesz branch.  `βloc` is the checked source
threshold; `Cem` is the printed constant of Remark A.1; `Cub` caps the partition
function at `2β-βloc`; `Cpf ≥ 1` caps it at `β`; the constants are chosen before
the density, the transport, the sign, the particle number and the competitor.
Estimate (2.22) is asserted for laws with finite relative entropy to the
Riesz Gibbs law (equivalently finite modulated free energy). -/
theorem exists_sourceRiesz_entropic_commutator (n : ℕ) (hn : 0 < n) (s : ℝ) (hs : 0 < s)
    (hd : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ) (hM : 0 ≤ M) :
    ∃ βloc : ℝ, 0 < βloc ∧ ∀ β : ℝ≥0, 0 < (β : ℝ) →
      ∃ Cub Cpf : ℝ, 1 ≤ Cub ∧ 1 ≤ Cpf ∧
      (∀ (ρ : E → ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
        (∀ᵐ x ∂volume, ρ x ≤ M) → ∀ N : ℕ, 1 ≤ N → βloc < (β : ℝ) →
          (DGRHS.CLT.sourceRieszSingularPartition s (2 * (β : ℝ) - βloc) ρ N).toReal ≤ Cub) ∧
      (∀ (ρ : E → ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
        (∀ᵐ x ∂volume, ρ x ≤ M) → ∀ N : ℕ, 1 ≤ N →
          1 ≤ (DGRHS.CLT.sourceRieszSingularPartition s (β : ℝ) ρ N).toReal ∧
          (DGRHS.CLT.sourceRieszSingularPartition s (β : ℝ) ρ N).toReal ≤ Cpf) ∧
      ∀ {K : ℝ≥0} {v : E → E}, LipschitzWith K v →
      let ε := sourceRieszPositiveTransportParameter (ι := ι) s M n K (β : ℝ)
      let Cem := sourceRieszTransportCem (β : ℝ) βloc glzUniversalTailConstant Cub
      0 < ε ∧ 1 ≤ Cem ∧ 0 ≤ Real.log Cpf + Real.log Cem ∧
      ∀ (ρ : E → ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
        (∀ᵐ x ∂volume, ρ x ≤ M) →
        (∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 1 ≤ N →
          Integrable (fun x => Real.exp (σ * ε * ((N : ℝ) *
            sourceRieszLocalTransportEnergy ρ s n v N x)))
            (DGRHS.CLT.sourceRieszSingularGibbs s (β : ℝ) ρ N) ∧
          (∫ x, Real.exp (σ * ε * ((N : ℝ) *
            sourceRieszLocalTransportEnergy ρ s n v N x))
            ∂DGRHS.CLT.sourceRieszSingularGibbs s (β : ℝ) ρ N) ≤ Cem) ∧
        ∀ N : ℕ, 1 ≤ N → ∀ (ν : Measure (Fin N → E)) [IsProbabilityMeasure ν],
          klDiv ν (DGRHS.CLT.sourceRieszSingularGibbs s (β : ℝ) ρ N) ≠ ∞ →
          (∃ e : ℝ, sourceRieszTransportExtendedFreeEnergy ρ s M (β : ℝ) N ν = (e : EReal)) ∧
          Integrable (fun x => (N : ℝ) * sourceRieszLocalTransportEnergy ρ s n v N x) ν ∧
          ((|∫ x, (N : ℝ) * sourceRieszLocalTransportEnergy ρ s n v N x ∂ν| : ℝ) : EReal) ≤
            (((β : ℝ)/ε)*(N : ℝ) : ℝ) * sourceRieszTransportExtendedFreeEnergy ρ s M (β : ℝ) N ν +
              (ε⁻¹ * (Real.log Cpf + Real.log Cem) : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have hs' : s < (Fintype.card ι : ℝ) := by linarith
  have hloc := (sourceRieszLocalBeta_properties (ι := ι) s M hs hs' hM).1
  refine ⟨sourceRieszLocalBeta (ι := ι) s M, hloc, ?_⟩
  intro β hβ
  have hβ' : 0 < (β : ℝ) := hβ
  obtain ⟨Cub, hCub1, hCubfam⟩ : ∃ Cub : ℝ, 1 ≤ Cub ∧
      (sourceRieszLocalBeta (ι := ι) s M < (β : ℝ) →
        ∀ ρ : E → ℝ, IsProbabilityMeasure (gaussianRieszDensityMeasure ρ) →
        (∀ᵐ x ∂volume, ρ x ≤ M) → ∀ N : ℕ, 1 ≤ N →
        Integrable (fun ω => Real.exp (sourceRieszLocalParticleExponent ρ s
          (2 * (β : ℝ) - sourceRieszLocalBeta (ι := ι) s M) N ω))
          (Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ)) ∧
        (∫ ω, Real.exp (sourceRieszLocalParticleExponent ρ s
          (2 * (β : ℝ) - sourceRieszLocalBeta (ι := ι) s M) N ω)
          ∂Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ)) ≤ Cub) := by
    by_cases hlarge : sourceRieszLocalBeta (ι := ι) s M < (β : ℝ)
    · obtain ⟨Cp1, hCp1, hP1⟩ := sourceRieszCommon_particle_moment (ι := ι) s
        (2 * (β : ℝ) - sourceRieszLocalBeta (ι := ι) s M) M hs (by linarith) hM hd
      refine ⟨max Cp1 1, le_max_right _ _, fun _ ρ hprob hρ N hN => ?_⟩
      have h := hP1 ρ hprob hρ N hN
      exact ⟨h.1, h.2.2.trans (le_max_left _ _)⟩
    · exact ⟨1, le_rfl, fun h => absurd h hlarge⟩
  obtain ⟨Cp, hCp, hPf⟩ := sourceRieszCommon_particle_moment (ι := ι) s (β : ℝ) M hs hβ'.le hM hd
  refine ⟨Cub, max Cp 1, hCub1, le_max_right _ _, ?_, ?_, ?_⟩
  · intro ρ hprob hρ N hN hlarge
    exact sourceRieszSingularPartition_toReal_le s _ hs (by linarith) hd ρ M hM hρ N Cub
      (hCubfam hlarge ρ hprob hρ N hN).2
  · intro ρ hprob hρ N hN
    have h := hPf ρ hprob hρ N hN
    exact ⟨sourceRieszSingularPartition_toReal_ge s _ hs hβ'.le hd ρ M hM hρ N 1 h.2.1,
      sourceRieszSingularPartition_toReal_le s _ hs hβ'.le hd ρ M hM hρ N _
        (h.2.2.trans (le_max_left _ _))⟩
  · intro K v hv
    dsimp only
    have hε := sourceRieszPositiveTransportParameter_pos (ι := ι) s M n K (β : ℝ) hs hd hM hβ'
    have hCem1 := one_le_sourceRieszTransportCem (β : ℝ) (sourceRieszLocalBeta (ι := ι) s M)
      glzUniversalTailConstant Cub glzUniversalTailConstant_pos.le hCub1
    refine ⟨hε, hCem1, ?_, ?_⟩
    · have h1 := Real.log_nonneg (le_max_right Cp 1)
      have h2 := Real.log_nonneg hCem1
      linarith
    · intro ρ hprob hρ
      have hNum := sourceRieszTransport_numerator_explicit (ι := ι) s M n hs hd hM (β : ℝ) hβ' Cub
        hv ρ hρ (fun hl N hN => hCubfam hl ρ hprob hρ N hN)
      refine ⟨?_, ?_⟩
      · intro σ hσ N hN
        have h := sourceRieszTransport_Gibbs_moment_of_numerator s M n hn1 hs hd hM (β : ℝ) hβ' _
          hCem1 hv ρ hρ hNum σ (le_of_eq hσ) N hN
        simpa only [mul_assoc] using h
      · intro N hN ν hν hKL
        obtain ⟨hac, hbg, hllr, ha, hb⟩ := sourceRieszTransport_finiteKL_entropic_of_caps s M n hn1
          hs hd hM (β : ℝ) hβ' (max Cp 1) _ hCem1 hv ρ hρ hNum
          (fun N hN => (hPf ρ hprob hρ N hN).2.2.trans (le_max_left _ _)) N hN ν hKL
        have hext := sourceRieszTransportExtendedFreeEnergy_eq_proper s M hs hd hM (β : ℝ) hβ' ρ hρ
          N hN ν hac hbg hllr
        refine ⟨⟨_, hext⟩, ha, ?_⟩
        rw [hext, ← EReal.coe_mul, ← EReal.coe_add]
        exact EReal.coe_le_coe_iff.mpr hb

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszTransportCem
#print axioms DGRHS.Commutator.sourceRieszTransportCem
#check @DGRHS.Commutator.one_le_sourceRieszTransportCem
#print axioms DGRHS.Commutator.one_le_sourceRieszTransportCem
#check @DGRHS.Commutator.sourceRieszTransport_numerator_explicit
#print axioms DGRHS.Commutator.sourceRieszTransport_numerator_explicit
#check @DGRHS.Commutator.sourceRieszTransport_Gibbs_moment_of_numerator
#print axioms DGRHS.Commutator.sourceRieszTransport_Gibbs_moment_of_numerator
#check @DGRHS.Commutator.sourceRieszTransport_finiteKL_entropic_of_caps
#print axioms DGRHS.Commutator.sourceRieszTransport_finiteKL_entropic_of_caps
#check @DGRHS.Commutator.exists_sourceRiesz_entropic_commutator
#print axioms DGRHS.Commutator.exists_sourceRiesz_entropic_commutator
