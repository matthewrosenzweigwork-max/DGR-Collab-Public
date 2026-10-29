import DGRHS.Commutator.SourceRieszEntropicCommutator
import DGRHS.CLT.SourceRieszSingularRate

/-! Source Theorem 2.8, positive Riesz branch `0<s<d/2`, with the printed
constant of Remark A.1 (eq. CemLargeBetaDef, rows 1 and 3, TeX 4144-4156):
`C_em = e+L` for `β ≤ β_loc` and
`C_em = e^{-β I_μ} (e+L)^{1/2} C_ub(2β-β_loc,μ)^{1/2}` for `β > β_loc`.
The factor `e^{-β I_μ}` comes from the Jensen lower bound
`K_{N,β} ≥ e^{β I_μ}` (TeX eq. KlowerJensen, 432-436), here taken from
`sourceRieszSingularPartition_original_rate`, instead of the weaker `K ≥ 1`.
Since `C_em` depends on `μ` through `I_μ`, it is chosen after the density
(the printed `C_em(β,μ,v,n)` depends on `μ`); `β_loc`, `ε`, `C_ub`, `C_pf`
are still chosen before it.  The existing export is not modified. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Concentration
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Printed `C_em` of Remark A.1 for `0<s<d/2`, including the Jensen factor
`e^{-β I}` for `β > β_loc`. -/
def sourceRieszPrintedCem (β βloc L Cub I : ℝ) : ℝ :=
  if β ≤ βloc then Real.exp 1 + L
  else Real.exp (-(β * I)) * (Real.sqrt (Real.exp 1 + L) * Real.sqrt Cub)

/-- Jensen lower bound `e^{β I_μ} ≤ K_{N,β}` (TeX eq. KlowerJensen) for the
Riesz particle partition integral. -/
lemma sourceRieszJensen_lower_integral (s β : ℝ) (hs : 0<s) (hβ : 0≤β)
    (hd : 2*s<(Fintype.card ι:ℝ)) (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (N : ℕ) (hN : 1≤N) :
    Real.exp (β*DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
      (fun a b : E => gaussianRieszPhysicalPair s (a,b)))≤
    (∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
      ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) := by
  have ha : 0<(Fintype.card ι:ℝ)/2-s := by linarith
  have h := DGRHS.CLT.sourceRieszSingularPartition_original_rate s β hs hβ ha ρ M hM hρ
  dsimp only at h
  obtain ⟨hh,hSym,hCan,κ,eig,e,-,-,-,-,-,-,C,hC,hr⟩ := h
  have hJ := (hr N hN).2.1
  have hnonneg : 0≤DGRHS.Concentration.physicalRieszSourcePartition s β ρ N :=
    integral_nonneg fun _=>(Real.exp_pos _).le
  rw [DGRHS.CLT.sourceRieszSingularPartition_eq_integral s β hs hβ ha ρ M hM hρ N,
    ENNReal.toReal_ofReal hnonneg] at hJ
  exact hJ

/-- Gibbs moments, both signs, from a numerator bound `Cnum ≤ Cem * Zlow` and a
partition lower bound `Zlow ≤ K_{N,β}`; includes the zero Lipschitz constant. -/
theorem sourceRieszTransport_Gibbs_moment_of_numerator_lower (s M : ℝ) (n : ℕ) (hn : 1≤n)
    (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β)
    (Cnum Zlow Cem : ℝ) (hCem : 1≤Cem) (hZpos : 0<Zlow) (hdiv : Cnum≤Cem*Zlow)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hNum : ∀ σ : ℝ,|σ|≤1→∀ N : ℕ,1≤N→
      Integrable (fun ω=>Real.exp (sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω))
        (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))≤Cnum)
    (hZlow : ∀ N : ℕ,1≤N→ Zlow≤(∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))) :
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
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) :=
      lt_of_lt_of_le hZpos (hZlow N hN)
    apply (div_le_iff₀ hdpos).mpr
    exact hi.2.trans (hdiv.trans (mul_le_mul_of_nonneg_left (hZlow N hN) (by linarith)))

/-- Finite-relative-entropy estimate (2.22) from the Gibbs exponential moments
of both signs (bounded by `Cem`) and a partition cap `Cpf`. -/
theorem sourceRieszTransport_finiteKL_entropic_of_moments (s M : ℝ) (n : ℕ)
    (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β)
    (Cpf Cem : ℝ)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hMom : ∀ σ : ℝ,|σ|≤1→∀ N : ℕ,1≤N→
      Integrable (fun ω=>Real.exp (σ*sourceRieszPositiveTransportParameter (ι:=ι) s M n K β*(N:ℝ)*
        sourceRieszLocalTransportEnergy ρ s n v N ω)) (DGRHS.CLT.sourceRieszSingularGibbs s β ρ N) ∧
      (∫ ω,Real.exp (σ*sourceRieszPositiveTransportParameter (ι:=ι) s M n K β*(N:ℝ)*
        sourceRieszLocalTransportEnergy ρ s n v N ω) ∂DGRHS.CLT.sourceRieszSingularGibbs s β ρ N)≤Cem)
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

/-- Source Theorem 2.8, positive Riesz branch, with the printed `C_em` of
Remark A.1 including `e^{-β I_μ}` for `β > β_loc`.  Identical to
`exists_sourceRiesz_entropic_commutator` except that `Cem` is chosen after the
density (it contains `I_μ = interactionEnergy μ W`, `W = ‖x-y‖^{-s}/s`). -/
theorem exists_sourceRiesz_entropic_commutator_printed_constants (n : ℕ) (hn : 0 < n)
    (s : ℝ) (hs : 0 < s)
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
      0 < ε ∧
      ∀ (ρ : E → ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
        (∀ᵐ x ∂volume, ρ x ≤ M) →
        let Cem := sourceRieszPrintedCem (β : ℝ) βloc glzUniversalTailConstant Cub
          (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
            (fun a b : E => gaussianRieszPhysicalPair s (a, b)))
        1 ≤ Cem ∧ 0 ≤ Real.log Cpf + Real.log Cem ∧
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
    refine ⟨hε, ?_⟩
    intro ρ hprob hρ
    have hNum := sourceRieszTransport_numerator_explicit (ι := ι) s M n hs hd hM (β : ℝ) hβ' Cub
      hv ρ hρ (fun hl N hN => hCubfam hl ρ hprob hρ N hN)
    have hCnum1 := one_le_sourceRieszTransportCem (β : ℝ) (sourceRieszLocalBeta (ι := ι) s M)
      glzUniversalTailConstant Cub glzUniversalTailConstant_pos.le hCub1
    set I := DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
      (fun a b : E => gaussianRieszPhysicalPair s (a, b)) with hI
    set Cem := sourceRieszPrintedCem (β : ℝ) (sourceRieszLocalBeta (ι := ι) s M)
      glzUniversalTailConstant Cub I with hCemdef
    -- the partition lower bound and the division constant
    obtain ⟨Zlow, hZpos, hZlow, hdiv⟩ : ∃ Zlow : ℝ, 0 < Zlow ∧
        (∀ N : ℕ, 1 ≤ N → Zlow ≤ (∫ ω, Real.exp (sourceRieszLocalParticleExponent ρ s (β : ℝ) N ω)
          ∂Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ))) ∧
        sourceRieszTransportCem (β : ℝ) (sourceRieszLocalBeta (ι := ι) s M)
          glzUniversalTailConstant Cub ≤ Cem * Zlow := by
      by_cases hsmall : (β : ℝ) ≤ sourceRieszLocalBeta (ι := ι) s M
      · refine ⟨1, one_pos, fun N hN => (hPf ρ hprob hρ N hN).2.1, ?_⟩
        have : Cem = sourceRieszTransportCem (β : ℝ) (sourceRieszLocalBeta (ι := ι) s M)
            glzUniversalTailConstant Cub := by
          rw [hCemdef]
          unfold sourceRieszPrintedCem sourceRieszTransportCem
          rw [ite_eq_left hsmall, ite_eq_left hsmall]
        rw [this, mul_one]
      · refine ⟨Real.exp ((β : ℝ) * I), Real.exp_pos _,
          fun N hN => sourceRieszJensen_lower_integral s (β : ℝ) hs hβ'.le hd ρ M hM hρ N hN, ?_⟩
        have : Cem = Real.exp (-((β : ℝ) * I)) *
            sourceRieszTransportCem (β : ℝ) (sourceRieszLocalBeta (ι := ι) s M)
              glzUniversalTailConstant Cub := by
          rw [hCemdef]
          unfold sourceRieszPrintedCem sourceRieszTransportCem
          rw [ite_eq_right hsmall, ite_eq_right hsmall]
        rw [this]
        have hmul : Real.exp (-((β : ℝ) * I)) * Real.exp ((β : ℝ) * I) = 1 := by
          rw [← Real.exp_add]; simp
        calc sourceRieszTransportCem (β : ℝ) (sourceRieszLocalBeta (ι := ι) s M)
              glzUniversalTailConstant Cub
            = (Real.exp (-((β : ℝ) * I)) * Real.exp ((β : ℝ) * I)) *
              sourceRieszTransportCem (β : ℝ) (sourceRieszLocalBeta (ι := ι) s M)
                glzUniversalTailConstant Cub := by rw [hmul, one_mul]
          _ = _ := by ring
          _ ≤ _ := le_rfl
    -- 1 ≤ Cem from the numerator bound at σ = 0 (the partition function itself)
    have hCem1 : 1 ≤ Cem := by
      have h0 := (hNum 0 (by simp) 1 le_rfl).2
      have hz : (fun ω : Fin 1 → E => Real.exp (sourceRieszTransportAllBetaExponent ρ s M n (β : ℝ)
          0 K v 1 ω)) = fun ω => Real.exp (sourceRieszLocalParticleExponent ρ s (β : ℝ) 1 ω) := by
        funext ω
        simp [sourceRieszTransportAllBetaExponent]
      rw [hz] at h0
      have h1 := hZlow 1 le_rfl
      have h2 : Zlow * 1 ≤ Zlow * Cem := by
        calc Zlow * 1 = Zlow := mul_one _
          _ ≤ _ := h1
          _ ≤ _ := h0
          _ ≤ Cem * Zlow := hdiv
          _ = Zlow * Cem := mul_comm _ _
      exact le_of_mul_le_mul_left h2 hZpos
    have hlog : 0 ≤ Real.log (max Cp 1) + Real.log Cem := by
      have h1 := Real.log_nonneg (le_max_right Cp 1)
      have h2 := Real.log_nonneg hCem1
      linarith
    have hMom := sourceRieszTransport_Gibbs_moment_of_numerator_lower s M n hn1 hs hd hM (β : ℝ) hβ'
      _ Zlow Cem hCem1 hZpos hdiv hv ρ hρ hNum hZlow
    refine ⟨hCem1, hlog, ?_, ?_⟩
    · intro σ hσ N hN
      have h := hMom σ (le_of_eq hσ) N hN
      simpa only [mul_assoc] using h
    · intro N hN ν hν hKL
      obtain ⟨hac, hbg, hllr, ha, hb⟩ := sourceRieszTransport_finiteKL_entropic_of_moments s M n
        hs hd hM (β : ℝ) hβ' (max Cp 1) Cem hv ρ hρ hMom
        (fun N hN => (hPf ρ hprob hρ N hN).2.2.trans (le_max_left _ _)) N hN ν hKL
      have hext := sourceRieszTransportExtendedFreeEnergy_eq_proper s M hs hd hM (β : ℝ) hβ' ρ hρ
        N hN ν hac hbg hllr
      refine ⟨⟨_, hext⟩, ha, ?_⟩
      rw [hext, ← EReal.coe_mul, ← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr hb

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszPrintedCem
#print axioms DGRHS.Commutator.sourceRieszPrintedCem
#check @DGRHS.Commutator.sourceRieszJensen_lower_integral
#print axioms DGRHS.Commutator.sourceRieszJensen_lower_integral
#check @DGRHS.Commutator.sourceRieszTransport_Gibbs_moment_of_numerator_lower
#print axioms DGRHS.Commutator.sourceRieszTransport_Gibbs_moment_of_numerator_lower
#check @DGRHS.Commutator.sourceRieszTransport_finiteKL_entropic_of_moments
#print axioms DGRHS.Commutator.sourceRieszTransport_finiteKL_entropic_of_moments
#check @DGRHS.Commutator.exists_sourceRiesz_entropic_commutator_printed_constants
#print axioms DGRHS.Commutator.exists_sourceRiesz_entropic_commutator_printed_constants
