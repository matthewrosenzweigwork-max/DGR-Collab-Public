import DGRHS.Commutator.SourceRieszThermalSource

/-! Corollary 7.3 (TeX 3547-3579), positive Riesz case, with the pointwise commutator premise
required only on COLLISION-FREE configurations.

The printed premise (eq. pointwiseCommutatorBound) is stated with the physical energy `F_N`,
which is `+infinity` on collisions, so it is vacuous there. The earlier exports
`sourceRieszCommon_thermal_minimum_source` / `sourceRieszCommon_allLaw_thermal_absolute_source`
demand the bound at every configuration with the totalized finite energy. Here the premise is
`∀ ω, (∀ i j, i ≠ j → ω i ≠ ω j) → ...`.

Signed finite-KL export: finite Gibbs KL forces `ν ≪ μ^{⊗N}` (already part of
`sourceRieszCommon_finiteKL_entropic`), which is concentrated on collision-free configurations
(`density_iid_collision_free`), so the pointwise bound is only used `ν`-a.e.
All-law absolute export: infinite KL gives `⊤` for positive `Cpw`; the single degenerate case
`Cpw = 0` with `ν` charging collisions is not covered by the printed estimate either and is
excluded by the explicit hypothesis `Cpw = 0 → ν ≪ μ^{⊗N}`.
The sign `0 ≤ Cpw` is derived from the collision-free two-particle configuration `(0,z)`.
The finite-KL signed domain and the all-law absolute domain (with log(2 Cem)) are kept distinct,
as in the earlier exports. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal BigOperators
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Concentration
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma sourceRiesz_twoParticle_collisionFree (z : E) (hz : z≠0) :
    ∀ i j : Fin 2,i≠j → (fun k : Fin 2=>if k=0 then (0:E) else z) i≠
      (fun k : Fin 2=>if k=0 then (0:E) else z) j := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · simpa using hz.symm
  · simpa using hz
  · exact absurd rfl hij

/-- Collision-free version of `sourceRiesz_twoParticle_energy_unbounded`. -/
theorem sourceRiesz_twoParticle_energy_unbounded_collisionFree (s M : ℝ) (hs : 0<s)
    (hd : s<(Fintype.card ι:ℝ)) (hM : 0≤M) (ρ : E→ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (R : ℝ) :
    ∃ ω : Fin 2→E,(∀ i j : Fin 2,i≠j → ω i≠ω j) ∧ R<DGRHS.CLT.sourceCanonicalModulatedEnergy
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
      (sourceRieszLocalPhysicalPotential ρ s) (sourceRieszLocalPhysicalEnergy ρ s) 2 ω := by
  classical
  have hcard : 0<(Fintype.card ι:ℝ) := hs.trans hd
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by exact_mod_cast hcard)
  let i : ι := Classical.arbitrary ι
  let B := gaussianRieszPhysicalPotentialConstant s M ι
  have hev : ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0), 4*(R+B+1)*s≤r^(-s) :=
    (tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos hs)).eventually
      (Filter.eventually_ge_atTop (4*(R+B+1)*s))
  have hrpos : ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),0<r :=
    Filter.mem_inf_of_right (Set.Subset.refl _)
  obtain ⟨r,hr,hpow⟩ := (hrpos.and hev).exists
  let z : E := EuclideanSpace.single i r
  let ω : Fin 2→E := fun j=>if j=0 then 0 else z
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : E=>gaussianRieszPhysicalPair s (a,b)
  have hz : ‖z‖=r := by simp [z, PiLp.norm_single, abs_of_pos hr]
  have hzne : z≠0 := norm_pos_iff.mp (by rw [hz];exact hr)
  have hW : 4*(R+B+1)≤gaussianRieszPhysicalPair s (0,z) := by
    simp only [gaussianRieszPhysicalPair, zero_sub, norm_neg, hz]
    exact (le_div_iff₀ hs).2 hpow
  have hraw := DGRHS.CLT.sourceCanonicalModulatedEnergy_raw μ W
    (fun a b=>by dsimp [W,gaussianRieszPhysicalPair];rw [norm_sub_rev]) 2 (by norm_num) ω
  have hsum : DGRHS.CanonicalVariance.offDiagonalSum (Function.uncurry W) ω =
      2*gaussianRieszPhysicalPair s (0,z) := sourceRiesz_twoParticle_offDiagonal s z
  have hpot := sourceRieszLocal_oneBody_bound ρ s M 1 hs hd hM (by norm_num) hρ 2 (by norm_num) ω
  simp only [one_mul] at hpot
  change (2:ℝ)⁻¹*(∑ j : Fin 2,DGRHS.potential μ W (ω j))-
    DGRHS.interactionEnergy μ W≤B at hpot
  refine ⟨ω,?_,?_⟩
  · exact sourceRiesz_twoParticle_collisionFree z hzne
  clear hzne
  change R<DGRHS.CLT.sourceCanonicalModulatedEnergy
    (fun p=>DGRHS.centeredKernel μ W p.1 p.2)
    (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) 2 ω
  rw [hraw,hsum]
  norm_num only [Nat.cast_ofNat] at *
  norm_num at hpot ⊢
  nlinarith

theorem sourceRiesz_thermal_pointwise_constant_nonneg_collisionFree (s M : ℝ) (n : ℕ)
    (hs : 0<s) (hd : s<(Fintype.card ι:ℝ)) (hM : 0≤M) (ρ : E→ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (v : E→E) (Cpw Cpt : ℝ)
    (hpoint : ∀ N : ℕ,1≤N→∀ ω : Fin N→E,(∀ i j : Fin N,i≠j → ω i≠ω j) →
      |sourceRieszLocalTransportEnergy ρ s n v N ω|≤Cpw*
        (DGRHS.CLT.sourceCanonicalModulatedEnergy
          (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
          (sourceRieszLocalPhysicalPotential ρ s) (sourceRieszLocalPhysicalEnergy ρ s) N ω+
          Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))/(N:ℝ))) : 0≤Cpw := by
  by_contra hc
  have hcneg : Cpw<0 := lt_of_not_ge hc
  obtain ⟨ω,hcf,hω⟩ := sourceRiesz_twoParticle_energy_unbounded_collisionFree s M hs hd hM ρ hρ
    (-Cpt*(2:ℝ)^(s/(Fintype.card ι:ℝ))/2)
  have hb := hpoint 2 (by norm_num) ω hcf
  have hpos : 0<DGRHS.CLT.sourceCanonicalModulatedEnergy
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
      (sourceRieszLocalPhysicalPotential ρ s) (sourceRieszLocalPhysicalEnergy ρ s) 2 ω+
      Cpt*(2:ℝ)^(s/(Fintype.card ι:ℝ))/2 := by linarith
  have hneg := mul_neg_of_neg_of_pos hcneg hpos
  norm_num only [Nat.cast_ofNat] at hb
  exact (not_lt_of_ge ((abs_nonneg _).trans hb)) hneg

theorem sourceRieszCommon_thermal_minimum_source_collisionFree (s M : ℝ) (n : ℕ) (hn : 1≤n)
    (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β) :
    ∃ Cpf Cem : ℝ,1≤Cpf ∧ 1≤Cem ∧ ∀ (K : ℝ≥0) (v : E→E),LipschitzWith K v →
      0<sourceRieszPositiveTransportParameter (ι:=ι) s M n K β ∧
      ∀ ρ : E→ℝ,IsProbabilityMeasure (gaussianRieszDensityMeasure ρ) →
      (∀ᵐ x ∂volume,ρ x≤M) → ∀ Cpw Cpt : ℝ,
      (∀ N : ℕ,1≤N → ∀ ω : Fin N→E,(∀ i j : Fin N,i≠j → ω i≠ω j) →
        |sourceRieszLocalTransportEnergy ρ s n v N ω|≤Cpw*
          (DGRHS.CLT.sourceCanonicalModulatedEnergy
            (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
            (sourceRieszLocalPhysicalPotential ρ s) (sourceRieszLocalPhysicalEnergy ρ s) N ω+
            Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))/(N:ℝ))) →
      ∀ N : ℕ,1≤N → ∀ (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν],
      klDiv ν (DGRHS.CLT.sourceRieszSingularGibbs s β ρ N)≠∞ →
      Integrable (fun ω=>(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω) ν ∧
      |∫ ω,(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω ∂ν|≤
        min ((β/sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)*(N:ℝ)*
          sourceRieszTransportProperFreeEnergy ρ s β N ν+
          (sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)⁻¹*(Real.log Cpf+Real.log Cem))
          (Cpw*(N:ℝ)*sourceRieszTransportProperFreeEnergy ρ s β N ν+
            Cpw*Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))) := by
  obtain ⟨Cpf,Cem,hCpf,hCem,hFamily⟩ := sourceRieszCommon_finiteKL_entropic (ι:=ι) s M n hn hs hd hM β hβ
  refine ⟨Cpf,Cem,hCpf,hCem,?_⟩
  intro K v hv
  obtain ⟨hε,hFam⟩ := hFamily K v hv
  refine ⟨hε,?_⟩
  intro ρ hprob hρ Cpw Cpt hpoint N hN ν hν hKL
  let _ := hprob
  haveI : Nonempty ι := Fintype.card_pos_iff.mp
    (by exact_mod_cast (show (0:ℝ)<(Fintype.card ι:ℝ) by linarith))
  have hCpw := sourceRiesz_thermal_pointwise_constant_nonneg_collisionFree s M n hs
    (by linarith) hM ρ hρ v Cpw Cpt hpoint
  obtain ⟨hac,hbg,hllr,ha,hent⟩ := hFam ρ hprob hρ N hN ν hKL
  have hNr : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  let a := fun ω : Fin N→E=>(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω
  have hscaled (ω : Fin N→E) (hω : ∀ i j : Fin N,i≠j → ω i≠ω j) :
      |a ω|≤Cpw*(sourceRieszTransportBackgroundEnergy ρ s N ω+
      Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))) := by
    have hm := mul_le_mul_of_nonneg_left (hpoint N hN ω hω) (Nat.cast_nonneg N)
    dsimp only [a]
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg N)]
    dsimp only [sourceRieszTransportBackgroundEnergy]
    convert hm using 1 <;> field_simp <;> ring
  have hscaledae : ∀ᵐ ω ∂ν,|a ω|≤Cpw*(sourceRieszTransportBackgroundEnergy ρ s N ω+
      Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))) := by
    filter_upwards [hac.ae_le (DGRHS.CLT.density_iid_collision_free ρ N)] with ω hω
    exact hscaled ω hω
  have hi := integral_mono_ae ha.abs
    ((hbg.add (integrable_const (Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))))).const_mul Cpw) hscaledae
  have hbpoint : (∫ ω,|a ω| ∂ν)≤Cpw*((∫ ω,sourceRieszTransportBackgroundEnergy ρ s N ω ∂ν)+
      Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))) := by
    rw [integral_const_mul] at hi
    simp only [Pi.add_apply] at hi
    rw [integral_add hbg (integrable_const _)] at hi
    simpa [a] using hi
  have hex : (N:ℝ)*sourceRieszTransportProperFreeEnergy ρ s β N ν=
      (klDiv ν (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))).toReal/β+
      (∫ ω,sourceRieszTransportBackgroundEnergy ρ s N ω ∂ν) := by
    unfold sourceRieszTransportProperFreeEnergy
    field_simp [hNr,hβ.ne']
    <;> ring
  have henergy : (∫ ω,sourceRieszTransportBackgroundEnergy ρ s N ω ∂ν)≤
      (N:ℝ)*sourceRieszTransportProperFreeEnergy ρ s β N ν := by
    rw [hex]
    exact le_add_of_nonneg_left (div_nonneg ENNReal.toReal_nonneg hβ.le)
  have hpointbound : |∫ ω,a ω ∂ν|≤Cpw*(N:ℝ)*sourceRieszTransportProperFreeEnergy ρ s β N ν+
      Cpw*Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ)) := by
    calc
      _ ≤ ∫ ω,|a ω| ∂ν := abs_integral_le_integral_abs
      _ ≤ Cpw*((∫ ω,sourceRieszTransportBackgroundEnergy ρ s N ω ∂ν)+
          Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))) := hbpoint
      _ ≤ Cpw*((N:ℝ)*sourceRieszTransportProperFreeEnergy ρ s β N ν+
          Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))) :=
        mul_le_mul_of_nonneg_left (add_le_add henergy le_rfl) hCpw
      _ = _ := by ring
  exact ⟨ha,le_min hent hpointbound⟩

theorem sourceRieszCommon_allLaw_thermal_absolute_source_collisionFree (s M : ℝ) (n : ℕ)
    (hn : 1≤n) (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β) :
    ∃ Cpf Cem : ℝ,1≤Cpf ∧ 1≤Cem ∧ ∀ (K : ℝ≥0) (v : E→E),LipschitzWith K v →
      0<sourceRieszPositiveTransportParameter (ι:=ι) s M n K β ∧
      ∀ ρ : E→ℝ,IsProbabilityMeasure (gaussianRieszDensityMeasure ρ) →
      (∀ᵐ x ∂volume,ρ x≤M) → ∀ Cpw Cpt : ℝ,
      (∀ N : ℕ,1≤N → ∀ ω : Fin N→E,(∀ i j : Fin N,i≠j → ω i≠ω j) →
        |sourceRieszLocalTransportEnergy ρ s n v N ω|≤Cpw*
          (DGRHS.CLT.sourceCanonicalModulatedEnergy
            (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
            (sourceRieszLocalPhysicalPotential ρ s) (sourceRieszLocalPhysicalEnergy ρ s) N ω+
            Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))/(N:ℝ))) →
      ∀ N : ℕ,1≤N → ∀ (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν],
      (Cpw = 0 → ν ≪ Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) →
      ((∫⁻ ω,ENNReal.ofReal |(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω| ∂ν):EReal)≤
        min (((β/sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)*(N:ℝ):ℝ)*
          sourceRieszTransportExtendedFreeEnergy ρ s M β N ν+
          ((sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)⁻¹*(Real.log Cpf+Real.log (2*Cem)):ℝ))
          ((Cpw*(N:ℝ):ℝ)*sourceRieszTransportExtendedFreeEnergy ρ s M β N ν+
            (Cpw*Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ)):ℝ)) := by
  obtain ⟨Cpf,Cem,hCpf,hCem,hFamily⟩ := sourceRieszCommon_allLaw_extendedFreeEnergy (ι:=ι) s M n hn hs hd hM β hβ
  obtain ⟨Cpd,Cmd,hCpd,hCmd,hDomain⟩ := sourceRieszCommon_finiteKL_entropic (ι:=ι) s M n hn hs hd hM β hβ
  refine ⟨Cpf,Cem,hCpf,hCem,?_⟩
  intro K v hv
  obtain ⟨hε,hFam⟩ := hFamily K v hv
  refine ⟨hε,?_⟩
  intro ρ hprob hρ Cpw Cpt hpoint N hN ν hν hν0
  let _ := hprob
  haveI : Nonempty ι := Fintype.card_pos_iff.mp
    (by exact_mod_cast (show (0:ℝ)<(Fintype.card ι:ℝ) by linarith))
  have hCpw := sourceRiesz_thermal_pointwise_constant_nonneg_collisionFree s M n hs
    (by linarith) hM ρ hρ v Cpw Cpt hpoint
  have hent := hFam ρ hprob hρ N hN ν
  apply le_min hent
  by_cases hc0 : Cpw=0
  · have haz : ∀ᵐ ω ∂ν,sourceRieszLocalTransportEnergy ρ s n v N ω=0 := by
      filter_upwards [(hν0 hc0).ae_le (DGRHS.CLT.density_iid_collision_free ρ N)] with ω hω
      have h := hpoint N hN ω hω
      rw [hc0,zero_mul] at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    have hl : (∫⁻ ω,ENNReal.ofReal |(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω| ∂ν)=0 := by
      refine (lintegral_congr_ae (g:=fun _=>(0:ℝ≥0∞)) ?_).trans lintegral_zero
      filter_upwards [haz] with ω hω
      simp [hω]
    rw [hl]
    simp only [EReal.coe_ennreal_zero,hc0,zero_mul,
      EReal.coe_zero,EReal.zero_mul,add_zero]
    exact le_rfl
  · have hcp : 0<Cpw*(N:ℝ) := mul_pos (lt_of_le_of_ne hCpw (Ne.symm hc0))
      (by exact_mod_cast (by omega : 0<N))
    by_cases hKL : klDiv ν (DGRHS.CLT.sourceRieszSingularGibbs s β ρ N)=∞
    · have heTop : sourceRieszTransportExtendedFreeEnergy ρ s M β N ν=⊤ := by
        rw [sourceRieszTransportExtendedFreeEnergy_rewrite s M hs hd hM β hβ ρ hρ N hN ν,
          hKL,EReal.coe_ennreal_top,EReal.top_sub_coe,
          EReal.top_mul_coe_of_pos (inv_pos.mpr (mul_pos hβ (by exact_mod_cast (by omega : 0<N))))]
      rw [heTop,EReal.coe_mul_top_of_pos hcp,EReal.top_add_coe]
      exact le_top
    · obtain ⟨hac,hbg,hllr,ha,_⟩ := (hDomain K v hv).2 ρ hprob hρ N hN ν hKL
      have hNr : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
      let a := fun ω : Fin N→E=>(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω
      have hscaled (ω : Fin N→E) (hω : ∀ i j : Fin N,i≠j → ω i≠ω j) :
          |a ω|≤Cpw*(sourceRieszTransportBackgroundEnergy ρ s N ω+
          Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))) := by
        have hm := mul_le_mul_of_nonneg_left (hpoint N hN ω hω) (Nat.cast_nonneg N)
        dsimp only [a]
        rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg N)]
        dsimp only [sourceRieszTransportBackgroundEnergy]
        convert hm using 1 <;> field_simp <;> ring
      have hscaledae : ∀ᵐ ω ∂ν,|a ω|≤Cpw*(sourceRieszTransportBackgroundEnergy ρ s N ω+
          Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))) := by
        filter_upwards [hac.ae_le (DGRHS.CLT.density_iid_collision_free ρ N)] with ω hω
        exact hscaled ω hω
      have hi := integral_mono_ae ha.abs
        ((hbg.add (integrable_const (Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))))).const_mul Cpw) hscaledae
      have hbpoint : (∫ ω,|a ω| ∂ν)≤Cpw*((∫ ω,sourceRieszTransportBackgroundEnergy ρ s N ω ∂ν)+
          Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))) := by
        rw [integral_const_mul] at hi
        simp only [Pi.add_apply] at hi
        rw [integral_add hbg (integrable_const _)] at hi
        simpa [a] using hi
      have hex : (N:ℝ)*sourceRieszTransportProperFreeEnergy ρ s β N ν=
          (klDiv ν (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))).toReal/β+
          (∫ ω,sourceRieszTransportBackgroundEnergy ρ s N ω ∂ν) := by
        unfold sourceRieszTransportProperFreeEnergy
        field_simp [hNr,hβ.ne']
        <;> ring
      have henergy : (∫ ω,sourceRieszTransportBackgroundEnergy ρ s N ω ∂ν)≤
          (N:ℝ)*sourceRieszTransportProperFreeEnergy ρ s β N ν := by
        rw [hex]
        exact le_add_of_nonneg_left (div_nonneg ENNReal.toReal_nonneg hβ.le)
      have hpointbound : (∫ ω,|a ω| ∂ν)≤Cpw*(N:ℝ)*sourceRieszTransportProperFreeEnergy ρ s β N ν+
          Cpw*Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ)) := by
        calc
          (∫ ω,|a ω| ∂ν) ≤ Cpw*((∫ ω,sourceRieszTransportBackgroundEnergy ρ s N ω ∂ν)+
              Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))) := hbpoint
          _ ≤ Cpw*((N:ℝ)*sourceRieszTransportProperFreeEnergy ρ s β N ν+
              Cpt*(N:ℝ)^(s/(Fintype.card ι:ℝ))) :=
            mul_le_mul_of_nonneg_left (add_le_add henergy le_rfl) hCpw
          _ = _ := by ring
      have heq := sourceRieszTransportExtendedFreeEnergy_eq_proper s M hs hd hM β hβ ρ hρ N hN ν hac hbg hllr
      rw [heq,←ofReal_integral_eq_lintegral_ofReal ha.abs (ae_of_all _ fun ω=>abs_nonneg _),
        EReal.coe_ennreal_ofReal,max_eq_left (integral_nonneg (fun ω=>abs_nonneg _)),
        ←EReal.coe_mul,←EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by simpa only [mul_assoc] using hpointbound)

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_twoParticle_energy_unbounded_collisionFree
#print axioms DGRHS.Commutator.sourceRiesz_twoParticle_energy_unbounded_collisionFree
#check @DGRHS.Commutator.sourceRiesz_thermal_pointwise_constant_nonneg_collisionFree
#print axioms DGRHS.Commutator.sourceRiesz_thermal_pointwise_constant_nonneg_collisionFree
#check @DGRHS.Commutator.sourceRieszCommon_thermal_minimum_source_collisionFree
#print axioms DGRHS.Commutator.sourceRieszCommon_thermal_minimum_source_collisionFree
#check @DGRHS.Commutator.sourceRieszCommon_allLaw_thermal_absolute_source_collisionFree
#print axioms DGRHS.Commutator.sourceRieszCommon_allLaw_thermal_absolute_source_collisionFree
