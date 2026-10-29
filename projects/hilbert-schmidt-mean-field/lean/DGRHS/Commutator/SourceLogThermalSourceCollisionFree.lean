import DGRHS.Commutator.SourceLogThermalSource

/-! Corollary 7.3 (TeX 3547-3579), LOG case, with the pointwise commutator premise
required only on COLLISION-FREE configurations.

The printed premise (eq. pointwiseCommutatorBound) is stated with the physical energy
`F_N`, which is `+infinity` on collisions, so it is vacuous there. The earlier exports
`exists_sourceLog_thermal_minimum_source` / `sourceLog_thermal_minimum_zero_source` demand the
bound at every configuration with the totalized finite energy. Here the premise is
`∀ x, (∀ i j, i ≠ j → x i ≠ x j) → ...`.

The proof only needs the pointwise bound `ν`-almost everywhere when `ν` has finite free
energy: finite relative entropy to the iid law forces `ν ≪ μ^{⊗N}`, which is concentrated on
collision-free configurations (`density_iid_collision_free`); infinite free energy gives `⊤`
whenever the multiplier `Cpw` is positive. The single degenerate case `Cpw = 0` with `ν`
charging collisions is not covered by the printed estimate either (`0 * (+∞)` is not
determined and the totalized observable need not vanish on collisions), and is excluded by the
explicit hypothesis `Cpw = 0 → ν ≪ μ^{⊗N}` in the general export; the zero-Lipschitz export
needs no such hypothesis because its observable vanishes identically.
The sign `0 ≤ Cpw` is derived from the collision-free two-particle configuration `(0,z)`. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace DGRHS.Entropy
open DGRHS.Gaussian DGRHS.CLT
variable {ι : Type*} [Fintype ι]

/-- Almost-everywhere variant of `bounded_observable_pointwise_freeEnergy`: the pointwise
bound is only needed `μ`-a.e.; when `k = 0` one additionally needs the `ν`-a.e. bound `|a| ≤ d`
(automatic if `ν ≪ μ`). -/
theorem bounded_observable_pointwise_freeEnergy_ae {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a E : S→ℝ) (ha : StronglyMeasurable a) (hE : StronglyMeasurable E)
    (A L b k d : ℝ) (hA : ∀ x,|a x|≤A) (hL : ∀ x,L≤E x)
    (hb : 0<b) (hk : 0≤k) (hk0 : k=0 → ∀ᵐ x ∂ν,|a x|≤d)
    (hpoint : ∀ᵐ x ∂μ,|a x|≤k*E x+d) :
    Integrable a ν ∧ ((|∫ x,a x ∂ν| : ℝ):EReal)≤
      (k:EReal)*boundedEnergyFreeEnergy μ ν E L b+(d:EReal) := by
  have hai : Integrable a ν := (integrable_const A).mono' ha.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x=>by simpa only [Real.norm_eq_abs] using hA x)
  refine ⟨hai,?_⟩
  have habs : |∫ x,a x ∂ν|≤∫ x,|a x| ∂ν := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm a (μ:=ν)
  have hAbsProper : Integrable (fun x=>|a x|) ν := by
    simpa only [Real.norm_eq_abs] using hai.norm
  by_cases hk0' : k=0
  · have hbnd : (∫ x,|a x| ∂ν)≤d := by
      have h := integral_mono_ae (f:=fun x=>|a x|) (g:=fun _=>d) hAbsProper
        (integrable_const d) (hk0 hk0')
      simpa only [Real.norm_eq_abs,integral_const,probReal_univ,one_smul] using h
    simpa only [hk0',EReal.coe_zero,zero_mul,zero_add,EReal.coe_le_coe_iff] using habs.trans hbnd
  have hkp : 0<k := lt_of_le_of_ne hk (Ne.symm hk0')
  by_cases hKL : klDiv ν μ=∞
  · simp only [boundedEnergyFreeEnergy,hKL,EReal.coe_ennreal_top,
      EReal.top_mul_coe_of_pos (inv_pos.mpr hb),
      EReal.top_add_of_ne_bot (EReal.coe_ennreal_ne_bot _),EReal.top_add_coe,
      EReal.coe_mul_top_of_pos hkp]
    exact le_top
  by_cases hShift : (∫⁻ x,ENNReal.ofReal (E x-L) ∂ν)=∞
  · have hKn : (klDiv ν μ:EReal)*(b⁻¹:ℝ)≠⊥ := by
      rw [←EReal.coe_ennreal_toReal hKL,←EReal.coe_mul]
      exact EReal.coe_ne_bot _
    simp only [boundedEnergyFreeEnergy,hShift,EReal.coe_ennreal_top,
      EReal.add_top_of_ne_bot hKn,EReal.top_add_coe,EReal.coe_mul_top_of_pos hkp]
    exact le_top
  have hShiftProper : Integrable (fun x=>E x-L) ν :=
    (lintegral_ofReal_ne_top_iff_integrable (hE.aestronglyMeasurable.sub aestronglyMeasurable_const)
      (Filter.Eventually.of_forall fun x=>sub_nonneg.mpr (hL x))).mp hShift
  have hEnergy : Integrable E ν := by
    convert hShiftProper.add (integrable_const L) using 1
    funext x
    simp only [Pi.add_apply]
    ring
  have hac : ν ≪ μ := (klDiv_ne_top_iff.mp hKL).1
  have hpν : ∀ᵐ x ∂ν,|a x|≤k*E x+d := hac.ae_le hpoint
  have hBound : |∫ x,a x ∂ν|≤k*(∫ x,E x ∂ν)+d := by
    have h := integral_mono_ae (f:=fun x=>|a x|) (g:=fun x=>k*E x+d)
      hAbsProper ((hEnergy.const_mul k).add (integrable_const d)) hpν
    rw [integral_add (hEnergy.const_mul _) (integrable_const d),integral_const_mul] at h
    simpa only [Real.norm_eq_abs,integral_const,probReal_univ,one_smul] using habs.trans h
  rw [boundedEnergyFreeEnergy_eq_proper μ ν E L b hL hEnergy hKL,
    ←EReal.coe_mul,←EReal.coe_add,EReal.coe_le_coe_iff]
  have hn : 0≤(klDiv ν μ).toReal/b := div_nonneg ENNReal.toReal_nonneg hb.le
  nlinarith [mul_nonneg hk hn]

/-- Collision-free variant of `sourceLog_bounded_pointwise_transfer`. -/
theorem sourceLog_bounded_pointwise_transfer_collisionFree (β : ℝ≥0) (hβ : 0<(β:ℝ))
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (N : ℕ) (hN : 1≤N) (ν : Measure (Fin N→EuclideanSpace ℝ ι)) [IsProbabilityMeasure ν]
    (a : (Fin N→EuclideanSpace ℝ ι)→ℝ) (ha : StronglyMeasurable a)
    (A : ℝ) (hA : ∀ x,|a x|≤A) (Cpw Cpt scale : ℝ) (hCpw : 0≤Cpw)
    (hν0 : Cpw=0 → ∀ᵐ x ∂ν,|a x|≤0) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
    let E := sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
      (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N
    (∀ x,(∀ i j : Fin N,i≠j → x i≠x j) → |a x|≤Cpw*((N:ℝ)*E x+Cpt*scale)) →
      Integrable a ν ∧ ((|∫ x,a x ∂ν| : ℝ):EReal)≤
        (Cpw*(N:ℝ) : ℝ)*sourceLogExtendedFreeEnergy β ρ M N ν+
        (Cpw*Cpt*scale : ℝ) := by
  dsimp only
  intro hpoint
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by exact_mod_cast hd)
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
  let E := sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
    (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N
  have hF : StronglyMeasurable (DGRHS.potential μ W) :=
    stronglyMeasurable_logPhysicalPair.integral_prod_right'
  have hE : StronglyMeasurable E := stronglyMeasurable_sourceCanonicalModulatedEnergy _ _ _
    (stronglyMeasurable_logPhysicalCenteredPair μ) hF N
  have hfloor : ∀ x,sourceLogEnergyFloor ρ M≤E x :=
    fun x=>sourceLogEnergy_uniform_lower_bound hd ρ M hM hρ hpair N (by omega) x
  have hae : ∀ᵐ x ∂Measure.pi (fun _ : Fin N=>μ),
      |a x|≤Cpw*(N:ℝ)*E x+Cpw*Cpt*scale := by
    filter_upwards [density_iid_collision_free ρ N] with x hx
    calc |a x|≤Cpw*((N:ℝ)*E x+Cpt*scale) := hpoint x hx
      _ = Cpw*(N:ℝ)*E x+Cpw*Cpt*scale := by ring
  refine bounded_observable_pointwise_freeEnergy_ae (Measure.pi (fun _ : Fin N=>μ)) ν a E ha hE A
    (sourceLogEnergyFloor ρ M) ((β:ℝ)*(N:ℝ)) (Cpw*(N:ℝ)) (Cpw*Cpt*scale) hA hfloor
    (mul_pos hβ (by exact_mod_cast (by omega : 0<N))) (mul_nonneg hCpw (Nat.cast_nonneg N))
    ?_ hae
  intro hk
  have hc : Cpw=0 := (mul_eq_zero.mp hk).resolve_right (Nat.cast_ne_zero.mpr (by omega))
  filter_upwards [hν0 hc] with x hx
  rw [hc]
  simpa using hx

end DGRHS.Entropy

namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma sourceTwoParticle_collisionFree (z : E) (hz : z≠0) :
    ∀ i j : Fin 2,i≠j → (fun k : Fin 2=>if k=0 then (0:E) else z) i≠
      (fun k : Fin 2=>if k=0 then (0:E) else z) j := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · simpa using hz.symm
  · simpa using hz
  · exact absurd rfl hij

/-- Collision-free version of `sourceLog_twoParticle_energy_unbounded`. -/
theorem sourceLog_twoParticle_energy_unbounded_collisionFree (hd : 0<(Fintype.card ι:ℝ))
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) (R : ℝ) :
    ∃ ω : Fin 2→E,(∀ i j : Fin 2,i≠j → ω i≠ω j) ∧ R<sourceCanonicalModulatedEnergy
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair)
      (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b=>logPhysicalPair (a,b)))
      (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b=>logPhysicalPair (a,b)))
      2 ω := by
  classical
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by exact_mod_cast hd)
  let i : ι := Classical.arbitrary ι
  let q : ℝ := (Fintype.card ι:ℝ)/4
  have hq : 0<q := by dsimp [q];positivity
  have hqd : 0<(Fintype.card ι:ℝ)/2-q := by dsimp [q];linarith
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : E=>logPhysicalPair (a,b)
  let I := DGRHS.interactionEnergy μ W
  let B := gaussianRieszPhysicalPotentialConstant q M ι
  let r := Real.exp (-4*(R+B-I+1))
  have hr : 0<r := Real.exp_pos _
  let z : E := EuclideanSpace.single i r
  let ω : Fin 2→E := fun j=>if j=0 then 0 else z
  have hz : ‖z‖=r := by simp [z,PiLp.norm_single,abs_of_pos hr]
  have hzne : z≠0 := norm_pos_iff.mp (by rw [hz];exact hr)
  have hW : logPhysicalPair (0,z)=4*(R+B-I+1) := by
    simp [logPhysicalPair,hz,r]
  have hpot0 := (logPhysicalPotential_proper_bounds q hq hqd ρ M hM hρ hpair 0).2.2
  have hpotz := (logPhysicalPotential_proper_bounds q hq hqd ρ M hM hρ hpair z).2.2
  change DGRHS.potential μ W 0≤B at hpot0
  change DGRHS.potential μ W z≤B at hpotz
  have hraw := sourceCanonicalModulatedEnergy_raw μ W
    (fun a b=>by dsimp [W,logPhysicalPair];rw [norm_sub_rev]) 2 (by norm_num) ω
  have hsum : DGRHS.CanonicalVariance.offDiagonalSum (Function.uncurry W) ω=
      2*logPhysicalPair (0,z) := sourceLog_twoParticle_offDiagonal z
  refine ⟨ω,sourceTwoParticle_collisionFree z hzne,?_⟩
  change R<sourceCanonicalModulatedEnergy (fun p=>DGRHS.centeredKernel μ W p.1 p.2)
    (DGRHS.potential μ W) I 2 ω
  rw [hraw,hsum,hW]
  norm_num [ω,Fin.sum_univ_two]
  change R<1/8*(2*(4*(R+B-I+1)))-1/2*(DGRHS.potential μ W 0+DGRHS.potential μ W z)+I
  linarith

theorem sourceLog_thermal_pointwise_constant_nonneg_collisionFree
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (n : ℕ) (v : E→E) (Cpw Cpt : ℝ)
    (hpoint : ∀ N : ℕ,1≤N→∀ ω : Fin N→E,(∀ i j : Fin N,i≠j → ω i≠ω j) →
      |sourceTransportEnergy (gaussianRieszDensityMeasure ρ) (sourceLogTransportKernel n v) N ω|≤
        Cpw*(sourceCanonicalModulatedEnergy
          (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair)
          (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b=>logPhysicalPair (a,b)))
          (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b=>logPhysicalPair (a,b))) N ω+
          Cpt*Real.log (Real.exp 1+(N:ℝ))/(N:ℝ))) : 0≤Cpw := by
  by_contra hc
  have hcneg : Cpw<0 := lt_of_not_ge hc
  obtain ⟨ω,hcf,hω⟩ := sourceLog_twoParticle_energy_unbounded_collisionFree hd ρ M hM hρ hpair
    (-Cpt*Real.log (Real.exp 1+(2:ℝ))/2)
  have hb := hpoint 2 (by norm_num) ω hcf
  have hpos : 0<sourceCanonicalModulatedEnergy
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair)
      (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b=>logPhysicalPair (a,b)))
      (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b=>logPhysicalPair (a,b))) 2 ω+
      Cpt*Real.log (Real.exp 1+(2:ℝ))/2 := by linarith
  have hneg := mul_neg_of_neg_of_pos hcneg hpos
  norm_num only [Nat.cast_ofNat] at hb
  exact (not_lt_of_ge ((abs_nonneg _).trans hb)) hneg

theorem exists_sourceLog_thermal_minimum_source_collisionFree (n : ℕ) (hn : 0 < n) :
    ∃ Csr : ℝ, 0 < Csr ∧ ∀ {K : ℝ≥0}
      {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}, LipschitzWith K v →
      0 < (K : ℝ) → 0 < (Fintype.card ι : ℝ) →
      ∀ (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ), 0 ≤ M →
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume, ρ x ≤ M) →
      Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
        (gaussianRieszDensityMeasure ρ)) →
      ∃ βloc : ℝ, 0 < βloc ∧ ∀ β : ℝ≥0, 0 < (β : ℝ) →
      ∃ Cub Cpf : ℝ, 1 ≤ Cub ∧ 1 ≤ Cpf ∧
      let μ := gaussianRieszDensityMeasure ρ
      let W := fun a b => logPhysicalPair (a,b)
      let I := DGRHS.interactionEnergy μ W
      let ε := sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ)^n)
      let Cem := sourceLogTransportCem (β : ℝ) βloc I
        DGRHS.Concentration.glzUniversalTailConstant Cub
      0 < ε ∧ 0 < Cem ∧
      ∀ Cpw Cpt : ℝ,
      (∀ N : ℕ, 1 ≤ N → ∀ x : Fin N → EuclideanSpace ℝ ι,
        (∀ i j : Fin N, i ≠ j → x i ≠ x j) →
        |sourceTransportEnergy μ (sourceLogTransportKernel n v) N x| ≤
          Cpw*(sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
            (DGRHS.potential μ W) I N x +
            Cpt*Real.log (Real.exp 1+(N : ℝ))/(N : ℝ))) →
      ∀ N : ℕ, 1 ≤ N → ∀ (ν : Measure (Fin N → EuclideanSpace ℝ ι))
        [IsProbabilityMeasure ν],
      (Cpw = 0 → ν ≪ Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ)) →
      Integrable (fun x => (N : ℝ)*sourceTransportEnergy μ
        (sourceLogTransportKernel n v) N x) ν ∧
      ((|∫ x, (N : ℝ)*sourceTransportEnergy μ (sourceLogTransportKernel n v) N x ∂ν| : ℝ) : EReal) ≤
        min ((((β : ℝ)/ε)*(N : ℝ) : ℝ)*sourceLogCollisionFreeEnergy β ρ M N ν +
          (ε⁻¹*(Real.log Cpf+Real.log Cem) : ℝ))
          ((Cpw*(N : ℝ) : ℝ)*sourceLogCollisionFreeEnergy β ρ M N ν +
            (Cpw*Cpt*Real.log (Real.exp 1+(N : ℝ)) : ℝ)) := by
  obtain ⟨Csr, hC, hfactory⟩ := exists_sourceLog_entropic_commutator (ι := ι) n hn
  refine ⟨Csr, hC, ?_⟩
  intro K v hv hK hd ρ M hM hμ hρ hpair
  obtain ⟨βloc, hloc, hβfactory⟩ := hfactory hv hK hd ρ M hM hρ hpair
  refine ⟨βloc, hloc, ?_⟩
  intro β hβ
  obtain ⟨Cub, Cpf, hCub, hCpf, _, hε, hCem, _, _, _, hent⟩ := hβfactory β hβ
  refine ⟨Cub, Cpf, hCub, hCpf, hε, hCem, ?_⟩
  intro Cpw Cpt hpoint
  have hCpw := sourceLog_thermal_pointwise_constant_nonneg_collisionFree hd ρ M hM hρ hpair
    n v Cpw Cpt hpoint
  intro N hN ν hν hν0
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by exact_mod_cast hd)
  obtain ⟨ha, A, hA, _⟩ := sourceLogTransport_all_law_proper n hn hv
    (gaussianRieszDensityMeasure ρ) N (by omega)
  obtain ⟨hi, hb1⟩ := hent N hN ν
  have hnr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hscaled (x : Fin N → EuclideanSpace ℝ ι) (hx : ∀ i j : Fin N, i ≠ j → x i ≠ x j) :
      |(N : ℝ)*sourceTransportEnergy (gaussianRieszDensityMeasure ρ)
        (sourceLogTransportKernel n v) N x| ≤
      Cpw*((N : ℝ)*sourceCanonicalModulatedEnergy
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair)
        (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b)))
        (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b))) N x +
        Cpt*Real.log (Real.exp 1+(N : ℝ))) := by
    have hm := mul_le_mul_of_nonneg_left (hpoint N hN x hx) (Nat.cast_nonneg N)
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    convert hm using 1 <;> field_simp <;> ring
  have hν0' : Cpw = 0 → ∀ᵐ x ∂ν, |(N : ℝ)*sourceTransportEnergy (gaussianRieszDensityMeasure ρ)
      (sourceLogTransportKernel n v) N x| ≤ 0 := by
    intro hc
    filter_upwards [(hν0 hc).ae_le (density_iid_collision_free ρ N)] with x hx
    have h := hscaled x hx
    rw [hc, zero_mul] at h
    exact h
  obtain ⟨_, hb2⟩ := sourceLog_bounded_pointwise_transfer_collisionFree β hβ hd ρ M hM hρ hpair N hN ν
    (fun x => (N : ℝ)*sourceTransportEnergy (gaussianRieszDensityMeasure ρ)
      (sourceLogTransportKernel n v) N x) ha A hA Cpw Cpt
      (Real.log (Real.exp 1+(N : ℝ))) hCpw hν0' hscaled
  rw [←sourceLogCollisionFreeEnergy_eq β hβ hd ρ M N hN ν] at hb2
  exact ⟨hi, le_min hb1 hb2⟩

theorem sourceLog_thermal_minimum_zero_source_collisionFree (n : ℕ) (hn : 0 < n)
    {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hv : LipschitzWith 0 v)
    (β : ℝ≥0) (hβ : 0 < (β : ℝ)) (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
      (gaussianRieszDensityMeasure ρ))) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cpf : ℝ, 1 ≤ Cpf ∧ ∀ Cpw Cpt : ℝ,
      (∀ N : ℕ, 1 ≤ N → ∀ x : Fin N → EuclideanSpace ℝ ι,
        (∀ i j : Fin N, i ≠ j → x i ≠ x j) →
        |sourceTransportEnergy (gaussianRieszDensityMeasure ρ) (sourceLogTransportKernel n v) N x| ≤
          Cpw*(sourceCanonicalModulatedEnergy
            (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair)
            (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b)))
            (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b))) N x +
            Cpt*Real.log (Real.exp 1+(N : ℝ))/(N : ℝ))) →
      ∀ N : ℕ, 1 ≤ N → ∀ (ν : Measure (Fin N → EuclideanSpace ℝ ι))
        [IsProbabilityMeasure ν],
      Integrable (fun x => (N : ℝ)*sourceTransportEnergy (gaussianRieszDensityMeasure ρ)
        (sourceLogTransportKernel n v) N x) ν ∧
      ((|∫ x, (N : ℝ)*sourceTransportEnergy (gaussianRieszDensityMeasure ρ)
        (sourceLogTransportKernel n v) N x ∂ν| : ℝ) : EReal) ≤
        min ((((β : ℝ)/ε)*(N : ℝ) : ℝ)*sourceLogCollisionFreeEnergy β ρ M N ν +
          (ε⁻¹*(Real.log Cpf+Real.log 1) : ℝ))
          ((Cpw*(N : ℝ) : ℝ)*sourceLogCollisionFreeEnergy β ρ M N ν +
            (Cpw*Cpt*Real.log (Real.exp 1+(N : ℝ)) : ℝ)) := by
  obtain ⟨Cpf, hCpf, hent⟩ := sourceLog_entropic_commutator_zero n hn hv β hβ hd ρ M hM hρ hpair ε hε
  refine ⟨Cpf, hCpf, ?_⟩
  intro Cpw Cpt hpoint N hN ν hν
  have hCpw := sourceLog_thermal_pointwise_constant_nonneg_collisionFree hd ρ M hM hρ hpair
    n v Cpw Cpt hpoint
  obtain ⟨hi, hb1⟩ := (hent N hN).2 ν
  let a := fun x : Fin N → EuclideanSpace ℝ ι => (N : ℝ)*sourceTransportEnergy
    (gaussianRieszDensityMeasure ρ) (sourceLogTransportKernel n v) N x
  have ha0 : a = fun _ => 0 := by
    funext x
    simp only [a, sourceTransportEnergy_zero_lipschitz (gaussianRieszDensityMeasure ρ) n hn hv, mul_zero]
  have ha : StronglyMeasurable a := by rw [ha0]; exact stronglyMeasurable_const
  have hbound : ∀ x, |a x| ≤ 0 := by simp [ha0]
  have hnr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hscaled (x : Fin N → EuclideanSpace ℝ ι) (hx : ∀ i j : Fin N, i ≠ j → x i ≠ x j) :
      |a x| ≤ Cpw*((N : ℝ)*sourceCanonicalModulatedEnergy
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair)
        (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b)))
        (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b))) N x +
        Cpt*Real.log (Real.exp 1+(N : ℝ))) := by
    have hm := mul_le_mul_of_nonneg_left (hpoint N hN x hx) (Nat.cast_nonneg N)
    dsimp only [a]
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    convert hm using 1 <;> field_simp <;> ring
  obtain ⟨_, hb2⟩ := sourceLog_bounded_pointwise_transfer_collisionFree β hβ hd ρ M hM hρ hpair N hN ν
    a ha 0 hbound Cpw Cpt (Real.log (Real.exp 1+(N : ℝ))) hCpw
    (fun _ => Filter.Eventually.of_forall hbound) hscaled
  rw [←sourceLogCollisionFreeEnergy_eq β hβ hd ρ M N hN ν] at hb2
  exact ⟨hi, le_min hb1 hb2⟩

end DGRHS.Commutator
#check @DGRHS.Entropy.bounded_observable_pointwise_freeEnergy_ae
#print axioms DGRHS.Entropy.bounded_observable_pointwise_freeEnergy_ae
#check @DGRHS.Entropy.sourceLog_bounded_pointwise_transfer_collisionFree
#print axioms DGRHS.Entropy.sourceLog_bounded_pointwise_transfer_collisionFree
#check @DGRHS.Commutator.sourceLog_twoParticle_energy_unbounded_collisionFree
#print axioms DGRHS.Commutator.sourceLog_twoParticle_energy_unbounded_collisionFree
#check @DGRHS.Commutator.sourceLog_thermal_pointwise_constant_nonneg_collisionFree
#print axioms DGRHS.Commutator.sourceLog_thermal_pointwise_constant_nonneg_collisionFree
#check @DGRHS.Commutator.exists_sourceLog_thermal_minimum_source_collisionFree
#print axioms DGRHS.Commutator.exists_sourceLog_thermal_minimum_source_collisionFree
#check @DGRHS.Commutator.sourceLog_thermal_minimum_zero_source_collisionFree
#print axioms DGRHS.Commutator.sourceLog_thermal_minimum_zero_source_collisionFree
