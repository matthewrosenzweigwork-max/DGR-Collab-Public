import DGRHS.Commutator.SourceRieszLocalPartition

/-! Common-density Riesz partition constants. Adaptation of the checked physical
master construction: all deterministic scales, envelopes and the finite maximum
are chosen before the probability density. Accepted source modules are unchanged. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology BigOperators
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Concentration
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The low-scale constant is uniform over all probability densities bounded by M. -/
theorem sourceRieszCommon_cutoff_moment (s β M : ℝ) (hs : 0<s) (hβ : 0≤β)
    (hM : 0≤M) (ha : 0<(Fintype.card ι:ℝ)/2-s) :
    ∃ δ : ℝ,0<δ ∧ δ<1 ∧ ∃ C : ℝ,∀ ρ : E→ℝ,
      IsProbabilityMeasure (gaussianRieszDensityMeasure ρ) → (∀ᵐ x ∂volume,ρ x≤M) →
      ∀ η : ℝ,0<η → η≤δ → ∀ n : ℕ,1≤n →
      Integrable (fun ω => Real.exp (β*iidNegativeStatistic n
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszTruncatedPair s η)) ω))
        (Measure.pi (fun _ : Fin n=>gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (β*iidNegativeStatistic n
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszTruncatedPair s η)) ω)
        ∂Measure.pi (fun _ : Fin n=>gaussianRieszDensityMeasure ρ))≤C := by
  obtain ⟨δ,hδ,hδ1,hrow,hop⟩ := exists_gaussianRieszMaster_scale (ι := ι) s β M hM ha
  let A := 1+4*β*gaussianRieszShortConstant s M ι
  let u₀ := 1+8*β*(gaussianRieszSourceCoefficient s/s*δ^(-s))
  have hc : 0 ≤ gaussianRieszShortConstant s M ι := by
    have hp := (gaussianRieszSourceCoefficient_pos s hs).le
    have hd : 0 < (Fintype.card ι : ℝ)-s := by linarith
    unfold gaussianRieszShortConstant
    positivity
  have hA : 0 < A := by dsimp [A];positivity
  have hAcontrol : 4*β*gaussianRieszShortConstant s M ι ≤ A := by dsimp [A];linarith
  have hD : 0 ≤ gaussianRieszSourceCoefficient s/s*δ^(-s) := by
    have hp := (gaussianRieszSourceCoefficient_pos s hs).le
    positivity
  have hu₀ : 1 ≤ u₀ := by
    have hh := mul_nonneg (by positivity : 0 ≤ 8*β) hD
    dsimp [u₀]
    linarith
  have hlow : 8*β*(gaussianRieszSourceCoefficient s/s*δ^(-s)) ≤ u₀ := by dsimp [u₀];linarith
  let K := (1+gaussianRieszAdaptiveC0 s δ β+gaussianRieszAdaptiveC1 s β A ι)^2
  have hdim : 0 < (Fintype.card ι : ℝ) := by linarith
  have hp : 2*s/(Fintype.card ι : ℝ) < 1 := riesz_master_power_lt_one _ _ hdim (by linarith)
  obtain ⟨N₀,hN₀⟩ := sublinear_power_envelope_growth (2*glzUniversalTailConstant^2) 0 K
    (2*s/(Fintype.card ι : ℝ)) hp
  refine ⟨δ,hδ,hδ1,masterEnvelopeConstant u₀ N₀
    (fun n => 0+K*(n : ℝ)^(2*s/(Fintype.card ι : ℝ))),?_⟩
  intro ρ hprob hρ
  let _ := hprob
  let μ := gaussianRieszDensityMeasure ρ
  let I := {η : ℝ // 0 < η ∧ η ≤ δ}
  let X := fun (θ : I) (n : ℕ) (ω : Fin n → EuclideanSpace ℝ ι) =>
    β*iidNegativeStatistic n (hoeffdingCentered μ (gaussianRieszTruncatedPair s θ.val)) ω
  have hX (θ : I) (n : ℕ) (hn : 1 ≤ n) : AEMeasurable (X θ n) (Measure.pi (fun _ : Fin n => μ)) :=
    (measurable_gaussianRieszCutoff_exponent s θ.val β hs θ.property.1 μ n).aemeasurable
  let data := fun (θ : I) (n : ℕ) (hn : 1 ≤ n) => gaussianRieszMasterCutoffData s θ.val δ β A u₀
    hs θ.property.1 θ.property.2 hδ hβ ha ρ M hM hρ n hn hA hAcontrol hu₀ hlow hrow.le hop.le
  have hsize (θ : I) (n : ℕ) (hn : 1 ≤ n) :
      masterCutoffSize μ (data θ n hn).kernel (data θ n hn).cap u₀ ≤ 0+K*(n : ℝ)^(2*s/(Fintype.card ι : ℝ)) := by
    have hb (u : ℝ) (hu : u₀ ≤ u) := gaussianRieszAdaptiveBand_cap_ess_bounds s θ.val δ β A hs
      θ.property.2 hδ hβ hA ha ρ M hM hρ n hn u (hu₀.trans hu)
    have hex := gaussianRieszAdaptive_exponents (Fintype.card ι : ℝ) s hs (by linarith)
    have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hz := (masterCutoffSize_le_adaptive_power μ (fun u => gaussianRieszAdaptiveBand s θ.val δ β A n u ρ)
      (fun u => gaussianRieszAdaptiveCap s θ.val δ β A n u ι) (n : ℝ) u₀
      (s/((Fintype.card ι : ℝ)-s)) (gaussianRieszAdaptiveC0 s δ β) (gaussianRieszAdaptiveC1 s β A ι)
      hn' hu₀ hex.1 hex.2.1 (hb u₀ le_rfl).1 (hb u₀ le_rfl).2.1
      (fun u hu => (hb u hu).2.2.2.1) (fun u hu => (hb u hu).2.2.2.2)).2
    rw [hex.2.2] at hz
    simpa only [data,gaussianRieszMasterCutoffData,K,zero_add] using hz
  have hC := master_uniform_exponential_envelope μ X hX u₀ hu₀ N₀ data
    (fun n => 0+K*(n : ℝ)^(2*s/(Fintype.card ι : ℝ))) hsize hN₀
  exact fun η hη hηδ n hn => hC ⟨η,hη,hηδ⟩ n hn

/-- One full singular canonical bound chosen before the density. -/
theorem sourceRieszCommon_full_moment (s β M : ℝ) (hs : 0<s) (hβ : 0≤β)
    (hM : 0≤M) (ha : 0<(Fintype.card ι:ℝ)/2-s) :
    ∃ C : ℝ,∀ ρ : E→ℝ,IsProbabilityMeasure (gaussianRieszDensityMeasure ρ) →
      (∀ᵐ x ∂volume,ρ x≤M) → ∀ n : ℕ,1≤n →
      Integrable (fun ω=>Real.exp (β*iidNegativeStatistic n
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s)) ω))
        (Measure.pi (fun _ : Fin n=>gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (β*iidNegativeStatistic n
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s)) ω)
        ∂Measure.pi (fun _ : Fin n=>gaussianRieszDensityMeasure ρ))≤C := by
  obtain ⟨δ,hδ,hδ1,C,hC⟩ := sourceRieszCommon_cutoff_moment s β M hs hβ hM ha
  refine ⟨C,?_⟩
  intro ρ hprob hρ n hn
  let _ := hprob
  let η := fun j : ℕ => δ*(((j+1 : ℕ):ℝ))⁻¹
  have hη : ∀ j,0<η j := by intro j;dsimp[η];positivity
  have hηδ : ∀ j,η j≤δ := by
    intro j
    have hj : (1:ℝ)≤((j+1:ℕ):ℝ) := by exact_mod_cast Nat.le_add_left 1 j
    dsimp[η]
    calc
      _ ≤ δ*1 := mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hj) hδ.le
      _ = δ := mul_one _
  have hcast : Tendsto (fun j : ℕ=>((j+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hη0 : Tendsto η atTop (𝓝 0) := by
    simpa only [η,Pi.inv_apply,mul_zero] using hcast.inv_tendsto_atTop.const_mul δ
  exact exponential_integrable_of_ae_tendsto
    (Measure.pi (fun _ : Fin n=>gaussianRieszDensityMeasure ρ))
    (fun j ω=>β*iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
      (gaussianRieszTruncatedPair s (η j))) ω)
    (fun ω=>β*iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
      (gaussianRieszPhysicalPair s)) ω)
    (fun j=>(hC ρ hprob hρ (η j) (hη j) (hηδ j) n hn).1) C
    (fun j=>(hC ρ hprob hρ (η j) (hη j) (hηδ j) n hn).2)
    (ae_tendsto_gaussianRieszParticleCutoff s β hs ha ρ M hM hρ η hη hη0 n)

/-- Actual source particle moment with a common constant BEFORE rho and N. -/
theorem sourceRieszCommon_particle_moment (s β M : ℝ) (hs : 0<s) (hβ : 0≤β)
    (hM : 0≤M) (hd : 2*s<(Fintype.card ι:ℝ)) :
    ∃ C : ℝ,0<C ∧ ∀ ρ : E→ℝ,IsProbabilityMeasure (gaussianRieszDensityMeasure ρ) →
      (∀ᵐ x ∂volume,ρ x≤M) → ∀ N : ℕ,1≤N →
      Integrable (fun ω=>Real.exp (sourceRieszLocalParticleExponent ρ s β N ω))
        (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) ∧
      1≤(∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))≤C := by
  obtain ⟨C,hC⟩ := sourceRieszCommon_full_moment (ι:=ι) s β M hs hβ hM (by linarith)
  let B := Real.exp (β*gaussianRieszPhysicalPotentialConstant s M ι)
  refine ⟨B*max C 1,by dsimp[B];positivity,?_⟩
  intro ρ hprob hρ N hN
  let _ := hprob
  have hn : 0<N := lt_of_lt_of_le (by norm_num : (0:ℕ)<1) hN
  obtain ⟨hi,hb⟩ := hC ρ hprob hρ N hN
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
#check DGRHS.Commutator.sourceRieszCommon_cutoff_moment
#print axioms DGRHS.Commutator.sourceRieszCommon_cutoff_moment

#check DGRHS.Commutator.sourceRieszCommon_full_moment
#print axioms DGRHS.Commutator.sourceRieszCommon_full_moment
#check DGRHS.Commutator.sourceRieszCommon_particle_moment
#print axioms DGRHS.Commutator.sourceRieszCommon_particle_moment
