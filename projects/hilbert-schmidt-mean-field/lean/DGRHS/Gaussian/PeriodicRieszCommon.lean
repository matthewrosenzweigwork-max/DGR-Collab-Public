import DGRHS.Gaussian.PeriodicRieszEntropicCommutatorPrinted

/-!
Packet P11a, unit 3 (Riesz, part 1): torus Riesz partition bounds with constants chosen BEFORE the
density (the "common" or family form needed for the measurable time coefficients of Theorem 2.9).

The existing torus bounds `periodicRieszCutoff_uniform_exponential`, `periodicRieszKernel_uniform_exponential`,
`periodicRieszWeight_uniform`, `periodicRieszParticleWeight_uniform` state `∃ C` after the density `ρ`.
Their proofs only use `ρ` through the data of the master layer-cake, whose scale, size and growth
constants depend on `(s, β, M, d)` alone; the final constant is the explicit
`masterEnvelopeConstant`.  Here the same proof is rearranged so that the constant is produced before
`ρ` (torus version of `sourceRieszCommon_cutoff_moment`, `sourceRieszCommon_particle_moment`).
-/

noncomputable section
open MeasureTheory InformationTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The uniform exponential moment of the periodic Riesz cutoff family with a constant chosen before
the density. -/
theorem periodicRieszCommon_cutoff_exponential (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hsd : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      ∀ τ : ℝ, 0 ≤ τ → ∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω => Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszMellinGreen s τ (q.1 - q.2))) ω))
        (Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszMellinGreen s τ (q.1 - q.2))) ω)
        ∂Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ≤ C := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  obtain ⟨a, ha, ha1, hrow, hop⟩ := exists_periodicRieszMaster_scale (ι := ι) s β M hsd
  have hF := (periodicRieszMellinFactor_pos (ι := ι) s hs).le
  have hD := periodicHeatDiagonalGlobalConstant_nonneg (ι := ι)
  have hh : 0 < ((Fintype.card ι : ℝ) - s) / 2 := by linarith
  let A := 1 + 4 * β * (M * (periodicRieszMellinFactor ι s / (((Fintype.card ι : ℝ) - s) / 2)))
  let T0 := β * (2 * periodicRieszMellinFactor ι s * periodicHeatDiagonalGlobalConstant ι *
    (a ^ (-s / 2) / (s / 2)))
  let u₀ := 1 + 4 * T0
  have hT0 : 0 ≤ T0 := by
    have : 0 ≤ a ^ (-s / 2) := Real.rpow_nonneg ha.le _
    dsimp [T0]; positivity
  have hAn : 0 ≤ 4 * β * (M * (periodicRieszMellinFactor ι s /
      (((Fintype.card ι : ℝ) - s) / 2))) := by positivity
  have hA : 0 < A := by dsimp [A]; linarith
  have hAcontrol : 4 * β * (M * (periodicRieszMellinFactor ι s /
      (((Fintype.card ι : ℝ) - s) / 2))) ≤ A := by dsimp [A]; linarith
  have hu₀ : 1 ≤ u₀ := by dsimp [u₀]; linarith
  have hlow : 4 * T0 ≤ u₀ := by dsimp [u₀]; linarith
  let K := (1 + periodicRieszAdaptiveC0 s a β ι + periodicRieszAdaptiveC1 s β A ι) ^ 2
  have hp : 2 * s / (Fintype.card ι : ℝ) < 1 := riesz_master_power_lt_one _ _ hd (by linarith)
  obtain ⟨N₀, hN₀⟩ := sublinear_power_envelope_growth (2 * glzUniversalTailConstant ^ 2) 0 K
    (2 * s / (Fintype.card ι : ℝ)) hp
  refine ⟨masterEnvelopeConstant u₀ N₀
    (fun n => 0 + K * (n : ℝ) ^ (2 * s / (Fintype.card ι : ℝ))), ?_⟩
  intro ρ hprob hρ τ hτ n hn
  let μ := periodicCappedDensityMeasure ρ
  let I := {τ : ℝ // 0 ≤ τ}
  let X := fun (θ : I) (n : ℕ) (ω : Fin n → PeriodicTorus ι) =>
    β * iidNegativeStatistic n (hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszMellinGreen s θ.val (q.1 - q.2))) ω
  have hX (θ : I) (n : ℕ) (hn : 1 ≤ n) :
      AEMeasurable (X θ n) (Measure.pi (fun _ : Fin n => μ)) :=
    (measurable_periodicRieszCutoff_exponent s θ.val β μ n).aemeasurable
  let data := fun (θ : I) (n : ℕ) (hn : 1 ≤ n) => periodicRieszMasterCutoffData s θ.val a β A u₀
    hs hsd θ.property ha ha1.le hβ ρ M hM hρ n hn hA hAcontrol hu₀ hlow hrow.le hop.le
  have hsize (θ : I) (n : ℕ) (hn : 1 ≤ n) :
      masterCutoffSize μ (data θ n hn).kernel (data θ n hn).cap u₀ ≤
        0 + K * (n : ℝ) ^ (2 * s / (Fintype.card ι : ℝ)) := by
    have hb (u : ℝ) (hu : u₀ ≤ u) :=
      periodicRieszAdaptiveBand_cap_ess_bounds s θ.val a β A hs hsd θ.property ha ha1.le hβ hA ρ n
        hn u (hu₀.trans hu)
    have hex := gaussianRieszAdaptive_exponents (Fintype.card ι : ℝ) s hs (by linarith)
    have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hz := (masterCutoffSize_le_adaptive_power μ
      (fun u => periodicRieszAdaptiveBand s θ.val a β A n u ρ)
      (fun u => periodicRieszAdaptiveCap s a β A n u ι) (n : ℝ) u₀
      (s / ((Fintype.card ι : ℝ) - s)) (periodicRieszAdaptiveC0 s a β ι)
      (periodicRieszAdaptiveC1 s β A ι)
      hn' hu₀ hex.1 hex.2.1 (hb u₀ le_rfl).1 (hb u₀ le_rfl).2.1
      (fun u hu => (hb u hu).2.2.2.1) (fun u hu => (hb u hu).2.2.2.2)).2
    rw [hex.2.2] at hz
    simpa only [data, periodicRieszMasterCutoffData, K, zero_add] using hz
  exact master_uniform_exponential_envelope μ X hX u₀ hu₀ N₀ data
    (fun n => 0 + K * (n : ℝ) ^ (2 * s / (Fintype.card ι : ℝ))) hsize hN₀ ⟨τ, hτ⟩ n hn

/-- The uniform exponential moment of the exact periodic Riesz kernel, constant before the density. -/
theorem periodicRieszCommon_kernel_exponential (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) → ∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω => Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))) ω))
        (Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))) ω)
        ∂Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ≤ C := by
  obtain ⟨C, hC⟩ := periodicRieszCommon_cutoff_exponential s β hs hβ hs2 M hM
  refine ⟨C, fun ρ hprob hρ n hn => ?_⟩
  obtain ⟨hi, hb⟩ := hC ρ hρ 0 le_rfl n hn
  have hpair : (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszMellinGreen s 0 (q.1 - q.2))
      =ᵐ[(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)]
      (fun q => periodicRieszKernel s hs2 (q.1 - q.2)) :=
    periodicDensity_pair_ae_of_haar ρ _ (periodicRieszMellinGreen_ae_kernel s hs2)
  have hstat := ae_physical_iidNegativeStatistic_congr (periodicCappedDensityMeasure ρ) n _ _
    (ae_hoeffdingCentered_congr (periodicCappedDensityMeasure ρ) _ _ hpair)
  have hexp : (fun ω => Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszMellinGreen s 0 (q.1 - q.2))) ω))
      =ᵐ[Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)]
      (fun ω => Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))) ω)) := by
    filter_upwards [hstat] with ω hω
    rw [hω]
  exact ⟨hi.congr hexp, by rw [← integral_congr_ae hexp]; exact hb⟩

/-- Modulated weights of the spectral kernel with a common constant. -/
theorem periodicRieszCommon_weight (s γ : ℝ) (hs0 : 0 < s) (hγ : 0 ≤ γ)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) → ∀ N : ℕ,
      let μ := periodicCappedDensityMeasure ρ
      let W := fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)
      let h := periodicRieszCentered s hs2 μ
      let F := DGRHS.potential μ W
      let I := DGRHS.interactionEnergy μ W
      Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (DGRHS.CLT.sourceParticleExponent h F I γ N x))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → PeriodicTorus ι, Real.exp (DGRHS.CLT.sourceParticleExponent h F I γ N x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ C := by
  obtain ⟨C0, hC0⟩ := periodicRieszCommon_kernel_exponential s γ hs0 hγ hs2 M hM
  set pk := M * ∫ z, |periodicRieszKernel s hs2 z| ∂periodicHaar ι with hpk
  have hpk0 : 0 ≤ pk := mul_nonneg hM (integral_nonneg fun z => abs_nonneg _)
  refine ⟨max (Real.exp (γ * pk) * max C0 0) 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro ρ hprob hρ N
  intro μ W h F I
  have hW : Integrable (Function.uncurry W) (μ.prod μ) :=
    periodicDensityPair_integrable_of_haar ρ M hρ _ (periodicRieszKernel_integrable s hs2)
  have hF : Integrable F μ := DGRHS.integrable_potential μ W hW
  have hK : ∀ᵐ x ∂μ, F x ≤ pk :=
    Filter.Eventually.of_forall fun x =>
      (le_abs_self _).trans (periodicRieszKernel_potential_abs_le s hs2 ρ M hM hρ x)
  have he (N : ℕ) : (fun x : Fin N → PeriodicTorus ι => Real.exp (γ * iidNegativeStatistic N h x)) =
      (fun x => Real.exp (-γ / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) := by
    funext x
    rw [DGRHS.CLT.iidCanonicalExponent_eq]
  have hProper : ∀ N, 1 ≤ N → Integrable (fun x : Fin N → PeriodicTorus ι =>
      Real.exp (-γ / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x))
      (Measure.pi (fun _ : Fin N => μ)) := by
    intro N hN
    have hi := (hC0 ρ hρ N hN).1
    rw [he N] at hi
    exact hi
  have hBound : ∀ N, 1 ≤ N → (∫ x : Fin N → PeriodicTorus ι,
      Real.exp (-γ / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ max C0 0 := by
    intro N hN
    have hb := (hC0 ρ hρ N hN).2
    rw [he N] at hb
    exact hb.trans (le_max_left _ _)
  have hmom := DGRHS.CLT.sourceWeight_of_canonical_moments h F hF _ hK I γ hγ (max C0 0) hProper hBound
  have hI0 : 0 ≤ I := by
    change 0 ≤ DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b))
    rw [periodicRieszInteraction_eq s hs0 hs2 ρ M hρ]
    exact periodicRieszInteraction_nonneg s hs0 hs2 ρ M hM hρ
  obtain ⟨hi, hb⟩ := hmom N
  refine ⟨hi, hb.trans ((max_le_max ?_ ?_).trans le_rfl)⟩
  · have h1 : Real.exp (γ * (pk - I)) ≤ Real.exp (γ * pk) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact mul_le_mul_of_nonneg_right h1 (le_max_right _ _)
  · have : Real.exp (-γ * I) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    exact this

/-- Particle weights with a common upper constant (torus form of
`sourceRieszCommon_particle_moment`); the Jensen lower bound `1 ≤ ∫` is kept. -/
theorem periodicRieszCommon_particle_weight (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) → ∀ N : ℕ, 1 ≤ N →
      Integrable (fun ω => Real.exp (periodicRieszParticleExponent s ρ β N ω))
        (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
      1 ≤ (∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ C := by
  obtain ⟨C, hC, hW⟩ := periodicRieszCommon_weight s β hs hβ hs2 M hM
  refine ⟨C, hC, fun ρ hprob hρ N hN => ?_⟩
  have hn : 0 < N := by omega
  have hI0 := periodicRieszInteraction_nonneg s hs hs2 ρ M hM hρ
  have hIeq := periodicRieszInteraction_eq s hs hs2 ρ M hρ
  have hexp : (fun ω => Real.exp (periodicRieszParticleExponent s ρ β N ω)) =ᵐ[
      Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)]
      (fun ω => Real.exp (DGRHS.CLT.sourceParticleExponent
        (periodicRieszCentered s hs2 (periodicCappedDensityMeasure ρ))
        (DGRHS.potential (periodicCappedDensityMeasure ρ)
          (fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)))
        (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
          (fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b))) β N ω)) := by
    filter_upwards [periodicRieszSourceExponent_ae s β hs hs2 ρ M hρ N] with ω hω
    rw [periodicRieszParticleExponent_eq s ρ β N hn, ← hω]
  have hW' := hW ρ hρ N
  dsimp only at hW'
  have hi := hW'.1.congr hexp.symm
  have hb : (∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω)
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ C := by
    rw [integral_congr_ae hexp]
    exact hW'.2
  refine ⟨hi, ?_, hb⟩
  have hJ := periodicRieszJensen_lower_integral s β hs hβ hs2 ρ M hM hρ N hN
  have h1 : 1 ≤ Real.exp (β * DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b))) := by
    rw [hIeq]
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (mul_nonneg hβ hI0)
  exact h1.trans hJ

/-- A finite actual extended free energy gives a finite Gibbs relative entropy. -/
lemma periodicRiesz_finiteObjective_GibbsKL (s M : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hM : 0 ≤ M) (β : ℝ) (hβ : 0 < β)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N)
    (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν] (e : ℝ)
    (he : periodicRieszTransportExtendedFreeEnergy s hs2 ρ M β N ν = (e : EReal)) :
    klDiv ν (periodicRieszSingularGibbs s β hs2 ρ N) ≠ ∞ := by
  intro htop
  have hb : 0 < β * (N : ℝ) := mul_pos hβ (by exact_mod_cast (by omega : 0 < N))
  rw [periodicRieszTransportExtendedFreeEnergy_rewrite s hs hs2 M hM β hβ ρ hρ N hN ν,
    htop, EReal.coe_ennreal_top, EReal.top_sub_coe,
    EReal.top_mul_coe_of_pos (inv_pos.mpr hb)] at he
  exact EReal.top_ne_coe e he

/-- Theorem 2.8 (Riesz, `n`, finite-relative-entropy class) with constants `C_pf`, `C_em` that
depend only on `(s, M, n, β)` and the dimension: chosen before the Lipschitz field, the density and
the competitor (torus form of `sourceRieszCommon_finiteObjective_transport`). -/
theorem periodicRieszCommon_finiteObjective_transport (s M : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hM : 0 ≤ M) (β : ℝ) (hβ : 0 < β) :
    ∃ Cpf Cem : ℝ, 1 ≤ Cpf ∧ 1 ≤ Cem ∧ ∀ (K : ℝ≥0) (v : PeriodicTorus ι → E), LipschitzWith K v →
      0 < periodicRieszPositiveTransportParameter s hs2 M n K β ∧
      ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) → ∀ N : ℕ, 1 ≤ N →
      ∀ (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν] (e : ℝ),
      periodicRieszTransportExtendedFreeEnergy s hs2 ρ M β N ν = (e : EReal) →
      Integrable (fun ω => (N : ℝ) * periodicRieszTransportEnergy s n v ρ N ω) ν ∧
      periodicRieszTransportProperFreeEnergy s ρ β N ν = e ∧
      |∫ ω, (N : ℝ) * periodicRieszTransportEnergy s n v ρ N ω ∂ν| ≤
        (β / periodicRieszPositiveTransportParameter s hs2 M n K β) * (N : ℝ) * e +
          (periodicRieszPositiveTransportParameter s hs2 M n K β)⁻¹ *
            (Real.log Cpf + Real.log Cem) := by
  have hL := glzUniversalTailConstant_pos.le
  obtain ⟨Cub, hCub1, hCubfam⟩ : ∃ Cub : ℝ, 1 ≤ Cub ∧
      (periodicRieszLocalBeta s hs2 M < β →
        ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
        (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) → ∀ N : ℕ, 1 ≤ N →
        Integrable (fun ω => Real.exp (periodicRieszParticleExponent s ρ
          (2 * β - periodicRieszLocalBeta s hs2 M) N ω))
          (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
        (∫ ω, Real.exp (periodicRieszParticleExponent s ρ
          (2 * β - periodicRieszLocalBeta s hs2 M) N ω)
          ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ Cub) := by
    by_cases hlarge : periodicRieszLocalBeta s hs2 M < β
    · obtain ⟨Cp1, hCp1, hP1⟩ := periodicRieszCommon_particle_weight s
        (2 * β - periodicRieszLocalBeta s hs2 M) hs (by linarith) hs2 M hM
      refine ⟨max Cp1 1, le_max_right _ _, fun _ ρ hprob hρ N hN => ?_⟩
      have h := hP1 ρ hρ N hN
      exact ⟨h.1, h.2.2.trans (le_max_left _ _)⟩
    · exact ⟨1, le_rfl, fun h => absurd h hlarge⟩
  obtain ⟨Cp, hCp, hPf⟩ := periodicRieszCommon_particle_weight s β hs hβ.le hs2 M hM
  have hCem1 := one_le_periodicRieszTransportCem β (periodicRieszLocalBeta s hs2 M)
    glzUniversalTailConstant Cub hL hCub1
  refine ⟨max Cp 1, periodicRieszTransportCem β (periodicRieszLocalBeta s hs2 M)
    glzUniversalTailConstant Cub, le_max_right _ _, hCem1, ?_⟩
  intro K v hv
  refine ⟨periodicRieszPositiveTransportParameter_pos s hs hs2 M hM n K β hβ, ?_⟩
  intro ρ hprob hρ N hN ν hν e he
  have hNum := periodicRieszTransport_numerator_explicit s M n hn hs hs2 hM β hβ Cub hv ρ hρ
    (fun hl N hN => hCubfam hl ρ hρ N hN)
  have hdiv : periodicRieszTransportCem β (periodicRieszLocalBeta s hs2 M)
      glzUniversalTailConstant Cub ≤ periodicRieszTransportCem β (periodicRieszLocalBeta s hs2 M)
        glzUniversalTailConstant Cub * 1 := by rw [mul_one]
  have hMom := periodicRieszTransport_Gibbs_moment_of_numerator_lower s M n hn hs hs2 hM β hβ _ 1 _
    hCem1 one_pos hdiv hv ρ hρ hNum (fun N hN => (hPf ρ hρ N hN).2.1)
  have hKL := periodicRiesz_finiteObjective_GibbsKL s M hs hs2 hM β hβ ρ hρ N hN ν e he
  obtain ⟨hac, hbg, hllr, ha, hb⟩ := periodicRieszTransport_finiteKL_entropic_of_moments s M n hn hs
    hs2 hM β hβ (max Cp 1) _ hv ρ hρ hMom
    (fun N hN => (hPf ρ hρ N hN).2.2.trans (le_max_left _ _)) N hN ν hKL
  have hext := periodicRieszTransportExtendedFreeEnergy_eq_proper s hs hs2 M hM β hβ ρ hρ N hN ν
    hac hbg hllr
  have hpe : periodicRieszTransportProperFreeEnergy s ρ β N ν = e := by
    apply EReal.coe_injective
    exact hext.symm.trans he
  exact ⟨ha, hpe, by simpa only [hpe] using hb⟩

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicRieszCommon_cutoff_exponential
#print axioms DGRHS.Periodic.periodicRieszCommon_kernel_exponential
#print axioms DGRHS.Periodic.periodicRieszCommon_weight
#print axioms DGRHS.Periodic.periodicRieszCommon_particle_weight
#print axioms DGRHS.Periodic.periodicRiesz_finiteObjective_GibbsKL
#print axioms DGRHS.Periodic.periodicRieszCommon_finiteObjective_transport
