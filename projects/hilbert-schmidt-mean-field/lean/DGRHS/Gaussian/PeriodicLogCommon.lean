import DGRHS.Gaussian.PeriodicLogEntropicCommutator

/-!
Packet P11a, unit 3 (LOG, part 1): torus LOG partition bounds with constants chosen BEFORE the
density (the "common" or family form needed for the measurable time coefficients of Theorem 2.9).

Same rearrangement as `PeriodicRieszCommon`: the existing `periodicLogMellinCutoff_uniform_exponential`,
`periodicLogKernel_uniform_exponential`, `periodicLogPartition_uniform` and
`periodicLogParticleWeight_uniform` state `∃ C` after `ρ`, but the master layer-cake data depend on
`(b, M, d)` alone and the constant is the explicit `masterEnvelopeConstant`.  The interaction energy
enters the weight bound only through `exp(-β I_μ)`, `I_μ ≥ -J₀` with the universal torus constant
`J₀ = periodicLogPairLower / 2` (`periodicLogInteraction_lower`), so no extra control is needed.
-/

noncomputable section
open MeasureTheory InformationTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration DGRHS.Entropy
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The uniform exponential moment of the torus LOG cutoff family at Mellin level, constant before the
density. -/
theorem periodicLogMellinCutoff_common_exponential (b : ℝ) (hb : 0 ≤ b) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      ∀ τ : ℝ, 0 ≤ τ → ∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω => Real.exp (b * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι =>
            periodicUnshiftedMellinHeatGreen (periodicLogMellinExponent ι) τ (q.1 - q.2))) ω))
        (Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (b * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι =>
            periodicUnshiftedMellinHeatGreen (periodicLogMellinExponent ι) τ (q.1 - q.2))) ω)
        ∂Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ≤ C := by
  have hL := glzUniversalTailConstant_pos
  obtain ⟨a, ha, ha1, hrow, hop⟩ := exists_periodicLogBand_small_scale (ι := ι) (2 * b) M
    (1 / glzUniversalTailConstant) (by positivity)
  have hTc := periodicLogTailConst_nonneg (ι := ι) a ha.le
  let A := 1 + 8 * periodicLogNearConst M ι
  let u₀ := 1 + 4 * (b * (2 * periodicLogTailConst ι a))
  have hAn := periodicLogNearConst_nonneg (ι := ι) M hM
  have hA : 0 < A := by dsimp [A]; linarith
  have hAC : 8 * periodicLogNearConst M ι ≤ A := by dsimp [A]; linarith
  have hT0 : 0 ≤ b * (2 * periodicLogTailConst ι a) := by positivity
  have hu₀ : 1 ≤ u₀ := by dsimp [u₀]; linarith
  have hlow : 4 * (b * (2 * periodicLogTailConst ι a)) ≤ u₀ := by dsimp [u₀]; linarith
  let K := (2 + periodicLogAdaptiveC1 A b ι) ^ 2
  obtain ⟨N₀, hN₀⟩ := sublinear_power_envelope_growth (2 * glzUniversalTailConstant ^ 2) 0 K
    (2 / 3 : ℝ) (by norm_num)
  refine ⟨masterEnvelopeConstant u₀ N₀ (fun n => 0 + K * (n : ℝ) ^ (2 / 3 : ℝ)), ?_⟩
  intro ρ hprob hρ τ hτ n hn
  let μ := periodicCappedDensityMeasure ρ
  let I := {τ : ℝ // 0 ≤ τ}
  let X := fun (θ : I) (n : ℕ) (ω : Fin n → PeriodicTorus ι) =>
    b * iidNegativeStatistic n (hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι =>
        periodicUnshiftedMellinHeatGreen (periodicLogMellinExponent ι) θ.val (q.1 - q.2))) ω
  have hX (θ : I) (n : ℕ) (hn : 1 ≤ n) :
      AEMeasurable (X θ n) (Measure.pi (fun _ : Fin n => μ)) :=
    (measurable_periodicLogCutoff_exponent θ.val b μ n).aemeasurable
  let data := fun (θ : I) (n : ℕ) (hn : 1 ≤ n) => periodicLogMasterCutoffData θ.val a b A u₀
    θ.property ha ha1.le hb hA ρ M hM hρ n hn hAC hu₀ hlow hrow.le hop.le
  have hsize (θ : I) (n : ℕ) (hn : 1 ≤ n) :
      masterCutoffSize μ (data θ n hn).kernel (data θ n hn).cap u₀ ≤
        0 + K * (n : ℝ) ^ (2 / 3 : ℝ) := by
    have hz := (periodicLogAdaptive_size_bound θ.val a b A u₀ θ.property ha ha1.le hA hb hu₀ ρ n
      hn).2
    simpa only [data, periodicLogMasterCutoffData, K, zero_add] using hz
  exact master_uniform_exponential_envelope μ X hX u₀ hu₀ N₀ data
    (fun n => 0 + K * (n : ℝ) ^ (2 / 3 : ℝ)) hsize hN₀ ⟨τ, hτ⟩ n hn

/-- Normalized heat-time LOG kernel, constant before the density. -/
theorem periodicLogMellinGreen_common_exponential (β : ℝ) (hβ : 0 ≤ β) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      ∀ τ : ℝ, 0 ≤ τ → ∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω => Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogMellinGreen τ (q.1 - q.2))) ω))
        (Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogMellinGreen τ (q.1 - q.2))) ω)
        ∂Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ≤ C := by
  have hc := (periodicLogMellinFactor_pos (ι := ι)).le
  obtain ⟨C, hC⟩ := periodicLogMellinCutoff_common_exponential (ι := ι)
    (β * periodicLogMellinFactor ι) (mul_nonneg hβ hc) M hM
  refine ⟨C, fun ρ hprob hρ τ hτ n hn => ?_⟩
  simp only [periodicLogMellinGreen_stat_eq]
  exact hC ρ hρ τ hτ n hn

/-- The exact torus LOG kernel, constant before the density. -/
theorem periodicLogCommon_kernel_exponential (β : ℝ) (hβ : 0 ≤ β) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) → ∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω => Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))) ω))
        (Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))) ω)
        ∂Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ≤ C := by
  obtain ⟨C, hC⟩ := periodicLogMellinGreen_common_exponential (ι := ι) β hβ M hM
  refine ⟨C, fun ρ hprob hρ n hn => ?_⟩
  obtain ⟨hi, hb⟩ := hC ρ hρ 0 le_rfl n hn
  have hpair : (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogMellinGreen 0 (q.1 - q.2))
      =ᵐ[(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)]
      (fun q => periodicLogKernel (q.1 - q.2)) :=
    periodicDensity_pair_ae_of_haar ρ _ periodicLogMellinGreen_ae_kernel
  have hstat := ae_physical_iidNegativeStatistic_congr (periodicCappedDensityMeasure ρ) n _ _
    (ae_hoeffdingCentered_congr (periodicCappedDensityMeasure ρ) _ _ hpair)
  have hexp : (fun ω => Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogMellinGreen 0 (q.1 - q.2))) ω))
      =ᵐ[Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)]
      (fun ω => Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))) ω)) := by
    filter_upwards [hstat] with ω hω
    rw [hω]
  exact ⟨hi.congr hexp, by rw [← integral_congr_ae hexp]; exact hb⟩

/-- The modulated partition integrand of the spectral LOG kernel with a common bound. -/
theorem periodicLogCommon_partition (β : ℝ) (hβ : 0 ≤ β) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      let μ := periodicCappedDensityMeasure ρ
      let W := fun (x y : PeriodicTorus ι) => periodicLogKernel (x - y)
      let h := hoeffdingCentered μ
        (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))
      let F := DGRHS.potential μ W
      let I := DGRHS.interactionEnergy μ W
      ∀ N, 1 ≤ N →
      Integrable (fun x : Fin N → PeriodicTorus ι =>
        Real.exp (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → PeriodicTorus ι,
        Real.exp (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x)
          ∂Measure.pi (fun _ : Fin N => μ)) ≤ C := by
  obtain ⟨C0, hC0⟩ := periodicLogCommon_kernel_exponential (ι := ι) β hβ M hM
  set pk := M * ∫ z, |periodicLogKernel (ι := ι) z| ∂periodicHaar ι with hpk
  set J0 := periodicLogPairLower ι / 2 with hJ0
  have hJ0n : 0 ≤ J0 := by
    have := periodicLogPairLower_nonneg (ι := ι)
    rw [hJ0]; positivity
  refine ⟨max (Real.exp (β * (pk + J0)) * max C0 0) (Real.exp (β * J0)),
    lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _), ?_⟩
  intro ρ hprob hρ μ W h F I N hN
  have hW : Integrable (Function.uncurry W) (μ.prod μ) :=
    periodicDensityPair_integrable_of_haar ρ M hρ _ periodicLogKernel_integrable
  have hF : Integrable F μ := DGRHS.integrable_potential μ W hW
  have hK : ∀ᵐ x ∂μ, F x ≤ pk :=
    Filter.Eventually.of_forall fun x =>
      (le_abs_self _).trans (periodicLogKernel_potential_abs_le ρ M hM hρ x)
  have he (N : ℕ) : (fun x : Fin N → PeriodicTorus ι => Real.exp (β * iidNegativeStatistic N h x)) =
      (fun x => Real.exp (-β / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) := by
    funext x
    rw [DGRHS.CLT.iidCanonicalExponent_eq]
  have hProper : ∀ N, 1 ≤ N → Integrable (fun x : Fin N → PeriodicTorus ι =>
      Real.exp (-β / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x))
      (Measure.pi (fun _ : Fin N => μ)) := by
    intro N hN
    have hi := (hC0 ρ hρ N hN).1
    rw [he N] at hi
    exact hi
  have hBound : ∀ N, 1 ≤ N → (∫ x : Fin N → PeriodicTorus ι,
      Real.exp (-β / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ max C0 0 := by
    intro N hN
    have hb := (hC0 ρ hρ N hN).2
    rw [he N] at hb
    exact hb.trans (le_max_left _ _)
  have hmom := DGRHS.CLT.sourceWeight_of_canonical_moments h F hF _ hK I β hβ (max C0 0)
    hProper hBound
  have hIlow : -J0 ≤ I := by
    have h1 := periodicLogInteraction_lower ρ
    have h2 := periodicLogInteraction_eq ρ M hρ
    change -J0 ≤ DGRHS.interactionEnergy μ W
    rw [h2]
    exact h1
  simp_rw [DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent _ _ _ _ (show 0 < N by omega)]
  refine ⟨(hmom N).1, ((hmom N).2).trans (max_le_max ?_ ?_)⟩
  · have h1 : Real.exp (β * (pk - I)) ≤ Real.exp (β * (pk + J0)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact mul_le_mul_of_nonneg_right h1 (le_max_right _ _)
  · exact Real.exp_le_exp.mpr (by nlinarith)

/-- Particle weights of the torus LOG gas with a common upper constant (torus form of the Euclidean
family cap `exists_log_family_literal_cap`). -/
theorem periodicLogCommon_particle_cap (β : ℝ) (hβ : 0 ≤ β) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) → ∀ N : ℕ, 1 ≤ N →
      Integrable (fun ω => Real.exp (periodicLogParticleExponent ρ β N ω))
        (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (periodicLogParticleExponent ρ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ C := by
  obtain ⟨C, hC, hU⟩ := periodicLogCommon_partition (ι := ι) β hβ M hM
  refine ⟨C, hC, fun ρ hprob hρ N hN => ?_⟩
  have hn : 0 < N := by omega
  have hexp : (fun ω => Real.exp (periodicLogParticleExponent ρ β N ω)) =ᵐ[
      Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)]
      (fun ω => Real.exp (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2)))
        (DGRHS.potential (periodicCappedDensityMeasure ρ)
          (fun a b : PeriodicTorus ι => periodicLogKernel (a - b)))
        (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
          (fun a b : PeriodicTorus ι => periodicLogKernel (a - b))) N ω)) := by
    filter_upwards [periodicLogSourceExponent_ae β ρ M hρ N] with ω hω
    rw [periodicLogParticleExponent_eq ρ β N hn]
    refine congrArg Real.exp ?_
    exact ((DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent _ _ _ β hn ω).trans hω).symm
  have hU' := hU ρ hρ N hN
  exact ⟨hU'.1.congr hexp.symm, by rw [integral_congr_ae hexp]; exact hU'.2⟩

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLogMellinCutoff_common_exponential
#print axioms DGRHS.Periodic.periodicLogMellinGreen_common_exponential
#print axioms DGRHS.Periodic.periodicLogCommon_kernel_exponential
#print axioms DGRHS.Periodic.periodicLogCommon_partition
#print axioms DGRHS.Periodic.periodicLogCommon_particle_cap
