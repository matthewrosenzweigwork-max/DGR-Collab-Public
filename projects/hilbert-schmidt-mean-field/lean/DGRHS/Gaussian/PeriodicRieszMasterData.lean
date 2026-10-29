import DGRHS.Gaussian.PeriodicRieszAdaptiveComparison
import DGRHS.Gaussian.GaussianRieszCutoffMoment

/-!
Packet P9b, units 4-5: periodic analogue of `gaussianRieszMasterCutoffData` (the actual master
layer-cake data: (M1)-(M3), the cap and the size supremum) and of
`gaussianRieszCutoff_uniform_small_scale_exponential` (the uniform exponential moment, TeX 1521-1643,
`prop:masterLayerCake` instantiated), for the periodic Riesz kernel family
`periodicRieszMellinGreen s τ` (heat shift `τ ≥ 0`; `τ = 0` is the exact kernel, a.e. equal to
`periodicRieszKernel`).  No exponential moment, concentration bound or event comparison is supplied.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicRieszMellinGreen_measurable (s τ : ℝ) :
    Measurable (periodicRieszMellinGreen (ι := ι) s τ) := by
  unfold periodicRieszMellinGreen periodicUnshiftedMellinHeatGreen
  refine measurable_const.mul ?_
  have hm : Measurable (fun q : ℝ × PeriodicTorus ι => (q.1 + τ, q.2)) := by fun_prop
  have hh := (periodicGaussianHeat_joint_measurable (ι := ι)).comp hm
  have hf : Measurable (fun q : ℝ × PeriodicTorus ι =>
      q.1 ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) *
        ((periodicGaussianHeat (q.1 + τ) q.2).re - 1)) :=
    (by fun_prop : Measurable (fun q : ℝ × PeriodicTorus ι =>
      q.1 ^ (((Fintype.card ι : ℝ) - s) / 2 - 1))).mul
      ((Complex.continuous_re.measurable.comp hh).sub measurable_const)
  exact (hf.stronglyMeasurable.integral_prod_left'
    (μ := (volume : Measure ℝ).restrict (Set.Ioi 0))).measurable

noncomputable def periodicRieszMasterCutoffData (s τ a β A u₀ : ℝ) (hs : 0 < s)
    (hsd : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hβ : 0 ≤ β) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (n : ℕ) (hn : 1 ≤ n) (hA : 0 < A)
    (hAcontrol : 4 * β * (M * (periodicRieszMellinFactor ι s /
      (((Fintype.card ι : ℝ) - s) / 2))) ≤ A)
    (hu₀ : 1 ≤ u₀)
    (hlow : 4 * (β * (2 * periodicRieszMellinFactor ι s * periodicHeatDiagonalGlobalConstant ι *
      (a ^ (-s / 2) / (s / 2)))) ≤ u₀)
    (hrow : 16 * (2 * β) ^ 2 * periodicRieszBandRowControl s a M ι ≤ 1 / glzUniversalTailConstant)
    (hop : 4 * |2 * β| * Real.sqrt (periodicRieszBandRowControl s a M ι) ≤
      1 / glzUniversalTailConstant) :
    MasterCutoffData (periodicCappedDensityMeasure ρ) n
      (fun ω => β * iidNegativeStatistic n (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszMellinGreen s τ (q.1 - q.2))) ω)
      u₀ := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have hsd' : s < (Fintype.card ι : ℝ) := by linarith
  have hT (u : ℝ) (hu : u₀ ≤ u) :=
    periodicRieszAdaptiveTime_pos_le (ι := ι) s a A u n ha hA hn (by linarith)
  have hb (u : ℝ) (hu : u₀ ≤ u) :=
    periodicRieszAdaptiveBand_cap_ess_bounds s τ a β A hs hsd hτ ha ha1 hβ hA ρ n hn u (hu₀.trans hu)
  have hex := gaussianRieszAdaptive_exponents (Fintype.card ι : ℝ) s hs (by linarith)
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hsize := masterCutoffSize_le_adaptive_power (periodicCappedDensityMeasure ρ)
    (fun u => periodicRieszAdaptiveBand s τ a β A n u ρ)
    (fun u => periodicRieszAdaptiveCap s a β A n u ι) (n : ℝ) u₀
    (s / ((Fintype.card ι : ℝ) - s)) (periodicRieszAdaptiveC0 s a β ι)
    (periodicRieszAdaptiveC1 s β A ι)
    hn' hu₀ hex.1 hex.2.1 (hb u₀ le_rfl).1 (hb u₀ le_rfl).2.1
    (fun u hu => (hb u hu).2.2.2.1) (fun u hu => (hb u hu).2.2.2.2)
  refine { kernel := fun u => periodicRieszAdaptiveBand s τ a β A n u ρ
           cap := fun u => periodicRieszAdaptiveCap s a β A n u ι
           measurable := ?_
           memLp := ?_
           symmetric := ?_
           canonical := ?_
           cap_pos := fun u hu => (hb u hu).2.2.1
           compare := ?_
           capped := ?_
           row := ?_
           joint := ?_
           operator := ?_
           size_finite := hsize.1 }
  · intro u hu
    exact measurable_periodicRieszMasterBand s τ _ a (2 * β) ρ
  · intro u hu
    exact memLp_infty_periodicRieszMasterBand s τ _ a (2 * β) hs hτ (hT u hu).1 ha1 ρ
  · intro u hu x y
    exact periodicRieszMasterBand_symmetric s τ _ a (2 * β) hτ (hT u hu).1.le ρ x y
  · intro u hu
    exact periodicRieszMasterBand_canonical s τ _ a (2 * β) hs hτ (hT u hu).1 ha1 ρ
  · intro u hu
    exact ae_periodicRieszParticle_adaptive_comparison s τ a β A u₀ u hs hsd' hτ ha ha1 hβ ρ M hM
      hρ n hn hA hAcontrol hu₀ hlow hu
  · intro u hu
    apply Filter.Eventually.of_forall
    intro ω
    have hc := periodicRieszMasterBand_particle_cap s τ _ a (2 * β) hs hτ (hT u hu).1 ha1
      (by linarith : 0 ≤ 2 * β) ρ n hn ω
    change iidNegativeStatistic n (periodicRieszMasterBand s τ _ a (2 * β) ρ) ω ≤
      1 + 4 * β * (periodicRieszMasterEnvelope s ι *
        (periodicRieszAdaptiveTime s a A n u ι) ^ (-s / 2))
    nlinarith only [hc]
  · intro u hu
    exact (periodicRieszMasterBand_norm_fields s τ _ a β hs hsd hτ (hT u hu).1 ha ha1 ρ M hM hρ
      hrow hop).1
  · intro u hu
    exact (periodicRieszMasterBand_norm_fields s τ _ a β hs hsd hτ (hT u hu).1 ha ha1 ρ M hM hρ
      hrow hop).2.1
  · intro u hu
    exact (periodicRieszMasterBand_norm_fields s τ _ a β hs hsd hτ (hT u hu).1 ha ha1 ρ M hM hρ
      hrow hop).2.2

lemma measurable_periodicRieszCutoff_exponent (s τ β : ℝ)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] (n : ℕ) :
    Measurable (fun ω => β * iidNegativeStatistic n (hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszMellinGreen s τ (q.1 - q.2))) ω) :=
  (measurable_physical_iidNegativeStatistic n _
    (stronglyMeasurable_hoeffdingCentered μ _
      ((periodicRieszMellinGreen_measurable (ι := ι) s τ).stronglyMeasurable.comp_measurable
        (measurable_fst.sub measurable_snd))).measurable).const_mul β

/-- Uniform exponential moment of the periodic Riesz cutoff family, uniform in the heat shift
`τ ≥ 0` (including the exact kernel `τ = 0`) and in `n ≥ 1`. -/
theorem periodicRieszCutoff_uniform_exponential (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hsd : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ → ∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω => Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszMellinGreen s τ (q.1 - q.2))) ω))
        (Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszMellinGreen s τ (q.1 - q.2))) ω)
        ∂Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ≤ C := by
  let μ := periodicCappedDensityMeasure ρ
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
  let I := {τ : ℝ // 0 ≤ τ}
  let X := fun (θ : I) (n : ℕ) (ω : Fin n → PeriodicTorus ι) =>
    β * iidNegativeStatistic n (hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszMellinGreen s θ.val (q.1 - q.2))) ω
  have hX (θ : I) (n : ℕ) (hn : 1 ≤ n) :
      AEMeasurable (X θ n) (Measure.pi (fun _ : Fin n => μ)) :=
    (measurable_periodicRieszCutoff_exponent s θ.val β μ n).aemeasurable
  let data := fun (θ : I) (n : ℕ) (hn : 1 ≤ n) => periodicRieszMasterCutoffData s θ.val a β A u₀
    hs hsd θ.property ha ha1.le hβ ρ M hM hρ n hn hA hAcontrol hu₀ hlow hrow.le hop.le
  let K := (1 + periodicRieszAdaptiveC0 s a β ι + periodicRieszAdaptiveC1 s β A ι) ^ 2
  have hp : 2 * s / (Fintype.card ι : ℝ) < 1 := riesz_master_power_lt_one _ _ hd (by linarith)
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
  obtain ⟨C, hC⟩ := master_uniform_sublinear_exponential_envelope μ X hX u₀ hu₀ data 0 K
    (2 * s / (Fintype.card ι : ℝ)) hp hsize
  exact ⟨C, fun τ hτ n hn => hC ⟨τ, hτ⟩ n hn⟩

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicRieszMellinGreen_measurable
#print axioms DGRHS.Periodic.periodicRieszMasterCutoffData
#print axioms DGRHS.Periodic.measurable_periodicRieszCutoff_exponent
#print axioms DGRHS.Periodic.periodicRieszCutoff_uniform_exponential
