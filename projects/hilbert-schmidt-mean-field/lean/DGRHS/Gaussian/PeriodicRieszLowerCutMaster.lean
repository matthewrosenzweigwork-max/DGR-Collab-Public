import DGRHS.Gaussian.PeriodicRieszLowerCutComparison

/-!
Packet P9f, unit 2 (part 2): master layer-cake data and the uniform exponential moment of the
lower-cut family `g_ε = periodicRieszPhysicalTail s 0 ε`, uniform in `0 < ε ≤ a` (with the small
scale `a ≤ 1` of `exists_periodicRieszMaster_scale`) and in `n ≥ 1`.

The adaptive master kernel at level `u` is the centered band between the time
`max (adaptive time) ε` and `a`: the cut-off `ε` simply raises the lower end of the band.  Caps and
`L²`/operator controls only get better, the near-field piece is the band `(ε, max(·))` whose mass is
at most `F δ(u)^h / h` in both cases, and the upper tail is the same as for the exact kernel.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Adaptive comparison for the lower cut: on the event that the lower-cut statistic reaches `u`, the
adaptive band statistic (lower end `max (adaptive time) ε`) reaches `u`. -/
lemma ae_periodicRieszLC_adaptive_comparison (s ε a β A u₀ u : ℝ) (hs : 0 < s)
    (hsd : s < (Fintype.card ι : ℝ)) (hε : 0 < ε) (hεa : ε ≤ a) (ha : 0 < a) (ha1 : a ≤ 1)
    (hβ : 0 ≤ β) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (n : ℕ) (hn : 1 ≤ n) (hA : 0 < A)
    (hAcontrol : 4 * β * (M * (periodicRieszMellinFactor ι s /
      (((Fintype.card ι : ℝ) - s) / 2))) ≤ A)
    (hu₀ : 1 ≤ u₀)
    (hlow : 4 * (β * (2 * periodicRieszMellinFactor ι s * periodicHeatDiagonalGlobalConstant ι *
      (a ^ (-s / 2) / (s / 2)))) ≤ u₀)
    (hu : u₀ ≤ u) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ),
      u ≤ β * iidNegativeStatistic n (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPhysicalTail s 0 ε (q.1 - q.2))) ω →
      u ≤ iidNegativeStatistic n (periodicRieszMasterBand s 0
        (max (periodicRieszAdaptiveTime s a A n u ι) ε) a (2 * β) ρ) ω := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hn)
  have hu0 : 0 < u := by linarith
  have hT := periodicRieszAdaptiveTime_pos_le (ι := ι) s a A u n ha hA hn hu0
  have hl := gaussianRieszAdaptiveScale_pos_le (Real.sqrt a) A (n : ℝ) u (Fintype.card ι : ℝ) s
    (Real.sqrt_pos.mpr ha) hA hn' hu0
  have hdim : 0 < (Fintype.card ι : ℝ) - s := by linarith
  have hp := gaussianRieszAdaptiveScale_power_le (Real.sqrt a) A (n : ℝ) u (Fintype.card ι : ℝ) s
    (Real.sqrt_pos.mpr ha) hA hn' hu0 hdim
  have hp' : (gaussianRieszAdaptiveScale (Real.sqrt a) A (n : ℝ) u (Fintype.card ι : ℝ) s) ^
      ((Fintype.card ι : ℝ) - s) * (A * (n : ℝ)) ≤ u := (le_div_iff₀ (mul_pos hA hn')).1 hp
  have hF := (periodicRieszMellinFactor_pos (ι := ι) s hs).le
  have hh : 0 < ((Fintype.card ι : ℝ) - s) / 2 := by linarith
  have hnearpow : (periodicRieszAdaptiveTime s a A n u ι) ^ (((Fintype.card ι : ℝ) - s) / 2) =
      (gaussianRieszAdaptiveScale (Real.sqrt a) A (n : ℝ) u (Fintype.card ι : ℝ) s) ^
        ((Fintype.card ι : ℝ) - s) := by
    unfold periodicRieszAdaptiveTime
    exact sq_rpow_half_sub _ _ _ hl.1
  have hlp : 0 ≤ (gaussianRieszAdaptiveScale (Real.sqrt a) A (n : ℝ) u (Fintype.card ι : ℝ) s) ^
      ((Fintype.card ι : ℝ) - s) := Real.rpow_nonneg hl.1.le _
  set P := (gaussianRieszAdaptiveScale (Real.sqrt a) A (n : ℝ) u (Fintype.card ι : ℝ) s) ^
      ((Fintype.card ι : ℝ) - s) with hP
  set Cn := M * (periodicRieszMellinFactor ι s / (((Fintype.card ι : ℝ) - s) / 2)) with hCn
  have hCn0 : 0 ≤ Cn := by positivity
  have hnear : β * (n : ℝ) * (M * (periodicRieszMellinFactor ι s *
      ((periodicRieszAdaptiveTime s a A n u ι) ^ (((Fintype.card ι : ℝ) - s) / 2) /
        (((Fintype.card ι : ℝ) - s) / 2)))) ≤ u / 4 := by
    rw [hnearpow]
    have e : β * (n : ℝ) * (M * (periodicRieszMellinFactor ι s *
        (P / (((Fintype.card ι : ℝ) - s) / 2)))) = (β * Cn) * ((n : ℝ) * P) := by
      rw [hCn]; ring
    rw [e]
    have h1 : 4 * β * Cn * ((n : ℝ) * P) ≤ A * ((n : ℝ) * P) :=
      mul_le_mul_of_nonneg_right hAcontrol (by positivity)
    nlinarith only [h1, hp']
  have htail : β * (2 * periodicRieszMellinFactor ι s * periodicHeatDiagonalGlobalConstant ι *
      (a ^ (-s / 2) / (s / 2))) ≤ u / 4 := by linarith
  set δ := periodicRieszAdaptiveTime s a A n u ι with hδdef
  have hδ'a : max δ ε ≤ a := max_le hT.2 hεa
  have hεδ' : ε ≤ max δ ε := le_max_right _ _
  have hnear' : β * (n : ℝ) * (M * (periodicRieszMellinFactor ι s *
      ((max δ ε) ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2)) -
      periodicRieszMellinFactor ι s *
      (ε ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2)))) ≤ u / 4 := by
    rcases le_total ε δ with h | h
    · rw [max_eq_left h]
      have hε0 : 0 ≤ periodicRieszMellinFactor ι s *
          (ε ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2)) := by
        have : 0 ≤ ε ^ (((Fintype.card ι : ℝ) - s) / 2) := Real.rpow_nonneg hε.le _
        positivity
      have hm : M * (periodicRieszMellinFactor ι s *
          (δ ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2)) -
          periodicRieszMellinFactor ι s *
          (ε ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2))) ≤
          M * (periodicRieszMellinFactor ι s *
          (δ ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2))) :=
        mul_le_mul_of_nonneg_left (by linarith) hM
      exact (mul_le_mul_of_nonneg_left hm (by positivity)).trans hnear
    · rw [max_eq_right h, sub_self, mul_zero, mul_zero]
      linarith
  filter_upwards [periodicRieszPhysicalTail_particle_comparison s ε (max δ ε) a β hs hsd hε hεδ' hδ'a
    ha1 hβ ρ M hM hρ n hn] with ω hω
  intro hx
  unfold periodicRieszMasterBand
  rw [physical_iidNegativeStatistic_const_smul]
  nlinarith only [hω, hx, hnear', htail]

lemma periodicRieszLCBand_cap_ess_bounds (s ε a β A : ℝ) (hs : 0 < s)
    (hsd : 2 * s < (Fintype.card ι : ℝ)) (hε : 0 < ε) (hεa : ε ≤ a) (ha : 0 < a) (ha1 : a ≤ 1)
    (hβ : 0 ≤ β) (hA : 0 < A) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (n : ℕ) (hn : 1 ≤ n) (u : ℝ)
    (hu : 1 ≤ u) :
    0 ≤ periodicRieszAdaptiveC0 s a β ι ∧ 0 ≤ periodicRieszAdaptiveC1 s β A ι ∧
      0 < periodicRieszAdaptiveCap s a β A n u ι ∧
      periodicRieszAdaptiveCap s a β A n u ι ≤
        periodicRieszAdaptiveC0 s a β ι + periodicRieszAdaptiveC1 s β A ι *
          ((n : ℝ) / u) ^ (s / ((Fintype.card ι : ℝ) - s)) ∧
      (eLpNormEssSup (periodicRieszMasterBand s 0
          (max (periodicRieszAdaptiveTime s a A n u ι) ε) a (2 * β) ρ)
        ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ))).toReal ≤
        periodicRieszAdaptiveC0 s a β ι + periodicRieszAdaptiveC1 s β A ι *
          ((n : ℝ) / u) ^ (s / ((Fintype.card ι : ℝ) - s)) := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have hsd' : s < (Fintype.card ι : ℝ) := by linarith
  have hu0 : 0 < u := by linarith
  have hE := periodicRieszMasterEnvelope_nonneg (ι := ι) s hs
  have hT := periodicRieszAdaptiveTime_pos_le (ι := ι) s a A u n ha hA hn hu0
  have hR := periodicRieszAdaptiveTime_rpow_neg_le (ι := ι) s a A u n ha hA hn hu0 hs hsd'
  have hpos : 0 ≤ (periodicRieszAdaptiveTime s a A n u ι) ^ (-s / 2) :=
    Real.rpow_nonneg hT.1.le _
  have hb : 8 * β * periodicRieszMasterEnvelope s ι * (periodicRieszAdaptiveTime s a A n u ι) ^ (-s / 2) ≤
      periodicRieszAdaptiveC0 s a β ι - 1 + periodicRieszAdaptiveC1 s β A ι *
        ((n : ℝ) / u) ^ (s / ((Fintype.card ι : ℝ) - s)) := by
    unfold periodicRieszAdaptiveC0 periodicRieszAdaptiveC1
    have hc : 0 ≤ 8 * β * periodicRieszMasterEnvelope s ι := by positivity
    have := mul_le_mul_of_nonneg_left hR hc
    nlinarith only [this]
  have hδ' : 0 < max (periodicRieszAdaptiveTime s a A n u ι) ε := lt_max_of_lt_right hε
  have hmono : (max (periodicRieszAdaptiveTime s a A n u ι) ε) ^ (-s / 2) ≤
      (periodicRieszAdaptiveTime s a A n u ι) ^ (-s / 2) :=
    Real.rpow_le_rpow_of_nonpos hT.1 (le_max_left _ _) (by linarith)
  have he := essential_periodicRieszMasterBand_le s 0 (max (periodicRieszAdaptiveTime s a A n u ι) ε) a
    (2 * β) hs le_rfl hδ' ha1 ρ
  rw [abs_of_nonneg (by linarith : 0 ≤ 2 * β)] at he
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold periodicRieszAdaptiveC0
    have : 0 ≤ (Real.sqrt a) ^ (-s) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    positivity
  · unfold periodicRieszAdaptiveC1
    positivity
  · unfold periodicRieszAdaptiveCap
    positivity
  · unfold periodicRieszAdaptiveCap
    nlinarith [mul_nonneg hβ (mul_nonneg hE hpos)]
  · have h1 : 4 * (2 * β) * (periodicRieszMasterEnvelope s ι *
        (max (periodicRieszAdaptiveTime s a A n u ι) ε) ^ (-s / 2)) ≤
        4 * (2 * β) * (periodicRieszMasterEnvelope s ι *
        (periodicRieszAdaptiveTime s a A n u ι) ^ (-s / 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono hE) (by positivity)
    nlinarith only [he, hb, h1]

/-- Master layer-cake data for the lower-cut family (analogue of `periodicRieszMasterCutoffData`). -/
noncomputable def periodicRieszLCMasterCutoffData (s ε a β A u₀ : ℝ) (hs : 0 < s)
    (hsd : 2 * s < (Fintype.card ι : ℝ)) (hε : 0 < ε) (hεa : ε ≤ a) (ha : 0 < a) (ha1 : a ≤ 1)
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
        (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPhysicalTail s 0 ε (q.1 - q.2))) ω)
      u₀ := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have hsd' : s < (Fintype.card ι : ℝ) := by linarith
  have hT (u : ℝ) (hu : u₀ ≤ u) :=
    periodicRieszAdaptiveTime_pos_le (ι := ι) s a A u n ha hA hn (by linarith)
  have hδ' (u : ℝ) (hu : u₀ ≤ u) :
      0 < max (periodicRieszAdaptiveTime s a A n u ι) ε := lt_max_of_lt_right hε
  have hb (u : ℝ) (hu : u₀ ≤ u) :=
    periodicRieszLCBand_cap_ess_bounds s ε a β A hs hsd hε hεa ha ha1 hβ hA ρ n hn u (hu₀.trans hu)
  have hex := gaussianRieszAdaptive_exponents (Fintype.card ι : ℝ) s hs (by linarith)
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hsize := masterCutoffSize_le_adaptive_power (periodicCappedDensityMeasure ρ)
    (fun u => periodicRieszMasterBand s 0 (max (periodicRieszAdaptiveTime s a A n u ι) ε) a (2 * β) ρ)
    (fun u => periodicRieszAdaptiveCap s a β A n u ι) (n : ℝ) u₀
    (s / ((Fintype.card ι : ℝ) - s)) (periodicRieszAdaptiveC0 s a β ι)
    (periodicRieszAdaptiveC1 s β A ι)
    hn' hu₀ hex.1 hex.2.1 (hb u₀ le_rfl).1 (hb u₀ le_rfl).2.1
    (fun u hu => (hb u hu).2.2.2.1) (fun u hu => (hb u hu).2.2.2.2)
  refine { kernel := fun u => periodicRieszMasterBand s 0
             (max (periodicRieszAdaptiveTime s a A n u ι) ε) a (2 * β) ρ
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
    exact measurable_periodicRieszMasterBand s 0 _ a (2 * β) ρ
  · intro u hu
    exact memLp_infty_periodicRieszMasterBand s 0 _ a (2 * β) hs le_rfl (hδ' u hu) ha1 ρ
  · intro u hu x y
    exact periodicRieszMasterBand_symmetric s 0 _ a (2 * β) le_rfl (hδ' u hu).le ρ x y
  · intro u hu
    exact periodicRieszMasterBand_canonical s 0 _ a (2 * β) hs le_rfl (hδ' u hu) ha1 ρ
  · intro u hu
    exact ae_periodicRieszLC_adaptive_comparison s ε a β A u₀ u hs hsd' hε hεa ha ha1 hβ ρ M hM
      hρ n hn hA hAcontrol hu₀ hlow hu
  · intro u hu
    apply Filter.Eventually.of_forall
    intro ω
    have hc := periodicRieszMasterBand_particle_cap s 0 _ a (2 * β) hs le_rfl (hδ' u hu) ha1
      (by linarith : 0 ≤ 2 * β) ρ n hn ω
    have hmono : (max (periodicRieszAdaptiveTime s a A n u ι) ε) ^ (-s / 2) ≤
        (periodicRieszAdaptiveTime s a A n u ι) ^ (-s / 2) :=
      Real.rpow_le_rpow_of_nonpos (hT u hu).1 (le_max_left _ _) (by linarith)
    have hE := periodicRieszMasterEnvelope_nonneg (ι := ι) s hs
    have h1 : 2 * (2 * β) * (periodicRieszMasterEnvelope s ι *
        (max (periodicRieszAdaptiveTime s a A n u ι) ε) ^ (-s / 2)) ≤
        2 * (2 * β) * (periodicRieszMasterEnvelope s ι *
        (periodicRieszAdaptiveTime s a A n u ι) ^ (-s / 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono hE) (by positivity)
    change iidNegativeStatistic n (periodicRieszMasterBand s 0 _ a (2 * β) ρ) ω ≤
      1 + 4 * β * (periodicRieszMasterEnvelope s ι *
        (periodicRieszAdaptiveTime s a A n u ι) ^ (-s / 2))
    nlinarith only [hc, h1]
  · intro u hu
    exact (periodicRieszMasterBand_norm_fields s 0 _ a β hs hsd le_rfl (hδ' u hu) ha ha1 ρ M hM hρ
      hrow hop).1
  · intro u hu
    exact (periodicRieszMasterBand_norm_fields s 0 _ a β hs hsd le_rfl (hδ' u hu) ha ha1 ρ M hM hρ
      hrow hop).2.1
  · intro u hu
    exact (periodicRieszMasterBand_norm_fields s 0 _ a β hs hsd le_rfl (hδ' u hu) ha ha1 ρ M hM hρ
      hrow hop).2.2

lemma measurable_periodicRieszLCCutoff_exponent (s ε β : ℝ)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] (n : ℕ) :
    Measurable (fun ω => β * iidNegativeStatistic n (hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPhysicalTail s 0 ε (q.1 - q.2))) ω) :=
  (measurable_physical_iidNegativeStatistic n _
    (stronglyMeasurable_hoeffdingCentered μ _
      ((periodicRieszPhysicalTail_measurable (ι := ι) s 0 ε).stronglyMeasurable.comp_measurable
        (measurable_fst.sub measurable_snd))).measurable).const_mul β

/-- Uniform exponential moment of the lower-cut family, uniform in the cut `0 < ε ≤ a` (some
`a ∈ (0,1]`) and in `n ≥ 1`. -/
theorem periodicRieszLowerCut_uniform_exponential (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hsd : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ∃ (C a : ℝ), 0 < a ∧ a ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ a → ∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω => Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPhysicalTail s 0 ε (q.1 - q.2))) ω))
        (Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPhysicalTail s 0 ε (q.1 - q.2))) ω)
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
  let I := {ε : ℝ // 0 < ε ∧ ε ≤ a}
  let X := fun (θ : I) (n : ℕ) (ω : Fin n → PeriodicTorus ι) =>
    β * iidNegativeStatistic n (hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPhysicalTail s 0 θ.val (q.1 - q.2))) ω
  have hX (θ : I) (n : ℕ) (hn : 1 ≤ n) :
      AEMeasurable (X θ n) (Measure.pi (fun _ : Fin n => μ)) :=
    (measurable_periodicRieszLCCutoff_exponent s θ.val β μ n).aemeasurable
  let data := fun (θ : I) (n : ℕ) (hn : 1 ≤ n) => periodicRieszLCMasterCutoffData s θ.val a β A u₀
    hs hsd θ.property.1 θ.property.2 ha ha1.le hβ ρ M hM hρ n hn hA hAcontrol hu₀ hlow hrow.le hop.le
  let K := (1 + periodicRieszAdaptiveC0 s a β ι + periodicRieszAdaptiveC1 s β A ι) ^ 2
  have hp : 2 * s / (Fintype.card ι : ℝ) < 1 := riesz_master_power_lt_one _ _ hd (by linarith)
  have hsize (θ : I) (n : ℕ) (hn : 1 ≤ n) :
      masterCutoffSize μ (data θ n hn).kernel (data θ n hn).cap u₀ ≤
        0 + K * (n : ℝ) ^ (2 * s / (Fintype.card ι : ℝ)) := by
    have hb (u : ℝ) (hu : u₀ ≤ u) :=
      periodicRieszLCBand_cap_ess_bounds s θ.val a β A hs hsd θ.property.1 θ.property.2 ha ha1.le hβ hA
        ρ n hn u (hu₀.trans hu)
    have hex := gaussianRieszAdaptive_exponents (Fintype.card ι : ℝ) s hs (by linarith)
    have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hz := (masterCutoffSize_le_adaptive_power μ
      (fun u => periodicRieszMasterBand s 0
        (max (periodicRieszAdaptiveTime s a A n u ι) θ.val) a (2 * β) ρ)
      (fun u => periodicRieszAdaptiveCap s a β A n u ι) (n : ℝ) u₀
      (s / ((Fintype.card ι : ℝ) - s)) (periodicRieszAdaptiveC0 s a β ι)
      (periodicRieszAdaptiveC1 s β A ι)
      hn' hu₀ hex.1 hex.2.1 (hb u₀ le_rfl).1 (hb u₀ le_rfl).2.1
      (fun u hu => (hb u hu).2.2.2.1) (fun u hu => (hb u hu).2.2.2.2)).2
    rw [hex.2.2] at hz
    simpa only [data, periodicRieszLCMasterCutoffData, K, zero_add] using hz
  obtain ⟨C, hC⟩ := master_uniform_sublinear_exponential_envelope μ X hX u₀ hu₀ data 0 K
    (2 * s / (Fintype.card ι : ℝ)) hp hsize
  exact ⟨C, a, ha, ha1.le, fun ε hε hεa n hn => hC ⟨ε, hε, hεa⟩ n hn⟩

end DGRHS.Periodic
