import DGPS.Structural.SmallRateCircleEquality
import DGPS.Foundations.NormalizationChecks

/-!
# STR022: eventual exact equality along bounded-amplitude circle sequences

For a sequence of direct Lipschitz circle models with uniformly bounded total oscillation `M_n`,
positive scalar rates `r_{*,n}` and `r_{*,n} → 0`, eventually `M_n > 0` (a model with `M_n = 0` is
the free model, with rate `a₀`) and `r_{ms,n} = r_{*,n}`
(`eventually_speciesRate_eq_scalarRate_of_boundedAmplitude`).

Route: the explicit STR021 threshold is bounded below by `e^{-C} min {a₀/9, 1/(4C)} > 0`; eventually
`r_{*,n}` lies below it and below `a₀`; `M_n = 0` forces `V` constant and `W = 0` (zero diagonal),
hence rate `a₀` (DEF032), a contradiction; STR021 applies to the remaining indices.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Structural

/-- If `M = 0` then `V` is constant and `W = 0` (zero diagonal). -/
theorem eq_const_of_totalOscillation_eq_zero (A : InteractionData 1)
    (hM : totalOscillation A = 0) :
    ∃ c : ℝ, A.V = (fun _ => c) ∧ A.W = (fun _ _ => 0) := by
  have h1 := potentialOscillation_nonneg A
  have h2 := interactionOscillation_nonneg A
  unfold totalOscillation at hM
  have hV0 : potentialOscillation A = 0 := by linarith
  have hW0 : interactionOscillation A = 0 := by linarith
  refine ⟨A.V 0, ?_, ?_⟩
  · funext x
    have a := def025_V_le A x
    have b := def025_le_V A x
    have a' := def025_V_le A 0
    have b' := def025_le_V A 0
    unfold potentialOscillation at hV0
    linarith
  · funext x y
    have a := def025_W_le A x y
    have b := def025_le_W A x y
    have a' := def025_W_le A x x
    have b' := def025_le_W A x x
    unfold interactionOscillation at hW0
    have := A.W_diag x
    linarith

/-- DEF032 consequence: a circle model with `M = 0` has scalar rate `a₀ = 4π²`, for every
weak-drift provider. -/
theorem scalarRate_eq_a0_of_totalOscillation_eq_zero (A : InteractionData 1)
    (hM : totalOscillation A = 0) (b : AbsoluteDrift A) :
    scalarRate A b = ENNReal.ofReal (4 * Real.pi ^ 2) := by
  obtain ⟨c, hV, hW⟩ := eq_const_of_totalOscillation_eq_zero A hM
  rw [← (circle_free_rates (AbsoluteDrift.zero 1)).1]
  -- free energy shifts by the constant `c`
  have hF : ∀ ν : ProbabilityMeasure (Torus 1), freeEnergy A ν =
      ((relativeEntropy (ν : Measure (Torus 1)) (haar 1) : ℝ≥0∞) : EReal) + (c : EReal) := by
    intro ν
    simp [freeEnergy, potentialEnergy, interactionEnergy, hV, hW]
  have hmin : freeEnergyMinimumReal A = c := by
    have h : freeEnergyMinimum A = ((c : ℝ) : EReal) := by
      refine le_antisymm ?_ ?_
      · refine (iInf_le _ (haarProbability 1)).trans ?_
        rw [hF]
        show ((relativeEntropy (haar 1) (haar 1) : ℝ≥0∞) : EReal) + _ ≤ _
        rw [relativeEntropy_self]; simp
      · refine le_iInf fun ν => ?_
        rw [hF]
        exact le_add_of_nonneg_left (EReal.coe_ennreal_nonneg _)
    rw [freeEnergyMinimumReal, h]; rfl
  have hdfe : ∀ ρ : AbsoluteDensity 1, densityFreeEnergy A ρ =
      densityFreeEnergy (InteractionData.zero 1) ρ + c := by
    intro ρ
    have h1 := coe_densityFreeEnergy A ρ
    have h2 := coe_densityFreeEnergy (InteractionData.zero 1) ρ
    rw [freeEnergy_zero_data] at h2
    rw [hF] at h1
    rw [← EReal.coe_eq_coe_iff, EReal.coe_add, h1, h2]
  have hgap : ∀ ρ : AbsoluteDensity 1, scalarGap A ρ = scalarGap (InteractionData.zero 1) ρ := by
    intro ρ
    apply NNReal.eq
    rw [coe_scalarGap, coe_scalarGap, hmin, hdfe, freeEnergyMinimumReal_zero_data]
    ring
  -- the drift vanishes a.e.
  have hpot : ∀ ρ : AbsoluteDensity 1, interactionPotential A ρ = fun _ => c := by
    intro ρ; funext x; simp [interactionPotential, hV, hW]
  have hforce : ∀ ρ : AbsoluteDensity 1, b.force ρ =ᵐ[haar 1] fun _ => 0 := by
    intro ρ
    refine b.ae_eq_of_isWeakGradient ρ (g := fun _ => 0) ?_
    rw [hpot]
    exact ⟨memLp_const c, memLp_const 0, (isWeakGradient_const (d := 1) c).ibp⟩
  have hdiss : ∀ ρ : AbsoluteDensity 1, scalarDissipation A b ρ =
      scalarDissipation (InteractionData.zero 1) (AbsoluteDrift.zero 1) ρ := by
    intro ρ
    unfold scalarDissipation
    refine lintegral_congr_ae ?_
    filter_upwards [hforce ρ] with x hx
    have hx' : b.force ρ x = 0 := hx
    simp [scalarScore, hx', AbsoluteDrift.zero]
  have hquot : ∀ ρ : AbsoluteDensity 1, scalarQuotient A b ρ =
      scalarQuotient (InteractionData.zero 1) (AbsoluteDrift.zero 1) ρ := by
    intro ρ
    unfold scalarQuotient
    rw [hdiss, hgap]
  refine le_antisymm (le_iInf fun ρ => ?_) (le_iInf fun ρ => ?_)
  · have hρ : 0 < scalarGap A ρ.1 := by rw [hgap]; exact ρ.2
    exact (scalarRate_le_quotient A b ρ.1 hρ).trans (le_of_eq (hquot ρ.1))
  · have hρ : 0 < scalarGap (InteractionData.zero 1) ρ.1 := by rw [← hgap]; exact ρ.2
    exact (scalarRate_le_quotient (InteractionData.zero 1) (AbsoluteDrift.zero 1) ρ.1 hρ).trans
      (le_of_eq (hquot ρ.1).symm)

/-- **STR022 / T07 (eventual form).** For a sequence of direct Lipschitz circle models with
`sup M_n < ∞`, `r_{*,n} > 0` and `r_{*,n} → 0`: eventually `M_n > 0` (a model with `M_n = 0` is
free, with rate `a₀`, and cannot occur eventually) and `r_{ms,n} = r_{*,n}`. -/
theorem eventually_speciesRate_eq_scalarRate_of_boundedAmplitude
    (A : ℕ → InteractionData 1) (hLip : ∀ n, LipschitzData (A n))
    (hbdd : ∃ C : ℝ, ∀ n, totalOscillation (A n) ≤ C)
    (hpos : ∀ n, 0 < scalarRate (A n) (lipschitz_absoluteDrift (A n) (hLip n)))
    (hlim : Tendsto (fun n => scalarRate (A n) (lipschitz_absoluteDrift (A n) (hLip n)))
      atTop (𝓝 0)) :
    (∀ᶠ n in atTop, 0 < totalOscillation (A n)) ∧
    ∀ᶠ n in atTop, speciesRate (A n) (lipschitz_absoluteDrift (A n) (hLip n)) =
      scalarRate (A n) (lipschitz_absoluteDrift (A n) (hLip n)) := by
  obtain ⟨C₀, hC₀⟩ := hbdd
  set C : ℝ := max C₀ 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  have hCpos : 0 < C := by linarith
  have hMC : ∀ n, totalOscillation (A n) ≤ C := fun n => (hC₀ n).trans (le_max_left _ _)
  set T : ℝ := Real.exp (-C) * min (a0 / 9) (1 / (4 * C)) with hT
  have hTpos : 0 < T := by
    have := a0_pos
    rw [hT]; positivity
  have hev : ∀ᶠ n in atTop,
      scalarRate (A n) (lipschitz_absoluteDrift (A n) (hLip n)) <
        ENNReal.ofReal (min T a0) := by
    have hm : 0 < min T a0 := lt_min hTpos a0_pos
    exact hlim.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.2 hm))
  have hmain : ∀ᶠ n in atTop, 0 < totalOscillation (A n) ∧
      speciesRate (A n) (lipschitz_absoluteDrift (A n) (hLip n)) =
        scalarRate (A n) (lipschitz_absoluteDrift (A n) (hLip n)) := by
    filter_upwards [hev] with n hn
    have hM0 : 0 ≤ totalOscillation (A n) :=
      add_nonneg (potentialOscillation_nonneg _) (interactionOscillation_nonneg _)
    rcases hM0.eq_or_lt with h0 | hMpos
    · exfalso
      rw [scalarRate_eq_a0_of_totalOscillation_eq_zero (A n) h0.symm] at hn
      exact absurd (hn.trans_le (ENNReal.ofReal_le_ofReal (min_le_right _ _)))
        (by simp [a0])
    · refine ⟨hMpos, ?_⟩
      refine speciesRate_eq_scalarRate_of_small_circle_rate (A n) (hLip n) hMpos (hpos n)
        (hn.le.trans (ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans ?_)))
      have hE : Real.exp (-C) ≤ Real.exp (-totalOscillation (A n)) :=
        Real.exp_le_exp.2 (by linarith [hMC n])
      have hinv : 1 / (4 * C) ≤ 1 / (4 * totalOscillation (A n)) :=
        one_div_le_one_div_of_le (by positivity) (by linarith [hMC n])
      have hmin : min (a0 / 9) (1 / (4 * C)) ≤
          min (a0 / 9) (1 / (4 * totalOscillation (A n))) := min_le_min le_rfl hinv
      have hm0 : 0 ≤ min (a0 / 9) (1 / (4 * C)) := le_min (by have := a0_pos; positivity)
        (by positivity)
      rw [hT]
      exact mul_le_mul hE hmin hm0 (Real.exp_pos _).le
  exact ⟨hmain.mono fun n h => h.1, hmain.mono fun n h => h.2⟩

end DGPS.Structural
