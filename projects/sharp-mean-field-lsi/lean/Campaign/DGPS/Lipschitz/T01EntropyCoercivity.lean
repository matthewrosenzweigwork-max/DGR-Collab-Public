import DGPS.Structural.MinimizerHessian

/-!
# The compactness step in direct-Lipschitz entropy coercivity

Uniqueness of the free-energy minimizer forces the continuous centered interaction
correction to be small on sufficiently low free-energy sublevels. This is the
intermediate-entropy step of the global coercivity argument. It does not assume
semiconvexity or the final entropy-coercivity estimate.
-/

open MeasureTheory Filter Topology

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- The centered interaction correction in the exact Gibbs free-energy splitting. -/
noncomputable def t01CenteredCorrection (A : InteractionData d)
    (μ ν : ProbabilityMeasure (Torus d)) : ℝ :=
  (1 / 2 : ℝ) * ∫ p, centeredKernel A (μ : Measure (Torus d)) p.1 p.2
    ∂((ν : Measure (Torus d)).prod (ν : Measure (Torus d)))

theorem t01_continuous_centeredCorrection (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) : Continuous (t01CenteredCorrection A μ) := by
  have hK := centeredKernel_continuous A (μ : Measure (Torus d))
  have h := (continuous_const : Continuous (fun _ : ProbabilityMeasure (Torus d) =>
    (1 / 2 : ℝ))).mul (SharpLSI.continuous_interAux
      (W := centeredKernel A (μ : Measure (Torus d))) hK)
  convert h using 1
  funext ν
  unfold t01CenteredCorrection
  rw [integral_prod_symm _ (hK.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))]
  rfl

theorem t01CenteredCorrection_self (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) : t01CenteredCorrection A μ μ = 0 := by
  unfold t01CenteredCorrection
  rw [integral_centeredKernel A (μ : Measure (Torus d)) (μ : Measure (Torus d))]
  ring

theorem t01CenteredCorrection_bounded (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ν, |t01CenteredCorrection A μ ν| ≤ B := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (t01_continuous_centeredCorrection A μ).continuousOn
  exact ⟨|C|, abs_nonneg _, fun ν => by
    simpa [Real.norm_eq_abs] using (hC ν (Set.mem_univ ν)).trans (le_abs_self C)⟩

/-- A quantitative low-sublevel neighborhood of the unique minimizer. The threshold is
uniform over all Borel probabilities, including singular ones. -/
theorem t01_small_gap_forces_small_centeredCorrection (A : InteractionData d)
    {μ : ProbabilityMeasure (Torus d)}
    (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (huniq : ∀ ν, freeEnergy A ν = freeEnergyMinimum A → ν = μ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, ∀ ν : ProbabilityMeasure (Torus d),
      freeEnergy A ν ≤ ((freeEnergyMinimumReal A + 1 / ((n : ℝ) + 1) : ℝ) : EReal) →
        |t01CenteredCorrection A μ ν| < δ / 2 := by
  by_contra hcon
  push_neg at hcon
  let C : ℕ → Set (ProbabilityMeasure (Torus d)) := fun n =>
    {ν | freeEnergy A ν ≤
      ((freeEnergyMinimumReal A + 1 / ((n : ℝ) + 1) : ℝ) : EReal) ∧
      δ / 2 ≤ |t01CenteredCorrection A μ ν|}
  have hcl : ∀ n, IsClosed (C n) := fun n =>
    ((lowerSemicontinuous_freeEnergy A).isClosed_preimage _).inter
      (isClosed_le continuous_const (t01_continuous_centeredCorrection A μ).abs)
  have hsub : ∀ n, C (n + 1) ⊆ C n := by
    intro n ν hν
    refine ⟨hν.1.trans (EReal.coe_le_coe_iff.mpr ?_), hν.2⟩
    have : 1 / (((n + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)
    linarith
  have hne : ∀ n, (C n).Nonempty := hcon
  obtain ⟨ν, hν⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
    hsub hne (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hν
  have hFν : freeEnergy A ν ≤ (freeEnergyMinimumReal A : EReal) := by
    have htop : freeEnergy A ν ≠ ⊤ :=
      ne_top_of_le_ne_top (EReal.coe_ne_top _) (hν 0).1
    rw [← EReal.coe_toReal htop (freeEnergy_ne_bot A ν), EReal.coe_le_coe_iff]
    refine le_of_forall_pos_lt_add fun t ht => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht
    have h := (hν n).1
    rw [← EReal.coe_toReal htop (freeEnergy_ne_bot A ν), EReal.coe_le_coe_iff] at h
    linarith
  have hmin : freeEnergy A ν = freeEnergyMinimum A := by
    rw [coe_freeEnergyMinimumReal] at hFν
    exact le_antisymm hFν (iInf_le _ ν)
  have hJ := (hν 0).2
  rw [huniq ν hmin, t01CenteredCorrection_self, abs_zero] at hJ
  linarith

end DGPS.Lipschitz
