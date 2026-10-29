import DGRHS.Decoupling.Prop33SourceAllPatternSelectedPatternWalshJoin

/-!
Probability bridge for the dPmS upper-bound proof of Proposition 3.3.

The pointwise finite-cube small-ball estimate for the all-pattern statistic `T`
(`Prop33SourceAllPatternSelectedPatternWalshJoin`) is integrated over the
heterogeneous two-copy product law. Every fixed coordinatewise replica swap
preserves that law, and `T` is swap invariant; hence

  `P(‖T‖ ≥ s) ≤ 4 A_k · P(2^k ‖D_ℓ‖ ≥ s)`

for every fixed copy pattern `ℓ`, with `A_k = sourceMixedDegreeWeight k`.
No symmetry of the ordered-tuple kernel and no equality of the coordinate
marginals is used. The only measure-theoretic input on the target is
`MeasurableAdd₂ E` (sums of measurable maps are measurable).
-/

noncomputable section
open MeasureTheory DGRHS.Decoupling.FiniteCube

namespace DGRHS.Decoupling.Prop33.SelectorTonelliBridge

open Classical in
/-- Abstract Tonelli step: if for every point of `SA` a fraction at least `δ` of
the selector-swaps land in `SB`, and every swap preserves `ν`, then
`δ ν(SA) ≤ ν(SB)`. -/
theorem selector_avg_tail_bound {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    {m : ℕ} (sw : Cube m → Ω → Ω) (hsw : ∀ σ, MeasurePreserving (sw σ) ν ν)
    (SA SB : Set Ω) (hSA : MeasurableSet SA) (hSB : MeasurableSet SB)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ ω ∈ SA, δ ≤ cubeAvg (fun σ => if sw σ ω ∈ SB then (1 : ℝ) else 0)) :
    ENNReal.ofReal δ * ν SA ≤ ν SB := by
  classical
  set N : ℕ := Fintype.card (Cube m) with hN
  have hNpos : 0 < N := Fintype.card_pos
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hpre : ∀ σ, ν ((sw σ) ⁻¹' SB) = ν SB := fun σ =>
    (hsw σ).measure_preimage hSB.nullMeasurableSet
  have hmeas : ∀ σ, Measurable (SB.indicator (fun _ : Ω => (1 : ENNReal)) ∘ sw σ) :=
    fun σ => (measurable_const.indicator hSB).comp (hsw σ).measurable
  -- pointwise inequality in ENNReal
  have hpt : ∀ ω, SA.indicator (fun _ => ENNReal.ofReal (δ * N)) ω ≤
      ∑ σ : Cube m, (SB.indicator (fun _ : Ω => (1 : ENNReal)) ∘ sw σ) ω := by
    intro ω
    by_cases hω : ω ∈ SA
    · rw [Set.indicator_of_mem hω]
      have h1 := h ω hω
      unfold cubeAvg avgOn at h1
      have h2 : δ * N ≤ ∑ σ : Cube m, (if sw σ ω ∈ SB then (1 : ℝ) else 0) := by
        have : (N : ℝ)⁻¹ * ∑ σ : Cube m, (if sw σ ω ∈ SB then (1 : ℝ) else 0) ≥ δ := h1
        have h3 := mul_le_mul_of_nonneg_left this hNreal.le
        rw [← mul_assoc, mul_inv_cancel₀ hNreal.ne', one_mul] at h3
        linarith
      calc ENNReal.ofReal (δ * N)
          ≤ ENNReal.ofReal (∑ σ : Cube m, (if sw σ ω ∈ SB then (1 : ℝ) else 0)) :=
            ENNReal.ofReal_le_ofReal h2
        _ = ∑ σ : Cube m, ENNReal.ofReal (if sw σ ω ∈ SB then (1 : ℝ) else 0) :=
            ENNReal.ofReal_sum_of_nonneg (fun σ _ => by split_ifs <;> norm_num)
        _ = ∑ σ : Cube m, (SB.indicator (fun _ : Ω => (1 : ENNReal)) ∘ sw σ) ω := by
            apply Finset.sum_congr rfl
            intro σ _
            by_cases hm : sw σ ω ∈ SB <;> simp [hm, Set.indicator]
    · rw [Set.indicator_of_notMem hω]; exact zero_le
  have hint := lintegral_mono (μ := ν) hpt
  rw [lintegral_indicator hSA, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter] at hint
  rw [lintegral_finsetSum _ (fun σ _ => hmeas σ)] at hint
  have hterm : ∀ σ : Cube m, ∫⁻ ω, (SB.indicator (fun _ : Ω => (1 : ENNReal)) ∘ sw σ) ω ∂ν
      = ν SB := by
    intro σ
    have : (SB.indicator (fun _ : Ω => (1 : ENNReal)) ∘ sw σ) =
        ((sw σ) ⁻¹' SB).indicator (fun _ => (1 : ENNReal)) := by
      funext ω; simp [Set.indicator, Function.comp]
    rw [this, lintegral_indicator_const ((hsw σ).measurable hSB), one_mul, hpre]
  simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hint
  have hNe : (N : ENNReal) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hNt : (N : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top N
  have hofr : ENNReal.ofReal (δ * N) = ENNReal.ofReal δ * N := by
    rw [ENNReal.ofReal_mul hδ, ENNReal.ofReal_natCast]
  rw [hofr] at hint
  have key : (N : ENNReal) * (ENNReal.ofReal δ * ν SA) ≤ (N : ENNReal) * ν SB := by
    calc (N : ENNReal) * (ENNReal.ofReal δ * ν SA)
        = ENNReal.ofReal δ * N * ν SA := by ring
      _ ≤ (N : ENNReal) * ν SB := hint
  exact (ENNReal.mul_le_mul_iff_right hNe hNt).mp key



open DGRHS.Decoupling.Prop33 DGRHS.Decoupling.Heterogeneous
open DGRHS.Decoupling.Prop33.CopySwap
open DGRHS.Decoupling.Prop33.SourceAllPatternSelectedPatternWalshJoin

theorem sourceMixedDegreeWeight_pos {k : ℕ} (hk : 0 < k) :
    0 < sourceMixedDegreeWeight k := by
  unfold sourceMixedDegreeWeight
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hs : 0 < ∑ r ∈ Finset.range k, (9 : ℝ) ^ (r + 1) :=
    Finset.sum_pos (fun r _ => by positivity) ⟨0, Finset.mem_range.mpr hk⟩
  positivity

theorem cubeAvg_mono_indicator {m : ℕ} (P Q : Cube m → Prop) [DecidablePred P]
    [DecidablePred Q] (h : ∀ σ, P σ → Q σ) :
    cubeAvg (fun σ => if P σ then (1 : ℝ) else 0) ≤
      cubeAvg (fun σ => if Q σ then (1 : ℝ) else 0) := by
  unfold cubeAvg avgOn
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro σ _
  by_cases hp : P σ
  · simp [hp, h σ hp]
  · simp only [hp, ite_false]; split_ifs <;> norm_num

variable {S E : Type*} [MeasurableSpace S] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableAdd₂ E] {n k : ℕ}

lemma measurable_sourcePatternArgument (t : OrderedTuple n k) (ell : Cube k) :
    Measurable (fun z : Fin n → S × S => sourcePatternArgument z t ell) := by
  refine measurable_pi_iff.mpr ?_
  intro j
  by_cases h : ell j
  · simp only [sourcePatternArgument, h, ite_true]
    exact measurable_fst.comp (measurable_pi_apply (t.1 j))
  · simp only [sourcePatternArgument, h, ite_false, Bool.false_eq_true]
    exact measurable_snd.comp (measurable_pi_apply (t.1 j))

lemma measurable_sourceCopyPatternStatistic (f : OrderedTuple n k → (Fin k → S) → E)
    (hf : ∀ t, Measurable (f t)) (ell : Cube k) :
    Measurable (fun z : Fin n → S × S => sourceCopyPatternStatistic f z ell) := by
  unfold sourceCopyPatternStatistic
  exact Finset.measurable_sum _ (fun t _ => (hf t).comp (measurable_sourcePatternArgument t ell))

lemma measurable_sourceAllPatternStatistic (f : OrderedTuple n k → (Fin k → S) → E)
    (hf : ∀ t, Measurable (f t)) :
    Measurable (fun z : Fin n → S × S => sourceAllPatternStatistic f z) := by
  unfold sourceAllPatternStatistic
  exact Finset.measurable_sum _ (fun ell _ => measurable_sourceCopyPatternStatistic f hf ell)

/-- All-pattern small-ball tail bound on the heterogeneous two-copy law: the tail of
the swap-invariant aggregate `T = ∑_ℓ D_ℓ` is bounded by `4 A_k` times the tail of
`2^k D_ℓ` for any fixed pattern `ℓ`. -/
theorem allPattern_tail_le_copyPattern_tail (hk : 0 < k)
    (marginal : Fin n → Measure S) [∀ i, IsProbabilityMeasure (marginal i)]
    (f : OrderedTuple n k → (Fin k → S) → E) (hf : ∀ t, Measurable (f t))
    (ell : Cube k) (s : ℝ) :
    heterogeneousPairSamples marginal {z | s ≤ ‖sourceAllPatternStatistic f z‖} ≤
      ENNReal.ofReal (4 * sourceMixedDegreeWeight k) *
        heterogeneousPairSamples marginal
          {z | s ≤ ‖(2 : ℝ) ^ k • sourceCopyPatternStatistic f z ell‖} := by
  classical
  set ν := heterogeneousPairSamples marginal with hν
  set A := sourceMixedDegreeWeight k with hA
  have hApos : 0 < A := sourceMixedDegreeWeight_pos hk
  have h4A : 0 < 4 * A := by positivity
  have hSA : MeasurableSet {z : Fin n → S × S | s ≤ ‖sourceAllPatternStatistic f z‖} :=
    measurableSet_le measurable_const (measurable_sourceAllPatternStatistic f hf).norm
  have hSB : MeasurableSet
      {z : Fin n → S × S | s ≤ ‖(2 : ℝ) ^ k • sourceCopyPatternStatistic f z ell‖} :=
    measurableSet_le measurable_const (by
      have : (fun z : Fin n → S × S => ‖(2 : ℝ) ^ k • sourceCopyPatternStatistic f z ell‖) =
          fun z => ‖(2 : ℝ) ^ k‖ * ‖sourceCopyPatternStatistic f z ell‖ := by
        funext z; exact norm_smul _ _
      rw [this]
      exact (measurable_sourceCopyPatternStatistic f hf ell).norm.const_mul _)
  have key := selector_avg_tail_bound ν (fun σ z => heterogeneousSwapSelected σ z)
    (fun σ => heterogeneousSwapSelected_measurePreserving marginal σ) _ _ hSA hSB
    (1 / (4 * A)) (by positivity) (by
      intro z hz
      have hsb := source_copy_pattern_selector_smallball hk f z ell
      refine le_trans hsb ?_
      apply cubeAvg_mono_indicator
      intro σ hσ
      simp only [Set.mem_ofPred_eq] at hz ⊢
      exact le_trans hz hσ)
  have hδpos : (0 : ENNReal) < ENNReal.ofReal (1 / (4 * A)) := by
    rw [ENNReal.ofReal_pos]; positivity
  have hinv : ENNReal.ofReal (4 * A) = (ENNReal.ofReal (1 / (4 * A)))⁻¹ := by
    rw [one_div, ENNReal.ofReal_inv_of_pos h4A, inv_inv]
  rw [hinv]
  have hne0 : ENNReal.ofReal (1 / (4 * A)) ≠ 0 := hδpos.ne'
  have hnet : ENNReal.ofReal (1 / (4 * A)) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc ν {z | s ≤ ‖sourceAllPatternStatistic f z‖}
      = (ENNReal.ofReal (1 / (4 * A)))⁻¹ *
          (ENNReal.ofReal (1 / (4 * A)) * ν {z | s ≤ ‖sourceAllPatternStatistic f z‖}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hne0 hnet, one_mul]
    _ ≤ _ := by gcongr

end DGRHS.Decoupling.Prop33.SelectorTonelliBridge
