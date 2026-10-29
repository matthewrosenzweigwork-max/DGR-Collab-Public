import SharpSymmetricLSI.Infra.ChainRule

/-!
# Lipschitz chain rule, part 1: two approximation lemmas

* `exists_smooth_lipschitz_approx`: an `L`-Lipschitz `χ : ℝ → ℝ` is the uniform limit of smooth
  `χ_j` with `|χ_j'| ≤ L` (normed bump convolutions, `|χ_j - χ| ≤ L/(j+1)`);
* `exists_tendsto_convexHull`: a bounded sequence in a Hilbert space has convex combinations of its
  tails converging strongly (minimal-norm points of the closed convex hulls of the tails form a
  Cauchy sequence by the parallelogram law). This replaces weak compactness and Mazur's lemma.
-/

open MeasureTheory Filter Topology Set Metric
open scoped Convolution NNReal ENNReal

namespace SharpLSI

/-! ### Smoothing a Lipschitz function on `ℝ` -/

theorem exists_smooth_lipschitz_approx {χ : ℝ → ℝ} {L : ℝ≥0} (hχ : LipschitzWith L χ) :
    ∃ χs : ℕ → ℝ → ℝ, (∀ j, ContDiff ℝ 1 (χs j)) ∧ (∀ j t, |deriv (χs j) t| ≤ L) ∧
      ∀ j t, |χs j t - χ t| ≤ L / ((j : ℝ) + 1) := by
  have hr : ∀ j : ℕ, (0 : ℝ) < 1 / (2 * ((j : ℝ) + 1)) := fun j => by positivity
  let φ : ℕ → ContDiffBump (0 : ℝ) := fun j =>
    ⟨1 / (2 * ((j : ℝ) + 1)), 1 / ((j : ℝ) + 1), hr j, by
      rw [div_lt_div_iff_of_pos_left one_pos (by positivity) (by positivity)]; linarith⟩
  refine ⟨fun j => ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] χ), ?_, ?_, ?_⟩
  · intro j
    exact ((φ j).hasCompactSupport_normed).contDiff_convolution_left _ (φ j).contDiff_normed
      hχ.continuous.locallyIntegrable
  · intro j t
    have hlip : LipschitzWith L ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] χ) := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      have hint : ∀ z : ℝ, Integrable (fun s => (φ j).normed volume s * χ (z - s)) volume := fun z =>
        (((φ j).continuous_normed.mul (hχ.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
          ((φ j).hasCompactSupport_normed.mul_right))
      simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, Real.dist_eq]
      rw [← integral_sub (hint x) (hint y)]
      calc |∫ s, ((φ j).normed volume s * χ (x - s) - (φ j).normed volume s * χ (y - s))|
          ≤ ∫ s, |(φ j).normed volume s * χ (x - s) - (φ j).normed volume s * χ (y - s)| :=
            abs_integral_le_integral_abs
        _ ≤ ∫ s, (φ j).normed volume s * (L * |x - y|) := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
              (((φ j).integrable_normed).mul_const _) (Eventually.of_forall fun s => ?_)
            dsimp only
            rw [← mul_sub, abs_mul, abs_of_nonneg ((φ j).nonneg_normed s)]
            refine mul_le_mul_of_nonneg_left ?_ ((φ j).nonneg_normed s)
            have := hχ.dist_le_mul (x - s) (y - s)
            rw [Real.dist_eq, Real.dist_eq, show x - s - (y - s) = x - y by ring] at this
            exact this
        _ = L * |x - y| := by rw [integral_mul_const, (φ j).integral_normed, one_mul]
    have := norm_deriv_le_of_lipschitz (x₀ := t) hlip
    rwa [Real.norm_eq_abs] at this
  · intro j t
    have h := (φ j).dist_normed_convolution_le (μ := volume) (x₀ := t) (ε := L / ((j : ℝ) + 1))
      hχ.continuous.aestronglyMeasurable fun x hx => by
        have h1 := hχ.dist_le_mul x t
        have h2 : dist x t < 1 / ((j : ℝ) + 1) := hx
        calc dist (χ x) (χ t) ≤ L * dist x t := h1
          _ ≤ L * (1 / ((j : ℝ) + 1)) := mul_le_mul_of_nonneg_left h2.le L.2
          _ = L / ((j : ℝ) + 1) := by ring
    rwa [Real.dist_eq] at h

/-! ### Strong limits of convex combinations of a bounded sequence in a Hilbert space -/

theorem exists_tendsto_convexHull {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] (x : ℕ → F) {C : ℝ} (hx : ∀ j, ‖x j‖ ≤ C) :
    ∃ v : F, ∃ w : ℕ → F, (∀ n, w n ∈ convexHull ℝ (x '' Ici n)) ∧ Tendsto w atTop (𝓝 v) := by
  set K : ℕ → Set F := fun n => closure (convexHull ℝ (x '' Ici n)) with hK
  have hKne : ∀ n, (K n).Nonempty := fun n =>
    ⟨x n, subset_closure (subset_convexHull ℝ _ ⟨n, Set.mem_Ici.mpr le_rfl, rfl⟩)⟩
  have hKc : ∀ n, IsComplete (K n) := fun n => isClosed_closure.isComplete
  have hKv : ∀ n, Convex ℝ (K n) := fun n => (convex_convexHull ℝ _).closure
  have hKmono : ∀ n m, n ≤ m → K m ⊆ K n := fun n m hnm =>
    closure_mono (convexHull_mono (image_mono (Ici_subset_Ici.mpr hnm)))
  have hKb : ∀ n, K n ⊆ closedBall 0 C := fun n => by
    refine closure_minimal ?_ isClosed_closedBall
    refine convexHull_min ?_ (convex_closedBall 0 C)
    rintro _ ⟨j, -, rfl⟩
    simpa using hx j
  choose p hpK hpmin using fun n => exists_norm_eq_iInf_of_complete_convex (hKne n) (hKc n) (hKv n) 0
  -- `‖p n‖ ≤ ‖z‖` on `K n`
  have hle : ∀ n, ∀ z ∈ K n, ‖p n‖ ≤ ‖z‖ := fun n z hz => by
    have h := hpmin n
    simp only [zero_sub, norm_neg] at h
    rw [h]
    exact ciInf_le ⟨0, forall_mem_range.2 fun _ => norm_nonneg _⟩ (⟨z, hz⟩ : K n)
  set a : ℕ → ℝ := fun n => ‖p n‖ ^ 2 with ha
  have ha_mono : Monotone a := monotone_nat_of_le_succ fun n => by
    simp only [ha]
    gcongr
    exact hle n _ (hKmono n (n + 1) (Nat.le_succ n) (hpK (n + 1)))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hx 0)
  have ha_bdd : ∀ n, a n ≤ C ^ 2 := fun n => by
    simp only [ha]
    have := hKb n (hpK n)
    rw [mem_closedBall, dist_zero_right] at this
    gcongr
  obtain ⟨A, hA⟩ : ∃ A, Tendsto a atTop (𝓝 A) :=
    ⟨_, tendsto_atTop_ciSup ha_mono ⟨C ^ 2, forall_mem_range.2 ha_bdd⟩⟩
  have haA : ∀ n, a n ≤ A := fun n => ha_mono.ge_of_tendsto hA n
  -- parallelogram
  have hpar : ∀ n m, n ≤ m → ‖p n - p m‖ ^ 2 ≤ 2 * (A - a n) := fun n m hnm => by
    have hmid : (1 / 2 : ℝ) • (p n + p m) ∈ K n := by
      have := (hKv n) (hpK n) (hKmono n m hnm (hpK m)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simpa [smul_add] using this
    have h1 := hle n _ hmid
    have hp := parallelogram_law_with_norm ℝ (p n) (p m)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h1
    have h2 : ‖p n‖ ^ 2 ≤ (1 / 2 * ‖p n + p m‖) ^ 2 := by gcongr
    have h3 := haA m
    simp only [ha] at h3 ⊢
    nlinarith [h2, hp, h3]
  have hcauchy : CauchySeq p := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hA' : Tendsto (fun n => 2 * (A - a n)) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := A)).sub hA
      simpa using this.const_mul 2
    obtain ⟨N, hN⟩ := (hA'.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε ^ 2))).exists_forall_of_atTop
    refine ⟨N, fun m hm => ?_⟩
    rw [dist_eq_norm, norm_sub_rev]
    have h := (hpar N m hm).trans_lt (hN N le_rfl)
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hw : ∀ n, ∃ w ∈ convexHull ℝ (x '' Ici n), dist w (p n) < 1 / ((n : ℝ) + 1) := fun n => by
    have := Metric.mem_closure_iff.mp (hpK n) (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨w, hw, hd⟩ := this
    exact ⟨w, hw, by rwa [dist_comm]⟩
  choose w hwK hwd using hw
  refine ⟨v, w, hwK, ?_⟩
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  rw [tendsto_iff_dist_tendsto_zero]
  have hpv := tendsto_iff_dist_tendsto_zero.mp hv
  refine squeeze_zero (fun n => dist_nonneg)
    (fun n => (dist_triangle (w n) (p n) v).trans (add_le_add (hwd n).le le_rfl)) ?_
  simpa using h0.add hpv

end SharpLSI
