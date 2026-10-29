import DGRHS.Gaussian.GaussianLogFrullaniBound

/-! Genuine Gaussian Frullani formula by fixed-bound dominated convergence.
Both actual proper Mellin integrals and their scalar values converge to the
same limit. No supplied improper limit or uniform-integrability premise.
Source SHA256 6f52778d92aa534e2b5851ca0f6b0712dc56470259cb3efcb7146ac2384dac0c. -/
noncomputable section
open MeasureTheory Set Real Filter
open scoped Topology
namespace DGRHS.Gaussian

lemma integral_gaussianLogFrullani_mellin (r : ℝ) (hr : 0 < r) :
    (∫ t : ℝ in Ioi 0, gaussianLogMellinDifference 0 r t) = -Real.log r := by
  let s : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hs0 (j : ℕ) : 0 < s j := by dsimp [s]; positivity
  have hs1 (j : ℕ) : s j ≤ 1 := by
    dsimp [s]
    apply (div_le_one (by positivity : 0 < (j : ℝ) + 1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hs : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hsRight : Tendsto s atTop (𝓝[>] 0) := by
    have hp : Tendsto s atTop (𝓟 (Ioi 0)) :=
      tendsto_principal.mpr (Eventually.of_forall hs0)
    simpa only [nhdsWithin, inf_idem, inf_comm] using hs.inf hp
  have hi : Tendsto (fun j => ∫ t : ℝ in Ioi 0, gaussianLogMellinDifference (s j) r t)
      atTop (𝓝 (∫ t : ℝ in Ioi 0, gaussianLogMellinDifference 0 r t)) := by
    apply tendsto_integral_of_dominated_convergence (gaussianLogFrullaniMajorant r)
    · intro j
      exact (integrableOn_gaussianLogMellinDifference (s j) r (hs0 j) hr).aestronglyMeasurable
    · exact integrableOn_gaussianLogFrullaniMajorant r hr
    · intro j
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact gaussianLogMellinDifference_norm_le (s j) r t (hs0 j).le (hs1 j) ht
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hArg : Tendsto (fun j => Real.log t * (-s j - 1)) atTop
          (𝓝 (Real.log t * (-1))) := by
        simpa only [neg_zero, zero_sub] using (hs.neg.sub_const 1).const_mul (Real.log t)
      have he := (Real.continuous_exp.tendsto (Real.log t * (-1))).comp hArg
      have hp := he.mul_const (Real.exp (-r ^ 2 / (2 * t ^ 2)) -
        Real.exp (-1 / (2 * t ^ 2)))
      simpa only [gaussianLogMellinDifference, Real.rpow_def_of_pos ht,
        Function.comp_def, neg_zero, zero_sub] using hp
  have hv : Tendsto (fun j => ∫ t : ℝ in Ioi 0, gaussianLogMellinDifference (s j) r t)
      atTop (𝓝 (-Real.log r)) := by
    have h := (tendsto_gaussianLogMellin_value r hr).comp hsRight
    convert h using 1
    funext j
    change (∫ t : ℝ in Ioi 0, gaussianLogMellinDifference (s j) r t) =
      (2 : ℝ) ^ (s j / 2) * Real.Gamma (s j / 2 + 1) *
        ((r ^ (-s j) - 1) / s j)
    rw [integral_gaussianLogMellinDifference (s j) r (hs0 j) hr]
    ring
  exact tendsto_nhds_unique hi hv

lemma integrableOn_gaussianLog_profile_difference (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t⁻¹ *
      (Real.exp (-r ^ 2 / (2 * t ^ 2)) - Real.exp (-1 / (2 * t ^ 2)))) (Ioi 0) := by
  have he : gaussianLogMellinDifference 0 r = fun t : ℝ => t⁻¹ *
      (Real.exp (-r ^ 2 / (2 * t ^ 2)) - Real.exp (-1 / (2 * t ^ 2))) := by
    funext t
    simp only [gaussianLogMellinDifference, neg_zero, zero_sub, Real.rpow_neg_one]
  rw [← he]
  exact integrableOn_gaussianLogFrullani r hr

lemma integral_gaussianLog_profile_difference (r : ℝ) (hr : 0 < r) :
    (∫ t : ℝ in Ioi 0, t⁻¹ *
      (Real.exp (-r ^ 2 / (2 * t ^ 2)) - Real.exp (-1 / (2 * t ^ 2)))) = -Real.log r := by
  simpa only [gaussianLogMellinDifference, neg_zero, zero_sub, Real.rpow_neg_one] using
    integral_gaussianLogFrullani_mellin r hr

end DGRHS.Gaussian

#check DGRHS.Gaussian.integral_gaussianLogFrullani_mellin
#print axioms DGRHS.Gaussian.integral_gaussianLogFrullani_mellin

#check DGRHS.Gaussian.integrableOn_gaussianLog_profile_difference
#print axioms DGRHS.Gaussian.integrableOn_gaussianLog_profile_difference

#check DGRHS.Gaussian.integral_gaussianLog_profile_difference
#print axioms DGRHS.Gaussian.integral_gaussianLog_profile_difference
