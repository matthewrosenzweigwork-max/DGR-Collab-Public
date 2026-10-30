import DGPS.Examples.ThreeSpeciesCircle.InteractingEntropyVariation

/-! Entropy differentiation on every original absolute H1 density, including
the zero-entropy reference. The latter is treated by a flat derivative and
norm domination of the nonnegative clipping, not an entropy-positivity premise. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem entropyClip_hasDerivAt_zero {f : ℝ → ℝ}
    (hf : HasDerivAt f 0 0) (hf0 : f 0 = 0) :
    HasDerivAt (fun t => (ENNReal.ofReal (f t)).toReal) 0 0 := by
  have hraw : f =o[𝓝 (0 : ℝ)] (fun t : ℝ => t) := by
    simpa only [hf0, sub_zero, smul_zero] using hf.isLittleO
  have hdom : (fun t => (ENNReal.ofReal (f t)).toReal) =O[𝓝 (0 : ℝ)] f := by
    apply Asymptotics.IsBigO.of_bound'
    exact Eventually.of_forall fun t => by
      by_cases ht : 0 ≤ f t
      · rw [ENNReal.toReal_ofReal ht]
      · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge ht), ENNReal.toReal_zero,
          norm_zero]
        exact norm_nonneg _
  apply HasDerivAt.of_isLittleO
  simpa only [hf0, ENNReal.ofReal_zero, ENNReal.toReal_zero, sub_zero,
    smul_zero] using hdom.trans_isLittleO hraw

/-- The full normalized entropy derivative has no positivity restriction on
entropy and uses every genuine original H1 direction. -/
theorem absoluteRootVariation_entropy_all_hasDerivAt (h : ℝ) (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    HasDerivAt
      (fun t : ℝ => (ordinaryEntropy h (absoluteRootVariation ρ hφ t)).toReal)
      ((∫ x, eulF' (ρ.sqrt x) * φ x ∂haar 1) -
        2 * (∫ x, ρ.sqrt x * φ x * Real.log (referenceDensity h x) ∂haar 1) -
        (2 * ∫ x, ρ.sqrt x * φ x ∂haar 1) * ((ordinaryEntropy h ρ).toReal + 1)) 0 := by
  by_cases hH0 : ordinaryEntropy h ρ = 0
  · let n := fun t : ℝ => ∫ x, (ρ.sqrt x + t * φ x) ^ 2 ∂haar 1
    let Φ := fun t : ℝ => ∫ x, eulF (ρ.sqrt x + t * φ x) ∂haar 1
    let R := fun t : ℝ => ∫ x, (ρ.sqrt x + t * φ x) ^ 2 *
      Real.log (referenceDensity h x) ∂haar 1
    let E := fun t : ℝ => Φ t / n t - Real.log (n t) - R t / n t
    let m := ∫ x, ρ.sqrt x * φ x ∂haar 1
    let L := ∫ x, ρ.sqrt x * φ x * Real.log (referenceDensity h x) ∂haar 1
    have hw := isWeakGradient_weakGradient ρ.sqrt_mem
    have hn0 : n 0 = 1 := by simpa only [n, zero_mul, add_zero] using ρ.mass_one
    have hn : HasDerivAt n (2 * m) 0 := by
      have hh := hasDerivAt_integral_quad
        (c := fun _ : Torus 1 => (1 : ℝ)) (C := 1) aestronglyMeasurable_const
        (fun x => by norm_num) ρ.memLp_sqrt hφ.memLp
      simpa only [n, m, mul_one] using hh
    have hΦ : HasDerivAt Φ (∫ x, eulF' (ρ.sqrt x) * φ x ∂haar 1) 0 :=
      hasDerivAt_integral_eulF hw hφ
    have hLc : Continuous (fun x : Torus 1 => Real.log (referenceDensity h x)) :=
      (continuous_referenceDensity h).log (fun x => (referenceDensity_pos (h := h) x).ne')
    have hR : HasDerivAt R (2 * L) 0 :=
      hasDerivAt_integral_quad hLc.aestronglyMeasurable
        (abs_log_referenceDensity_le h) ρ.memLp_sqrt hφ.memLp
    have hlog : (fun x => Real.log (ρ.sqrt x ^ 2)) =ᵐ[haar 1]
        (fun x => Real.log (referenceDensity h x)) := by
      filter_upwards [str025_sqrt_eq_of_entropy_zero h ρ hH0] with x hx
      rw [hx, str025_w, Real.sq_sqrt (referenceDensity_pos (h := h) x).le]
    have hΦR : Φ 0 = R 0 := by
      apply integral_congr_ae
      filter_upwards [hlog] with x hx
      simp only [Φ, R, zero_mul, add_zero, eulF, hx]
    have hiL := integrable_mul_bdd_two hLc.aestronglyMeasurable
      (abs_log_referenceDensity_le h) ρ.memLp_sqrt hφ.memLp
    have him : Integrable (fun x => ρ.sqrt x * φ x) (haar 1) :=
      ρ.memLp_sqrt.integrable_mul hφ.memLp
    have hprime : (∫ x, eulF' (ρ.sqrt x) * φ x ∂haar 1) = 2 * L + 2 * m := by
      calc
        _ = ∫ x, 2 * (ρ.sqrt x * φ x * Real.log (referenceDensity h x)) +
            2 * (ρ.sqrt x * φ x) ∂haar 1 := by
          apply integral_congr_ae
          filter_upwards [hlog] with x hx
          unfold eulF'
          rw [hx]
          ring
        _ = _ := by
          rw [integral_add (hiL.const_mul 2) (him.const_mul 2),
            integral_const_mul, integral_const_mul]
    have hEn := ((hΦ.div hn (by rw [hn0]; exact one_ne_zero)).sub
      (hn.log (by rw [hn0]; exact one_ne_zero))).sub
        (hR.div hn (by rw [hn0]; exact one_ne_zero))
    have hE : HasDerivAt E 0 0 := by
      convert hEn using 1
      rw [hn0, hΦR, hprime]
      ring
    have hE0 : E 0 = 0 := by simp only [E, hn0, hΦR, div_one, Real.log_one]; ring
    have hclip := entropyClip_hasDerivAt_zero hE hE0
    have hnpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < n t :=
      hn.continuousAt.eventually (lt_mem_nhds (by rw [hn0]; norm_num))
    have hactual : HasDerivAt
        (fun t : ℝ => (ordinaryEntropy h (absoluteRootVariation ρ hφ t)).toReal) 0 0 := by
      apply hclip.congr_of_eventuallyEq
      filter_upwards [hnpos] with t hnt
      have hvm : MemH1 (fun x => ρ.sqrt x + t * φ x) := ⟨_, hw.add (hφ.smul t)⟩
      have he : ordinaryEntropy h (absoluteRootVariation ρ hφ t) = ENNReal.ofReal (E t) := by
        unfold absoluteRootVariation
        rw [dif_pos hnt]
        exact normAbs_entropy h hvm hnt
      rw [he]
    convert hactual using 1
    rw [hprime, hH0, ENNReal.toReal_zero]
    dsimp only [L, m]
    ring
  · exact absoluteRootVariation_entropy_hasDerivAt h ρ (lt_of_le_of_ne zero_le (Ne.symm hH0)) hφ

end DGPS.Examples.ThreeSpeciesCircle
