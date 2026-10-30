import DGPS.FiniteN.AnisotropicQuarticRareStrip
import DGPS.FiniteN.AnisotropicQuarticEuclidean

/-! Restoration of the exact Euclidean auxiliary coordinates in the rare-strip bound. -/

open MeasureTheory Set
open DGPS.Models DGPS.FiniteN.QuarticSaddleGlobalFIN066

namespace DGPS.FiniteN

def quarticRareStrip (δ s : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {w | |w 0 + 4| ≤ δ ∧ |w 1| ≤ s}

theorem quartic_rare_strip_integral_coordinates (N δ s : ℝ) :
    (∫ w in quarticRareStrip δ s, Real.exp (-(N * quarticPsi_FIN066 w))) =
      ∫ p : ℝ × ℝ in Icc (-δ) δ ×ˢ Icc (-s) s,
        Real.exp (-(N * quarticPsi_FIN066 !₂[-4 + p.1, p.2])) := by
  let S : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℝ × ℝ :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  let T : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ := fun w => S w + (4, 0)
  have hS : MeasurePreserving S := by
    convert quartic_euclidean_volume_preserving using 1 <;> rfl
  have hT : MeasurePreserving T := (measurePreserving_add_right volume (4, 0)).comp hS
  have hemb : MeasurableEmbedding T :=
    (measurableEmbedding_addRight (4, 0)).comp S.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hset : T ⁻¹' (Icc (-δ) δ ×ˢ Icc (-s) s) = quarticRareStrip δ s := by
    ext w
    change ((-δ ≤ w 0 + 4 ∧ w 0 + 4 ≤ δ) ∧ (-s ≤ w 1 + 0 ∧ w 1 + 0 ≤ s)) ↔ _
    simp only [quarticRareStrip, mem_setOf_eq, abs_le, add_zero]
  have he : ∀ w, (!₂[-4 + (T w).1, (T w).2] : EuclideanSpace ℝ (Fin 2)) = w := by
    intro w
    ext i
    fin_cases i
    · change -4 + (w 0 + 4) = w 0
      ring
    · change w 1 + 0 = w 1
      ring
  have h := hT.setIntegral_preimage_emb hemb
    (fun p : ℝ × ℝ => Real.exp (-(N * quarticPsi_FIN066 !₂[-4 + p.1, p.2])))
    (Icc (-δ) δ ×ˢ Icc (-s) s)
  rw [hset] at h
  simpa only [he] using h

/-- The enlarged-strip bound for the genuine auxiliary measure's Euclidean coordinates. -/
theorem quartic_physical_rare_strip_raw_upper :
    ∃ δ c K : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < c ∧ 0 < K ∧ ∀ N s L : ℝ,
      0 < N → 0 ≤ s → 0 ≤ L → s ^ 2 ≤ δ → N * s ^ 4 ≤ L →
      (∫ w in quarticRareStrip δ s, Real.exp (-(N * quarticPsi_FIN066 w))) ≤
        (Real.exp (K * L) * Real.exp (-(N * quarticPsi_FIN066 !₂[-4, 0]))) *
          Real.sqrt (Real.pi / (N * c)) * (2 * s) := by
  obtain ⟨δ, c, K, hδ, hδ1, hc, hK, hupper⟩ := quartic_rare_strip_raw_upper
  refine ⟨δ, c, K, hδ, hδ1, hc, hK, fun N s L hN hs hL hsδ hscale => ?_⟩
  rw [quartic_rare_strip_integral_coordinates]
  exact hupper N s L hN hs hL hsδ hscale

end DGPS.FiniteN
