import DGPS.FiniteN.AnisotropicQuarticScale

/-!
# Compact test transport for the anisotropic quartic chart

This is the smooth zero-extension step of the existing FIN059 chart architecture, applied to
an open two-dimensional chart. FIN068 supplies the map, inverse, open sets, and identities.
The weighted change-of-variables and full original-coordinate FIN069 estimate remain open.
-/

open MeasureTheory Filter Topology
open scoped ContDiff

namespace DGPS.FiniteN

/-- The zero extension of a smooth test pulled through the FIN068 inverse chart is a
legitimate smooth compactly supported test. These are precisely the open-chart and inverse
identities supplied by FIN068; there is no spectral or integral comparison hypothesis. -/
theorem quartic_chart_pullback (U Q : Set (ℝ × ℝ)) (hQo : IsOpen Q)
    (T R : ℝ × ℝ → ℝ × ℝ) (hT : ContinuousOn T U) (hR : ContDiffOn ℝ ∞ R Q)
    (hTU : ∀ x ∈ U, T x ∈ Q) (hTR : ∀ q ∈ Q, T (R q) = q)
    (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hFU : tsupport F ⊆ U) :
    ContDiff ℝ ∞ (Q.indicator (fun q => F (R q))) ∧
      HasCompactSupport (Q.indicator (fun q => F (R q))) ∧
      (∀ q ∈ Q, fderiv ℝ (Q.indicator (fun z => F (R z))) q =
        (fderiv ℝ F (R q)).comp (fderiv ℝ R q)) := by
  classical
  let K := T '' tsupport F
  have hKc : IsCompact K := hFc.isCompact.image_of_continuousOn (hT.mono hFU)
  have hKQ : K ⊆ Q := by
    rintro q ⟨x, hx, rfl⟩
    exact hTU x (hFU hx)
  have hzero : ∀ q, q ∉ K → Q.indicator (fun z => F (R z)) q = 0 := by
    intro q hq
    by_cases hqQ : q ∈ Q
    · rw [Set.indicator_of_mem hqQ]
      by_contra h
      exact hq ⟨R q, subset_tsupport F h, hTR q hqQ⟩
    · rw [Set.indicator_of_notMem hqQ]
  have heq : ∀ q ∈ Q, Q.indicator (fun z => F (R z)) =ᶠ[nhds q]
      fun z => F (R z) := by
    intro q hq
    filter_upwards [hQo.mem_nhds hq] with z hz
    exact Set.indicator_of_mem hz _
  refine ⟨?_, HasCompactSupport.intro hKc hzero, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro q
    by_cases hq : q ∈ Q
    · have hRq : ContDiffAt ℝ ∞ R q := hR.contDiffAt (hQo.mem_nhds hq)
      exact (hF.contDiffAt.comp q hRq).congr_of_eventuallyEq (heq q hq)
    · have hqK : q ∉ K := fun h => hq (hKQ h)
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hqK] with z hz
      exact hzero z hz
  · intro q hq
    have hRq : DifferentiableAt ℝ R q :=
      (hR.contDiffAt (hQo.mem_nhds hq)).differentiableAt (by simp)
    have hcomp := ((hF.differentiable (by simp)) (R q)).hasFDerivAt.comp q hRq.hasFDerivAt
    rw [(heq q hq).fderiv_eq]
    change fderiv ℝ (F ∘ R) q = (fderiv ℝ F (R q)).comp (fderiv ℝ R q)
    exact hcomp.fderiv

end DGPS.FiniteN
