import DGPS.FiniteN.AnisotropicQuarticRareRectangle
import DGPS.FiniteN.AnisotropicQuarticAuxiliaryMass
import DGPS.FiniteN.AnisotropicQuarticEuclidean

/-! A genuine two-sided auxiliary mass estimate on an original-coordinate rare core.
The parameter `s` will be `N^(-1/4)`; no occupation estimate or rare mass is an input. -/

open MeasureTheory Set
open DGPS.Models DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ENNReal

namespace DGPS.FiniteN

def quarticRareRectangle (s : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  (fun w => (w 0, w 1)) ⁻¹' (Icc (-4 - s ^ 2) (-4 + s ^ 2) ×ˢ Icc (-s) s)

theorem quarticRareRectangle_measurable (s : ℝ) : MeasurableSet (quarticRareRectangle s) :=
  (isClosed_Icc.prod isClosed_Icc).measurableSet.preimage
    quartic_euclidean_volume_preserving.measurable

/-- The exact Euclidean volume, with the physical coordinates and their normalization. -/
theorem quarticRareRectangle_volume (s : ℝ) (hs : 0 ≤ s) :
    volume (quarticRareRectangle s) = ENNReal.ofReal (4 * s ^ 3) := by
  unfold quarticRareRectangle
  rw [quartic_euclidean_volume_preserving.measure_preimage
    (isClosed_Icc.prod isClosed_Icc).measurableSet.nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
  rw [show (-4 + s ^ 2) - (-4 - s ^ 2) = 2 * s ^ 2 by ring,
    show s - -s = 2 * s by ring, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * s ^ 2)]
  congr 1
  ring

theorem quarticRareRectangle_mem (s : ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    w ∈ quarticRareRectangle s ↔ |w 0 + 4| ≤ s ^ 2 ∧ |w 1| ≤ s := by
  change ((-4 - s ^ 2 ≤ w 0 ∧ w 0 ≤ -4 + s ^ 2) ∧ (-s ≤ w 1 ∧ w 1 ≤ s)) ↔ _
  rw [abs_le, abs_le]
  constructor <;> intro h <;> constructor <;> constructor <;> linarith [h.1.1, h.1.2, h.2.1, h.2.2]

/-- The raw mass is comparable to the true saddle weight times the exact rare-core volume. -/
theorem quartic_rare_rectangle_raw_mass :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ ∀ N s : ℝ,
      0 < N → 0 ≤ s → s ≤ δ → N * s ^ 4 ≤ 1 →
      4 * s ^ 3 * (Real.exp (-C) * Real.exp (-(N * quarticPsi_FIN066 !₂[-4, 0]))) ≤
        ∫ w in quarticRareRectangle s, Real.exp (-(N * quarticPsi_FIN066 w)) ∧
      (∫ w in quarticRareRectangle s, Real.exp (-(N * quarticPsi_FIN066 w))) ≤
        4 * s ^ 3 * (Real.exp C * Real.exp (-(N * quarticPsi_FIN066 !₂[-4, 0]))) := by
  obtain ⟨δ, C, hδ, hδ1, hC, hweight⟩ := quartic_rare_rectangle_weight
  refine ⟨δ, C, hδ, hδ1, hC, fun N s hN hs hsδ hscale => ?_⟩
  have hfinite : volume (quarticRareRectangle s) ≠ ∞ := by
    rw [quarticRareRectangle_volume s hs]
    exact ENNReal.ofReal_ne_top
  have hi := (quartic_weight_integrable N hN).integrableOn (s := quarticRareRectangle s)
  have hb : ∀ w ∈ quarticRareRectangle s,
      Real.exp (-C) * Real.exp (-(N * quarticPsi_FIN066 !₂[-4, 0])) ≤
        Real.exp (-(N * quarticPsi_FIN066 w)) ∧
      Real.exp (-(N * quarticPsi_FIN066 w)) ≤
        Real.exp C * Real.exp (-(N * quarticPsi_FIN066 !₂[-4, 0])) := by
    intro w hw
    obtain ⟨hx, hy⟩ := (quarticRareRectangle_mem s w).mp hw
    have h := hweight N s (w 0 + 4) (w 1) hN.le hs hsδ hscale hx hy
    have he : (!₂[-4 + (w 0 + 4), w 1] : EuclideanSpace ℝ (Fin 2)) = w := by
      ext i
      fin_cases i <;> simp <;> ring
    simpa only [he] using h
  have hlo := setIntegral_mono_on (integrableOn_const hfinite) hi
    (quarticRareRectangle_measurable s) (fun w hw => (hb w hw).1)
  have hhi := setIntegral_mono_on hi (integrableOn_const hfinite)
    (quarticRareRectangle_measurable s) (fun w hw => (hb w hw).2)
  have hvol : volume.real (quarticRareRectangle s) = 4 * s ^ 3 := by
    rw [measureReal_def, quarticRareRectangle_volume s hs, ENNReal.toReal_ofReal (by positivity)]
  simpa only [setIntegral_const, smul_eq_mul, hvol] using And.intro hlo hhi

/-- Actual normalized auxiliary mass, retaining the genuine finite positive normalizer. -/
theorem quartic_rare_rectangle_normalized_mass :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ ∀ N s : ℝ,
      0 < N → 0 ≤ s → s ≤ δ → N * s ^ 4 ≤ 1 →
      (4 * s ^ 3 * (Real.exp (-C) * Real.exp (-(N * quarticPsi_FIN066 !₂[-4, 0])))) /
          (∫ w, Real.exp (-(N * quarticPsi_FIN066 w))) ≤
        ((imsEta N quarticPsi_FIN066) (quarticRareRectangle s)).toReal ∧
      ((imsEta N quarticPsi_FIN066) (quarticRareRectangle s)).toReal ≤
        (4 * s ^ 3 * (Real.exp C * Real.exp (-(N * quarticPsi_FIN066 !₂[-4, 0])))) /
          (∫ w, Real.exp (-(N * quarticPsi_FIN066 w))) := by
  obtain ⟨δ, C, hδ, hδ1, hC, hraw⟩ := quartic_rare_rectangle_raw_mass
  refine ⟨δ, C, hδ, hδ1, hC, fun N s hN hs hsδ hscale => ?_⟩
  rw [TiltedXY.Fin049.imsEta_real_FIN049 N quarticPsi_FIN066 (quartic_partition_pos N hN)
    (quarticRareRectangle s) (quarticRareRectangle_measurable s)]
  exact ⟨div_le_div_of_nonneg_right (hraw N s hN hs hsδ hscale).1
      (quartic_partition_pos N hN).le,
    div_le_div_of_nonneg_right (hraw N s hN hs hsδ hscale).2
      (quartic_partition_pos N hN).le⟩

end DGPS.FiniteN
