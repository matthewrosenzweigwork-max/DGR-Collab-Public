import DGRHS.Gaussian.SharpnessCubes
import Mathlib.MeasureTheory.Group.Prod

/-! Coordinate shells and their actual ordered-pair Lebesgue measure.  The
measure-preserving shear is the pinned native theorem; no favorable shell mass
is assumed.  This is an annular adaptation of the source lattice proof. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def sharpnessCoordinateShell (R : ℝ) : Set (ι → ℝ) :=
  Metric.closedBall 0 R \ Metric.closedBall 0 (R/2)

lemma measurableSet_sharpnessCoordinateShell (R : ℝ) :
    MeasurableSet (sharpnessCoordinateShell (ι := ι) R) :=
  measurableSet_closedBall.diff measurableSet_closedBall

lemma volume_sharpnessCoordinateShell {R : ℝ} (hR : 0 ≤ R) :
    volume (sharpnessCoordinateShell (ι := ι) R) =
      ENNReal.ofReal ((2*R)^Fintype.card ι - R^Fintype.card ι) := by
  have hs : Metric.closedBall (0 : ι → ℝ) (R/2) ⊆ Metric.closedBall 0 R :=
    Metric.closedBall_subset_closedBall (by linarith)
  have ho : volume (Metric.closedBall (0 : ι → ℝ) R) ≠ ∞ := by
    rw [Real.volume_pi_closedBall _ hR]; exact ENNReal.ofReal_ne_top
  have hi : volume (Metric.closedBall (0 : ι → ℝ) (R/2)) ≠ ∞ :=
    ne_top_of_le_ne_top ho (measure_mono hs)
  have hd : volume (sharpnessCoordinateShell (ι := ι) R) ≠ ∞ :=
    ne_top_of_le_ne_top ho (measure_mono sdiff_subset)
  change volume (Metric.closedBall (0 : ι → ℝ) R \ Metric.closedBall 0 (R/2)) ≠ ∞ at hd
  have he := congrArg ENNReal.toReal (measure_inter_add_sdiff (μ := volume)
    (t := Metric.closedBall (0 : ι → ℝ) (R/2))
    (Metric.closedBall (0 : ι → ℝ) R) measurableSet_closedBall)
  rw [inter_eq_right.mpr hs, ENNReal.toReal_add hi hd,
    Real.volume_pi_closedBall _ hR,
    Real.volume_pi_closedBall _ (by linarith : 0 ≤ R/2),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (2*R)^Fintype.card ι),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (2*(R/2))^Fintype.card ι)] at he
  have htwo : 2*(R/2) = R := by ring
  rw [htwo] at he
  change volume (Metric.closedBall (0 : ι → ℝ) R \ Metric.closedBall 0 (R/2)) = _
  rw [← ENNReal.ofReal_toReal hd]
  congr 1
  linarith

/-- The pair set uses the actual coordinate displacement, not a cell count. -/
def sharpnessAnnularPairs (z : ι → ℝ) (q R : ℝ) : Set ((ι → ℝ) × (ι → ℝ)) :=
  (fun p => (p.1, p.2-p.1)) ⁻¹'
    (Metric.closedBall z (q/2) ×ˢ sharpnessCoordinateShell R)

lemma measurableSet_sharpnessAnnularPairs (z : ι → ℝ) (q R : ℝ) :
    MeasurableSet (sharpnessAnnularPairs z q R) :=
  (measurableSet_closedBall.prod (measurableSet_sharpnessCoordinateShell R)).preimage
    (measurable_fst.prodMk (measurable_snd.sub measurable_fst))

lemma volume_sharpnessAnnularPairs (z : ι → ℝ) {q R : ℝ}
    (hq : 0 ≤ q) (hR : 0 ≤ R) :
    (volume.prod volume) (sharpnessAnnularPairs z q R) =
      ENNReal.ofReal (q^Fintype.card ι * ((2*R)^Fintype.card ι-R^Fintype.card ι)) := by
  rw [sharpnessAnnularPairs,
    (measurePreserving_prod_sub (volume : Measure (ι → ℝ)) volume).measure_preimage
      (measurableSet_closedBall.prod (measurableSet_sharpnessCoordinateShell R)).nullMeasurableSet,
    Measure.prod_prod, Real.volume_pi_closedBall _ (by linarith : 0 ≤ q/2),
    volume_sharpnessCoordinateShell hR]
  have he : 2*(q/2) = q := by ring
  rw [he, ← ENNReal.ofReal_mul (by positivity)]

lemma sharpnessAnnularPairs_subset_cube (z : ι → ℝ) {q R : ℝ}
    (hq : 0 ≤ q) (hR : R ≤ q/2) :
    sharpnessAnnularPairs z q R ⊆ Metric.closedBall z q ×ˢ Metric.closedBall z q := by
  rintro ⟨x,y⟩ hx
  have hxcore : dist x z ≤ q/2 := hx.1
  have hsep : dist y x ≤ R := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hx.2.1
  exact ⟨(le_trans hxcore (by linarith)),
    (dist_triangle y x z).trans (by linarith)⟩

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.volume_sharpnessCoordinateShell
#print axioms DGRHS.Gaussian.volume_sharpnessAnnularPairs
#print axioms DGRHS.Gaussian.sharpnessAnnularPairs_subset_cube
#check @DGRHS.Gaussian.volume_sharpnessAnnularPairs
