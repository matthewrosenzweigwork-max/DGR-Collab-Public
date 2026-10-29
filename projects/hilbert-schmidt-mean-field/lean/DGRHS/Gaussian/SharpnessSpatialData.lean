import DGRHS.Gaussian.SharpnessInitialCube
import DGRHS.Gaussian.SharpnessBadCells
import DGRHS.Gaussian.SharpnessCellMass

noncomputable section
open MeasureTheory Set BoxIntegral
open scoped ENNReal Classical
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def sharpnessInitialBox (z : ι → ℝ) (r : ℝ) (hr : 0 < r) : Box ι :=
  ⟨(fun i => z i-r), (fun i => z i+r), fun i => by linarith⟩

lemma sharpness_coordinate_closedBall_eq_Icc (z : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    Metric.closedBall z r = Icc (fun i => z i-r) (fun i => z i+r) := by
  ext x
  simp only [Metric.mem_closedBall, dist_pi_le_iff hr, Real.dist_eq, abs_le,
    mem_Icc, Pi.le_def]
  constructor
  · intro h
    constructor <;> intro i <;> linarith [(h i).1, (h i).2]
  · rintro ⟨hl, hu⟩ i
    constructor <;> linarith [hl i, hu i]

lemma sharpness_initial_box_ae_closedBall (z : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    (sharpnessInitialBox z r hr : Set (ι → ℝ)) =ᵐ[volume] Metric.closedBall z r := by
  rw [Box.coe_eq_pi, sharpness_coordinate_closedBall_eq_Icc z hr.le]
  exact Measure.univ_pi_Ioc_ae_eq_Icc

/-- Genuine source Q0 and all its finite dyadic bad-count bounds are constructed
from the actual bounded probability density; none is a favorable input. -/
theorem sharpness_exists_spatial_data (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρm : Measurable ρ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ a : ℝ, 0 < a ∧ ∃ I : Box ι, ∃ L : ℝ, 0 < L ∧
      (∀ i, I.upper i-I.lower i = L) ∧
      gaussianRieszDensityMeasure ρ (WithLp.ofLp ⁻¹' (I : Set (ι → ℝ))) ≤
        ENNReal.ofReal (1/2 : ℝ) ∧
      (∀ x y : EuclideanSpace ℝ ι, WithLp.ofLp x ∈ I → WithLp.ofLp y ∈ I → x ≠ y →
        gaussianRieszPhysicalPair s (x,y)/2 ≤
          hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s) (x,y)) ∧
      (∀ m : ℕ, ((sharpnessBadCells (sharpnessDyadicPartition I m)
        {z : ι → ℝ | a ≤ ρ (WithLp.toLp 2 z)}).card : ℝ) *
          (L/(2 : ℝ)^m)^Fintype.card ι ≤ 2*ε*(volume (I : Set (ι → ℝ))).toReal) := by
  obtain ⟨a, hap, z, r, hr, hden, hmass, hlocal⟩ :=
    sharpness_exists_initial_cube s hs ha ρ hρm M hM hρ ε hε
  let I := sharpnessInitialBox z r hr
  let S := {w : ι → ℝ | a ≤ ρ (WithLp.toLp 2 w)}
  have hS : MeasurableSet S := measurableSet_le measurable_const
    (hρm.comp (PiLp.volume_preserving_toLp ι).measurable)
  have he := sharpness_initial_box_ae_closedBall z hr
  have hv : volume (Metric.closedBall z r) = volume (I : Set (ι → ℝ)) := (measure_congr he).symm
  have hVfin : volume (Metric.closedBall z r) ≠ ∞ := by rw [hv]; exact sharpness_volume_box_ne_top I
  have hVpos : volume (Metric.closedBall z r) ≠ 0 := by
    rw [hv, volume_sharpnessBox]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    dsimp [I, sharpnessInitialBox]
    simp only [ENNReal.ofReal_eq_zero]
    linarith
  have hEnumFin : volume (S ∩ Metric.closedBall z r) ≠ ∞ :=
    ne_top_of_le_ne_top hVfin (measure_mono inter_subset_right)
  have hmul := (ENNReal.lt_div_iff_mul_lt (Or.inl hVpos) (Or.inl hVfin)).mp hden
  have hreal := ENNReal.toReal_strict_mono hEnumFin hmul
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith : 0 ≤ 1-ε)] at hreal
  have hDfin : volume (Metric.closedBall z r \ S) ≠ ∞ :=
    ne_top_of_le_ne_top hVfin (measure_mono sdiff_subset)
  have hadd := congrArg ENNReal.toReal (measure_inter_add_sdiff (μ := volume)
    (Metric.closedBall z r) hS)
  rw [inter_comm] at hadd
  rw [ENNReal.toReal_add hEnumFin hDfin] at hadd
  have hD : (volume ((I : Set (ι → ℝ)) \ S)).toReal ≤
      ε*(volume (I : Set (ι → ℝ))).toReal := by
    have heD : ((I : Set (ι → ℝ)) \ S) =ᵐ[volume] (Metric.closedBall z r \ S) := by
      filter_upwards [he] with x hx
      simp only [mem_sdiff]
      exact congrArg (fun p : Prop => p ∧ x ∉ S) hx
    rw [measure_congr heD, ← hv]
    linarith
  have hsub : (WithLp.ofLp ⁻¹' (I : Set (ι → ℝ))) ⊆ sharpnessCenteredCube z r := by
    intro x hx
    change (∀ i, z i-r ≤ x i) ∧ (∀ i, x i ≤ z i+r)
    change ∀ i, x i ∈ Ioc (z i-r) (z i+r) at hx
    exact ⟨fun i => (hx i).1.le, fun i => (hx i).2⟩
  refine ⟨a, hap, I, 2*r, by positivity, ?_, (measure_mono hsub).trans hmass, ?_, ?_⟩
  · intro i
    dsimp [I, sharpnessInitialBox]
    ring
  · intro x y hx hy hxy
    exact hlocal x y (hsub hx) (hsub hy) hxy
  · intro m
    have hw (i : ι) : I.upper i-I.lower i = 2*r := by dsimp [I, sharpnessInitialBox]; ring
    have hb := sharpness_dyadic_bad_count I (2*r) (by positivity) hw m S hS
    nlinarith

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_initial_box_ae_closedBall
#print axioms DGRHS.Gaussian.sharpness_exists_spatial_data
#check @DGRHS.Gaussian.sharpness_exists_spatial_data
