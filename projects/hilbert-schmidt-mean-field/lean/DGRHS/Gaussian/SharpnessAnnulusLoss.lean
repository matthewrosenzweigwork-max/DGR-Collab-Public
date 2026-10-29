import DGRHS.Gaussian.SharpnessAnnulusGeometry
import DGRHS.Gaussian.SharpnessGoodDensity
import DGRHS.Gaussian.SharpnessSpatialData

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def sharpnessClosePairs (D : Set (ι → ℝ)) (R : ℝ) : Set ((ι → ℝ) × (ι → ℝ)) :=
  (fun p => (p.1, p.2-p.1)) ⁻¹' (D ×ˢ Metric.closedBall 0 R)

lemma measurableSet_sharpnessClosePairs {D : Set (ι → ℝ)} (hD : MeasurableSet D) (R : ℝ) :
    MeasurableSet (sharpnessClosePairs D R) :=
  (hD.prod measurableSet_closedBall).preimage
    (measurable_fst.prodMk (measurable_snd.sub measurable_fst))

lemma volume_sharpnessClosePairs {D : Set (ι → ℝ)} (hD : MeasurableSet D)
    {R : ℝ} (hR : 0 ≤ R) :
    (volume.prod volume) (sharpnessClosePairs D R) =
      volume D * ENNReal.ofReal ((2*R)^Fintype.card ι) := by
  rw [sharpnessClosePairs,
    (measurePreserving_prod_sub (volume : Measure (ι → ℝ)) volume).measure_preimage
      (hD.prod measurableSet_closedBall).nullMeasurableSet,
    Measure.prod_prod, Real.volume_pi_closedBall _ hR]

/-- Exact annular pair volume minus the genuine loss from either missing
endpoint.  The missing-volume hypothesis is not a pair-count premise. -/
theorem sharpness_good_annular_volume (z : ι → ℝ) {q R : ℝ}
    (hq : 0 ≤ q) (hR : 0 ≤ R) (hRq : R ≤ q/2)
    (G : Set (ι → ℝ)) (hG : MeasurableSet G) :
    q^Fintype.card ι*((2*R)^Fintype.card ι-R^Fintype.card ι) -
      2*(volume (Metric.closedBall z q \ G)).toReal*(2*R)^Fintype.card ι ≤
    ((volume.prod volume) (sharpnessAnnularPairs z q R ∩ (G ×ˢ G))).toReal := by
  let S := sharpnessAnnularPairs z q R
  let D := Metric.closedBall z q \ G
  let U := sharpnessClosePairs D R
  let V := Prod.swap ⁻¹' U
  have hD : MeasurableSet D := measurableSet_closedBall.diff hG
  have hU := measurableSet_sharpnessClosePairs hD R
  have hV : MeasurableSet V := hU.preimage measurable_swap
  have hS := measurableSet_sharpnessAnnularPairs z q R
  have hsubS := sharpnessAnnularPairs_subset_cube z hq hRq
  have hsub : S \ (G ×ˢ G) ⊆ U ∪ V := by
    rintro ⟨x,y⟩ ⟨hxy,hnot⟩
    have hcube := hsubS hxy
    have hsep : dist y x ≤ R := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hxy.2.1
    by_cases hx : x ∈ G
    · right
      have hy : y ∉ G := by intro hy; exact hnot ⟨hx,hy⟩
      exact ⟨⟨hcube.2,hy⟩, by simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero, Prod.swap,
        norm_sub_rev] using hsep⟩
    · left
      exact ⟨⟨hcube.1,hx⟩, by simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hsep⟩
  have hDfin : volume D ≠ ∞ := ne_top_of_le_ne_top
    (by rw [Real.volume_pi_closedBall z hq]; exact ENNReal.ofReal_ne_top)
    (measure_mono sdiff_subset)
  have hUvol : (volume.prod volume) U = volume D * ENNReal.ofReal ((2*R)^Fintype.card ι) :=
    volume_sharpnessClosePairs hD hR
  have hUfin : (volume.prod volume) U ≠ ∞ := by rw [hUvol]; finiteness
  have hVvol : (volume.prod volume) V = (volume.prod volume) U :=
    (Measure.measurePreserving_swap (μ := volume) (ν := volume)).measure_preimage hU.nullMeasurableSet
  have hVfin : (volume.prod volume) V ≠ ∞ := by rw [hVvol]; exact hUfin
  have hSvol : (volume.prod volume) S =
      ENNReal.ofReal (q^Fintype.card ι*((2*R)^Fintype.card ι-R^Fintype.card ι)) :=
    volume_sharpnessAnnularPairs z hq hR
  have hSfin : (volume.prod volume) S ≠ ∞ := by rw [hSvol]; exact ENNReal.ofReal_ne_top
  have hBfin : (volume.prod volume) (S \ (G ×ˢ G)) ≠ ∞ :=
    ne_top_of_le_ne_top hSfin (measure_mono sdiff_subset)
  have hGoodfin : (volume.prod volume) (S ∩ (G ×ˢ G)) ≠ ∞ :=
    ne_top_of_le_ne_top hSfin (measure_mono inter_subset_left)
  have hb := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hUfin,hVfin⟩)
    ((measure_mono hsub).trans (measure_union_le U V))
  rw [ENNReal.toReal_add hUfin hVfin, hVvol, hUvol, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (2*R)^Fintype.card ι)] at hb
  have he := congrArg ENNReal.toReal (measure_inter_add_sdiff (μ := volume.prod volume)
    S (hG.prod hG))
  have hpow : R^Fintype.card ι ≤ (2*R)^Fintype.card ι := by gcongr; linarith
  rw [ENNReal.toReal_add hGoodfin hBfin, hSvol,
    ENNReal.toReal_ofReal (mul_nonneg (by positivity) (sub_nonneg.mpr hpow))] at he
  change q^Fintype.card ι*((2*R)^Fintype.card ι-R^Fintype.card ι) -
    2*(volume D).toReal*(2*R)^Fintype.card ι ≤
    ((volume.prod volume) (S ∩ (G ×ˢ G))).toReal
  linarith

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.volume_sharpnessClosePairs
#print axioms DGRHS.Gaussian.sharpness_good_annular_volume
#check @DGRHS.Gaussian.sharpness_good_annular_volume

namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

/-- Actual density-level good atoms incur at most six times the missing
level volume in the annular ordered-pair estimate. -/
theorem sharpness_dyadic_good_annular_volume
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρm : Measurable ρ) (a : ℝ)
    (z : ι → ℝ) {q R : ℝ} (hq : 0 < q) (hR : 0 ≤ R) (hRq : R ≤ q/2) (m : ℕ) :
    let I := sharpnessInitialBox z q hq
    let G := WithLp.toLp 2 ⁻¹' sharpnessGoodUnion ρ a (sharpnessDyadicPartition I m)
    q^Fintype.card ι*((2*R)^Fintype.card ι-R^Fintype.card ι) -
      6*(volume ((I : Set (ι → ℝ)) \ {w | a ≤ ρ (WithLp.toLp 2 w)})).toReal *
        (2*R)^Fintype.card ι ≤
    ((volume.prod volume) (sharpnessAnnularPairs z q R ∩ (G ×ˢ G))).toReal := by
  dsimp only
  let I := sharpnessInitialBox z q hq
  let G := WithLp.toLp 2 ⁻¹' sharpnessGoodUnion ρ a (sharpnessDyadicPartition I m)
  have hG : MeasurableSet G := (measurableSet_sharpnessGoodUnion ρ hρm a _).preimage
    (PiLp.volume_preserving_toLp ι).measurable
  have hd := sharpness_good_union_complement_volume ρ hρm a I m
  have hae : ((I : Set (ι → ℝ)) \ G) =ᵐ[volume] (Metric.closedBall z q \ G) := by
    filter_upwards [sharpness_initial_box_ae_closedBall z hq] with x hx
    simp only [mem_sdiff]
    exact congrArg (fun p : Prop => p ∧ x ∉ G) hx
  rw [measure_congr hae] at hd
  have hbase := sharpness_good_annular_volume z hq.le hR hRq G hG
  have hmul := mul_le_mul_of_nonneg_right hd
    (show 0 ≤ (2*R)^Fintype.card ι by positivity)
  change q^Fintype.card ι*((2*R)^Fintype.card ι-R^Fintype.card ι) -
    6*(volume ((I : Set (ι → ℝ)) \ {w | a ≤ ρ (WithLp.toLp 2 w)})).toReal *
      (2*R)^Fintype.card ι ≤ _
  linarith

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_dyadic_good_annular_volume
#check @DGRHS.Gaussian.sharpness_dyadic_good_annular_volume
