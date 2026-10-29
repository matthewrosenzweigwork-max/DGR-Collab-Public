import DGRHS.Gaussian.SharpnessAnnulusLoss

noncomputable section
open MeasureTheory Set BoxIntegral
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

/-- The actual physical density-point cube supplies simultaneous annular
mass bounds at every dyadic refinement and every shell below the core scale.
No annular pair-mass conclusion is an input. -/
theorem sharpness_exists_physical_annular_data (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρm : Measurable ρ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ a : ℝ, 0 < a ∧ ∃ z : ι → ℝ, ∃ q : ℝ, ∃ hq : 0 < q,
      gaussianRieszDensityMeasure ρ (sharpnessCenteredCube z q) ≤ ENNReal.ofReal (1/2 : ℝ) ∧
      (∀ x y : EuclideanSpace ℝ ι, x ∈ sharpnessCenteredCube z q →
        y ∈ sharpnessCenteredCube z q → x ≠ y →
        gaussianRieszPhysicalPair s (x,y)/2 ≤
          hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s) (x,y)) ∧
      ∀ (m : ℕ) (R : ℝ), 0 ≤ R → R ≤ q/2 →
        let I := sharpnessInitialBox z q hq
        let G := WithLp.toLp 2 ⁻¹' sharpnessGoodUnion ρ a (sharpnessDyadicPartition I m)
        q^Fintype.card ι*((2*R)^Fintype.card ι-R^Fintype.card ι) -
          6*ε*(2*q)^Fintype.card ι*(2*R)^Fintype.card ι ≤
        ((volume.prod volume) (sharpnessAnnularPairs z q R ∩ (G ×ˢ G))).toReal := by
  obtain ⟨a,hap,z,q,hq,hden,hmass,hlocal⟩ :=
    sharpness_exists_initial_cube s hs ha ρ hρm M hM hρ ε hε
  let I := sharpnessInitialBox z q hq
  let E := {w : ι → ℝ | a ≤ ρ (WithLp.toLp 2 w)}
  have hE : MeasurableSet E := measurableSet_le measurable_const
    (hρm.comp (PiLp.volume_preserving_toLp ι).measurable)
  have hv : volume (Metric.closedBall z q) = volume (I : Set (ι → ℝ)) :=
    (measure_congr (sharpness_initial_box_ae_closedBall z hq)).symm
  have hvfin : volume (Metric.closedBall z q) ≠ ∞ := by
    rw [Real.volume_pi_closedBall z hq.le]; exact ENNReal.ofReal_ne_top
  have hvpos : volume (Metric.closedBall z q) ≠ 0 := by
    rw [Real.volume_pi_closedBall z hq.le, ENNReal.ofReal_ne_zero_iff]
    positivity
  have hinfin : volume (E ∩ Metric.closedBall z q) ≠ ∞ :=
    ne_top_of_le_ne_top hvfin (measure_mono inter_subset_right)
  have hmul := (ENNReal.lt_div_iff_mul_lt (Or.inl hvpos) (Or.inl hvfin)).mp hden
  have hreal := ENNReal.toReal_strict_mono hinfin hmul
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith : 0 ≤ 1-ε)] at hreal
  have hdifffin : volume (Metric.closedBall z q \ E) ≠ ∞ :=
    ne_top_of_le_ne_top hvfin (measure_mono sdiff_subset)
  have hadd := congrArg ENNReal.toReal (measure_inter_add_sdiff (μ := volume)
    (Metric.closedBall z q) hE)
  rw [inter_comm, ENNReal.toReal_add hinfin hdifffin] at hadd
  have hd : (volume ((I : Set (ι → ℝ)) \ E)).toReal ≤ ε*(2*q)^Fintype.card ι := by
    have hae : ((I : Set (ι → ℝ)) \ E) =ᵐ[volume] (Metric.closedBall z q \ E) := by
      filter_upwards [sharpness_initial_box_ae_closedBall z hq] with x hx
      simp only [mem_sdiff]
      exact congrArg (fun p : Prop => p ∧ x ∉ E) hx
    rw [measure_congr hae]
    rw [Real.volume_pi_closedBall z hq.le,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ (2*q)^Fintype.card ι)] at hreal hadd
    linarith
  refine ⟨a,hap,z,q,hq,hmass,hlocal,?_⟩
  intro m R hR hRq
  have hb := sharpness_dyadic_good_annular_volume ρ hρm a z hq hR hRq m
  have hh := mul_le_mul_of_nonneg_right hd
    (show 0 ≤ (2*R)^Fintype.card ι by positivity)
  dsimp only at hb ⊢
  linarith

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_exists_physical_annular_data
#check @DGRHS.Gaussian.sharpness_exists_physical_annular_data
