import DGRHS.Gaussian.GaussianLogInfiniteDiagonal
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! Supporting development. Actual Hilbert-valued measurability via measurable
proper squared distances, without assuming raw point evaluation is measurable in L2. -/
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology
namespace DGRHS.Gaussian

lemma measurable_of_measurable_distances {X E : Type*} [MeasurableSpace X]
    [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (f : X → E) (h : ∀ c, Measurable (fun x => dist (f x) c)) : Measurable f := by
  let B : Set (Set E) := {s | ∃ (c : E) (r : ℝ), s = Metric.ball c r}
  have hb : IsTopologicalBasis B := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro s ⟨c,r,rfl⟩;exact Metric.isOpen_ball
    · intro a s ha hs
      obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp hs a ha
      exact ⟨Metric.ball a r,⟨a,r,rfl⟩,Metric.mem_ball_self hr,hsub⟩
  rw [‹BorelSpace E›.measurable_eq,hb.borel_eq_generateFrom]
  apply measurable_generateFrom
  rintro s ⟨c,r,rfl⟩
  exact measurableSet_lt (h c) measurable_const

variable {ι : Type*} [Fintype ι]

lemma separableSpace_gaussianLogPhaseHilbert (η : ℝ) :
    SeparableSpace (Lp ℂ 2 (gaussianLogPhaseMeasure ι η)) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  letI : SecondCountableTopology (Lp ℂ 2 (gaussianLogPhaseMeasure ι η)) := inferInstance
  infer_instance

variable (η : ℝ) (hη : 0 < η) (hd : 0 < (Fintype.card ι : ℝ))
variable (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
variable (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
variable [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
variable (hpair : Integrable logPhysicalPair
  ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
include hη hd M hM hρ hpair

lemma norm_sq_sub_gaussianLogCenteredInfiniteFeature (x : EuclideanSpace ℝ ι)
    (ψ : Lp ℂ 2 (gaussianLogPhaseMeasure ι η)) :
    ‖gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair x - ψ‖^2 =
      ∫ p,‖gaussianLogCenteredPhase (gaussianRieszDensityMeasure ρ) x p - ψ p‖^2
        ∂gaussianLogPhaseMeasure ι η := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair x) ψ,
    coeFn_gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair x] with p hp hx
  rw [hp]
  simp only [Pi.sub_apply]
  rw [hx,real_inner_self_eq_norm_sq]

lemma stronglyMeasurable_gaussianLogCenteredInfiniteFeature :
    StronglyMeasurable (gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair) := by
  let μ := gaussianRieszDensityMeasure ρ
  let ν := gaussianLogPhaseMeasure ι η
  let k := gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair
  letI : SeparableSpace (Lp ℂ 2 ν) := separableSpace_gaussianLogPhaseHilbert η
  letI : MeasurableSpace (Lp ℂ 2 ν) := borel _
  letI : BorelSpace (Lp ℂ 2 ν) := ⟨rfl⟩
  have hm : Measurable k := by
    apply measurable_of_measurable_distances
    intro ψ
    have hs : StronglyMeasurable (fun q : EuclideanSpace ℝ ι × (ℝ × (ι → ℝ)) =>
        ‖gaussianLogCenteredPhase μ q.1 q.2 - ψ q.2‖^2) :=
      ((stronglyMeasurable_gaussianLogCenteredPhase_joint μ).sub
        ((Lp.stronglyMeasurable ψ).comp_measurable measurable_snd)).norm.pow 2
    have hi : Measurable (fun x => ∫ p,‖gaussianLogCenteredPhase μ x p - ψ p‖^2 ∂ν) :=
      hs.integral_prod_right'.measurable
    have he (x : EuclideanSpace ℝ ι) : dist (k x) ψ =
        Real.sqrt (∫ p,‖gaussianLogCenteredPhase μ x p - ψ p‖^2 ∂ν) := by
      rw [← norm_sq_sub_gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair]
      simp only [Real.sqrt_sq_eq_abs,abs_norm,dist_eq_norm,k]
    simp_rw [he]
    exact Real.continuous_sqrt.measurable.comp hi
  exact hm.stronglyMeasurable

lemma memLp_gaussianLogCenteredInfiniteFeature :
    MemLp (gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair) 2
      (gaussianRieszDensityMeasure ρ) := by
  let μ := gaussianRieszDensityMeasure ρ
  let k := gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair
  have hs := stronglyMeasurable_gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair
  apply (memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).mpr
  apply (integrable_gaussianLogBandDiagonalMajorant η M μ hpair).mono' (hs.norm.pow 2).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    change ‖‖k x‖^2‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact norm_sq_gaussianLogCenteredInfiniteFeature_le η hη hd ρ M hM hρ hpair x)

end DGRHS.Gaussian
#check @DGRHS.Gaussian.measurable_of_measurable_distances
#print axioms DGRHS.Gaussian.measurable_of_measurable_distances
#check @DGRHS.Gaussian.separableSpace_gaussianLogPhaseHilbert
#print axioms DGRHS.Gaussian.separableSpace_gaussianLogPhaseHilbert
#check @DGRHS.Gaussian.norm_sq_sub_gaussianLogCenteredInfiniteFeature
#print axioms DGRHS.Gaussian.norm_sq_sub_gaussianLogCenteredInfiniteFeature
#check @DGRHS.Gaussian.stronglyMeasurable_gaussianLogCenteredInfiniteFeature
#print axioms DGRHS.Gaussian.stronglyMeasurable_gaussianLogCenteredInfiniteFeature
#check @DGRHS.Gaussian.memLp_gaussianLogCenteredInfiniteFeature
#print axioms DGRHS.Gaussian.memLp_gaussianLogCenteredInfiniteFeature
