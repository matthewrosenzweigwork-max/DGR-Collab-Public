import LeanResearch.PeriodicAttractiveLogGas.ReferenceSelfTerms
import LeanResearch.PeriodicAttractiveLogGas.PositiveProductConditionals
import LeanResearch.PeriodicAttractiveLogGas.RelativeEntropyVariational
import Mathlib.Probability.Independence.Integration

/-! The actual product-reference density and source change of reference.
No fixed-point existence, desired density identity, or exponential moment is assumed. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal

namespace PeriodicAttractiveLogGas.ReferenceDensityChange

open MeshCells LabelOccupations CellRestrictions ReferenceResidual ReferenceSelfTerms

/-- A finite product of actual density laws, proved on measurable rectangles. -/
theorem pi_density {N : ℕ} (τ μ : Fin N → Measure Torus)
    [∀ i, IsProbabilityMeasure (τ i)] [∀ i, IsProbabilityMeasure (μ i)]
    (w : Fin N → Torus → ℝ≥0∞) (hw : ∀ i, Measurable (w i))
    (hμ : ∀ i, μ i = (τ i).withDensity (w i)) :
    Measure.pi μ = (Measure.pi τ).withDensity (fun X => ∏ i, w i (X i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have he : (Set.univ.pi s).indicator (fun X : Fin N → Torus => ∏ i, w i (X i)) =
      fun X => ∏ i, (s i).indicator (w i) (X i) := by
    funext X
    by_cases hX : X ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hX]
      apply Finset.prod_congr rfl
      intro i _
      rw [Set.indicator_of_mem (hX i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hX]
      have hi : ∃ i, X i ∉ s i := by simpa only [Set.mem_univ_pi, not_forall] using hX
      obtain ⟨i, hi⟩ := hi
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs), he]
  have hind : iIndepFun (fun i (X : Fin N → Torus) => (s i).indicator (w i) (X i))
      (Measure.pi τ) := iIndepFun_pi (fun i => ((hw i).indicator (hs i)).aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _ hind
    (fun i => ((hw i).indicator (hs i)).comp (measurable_pi_apply i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [hμ i, withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]
  have hm := (measurePreserving_eval τ i).map_eq
  rw [← hm, lintegral_map ((hw i).indicator (hs i)) (measurable_pi_apply i)]

theorem measurable_potential (μ : Measure Torus) [SFinite μ] :
    Measurable (potential μ) :=
  measurable_greenKernel.stronglyMeasurable.integral_prod_right.measurable

theorem measurable_averagePotential {J N : ℕ}
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N) : Measurable (averagePotential μ η) := by
  unfold averagePotential
  exact (Finset.measurable_sum _ (fun i _ => measurable_potential (μ (η i)))).div_const _

theorem measurable_selfTerm {J N : ℕ}
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N) : Measurable (selfTerm μ η) := by
  unfold selfTerm
  exact (Finset.measurable_sum _ (fun i _ =>
    (measurable_potential (μ (η i))).comp (measurable_pi_apply i))).div_const _

theorem measurable_residualSum {J N : ℕ}
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N) : Measurable (ResidualExponential.residualSum μ η) := by
  have hh := ResidualExponential.measurable_near_far 0 μ η
  have he := funext (ResidualExponential.residualSum_split 0 μ η)
  rw [he]
  exact hh.2.add hh.1

/-- The original Fourier representative and the regular representative yield
the same weight under the actual prescribed-cell product law. -/
theorem ae_regular_weight {J N : ℕ} (hJ : 0 < J) (η : LabelVector J N) (β : ℝ) :
    gibbsWeight regularGreenRepresentative N β =ᵐ[labelReference hJ η]
      gibbsWeight greenRealRepresentative N β := by
  rw [labelReference_eq]
  exact Measure.ae_smul_measure ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self :
    (referenceMeasure N).restrict (labelFiber hJ η) ≪ referenceMeasure N).ae_le
    (gibbsWeight_congr_ae_kernel regularGreenRepresentative_ae N β)) _


def cellNormalizer {J N : ℕ} (hJ : 0 < J) (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J N) (β : ℝ) (a : MeshIndex J) : ℝ :=
  ∫ z, Real.exp (β * averagePotential μ η z) ∂meshCellMeasure J hJ a

def referenceTilt {J N : ℕ} (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J N) (β : ℝ) (X : Configuration N) : ℝ :=
  Real.exp (β * ResidualExponential.residualSum μ η X - β * selfTerm μ η X)

def referenceNormalizer {J N : ℕ} (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J N) (β : ℝ) : ℝ :=
  ∫ X, referenceTilt μ η β X ∂Measure.pi (fun i => μ (η i))

theorem measurable_referenceTilt {J N : ℕ}
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N) (β : ℝ) : Measurable (referenceTilt μ η β) :=
  (((measurable_residualSum μ η).const_mul β).sub
    ((measurable_selfTerm μ η).const_mul β)).exp

theorem cellNormalizer_pos_of_formula {J N : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N) (β : ℝ) (a : MeshIndex J)
    (hμ : μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a))) :
    0 < cellNormalizer hJ μ η β a := by
  have hn : 0 ≤ cellNormalizer hJ μ η β a := integral_nonneg fun _ => (Real.exp_pos _).le
  by_contra hp
  have hz : cellNormalizer hJ μ η β a = 0 := le_antisymm (le_of_not_gt hp) hn
  have hm : μ a Set.univ = 1 := measure_univ
  rw [hμ] at hm
  simp only [hz, div_zero, ENNReal.ofReal_zero] at hm
  change ((meshCellMeasure J hJ a).withDensity 0) Set.univ = 1 at hm
  rw [withDensity_zero] at hm
  exact zero_ne_one hm

theorem pi_cell_formula {J N : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N) (β : ℝ)
    (hμ : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a))) :
    Measure.pi (fun i => μ (η i)) = (labelReference hJ η).withDensity (fun X =>
      ENNReal.ofReal (Real.exp (β * ∑ i, averagePotential μ η (X i)) /
        ∏ i, cellNormalizer hJ μ η β (η i))) := by
  classical
  rw [pi_density (fun i => meshCellMeasure J hJ (η i)) (fun i => μ (η i))
    (fun i z => ENNReal.ofReal (Real.exp (β * averagePotential μ η z) /
      cellNormalizer hJ μ η β (η i)))
    (fun i => (((measurable_averagePotential μ η).const_mul β).exp.div_const _).ennreal_ofReal)
    (fun i => hμ (η i))]
  congr 1
  funext X
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => div_nonneg
    (Real.exp_pos _).le (cellNormalizer_pos_of_formula hJ μ η β (η i) (hμ (η i))).le)]
  congr 1
  rw [Finset.prod_div_distrib, ← Real.exp_sum, ← Finset.mul_sum]

/-- The source configuration-independent constant is retained explicitly. -/
def referenceFactor {J N : ℕ} (hJ : 0 < J) (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J N) (β : ℝ) : ℝ :=
  Real.exp (β * ((∑ ij ∈ ResidualNearExponential.upperPairs N,
    pairAverage (μ (η ij.1)) (μ (η ij.2))) / (N : ℝ))) /
    ∏ i, cellNormalizer hJ μ η β (η i)

theorem referenceFactor_pos {J N : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N) (β : ℝ)
    (hμ : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a))) :
    0 < referenceFactor hJ μ η β :=
  div_pos (Real.exp_pos _) (Finset.prod_pos fun i _ =>
    cellNormalizer_pos_of_formula hJ μ η β (η i) (hμ (η i)))

theorem reference_weight_identity {J N : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N) (β : ℝ) (X : Configuration N) :
    (Real.exp (β * ∑ i, averagePotential μ η (X i)) /
        ∏ i, cellNormalizer hJ μ η β (η i)) * referenceTilt μ η β X =
      referenceFactor hJ μ η β * gibbsWeight regularGreenRepresentative N β X := by
  rw [referenceTilt, referenceFactor, gibbsWeight, centering_expansion μ η X,
    pairEnergy_eq_sum_orderedPairs]
  have he : (∑ ij ∈ planarOrderedPairs N, regularGreenRepresentative (X ij.1 - X ij.2)) =
      ∑ ij ∈ ResidualNearExponential.upperPairs N, greenKernel (X ij.1) (X ij.2) := rfl
  rw [he]
  rw [div_mul_eq_mul_div, ← Real.exp_add, div_mul_eq_mul_div, ← Real.exp_add]
  congr 2
  ring

/-- The actual unnormalized tilted product reference equals a finite positive
constant times the original labelled Gibbs weight; representatives are identified AE. -/
theorem unnormalized_reference_density {J N : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N) (β : ℝ)
    (hμ : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a))) :
    (Measure.pi (fun i => μ (η i))).withDensity (fun X => ENNReal.ofReal (referenceTilt μ η β X)) =
      ENNReal.ofReal (referenceFactor hJ μ η β) •
        (labelReference hJ η).withDensity (greenWeightDensity N β) := by
  have hp : 0 < ∏ i, cellNormalizer hJ μ η β (η i) :=
    Finset.prod_pos fun i _ => cellNormalizer_pos_of_formula hJ μ η β (η i) (hμ (η i))
  have hD : Measurable (fun X : Configuration N => ENNReal.ofReal
      (Real.exp (β * ∑ i, averagePotential μ η (X i)) /
        ∏ i, cellNormalizer hJ μ η β (η i))) := by
    apply Measurable.ennreal_ofReal
    apply Measurable.div_const
    apply Measurable.exp
    apply Measurable.const_mul
    exact Finset.measurable_sum _ (fun i _ =>
      (measurable_averagePotential μ η).comp (measurable_pi_apply i))
  rw [pi_cell_formula hJ μ η β hμ, ← withDensity_mul _ hD
    (measurable_referenceTilt μ η β).ennreal_ofReal,
    ← withDensity_smul _ (measurable_greenWeightDensity N β)]
  apply withDensity_congr_ae
  filter_upwards [ae_regular_weight hJ η β] with X hX
  change ENNReal.ofReal _ * ENNReal.ofReal _ = ENNReal.ofReal _ * ENNReal.ofReal _
  rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le hp.le),
    reference_weight_identity, ENNReal.ofReal_mul (referenceFactor_pos hJ μ η β hμ).le, hX]


/-- Finiteness of the source normalizer follows from actual labelled Gibbs
normalization and the proved finite positive change-of-reference factor. -/
theorem referenceTilt_integrable {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (hμ : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a))) :
    Integrable (referenceTilt μ η β) (Measure.pi (fun i => μ (η i))) := by
  have he := congrArg (fun ν : Measure (Configuration N) => ν Set.univ)
    (unnormalized_reference_density hJ μ η β hμ)
  simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    Measure.smul_apply, smul_eq_mul] at he
  have hn : (∫⁻ X, ENNReal.ofReal (referenceTilt μ η β X) ∂Measure.pi (fun i => μ (η i))) ≠ ⊤ := by
    rw [he]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (labelPartitionFunction_ne_top hJ hN η hβ hsub)
  exact (lintegral_ofReal_ne_top_iff_integrable (measurable_referenceTilt μ η β).aestronglyMeasurable
    (Eventually.of_forall fun X => (Real.exp_pos _).le)).mp hn

theorem referenceNormalizer_pos {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (hμ : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a))) :
    0 < referenceNormalizer μ η β :=
  integral_exp_pos (referenceTilt_integrable hJ hN μ η hβ hsub hμ)

/-- Source eq:reference-density for every actual family satisfying the stated
cell exponential formula. True tilt integrability and normalizer positivity
are conclusions; fixed-point existence is a separate preceding source theorem. -/
theorem change_of_reference {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (hμ : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a))) :
    Integrable (referenceTilt μ η β) (Measure.pi (fun i => μ (η i))) ∧
      0 < referenceNormalizer μ η β ∧
      labelGibbsMeasure hJ η β = (Measure.pi (fun i => μ (η i))).withDensity
        (fun X => ENNReal.ofReal (referenceTilt μ η β X / referenceNormalizer μ η β)) := by
  have hi := referenceTilt_integrable hJ hN μ η hβ hsub hμ
  have hz := referenceNormalizer_pos hJ hN μ η hβ hsub hμ
  refine ⟨hi, hz, ?_⟩
  calc
    labelGibbsMeasure hJ η β =
        ProbabilityTheory.cond ((labelReference hJ η).withDensity (greenWeightDensity N β)) Set.univ := by
      simp only [labelGibbsMeasure, ProbabilityTheory.cond, withDensity_apply _ MeasurableSet.univ,
        Measure.restrict_univ, labelPartitionFunction]
    _ = ProbabilityTheory.cond ((Measure.pi (fun i => μ (η i))).withDensity
        (fun X => ENNReal.ofReal (referenceTilt μ η β X))) Set.univ := by
      rw [unnormalized_reference_density hJ μ η β hμ,
        CellRestrictions.cond_smul _ _ (ENNReal.ofReal_pos.mpr (referenceFactor_pos hJ μ η β hμ)).ne'
          ENNReal.ofReal_ne_top]
    _ = _ := PositiveProductConditionals.cond_withDensity_eq_real_density _
      (measurable_referenceTilt μ η β) (fun _ => (Real.exp_pos _).le) hi hz

/-- Full density-facing source lemma, retaining the supplied two-sided bounds,
the exact self coefficient and the diagonal reference constants. -/
theorem change_of_reference_with_self_bounds {J N : ℕ} (hJ : 0 < J)
    (hmesh : 8 ≤ J) (hN : 2 ≤ N)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (hμ : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
    (hb : ∀ a, ∀ᵐ z ∂meshCellMeasure J hJ a,
      Real.exp (-1) ≤ Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ∧
        Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ≤ Real.exp 1) :
    Integrable (referenceTilt μ η β) (Measure.pi (fun i => μ (η i))) ∧
      0 < referenceNormalizer μ η β ∧
      labelGibbsMeasure hJ η β = (Measure.pi (fun i => μ (η i))).withDensity
        (fun X => ENNReal.ofReal (referenceTilt μ η β X / referenceNormalizer μ η β)) ∧
      (∀ a, Integrable (potential (μ a)) (μ a) ∧ |pairAverage (μ a) (μ a)| ≤ selfBound J) ∧
      (∀ X, (∀ i, X i ∈ closure (meshCell J hJ (η i))) → |selfTerm μ η X| ≤ selfBound J) ∧
      (∀ᵐ X ∂Measure.pi (fun i => μ (η i)), |selfTerm μ η X| ≤ selfBound J) := by
  have hh := change_of_reference hJ hN μ η hβ hsub hμ
  have hs := self_terms_density_bound hJ hmesh μ
    (fun a z => ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a))
    hμ (fun a => (hb a).mono fun z hz =>
      ⟨ENNReal.ofReal_le_ofReal hz.1, ENNReal.ofReal_le_ofReal hz.2⟩) η
  exact ⟨hh.1, hh.2.1, hh.2.2, hs.1, hs.2⟩

end PeriodicAttractiveLogGas.ReferenceDensityChange
