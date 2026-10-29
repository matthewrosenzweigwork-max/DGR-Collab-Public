import DGRHS.Concentration.QuadraticDeletion
import DGRHS.Concentration.ReplacementCopy
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace
namespace DGRHS.Concentration

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {n : ℕ}

def empiricalDirectionalSquare (z : Fin n → H) (u : H) : ℝ :=
  ∑ i, (inner ℝ (z i) u)^2

/-- The actual common-direction quadratic supremum on the closed unit ball. -/
def empiricalQuadratic (z : Fin n → H) : ℝ :=
  sSup (empiricalDirectionalSquare z '' Metric.closedBall (0 : H) 1)

lemma empirical_directional_square_le (z : Fin n → H) {u : H} (hu : ‖u‖ ≤ 1) :
    empiricalDirectionalSquare z u ≤ ∑ i, ‖z i‖^2 := by
  apply Finset.sum_le_sum
  intro i _
  have h : |inner ℝ (z i) u| ≤ ‖z i‖ :=
    (abs_real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (z i)])
  nlinarith [abs_nonneg (inner ℝ (z i) u), norm_nonneg (z i), sq_abs (inner ℝ (z i) u)]

lemma empirical_quadratic_image_nonempty (z : Fin n → H) :
    (empiricalDirectionalSquare z '' Metric.closedBall (0 : H) 1).Nonempty := by
  exact Set.Nonempty.image _ ⟨0, by simp⟩

lemma empirical_quadratic_image_bdd (z : Fin n → H) :
    BddAbove (empiricalDirectionalSquare z '' Metric.closedBall (0 : H) 1) := by
  refine ⟨∑ i, ‖z i‖^2, ?_⟩
  rintro _ ⟨u,hu,rfl⟩
  exact empirical_directional_square_le z (by simpa using hu)

lemma empirical_directional_le_quadratic (z : Fin n → H) {u : H} (hu : ‖u‖ ≤ 1) :
    empiricalDirectionalSquare z u ≤ empiricalQuadratic z := by
  exact le_csSup (empirical_quadratic_image_bdd z) ⟨u,by simpa using hu,rfl⟩

lemma empirical_quadratic_nonneg (z : Fin n → H) : 0 ≤ empiricalQuadratic z := by
  have h := empirical_directional_le_quadratic z (u := 0) (by simp)
  simpa [empiricalDirectionalSquare] using h

lemma empirical_quadratic_le_trace (z : Fin n → H) :
    empiricalQuadratic z ≤ ∑ i, ‖z i‖^2 := by
  exact csSup_le (empirical_quadratic_image_nonempty z) (by
    rintro _ ⟨u,hu,rfl⟩
    exact empirical_directional_square_le z (by simpa using hu))

lemma empirical_quadratic_le_uniform (z : Fin n → H) (B : ℝ)
    (hB : ∀ i, ‖z i‖ ≤ B) : empiricalQuadratic z ≤ (n : ℝ)*B^2 := by
  calc
    _ ≤ ∑ i, ‖z i‖^2 := empirical_quadratic_le_trace z
    _ ≤ ∑ _i : Fin n, B^2 := Finset.sum_le_sum fun i _ ↦ by
      nlinarith [hB i,norm_nonneg (z i)]
    _ = _ := by simp

lemma empirical_directional_delete (z : Fin n → H) (i : Fin n) (u : H) :
    empiricalDirectionalSquare z u =
      empiricalDirectionalSquare (Function.update z i 0) u + (inner ℝ (z i) u)^2 := by
  classical
  have he : ∀ j, (inner ℝ (z j) u)^2 =
      (inner ℝ ((Function.update z i 0) j) u)^2 +
        if j=i then (inner ℝ (z i) u)^2 else 0 := by
    intro j
    by_cases h : j=i <;> simp [h,Function.update]
  unfold empiricalDirectionalSquare
  calc
    _ = ∑ j, ((inner ℝ ((Function.update z i 0) j) u)^2 +
        if j=i then (inner ℝ (z i) u)^2 else 0) := Finset.sum_congr rfl fun j _ ↦ he j
    _ = _ := by simp [Finset.sum_add_distrib]

lemma empirical_quadratic_delete_le (z : Fin n → H) (i : Fin n) :
    empiricalQuadratic (Function.update z i 0) ≤ empiricalQuadratic z := by
  apply csSup_le (empirical_quadratic_image_nonempty _)
  rintro _ ⟨u,hu,rfl⟩
  have h := empirical_directional_delete z i u
  exact (by linarith [sq_nonneg (inner ℝ (z i) u)] :
    empiricalDirectionalSquare (Function.update z i 0) u ≤ empiricalDirectionalSquare z u).trans
      (empirical_directional_le_quadratic z (by simpa using hu))

lemma empirical_quadratic_delete_difference (z : Fin n → H) (i : Fin n) :
    0 ≤ empiricalQuadratic z-empiricalQuadratic (Function.update z i 0) ∧
      empiricalQuadratic z-empiricalQuadratic (Function.update z i 0) ≤ ‖z i‖^2 := by
  refine ⟨sub_nonneg.mpr (empirical_quadratic_delete_le z i), ?_⟩
  have hh : empiricalQuadratic z ≤ empiricalQuadratic (Function.update z i 0)+‖z i‖^2 := by
    apply csSup_le (empirical_quadratic_image_nonempty z)
    rintro _ ⟨u,hu,rfl⟩
    have hu' : ‖u‖ ≤ 1 := by simpa using hu
    rw [empirical_directional_delete z i u]
    have ha := empirical_directional_le_quadratic (Function.update z i 0) hu'
    have hb : (inner ℝ (z i) u)^2 ≤ ‖z i‖^2 := by
      have h := (abs_real_inner_le_norm (z i) u).trans
        (by nlinarith [norm_nonneg (z i)] : ‖z i‖*‖u‖ ≤ ‖z i‖)
      nlinarith [abs_nonneg (inner ℝ (z i) u), norm_nonneg (z i), sq_abs (inner ℝ (z i) u)]
    exact add_le_add ha hb
  linarith

lemma continuous_empirical_quadratic [FiniteDimensional ℝ H] :
    Continuous (empiricalQuadratic (H := H) (n := n)) := by
  have hf : Continuous (fun p : (Fin n → H) × H ↦ empiricalDirectionalSquare p.1 p.2) := by
    unfold empiricalDirectionalSquare
    fun_prop
  exact (isCompact_closedBall (0 : H) 1).continuous_sSup hf

lemma empirical_quadratic_attained [FiniteDimensional ℝ H] (z : Fin n → H) :
    ∃ u : H, ‖u‖ ≤ 1 ∧ empiricalQuadratic z = empiricalDirectionalSquare z u := by
  obtain ⟨u,hu,hv⟩ := (isCompact_closedBall (0 : H) 1).exists_sSup_image_eq
    (show (Metric.closedBall (0 : H) 1).Nonempty from ⟨0,by simp⟩)
    (show Continuous (empiricalDirectionalSquare z) from by
      unfold empiricalDirectionalSquare
      fun_prop).continuousOn
  exact ⟨u,by simpa using hu,hv⟩

lemma empirical_quadratic_deletion_sum [FiniteDimensional ℝ H] (z : Fin n → H) :
    (∑ i : Fin n, (empiricalQuadratic z-empiricalQuadratic (Function.update z i 0))) ≤
      empiricalQuadratic z := by
  obtain ⟨u,hu,hv⟩ := empirical_quadratic_attained z
  have hi : ∀ i, empiricalQuadratic z-empiricalQuadratic (Function.update z i 0) ≤
      (inner ℝ (z i) u)^2 := by
    intro i
    have h := empirical_directional_le_quadratic (Function.update z i 0) hu
    have he := empirical_directional_delete z i u
    linarith
  calc
    _ ≤ ∑ i, (inner ℝ (z i) u)^2 := Finset.sum_le_sum fun i _ ↦ hi i
    _ = _ := hv.symm

def empiricalQuadraticOnProduct {Ω : Type*} (Z : Fin n → Ω → H) (ω : Fin n → Ω) : ℝ :=
  empiricalQuadratic (fun i ↦ Z i (ω i))

def empiricalQuadraticDeletion {Ω : Type*} (Z : Fin n → Ω → H)
    (i : Fin n) (ω : Fin n → Ω) : ℝ :=
  empiricalQuadratic (Function.update (fun j ↦ Z j (ω j)) i 0)

lemma empirical_quadratic_deletion_invariant {Ω : Type*} (Z : Fin n → Ω → H)
    (i : Fin n) (ω : Fin n → Ω) (x : Ω) :
    empiricalQuadraticDeletion Z i (Function.update ω i x) = empiricalQuadraticDeletion Z i ω := by
  unfold empiricalQuadraticDeletion
  congr 1
  funext j
  by_cases h : j=i <;> simp [Function.update,h]

variable [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

omit [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] in
lemma empirical_product_tuple_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : Fin n → Ω → H) (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i)) :
    AEMeasurable (fun ω : Fin n → Ω ↦ fun i ↦ Z i (ω i)) (Measure.pi μ) := by
  exact aemeasurable_pi_iff.mpr fun i ↦
    ((hZ i).comp_quasiMeasurePreserving
      (measurePreserving_pi_coordinate μ i).quasiMeasurePreserving).aemeasurable

lemma empirical_quadratic_product_aestronglyMeasurable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : Fin n → Ω → H) (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i)) :
    AEStronglyMeasurable (empiricalQuadraticOnProduct Z) (Measure.pi μ) := by
  exact (continuous_empirical_quadratic.measurable.comp_aemeasurable
    (empirical_product_tuple_aemeasurable μ Z hZ)).aestronglyMeasurable

lemma empirical_quadratic_deletion_aestronglyMeasurable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : Fin n → Ω → H) (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i)) (i : Fin n) :
    AEStronglyMeasurable (empiricalQuadraticDeletion Z i) (Measure.pi μ) := by
  have hc : Continuous (fun z : Fin n → H ↦ Function.update z i 0) := by fun_prop
  exact ((continuous_empirical_quadratic.comp hc).measurable.comp_aemeasurable
    (empirical_product_tuple_aemeasurable μ Z hZ)).aestronglyMeasurable

/-- The actual empirical quadratic supremum satisfies the self-bounding entropy inequality. -/
theorem empirical_quadratic_entropy {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : Fin n → Ω → H) (B : ℝ)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i))
    (hB : ∀ i, ∀ᵐ x ∂μ i, ‖Z i x‖ ≤ B) (lam : ℝ) (hlam : 0 ≤ lam) :
    functionalEntropy (Measure.pi μ) (fun ω ↦ Real.exp (lam*empiricalQuadraticOnProduct Z ω)) ≤
      (lam^2*B^2/2)*(∫ ω, Real.exp (lam*empiricalQuadraticOnProduct Z ω)*
        empiricalQuadraticOnProduct Z ω ∂Measure.pi μ) := by
  have hj : ∀ᵐ ω ∂Measure.pi μ, ∀ i, ‖Z i (ω i)‖ ≤ B := ae_all_iff.mpr fun i ↦
    (measurePreserving_pi_coordinate μ i).quasiMeasurePreserving.ae (hB i)
  have hBound : ∀ᵐ ω ∂Measure.pi μ, |empiricalQuadraticOnProduct Z ω| ≤ (n : ℝ)*B^2 := by
    filter_upwards [hj] with ω hω
    unfold empiricalQuadraticOnProduct
    rw [abs_of_nonneg (empirical_quadratic_nonneg _)]
    exact empirical_quadratic_le_uniform _ B hω
  have hDBound : ∀ i, ∀ᵐ ω ∂Measure.pi μ,
      |empiricalQuadraticDeletion Z i ω| ≤ (n : ℝ)*B^2 := by
    intro i
    filter_upwards [hj] with ω hω
    unfold empiricalQuadraticDeletion
    rw [abs_of_nonneg (empirical_quadratic_nonneg _)]
    exact (empirical_quadratic_delete_le _ i).trans (empirical_quadratic_le_uniform _ B hω)
  have hDiff : ∀ i, ∀ᵐ ω ∂Measure.pi μ,
      0 ≤ empiricalQuadraticOnProduct Z ω-empiricalQuadraticDeletion Z i ω ∧
        empiricalQuadraticOnProduct Z ω-empiricalQuadraticDeletion Z i ω ≤ B^2 := by
    intro i
    filter_upwards [hj] with ω hω
    have h := empirical_quadratic_delete_difference (fun j ↦ Z j (ω j)) i
    refine ⟨h.1,h.2.trans ?_⟩
    nlinarith [hω i,norm_nonneg (Z i (ω i))]
  exact finite_product_self_bounding_deletion_entropy n μ (empiricalQuadraticOnProduct Z)
    (empiricalQuadraticDeletion Z) ((n : ℝ)*B^2) (fun _ ↦ (n : ℝ)*B^2) (B^2)
    (empirical_quadratic_product_aestronglyMeasurable μ Z hZ)
    (empirical_quadratic_deletion_aestronglyMeasurable μ Z hZ) hBound hDBound
    (empirical_quadratic_deletion_invariant Z) (sq_nonneg B) hDiff
    (Filter.Eventually.of_forall fun ω ↦ empirical_quadratic_deletion_sum _) lam hlam

#print axioms DGRHS.Concentration.empirical_quadratic_delete_difference
#print axioms DGRHS.Concentration.empirical_quadratic_deletion_sum
#print axioms DGRHS.Concentration.empirical_quadratic_product_aestronglyMeasurable
#print axioms DGRHS.Concentration.empirical_quadratic_entropy
#check @DGRHS.Concentration.empirical_quadratic_entropy

end DGRHS.Concentration
