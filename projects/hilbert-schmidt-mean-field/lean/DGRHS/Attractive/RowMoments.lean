import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.LpSpace.Basic

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Attractive

/-- Finite Lebesgue row moments; the supremum is outside integration. -/
structure RowFactorialMoments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω × Ω → ℝ) (C : ℝ) : Prop where
  nonneg : 0 ≤ C
  proper : ∀ p : ℕ, 1 ≤ p → ∀ y, Integrable (fun x ↦ |h (x,y)|^p) μ
  bound : ∀ p : ℕ, 1 ≤ p → ∀ y,
    (∫ x, |h (x,y)|^p ∂μ) ≤ C^p * (p.factorial : ℝ)

/-- Nonnegativity is derived from the source's first absolute moment bound. -/
lemma rowFactorialMoments_of_proper_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : Ω × Ω → ℝ) (C : ℝ)
    (hi : ∀ p : ℕ, 1 ≤ p → ∀ y, Integrable (fun x ↦ |h (x,y)|^p) μ)
    (hb : ∀ p : ℕ, 1 ≤ p → ∀ y,
      (∫ x, |h (x,y)|^p ∂μ) ≤ C^p * (p.factorial : ℝ)) :
    RowFactorialMoments μ h C := by
  refine ⟨?_,hi,hb⟩
  by_contra hC
  have hy : ∀ y : Ω, False := fun y ↦ by
    have hnn : 0 ≤ ∫ x, |h (x,y)| ∂μ := integral_nonneg fun x ↦ abs_nonneg _
    have hle := hb 1 (by omega) y
    simp only [pow_one,Nat.factorial_one,Nat.cast_one,mul_one] at hle
    exact hC (hnn.trans hle)
  have he : (Set.univ : Set Ω) = ∅ := by
    ext y
    constructor
    · intro _
      exact hy y
    · intro hf
      exact hf.elim
  have hp : μ Set.univ = 1 := measure_univ
  rw [he,measure_empty] at hp
  exact zero_ne_one hp

/-- Finite extended-valued moment bounds construct proper rows, so an improper
real integral cannot satisfy this source-facing version accidentally. -/
lemma rowFactorialMoments_of_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ p : ℕ, 1 ≤ p → ∀ y,
      (∫⁻ x, ENNReal.ofReal (|h (x,y)|^p) ∂μ) ≤ ENNReal.ofReal (C^p * (p.factorial : ℝ))) :
    RowFactorialMoments μ h C := by
  have hi (p : ℕ) (hp : 1 ≤ p) (y : Ω) :
      Integrable (fun x ↦ |h (x,y)|^p) μ := by
    have hm : AEStronglyMeasurable (fun x ↦ |h (x,y)|^p) μ :=
      ((continuous_pow p).measurable.comp
        (continuous_abs.measurable.comp (hh.comp (measurable_id.prodMk measurable_const)))).aestronglyMeasurable
    have hn : 0 ≤ᵐ[μ] (fun x ↦ |h (x,y)|^p) :=
      Filter.Eventually.of_forall fun x ↦ pow_nonneg (abs_nonneg _) _
    exact ⟨hm,(hasFiniteIntegral_iff_ofReal hn).mpr ((hb p hp y).trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hC,hi,?_⟩
  intro p hp y
  have hn : 0 ≤ᵐ[μ] (fun x ↦ |h (x,y)|^p) :=
    Filter.Eventually.of_forall fun x ↦ pow_nonneg (abs_nonneg _) _
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hb p hp y)
  rw [← ofReal_integral_eq_lintegral_ofReal (hi p hp y) hn] at hreal
  have hnn : 0 ≤ ∫ x, |h (x,y)|^p ∂μ :=
    integral_nonneg fun x ↦ pow_nonneg (abs_nonneg _) _
  rw [ENNReal.toReal_ofReal hnn,
    ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg hC p) (Nat.cast_nonneg _))] at hreal
  exact hreal

/-- Actual joint high moments derived from proper uniformly bounded rows. -/
lemma joint_abs_power_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : Ω × Ω → ℝ)
    (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (p : ℕ) (hp : 1 ≤ p) :
    Integrable (fun z ↦ |h z|^p) (μ.prod μ) := by
  have hm : StronglyMeasurable (fun z ↦ |h z|^p) :=
    ((continuous_pow p).measurable.comp (continuous_abs.measurable.comp hh)).stronglyMeasurable
  apply (integrable_prod_iff' hm.aestronglyMeasurable).2
  refine ⟨Filter.Eventually.of_forall (hC.proper p hp), ?_⟩
  apply (integrable_const (C^p * (p.factorial : ℝ))).mono'
    hm.norm.integral_prod_left'.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y ↦ by
    have hnn : 0 ≤ ∫ x, ‖|h (x,y)|^p‖ ∂μ := integral_nonneg fun x ↦ norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using hC.bound p hp y

lemma joint_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : Ω × Ω → ℝ)
    (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (p : ℕ) (hp : 1 ≤ p) : MemLp h (p : ℝ≥0∞) (μ.prod μ) := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hp)
  apply (memLp_norm_rpow_iff (p := (p : ℝ≥0∞)) hh.aestronglyMeasurable
    hp0 (ENNReal.natCast_ne_top p)).mp
  rw [ENNReal.div_self hp0 (ENNReal.natCast_ne_top p),memLp_one_iff_integrable]
  simpa only [Real.norm_eq_abs,ENNReal.toReal_natCast,Real.rpow_natCast] using
    joint_abs_power_integrable μ h hh C hC p hp

/-- Coordinates of the two independent arrays have the actual product law,
including when their numeric labels agree. -/
lemma independent_array_pair_preserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (i j : Fin n) :
    MeasurePreserving (fun z : (Fin n → Ω) × (Fin n → Ω) ↦ (z.1 i,z.2 j))
      ((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ μ)))
      (μ.prod μ) :=
  (measurePreserving_eval (fun _ : Fin n ↦ μ) i).prod
    (measurePreserving_eval (fun _ : Fin n ↦ μ) j)

lemma independent_array_term_abs_power_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : Ω × Ω → ℝ)
    (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (p : ℕ) (hp : 1 ≤ p) {n : ℕ} (i j : Fin n) :
    Integrable (fun z : (Fin n → Ω) × (Fin n → Ω) ↦ |h (z.1 i,z.2 j)|^p)
      ((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ μ))) :=
  (independent_array_pair_preserving μ i j).integrable_comp_of_integrable
    (joint_abs_power_integrable μ h hh C hC p hp)

/-- Symmetry transports the exact proper row hypothesis to the other side. -/
lemma symmetric_row_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω × Ω → ℝ) (C : ℝ)
    (hC : RowFactorialMoments μ h C) (hs : ∀ x y, h (x,y) = h (y,x)) :
    RowFactorialMoments μ (fun z ↦ h z.swap) C := by
  convert hC using 1
  funext z
  exact hs z.2 z.1

#check @DGRHS.Attractive.joint_abs_power_integrable
#print axioms DGRHS.Attractive.joint_abs_power_integrable
#check @DGRHS.Attractive.independent_array_term_abs_power_integrable
#print axioms DGRHS.Attractive.independent_array_term_abs_power_integrable
#check @DGRHS.Attractive.joint_memLp
#print axioms DGRHS.Attractive.joint_memLp
#print axioms DGRHS.Attractive.rowFactorialMoments_of_proper_bound
#print axioms DGRHS.Attractive.rowFactorialMoments_of_lintegral
end DGRHS.Attractive
