import FullLabeledLSI.Examples.E01h3_Trig
import FullLabeledLSI.Examples.E01h2_UintPoly

/-!
# Lane D, Task B3 (part 1): termwise integration of cosine/sine series against signed measures

For a pair `(α, β)` of finite measures (the signed measure `σ = α - β`) and a base point `x`:
`cI x n = σ(z ↦ cos(2π n (z - x)))`, `sI x n = σ(z ↦ sin(2π n (z - x)))`.
If `g = ∑_m a_m cos(4π m ·) + b_m sin(4π m ·)` (absolutely summable coefficients), then
`g * σ = ∑_m (a_m c_m - b_m d_m) cos(4π m (· - x)) + (a_m d_m + b_m c_m) sin(4π m (· - x))`
and `σ(g * σ) = ∑_m a_m (c_m² + d_m²)`.
-/

open MeasureTheory Complex UnitAddTorus Filter Topology
open scoped Real ComplexConjugate ContDiff ENNReal

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

section

variable (α β : Measure (Torus 1)) [IsFiniteMeasure α] [IsFiniteMeasure β] (x : Torus 1)

/-- `σ(z ↦ cos(2π n (z - x)))`. -/
noncomputable def cI (n : ℤ) : ℝ := intS (fun z => cm n (z - x)) α β

/-- `σ(z ↦ sin(2π n (z - x)))`. -/
noncomputable def sI (n : ℤ) : ℝ := intS (fun z => sm n (z - x)) α β

theorem cont_cm_sub (n : ℤ) : Continuous (fun z : Torus 1 => cm n (z - x)) :=
  (continuous_cm n).comp (continuous_id.sub continuous_const)

theorem cont_sm_sub (n : ℤ) : Continuous (fun z : Torus 1 => sm n (z - x)) :=
  (continuous_sm n).comp (continuous_id.sub continuous_const)

theorem cI_neg (n : ℤ) : cI α β x (-n) = cI α β x n := by
  unfold cI; simp only [cm_neg_idx]

theorem sI_neg (n : ℤ) : sI α β x (-n) = - sI α β x n := by
  unfold sI
  simp only [sm_neg_idx]
  have := (linC_intS α β).smul (-1) (fun z => sm n (z - x))
  simpa using this

theorem abs_intS_le {f : Torus 1 → ℝ} {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    |intS f α β| ≤ M * ((α Set.univ).toReal + (β Set.univ).toReal) := by
  unfold intS
  have h1 : ‖∫ x, f x ∂α‖ ≤ M * (α Set.univ).toReal :=
    norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => by simpa using hM x)
  have h2 : ‖∫ x, f x ∂β‖ ≤ M * (β Set.univ).toReal :=
    norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => by simpa using hM x)
  rw [Real.norm_eq_abs] at h1 h2
  calc |∫ x, f x ∂α - ∫ x, f x ∂β| ≤ |∫ x, f x ∂α| + |∫ x, f x ∂β| := abs_sub _ _
    _ ≤ _ := by nlinarith

/-- A uniform bound for the mass of `σ`. -/
noncomputable def mass : ℝ := (α Set.univ).toReal + (β Set.univ).toReal

theorem mass_nonneg : 0 ≤ mass α β := by unfold mass; positivity

theorem abs_cI_le (n : ℤ) : |cI α β x n| ≤ mass α β := by
  have := abs_intS_le α β (f := fun z => cm n (z - x)) (M := 1) (fun z => abs_cm_le n _)
  simpa [cI, mass] using this

theorem abs_sI_le (n : ℤ) : |sI α β x n| ≤ mass α β := by
  have := abs_intS_le α β (f := fun z => sm n (z - x)) (M := 1) (fun z => abs_sm_le n _)
  simpa [sI, mass] using this

theorem cI_zero (hm : α Set.univ = β Set.univ) : cI α β x 0 = 0 := by
  unfold cI intS
  simp only [cm_zero_idx, integral_const, smul_eq_mul, mul_one, Measure.real, hm, sub_self]

theorem sI_zero : sI α β x 0 = 0 := by
  unfold sI intS
  simp only [sm_zero_idx, integral_const, smul_eq_mul, mul_zero, sub_self]

/-- Convolving a mode with `σ`. -/
theorem intS_cm_conv (n : ℤ) (z : Torus 1) :
    intS (fun y => cm n (z - y)) α β = cm n (z - x) * cI α β x n + sm n (z - x) * sI α β x n := by
  have h : ∀ y : Torus 1, cm n (z - y) =
      cm n (z - x) * cm n (y - x) + sm n (z - x) * sm n (y - x) := by
    intro y
    rw [show z - y = (z - x) - (y - x) by abel, cm_sub]
  have e : (fun y : Torus 1 => cm n (z - y)) = fun y =>
      cm n (z - x) * cm n (y - x) + sm n (z - x) * sm n (y - x) := funext h
  rw [e]
  have := (linC_intS α β).add (fun y => cm n (z - x) * cm n (y - x))
    (fun y => sm n (z - x) * sm n (y - x)) (continuous_const.mul (cont_cm_sub x n))
    (continuous_const.mul (cont_sm_sub x n))
  rw [this, (linC_intS α β).smul, (linC_intS α β).smul]
  rfl

theorem intS_sm_conv (n : ℤ) (z : Torus 1) :
    intS (fun y => sm n (z - y)) α β = sm n (z - x) * cI α β x n - cm n (z - x) * sI α β x n := by
  have h : ∀ y : Torus 1, sm n (z - y) =
      sm n (z - x) * cm n (y - x) + (-(cm n (z - x))) * sm n (y - x) := by
    intro y
    rw [show z - y = (z - x) - (y - x) by abel, sm_sub]; ring
  have e : (fun y : Torus 1 => sm n (z - y)) = fun y =>
      sm n (z - x) * cm n (y - x) + (-(cm n (z - x))) * sm n (y - x) := funext h
  rw [e]
  have := (linC_intS α β).add (fun y => sm n (z - x) * cm n (y - x))
    (fun y => (-(cm n (z - x))) * sm n (y - x)) (continuous_const.mul (cont_cm_sub x n))
    (continuous_const.mul (cont_sm_sub x n))
  rw [this, (linC_intS α β).smul, (linC_intS α β).smul]
  unfold cI sI
  ring

/-- Rotation invariance of `c² + d²`. -/
theorem cI_sq_add_sI_sq (n : ℤ) :
    cI α β x n ^ 2 + sI α β x n ^ 2 = cI α β 0 n ^ 2 + sI α β 0 n ^ 2 := by
  have h1 : cI α β x n = cI α β 0 n * cm n x + sI α β 0 n * sm n x := by
    unfold cI sI
    have h : ∀ z : Torus 1, cm n (z - x) = cm n x * cm n (z - 0) + sm n x * sm n (z - 0) := by
      intro z; rw [sub_zero, cm_sub]; ring
    have e : (fun z : Torus 1 => cm n (z - x)) = fun z =>
        cm n x * cm n (z - 0) + sm n x * sm n (z - 0) := funext h
    rw [e]
    have := (linC_intS α β).add (fun z => cm n x * cm n (z - 0)) (fun z => sm n x * sm n (z - 0))
      (continuous_const.mul (cont_cm_sub 0 n)) (continuous_const.mul (cont_sm_sub 0 n))
    rw [this, (linC_intS α β).smul, (linC_intS α β).smul]
    ring
  have h2 : sI α β x n = sI α β 0 n * cm n x - cI α β 0 n * sm n x := by
    unfold cI sI
    have h : ∀ z : Torus 1, sm n (z - x) = cm n x * sm n (z - 0) + (-(sm n x)) * cm n (z - 0) := by
      intro z; rw [sub_zero, sm_sub]; ring
    have e : (fun z : Torus 1 => sm n (z - x)) = fun z =>
        cm n x * sm n (z - 0) + (-(sm n x)) * cm n (z - 0) := funext h
    rw [e]
    have := (linC_intS α β).add (fun z => cm n x * sm n (z - 0)) (fun z => (-(sm n x)) * cm n (z - 0))
      (continuous_const.mul (cont_sm_sub 0 n)) (continuous_const.mul (cont_cm_sub 0 n))
    rw [this, (linC_intS α β).smul, (linC_intS α β).smul]
    ring
  rw [h1, h2]
  have h3 : cm n x ^ 2 + sm n x ^ 2 = 1 := by
    obtain ⟨t, rfl⟩ := exists_lift1 x
    rw [cm_lift1, sm_lift1]; exact Real.cos_sq_add_sin_sq _
  linear_combination (cI α β 0 n ^ 2 + sI α β 0 n ^ 2) * h3

end

section tsum

variable (α β : Measure (Torus 1)) [IsFiniteMeasure α] [IsFiniteMeasure β]

/-- Termwise integration of a series of continuous functions against `σ = α - β`. -/
theorem intS_tsum {ι : Type*} [Countable ι] {f : ι → Torus 1 → ℝ} (hf : ∀ i, Continuous (f i))
    {b : ι → ℝ} (hb : Summable b) (hfb : ∀ i x, |f i x| ≤ b i) :
    HasSum (fun i => intS (f i) α β) (intS (fun x => ∑' i, f i x) α β) := by
  have hnorm : ∀ (μ : Measure (Torus 1)) [IsFiniteMeasure μ],
      HasSum (fun i => ∫ x, f i x ∂μ) (∫ x, ∑' i, f i x ∂μ) := by
    intro μ _
    refine hasSum_integral_of_summable_integral_norm (fun i => integrable_of_cont (hf i) μ) ?_
    have hnn : ∀ i, 0 ≤ ∫ x, ‖f i x‖ ∂μ := fun i => integral_nonneg (fun x => norm_nonneg (f i x))
    refine Summable.of_nonneg_of_le hnn (fun i => ?_) (hb.mul_right (μ Set.univ).toReal)
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => ‖f i x‖) (C := b i)
      (Eventually.of_forall fun x => by simpa using hfb i x)
    exact (Real.le_norm_self _).trans this
  exact (hnorm α).sub (hnorm β)

theorem continuous_tsum_fun {ι : Type*} {f : ι → Torus 1 → ℝ} (hf : ∀ i, Continuous (f i))
    {b : ι → ℝ} (hb : Summable b) (hfb : ∀ i x, |f i x| ≤ b i) :
    Continuous (fun x => ∑' i, f i x) :=
  continuous_tsum hf hb (fun i x => by simpa using hfb i x)

end tsum

end SharpLSI.FL.Ex.LaneD
