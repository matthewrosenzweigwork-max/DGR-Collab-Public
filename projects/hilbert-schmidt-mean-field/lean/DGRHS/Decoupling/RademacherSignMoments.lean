import DGRHS.Decoupling.Selector

noncomputable section
open MeasureTheory ProbabilityTheory

namespace DGRHS.Decoupling

/-- The sign associated with a fair Bool selector. -/
def rademacherSign (b : Bool) : ℝ := if b then 1 else -1

lemma integral_rademacherSign :
    ∫ b, rademacherSign b ∂fairBool = 0 := by
  unfold fairBool
  rw [PMF.integral_eq_sum]
  norm_num [rademacherSign, PMF.uniformOfFintype_apply, Fintype.sum_bool]

lemma integral_rademacherSign_sq :
    ∫ b, rademacherSign b ^ 2 ∂fairBool = 1 := by
  unfold fairBool
  rw [PMF.integral_eq_sum]
  norm_num [rademacherSign, PMF.uniformOfFintype_apply, Fintype.sum_bool]

lemma integral_rademacherSign_fourth :
    ∫ b, rademacherSign b ^ 4 ∂fairBool = 1 := by
  unfold fairBool
  rw [PMF.integral_eq_sum]
  norm_num [rademacherSign, PMF.uniformOfFintype_apply, Fintype.sum_bool]

lemma rademacherSign_sq (b : Bool) : rademacherSign b ^ 2 = 1 := by
  cases b <;> norm_num [rademacherSign]

lemma rademacherSign_fourth (b : Bool) : rademacherSign b ^ 4 = 1 := by
  cases b <;> norm_num [rademacherSign]

/-- Distinct selector coordinates are orthogonal in `L²`. -/
lemma integral_selector_rademacherSign_mul {ι : Type*} [Fintype ι]
    (i j : ι) (hij : i ≠ j) :
    ∫ s, rademacherSign (s i) * rademacherSign (s j) ∂selectorLaw ι = 0 := by
  have hi : iIndepFun (fun i (s : ι → Bool) ↦ s i) (selectorLaw ι) :=
    iIndepFun_pi (fun _ ↦ aemeasurable_id)
  have h := (hi.indepFun hij).comp (measurable_of_finite rademacherSign)
    (measurable_of_finite rademacherSign)
  have he := h.integral_fun_mul_eq_mul_integral
    ((measurable_of_finite _).aestronglyMeasurable)
    ((measurable_of_finite _).aestronglyMeasurable)
  simp only [Function.comp_def] at he
  rw [he]
  change (∫ s, rademacherSign (s i) ∂Measure.pi (fun _ : ι ↦ fairBool)) *
      (∫ s, rademacherSign (s j) ∂Measure.pi (fun _ : ι ↦ fairBool)) = 0
  rw [integral_comp_eval (μ := fun _ : ι ↦ fairBool) (X := fun _ : ι ↦ Bool)
      (i := i) (f := rademacherSign) ((measurable_of_finite _).aestronglyMeasurable),
    integral_comp_eval (μ := fun _ : ι ↦ fairBool) (X := fun _ : ι ↦ Bool)
      (i := j) (f := rademacherSign) ((measurable_of_finite _).aestronglyMeasurable),
    integral_rademacherSign]
  norm_num

/-- A Walsh character supported on two distinct coordinates has unit square. -/
lemma selector_pair_rademacherSign_mul_sq {ι : Type*} (s : ι → Bool) (i j : ι) :
    (rademacherSign (s i) * rademacherSign (s j)) ^ 2 = 1 := by
  rw [mul_pow, rademacherSign_sq, rademacherSign_sq, one_mul]

#print axioms DGRHS.Decoupling.integral_rademacherSign
#print axioms DGRHS.Decoupling.integral_rademacherSign_sq
#print axioms DGRHS.Decoupling.integral_rademacherSign_fourth
#print axioms DGRHS.Decoupling.integral_selector_rademacherSign_mul

end DGRHS.Decoupling
