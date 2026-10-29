import DGRHS.Decoupling.RademacherSignMoments

noncomputable section
open MeasureTheory ProbabilityTheory

namespace DGRHS.Decoupling

/-- A nonempty product of distinct-coordinate selector signs has zero mean. -/
lemma integral_selector_sign_prod_eq_zero {n : ℕ} (s : Finset (Fin n))
    (hs : s.Nonempty) :
    ∫ ω, (∏ i ∈ s, rademacherSign (ω i)) ∂selectorLaw (Fin n) = 0 := by
  classical
  obtain ⟨i, hi⟩ := hs.exists_mem
  let X : Fin n → (Fin n → Bool) → ℝ := fun j ω ↦ rademacherSign (ω j)
  have hBool : iIndepFun (fun j (ω : Fin n → Bool) ↦ ω j) (selectorLaw (Fin n)) :=
    iIndepFun_pi (fun _ ↦ aemeasurable_id)
  have hX : iIndepFun X (selectorLaw (Fin n)) :=
    hBool.comp (fun _ ↦ rademacherSign) (fun _ ↦ measurable_of_finite _)
  have hiErase : i ∉ s.erase i := Finset.notMem_erase i s
  have hInd := hX.indepFun_finsetProd_of_notMem
    (fun _ ↦ measurable_of_finite _) (s := s.erase i) (i := i) hiErase
  have hfac := hInd.integral_fun_mul_eq_mul_integral
    ((measurable_of_finite _).aestronglyMeasurable)
    ((measurable_of_finite _).aestronglyMeasurable)
  have hiInt : ∫ ω, X i ω ∂selectorLaw (Fin n) = 0 := by
    dsimp [X]
    change ∫ ω, rademacherSign (ω i) ∂Measure.pi (fun _ : Fin n ↦ fairBool) = 0
    rw [integral_comp_eval (μ := fun _ : Fin n ↦ fairBool)
      (X := fun _ : Fin n ↦ Bool) (i := i) (f := rademacherSign)
      ((measurable_of_finite _).aestronglyMeasurable), integral_rademacherSign]
  have hprod (ω : Fin n → Bool) :
      (∏ j ∈ s, rademacherSign (ω j)) =
        (∏ j ∈ s.erase i, X j ω) * X i ω := by
    rw [← Finset.prod_erase_mul s (fun j ↦ rademacherSign (ω j)) hi]
  calc
    _ = ∫ ω, ((∏ j ∈ s.erase i, X j) ω) * X i ω ∂selectorLaw (Fin n) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω ↦ by
        change (∏ j ∈ s, rademacherSign (ω j)) =
          ((∏ j ∈ s.erase i, X j) ω) * X i ω
        rw [hprod ω]
        simp only [← Finset.prod_apply])
    _ = 0 := by rw [hfac, hiInt]; simp

#print axioms DGRHS.Decoupling.integral_selector_sign_prod_eq_zero

end DGRHS.Decoupling
