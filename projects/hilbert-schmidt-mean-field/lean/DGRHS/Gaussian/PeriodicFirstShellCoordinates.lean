import DGRHS.Gaussian.PeriodicFirstShellForm

/-! Actual first-shell frequency multiplicity and real coordinate reduction.
The source has two real modes per coordinate; no spectral multiplicity,
orthogonality or residual form bound is supplied as a hypothesis. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicFirstShellFrequency_injective :
    Function.Injective (periodicFirstShellFrequency (ι := ι)) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ h
  cases b <;> cases c
  · have hij : i=j := by
      by_contra hn
      have he := congrFun h i
      simp [periodicFirstShellFrequency,periodicFirstFrequency,Pi.single_apply,hn,Ne.symm hn] at he
    subst j
    rfl
  · have he := congrFun h i
    by_cases hij : i=j
    · subst j
      simp [periodicFirstShellFrequency,periodicFirstFrequency,Pi.single_apply] at he
    · simp [periodicFirstShellFrequency,periodicFirstFrequency,Pi.single_apply,hij,Ne.symm hij] at he
  · have he := congrFun h i
    by_cases hij : i=j
    · subst j
      simp [periodicFirstShellFrequency,periodicFirstFrequency,Pi.single_apply] at he
    · simp [periodicFirstShellFrequency,periodicFirstFrequency,Pi.single_apply,hij,Ne.symm hij] at he
  · have hij : i=j := by
      by_contra hn
      have he := congrFun h i
      simp [periodicFirstShellFrequency,periodicFirstFrequency,Pi.single_apply,hn,Ne.symm hn] at he
    subst j
    rfl

lemma periodic_real_fourierCoeff_neg (F : PeriodicTorus ι → ℝ) (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (fun x => (F x:ℂ)) (-k) =
      conj (UnitAddTorus.mFourierCoeff (fun x => (F x:ℂ)) k) := by
  have h := periodic_mFourierCoeff_conj (fun x => (F x:ℂ)) (-k)
  simpa only [Complex.conj_ofReal,neg_neg] using h

lemma periodicFirstShell_real_form_sum (F : PeriodicTorus ι → ℝ) :
    (∑ k ∈ periodicFirstShellFrequencies (ι := ι),
      ((UnitAddTorus.mFourierCoeff (fun x => (F x:ℂ)) k).re^2+
       (UnitAddTorus.mFourierCoeff (fun x => (F x:ℂ)) k).im^2)) =
    2*∑ i : ι,((UnitAddTorus.mFourierCoeff (fun x => (F x:ℂ)) (periodicFirstFrequency i)).re^2+
      (UnitAddTorus.mFourierCoeff (fun x => (F x:ℂ)) (periodicFirstFrequency i)).im^2) := by
  unfold periodicFirstShellFrequencies
  rw [Finset.sum_image (fun a _ b _ h => periodicFirstShellFrequency_injective h)]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,periodicFirstShellFrequency,Bool.false_eq_true,↓reduceIte,
    periodic_real_fourierCoeff_neg,Complex.conj_re,Complex.conj_im,neg_sq]
  rw [Finset.sum_add_distrib]
  ring

/-- The exact source two-real-modes-per-coordinate form is dominated by the
full actual logarithmic kernel for every bounded measurable real test. -/
theorem periodicLog_coordinate_firstShell_form_lower (F : PeriodicTorus ι → ℝ)
    (hF : AEStronglyMeasurable F (periodicHaar ι))
    (B : ℝ) (hb : ∀ x,‖F x‖≤B) :
    (2*(periodicStabilityThreshold ι)⁻¹)*
      ∑ i : ι,((UnitAddTorus.mFourierCoeff (fun x => (F x:ℂ)) (periodicFirstFrequency i)).re^2+
        (UnitAddTorus.mFourierCoeff (fun x => (F x:ℂ)) (periodicFirstFrequency i)).im^2) ≤
    ∫ x,F x*(∫ y,F y*periodicLogKernel (x-y) ∂periodicHaar ι) ∂periodicHaar ι := by
  have h := periodicLog_firstShell_form_lower F hF B hb
  rw [periodicFirstShell_real_form_sum] at h
  convert h using 1 <;> ring

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicFirstShellFrequency_injective
#print axioms DGRHS.Periodic.periodic_real_fourierCoeff_neg
#print axioms DGRHS.Periodic.periodicFirstShell_real_form_sum
#print axioms DGRHS.Periodic.periodicLog_coordinate_firstShell_form_lower
#check @DGRHS.Periodic.periodicLog_coordinate_firstShell_form_lower
