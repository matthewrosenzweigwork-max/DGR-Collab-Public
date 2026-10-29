import DGRHS.Gaussian.PeriodicBoundedFourierForm

/-! Actual removal of the first Fourier shell at the quadratic-form level.
The finite shell and its common coefficient are derived from the original
kernel; no residual positivity conclusion is supplied. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Classical BigOperators ComplexConjugate
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicFirstShellFrequency (q : ι × Bool) : PeriodicFrequency ι :=
  if q.2 then periodicFirstFrequency q.1 else -periodicFirstFrequency q.1

def periodicFirstShellFrequencies : Finset (PeriodicFrequency ι) :=
  Finset.univ.image (periodicFirstShellFrequency (ι := ι))

lemma periodicFirstShell_coefficient {k : PeriodicFrequency ι}
    (hk : k ∈ periodicFirstShellFrequencies (ι := ι)) :
    periodicLogFourierCoeff k = ((periodicStabilityThreshold ι)⁻¹ : ℝ) := by
  obtain ⟨⟨i,b⟩,_,rfl⟩ := Finset.mem_image.mp hk
  cases b <;> simp [periodicFirstShellFrequency,periodicLogFourierCoeff_neg,
    periodicLogFourierCoeff_first]

/-- Every actual bounded real test has nonnegative quadratic residual after
subtracting the first-shell spectral form, derived by positive Fourier
summation. Properness and the full Parseval identity are proved upstream. -/
theorem periodicLog_firstShell_form_lower (F : PeriodicTorus ι → ℝ)
    (hF : AEStronglyMeasurable F (periodicHaar ι))
    (B : ℝ) (hb : ∀ x,‖F x‖≤B) :
    (periodicStabilityThreshold ι)⁻¹ *
      ∑ k ∈ periodicFirstShellFrequencies (ι := ι),
        ((UnitAddTorus.mFourierCoeff (fun x => (F x:ℂ)) k).re^2+
         (UnitAddTorus.mFourierCoeff (fun x => (F x:ℂ)) k).im^2) ≤
      ∫ x,F x*(∫ y,F y*periodicLogKernel (x-y) ∂periodicHaar ι) ∂periodicHaar ι := by
  let a : PeriodicFrequency ι → ℝ := fun k => (periodicLogFourierCoeff k).re
  have ha (k : PeriodicFrequency ι) : 0≤a k := by
    dsimp [a,periodicLogFourierCoeff]
    split_ifs
    · simp
    · simp only [Complex.ofReal_re]
      have hC := periodicLogConstant_pos (ι := ι)
      positivity
  have hc (k : PeriodicFrequency ι) :
      UnitAddTorus.mFourierCoeff (fun x => (periodicLogKernel x:ℂ)) k = (a k:ℂ) := by
    rw [periodicLogKernel_fourierCoeff]
    apply Complex.ext
    · change (periodicLogFourierCoeff k).re=(periodicLogFourierCoeff k).re
      rfl
    · change (periodicLogFourierCoeff k).im=0
      exact RCLike.conj_eq_iff_im.mp (conj_periodicLogFourierCoeff k)
  have hs := periodic_bounded_fourier_form_hasSum periodicLogKernel F
    periodicLogKernel_integrable hF B hb a hc
  calc
    _ = ∑ k ∈ periodicFirstShellFrequencies (ι := ι),
        a k*((UnitAddTorus.mFourierCoeff (fun x => (F x:ℂ)) k).re^2+
         (UnitAddTorus.mFourierCoeff (fun x => (F x:ℂ)) k).im^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have he : a k=(periodicStabilityThreshold ι)⁻¹ := by
        dsimp [a]
        rw [periodicFirstShell_coefficient hk]
        simp
      rw [he]
    _ ≤ _ := by
      rw [←hs.tsum_eq]
      exact hs.summable.sum_le_tsum _ (fun k _ =>
        mul_nonneg (ha k) (add_nonneg (sq_nonneg _) (sq_nonneg _)))

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicFirstShell_coefficient
#print axioms DGRHS.Periodic.periodicLog_firstShell_form_lower
#check @DGRHS.Periodic.periodicLog_firstShell_form_lower
