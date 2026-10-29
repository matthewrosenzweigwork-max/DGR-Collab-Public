import DGRHS.Gaussian.PeriodicFirstShellCoordinates

/-! Actual cosine-sine first-shell kernel and proper bounded-test residual.
The kernel is constructed from the genuine Fourier characters, with its
source coefficient; residual positivity is derived from full Parseval. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ComplexConjugate
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodic_first_character (i : ι) (x : PeriodicTorus ι) :
    UnitAddTorus.mFourier (periodicFirstFrequency i) x = fourier 1 (x i) := by
  simp [UnitAddTorus.mFourier,periodicFirstFrequency,Pi.single_apply]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

def periodicFirstShellMode (q : ι × Bool) (x : PeriodicTorus ι) : ℝ :=
  if q.2 then (fourier 1 (x q.1)).im else (fourier 1 (x q.1)).re

lemma periodicFirstShellMode_continuous (q : ι × Bool) :
    Continuous (periodicFirstShellMode q) := by
  cases q with | mk i b => cases b <;> unfold periodicFirstShellMode <;> simp only [Bool.false_eq_true,↓reduceIte] <;> fun_prop

lemma periodicFirstShellMode_abs_le_one (q : ι × Bool) (x : PeriodicTorus ι) :
    |periodicFirstShellMode q x| ≤ 1 := by
  have h := Complex.abs_re_le_norm (fourier 1 (x q.1))
  have h' := Complex.abs_im_le_norm (fourier 1 (x q.1))
  have hn : ‖fourier 1 (x q.1)‖=1 := by simp [fourier_apply]
  cases q with
  | mk i b =>
    cases b
    · simpa only [periodicFirstShellMode,Prod.fst,Prod.snd,Bool.false_eq_true,↓reduceIte] using h.trans_eq hn
    · simpa only [periodicFirstShellMode,Prod.fst,Prod.snd,↓reduceIte] using h'.trans_eq hn

lemma periodic_mode_test_integrable (F : PeriodicTorus ι → ℝ)
    (hF : Integrable F (periodicHaar ι)) (q : ι × Bool) :
    Integrable (fun x => F x*periodicFirstShellMode q x) (periodicHaar ι) := by
  have h := hF.bdd_mul (periodicFirstShellMode_continuous q).aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using periodicFirstShellMode_abs_le_one q x)
  exact h.congr (Eventually.of_forall fun x => mul_comm _ _)

lemma periodic_first_real_coefficient (F : PeriodicTorus ι → ℝ)
    (hF : Integrable F (periodicHaar ι)) (i : ι) :
    UnitAddTorus.mFourierCoeff (fun x => (F x:ℂ)) (periodicFirstFrequency i) =
      ((∫ x,F x*periodicFirstShellMode (i,false) x ∂periodicHaar ι : ℝ):ℂ)-
      ((∫ x,F x*periodicFirstShellMode (i,true) x ∂periodicHaar ι : ℝ):ℂ)*Complex.I := by
  have hi : Integrable (fun x : PeriodicTorus ι =>
      UnitAddTorus.mFourier (-(periodicFirstFrequency i)) x*(F x:ℂ)) (periodicHaar ι) := by
    have h := hF.ofReal.bdd_mul (c := 1)
      (UnitAddTorus.mFourier (-(periodicFirstFrequency i))).continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => by simp [UnitAddTorus.mFourier_neg,periodic_first_character,fourier_apply])
    exact h
  apply Complex.ext
  · rw [periodic_mFourierCoeff_eq_integral]
    change RCLike.re (∫ x, UnitAddTorus.mFourier (-(periodicFirstFrequency i)) x*(F x:ℂ) ∂periodicHaar ι)=_
    rw [←integral_re hi]
    simp only [Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.ofReal_im,Complex.I_im,mul_zero,zero_mul,mul_one,sub_zero]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp [UnitAddTorus.mFourier_neg,periodic_first_character,periodicFirstShellMode]
      ring
  · rw [periodic_mFourierCoeff_eq_integral]
    change RCLike.im (∫ x, UnitAddTorus.mFourier (-(periodicFirstFrequency i)) x*(F x:ℂ) ∂periodicHaar ι)=_
    rw [←integral_im hi]
    simp only [Complex.sub_im,Complex.ofReal_im,Complex.mul_im,Complex.I_im,
      Complex.ofReal_re,Complex.I_re,mul_one,mul_zero,add_zero,zero_sub]
    rw [←integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp [UnitAddTorus.mFourier_neg,periodic_first_character,periodicFirstShellMode]
      ring

/-- Genuine finite-rank first-shell source kernel. -/
def periodicFirstShellKernel (x y : PeriodicTorus ι) : ℝ :=
  (2*(periodicStabilityThreshold ι)⁻¹)*∑ q : ι × Bool,
    periodicFirstShellMode q x*periodicFirstShellMode q y

lemma periodic_finite_Gram_form {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {α : Type*} [Fintype α] (q : α → X → ℝ) (F : X → ℝ)
    (h : ∀ i,Integrable (fun x => F x*q i x) μ) :
    (∫ x,F x*(∫ y,F y*(∑ i,q i x*q i y) ∂μ) ∂μ) =
      ∑ i,(∫ x,F x*q i x ∂μ)^2 := by
  have he (x : X) : (∫ y,F y*(∑ i,q i x*q i y) ∂μ) =
      ∑ i,q i x*(∫ y,F y*q i y ∂μ) := by
    calc
      _ = ∫ y,∑ i,q i x*(F y*q i y) ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by
          dsimp only
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = _ := by rw [integral_finsetSum _ (fun i _ => (h i).const_mul _)];simp_rw [integral_const_mul]
  simp_rw [he]
  calc
    _ = ∫ x,∑ i,(F x*q i x)*(∫ y,F y*q i y ∂μ) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = _ := by
      rw [integral_finsetSum _ (fun i _ => (h i).mul_const _)]
      simp_rw [integral_mul_const,pow_two]

lemma periodicFirstShell_form_identity (F : PeriodicTorus ι → ℝ)
    (hF : Integrable F (periodicHaar ι)) :
    (∫ x,F x*(∫ y,F y*periodicFirstShellKernel x y ∂periodicHaar ι) ∂periodicHaar ι) =
      (2*(periodicStabilityThreshold ι)⁻¹)*
        ∑ i : ι,((UnitAddTorus.mFourierCoeff (fun x => (F x:ℂ)) (periodicFirstFrequency i)).re^2+
          (UnitAddTorus.mFourierCoeff (fun x => (F x:ℂ)) (periodicFirstFrequency i)).im^2) := by
  have hi := periodic_finite_Gram_form (periodicHaar ι) periodicFirstShellMode F
    (periodic_mode_test_integrable F hF)
  have he : (∫ x,F x*(∫ y,F y*periodicFirstShellKernel x y ∂periodicHaar ι) ∂periodicHaar ι) =
      (2*(periodicStabilityThreshold ι)⁻¹)*
        (∫ x,F x*(∫ y,F y*(∑ q : ι × Bool,periodicFirstShellMode q x*periodicFirstShellMode q y)
          ∂periodicHaar ι) ∂periodicHaar ι) := by
    have heinner (x : PeriodicTorus ι) :
        (∫ y,F y*periodicFirstShellKernel x y ∂periodicHaar ι) =
        (2*(periodicStabilityThreshold ι)⁻¹)*
          (∫ y,F y*(∑ q : ι × Bool,periodicFirstShellMode q x*periodicFirstShellMode q y)
            ∂periodicHaar ι) := by
      calc
        _ = ∫ y,(2*(periodicStabilityThreshold ι)⁻¹)*
            (F y*(∑ q : ι × Bool,periodicFirstShellMode q x*periodicFirstShellMode q y))
            ∂periodicHaar ι := by
          apply integral_congr_ae
          exact Eventually.of_forall fun y => by dsimp [periodicFirstShellKernel];ring
        _ = _ := integral_const_mul _ _
    simp_rw [heinner]
    calc
      _ = ∫ x,(2*(periodicStabilityThreshold ι)⁻¹)*
          (F x*(∫ y,F y*(∑ q : ι × Bool,periodicFirstShellMode q x*periodicFirstShellMode q y)
            ∂periodicHaar ι)) ∂periodicHaar ι := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by dsimp only;ring
      _ = _ := integral_const_mul _ _
  rw [he,hi,Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [periodic_first_real_coefficient F hF i]
  simp only [Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
    Complex.ofReal_im,Complex.I_im,mul_zero,zero_mul,mul_one,sub_zero,
    Complex.sub_im,Complex.mul_im,add_zero,zero_sub,neg_sq]
  ring

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_first_character
#print axioms DGRHS.Periodic.periodicFirstShellMode_continuous
#print axioms DGRHS.Periodic.periodicFirstShellMode_abs_le_one
#print axioms DGRHS.Periodic.periodic_mode_test_integrable
#print axioms DGRHS.Periodic.periodic_first_real_coefficient
#print axioms DGRHS.Periodic.periodic_finite_Gram_form
#print axioms DGRHS.Periodic.periodicFirstShell_form_identity
#check @DGRHS.Periodic.periodicFirstShell_form_identity
