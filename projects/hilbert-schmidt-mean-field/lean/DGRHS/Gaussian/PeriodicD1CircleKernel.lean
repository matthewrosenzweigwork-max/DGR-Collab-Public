import DGRHS.Gaussian.PeriodicD1AbelBoundary
import DGRHS.Gaussian.PeriodicD1FourierNormalization
import DGRHS.Gaussian.PeriodicCosineTrial

/-! UNCOMPILED REPAIRED COPY (Claude complete physical d1 return, 2026-10-03).
Repairs: explicit `f` in the coordinate transfer and the Fourier-coefficient rewrite
(`Integrable.ofReal` produces the RCLike cast, not `Complex.ofReal`); the coefficient
case split now uses `k = 0` / `k = -(j+1)` / `k = j+1` with `Int.toNat_of_nonneg`
instead of `cases` on `Int.ofNat/negSucc` and `omega` on `negSucc`. Statements
unchanged. Original header follows.
 Draft identification of the actual one-dimensional source Green kernel.
The circle logarithm coefficients are derived through the preceding Abel
series and dominated convergence. Haar coordinate transfer and the already
checked L1 uniqueness theorem then identify the source representative almost
everywhere. No desired kernel identity or L2 hypothesis is supplied. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical
namespace DGRHS.Periodic

lemma periodicD1_frequency_eq (k : PeriodicFrequency (Fin 1)) :
    k=periodicD1Frequency (k 0) := by
  funext i
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  rfl

lemma periodicD1_mFourier (k : PeriodicFrequency (Fin 1)) (x : PeriodicTorus (Fin 1)) :
    UnitAddTorus.mFourier k x=fourier (k 0) (x 0) := by
  simp [UnitAddTorus.mFourier]

lemma periodicD1_coordinate_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : UnitAddCircle → E} (hf : Integrable f AddCircle.haarAddCircle) :
    Integrable (fun x : PeriodicTorus (Fin 1) => f (x 0)) (periodicHaar (Fin 1)) := by
  exact (measurePreserving_eval
    (fun _ : Fin 1 => (AddCircle.haarAddCircle : Measure UnitAddCircle)) 0).integrable_comp_of_integrable hf

lemma periodicD1_coordinate_fourierCoeff {f : UnitAddCircle → ℂ}
    (hf : Integrable f AddCircle.haarAddCircle) (k : PeriodicFrequency (Fin 1)) :
    UnitAddTorus.mFourierCoeff (fun x : PeriodicTorus (Fin 1) => f (x 0)) k=
      fourierCoeff f (k 0) := by
  rw [periodic_mFourierCoeff_eq_integral,fourierCoeff]
  simp only [periodicD1_mFourier,Pi.neg_apply,smul_eq_mul]
  exact periodicHaar_integral_coordinate (f := fun t => fourier (-(k 0)) t * f t)
    (by simpa only [smul_eq_mul] using hf.fourier_smul (-(k 0))) 0

lemma periodicD1_boundary_fourierCoeff (k : ℤ) :
    fourierCoeff (fun x : UnitAddCircle => (periodicD1AbelCircle 1 x:ℂ)) k=
      periodicLogFourierCoeff (periodicD1Frequency k) := by
  by_cases hk : k = 0
  · subst hk
    rw [periodicD1_boundary_fourier_zero,
      show periodicD1Frequency 0 = 0 from funext fun _ => rfl, periodicLogFourierCoeff_zero]
  rw [periodicD1_log_fourierCoeff hk]
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, k = -((j:ℤ)+1) :=
      ⟨(-k-1).toNat, by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
    subst hj
    rw [periodicD1_boundary_fourier_negative j]
    have ha : |((-((j:ℤ)+1):ℤ):ℝ)| = (j:ℝ)+1 := by
      rw [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, abs_neg,
        abs_of_nonneg (by positivity)]
    congr 1
    rw [ha]
    field_simp [show (j:ℝ)+1≠0 by positivity] <;> ring
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, k = (j:ℤ)+1 :=
      ⟨(k-1).toNat, by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
    subst hj
    rw [periodicD1_boundary_fourier_positive j]
    have ha : |(((j:ℤ)+1:ℤ):ℝ)| = (j:ℝ)+1 := by
      rw [Int.cast_add, Int.cast_natCast, Int.cast_one, abs_of_nonneg (by positivity)]
    congr 1
    rw [ha]
    field_simp [show (j:ℝ)+1≠0 by positivity] <;> ring

def periodicD1CircleKernel (x : PeriodicTorus (Fin 1)) : ℝ := periodicD1AbelCircle 1 (x 0)

lemma periodicD1CircleKernel_measurable : Measurable periodicD1CircleKernel :=
  (periodicD1AbelCircle_measurable 1).comp (measurable_pi_apply 0)

lemma periodicD1CircleKernel_integrable :
    Integrable periodicD1CircleKernel (periodicHaar (Fin 1)) :=
  periodicD1_coordinate_integrable (periodicD1AbelCircle_integrable 1)

lemma periodicD1CircleKernel_fourierCoeff (k : PeriodicFrequency (Fin 1)) :
    UnitAddTorus.mFourierCoeff (fun x => (periodicD1CircleKernel x:ℂ)) k=
      periodicLogFourierCoeff k := by
  change UnitAddTorus.mFourierCoeff
    (fun x : PeriodicTorus (Fin 1) => (periodicD1AbelCircle 1 (x 0):ℂ)) k=_
  rw [periodicD1_coordinate_fourierCoeff (f := fun x : UnitAddCircle => (periodicD1AbelCircle 1 x:ℂ))
      (periodicD1AbelCircle_integrable 1).ofReal,
    periodicD1_boundary_fourierCoeff,←periodicD1_frequency_eq k]

/-- Exact source representative identification, with equality stated only
almost everywhere because the collision value is immaterial to Haar-L2. -/
theorem periodicD1CircleKernel_eq_kernel_ae :
    periodicD1CircleKernel=ᵐ[periodicHaar (Fin 1)]periodicLogKernel := by
  have h := periodicL1_fourier_unique (fun x => (periodicD1CircleKernel x:ℂ))
    (fun x => (periodicLogKernel x:ℂ)) periodicD1CircleKernel_integrable.ofReal
    periodicLogKernel_integrable.ofReal (fun k =>
      (periodicD1CircleKernel_fourierCoeff k).trans (periodicLogKernel_fourierCoeff k).symm)
  filter_upwards [h] with x hx
  exact Complex.ofReal_injective hx

lemma periodicD1CircleKernel_memLp : MemLp periodicD1CircleKernel 2 (periodicHaar (Fin 1)) :=
  (memLp_congr_ae periodicD1CircleKernel_eq_kernel_ae).mpr periodicLogKernel_memLp

lemma periodicD1CircleKernel_integral_zero :
    (∫ x,periodicD1CircleKernel x ∂periodicHaar (Fin 1))=0 :=
  (integral_congr_ae periodicD1CircleKernel_eq_kernel_ae).trans periodicLogKernel_integral_zero

end DGRHS.Periodic
