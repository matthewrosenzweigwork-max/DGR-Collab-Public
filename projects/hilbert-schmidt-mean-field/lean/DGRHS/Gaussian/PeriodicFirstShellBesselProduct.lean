import DGRHS.Gaussian.PeriodicFirstShellTilt
import DGRHS.Gaussian.PeriodicBesselPhase

/-! The true spatial first-shell normalizer is the product of genuine
circle Bessel integrals. The two real Fourier modes are kept explicit. -/
noncomputable section
open MeasureTheory
open scoped ENNReal Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicFirstShellWeight_coordinate_product (t : ℝ) (z : ι × Bool → ℝ)
    (x : PeriodicTorus ι) :
    periodicFirstShellWeight t z x =
      ∏ j : ι,Real.exp ((t*Real.sqrt (2*(periodicStabilityThreshold ι)⁻¹))*
        (z (j,false)*(fourier 1 (x j)).re+z (j,true)*(fourier 1 (x j)).im)) := by
  unfold periodicFirstShellWeight periodicFirstShellField
  rw [Fintype.sum_prod_type,←Real.exp_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fintype.sum_bool,periodicFirstShellMode,Bool.false_eq_true,↓reduceIte]
  ring

lemma periodicFirstShellNormalizer_bessel_product (t : ℝ) (z : ι × Bool → ℝ) :
    periodicFirstShellNormalizer t z = ∏ j : ι,periodicBesselI0
      ((t*Real.sqrt (2*(periodicStabilityThreshold ι)⁻¹))*
        ‖(z (j,false):ℂ)+(z (j,true):ℂ)*Complex.I‖) := by
  unfold periodicFirstShellNormalizer periodicHaar
  simp_rw [periodicFirstShellWeight_coordinate_product]
  rw [integral_fintype_prod_eq_prod (fun j (x : UnitAddCircle) => Real.exp
    ((t*Real.sqrt (2*(periodicStabilityThreshold ι)⁻¹))*
      (z (j,false)*(fourier 1 x).re+z (j,true)*(fourier 1 x).im)))]
  apply Finset.prod_congr rfl
  intro j _
  exact periodicBessel_circle_linear_pair _ _ _

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicFirstShellWeight_coordinate_product
#print axioms DGRHS.Periodic.periodicFirstShellNormalizer_bessel_product
#check @DGRHS.Periodic.periodicFirstShellNormalizer_bessel_product
