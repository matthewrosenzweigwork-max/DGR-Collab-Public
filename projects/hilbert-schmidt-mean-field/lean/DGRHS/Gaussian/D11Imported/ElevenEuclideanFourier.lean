/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.StudentFourier
import DGRHS.Gaussian.D11Imported.HalfIntegerLaplace
import DGRHS.Gaussian.D11Imported.ElevenEuclideanMass

/-! The Fourier transform of the actual normalized, scaled eleven-dimensional
profile. Gamma subordination and the half-integer integral give precisely the
polynomial Phi in Section 4. -/
noncomputable section
open MeasureTheory Set
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven

lemma euclideanProfile_norm (x : EuclideanSpace ℝ (Fin 11)) :
    euclideanProfile (fun i => x i) =
      (5:ℝ)^11*(122880/Real.pi^6)*(1+25*‖x‖^2)^(-(11:ℝ)) := by
  simp only [euclideanProfile, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  rw [show -(11:ℝ) = ((-11:ℤ):ℝ) by norm_num, Real.rpow_intCast]

lemma euclideanProfile_fourier (w : EuclideanSpace ℝ (Fin 11)) :
    (∫ x : EuclideanSpace ℝ (Fin 11),
      StudentIntegral.phase w x * (euclideanProfile (fun i => x i):ℂ)) =
        (fourierProfile (2*Real.pi*‖w‖/5):ℂ) := by
  let z : ℝ := 2*Real.pi*‖w‖/5
  let R : ℝ := (Real.pi/25)^((11:ℝ)/2)
  let A : ℝ := Real.sqrt Real.pi*Real.exp (-z)*fourierPolynomial z/32
  let L : ℂ := ∫ x : EuclideanSpace ℝ (Fin 11),
    StudentIntegral.phase w x*((1+25*‖x‖^2)^(-(11:ℝ)):ℝ)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have h := StudentIntegral.student_fourier_subordination 11
    (by norm_num : (11:ℝ)/2 < 11) (by norm_num : (0:ℝ)<25) w
  have hg : Real.Gamma 11 = 3628800 := by
    convert Real.Gamma_nat_eq_factorial 10 using 1 <;> norm_num
  have hi : (∫ t in Ioi (0:ℝ), t^((9:ℝ)/2)*
      Real.exp (-t-Real.pi^2*‖w‖^2/(25*t))) = A := by
    have he (t : ℝ) : Real.pi^2*‖w‖^2/(25*t) = z^2/(4*t) := by dsimp [z]; ring
    simp_rw [he]
    exact ReciprocalGaussian.laplace_half_eleven hz
  norm_num only [Nat.cast_ofNat] at h
  rw [hg, hi] at h
  change L*(3628800:ℂ) = (R:ℂ)*(A:ℂ) at h
  have hL : L = ((R*A/3628800:ℝ):ℂ) := by
    apply mul_right_cancel₀ (by norm_num : (3628800:ℂ)≠0)
    rw [h]
    push_cast
    ring
  have he (x : EuclideanSpace ℝ (Fin 11)) :
      StudentIntegral.phase w x * (euclideanProfile (fun i => x i):ℂ) =
        (((5:ℝ)^11*(122880/Real.pi^6):ℝ):ℂ)*
          (StudentIntegral.phase w x*((1+25*‖x‖^2)^(-(11:ℝ)):ℝ)) := by
    rw [euclideanProfile_norm]
    push_cast
    ring
  simp_rw [he]
  rw [integral_const_mul]
  change (((5:ℝ)^11*(122880/Real.pi^6):ℝ):ℂ)*L = (fourierProfile z:ℂ)
  rw [hL, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  have hp : R = (Real.pi^5*Real.sqrt Real.pi)/5^11 := by
    dsimp [R]
    rw [show (11:ℝ)/2 = (5:ℕ)+(1/2:ℝ) by norm_num,
      Real.rpow_add (by positivity), Real.rpow_natCast, ← Real.sqrt_eq_rpow,
      Real.sqrt_div Real.pi_pos.le, show Real.sqrt 25 = 5 by norm_num]
    ring
  rw [hp]
  dsimp [A, fourierProfile]
  have hs := Real.sq_sqrt Real.pi_pos.le
  field_simp
  rw [hs]
  ring

#print axioms euclideanProfile_fourier
end DGRHS.Gaussian.D11Imported.HighDim.Eleven
