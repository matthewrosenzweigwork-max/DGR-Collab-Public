/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.StudentFourierGaussian
import DGRHS.Gaussian.D11Imported.Definitions

/-! Identification of the quotient character with the Euclidean Fourier
phase, including its exact invariance under the integer lattice. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace DGRHS.Gaussian.D11Imported.HighDim

def liftedCharacter {d : ℕ} (k : Frequency d) (x : Fin d → ℝ) : ℂ :=
  UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle))

lemma liftedCharacter_measurable {d : ℕ} (k : Frequency d) : Measurable (liftedCharacter k) := by
  unfold liftedCharacter
  fun_prop

lemma liftedCharacter_norm {d : ℕ} (k : Frequency d) (x : Fin d → ℝ) :
    ‖liftedCharacter k x‖ = 1 := by
  simp only [liftedCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
    fourier_apply, Circle.norm_coe, Finset.prod_const_one]

lemma liftedCharacter_periodic {d : ℕ} (k n : Frequency d) (x : Fin d → ℝ) :
    liftedCharacter k (fun i => x i+(n i:ℝ)) = liftedCharacter k x := by
  unfold liftedCharacter
  congr 1
  funext i
  have hn : ((n i:ℝ):UnitAddCircle) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr
    exact ⟨n i, by simp⟩
  rw [AddCircle.coe_add, hn, add_zero]

lemma liftedCharacter_eq_phase {d : ℕ} (k : Frequency d) (x : Fin d → ℝ) :
    liftedCharacter k x = StudentIntegral.phase
      (WithLp.toLp 2 (fun i => (k i:ℝ))) (WithLp.toLp 2 x) := by
  simp only [liftedCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    Pi.neg_apply, fourier_coe_apply, Complex.ofReal_one, div_one, Int.cast_neg]
  rw [← Complex.exp_sum]
  unfold StudentIntegral.phase
  congr 1
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, WithLp.toLp_ofLp,
    Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_neg, Complex.ofReal_ofNat,
    Complex.ofReal_intCast]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

#print axioms liftedCharacter_eq_phase
end DGRHS.Gaussian.D11Imported.HighDim
