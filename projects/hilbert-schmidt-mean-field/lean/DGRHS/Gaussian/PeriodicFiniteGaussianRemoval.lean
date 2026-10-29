import DGRHS.Gaussian.PeriodicFiniteGaussianWick
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual independent residual Gaussian removal for a finite weighted atom
law. All Gaussian integrability is proved from genuine linear MGF formulas
and finite word expansion; no comparison, covariance or properness conclusion
is supplied. The physical residual Gram realization is instantiated separately. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Classical BigOperators
namespace DGRHS.Periodic
open DGRHS.Gaussian
variable {α γ δ : Type*} [Fintype α] [Fintype γ] [Fintype δ]

def periodicFiniteWickFactor (p : α → ℝ) (q : α → γ → ℝ) (t : ℝ)
    (z : γ → ℝ) : ℝ := ∑ a,p a*periodicFiniteGaussianWick t (q a) z

def periodicFiniteJoinedFactor (p : α → ℝ) (q : α → γ → ℝ) (r : α → δ → ℝ)
    (t : ℝ) (zw : (γ → ℝ) × (δ → ℝ)) : ℝ :=
  ∑ a,p a*periodicFiniteGaussianWick t (q a) zw.1*periodicFiniteGaussianWick t (r a) zw.2

lemma periodicFiniteWickFactor_pow_eq (p : α → ℝ) (q : α → γ → ℝ) (t : ℝ) (N : ℕ)
    (z : γ → ℝ) : periodicFiniteWickFactor p q t z^N =
    ∑ l : Fin N → α,(∏ i,p (l i))*(∏ i,periodicFiniteGaussianWick t (q (l i)) z) := by
  rw [periodicFiniteWickFactor,Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.prod_mul_distrib]

lemma periodicFiniteWickFactor_pow_integrable (p : α → ℝ) (q : α → γ → ℝ)
    (t : ℝ) (N : ℕ) :
    Integrable (fun z => periodicFiniteWickFactor p q t z^N) (finiteStandardGaussian γ) := by
  simp_rw [periodicFiniteWickFactor_pow_eq]
  apply integrable_finsetSum
  intro l _
  exact (periodicFiniteGaussianWick_particle_integral t (fun i : Fin N => q (l i))).1.const_mul _

lemma periodicFiniteJoinedFactor_section (p : α → ℝ) (q : α → γ → ℝ)
    (r : α → δ → ℝ) (t : ℝ) (z : γ → ℝ) :
    Integrable (fun w => periodicFiniteJoinedFactor p q r t (z,w)) (finiteStandardGaussian δ) ∧
    (∫ w,periodicFiniteJoinedFactor p q r t (z,w) ∂finiteStandardGaussian δ) =
      periodicFiniteWickFactor p q t z := by
  have hi (a : α) := (periodicFiniteGaussianWick_mean_one t (r a)).1.const_mul
    (p a*periodicFiniteGaussianWick t (q a) z)
  constructor
  · exact integrable_finsetSum _ (fun a _ => hi a)
  · simp only [periodicFiniteJoinedFactor]
    rw [integral_finsetSum _ (fun a _ => hi a)]
    simp only [integral_const_mul,(periodicFiniteGaussianWick_mean_one t _).2,mul_one,
      periodicFiniteWickFactor]

lemma periodicFiniteJoinedFactor_section_pow_integrable (p : α → ℝ) (q : α → γ → ℝ)
    (r : α → δ → ℝ) (t : ℝ) (z : γ → ℝ) (N : ℕ) :
    Integrable (fun w => periodicFiniteJoinedFactor p q r t (z,w)^N) (finiteStandardGaussian δ) :=
  periodicFiniteWickFactor_pow_integrable
    (fun a => p a*periodicFiniteGaussianWick t (q a) z) r t N

lemma periodicFiniteJoinedFactor_pow_eq (p : α → ℝ) (q : α → γ → ℝ)
    (r : α → δ → ℝ) (t : ℝ) (N : ℕ) (zw : (γ → ℝ) × (δ → ℝ)) :
    periodicFiniteJoinedFactor p q r t zw^N =
    ∑ l : Fin N → α,(∏ i,p (l i))*
      ((∏ i,periodicFiniteGaussianWick t (q (l i)) zw.1)*
        (∏ i,periodicFiniteGaussianWick t (r (l i)) zw.2)) := by
  rw [periodicFiniteJoinedFactor,Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  ring

lemma periodicFiniteJoinedFactor_pow_integrable (p : α → ℝ) (q : α → γ → ℝ)
    (r : α → δ → ℝ) (t : ℝ) (N : ℕ) :
    Integrable (fun zw => periodicFiniteJoinedFactor p q r t zw^N)
      ((finiteStandardGaussian γ).prod (finiteStandardGaussian δ)) := by
  simp_rw [periodicFiniteJoinedFactor_pow_eq]
  apply integrable_finsetSum
  intro l _
  exact ((periodicFiniteGaussianWick_particle_integral t (fun i : Fin N => q (l i))).1.mul_prod
    (periodicFiniteGaussianWick_particle_integral t (fun i : Fin N => r (l i))).1).const_mul _

/-- Actual independent Gaussian Jensen removes the residual for every N,
including the empty/constant case, with genuine properness on both sides. -/
theorem periodicFiniteGaussian_residual_removal (p : α → ℝ) (hp : ∀ a,0≤p a)
    (q : α → γ → ℝ) (r : α → δ → ℝ) (t : ℝ) (N : ℕ) :
    (∫ z,periodicFiniteWickFactor p q t z^N ∂finiteStandardGaussian γ) ≤
      ∫ zw,periodicFiniteJoinedFactor p q r t zw^N
        ∂(finiteStandardGaussian γ).prod (finiteStandardGaussian δ) := by
  have hi := periodicFiniteJoinedFactor_pow_integrable p q r t N
  rw [integral_prod _ hi]
  apply integral_mono (periodicFiniteWickFactor_pow_integrable p q t N) hi.integral_prod_left
  intro z
  have hj := (convexOn_pow (𝕜 := ℝ) N).map_integral_le (by fun_prop) isClosed_Ici
    (Eventually.of_forall (fun w => Finset.sum_nonneg
      (fun a _ => mul_nonneg (mul_nonneg (hp a) (Real.exp_pos _).le) (Real.exp_pos _).le)))
    (periodicFiniteJoinedFactor_section p q r t z).1
    (periodicFiniteJoinedFactor_section_pow_integrable p q r t z N)
  change (∫ w,periodicFiniteJoinedFactor p q r t (z,w) ∂finiteStandardGaussian δ)^N ≤
    (∫ w,periodicFiniteJoinedFactor p q r t (z,w)^N ∂finiteStandardGaussian δ) at hj
  rw [(periodicFiniteJoinedFactor_section p q r t z).2] at hj
  exact hj

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicFiniteWickFactor_pow_eq
#print axioms DGRHS.Periodic.periodicFiniteWickFactor_pow_integrable
#print axioms DGRHS.Periodic.periodicFiniteJoinedFactor_section
#print axioms DGRHS.Periodic.periodicFiniteJoinedFactor_section_pow_integrable
#print axioms DGRHS.Periodic.periodicFiniteJoinedFactor_pow_eq
#print axioms DGRHS.Periodic.periodicFiniteJoinedFactor_pow_integrable
#print axioms DGRHS.Periodic.periodicFiniteGaussian_residual_removal
#check @DGRHS.Periodic.periodicFiniteGaussian_residual_removal
