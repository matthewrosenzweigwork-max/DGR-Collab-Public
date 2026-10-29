import DGRHS.Gaussian.PeriodicFirstShellAtomFeature
import DGRHS.Gaussian.SharpnessNormalizedAtom
import Mathlib.Analysis.Convex.Integral

/-! Genuine constant first-shell diagonal and its conditional atom bound.
The residual diagonal is not assumed bounded or convergent. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace DGRHS.Periodic
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicFirstShellMode_square_sum (x : PeriodicTorus ι) :
    (∑ q : ι × Bool,periodicFirstShellMode q x^2)=(Fintype.card ι : ℝ) := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  have he (i : ι) : periodicFirstShellMode (i,false) x^2+
      periodicFirstShellMode (i,true) x^2=1 := by
    have hn : ‖fourier 1 (x i)‖=1 := by simp [fourier_apply]
    have h := Complex.sq_norm (fourier 1 (x i))
    rw [hn,Complex.normSq_apply] at h
    simpa [periodicFirstShellMode,pow_two] using h.symm
  have he' (i : ι) : periodicFirstShellMode (i,true) x^2+
      periodicFirstShellMode (i,false) x^2=1 := by rw [add_comm];exact he i
  simp only [he',Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]

lemma periodicFirstShellAtomMode_eq_integral (A : Set (PeriodicTorus ι)) (q : ι × Bool) :
    periodicFirstShellAtomMode A q =
      ∫ x,periodicFirstShellMode q x ∂sharpnessNormalizedAtom (periodicHaar ι) A := by
  unfold periodicFirstShellAtomMode sharpnessNormalizedAtom
  rw [integral_smul_measure]
  simp only [ENNReal.toReal_inv,smul_eq_mul,div_eq_mul_inv]
  ring

lemma periodicFirstShellAtomMode_square_sum_le (A : Set (PeriodicTorus ι))
    (hm : 0<((periodicHaar ι) A).toReal) :
    (∑ q : ι × Bool,periodicFirstShellAtomMode A q^2) ≤ (Fintype.card ι : ℝ) := by
  let ν := sharpnessNormalizedAtom (periodicHaar ι) A
  haveI : IsProbabilityMeasure ν := sharpnessNormalizedAtom_probability _ A hm
  have hi (q : ι × Bool) : Integrable (periodicFirstShellMode q) ν :=
    (periodicFirstShellMode_continuous q).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs (q : ι × Bool) : Integrable (fun x => periodicFirstShellMode q x^2) ν :=
    ((periodicFirstShellMode_continuous q).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hj (q : ι × Bool) : (periodicFirstShellAtomMode A q)^2 ≤
      ∫ x,periodicFirstShellMode q x^2 ∂ν := by
    rw [periodicFirstShellAtomMode_eq_integral]
    exact ((even_two_mul 1).convexOn_pow (𝕜 := ℝ)).map_integral_le (by fun_prop) isClosed_univ
      (Eventually.of_forall fun x => mem_univ _) (hi q) (hs q)
  calc
    _ ≤ ∑ q : ι × Bool,∫ x,periodicFirstShellMode q x^2 ∂ν := Finset.sum_le_sum (fun q _ => hj q)
    _ = ∫ x,∑ q : ι × Bool,periodicFirstShellMode q x^2 ∂ν :=
      (integral_finsetSum _ (fun q _ => hs q)).symm
    _ = _ := by simp_rw [periodicFirstShellMode_square_sum];simp

lemma periodicFirstShellAtomFeature_diagonal_le (A : Set (PeriodicTorus ι))
    (hm : 0<((periodicHaar ι) A).toReal) :
    (∑ q : ι × Bool,(periodicFirstShellAtomFeature A q)^2) ≤
      2*(periodicStabilityThreshold ι)⁻¹*(Fintype.card ι : ℝ) := by
  have hc : 0≤2*(periodicStabilityThreshold ι)⁻¹ :=
    mul_nonneg (by norm_num) (inv_nonneg.mpr periodicStabilityThreshold_pos.le)
  calc
    _ = (2*(periodicStabilityThreshold ι)⁻¹)*∑ q : ι × Bool,periodicFirstShellAtomMode A q^2 := by
      change (∑ q : ι × Bool,(Real.sqrt (2*(periodicStabilityThreshold ι)⁻¹)*periodicFirstShellAtomMode A q)^2)=_
      simp only [mul_pow,Real.sq_sqrt hc]
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (periodicFirstShellAtomMode_square_sum_le A hm) hc

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicFirstShellMode_square_sum
#print axioms DGRHS.Periodic.periodicFirstShellAtomMode_eq_integral
#print axioms DGRHS.Periodic.periodicFirstShellAtomMode_square_sum_le
#print axioms DGRHS.Periodic.periodicFirstShellAtomFeature_diagonal_le
#check @DGRHS.Periodic.periodicFirstShellAtomFeature_diagonal_le
