/- Development: the actual inverse operator, Parseval identity, and SAME-process
Gaussian transform. Neither an inverse nor the target identity is assumed. -/
import DGRHS.Gaussian.InfiniteHilbertTilt
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace
namespace DGRHS.Gaussian
variable {ι H : Type*} [Countable ι] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

omit [Countable ι] [CompleteSpace H] in
lemma tilted_basis_coeff_tsum_eq_inner (b : HilbertBasis ι ℝ H) (β : ℝ)
    (a : ι → ℝ) (R : H →L[ℝ] H)
    (hR : ∀ v i, b.repr (R v) i = (1+β*a i)⁻¹*b.repr v i) (v : H) :
    (∑' i, (b.repr v i)^2/(1+β*a i)) = inner ℝ v (R v) := by
  calc
    _ = ∑' i, (b.repr v i)*(b.repr (R v) i) := by
      apply tsum_congr
      intro i
      rw [hR v i]
      ring
    _ = _ := by
      simpa only [b.repr_apply_apply, real_inner_comm] using b.tsum_inner_mul_inner v (R v)

/-- Full basis, including zero modes. The inverse identities and transform are
obtained from the actual symmetric operator's eigenbasis and square summability. -/
theorem exists_hilbert_tilt_resolvent (T : H →L[ℝ] H) (hT : T.toLinearMap.IsSymmetric)
    (b : HilbertBasis ι ℝ H) (a : ι → ℝ) (he : ∀ i, T (b i) = a i • b i)
    (β : ℝ) (ha : Summable (fun i => (a i)^2)) (hm : ∀ i, 0 < 1+β*a i)
    (f : ι → ℕ) (hf : Function.Injective f) :
    ∃ R : H →L[ℝ] H,
      (∀ v, R v + β • T (R v) = v) ∧
      (∀ v, R (v + β • T v) = v) ∧
      (∀ v i, b.repr (R v) i = (1+β*a i)⁻¹*b.repr v i) ∧
      ∀ v, Integrable (fun ω => Real.exp (indexedGaussianIsometry b f hf v ω-
          (β/2)*centeredGaussianChaos a f ω)) IsonormalProcess.iidStdGaussian ∧
        (∫ ω, Real.exp (indexedGaussianIsometry b f hf v ω-
          (β/2)*centeredGaussianChaos a f ω) ∂IsonormalProcess.iidStdGaussian) =
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β*a i)))⁻¹ *
            Real.exp (inner ℝ v (R v)/2) := by
  obtain ⟨δ,hδ,hδm⟩ := DGRHS.Kernel.exists_uniform_spectral_margin β a ha hm
  obtain ⟨R,hR1,hR2,hRc⟩ := DGRHS.Kernel.spectralMultiplier_inverse T hT b a he β δ hδ hδm
  refine ⟨R,hR1,hR2,hRc,fun v => ?_⟩
  have h := integral_exp_hilbert_tilt_weak_margin b v β a ha hm f hf
  rw [tilted_basis_coeff_tsum_eq_inner b β a R hRc v] at h
  exact h
end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.tilted_basis_coeff_tsum_eq_inner
#print axioms DGRHS.Gaussian.exists_hilbert_tilt_resolvent
#check @DGRHS.Gaussian.exists_hilbert_tilt_resolvent
