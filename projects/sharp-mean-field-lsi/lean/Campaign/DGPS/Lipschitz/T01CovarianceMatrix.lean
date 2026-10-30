import DGPS.Lipschitz.GaussianKernelTilt
import SharpSymmetricLSI.Defs.D16_GaussianLimit
import DGPS.Lipschitz.T01FiniteRankBridge
import FullLabeledLSI.Paper.Sec6Rank3

/-!
# The actual covariance matrix in positive spectral coordinates

The operator inverse is the genuine ring inverse. Its inverse identity is used only with the
coercivity certificate, and the constant coordinate is excluded from the matrix indices.
-/

namespace DGPS.Lipschitz

open KernelApproximation
open MeasureTheory Filter Topology
open scoped InnerProductSpace

/-- Restrict a summable pair-indexed real family to strictly positive indices. -/
theorem t01_shifted_pair_summable (f : ℕ × ℕ → ℝ) (hf : Summable f) :
    Summable (fun p : ℕ × ℕ => f (p.1 + 1, p.2 + 1)) := by
  have hshift : Function.Injective (fun p : ℕ × ℕ => (p.1 + 1, p.2 + 1)) := by
    intro p q h
    exact Prod.ext (Nat.add_right_cancel (congrArg Prod.fst h))
      (Nat.add_right_cancel (congrArg Prod.snd h))
  exact hf.comp_injective hshift

noncomputable def t01CovarianceMatrix {d : ℕ} (S : Spec d) (J : InteractionData d)
    (i j : ℕ) : ℝ :=
  inner ℝ ((spectralBasis_LIP016 S) (i + 1))
    (Ring.inverse (1 + DGPS.kernelOp J (specProbability_LIP016 S)) ((spectralBasis_LIP016 S) (j + 1)))

theorem t01_Tmat_eq_operator {d : ℕ} (S : Spec d) (J : InteractionData d) (i j : ℕ) :
    SharpLSI.Tmat J.W S.mu S.v i j =
      inner ℝ ((spectralBasis_LIP016 S) (i + 1)) (DGPS.kernelOp J (specProbability_LIP016 S) ((spectralBasis_LIP016 S) (j + 1))) := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  rw [DGPS.inner_kernelOp]
  have hc := (centeredKernel_continuous J S.mu).mul
    (((S.vc (i + 1)).comp continuous_fst).mul ((S.vc (j + 1)).comp continuous_snd))
  have hi : Integrable (fun p : Torus d × Torus d => centeredKernel J S.mu p.1 p.2 *
      (S.v (i + 1) p.1 * S.v (j + 1) p.2)) (S.mu.prod S.mu) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    SharpLSI.Tmat J.W S.mu S.v i j =
        ∫ p, centeredKernel J S.mu p.1 p.2 * (S.v (i + 1) p.1 * S.v (j + 1) p.2)
          ∂S.mu.prod S.mu := by
      unfold SharpLSI.Tmat
      rw [legacy_centeredKernel_eq, integral_prod _ hi]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => integral_congr_ae
        (Eventually.of_forall fun y => by ring)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [
        (Measure.quasiMeasurePreserving_fst (μ := S.mu) (ν := S.mu)).ae_eq_comp
          (S.ae_mu (S.ve (i + 1))),
        (Measure.quasiMeasurePreserving_snd (μ := S.mu) (ν := S.mu)).ae_eq_comp
          (S.ae_mu (S.ve (j + 1)))] with p hp hq
      change S.v (i + 1) p.1 = spectralBasis_LIP016 S (i + 1) p.1 at hp
      change S.v (j + 1) p.2 = spectralBasis_LIP016 S (j + 1) p.2 at hq
      rw [hp, hq] <;> rfl

theorem t01_Tmat_eq_TK {d : ℕ} (S : Spec d) (D : KData d) (J : InteractionData d)
    (hD : D.K = centeredKernel J S.mu) (i j : ℕ) :
    SharpLSI.Tmat J.W S.mu S.v i j = TK S D.K (i + 1) (j + 1) := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  rw [t01_Tmat_eq_operator, DGPS.inner_kernelOp]
  unfold TK
  simp only [hD]
  apply integral_congr_ae
  filter_upwards [
    (Measure.quasiMeasurePreserving_fst (μ := S.mu) (ν := S.mu)).ae_eq_comp
      (S.ae_mu (S.ve (i + 1))),
    (Measure.quasiMeasurePreserving_snd (μ := S.mu) (ν := S.mu)).ae_eq_comp
      (S.ae_mu (S.ve (j + 1)))] with p hp hq
  change S.v (i + 1) p.1 = spectralBasis_LIP016 S (i + 1) p.1 at hp
  change S.v (j + 1) p.2 = spectralBasis_LIP016 S (j + 1) p.2 at hq
  rw [← hp, ← hq] <;> rfl

theorem t01_Tmat_finiteSection_coercive {d : ℕ} (S : Spec d) (J : InteractionData d)
    {σ : ℝ}
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ inner ℝ g (DGPS.densityHessian J (specProbability_LIP016 S) g))
    (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    min 1 σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 +
      inner ℝ y (SharpLSI.secOp (SharpLSI.Tmat J.W S.mu S.v) n y) := by
  let f := ∑ i : Fin n, y i • (spectralBasis_LIP016 S) (i.val + 1)
  have ho : Orthonormal ℝ (fun i : Fin n => (spectralBasis_LIP016 S) (i.val + 1)) :=
    (spectralBasis_LIP016 S).orthonormal.comp _ (fun i j h => Fin.ext (Nat.add_right_cancel h))
  have hn : ‖f‖ ^ 2 = ∑ i : Fin n, y i ^ 2 := by
    simpa only [f, real_inner_self_eq_norm_sq, conj_trivial, ← sq] using
      ho.inner_sum (fun i => y i) (fun i => y i) Finset.univ
  have hform : inner ℝ f (DGPS.kernelOp J (specProbability_LIP016 S) f) =
      ∑ i : Fin n, ∑ j : Fin n,
        SharpLSI.Tmat J.W S.mu S.v i j * (y i * y j) := by
    dsimp only [f]
    simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_left,
      inner_smul_right, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [t01_Tmat_eq_operator]
    simp only [conj_trivial]
    ring
  have h := centered_coercivity_full_LIP016 J (specProbability_LIP016 S) hH f
  rw [hn, hform] at h
  rw [SharpLSI.inner_secOp_self]
  simpa only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs] using h

/-- The genuine operator inverse supplies the infinite matrix inverse on positive modes. -/
theorem t01CovarianceMatrix_isInverse {d : ℕ} (S : Spec d) (aux : Aux S)
    (J : InteractionData d) {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ inner ℝ g (DGPS.densityHessian J (specProbability_LIP016 S) g)) :
    SharpLSI.IsInverseOfIPlus
      (fun i j => inner ℝ ((spectralBasis_LIP016 S) (i + 1)) (DGPS.kernelOp J (specProbability_LIP016 S) ((spectralBasis_LIP016 S) (j + 1))))
      (t01CovarianceMatrix S J) := by
  let T := DGPS.kernelOp J (specProbability_LIP016 S)
  let U := Ring.inverse (1 + T)
  let u j := U ((spectralBasis_LIP016 S) (j + 1))
  have hunit : IsUnit (1 + T) := by
    apply isUnit_of_coercive_LIP016 _ (lt_min zero_lt_one hσ)
    intro f
    simpa only [add_apply, one_apply_eq_self,
      inner_add_right, real_inner_self_eq_norm_sq, T] using
      centered_coercivity_full_LIP016 J (specProbability_LIP016 S) hH f
  have hsym : ∀ f g : Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d)),
      inner ℝ (T f) g = inner ℝ f (T g) := fun f g =>
    kernelOp_symmetric_LIP016 J (specProbability_LIP016 S) f g
  have hsol : ∀ j, u j + T (u j) = (spectralBasis_LIP016 S) (j + 1) := by
    intro j
    have h := congrArg (fun L => L ((spectralBasis_LIP016 S) (j + 1))) (Ring.mul_inverse_cancel (1 + T) hunit)
    exact h
  have hT0 : T ((spectralBasis_LIP016 S) 0) = 0 := by
    rw [spectralBasis_zero_LIP016 S aux]
    exact kernelOp_const_one_LIP016 J (specProbability_LIP016 S)
  have hite := orthonormal_iff_ite.mp (spectralBasis_LIP016 S).orthonormal
  have hu0 : ∀ j, inner ℝ ((spectralBasis_LIP016 S) 0) (u j) = 0 := by
    intro j
    have h := congrArg (fun f => inner ℝ ((spectralBasis_LIP016 S) 0) f) (hsol j)
    have hT : inner ℝ ((spectralBasis_LIP016 S) 0) (T (u j)) = 0 := by
      rw [real_inner_comm, hsym (u j) ((spectralBasis_LIP016 S) 0), hT0, inner_zero_right]
    rw [inner_add_right, hT, add_zero, hite] at h
    simpa using h
  change SharpLSI.IsInverseOfIPlus
    (fun i j => inner ℝ ((spectralBasis_LIP016 S) (i + 1)) (T ((spectralBasis_LIP016 S) (j + 1))))
    (fun i j => inner ℝ ((spectralBasis_LIP016 S) (i + 1)) (u j))
  intro j
  refine ⟨?_, fun i => ?_⟩
  · have h := ((spectralBasis_LIP016 S).orthonormal.comp (· + 1) (add_left_injective 1)).inner_products_summable
      (x := u j)
    simpa only [Function.comp_apply, Real.norm_eq_abs, sq_abs] using h
  · let w := (spectralBasis_LIP016 S) (i + 1) + T ((spectralBasis_LIP016 S) (i + 1))
    have hterm : ∀ k, ((if i = k then 1 else 0) +
        inner ℝ ((spectralBasis_LIP016 S) (i + 1)) (T ((spectralBasis_LIP016 S) (k + 1)))) * inner ℝ ((spectralBasis_LIP016 S) (k + 1)) (u j) =
        inner ℝ w ((spectralBasis_LIP016 S) (k + 1)) * inner ℝ ((spectralBasis_LIP016 S) (k + 1)) (u j) := by
      intro k
      dsimp only [w]
      rw [inner_add_left, hsym ((spectralBasis_LIP016 S) (i + 1)) ((spectralBasis_LIP016 S) (k + 1)), hite]
      simp only [Nat.add_right_cancel_iff]
    have hpar := (spectralBasis_LIP016 S).hasSum_inner_mul_inner w (u j)
    have hb0 : inner ℝ w ((spectralBasis_LIP016 S) 0) * inner ℝ ((spectralBasis_LIP016 S) 0) (u j) = 0 := by rw [hu0, mul_zero]
    have hshift : HasSum (fun k => inner ℝ w ((spectralBasis_LIP016 S) (k + 1)) *
        inner ℝ ((spectralBasis_LIP016 S) (k + 1)) (u j)) (inner ℝ w (u j)) := by
      have h := (hasSum_nat_add_iff' 1).2 hpar
      simpa only [Finset.sum_range_one, hb0, sub_zero] using h
    have hval : inner ℝ w (u j) = if i = j then 1 else 0 := by
      dsimp only [w]
      rw [inner_add_left, hsym ((spectralBasis_LIP016 S) (i + 1)) (u j), ← inner_add_right, hsol j, hite]
      simp only [Nat.add_right_cancel_iff]
    refine ⟨?_, ?_⟩
    · have s1 := ((spectralBasis_LIP016 S).orthonormal.comp (· + 1) (add_left_injective 1)).inner_products_summable
        (x := w)
      have s2 := ((spectralBasis_LIP016 S).orthonormal.comp (· + 1) (add_left_injective 1)).inner_products_summable
        (x := u j)
      refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => ?_)
        ((s1.add s2).div_const 2)
      rw [hterm, abs_mul, real_inner_comm ((spectralBasis_LIP016 S) (k + 1)) w]
      simp only [Function.comp_apply, Real.norm_eq_abs, sq_abs]
      have h := two_mul_le_add_sq |inner ℝ ((spectralBasis_LIP016 S) (k + 1)) w| |inner ℝ ((spectralBasis_LIP016 S) (k + 1)) (u j)|
      rw [sq_abs, sq_abs] at h
      linarith
    · rw [← hval, ← hshift.tsum_eq]
      exact tsum_congr hterm

private theorem t01_Tmat_symmetric {d : ℕ} (S : Spec d) (J : InteractionData d) :
    ∀ i j, SharpLSI.Tmat J.W S.mu S.v i j = SharpLSI.Tmat J.W S.mu S.v j i := by
  intro i j
  rw [t01_Tmat_eq_operator, t01_Tmat_eq_operator]
  exact (real_inner_comm
    (DGPS.kernelOp J (specProbability_LIP016 S) (spectralBasis_LIP016 S (j + 1)))
    (spectralBasis_LIP016 S (i + 1))).trans
      (kernelOp_symmetric_LIP016 J (specProbability_LIP016 S)
        (spectralBasis_LIP016 S (j + 1)) (spectralBasis_LIP016 S (i + 1)))

private theorem t01_Tmat_hs {d : ℕ} (S : Spec d) (D : KData d) (J : InteractionData d)
    (hD : D.K = centeredKernel J S.mu) :
    Summable (fun p : ℕ × ℕ => SharpLSI.Tmat J.W S.mu S.v p.1 p.2 ^ 2) := by
  have hs := t01_shifted_pair_summable (fun p : ℕ × ℕ => TK S D.K p.1 p.2 ^ 2)
    (hasSum_prod_sq S D).summable
  exact Summable.of_nonneg_of_le (fun p => sq_nonneg _) (fun p =>
    le_of_eq (congrArg (fun x : ℝ => x ^ 2) (t01_Tmat_eq_TK S D J hD p.1 p.2))) hs

theorem t01CovarianceMatrix_symPkg {d : ℕ} (S : Spec d) (aux : Aux S)
    (J : InteractionData d) (D : KData d) (hD : D.K = centeredKernel J S.mu)
    {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ inner ℝ g (DGPS.densityHessian J (specProbability_LIP016 S) g)) :
    SharpLSI.FL.Rank3.SymPkg (SharpLSI.Tmat J.W S.mu S.v)
      (t01CovarianceMatrix S J) (min 1 σ) := by
  refine {
    symm := t01_Tmat_symmetric S J
    hs := t01_Tmat_hs S D J hD
    pos := lt_min zero_lt_one hσ
    sec := t01_Tmat_finiteSection_coercive S J hH
    inv := ?_ }
  have heq : SharpLSI.Tmat J.W S.mu S.v =
      (fun i j => inner ℝ (spectralBasis_LIP016 S (i + 1))
        (DGPS.kernelOp J (specProbability_LIP016 S) (spectralBasis_LIP016 S (j + 1)))) := by
    funext i j
    exact t01_Tmat_eq_operator S J i j
  rw [heq]
  exact t01CovarianceMatrix_isInverse S aux J hσ hH

end DGPS.Lipschitz
