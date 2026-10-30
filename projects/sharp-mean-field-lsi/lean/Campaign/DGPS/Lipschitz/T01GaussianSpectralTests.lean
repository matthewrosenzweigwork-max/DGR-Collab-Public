import DGPS.Lipschitz.T01GaussianRateBridge
import DGPS.Lipschitz.T01ScalarGaussian

/-! Exact finite positive spectral tests for the scalar Gaussian comparison. -/

noncomputable section
open MeasureTheory Filter
open scoped RealInnerProductSpace

namespace DGPS.Lipschitz
open KernelApproximation
variable {d : ℕ}

/-- Finite sums preserve the actual periodic weak-gradient relation. -/
theorem t01_isWeakGradient_finset_sum {ι : Type*} (s : Finset ι)
    (u : ι → Torus d → ℝ) (G : ι → Torus d → Tangent d)
    (hu : ∀ i ∈ s, IsWeakGradient (u i) (G i)) :
    IsWeakGradient (fun x => ∑ i ∈ s, u i x) (fun x => ∑ i ∈ s, G i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isWeakGradient_zero (d := d))
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hu a (Finset.mem_insert_self _ _)).add
        (ih fun i hi => hu i (Finset.mem_insert_of_mem hi))

/-- The continuous spectral representatives represent their finite L² combination. -/
theorem t01_finite_spectral_ae (S : Spec d) (n : ℕ) (v : ℕ → ℝ) :
    (fun x => ∑ i ∈ Finset.range n, v i * S.v (i + 1) x) =ᵐ[S.mu]
      ((∑ i ∈ Finset.range n, v i • S.e (i + 1) : Lp ℝ 2 S.mu) : Torus d → ℝ) := by
  have h : ∀ s : Finset ℕ,
      (fun x => ∑ i ∈ s, v i * S.v (i + 1) x) =ᵐ[S.mu]
        ((∑ i ∈ s, v i • S.e (i + 1) : Lp ℝ 2 S.mu) : Torus d → ℝ) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        filter_upwards [Lp.coeFn_zero ℝ 2 S.mu] with x hx
        simpa only [Pi.zero_apply] using hx.symm
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        filter_upwards [S.ae_mu (S.ve (i + 1)), ih,
          Lp.coeFn_smul (v i) (S.e (i + 1)),
          Lp.coeFn_add (v i • S.e (i + 1)) (∑ j ∈ s, v j • S.e (j + 1))] with x hx hs hsm hadd
        rw [hadd]
        simp only [Pi.add_apply]
        rw [hsm]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← hx, hs]
  exact h _

/-- Finite spectral tests have their exact spectral Dirichlet energy. -/
theorem t01_finite_spectral_test (S : Spec d) (aux : Aux S) (n : ℕ) (v : ℕ → ℝ) :
    ∃ (g : C(Torus d, ℝ)) (L : ℝ),
      (fun x => g x) =ᵐ[S.mu]
        ((∑ i ∈ Finset.range n, v i • S.e (i + 1) : Lp ℝ 2 S.mu) : Torus d → ℝ) ∧
      TorusLipschitzWith L (fun x => g x) ∧
      (∫ x, ‖smoothGrad (fun y => g y) x‖ ^ 2 ∂S.mu) =
        ∑ i ∈ Finset.range n, S.lam (i + 1) * v i ^ 2 := by
  classical
  let g : C(Torus d, ℝ) :=
    ⟨fun x => ∑ i ∈ Finset.range n, v i * S.v (i + 1) x,
      continuous_finsetSum _ fun i hi => continuous_const.mul (S.vc (i + 1))⟩
  let G : Torus d → Tangent d := fun x => ∑ i ∈ Finset.range n, v i • aux.g (i + 1) x
  let L : ℝ := ∑ i ∈ Finset.range n, |v i| * (aux.Kc * (1 + S.lam (i + 1)) ^ d)
  have hgG : IsWeakGradient (fun x => g x) G := by
    change IsWeakGradient (fun x => ∑ i ∈ Finset.range n, v i * S.v (i + 1) x)
      (fun x => ∑ i ∈ Finset.range n, v i • aux.g (i + 1) x)
    exact t01_isWeakGradient_finset_sum (Finset.range n) _ _
      fun i hi => (aux.gw (i + 1)).smul (v i)
  have hb : ∀ x, ‖G x‖ ≤ L := by
    intro x
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      ((le_add_of_nonneg_left (abs_nonneg _)).trans (aux.c1 (i + 1) x)) (abs_nonneg _)
  have hLip := torusLipschitz_of_weakGradient_bound g.continuous hgG hb
  have hL : 0 ≤ L := (norm_nonneg (G 0)).trans (hb 0)
  have hsm : IsWeakGradient (fun x => g x) (smoothGrad (fun x => g x)) := by
    obtain ⟨hw, -⟩ := exists_weak_gradient hL hLip
    exact isWeakGradient_iff_isWeakGradientLp.mpr
      ⟨hw.memLp.mono_exponent (by simp), hw.memLp_grad.mono_exponent (by simp), hw.ibp⟩
  let f : Lp ℝ 2 S.mu := ∑ i ∈ Finset.range n, v i • S.e (i + 1)
  have hgf := t01_finite_spectral_ae S n v
  have hfG : IsWeakGradient (f : Torus d → ℝ) (smoothGrad (fun x => g x)) :=
    hsm.congr_ae (S.ae_haar hgf) (EventuallyEq.refl _ _)
  have hform := S.form f _ hfG
  rw [S.weightedForm_eq] at hform
  have hc : ∀ j, inner ℝ (S.e j) f =
      ∑ i ∈ Finset.range n, if j = i + 1 then v i else 0 := by
    intro j
    simp only [f, inner_sum, inner_smul_right, orthonormal_iff_ite.mp S.e.orthonormal]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp_all
  have hs := hasSum_sum (s := Finset.range n) (fun i hi =>
    hasSum_ite_eq (i + 1) (S.lam (i + 1) * v i ^ 2))
  have heq : (fun j => S.lam j * inner ℝ (S.e j) f ^ 2) =
      (fun j => ∑ i ∈ Finset.range n, if j = i + 1 then S.lam (i + 1) * v i ^ 2 else 0) := by
    funext j
    rw [hc]
    by_cases hj : ∃ i ∈ Finset.range n, j = i + 1
    · obtain ⟨i, hi, rfl⟩ := hj
      simp only [Nat.add_right_cancel_iff]
      simp [Finset.sum_ite_eq', hi]
    · push_neg at hj
      simp only [Finset.sum_eq_zero (fun i hi => if_neg (hj i hi)), zero_pow (by norm_num : 2 ≠ 0), mul_zero]
  refine ⟨g, L, hgf, hLip, ?_⟩
  exact hform.unique (by simpa only [heq, eq_comm] using hs)

/-- The actual scalar rate bounds each finite positive-coordinate Gaussian ratio. -/
theorem t01_scalarRate_le_finite_gaussian (S : Spec d) (aux : Aux S)
    (A : InteractionData d) (hA : LipschitzData A) (b : AbsoluteDrift A)
    (hmin : ∀ ν : ProbabilityMeasure (Torus d),
      freeEnergy A (specProbability_LIP016 S) ≤ freeEnergy A ν)
    (hH : IsCoerciveDensityHessian A (specProbability_LIP016 S))
    (n : ℕ) (v : ℕ → ℝ)
    (hQ : 0 < ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      v i * t01CovarianceMatrix S A i j * v j) :
    scalarRate A b ≤ ENNReal.ofReal (∑ i ∈ Finset.range n, S.lam (i + 1) * v i ^ 2) /
      ENNReal.ofReal (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        v i * t01CovarianceMatrix S A i j * v j) := by
  obtain ⟨f, hf, hcov⟩ := t01_finite_densityCovariance_quadratic S aux A hH n v
  obtain ⟨g, L, hgf, hg, henergy⟩ := t01_finite_spectral_test S aux n v
  have hfg : (fun x => g x) =ᵐ[(specProbability_LIP016 S : Measure (Torus d))]
      (f : Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d))) := by
    rw [hf]
    change (fun x => g x) =ᵐ[S.mu]
      ((∑ i ∈ Finset.range n, v i • S.e (i + 1) : Lp ℝ 2 S.mu) : Torus d → ℝ)
    exact hgf
  have henergy' : (∫ x, ‖smoothGrad (fun y => g y) x‖ ^ 2
      ∂(specProbability_LIP016 S : Measure (Torus d))) =
        ∑ i ∈ Finset.range n, S.lam (i + 1) * v i ^ 2 := by
    change (∫ x, ‖smoothGrad (fun y => g y) x‖ ^ 2 ∂S.mu) = _
    exact henergy
  have h := scalarRate_le_covariance_quotient A hA b (specProbability_LIP016 S)
    hmin hH f g hfg hg (by rwa [hcov])
  rw [hcov, henergy', ENNReal.ofReal_div_of_pos hQ] at h
  exact h

/-- The scalar rate is bounded by the actual infinite matrix Gaussian quotient. -/
theorem t01_scalarRate_le_lamG (S : Spec d) (aux : Aux S)
    (A : InteractionData d) (hA : LipschitzData A) (b : AbsoluteDrift A)
    (hmin : ∀ ν : ProbabilityMeasure (Torus d),
      freeEnergy A (specProbability_LIP016 S) ≤ freeEnergy A ν)
    (hH : IsCoerciveDensityHessian A (specProbability_LIP016 S))
    (D : KData d) (hD : D.K = centeredKernel A S.mu) :
    scalarRate A b ≤ SharpLSI.lamG (fun i => S.lam (i + 1)) (t01CovarianceMatrix S A) := by
  obtain ⟨σ, hσ, hbound⟩ := hH
  have P := t01CovarianceMatrix_symPkg S aux A D hD hσ hbound
  apply SharpLSI.le_lamG_of_trunc P.pos P.Csymm P.nn P.up P.col
  · intro i
    have hpow : 0 < ((i + 1 : ℕ) : ℝ) ^ (2 / (d : ℝ)) :=
      Real.rpow_pos_of_pos (by positivity) _
    exact (mul_pos aux.a_pos hpow).trans_le (aux.weyl (i + 1) (by omega))
  · exact t01_scalarRate_le_finite_gaussian S aux A hA b hmin ⟨σ, hσ, hbound⟩

end DGPS.Lipschitz
