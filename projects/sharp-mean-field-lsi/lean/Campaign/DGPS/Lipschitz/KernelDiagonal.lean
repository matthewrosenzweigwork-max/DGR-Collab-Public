import DGPS.Lipschitz.KernelApproximation

/-!
# Diagonal restrictions for kernel approximation (LIP012)

For the smoothed finite-rank kernels `K_R` of LIP011, the diagonal `k_R(x) = K_R(x,x)` converges
uniformly to `k(x) = K(x,x)`, and `∇k_R = (∇₁K_R + ∇₂K_R)(x,x)` with a bound uniform in `R`.
No convergence of the gradients `∇k_R` is claimed.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace

namespace DGPS.Lipschitz.KernelDiagonal

open DGPS DGPS.Lipschitz.KernelApproximation

variable {d : ℕ}

/-- The diagonal embedding has Euclidean Lipschitz constant `√2`, in the sharp form
`‖a + b‖ ≤ √2 · √(‖a‖² + ‖b‖²)`. -/
theorem norm_add_le_sqrt_two_mul (a b : Tangent d) :
    ‖a + b‖ ≤ Real.sqrt 2 * Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  rw [← Real.sqrt_mul (by norm_num)]
  apply Real.le_sqrt_of_sq_le
  nlinarith [norm_add_le a b, norm_nonneg a, norm_nonneg b, norm_nonneg (a + b),
    sq_nonneg (‖a‖ - ‖b‖)]

/-- Uniform convergence of values restricts to the diagonal. -/
theorem tendstoUniformly_diagonal {ι : Type*} {l : Filter ι} {F : ι → Torus d × Torus d → ℝ}
    {f : Torus d × Torus d → ℝ} (h : TendstoUniformly F f l) :
    TendstoUniformly (fun i (x : Torus d) => F i (x, x)) (fun x => f (x, x)) l :=
  h.comp (fun x : Torus d => (x, x))

/-- The diagonal of the smoothed kernel is differentiable in lifted coordinates, with gradient
`(∇₁ + ∇₂)(x,x)` (ordinary chain rule, applied to the finite sum defining `K_R` only). -/
theorem smoothK_diag_hasFDerivAt (S : Spec d) (A : Aux S) (D : KData d) (t : ℝ) (m : ℕ)
    (z : Tangent d) :
    HasFDerivAt (fun z : Tangent d =>
        smoothK S D t m (torusLift z.ofLp) (torusLift z.ofLp))
      (InnerProductSpace.toDual ℝ (Tangent d)
        (smoothG1 S A D t m (torusLift z.ofLp) (torusLift z.ofLp) +
          smoothG2 S A D t m (torusLift z.ofLp) (torusLift z.ofLp))) z := by
  set c : ℕ → ℕ → ℝ := fun i j => Real.exp (-(t * (S.lam i + S.lam j))) * TK S D.K i j with hc
  have hterm : ∀ i j, HasFDerivAt
      (fun z : Tangent d => c i j * (S.v i (torusLift z.ofLp) * S.v j (torusLift z.ofLp)))
      (c i j • (S.v i (torusLift z.ofLp) •
          InnerProductSpace.toDual ℝ (Tangent d) (A.g j (torusLift z.ofLp)) +
        S.v j (torusLift z.ofLp) •
          InnerProductSpace.toDual ℝ (Tangent d) (A.g i (torusLift z.ofLp)))) z := by
    intro i j
    exact ((A.gd i z).mul (A.gd j z)).const_mul (c i j)
  have hsum := HasFDerivAt.fun_sum (u := Finset.range (m + 1)) (fun i _ =>
    HasFDerivAt.fun_sum (u := Finset.range (m + 1)) (fun j _ => hterm i j))
  have hfun : (fun z : Tangent d =>
        smoothK S D t m (torusLift z.ofLp) (torusLift z.ofLp)) =
      fun z => ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        c i j * (S.v i (torusLift z.ofLp) * S.v j (torusLift z.ofLp)) := by
    funext z
    simp only [smoothK, hc]
  rw [hfun]
  convert hsum using 1
  simp only [smoothG1, smoothG2, map_add, map_sum, map_smul, ← Finset.sum_add_distrib, hc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [smul_add, smul_smul, smul_smul, add_comm]

end DGPS.Lipschitz.KernelDiagonal

namespace DGPS.Lipschitz

open DGPS DGPS.Lipschitz.KernelApproximation DGPS.Lipschitz.KernelDiagonal

/-- LIP012. For the smoothed kernels `K_R` of LIP011, the diagonals `k_R(x) = K_R(x,x)` converge
uniformly to `k(x) = K(x,x)`; each `k_R` is differentiable (in lifted coordinates) with gradient
`(∇₁K_R + ∇₂K_R)(x,x)`, whose norm is at most `√2` times the pointwise Euclidean norm
`√(‖∇₁K_R‖² + ‖∇₂K_R‖²)` of the full gradient, and `sup_R ‖∇k_R‖_∞ ≤ 2C` is finite.
No convergence of `∇k_R` is claimed. -/
theorem diagonal_restrictions_for_kernel_approximation {d : ℕ}
    {Φ : Torus d → ℝ} {LΦ : ℝ} (hd : 0 < d) (hL : 0 ≤ LΦ)
    (hΦ : TorusLipschitzWith LΦ Φ) {b : Torus d → Tangent d}
    (hb : IsWeakGradient (fun x => Real.log (WeightedGenerator.gibbsW Φ x)) b) :
    ∃ (S : Spec d) (A : Aux S), S.w = WeightedGenerator.gibbsW Φ ∧
      ∀ D : KData d, (∀ y, ∫ x, D.K x y ∂S.mu = 0) → (∀ x y, D.K x y = D.K y x) →
        ∃ (t : ℕ → ℝ) (m : ℕ → ℕ) (C : ℝ), (∀ R, 0 < t R) ∧ Antitone t ∧
          Filter.Tendsto t Filter.atTop (nhds 0) ∧ StrictMono m ∧ 0 ≤ C ∧
          (∀ R x y, |smoothK S D (t R) (m R) x y| ≤ C) ∧
          (∀ R x y, ‖smoothG1 S A D (t R) (m R) x y‖ ≤ C) ∧
          (∀ R x y, ‖smoothG2 S A D (t R) (m R) x y‖ ≤ C) ∧
          TendstoUniformly (fun R (x : Torus d) => smoothK S D (t R) (m R) x x)
            (fun x => D.K x x) Filter.atTop ∧
          (∀ R (z : Tangent d),
            HasFDerivAt (fun z : Tangent d =>
                smoothK S D (t R) (m R) (torusLift z.ofLp) (torusLift z.ofLp))
              (InnerProductSpace.toDual ℝ (Tangent d)
                (smoothG1 S A D (t R) (m R) (torusLift z.ofLp) (torusLift z.ofLp) +
                  smoothG2 S A D (t R) (m R) (torusLift z.ofLp) (torusLift z.ofLp))) z) ∧
          (∀ R (x : Torus d),
            ‖smoothG1 S A D (t R) (m R) x x + smoothG2 S A D (t R) (m R) x x‖ ≤
              Real.sqrt 2 * Real.sqrt (‖smoothG1 S A D (t R) (m R) x x‖ ^ 2 +
                ‖smoothG2 S A D (t R) (m R) x x‖ ^ 2)) ∧
          (∀ R (x : Torus d),
            ‖smoothG1 S A D (t R) (m R) x x + smoothG2 S A D (t R) (m R) x x‖ ≤ 2 * C) := by
  obtain ⟨S, A, hw⟩ := exists_spec_aux hd hL hΦ hb
  refine ⟨S, A, hw, fun D _ _ => ?_⟩
  obtain ⟨t, m, C, ht, hanti, htend, hm, hC, hK, hG1, hG2, -, -, hU, -⟩ :=
    smoothed_approximation' S A D
  refine ⟨t, m, C, ht, hanti, htend, hm, hC, hK, hG1, hG2,
    tendstoUniformly_diagonal (f := fun p => D.K p.1 p.2) hU,
    fun R z => smoothK_diag_hasFDerivAt S A D (t R) (m R) z,
    fun R x => norm_add_le_sqrt_two_mul _ _, fun R x => ?_⟩
  calc _ ≤ ‖smoothG1 S A D (t R) (m R) x x‖ + ‖smoothG2 S A D (t R) (m R) x x‖ :=
        norm_add_le _ _
    _ ≤ C + C := add_le_add (hG1 R x x) (hG2 R x x)
    _ = 2 * C := by ring

end DGPS.Lipschitz
