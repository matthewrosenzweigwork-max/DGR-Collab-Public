import DGPS.Lipschitz.T01FiniteRankBridge

/-!
# Finite-rank approximation retaining its smoothing witnesses

The same parameters feed the rank comparison, residual force and changed-measure estimates.
-/

namespace DGPS.Lipschitz

open MeasureTheory Filter Topology KernelApproximation

/-- Retain the current smoothing estimates on the actual legacy approximation witness. -/
theorem exists_legacy_finiteRankApprox_with_smoothing {d : ℕ}
    (J : InteractionData d) (S : Spec d) (aux : Aux S) (D : KData d)
    (hD : D.K = centeredKernel J S.mu) :
    ∃ (t : ℕ → ℝ) (m : ℕ → ℕ) (C : ℝ)
      (F : SharpLSI.FL.FiniteRankApprox J.W S.mu S.v),
      (∀ R, 0 < t R) ∧ Antitone t ∧ Tendsto t atTop (𝓝 0) ∧ StrictMono m ∧
      (∀ R, F.s R = Finset.range (m R)) ∧
      (∀ R i j, F.a R i j = positiveKernelCoefficient S D (t R) (m R) i j) ∧
      0 ≤ C ∧
      (∀ R x y, |smoothK S D (t R) (m R) x y| ≤ C) ∧
      (∀ R x y, ‖smoothG1 S aux D (t R) (m R) x y‖ ≤ C) ∧
      (∀ R x y, ‖smoothG2 S aux D (t R) (m R) x y‖ ≤ C) ∧
      TendstoUniformly (fun R (p : Torus d × Torus d) => smoothK S D (t R) (m R) p.1 p.2)
        (fun p => D.K p.1 p.2) atTop ∧
      Tendsto (fun R =>
        ∫ p, (D.K p.1 p.2 - smoothK S D (t R) (m R) p.1 p.2) ^ 2 ∂S.mu.prod S.mu +
        ∫ p, ‖D.G1 p.1 p.2 - smoothG1 S aux D (t R) (m R) p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu +
        ∫ p, ‖D.G2 p.1 p.2 - smoothG2 S aux D (t R) (m R) p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu)
        atTop (𝓝 0) := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  have hsym : ∀ x y, D.K x y = D.K y x := by
    intro x y
    rw [hD]
    exact centeredKernel_symm J S.mu x y
  have hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0 := by
    intro y
    simp only [hD, centeredKernel_symm J S.mu _ y]
    exact integral_centeredKernel_right J S.mu y
  obtain ⟨t, m, C, ht, hanti, htend, hm, hC, hK, h1, h2, -, -, hU, hH1⟩ :=
    smoothed_approximation' S aux D
  have hApprox := legacy_isKernelApprox_of_smoothing J S aux D hD t m hC hK h1 h2 hU hH1
  let F : SharpLSI.FL.FiniteRankApprox J.W S.mu S.v := {
    s := fun R => Finset.range (m R)
    a := fun R => positiveKernelCoefficient S D (t R) (m R)
    symm := fun R => positiveKernelCoefficient_symm S D hsym (t R) (m R)
    supp := fun R i j => positiveKernelCoefficient_support S D (t R) (m R) i j
    approx := by
      have he : (fun R x y => ∑ i ∈ Finset.range (m R), ∑ j ∈ Finset.range (m R),
          positiveKernelCoefficient S D (t R) (m R) i j * S.v (i + 1) x * S.v (j + 1) y) =
          (fun R => smoothK S D (t R) (m R)) := by
        funext R x y
        exact (smoothK_eq_positive_block S aux D hc hsym (t R) (m R) x y).symm
      rw [he]
      exact hApprox }
  exact ⟨t, m, C, F, ht, hanti, htend, hm, fun _ => rfl,
    fun _ _ _ => rfl, hC, hK, h1, h2, hU, hH1⟩

end DGPS.Lipschitz
