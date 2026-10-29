import SharpSymmetricLSI.Paper.FormLiminf1
import SharpSymmetricLSI.Paper.TestEnergy5

/-!
# R33 (8.20) groundwork: the eigenvalue equation in one particle variable (smooth case)

For `Φ` with `C¹` lift on `𝕋^{N×d}`,
`∫ ∇_lΦ · ∇e_i(X_l) dμ^{⊗N} = λ_i ∫ e_i(X_l) Φ dμ^{⊗N}`
(slice in the variable `X_l`, the weak eigenvalue equation, Fubini).
-/

open MeasureTheory Filter Topology Real

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
  (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j)
include hyp hμ he hφ heC

/-- The weak eigenvalue equation for a `C¹` test function, with the `C¹` representatives. -/
theorem eigen_C1 (i : ℕ) {ψ : Torus d → ℝ} (hψ : ContDiff ℝ 1 (ψ ∘ liftT)) :
    ∫ y, ∑ k, cgrad ψ y k * cgrad (eC i) y k ∂(μ : Measure (Torus d)) =
      lam i * ∫ y, eC i y * ψ y ∂(μ : Measure (Torus d)) := by
  have hac := minimizer_ac hyp hμ
  have hw : ∀ m, ∀ᵐ x ∂(μ : Measure (Torus d)), weakGrad (e m) x = fun k => cgrad (eC m) x k :=
    fun m => hac.ae_le (weakGrad_ae_eq ((isWeakGrad_of_contDiff (hφ m)).congr_ae (heC m)))
  have hψw : ∀ᵐ x ∂(μ : Measure (Torus d)), weakGrad ψ x = fun k => cgrad ψ x k :=
    hac.ae_le (weakGrad_ae_eq (isWeakGrad_of_contDiff hψ))
  have hP : IsProbabilityMeasure (μ : Measure (Torus d)) := inferInstance
  have hH1 : MemH1 (μ : Measure (Torus d)) ψ := memH1_of_contDiff_ac hac hψ
  have h := he.eigen i ψ hH1
  have h1 : ∫ y, ∑ k, cgrad ψ y k * cgrad (eC i) y k ∂(μ : Measure (Torus d)) =
      ∫ x, ∑ k, weakGrad (e i) x k * weakGrad ψ x k ∂(μ : Measure (Torus d)) := by
    refine integral_congr_ae ?_
    filter_upwards [hw i, hψw] with x h1 h2
    rw [h1, h2]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have h2 : ∫ y, eC i y * ψ y ∂(μ : Measure (Torus d)) = ∫ x, e i x * ψ x ∂(μ : Measure (Torus d)) := by
    refine integral_congr_ae ?_
    filter_upwards [hac.ae_le (heC i)] with x hx
    rw [hx]
  rw [h1, h, h2]

/-- **The eigenvalue equation in the variable `X_l`** (smooth case). -/
theorem eigen_slice_smooth {N : ℕ} (l : Fin N) (i : ℕ) {Φ : UnitAddTorus (Fin N × Fin d) → ℝ}
    (hΦ : ContDiff ℝ 1 (Φ ∘ liftT)) :
    ∫ X, ∑ k, cgrad Φ (flat X) (l, k) * cgrad (eC i) (X l) k
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) =
      lam i * ∫ X, eC i (X l) * Φ (flat X) ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨CΦ, hCΦ⟩ := exists_bound_cgrad hΦ
  obtain ⟨BΦ, hBΦ⟩ := exists_bound_of_contDiff hΦ
  obtain ⟨Ce, hCe⟩ := exists_bound_cgrad (hφ i)
  obtain ⟨Be, hBe⟩ := exists_bound_of_contDiff (hφ i)
  have hmΦ : Measurable Φ := measurable_of_contDiff hΦ
  have hgm : Measurable fun X : Config N d =>
      ∑ k, cgrad Φ (flat X) (l, k) * cgrad (eC i) (X l) k :=
    Finset.measurable_sum _ fun k _ => ((measurable_cgrad hΦ (l, k)).comp measurable_flat).mul
      ((measurable_cgrad (hφ i) k).comp (measurable_pi_apply l))
  have hfm : Measurable fun X : Config N d => eC i (X l) * Φ (flat X) :=
    ((measurable_of_contDiff (hφ i)).comp (measurable_pi_apply l)).mul (hmΦ.comp measurable_flat)
  have hgi : Integrable (fun X : Config N d => ∑ k, cgrad Φ (flat X) (l, k) * cgrad (eC i) (X l) k)
      (Measure.pi fun _ : Fin N => μm) :=
    integrable_of_bdd hgm (C := d * (|CΦ| * |Ce|)) fun X => by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k, |cgrad Φ (flat X) (l, k) * cgrad (eC i) (X l) k| ≤ ∑ _k : Fin d, |CΦ| * |Ce| :=
            Finset.sum_le_sum fun k _ => by
              rw [abs_mul]
              exact mul_le_mul ((hCΦ _ _).trans (le_abs_self _)) ((hCe _ _).trans (le_abs_self _))
                (abs_nonneg _) (abs_nonneg _)
        _ = d * (|CΦ| * |Ce|) := by simp
  have hfi : Integrable (fun X : Config N d => eC i (X l) * Φ (flat X))
      (Measure.pi fun _ : Fin N => μm) :=
    integrable_of_bdd hfm (C := |Be| * |BΦ|) fun X => by
      rw [abs_mul]
      exact mul_le_mul ((hBe _).trans (le_abs_self _)) ((hBΦ _).trans (le_abs_self _))
        (abs_nonneg _) (abs_nonneg _)
  rw [integral_update_resample μm l hgi, integral_update_resample μm l hfi, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  simp only [Function.update_self]
  have hs := eigen_C1 hyp hμ he hφ heC i (contDiff_sliceF hΦ X l)
  simp only [cgrad_sliceF hΦ X l] at hs
  exact hs

end

end SharpLSI
