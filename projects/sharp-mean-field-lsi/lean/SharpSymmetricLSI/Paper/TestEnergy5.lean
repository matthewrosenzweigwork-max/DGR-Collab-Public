import SharpSymmetricLSI.Paper.TestEnergy2
import SharpSymmetricLSI.Paper.TestEnergy3
import SharpSymmetricLSI.Paper.ParticleForce

/-!
# R33 groundwork: the empirical mobility converges to `Λ` (manuscript (8.13))

`∫ ∇e_i·∇e_j dμ = λ_i δ_{ij}` (the eigenvalue equation), and `A_{N,ij} → λ_i δ_{ij}` in `L²(μ^{⊗N})`
with rate `N^{-1/2}`.
-/

open MeasureTheory Filter Topology Real

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
  (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j)
include hyp hμ he hφ heC

/-- `∫ ∇e_{i+1}·∇e_{j+1} dμ = λ_{i+1} δ_{ij}`. -/
theorem integral_mob_mean (i j : ℕ) :
    ∫ x, ∑ k, cgrad (eC (i + 1)) x k * cgrad (eC (j + 1)) x k ∂(μ : Measure (Torus d)) =
      if i = j then lam (i + 1) else 0 := by
  have hac := minimizer_ac hyp hμ
  have hw : ∀ m, ∀ᵐ x ∂(μ : Measure (Torus d)), weakGrad (e m) x = fun k => cgrad (eC m) x k :=
    fun m => hac.ae_le (weakGrad_ae_eq ((isWeakGrad_of_contDiff (hφ m)).congr_ae (heC m)))
  have h := he.eigen (i + 1) (e (j + 1)) (he.memH1 (j + 1))
  rw [he.orthonormal] at h
  have h2 : ∫ x, ∑ k, cgrad (eC (i + 1)) x k * cgrad (eC (j + 1)) x k ∂(μ : Measure (Torus d)) =
      ∫ x, ∑ k, weakGrad (e (i + 1)) x k * weakGrad (e (j + 1)) x k ∂(μ : Measure (Torus d)) := by
    refine integral_congr_ae ?_
    filter_upwards [hw (i + 1), hw (j + 1)] with x h1 h2
    rw [h1, h2]
  rw [h2, h]
  by_cases hij : i = j
  · subst hij; simp
  · have : i + 1 ≠ j + 1 := by omega
    simp [hij, this]

/-- **The `L²` LLN for the mobility.** -/
theorem integral_mob_sub_sq (i j : ℕ) : ∃ B : ℝ, ∀ N : ℕ, 1 ≤ N →
    ∫ X, (mobA eC N X i j - if i = j then lam (i + 1) else 0) ^ 2
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ B / N := by
  obtain ⟨Ci, hCi⟩ := exists_bound_cgrad (hφ (i + 1))
  obtain ⟨Cj, hCj⟩ := exists_bound_cgrad (hφ (j + 1))
  set g : Torus d → ℝ := fun x => ∑ k, cgrad (eC (i + 1)) x k * cgrad (eC (j + 1)) x k
  have hgm : Measurable g := Finset.measurable_sum _ fun k _ =>
    (measurable_cgrad (hφ (i + 1)) k).mul (measurable_cgrad (hφ (j + 1)) k)
  have hgb : ∀ x, |g x| ≤ d * (|Ci| * |Cj|) := fun x => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |cgrad (eC (i + 1)) x k * cgrad (eC (j + 1)) x k| ≤ ∑ _k : Fin d, |Ci| * |Cj| :=
          Finset.sum_le_sum fun k _ => by
            rw [abs_mul]
            exact mul_le_mul ((hCi x k).trans (le_abs_self _)) ((hCj x k).trans (le_abs_self _))
              (abs_nonneg _) (abs_nonneg _)
      _ = d * (|Ci| * |Cj|) := by simp
  refine ⟨(2 * (d * (|Ci| * |Cj|))) ^ 2, fun N hN => ?_⟩
  have := integral_avg_sub_sq (μ := (μ : Measure (Torus d))) hgm hgb hN
  rw [integral_mob_mean hyp hμ he hφ heC i j] at this
  exact this

end

end SharpLSI
