import SharpSymmetricLSI.Paper.FormLiminf3

/-!
# R33 (8.20) groundwork: the eigenvalue equation in one particle variable for `W^{1,1}` functions
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
  (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j)
include hyp hμ he hφ heC

/-- **`∫ ∇_lΦ · ∇e_i(X_l) dμ^{⊗N} = λ_i ∫ e_i(X_l) Φ dμ^{⊗N}`** for `Φ ∈ W^{1,1}`. -/
theorem eigen_slice {N : ℕ} (l : Fin N) (i : ℕ) {Φ : UnitAddTorus (Fin N × Fin d) → ℝ}
    {G : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} (hΦ : IsWeakGrad Φ G)
    (hΦi : Integrable Φ volume) (hGi : ∀ p, Integrable (fun y => G y p) volume) :
    ∫ X, ∑ k, G (flat X) (l, k) * cgrad (eC i) (X l) k
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) =
      lam i * ∫ X, Φ (flat X) * eC i (X l) ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨F, Gs, hFs, hFw, hFm, hGm, hF1, hG1⟩ := exists_smooth_approx hΦ hΦi hGi
  have hF1' : ∀ n, ContDiff ℝ 1 (F n ∘ liftT) := fun n => (hFs n).of_le (by simp)
  obtain ⟨Ce, hCe⟩ := exists_bound_cgrad (hφ i)
  obtain ⟨Be, hBe⟩ := exists_bound_of_contDiff (hφ i)
  have hcm : ∀ k : Fin d, Measurable fun X : Config N d => cgrad (eC i) (X l) k := fun k =>
    (measurable_cgrad (hφ i) k).comp (measurable_pi_apply l)
  have hem : Measurable fun X : Config N d => eC i (X l) :=
    (measurable_of_contDiff (hφ i)).comp (measurable_pi_apply l)
  -- the smooth approximants: classical gradient = `Gs n` a.e.
  have hGae : ∀ n, (fun y => cgrad (F n) y) =ᵐ[volume] Gs n := fun n =>
    (weakGrad_ae_eq (isWeakGrad_of_contDiff (hF1' n))).symm.trans (weakGrad_ae_eq (hFw n))
  have hFint : ∀ n, Integrable (F n) volume := fun n => by
    obtain ⟨B, hB⟩ := exists_bound_of_contDiff (hF1' n)
    exact integrable_of_bdd_meas (hFm n) hB
  have hGint : ∀ n p, Integrable (fun y => Gs n y p) volume := fun n p => by
    obtain ⟨B, hB⟩ := exists_bound_cgrad (hF1' n)
    refine (integrable_of_bdd_meas (measurable_cgrad (hF1' n) p) fun y => hB y p).congr ?_
    filter_upwards [hGae n] with y hy
    exact congrFun hy p
  -- the identity for each `n`
  have hn : ∀ n, ∑ k, ∫ X, Gs n (flat X) (l, k) * cgrad (eC i) (X l) k ∂Measure.pi (fun _ : Fin N => μm) =
      lam i * ∫ X, F n (flat X) * eC i (X l) ∂Measure.pi (fun _ : Fin N => μm) := fun n => by
    have h := eigen_slice_smooth hyp hμ he hφ heC l i (hF1' n)
    rw [← integral_finsetSum _ fun k _ => integrable_pi_comp hyp hμ (hGint n (l, k)) (hcm k)
      fun X => (hCe _ _)]
    have hae := ae_pi_of_ae_volume hyp hμ (μ := μ) (hGae n)
    rw [← integral_congr_ae (hae.mono fun X hX =>
      Finset.sum_congr rfl fun k _ => by rw [← congrFun hX (l, k)]), h]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun X => mul_comm _ _)
  -- limits
  have hL : Tendsto (fun n => ∑ k, ∫ X, Gs n (flat X) (l, k) * cgrad (eC i) (X l) k
      ∂Measure.pi (fun _ : Fin N => μm)) atTop
      (𝓝 (∑ k, ∫ X, G (flat X) (l, k) * cgrad (eC i) (X l) k ∂Measure.pi (fun _ : Fin N => μm))) :=
    tendsto_finset_sum _ fun k _ => tendsto_integral_pi_of_L1 hyp hμ (fun n => hGint n (l, k))
      (hGi (l, k)) (hG1 (l, k)) (hcm k) fun X => hCe _ _
  have hR : Tendsto (fun n => lam i * ∫ X, F n (flat X) * eC i (X l)
      ∂Measure.pi (fun _ : Fin N => μm)) atTop
      (𝓝 (lam i * ∫ X, Φ (flat X) * eC i (X l) ∂Measure.pi (fun _ : Fin N => μm))) :=
    (tendsto_integral_pi_of_L1 hyp hμ hFint hΦi hF1 hem fun X => hBe _).const_mul _
  rw [integral_finsetSum _ fun k _ => integrable_pi_comp hyp hμ (hGi (l, k)) (hcm k)
    fun X => hCe _ _]
  exact tendsto_nhds_unique (hL.congr hn) hR

end

end SharpLSI
