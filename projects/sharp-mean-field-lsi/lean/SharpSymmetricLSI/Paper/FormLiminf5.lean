import SharpSymmetricLSI.Paper.FormLiminf4
import SharpSymmetricLSI.Paper.GroundT1

/-!
# R33 (8.20) groundwork: integration by parts against `∇e_i(X_l)` with a Lipschitz multiplier

For `F ∈ W^{1,1}` and `h` bounded with bounded weak gradient,
`∫ ∇_l F · ∇e_i(X_l) h dμ^{⊗N} = λ_i ∫ F h e_i(X_l) dμ^{⊗N} - ∫ F ∇_l h · ∇e_i(X_l) dμ^{⊗N}`.
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

theorem ibp_mult {N : ℕ} (l : Fin N) (i : ℕ) {F : UnitAddTorus (Fin N × Fin d) → ℝ}
    {g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} (hF : IsWeakGrad F g)
    (hFi : Integrable F volume) (hgi : ∀ p, Integrable (fun y => g y p) volume)
    {h : UnitAddTorus (Fin N × Fin d) → ℝ} {gh : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    (hh : IsWeakGrad h gh) (hm : Measurable h) {B L : ℝ} (hB : ∀ y, |h y| ≤ B)
    (hghm : ∀ p, Measurable fun y => gh y p) (hL : ∀ y p, |gh y p| ≤ L) :
    ∫ X, ∑ k, g (flat X) (l, k) * h (flat X) * cgrad (eC i) (X l) k
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) =
      lam i * ∫ X, F (flat X) * h (flat X) * eC i (X l)
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) -
        ∫ X, F (flat X) * ∑ k, gh (flat X) (l, k) * cgrad (eC i) (X l) k
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) := by
  set μm := (μ : Measure (Torus d))
  have hFh := hF.mul_lip hFi hgi hh hm hB hghm hL
  have hFhi : Integrable (fun y => F y * h y) volume :=
    (integrable_bdd_mul hB hm.aestronglyMeasurable hFi).congr
      (Eventually.of_forall fun y => mul_comm _ _)
  have hgh : ∀ p, Integrable (fun y => g y p * h y) volume := fun p =>
    (integrable_bdd_mul hB hm.aestronglyMeasurable (hgi p)).congr
      (Eventually.of_forall fun y => mul_comm _ _)
  have hFgh : ∀ p, Integrable (fun y => F y * gh y p) volume := fun p =>
    (integrable_bdd_mul (fun y => hL y p) (hghm p).aestronglyMeasurable hFi).congr
      (Eventually.of_forall fun y => mul_comm _ _)
  have hGi : ∀ p, Integrable (fun y => g y p * h y + F y * gh y p) volume := fun p =>
    (hgh p).add (hFgh p)
  have hs := eigen_slice hyp hμ he hφ heC l i hFh hFhi hGi
  obtain ⟨Ce, hCe⟩ := exists_bound_cgrad (hφ i)
  obtain ⟨Be, hBe⟩ := exists_bound_of_contDiff (hφ i)
  have hcm : ∀ k : Fin d, Measurable fun X : Config N d => cgrad (eC i) (X l) k := fun k =>
    (measurable_cgrad (hφ i) k).comp (measurable_pi_apply l)
  have hem : Measurable fun X : Config N d => eC i (X l) :=
    (measurable_of_contDiff (hφ i)).comp (measurable_pi_apply l)
  have i1 : Integrable (fun X : Config N d => ∑ k, g (flat X) (l, k) * h (flat X) *
      cgrad (eC i) (X l) k) (Measure.pi fun _ : Fin N => μm) :=
    integrable_finsetSum _ fun k _ => integrable_pi_comp hyp hμ (hgh (l, k)) (hcm k)
      fun X => hCe _ _
  have i2 : Integrable (fun X : Config N d => F (flat X) * ∑ k, gh (flat X) (l, k) *
      cgrad (eC i) (X l) k) (Measure.pi fun _ : Fin N => μm) := by
    have := integrable_finsetSum (μ := Measure.pi fun _ : Fin N => μm) Finset.univ
      fun k _ => integrable_pi_comp hyp hμ (hFgh (l, k)) (hcm k) fun X => hCe _ _
    refine this.congr (Eventually.of_forall fun X => ?_)
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hsplit : ∀ X : Config N d, ∑ k, (g (flat X) (l, k) * h (flat X) + F (flat X) * gh (flat X) (l, k)) *
      cgrad (eC i) (X l) k = (∑ k, g (flat X) (l, k) * h (flat X) * cgrad (eC i) (X l) k) +
        F (flat X) * ∑ k, gh (flat X) (l, k) * cgrad (eC i) (X l) k := fun X => by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [hsplit] at hs
  rw [integral_add i1 i2] at hs
  linarith

end

end SharpLSI
