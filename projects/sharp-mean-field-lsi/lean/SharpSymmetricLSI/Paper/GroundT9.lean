import SharpSymmetricLSI.Paper.GroundT8
import SharpSymmetricLSI.Paper.R37Rescaling

/-!
# R30 groundwork: rescaled ground states and symmetry

* `H¹(μ^{⊗N})` and `|∇·|²` under multiplication by a constant.
* `U_N` is permutation invariant, so `f √p` is symmetric for symmetric `f`.
* `Ψ'_N = f √(e^{-U_N}/K')` for any `K' > 0`: `Ψ'_N = √(K_N/K') Ψ_N`.
-/

open MeasureTheory InformationTheory Set Filter Topology Real
open scoped ENNReal NNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem Ucentered_perm (μ : Measure (Torus d)) {N : ℕ} (σ : Equiv.Perm (Fin N)) (X : Config N d) :
    Ucentered W μ N (X ∘ σ) = Ucentered W μ N X := by
  unfold Ucentered
  congr 1
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp σ (fun i => ∑ j, centeredKernel W μ (X i) (X (σ j)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Equiv.sum_comp σ (fun j => centeredKernel W μ (X i) (X j))

section
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {N : ℕ}
include hyp hμ

theorem memH1C_pi_const_mul {u : Config N d → ℝ}
    (hu : MemH1C (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) u) (c : ℝ) :
    MemH1C (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) (fun X => c * u X) := by
  have hac := pi_map_flat_ac hyp hμ (N := N)
  refine ⟨⟨_, (isWeakGrad_weakGrad hu.1).const_mul c⟩, hu.2.1.const_mul c, ?_⟩
  refine (hu.2.2.const_mul |c|).ae_eq ?_
  filter_upwards [hac.ae_le (weakGrad_const_mul_ae hu.1 c)] with y hy
  show |c| * Real.sqrt (sqNorm (weakGrad (u ∘ unflat) y)) =
    Real.sqrt (sqNorm (weakGrad ((fun X => c * u X) ∘ unflat) y))
  rw [show ((fun X => c * u X) ∘ unflat) = fun y => c * (u ∘ unflat) y from rfl, hy]
  unfold sqNorm
  simp_rw [mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem gradSqC_const_mul_ae {u : Config N d → ℝ} (hu : HasWeakGrad (u ∘ unflat)) (c : ℝ) :
    ∀ᵐ X ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))),
      gradSqC (fun X => c * u X) X = c ^ 2 * gradSqC u X := by
  filter_upwards [ae_pi_of_ae_volume hyp hμ (weakGrad_const_mul_ae hu c)] with X hX
  rw [gradSqC_eq_sqNorm, gradSqC_eq_sqNorm,
    show ((fun X => c * u X) ∘ unflat) = fun y => c * (u ∘ unflat) y from rfl, hX]
  unfold sqNorm
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]

end

end SharpLSI
