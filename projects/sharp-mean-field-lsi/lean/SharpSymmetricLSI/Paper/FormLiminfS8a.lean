import SharpSymmetricLSI.Paper.TestEnergy7
import SharpSymmetricLSI.Paper.LamSym2
import SharpSymmetricLSI.Paper.LamSym7
import SharpSymmetricLSI.Paper.LamSym8
import SharpSymmetricLSI.Paper.FormLiminf8

/-!
# R33: uniform fourth moment of `Z_{N,q+1}` under the Gibbs measure

`sup_{N ≥ 1} E_{P_N} (N^{-1/2} ∑_l e_{q+1}(X_l))⁴ < ∞` (`fourth_moment_zq`): Hoeffding's
square-exponential moment under `μ^{⊗N}` (`exp_moment_linTest`, for the shifted family
`j ↦ e_{j+q}` and the single test vector `1`), Hölder with the partition-function bound
(`gibbs_lintegral_exp_le`), and `fourth_moment_of_exp`.
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- `∫ e_{j+1} dμ = 0` for the continuous representatives. -/
theorem integral_eC_succ_eq_zero {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (heC : ∀ j, eC j =ᵐ[haar d] e j) (j : ℕ) :
    ∫ x, eC (j + 1) x ∂(μ : Measure (Torus d)) = 0 := by
  have hac := minimizer_ac hyp hμ
  rw [integral_congr_ae (hac.ae_le (heC (j + 1)))]
  have h := he.orthonormal (j + 1) 0
  rw [if_neg (Nat.succ_ne_zero j), he.zero] at h
  simpa using h

theorem fourth_moment_zq {V W KV KW} (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j)
    (hpart : ∃ Bp p : ℝ, 1 < p ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ X, (rexp (-Ucentered W μ N X) / centeredPartition W μ N) ^ p
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ Bp) (q : ℕ) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
      Integrable (fun X => ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l)) ^ 4) (gibbs V W N) ∧
      ∫ X, ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l)) ^ 4 ∂gibbs V W N ≤ K := by
  obtain ⟨Bp, p, hp, hBp⟩ := hpart
  -- the shifted family `j ↦ e_{j+q}` and the test vector `1 ∈ ℝ^1`
  set eS : ℕ → Torus d → ℝ := fun j => eC (j + q)
  have hφS : ∀ j, ContDiff ℝ 1 (eS j ∘ liftT) := fun j => hφ (j + q)
  have hcS : ∀ j, ∫ x, eS (j + 1) x ∂(μ : Measure (Torus d)) = 0 := fun j => by
    have := integral_eC_succ_eq_zero hyp hμ he heC (j + q)
    simpa [eS, show j + 1 + q = j + q + 1 by ring] using this
  set v : Fin 1 → ℝ := fun _ => 1
  have hlin : ∀ N (X : Config N d), linTest eS N 1 v X =
      (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l) := fun N X => by
    rw [linTest_eq]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [linG, eS, v, add_comm]
  obtain ⟨a, ha, hexp⟩ := exp_moment_linTest hφS v hcS (μ := (μ : Measure (Torus d)))
  set q' := p.conjExponent
  have hq' : 0 < q' := (Real.HolderConjugate.conjExponent hp).symm.pos
  have hp0 : 0 < p := by linarith
  set B : ℝ≥0∞ := ENNReal.ofReal Bp ^ (1 / p) * gaussSqConst ^ (1 / q')
  have hBt : B ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) gaussSqConst_ne_top)
  refine ⟨2 / (a / q') ^ 2 * B.toReal, fun N hN => ?_⟩
  have hYm : Measurable (fun X : Config N d => linTest eS N 1 v X) := by
    have : (fun X : Config N d => linTest eS N 1 v X) =
        fun X => (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, linG eS v (X l) := funext (linTest_eq eS N 1 v)
    rw [this]
    exact measurable_const.mul (Finset.measurable_sum _ fun l _ =>
      (measurable_linG hφS v).comp (measurable_pi_apply l))
  have hgib := gibbs_lintegral_exp_le hyp hμ hp N (hBp N hN) hYm.aemeasurable ha
  have hle : ∫⁻ X, ENNReal.ofReal (rexp (a / q' * linTest eS N 1 v X ^ 2)) ∂gibbs V W N ≤ B :=
    hgib.trans (mul_le_mul_right (ENNReal.rpow_le_rpow (hexp N hN) (by positivity)) _)
  have h4 := fourth_moment_of_exp hYm.aestronglyMeasurable (div_pos ha hq') hBt hle
  simp only [hlin] at h4
  exact h4

end SharpLSI
