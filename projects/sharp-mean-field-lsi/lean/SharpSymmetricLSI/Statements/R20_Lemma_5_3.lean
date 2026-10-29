import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D15_Forces
import SharpSymmetricLSI.Paper.ParticleForce
import SharpSymmetricLSI.Paper.Sec5_6
import SharpSymmetricLSI.Statements.R16_Lemma_4_2

/-!
# R20: Lemma 5.3 (`lem:force-exponential`), exponential force bound; (5.11), (5.12)

Manuscript (5.11), (5.12), Lemma 5.3, (5.13)–(5.15). Assume (1.2), `r_* > 0`, `μ` the minimizer.
* (5.11)–(5.12): `b_Δ = -∇(W*μ)` (an identity of weak gradients, hence a.e.); `∇ᵢU_N = N^{-1}(∑_{l≠i} b(Xᵢ,X_l) + b_Δ(Xᵢ))` a.e.;
  `∫ b(x,y) dμ(y) = 0` for a.e. `x`.
* (5.13) `∫ e^{a_0|∇U_N|²} dμ^{⊗N} ≤ C` uniformly in `N`, for some `a_0 > 0`.
* (5.14) `E_ν|∇U_N|² ≤ C(H(ν|P_N) + 1)` and (5.15) `I(ν|μ^{⊗N}) ≤ 2I(ν|P_N) + C(H(ν|P_N) + 1)`
  for every symmetric `ν` of finite relative entropy.
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- (5.11), (5.12): the particle force. -/
theorem particle_force {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) :
    (∀ᵐ x ∂haar d, ∀ k, bDiag W μ x k = -weakGrad (convMeas W μ) x k) ∧
    (∀ᵐ x ∂(μ : Measure (Torus d)), ∀ k, ∫ y, bForce W μ x y k ∂(μ : Measure (Torus d)) = 0) ∧
    ∀ N : ℕ, 1 ≤ N → ∀ᵐ X ∂(volume : Measure (Config N d)), ∀ i k,
      weakGradC (Ucentered W μ N) X i k =
        (N : ℝ)⁻¹ * ((∑ l, if l ≠ i then bForce W μ (X i) (X l) k else 0) + bDiag W μ (X i) k) := by
  exact particle_force_aux hyp hμ

/-- Lemma 5.3, (5.13)–(5.15). -/
theorem force_exponential {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧ ∀ N : ℕ, 1 ≤ N →
      ∫⁻ X, ENNReal.ofReal (Real.exp (a₀ * gradSqC (Ucentered W μ N) X))
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ ENNReal.ofReal C ∧
      ∀ ν : Measure (Config N d), IsProbabilityMeasure ν → IsSymmetricMeasure ν →
        klDiv ν (gibbs V W N) ≠ ⊤ →
        ∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W μ N) X) ∂ν ≤
            ENNReal.ofReal C * (klDiv ν (gibbs V W N) + 1) ∧
        fisherInfoC ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤
          2 * fisherInfoC ν (gibbs V W N) + ENNReal.ofReal C * (klDiv ν (gibbs V W N) + 1) := by
  exact force_exponential_of hyp hd hμ (gap_ge_entropy hd hyp hr hμ)

end SharpLSI
