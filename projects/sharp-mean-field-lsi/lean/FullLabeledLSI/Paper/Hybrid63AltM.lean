import FullLabeledLSI.Paper.Hybrid63AltL
import FullLabeledLSI.Statements.S26_Lemma_7_1

/-!
# Proposition 6.3: the terms controlled by Lemma 7.1

`errT2, errT3, errT4, errT6, errT7` are small for `δ` small and `N` large, uniformly in the
coefficients: the four tests `s² log s²`, `s²`, `s² u_R(z)`, `s² v_R(z)` of Lemma 7.1 and the
uniform continuity of `ψ(t) = t log t` on a compact interval.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace SharpLSI.FL

variable {d : ℕ}

section
variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- Lemma 7.1 for the good basis `e'`. -/
theorem joint_replace_e' (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (e' : ℕ → Torus d → ℝ) (hae : ∀ j, e j =ᵐ[(μ : Measure (Torus d))] e' j)
    (J JR : ℕ) (hJ : JR ≤ J) (Φ : ℝ × (Fin JR → ℝ) → ℝ) (hΦ : Continuous Φ)
    (hgrowth : ∃ (K : ℝ) (k : ℕ), ∀ p, |Φ p| ≤ K * (1 + ‖p‖) ^ k) (L B : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ᶠ N in atTop, ∀ c : (Fin N → Fin (J + 1)) → ℝ, SpectralCoeff lam L c →
        ∑ j, c j ^ 2 ≤ B ^ 2 →
          |∫ X, Φ (polyEval e' c X, fun m => Zlow e' c δ X (Fin.castLE hJ m))
              ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) -
            ∫ w, Φ (hybEval e' c δ w, fun m => Glow c δ w (Fin.castLE hJ m))
              ∂hybMeasure (μ : Measure (Torus d)) N J| ≤ ε := by
  intro ε hε
  obtain ⟨δ₀, hδ₀, H⟩ := joint_replace hd hyp hr μ hμ e lam he J JR hJ Φ hΦ hgrowth L B ε hε
  refine ⟨δ₀, hδ₀, fun δ hδ hδδ => ?_⟩
  filter_upwards [H δ hδ hδδ] with N hN c hc hB
  rw [← integral_orig_congr hae c δ hJ Φ, ← integral_hyb_congr hae c δ hJ Φ]
  exact hN c hc hB

theorem zext_castLE {J JR : ℕ} (hJ : JR ≤ J) (z : Fin J → ℝ) {i : ℕ} (hi : i < JR) :
    zext (fun m : Fin JR => z (Fin.castLE hJ m)) i = zext z i := by
  unfold zext
  simp only [hi, dite_true, Nat.lt_of_lt_of_le hi hJ]
  rfl

theorem vR_zext_castLE {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}
    (A : FiniteRankApprox W μ e) (lam : ℕ → ℝ) (R : ℕ) {J JR : ℕ} (hJ : JR ≤ J)
    (hs : ∀ i ∈ A.s R, i < JR) (z : Fin J → ℝ) :
    vR A lam R (zext z) = quadFA (A.s R) (vQ A lam R)
      (zext (fun m : Fin JR => z (Fin.castLE hJ m))) +
      (-((1 / 2) * ∑ m ∈ A.s R, A.a R m m * lam (m + 1))) := by
  rw [vR_eq_quad, quadF_congr (A.s R) (vQ A lam R) (z' := zext z)
    (fun i hi => zext_castLE hJ z (hs i hi))]
  ring

theorem uR_zext_castLE {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}
    (A : FiniteRankApprox W μ e) (R : ℕ) {J JR : ℕ} (hJ : JR ≤ J)
    (hs : ∀ i ∈ A.s R, i < JR) (z : Fin J → ℝ) :
    uR A R (zext z) = quadFA (A.s R) (fun i j => A.a R i j / 2)
      (zext (fun m : Fin JR => z (Fin.castLE hJ m))) + 0 := by
  rw [uR_eq_quadA, quadF_congr (A.s R) (fun i j => A.a R i j / 2) (z' := zext z)
    (fun i hi => zext_castLE hJ z (hs i hi))]
  ring

end

end SharpLSI.FL

end
