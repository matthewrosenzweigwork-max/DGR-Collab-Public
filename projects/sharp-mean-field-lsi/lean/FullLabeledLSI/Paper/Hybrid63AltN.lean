import FullLabeledLSI.Paper.Hybrid63AltM

/-!
# Proposition 6.3: `errT2, errT3, errT4, errT6, errT7` are small
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace SharpLSI.FL

variable {d : ℕ}

section
variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem errS26_small (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (R : ℕ)
    (e' : ℕ → Torus d → ℝ) (hae : ∀ j, e j =ᵐ[(μ : Measure (Torus d))] e' j)
    (J JR : ℕ) (hJ : JR ≤ J) (hsJR : ∀ i ∈ A.s R, i < JR) (L B τ K0 : ℝ) (hτ : 0 < τ)
    (hK0 : 0 ≤ K0) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ᶠ N in atTop, ∀ c : (Fin N → Fin (J + 1)) → ℝ, SpectralCoeff lam L c →
        ∑ j, c j ^ 2 ≤ B ^ 2 →
        ∫ X, polyEval e' c X ^ 2 ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ B ^ 2 →
          errT2 (μ : Measure (Torus d)) A lam R e' c δ ≤ τ ∧
          errT3 (μ : Measure (Torus d)) e' c δ ≤ τ ∧
          errT4 (μ : Measure (Torus d)) e' c δ ≤ τ ∧
          errT6 (μ : Measure (Torus d)) A R e' c δ ≤ τ ∧
          K0 * errT7 (μ : Measure (Torus d)) e' c δ ≤ τ := by
  -- uniform continuity of `ψ`
  have huc : UniformContinuousOn Sec6.psi (Set.Icc 0 (B ^ 2 + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous Real.continuous_mul_log.continuousOn
  obtain ⟨η, hη, hηH⟩ := Metric.uniformContinuousOn_iff.mp huc τ hτ
  set ε0 : ℝ := min (min (τ / (K0 + 1)) (η / 2)) 1 with hε0
  have hε0pos : 0 < ε0 := by
    have : 0 < K0 + 1 := by linarith
    positivity
  have hε01 : ε0 ≤ τ / (K0 + 1) := (min_le_left _ _).trans (min_le_left _ _)
  have hε02 : ε0 ≤ η / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hε03 : ε0 ≤ 1 := min_le_right _ _
  -- the four tests
  obtain ⟨δ1, hδ1, H1⟩ := joint_replace_e' hd hyp hr μ hμ e lam he e' hae J JR hJ (Phi1 JR)
    (continuous_Phi1 JR) (growth_Phi1 JR) L B τ hτ
  obtain ⟨δ0, hδ0, H0⟩ := joint_replace_e' hd hyp hr μ hμ e lam he e' hae J JR hJ (Phi0 JR)
    (continuous_Phi0 JR) (growth_Phi0 JR) L B ε0 hε0pos
  obtain ⟨δu, hδu, Hu⟩ := joint_replace_e' hd hyp hr μ hμ e lam he e' hae J JR hJ
    (PhiQuad JR (A.s R) (fun i j => A.a R i j / 2) 0)
    (continuous_PhiQuad JR _ _ _) (growth_PhiQuad JR _ _ _) L B τ hτ
  obtain ⟨δv, hδv, Hv⟩ := joint_replace_e' hd hyp hr μ hμ e lam he e' hae J JR hJ
    (PhiQuad JR (A.s R) (vQ A lam R) (-((1 / 2) * ∑ m ∈ A.s R, A.a R m m * lam (m + 1))))
    (continuous_PhiQuad JR _ _ _) (growth_PhiQuad JR _ _ _) L B τ hτ
  refine ⟨min (min δ1 δ0) (min δu δv), lt_min (lt_min hδ1 hδ0) (lt_min hδu hδv),
    fun δ hδ hδlt => ?_⟩
  have d1 : δ < δ1 := hδlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have d0 : δ < δ0 := hδlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have du : δ < δu := hδlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have dv : δ < δv := hδlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  filter_upwards [H1 δ hδ d1, H0 δ hδ d0, Hu δ hδ du, Hv δ hδ dv] with N h1 h0 hu hv
  intro c hc hB hq
  have e3 := h1 c hc hB
  have e7 := h0 c hc hB
  have e6 := hu c hc hB
  have e2 := hv c hc hB
  -- identify the errors with the Lemma 7.1 differences
  have hE3 : errT3 (μ : Measure (Torus d)) e' c δ ≤ τ := by
    unfold errT3; exact e3
  have hE7 : errT7 (μ : Measure (Torus d)) e' c δ ≤ ε0 := by
    unfold errT7; exact e7
  have hE6 : errT6 (μ : Measure (Torus d)) A R e' c δ ≤ τ := by
    unfold errT6
    simp_rw [uR_zext_castLE A R hJ hsJR]
    simpa [PhiQuad] using e6
  have hE2 : errT2 (μ : Measure (Torus d)) A lam R e' c δ ≤ τ := by
    unfold errT2
    simp_rw [vR_zext_castLE A lam R hJ hsJR]
    simpa [PhiQuad] using e2
  refine ⟨hE2, hE3, ?_, hE6, ?_⟩
  · -- ψ
    set mq : ℝ := ∫ X, polyEval e' c X ^ 2 ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d)))
      with hmq
    set mh : ℝ := ∫ w, hybEval e' c δ w ^ 2 ∂hybMeasure (μ : Measure (Torus d)) N J with hmh
    have hmq0 : 0 ≤ mq := integral_nonneg fun X => sq_nonneg _
    have hmh0 : 0 ≤ mh := integral_nonneg fun w => sq_nonneg _
    have habs : |mq - mh| ≤ ε0 := by unfold errT7 at hE7; exact hE7
    have hmh1 : mh ≤ B ^ 2 + 1 := by
      have := (abs_le.1 habs).1
      linarith
    have hd' : dist mq mh < η := by
      rw [Real.dist_eq]; linarith
    have := hηH mq ⟨hmq0, by linarith⟩ mh ⟨hmh0, hmh1⟩ hd'
    rw [Real.dist_eq] at this
    unfold errT4
    exact this.le
  · calc K0 * errT7 (μ : Measure (Torus d)) e' c δ ≤ K0 * ε0 :=
          mul_le_mul_of_nonneg_left hE7 hK0
      _ ≤ K0 * (τ / (K0 + 1)) := mul_le_mul_of_nonneg_left hε01 hK0
      _ ≤ τ := by
          rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
          nlinarith

end

end SharpLSI.FL

end
