import FullLabeledLSI.Paper.Hybrid63AltG
import FullLabeledLSI.Paper.HybridGroundAlt
import FullLabeledLSI.Paper.HybridMatrix
import FullLabeledLSI.Infra.HypercontrTorus7
import FullLabeledLSI.Paper.Hybrid63AltB

/-!
# Proposition 6.3, steps R2, R3, R5, R6: the per-`N` inequality

`master_alg`: pure real bookkeeping. `Jexpr_eq_e'`: `Jexpr` through a measurable bounded basis.
`per_N`: `-(error terms) ≤ Jexpr` for one `N`, one `δ`, from the hybrid inequality (7.17).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace SharpLSI.FL

variable {d : ℕ}

theorem master_alg {E Vq Vl Vh Uq Ul Uh I1q I1h mq mh Eq Eh ρ K : ℝ} (hρ : 0 ≤ ρ)
    (hEq : Eq = max (I1q - Sec6.psi mq) 0) (hEh : Eh = max (I1h - Sec6.psi mh) 0)
    (hyb : 0 ≤ E + Vh - ρ / 2 * (Eh + Uh + K * mh)) :
    -(|Vq - Vl| + |Vl - Vh| + ρ / 2 * (|I1q - I1h| + |Sec6.psi mq - Sec6.psi mh| +
      |Uq - Ul| + |Ul - Uh| + |K| * |mq - mh|)) ≤ E + Vq - ρ / 2 * (Eq + Uq + K * mq) := by
  have hE : |Eq - Eh| ≤ |I1q - I1h| + |Sec6.psi mq - Sec6.psi mh| := by
    rw [hEq, hEh]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    have := abs_sub (I1q - I1h) (Sec6.psi mq - Sec6.psi mh)
    calc |I1q - Sec6.psi mq - (I1h - Sec6.psi mh)| =
        |(I1q - I1h) - (Sec6.psi mq - Sec6.psi mh)| := by ring_nf
      _ ≤ _ := this
  have hU : |Uq - Uh| ≤ |Uq - Ul| + |Ul - Uh| := by
    have := abs_add_le (Uq - Ul) (Ul - Uh)
    simpa using this
  have hV : |Vq - Vh| ≤ |Vq - Vl| + |Vl - Vh| := by
    have := abs_add_le (Vq - Vl) (Vl - Vh)
    simpa using this
  set X : ℝ := (Eq - Eh) + (Uq - Uh) + K * (mq - mh) with hX
  have hXabs : |X| ≤ |I1q - I1h| + |Sec6.psi mq - Sec6.psi mh| + |Uq - Ul| + |Ul - Uh| +
      |K| * |mq - mh| := by
    have h1 := abs_add_le ((Eq - Eh) + (Uq - Uh)) (K * (mq - mh))
    have h2 := abs_add_le (Eq - Eh) (Uq - Uh)
    rw [abs_mul] at h1
    rw [hX]
    linarith
  have hρX : ρ / 2 * X ≤ ρ / 2 * (|I1q - I1h| + |Sec6.psi mq - Sec6.psi mh| + |Uq - Ul| +
      |Ul - Uh| + |K| * |mq - mh|) :=
    mul_le_mul_of_nonneg_left ((le_abs_self X).trans hXabs) (by linarith)
  have hVq : -(|Vq - Vl| + |Vl - Vh|) ≤ Vq - Vh := by
    have := neg_abs_le (Vq - Vh); linarith
  have : E + Vq - ρ / 2 * (Eq + Uq + K * mq) =
      (E + Vh - ρ / 2 * (Eh + Uh + K * mh)) + (Vq - Vh) - ρ / 2 * X := by
    rw [hX]; ring
  rw [this]
  linarith

section expr
variable {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
  {e e' : ℕ → Torus d → ℝ}

theorem fluct_congr {N : ℕ} (X : Config N d) (h : ∀ l j, e j (X l) = e' j (X l)) (n : ℕ) :
    fluct e N n X = fluct e' N n X := by
  unfold fluct
  rw [Finset.sum_congr rfl fun l _ => h l _]

theorem Jexpr_eq_e' (A : FiniteRankApprox W μ e) (lam : ℕ → ℝ) (CR : ℕ → ℕ → ℝ) (R : ℕ)
    (hae : ∀ j, e j =ᵐ[μ] e' j) {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) {E : ℝ}
    (hE : (refEnergy μ (polyEval e c)).toReal = E) :
    Jexpr A lam CR R (polyEval e c) =
      E + ∫ X, polyEval e' c X ^ 2 * vR A lam R (fun n => fluct e' N n X)
            ∂Measure.pi (fun _ : Fin N => μ)
        - (bRate μ lam CR).toReal / 2 *
          ((ent (Measure.pi fun _ : Fin N => μ) (fun X => polyEval e' c X ^ 2)).toReal
            + ∫ X, polyEval e' c X ^ 2 * uR A R (fun n => fluct e' N n X)
                ∂Measure.pi (fun _ : Fin N => μ)
            + Real.log (kappaR A R) * ∫ X, polyEval e' c X ^ 2 ∂Measure.pi (fun _ : Fin N => μ)) := by
  have hQ := ae_pi_eq hae N
  have i1 : ∫ X, polyEval e c X ^ 2 * vR A lam R (fun n => fluct e N n X)
        ∂Measure.pi (fun _ : Fin N => μ) =
      ∫ X, polyEval e' c X ^ 2 * vR A lam R (fun n => fluct e' N n X)
        ∂Measure.pi (fun _ : Fin N => μ) := by
    refine integral_congr_ae (hQ.mono fun X hX => ?_)
    simp only [polyEval_congr c X hX, fluct_congr X hX]
  have i2 : ∫ X, polyEval e c X ^ 2 * URN A R N X ∂Measure.pi (fun _ : Fin N => μ) =
      ∫ X, polyEval e' c X ^ 2 * uR A R (fun n => fluct e' N n X)
        ∂Measure.pi (fun _ : Fin N => μ) := by
    refine integral_congr_ae (hQ.mono fun X hX => ?_)
    simp only [URN, polyEval_congr c X hX, fluct_congr X hX]
  have i3 : ∫ X, polyEval e c X ^ 2 ∂Measure.pi (fun _ : Fin N => μ) =
      ∫ X, polyEval e' c X ^ 2 ∂Measure.pi (fun _ : Fin N => μ) := by
    refine integral_congr_ae (hQ.mono fun X hX => ?_)
    simp only [polyEval_congr c X hX]
  have i4 : ent (Measure.pi fun _ : Fin N => μ) (fun X => polyEval e c X ^ 2) =
      ent (Measure.pi fun _ : Fin N => μ) (fun X => polyEval e' c X ^ 2) :=
    ent_congr_ae (hQ.mono fun X hX => by simp only [polyEval_congr c X hX])
  unfold Jexpr
  simp only []
  rw [hE, i1, i2, i3, i4]

end expr

end SharpLSI.FL

end
