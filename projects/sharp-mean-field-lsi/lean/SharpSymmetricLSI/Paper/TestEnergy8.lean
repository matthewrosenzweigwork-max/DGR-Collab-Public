import SharpSymmetricLSI.Paper.TestEnergy4
import SharpSymmetricLSI.Paper.TestEnergy7
import SharpSymmetricLSI.Paper.GaussLaw11
import SharpSymmetricLSI.Paper.GaussForm14

/-!
# R33: (8.14), (8.18), convergence of the test energies, given Prop. 2.1 and Lemma 5.2

`ℰ_N(φ_N) = E_{P_N} ∑_{ij} A_{N,ij} ∂_iφ ∂_jφ(Z_N) → ∫ ∑_i λ_i (∂_iφ)² dγ_∞ = ℰ_∞(φ)`: the mobility
converges in `L¹(P_N)` (TestEnergy7) and the fluctuations converge in law (R27,
`gaussian_limit_law_of`); the limit law is identified with any `γ` of covariance `C` on
cylinders (TestEnergy4).
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem zC_ae_eq_fluct {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {e eC : ℕ → Torus d → ℝ}
    (hac : μ ≪ haar d)
    (heC : ∀ j, eC j =ᵐ[haar d] e j) (N J : ℕ) :
    ∀ᵐ X ∂Measure.pi (fun _ : Fin N => μ), zC eC N J X = fun i : Fin J => fluct e N i X := by
  have hcomp : ∀ (j : ℕ) (l : Fin N), ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ),
      eC j (X l) = e j (X l) := fun j l =>
    (measurePreserving_eval (fun _ : Fin N => μ) l).quasiMeasurePreserving.ae_eq_comp
      (hac.ae_le (heC j))
  have hall : ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), ∀ (j : ℕ) (l : Fin N),
      eC j (X l) = e j (X l) := by
    rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro l; exact hcomp j l
  filter_upwards [hall] with X hX
  funext i
  simp only [zC, fluct, hX]

theorem exists_bound_fderiv_cyl (c : Cyl) :
    ∃ K, 0 ≤ K ∧ ∀ z (i : Fin c.J), |fderiv ℝ c.φ z (Pi.single i 1)| ≤ K := by
  have hc : Continuous (fderiv ℝ c.φ) := c.smooth.continuous_fderiv (by simp)
  obtain ⟨K, hK⟩ := hc.bounded_above_of_compact_support (c.compact.fderiv (𝕜 := ℝ))
  refine ⟨max K 0, le_max_right _ _, fun z i => ?_⟩
  rw [← Real.norm_eq_abs]
  refine ((fderiv ℝ c.φ z).le_opNorm _).trans ?_
  have h1 : ‖(Pi.single i (1 : ℝ) : Fin c.J → ℝ)‖ ≤ 1 := by
    rw [Pi.norm_single, norm_one]
  calc ‖fderiv ℝ c.φ z‖ * ‖(Pi.single i (1 : ℝ) : Fin c.J → ℝ)‖ ≤ max K 0 * 1 :=
        mul_le_mul ((hK z).trans (le_max_left _ _)) h1 (norm_nonneg _) (le_max_right _ _)
    _ = max K 0 := mul_one _

theorem continuous_fderiv_cyl (c : Cyl) (i : Fin c.J) :
    Continuous fun z => fderiv ℝ c.φ z (Pi.single i 1) :=
  (c.smooth.continuous_fderiv (by simp)).clm_apply continuous_const

/-- `H(z) = ∑_i λ_i (∂_iφ(z))²`, the integrand of `ℰ_∞(φ)`. -/
noncomputable def cylH (lam' : ℕ → ℝ) (c : Cyl) (z : Fin c.J → ℝ) : ℝ :=
  ∑ i : Fin c.J, lam' i * (fderiv ℝ c.φ z (Pi.single i 1)) ^ 2

theorem continuous_cylH (lam' : ℕ → ℝ) (c : Cyl) : Continuous (cylH lam' c) := by
  unfold cylH
  exact continuous_finsetSum _ fun i _ => continuous_const.mul ((continuous_fderiv_cyl c i).pow 2)

theorem cylH_bounds {lam' : ℕ → ℝ} (hlam : ∀ i, 0 ≤ lam' i) (c : Cyl) :
    ∃ K, ∀ z, 0 ≤ cylH lam' c z ∧ cylH lam' c z ≤ K := by
  obtain ⟨Ka, hKa0, hKa⟩ := exists_bound_fderiv_cyl c
  refine ⟨∑ i : Fin c.J, lam' i * Ka ^ 2, fun z => ⟨?_, ?_⟩⟩
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hlam _) (sq_nonneg _)
  · refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hlam _)
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hKa z i) 2

/-- `cylH` as a bounded continuous function. -/
noncomputable def cylHb {lam' : ℕ → ℝ} (hlam : ∀ i, 0 ≤ lam' i) (c : Cyl) : (Fin c.J → ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨cylH lam' c, continuous_cylH lam' c⟩
    (2 * (cylH_bounds hlam c).choose) fun a b => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have ha := (cylH_bounds hlam c).choose_spec a
      have hb := (cylH_bounds hlam c).choose_spec b
      rw [abs_le]; constructor <;> linarith

theorem cylHb_apply {lam' : ℕ → ℝ} (hlam : ∀ i, 0 ≤ lam' i) (c : Cyl) (z : Fin c.J → ℝ) :
    cylHb hlam c z = cylH lam' c z := rfl

end SharpLSI
