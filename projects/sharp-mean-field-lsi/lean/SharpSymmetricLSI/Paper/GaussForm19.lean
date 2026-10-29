import SharpSymmetricLSI.Paper.GaussForm18

/-!
# R32 (E4): Gross' inequality under `γ` for functions of finitely many coordinates

If every finite block of `C` is positive semidefinite, the law of `(z_0,…,z_{N-1})` under `γ` is
`√S · N(0,I)` (`map_block_eq`), and `x = √S g` turns `gross_bdd` into
`Ent_γ(G(z_{<N})²) ≤ 2 ∫ ∑_{k,l<N} C_{kl} ∂_kG ∂_lG dγ` for `G ∈ C^∞_c(ℝ^N)`
(`gross_gamma_block`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ContDiff MatrixOrder

namespace SharpLSI

variable {γ : Measure (ℕ → ℝ)} {C : ℕ → ℕ → ℝ}

theorem sum_sq_mulVec_transpose {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℝ) :
    ∑ k, (∑ l, A l k * d l) ^ 2 = ∑ l, ∑ l', (A * Aᵀ) l l' * d l * d l' := by
  simp_rw [sq, Finset.sum_mul_sum, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l' _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Gross' inequality under `γ`** for `G(z_0, …, z_{N-1})`, `G ∈ C^∞_c(ℝ^N)`. -/
theorem gross_gamma_block (hγ : IsCenteredGaussianCov γ C) {N : ℕ}
    (hS : (blockMat C N).PosSemidef) {G : (Fin N → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) :
    entR γ (fun z => G (zBlock N z) ^ 2) ≤
      2 * ∫ z, ∑ k : Fin N, ∑ l : Fin N, C k l * fderiv ℝ G (zBlock N z) (Pi.single k 1) *
        fderiv ℝ G (zBlock N z) (Pi.single l 1) ∂γ := by
  set A := CFC.sqrt (blockMat C N)
  set P := gpi N
  have hAm : Measurable fun y : Fin N → ℝ => A *ᵥ y := (matCLM A).continuous.measurable
  have hmap := map_block_eq hγ hS
  have htr : ∀ H : (Fin N → ℝ) → ℝ, Continuous H →
      ∫ z, H (zBlock N z) ∂γ = ∫ y, H (A *ᵥ y) ∂P := fun H hH => by
    rw [← integral_map (measurable_zBlock _).aemeasurable hH.aestronglyMeasurable, hmap,
      integral_map hAm.aemeasurable hH.aestronglyMeasurable]
  obtain ⟨B, hFB, hdB, -, -, hder⟩ := exists_bounds_comp hG hc (matCLM A)
  have hF : ContDiff ℝ ∞ (fun y => G (matCLM A y)) := hG.comp (matCLM A).contDiff
  have hgross := gross_bdd hF hFB hdB
  have hGc := hG.continuous
  have hdc : ∀ k : Fin N, Continuous fun x => fderiv ℝ G x (Pi.single k 1) := fun k =>
    (hG.continuous_fderiv (by simp)).clm_apply continuous_const
  have hent : entR γ (fun z => G (zBlock N z) ^ 2) =
      entR P (fun y => G (matCLM A y) ^ 2) := by
    unfold entR
    rw [htr (fun x => G x ^ 2 * Real.log (G x ^ 2))
        (Real.continuous_mul_log.comp (hGc.pow 2)),
      htr (fun x => G x ^ 2) (hGc.pow 2)]
    rfl
  have hgrad : ∀ y, ∑ k, fderiv ℝ (fun y => G (matCLM A y)) y (Pi.single k 1) ^ 2 =
      ∑ k : Fin N, ∑ l : Fin N, C k l * fderiv ℝ G (A *ᵥ y) (Pi.single k 1) *
        fderiv ℝ G (A *ᵥ y) (Pi.single l 1) := fun y => by
    have e1 : ∀ k, fderiv ℝ (fun y => G (matCLM A y)) y (Pi.single k 1) =
        ∑ l, A l k * fderiv ℝ G (A *ᵥ y) (Pi.single l 1) := fun k => by
      rw [hder, ContinuousLinearMap.comp_apply, matCLM_single, fderiv_apply_sum]
      rfl
    simp_rw [e1]
    rw [sum_sq_mulVec_transpose, sqrt_mul_transpose hS]
    rfl
  rw [hent]
  refine hgross.trans (le_of_eq ?_)
  congr 1
  simp_rw [hgrad]
  exact (htr _ (continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
    (continuous_const.mul (hdc k)).mul (hdc l))).symm

end SharpLSI
