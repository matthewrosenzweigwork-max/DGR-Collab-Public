import SharpSymmetricLSI.Paper.GaussForm3

/-!
# R32 (A4): Stein's lemma for any coordinate against a function of the first `J` coordinates

`∫ z_q g(z_{<J}) dγ = ∑_{l<J} C_{ql} ∫ ∂_l g(z_{<J}) dγ` for every `q ∈ ℕ` (`stein_gamma_nat`),
assuming the finite blocks of `C` are positive semidefinite.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Matrix
open scoped NNReal MatrixOrder

namespace SharpLSI

/-- The projection `ℝ^N → ℝ^J`, `J ≤ N`. -/
noncomputable def projCLM {J N : ℕ} (h : J ≤ N) : (Fin N → ℝ) →L[ℝ] (Fin J → ℝ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Fin.castLE h j)

theorem projCLM_apply {J N : ℕ} (h : J ≤ N) (y : Fin N → ℝ) (j : Fin J) :
    projCLM h y j = y (Fin.castLE h j) := rfl

theorem norm_projCLM_le {J N : ℕ} (h : J ≤ N) : ‖projCLM h‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro j
  exact norm_le_pi_norm y _

theorem projCLM_single {J N : ℕ} (h : J ≤ N) (l : Fin N) :
    projCLM h (Pi.single l 1) =
      if hl : (l : ℕ) < J then (Pi.single ⟨l, hl⟩ 1 : Fin J → ℝ) else 0 := by
  funext j
  rw [projCLM_apply]
  split_ifs with hl
  · simp only [Pi.single_apply, Fin.ext_iff, Fin.coe_castLE]
  · have : Fin.castLE h j ≠ l := fun e => hl (by rw [← e]; simp [j.isLt])
    simp [Pi.single_apply, this]

theorem block_proj {J N : ℕ} (h : J ≤ N) (z : ℕ → ℝ) : projCLM h (zBlock N z) = zBlock J z := rfl

variable {γ : Measure (ℕ → ℝ)} {C : ℕ → ℕ → ℝ}

/-- **Stein's lemma for any coordinate.** -/
theorem stein_gamma_nat (hγ : IsCenteredGaussianCov γ C) (hPSD : ∀ N, (blockMat C N).PosSemidef)
    {J : ℕ} {g : (Fin J → ℝ) → ℝ} (hg : Differentiable ℝ g)
    (hgc : Continuous fun y => fderiv ℝ g y) {B : ℝ} (hgB : ∀ y, |g y| ≤ B)
    (hdB : ∀ y, ‖fderiv ℝ g y‖ ≤ B) (q : ℕ) :
    ∫ z, z q * g (zBlock J z) ∂γ =
      ∑ l : Fin J, C q l * ∫ z, fderiv ℝ g (zBlock J z) (Pi.single l 1) ∂γ := by
  set N := J + q + 1
  have hJN : J ≤ N := by omega
  have hqN : q < N := by omega
  set P := projCLM hJN
  set G : (Fin N → ℝ) → ℝ := fun y => g (P y)
  have hGd : ∀ y, HasFDerivAt G ((fderiv ℝ g (P y)).comp P) y := fun y =>
    (hg (P y)).hasFDerivAt.comp y P.hasFDerivAt
  have hGder : ∀ y, fderiv ℝ G y = (fderiv ℝ g (P y)).comp P := fun y => (hGd y).fderiv
  have hG : Differentiable ℝ G := fun y => (hGd y).differentiableAt
  have hGc : Continuous fun y => fderiv ℝ G y := by
    simp_rw [hGder]
    exact (ContinuousLinearMap.compL ℝ _ _ _ |>.flip P).continuous.comp (hgc.comp P.continuous)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB 0)
  have hGdB : ∀ y, ‖fderiv ℝ G y‖ ≤ B := fun y => by
    rw [hGder]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc ‖fderiv ℝ g (P y)‖ * ‖P‖ ≤ B * 1 :=
          mul_le_mul (hdB _) (norm_projCLM_le hJN) (norm_nonneg _) hB0
      _ = B := mul_one B
  have h := stein_gamma hγ (hPSD N) hG hGc (fun y => hgB _) hGdB ⟨q, hqN⟩
  have e1 : ∫ z, z q * g (zBlock J z) ∂γ =
      ∫ z, z ((⟨q, hqN⟩ : Fin N) : ℕ) * G (zBlock N z) ∂γ := rfl
  rw [e1, h]
  set f : ℕ → ℝ := fun l => if hl : l < J then
    C q l * ∫ z, fderiv ℝ g (zBlock J z) (Pi.single ⟨l, hl⟩ 1) ∂γ else 0 with hf
  have hL : ∀ l : Fin N, C q l * ∫ z, fderiv ℝ G (zBlock N z) (Pi.single l 1) ∂γ = f l := fun l => by
    have hPs := projCLM_single hJN l
    simp_rw [hGder, ContinuousLinearMap.comp_apply]
    rw [show P (Pi.single l 1) = _ from hPs]
    simp only [hf]
    split_ifs with hl
    · rfl
    · simp
  have hR : ∀ l : Fin J, C q l * ∫ z, fderiv ℝ g (zBlock J z) (Pi.single l 1) ∂γ = f l := fun l => by
    simp only [hf, dite_eq_left_iff, l.isLt]; simp [l.isLt]
  simp_rw [hL, hR]
  rw [Fin.sum_univ_eq_sum_range f N, Fin.sum_univ_eq_sum_range f J,
    show N = J + (q + 1) by omega, Finset.sum_range_add]
  have h0 : ∑ x ∈ Finset.range (q + 1), f (J + x) = 0 :=
    Finset.sum_eq_zero fun x _ => by simp [hf]
  rw [h0, add_zero]

end SharpLSI
