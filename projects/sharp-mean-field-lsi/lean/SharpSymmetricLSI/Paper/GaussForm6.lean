import SharpSymmetricLSI.Paper.GaussForm5

/-!
# R32 (B1): cylinder functions, their partial derivatives and bounds

* `Cyl.dd c i z = ∂_i c(z)` (`0` for `i ≥ J`), `Cyl.dd2 c i z = ∂_{ii} c(z)`.
* Smooth compactly supported functions and their derivatives are bounded.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ContDiff

namespace SharpLSI

/-- `∂_k f` for `f : ℝ^J → ℝ`. -/
noncomputable def pd {J : ℕ} (f : (Fin J → ℝ) → ℝ) (k : Fin J) (x : Fin J → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single k 1)

theorem contDiff_pd {J : ℕ} {f : (Fin J → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (k : Fin J) :
    ContDiff ℝ ∞ (pd f k) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem hasCompactSupport_pd {J : ℕ} {f : (Fin J → ℝ) → ℝ} (hf : HasCompactSupport f) (k : Fin J) :
    HasCompactSupport (pd f k) :=
  hf.fderiv_apply (𝕜 := ℝ) _

/-- A smooth compactly supported function is bounded with bounded continuous derivative. -/
theorem exists_bounds_of_cc {J : ℕ} {f : (Fin J → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    ∃ B, (∀ x, |f x| ≤ B) ∧ (∀ x, ‖fderiv ℝ f x‖ ≤ B) ∧ Continuous (fun x => fderiv ℝ f x) ∧
      Differentiable ℝ f := by
  have hd : Continuous fun x => fderiv ℝ f x := hf.continuous_fderiv (by simp)
  obtain ⟨B1, hB1⟩ := hc.exists_bound_of_continuous hf.continuous
  obtain ⟨B2, hB2⟩ := (hc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous hd
  refine ⟨max B1 B2, fun x => ?_, fun x => (hB2 x).trans (le_max_right _ _), hd,
    hf.differentiable (by simp)⟩
  rw [← Real.norm_eq_abs]; exact (hB1 x).trans (le_max_left _ _)

/-- Bounds for `H ∘ P`, `H` smooth compactly supported on a finite-dimensional space. -/
theorem exists_bounds_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {H : F → ℝ}
    (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) (P : E →L[ℝ] F) :
    ∃ B, (∀ x, |H (P x)| ≤ B) ∧ (∀ x, ‖fderiv ℝ (fun y => H (P y)) x‖ ≤ B) ∧
      Continuous (fun x => fderiv ℝ (fun y => H (P y)) x) ∧ Differentiable ℝ (fun y => H (P y)) ∧
      ∀ x, fderiv ℝ (fun y => H (P y)) x = (fderiv ℝ H (P x)).comp P := by
  have hd : Continuous fun x => fderiv ℝ H x := hH.continuous_fderiv (by simp)
  have hdiff : Differentiable ℝ H := hH.differentiable (by simp)
  obtain ⟨B1, hB1⟩ := hc.exists_bound_of_continuous hH.continuous
  obtain ⟨B2, hB2⟩ := (hc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous hd
  have hder : ∀ x, fderiv ℝ (fun y => H (P y)) x = (fderiv ℝ H (P x)).comp P := fun x =>
    ((hdiff (P x)).hasFDerivAt.comp x P.hasFDerivAt).fderiv
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  refine ⟨max B1 (B2 * ‖P‖), fun x => ?_, fun x => ?_, ?_, fun x =>
    ((hdiff (P x)).hasFDerivAt.comp x P.hasFDerivAt).differentiableAt, hder⟩
  · rw [← Real.norm_eq_abs]; exact (hB1 _).trans (le_max_left _ _)
  · rw [hder]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans ((mul_le_mul_of_nonneg_right (hB2 _)
      (norm_nonneg _)).trans (le_max_right _ _))
  · simp_rw [hder]
    exact (ContinuousLinearMap.compL ℝ _ _ _ |>.flip P).continuous.comp (hd.comp P.continuous)

theorem hasCompactSupport_prod_mul {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : E → ℝ} {g : F → ℝ} (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport fun p : E × F => f p.1 * g p.2 := by
  refine HasCompactSupport.intro (hf.isCompact.prod hg.isCompact) fun p hp => ?_
  simp only [Set.mem_prod, not_and_or] at hp
  rcases hp with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem fderiv_prod_mul_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → ℝ} {g : F → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (p : E × F) (v : E × F) :
    fderiv ℝ (fun p : E × F => f p.1 * g p.2) p v =
      fderiv ℝ f p.1 v.1 * g p.2 + f p.1 * fderiv ℝ g p.2 v.2 := by
  have h1 : HasFDerivAt (fun p : E × F => f p.1) ((fderiv ℝ f p.1).comp (ContinuousLinearMap.fst ℝ E F)) p :=
    (hf p.1).hasFDerivAt.comp p (ContinuousLinearMap.fst ℝ E F).hasFDerivAt
  have h2 : HasFDerivAt (fun p : E × F => g p.2) ((fderiv ℝ g p.2).comp (ContinuousLinearMap.snd ℝ E F)) p :=
    (hg p.2).hasFDerivAt.comp p (ContinuousLinearMap.snd ℝ E F).hasFDerivAt
  have h3 : HasFDerivAt (fun p : E × F => f p.1 * g p.2)
      (f p.1 • (fderiv ℝ g p.2).comp (ContinuousLinearMap.snd ℝ E F) +
        g p.2 • (fderiv ℝ f p.1).comp (ContinuousLinearMap.fst ℝ E F)) p := h1.mul h2
  rw [h3.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  ring

namespace Cyl

/-- `∂_i c(z)` (zero for `i ≥ J`). -/
noncomputable def dd (c : Cyl) (i : ℕ) (z : ℕ → ℝ) : ℝ :=
  if h : i < c.J then pd c.φ ⟨i, h⟩ (zBlock c.J z) else 0

theorem eval_eq (c : Cyl) (z : ℕ → ℝ) : c.eval z = c.φ (zBlock c.J z) := rfl

end Cyl

end SharpLSI
