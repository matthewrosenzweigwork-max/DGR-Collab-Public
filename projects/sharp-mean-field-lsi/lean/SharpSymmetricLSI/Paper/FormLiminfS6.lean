import SharpSymmetricLSI.Paper.FormLiminfS5
import SharpSymmetricLSI.Defs.D18_GaussianForm

/-!
# (8.20) (lane s42): the duality step in the shape of R32 `form_duality`

`gaussForm_le_liminf_of_duality`: given the duality formula of R32 `form_duality` as a hypothesis
(`ℰ_∞(f) = sup_c 2∫f(-L_∞φ_c) dγ - ℰ_∞(φ_c)`), and for every cylinder `c` real sequences with
`x_k → ∫f(-L_∞φ_c)`, `y_k → ℰ_∞(φ_c)`, `2x_k - y_k ≤ E_k`, we get `ℰ_∞(f) ≤ liminf E`.
Cylinder forms are finite (`Cyl.form_ne_top`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace SharpLSI

/-- The form of a cylinder function is finite. -/
theorem Cyl.form_ne_top (lam' : ℕ → ℝ) {γ : Measure (ℕ → ℝ)} [IsFiniteMeasure γ] (c : Cyl) :
    c.form lam' γ ≠ ⊤ := by
  have hdc : ∀ i : Fin c.J, Continuous fun x => fderiv ℝ c.φ x (Pi.single i 1) := fun i =>
    (c.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  set g : (Fin c.J → ℝ) → ℝ := fun x => ∑ i : Fin c.J, lam' i * (fderiv ℝ c.φ x (Pi.single i 1)) ^ 2
  have hgc : Continuous g := continuous_finsetSum _ fun i _ => continuous_const.mul ((hdc i).pow 2)
  have hgs : HasCompactSupport g := by
    refine HasCompactSupport.intro (c.compact.fderiv (𝕜 := ℝ)) fun x hx => ?_
    simp only [g, image_eq_zero_of_notMem_tsupport hx, ContinuousLinearMap.zero_apply]
    simp
  obtain ⟨C, hC⟩ := hgs.exists_bound_of_continuous hgc
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun z => ENNReal.ofReal_le_ofReal
    (show g (fun j => z j) ≤ C from (le_abs_self _).trans (by
      rw [← Real.norm_eq_abs]; exact hC _))) ?_)
  rw [lintegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top γ _)

/-- **`ℰ_∞(f) ≤ liminf E`** from the duality formula (R32 `form_duality` shape). -/
theorem gaussForm_le_liminf_of_duality {lam' : ℕ → ℝ} {γ : Measure (ℕ → ℝ)} [IsFiniteMeasure γ]
    {Y : ℕ → (ℕ → ℝ) → ℝ} {f : (ℕ → ℝ) → ℝ} {E : ℕ → ℝ≥0∞} (hE : ∀ k, E k ≠ ⊤)
    (hdual : (gaussForm lam' γ f : EReal) =
      ⨆ c : Cyl, ((2 * ∫ z, f z * (-(c.gen lam' Y z)) ∂γ : ℝ) : EReal) - (c.form lam' γ : EReal))
    (hseq : ∀ c : Cyl, ∃ x y : ℕ → ℝ,
      Tendsto x atTop (𝓝 (∫ z, f z * (-(c.gen lam' Y z)) ∂γ)) ∧
      Tendsto y atTop (𝓝 (c.form lam' γ).toReal) ∧ ∀ k, 2 * x k - y k ≤ (E k).toReal) :
    gaussForm lam' γ f ≤ liminf E atTop :=
  le_liminf_of_duality hE (fun c => Cyl.form_ne_top lam' c) hdual hseq

end SharpLSI
