import SharpSymmetricLSI.Paper.LemmaA2_17

/-!
# R25 Lemma A.2, part 18: the reference semigroup on Lipschitz functions

With `C¹` representatives `eC_j` (`|eC_j| ≤ M_j`, `‖∇eC_j‖ ≤ M'_j`) and `∑ e^{-tλ_j}(M_j + M'_j) < ∞`
for `t > 0`, the series `P_t h = ∑ e^{-tλ_j} ⟨h, e_j⟩ eC_j` is `C¹`; continuous functions are
determined by their coefficients (`eq_of_coeff_eq`), so `P_t h` is the function of
`euler_lipschitz`: `Lip(P_t h) ≤ e^{Kt} Lip h` and `|P_t h| ≤ sup |h|` (`semi_props`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

section semi

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C) (hρc : Continuous ρ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (hb : IsRefEigenbasis (densMeasure ρ) e lam)

include hρ hb in
theorem integral_abs_e_le' (j : ℕ) : ∫ y, |e j y| ∂densMeasure ρ ≤ 1 := by
  haveI := hρ.isProb
  have h2 : Integrable (fun y => e j y ^ 2) (densMeasure ρ) := (hb.memH1 j).2.1.integrable_sq
  have h1 : ∫ y, e j y ^ 2 ∂densMeasure ρ = 1 := by
    have := hb.orthonormal j j
    rw [if_pos rfl] at this
    refine Eq.trans ?_ this
    exact integral_congr_ae (Eventually.of_forall fun y => by simp only [sq])
  have hpt : ∀ y, |e j y| ≤ (1 + e j y ^ 2) / 2 := fun y => by
    have := sq_nonneg (|e j y| - 1)
    have h3 : |e j y| ^ 2 = e j y ^ 2 := sq_abs _
    nlinarith
  have hi : Integrable (fun y => (1 + e j y ^ 2) / 2) (densMeasure ρ) :=
    ((integrable_const 1).add h2).div_const 2
  have hle := integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg (e j y)) hi
    (Eventually.of_forall hpt)
  have he : ∫ y, (1 + e j y ^ 2) / 2 ∂densMeasure ρ = 1 := by
    rw [integral_div, integral_add (integrable_const 1) h2, h1, integral_const]
    simp
  linarith

include hρ hb in
theorem abs_coeff_le_sup {h : Torus d → ℝ} {B : ℝ} (hhm : AEStronglyMeasurable h (densMeasure ρ))
    (hB : ∀ y, |h y| ≤ B) (j : ℕ) : |∫ y, h y * e j y ∂densMeasure ρ| ≤ B := by
  haveI := hρ.isProb
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary _))
  have hej : Integrable (e j) (densMeasure ρ) := ((hb.memH1 j).2.1).integrable one_le_two
  calc |∫ y, h y * e j y ∂densMeasure ρ| ≤ ∫ y, |h y * e j y| ∂densMeasure ρ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y, B * |e j y| ∂densMeasure ρ := integral_mono_of_nonneg
        (Eventually.of_forall fun _ => abs_nonneg _) (hej.abs.const_mul B)
        (Eventually.of_forall fun y => by
          show |h y * e j y| ≤ B * |e j y|
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hB y) (abs_nonneg _))
    _ = B * ∫ y, |e j y| ∂densMeasure ρ := integral_const_mul _ _
    _ ≤ B := by
        have h1 := integral_abs_e_le' hρ hb j
        have h2 : 0 ≤ ∫ y, |e j y| ∂densMeasure ρ := integral_nonneg fun y => abs_nonneg (e j y)
        nlinarith

include hρ hρc hb in
/-- **Continuous functions are determined by their coefficients.** -/
theorem eq_of_coeff_eq {f g : Torus d → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ j, ∫ y, f y * e j y ∂densMeasure ρ = ∫ y, g y * e j y ∂densMeasure ρ) : f = g := by
  haveI := hρ.isProb
  obtain ⟨Bf, hBf⟩ := isCompact_univ.exists_bound_of_continuousOn (hf.sub hg).continuousOn
  have hmem : MemLp (fun y => f y - g y) 2 (densMeasure ρ) :=
    MemLp.of_bound (hf.sub hg).aestronglyMeasurable Bf
      (Eventually.of_forall fun y => hBf y (mem_univ _))
  have h0 := hb.complete _ hmem fun j => by
    have hej : Integrable (e j) (densMeasure ρ) := ((hb.memH1 j).2.1).integrable one_le_two
    obtain ⟨B1, hB1⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
    obtain ⟨B2, hB2⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
    have i1 : Integrable (fun y => f y * e j y) (densMeasure ρ) :=
      hej.bdd_mul (c := B1) hf.aestronglyMeasurable (Eventually.of_forall fun y => hB1 y (mem_univ _))
    have i2 : Integrable (fun y => g y * e j y) (densMeasure ρ) :=
      hej.bdd_mul (c := B2) hg.aestronglyMeasurable (Eventually.of_forall fun y => hB2 y (mem_univ _))
    simp_rw [sub_mul]
    rw [integral_sub i1 i2, h j, sub_self]
  have h1 : (fun y => f y - g y) =ᵐ[volume] 0 := hρ.ac'.ae_le h0
  have h2 := eq_of_ae_eq_continuous (hf.sub hg) continuous_const h1
  funext y
  have := congrFun h2 y
  have h3 : f y - g y = 0 := this
  linarith

end semi

end SharpLSI
