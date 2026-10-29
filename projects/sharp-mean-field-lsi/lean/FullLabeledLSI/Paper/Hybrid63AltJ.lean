import FullLabeledLSI.Paper.Hybrid63AltI

/-!
# Proposition 6.3: integrability and the reduction of the `(7.21)` differences to `est721`

For a fixed `N`, the observable `F = polyEval e' c` and the fluctuation vectors are bounded
measurable functions of `X`, so every integrand below is integrable and the difference of two
integrals is the integral of the difference.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace SharpLSI.FL

variable {d : ℕ}

section bdd
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

theorem measurable_quadF {s : Finset ℕ} (Qm : ℕ → ℕ → ℝ) {z : ℕ → Ω → ℝ}
    (hz : ∀ i ∈ s, Measurable (z i)) : Measurable fun ω => quadFA s Qm (fun i => z i ω) := by
  unfold quadFA
  refine Finset.measurable_sum _ fun i hi => Finset.measurable_sum _ fun j hj => ?_
  exact (measurable_const.mul (hz i hi)).mul (hz j hj)

theorem abs_quadFA_le {s : Finset ℕ} (Qm : ℕ → ℕ → ℝ) {z : ℕ → ℝ} {b : ℝ}
    (hz : ∀ i ∈ s, |z i| ≤ b) : |quadFA s Qm z| ≤ (∑ i ∈ s, ∑ j ∈ s, |Qm i j|) * b ^ 2 := by
  unfold quadFA
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  rw [abs_mul, abs_mul]
  have h1 := hz i hi
  have h2 := hz j hj
  have hb0 : 0 ≤ b := (abs_nonneg _).trans h1
  calc |Qm i j| * |z i| * |z j| ≤ |Qm i j| * b * b :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) h2 (abs_nonneg _)
          (mul_nonneg (abs_nonneg _) hb0)
    _ = |Qm i j| * b ^ 2 := by ring

theorem integrable_poly_quad {f : Ω → ℝ} {Kf : ℝ} (hf : Measurable f) (hfb : ∀ ω, |f ω| ≤ Kf)
    {s : Finset ℕ} (Qm : ℕ → ℕ → ℝ) {z : ℕ → Ω → ℝ} {Kz : ℝ}
    (hz : ∀ i ∈ s, Measurable (z i)) (hzb : ∀ i ∈ s, ∀ ω, |z i ω| ≤ Kz) (c0 : ℝ) :
    Integrable (fun ω => f ω ^ 2 * (quadFA s Qm (fun i => z i ω) + c0)) P := by
  refine Integrable.of_bound ((hf.pow_const 2).mul
    ((measurable_quadF Qm hz).add measurable_const)).aestronglyMeasurable
    (Kf ^ 2 * ((∑ i ∈ s, ∑ j ∈ s, |Qm i j|) * Kz ^ 2 + |c0|))
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  have h1 : |f ω| ^ 2 ≤ Kf ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hfb ω) 2
  have h2 : |quadFA s Qm (fun i => z i ω) + c0| ≤ (∑ i ∈ s, ∑ j ∈ s, |Qm i j|) * Kz ^ 2 + |c0| :=
    (abs_add_le _ _).trans (add_le_add (abs_quadFA_le Qm (fun i hi => hzb i hi ω)) le_rfl)
  exact mul_le_mul h1 h2 (abs_nonneg _) (sq_nonneg _)

/-- The difference of two integrals of `f² w(z)` is the integral of `f² (quad z - quad z')`. -/
theorem integral_sub_quad {f : Ω → ℝ} {Kf : ℝ} (hf : Measurable f) (hfb : ∀ ω, |f ω| ≤ Kf)
    {s : Finset ℕ} (Qm : ℕ → ℕ → ℝ) {z z' : ℕ → Ω → ℝ} {Kz : ℝ}
    (hz : ∀ i ∈ s, Measurable (z i)) (hzb : ∀ i ∈ s, ∀ ω, |z i ω| ≤ Kz)
    (hz' : ∀ i ∈ s, Measurable (z' i)) (hzb' : ∀ i ∈ s, ∀ ω, |z' i ω| ≤ Kz)
    (w : (ℕ → ℝ) → ℝ) (c0 : ℝ) (hw : ∀ y, w y = quadFA s Qm y + c0) :
    ∫ ω, f ω ^ 2 * w (fun i => z i ω) ∂P - ∫ ω, f ω ^ 2 * w (fun i => z' i ω) ∂P =
      ∫ ω, f ω ^ 2 * (quadFA s Qm (fun i => z i ω) - quadFA s Qm (fun i => z' i ω)) ∂P := by
  have i1 := integrable_poly_quad (P := P) hf hfb Qm hz hzb c0
  have i2 := integrable_poly_quad (P := P) hf hfb Qm hz' hzb' c0
  simp only [hw]
  rw [← integral_sub i1 i2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only []
  ring

end bdd

section fl
variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {e' : ℕ → Torus d → ℝ}

theorem fluct_bdd (hG : GoodBasis μ e') (N n : ℕ) :
    ∃ K : ℝ, ∀ X : Config N d, |fluct e' N n X| ≤ K := by
  obtain ⟨C, hC⟩ := hG.bdd (n + 1)
  refine ⟨|(N : ℝ) ^ (-(1 / 2 : ℝ))| * (N * |C|), fun X => ?_⟩
  unfold fluct
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ l : Fin N, |e' (n + 1) (X l)| ≤ ∑ _l : Fin N, |C| :=
        Finset.sum_le_sum fun l _ => (hC _).trans (le_abs_self C)
    _ = N * |C| := by simp

theorem Zlow_bdd (hG : GoodBasis μ e') {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ)
    (m : Fin J) : ∃ K : ℝ, ∀ X : Config N d, |Zlow e' c δ X m| ≤ K := by
  obtain ⟨C, hC⟩ := hG.bdd ((m : ℕ) + 1)
  refine ⟨|(Real.sqrt (lowCount c δ))⁻¹| * (N * |C|), fun X => ?_⟩
  unfold Zlow
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ l ∈ (retained c δ)ᶜ, |e' ((m : ℕ) + 1) (X l)| ≤ ∑ _l ∈ (retained c δ)ᶜ, |C| :=
        Finset.sum_le_sum fun l _ => (hC _).trans (le_abs_self C)
    _ ≤ N * |C| := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have : ((retained c δ)ᶜ.card : ℝ) ≤ N := by
          exact_mod_cast (by simpa using Finset.card_le_univ (retained c δ)ᶜ)
        exact mul_le_mul_of_nonneg_right this (abs_nonneg _)

end fl

end SharpLSI.FL

end
