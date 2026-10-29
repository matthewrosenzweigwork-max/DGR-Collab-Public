import SharpSymmetricLSI.Paper.FormLiminf6

/-!
# R33 (8.20) groundwork: integration by parts with the multiplier `∂_iφ(Z_N) e^{-U_N}`
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `h = ψ(Z_N) e^{-U_N}` on `𝕋^{N×d}`. -/
noncomputable def multH (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (eC : ℕ → Torus d → ℝ)
    (N J : ℕ) (ψ : (Fin J → ℝ) → ℝ) (y : UnitAddTorus (Fin N × Fin d)) : ℝ :=
  ψ (zC eC N J (unflat y)) * gsE W μ N y * gsE W μ N y

/-- Its weak gradient (product rule, unsimplified). -/
noncomputable def multG (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (eC : ℕ → Torus d → ℝ)
    (N J : ℕ) (ψ : (Fin J → ℝ) → ℝ) (y : UnitAddTorus (Fin N × Fin d)) (p : Fin N × Fin d) : ℝ :=
  (gradZ eC N J ψ y p * gsE W μ N y + ψ (zC eC N J (unflat y)) *
      (-(1 / 2) * gsE W μ N y * gsG W μ N y p)) * gsE W μ N y +
    ψ (zC eC N J (unflat y)) * gsE W μ N y * (-(1 / 2) * gsE W μ N y * gsG W μ N y p)

theorem multG_eq (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (eC : ℕ → Torus d → ℝ)
    (N J : ℕ) (ψ : (Fin J → ℝ) → ℝ) (y : UnitAddTorus (Fin N × Fin d)) (p : Fin N × Fin d) :
    multG W μ eC N J ψ y p = gsE W μ N y ^ 2 *
      (gradZ eC N J ψ y p - ψ (zC eC N J (unflat y)) * gsG W μ N y p) := by
  unfold multG; ring

section
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {eC : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) {N : ℕ} (hN : 1 ≤ N)
  {J : ℕ} {ψ : (Fin J → ℝ) → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
include hyp hμ hφ hN hψ hc

theorem multH_props :
    IsWeakGrad (multH W μ eC N J ψ) (multG W μ eC N J ψ) ∧ Measurable (multH W μ eC N J ψ) ∧
      (∃ B, ∀ y, |multH W μ eC N J ψ y| ≤ B) ∧
      (∀ p, Measurable fun y => multG W μ eC N J ψ y p) ∧
      ∃ L, ∀ y p, |multG W μ eC N J ψ y p| ≤ L := by
  set μm := (μ : Measure (Torus d))
  have hac := minimizer_ac hyp hμ
  obtain ⟨K, hK0, hK⟩ := exists_bound_of_compact hψ.continuous hc
  obtain ⟨hgm, L, hL⟩ := gradZ_props hφ (N := N) hψ hc
  obtain ⟨BE, hBE⟩ := exists_bound_gsE hyp (W := W) (μ := μm) (N := N)
  obtain ⟨CG, hCG0, hCG⟩ := exists_bound_gsG hyp hac (N := N) (μ := μm)
  have hAm : Measurable fun y : UnitAddTorus (Fin N × Fin d) => ψ (zC eC N J (unflat y)) :=
    hψ.continuous.measurable.comp (measurable_zC_unflat hφ J)
  have hEm := measurable_gsE hyp (W := W) (μ := μm) (N := N)
  have hGm : ∀ p, Measurable fun y => gsG W μm N y p := measurable_gsG hyp hac
  have hA := isWeakGrad_gradZ hφ (N := N) hψ
  have hE := isWeakGrad_gsE hyp hac hN (μ := μm)
  have hBE0 : 0 ≤ BE := (abs_nonneg _).trans (hBE 0)
  have hEg : ∀ y p, |-(1 / 2) * gsE W μm N y * gsG W μm N y p| ≤ BE * CG := fun y p => by
    rw [abs_mul, abs_mul]
    calc |-(1 / 2 : ℝ)| * |gsE W μm N y| * |gsG W μm N y p| ≤ 1 * BE * CG := by
          gcongr
          · norm_num
          · exact hBE y
          · exact hCG y p
      _ = BE * CG := by ring
  have hEgm : ∀ p, Measurable fun y => -(1 / 2) * gsE W μm N y * gsG W μm N y p := fun p =>
    (measurable_const.mul hEm).mul (hGm p)
  -- `A · e^{-U/2}`
  have h1 := hA.mul_lip (integrable_of_bdd_meas hAm fun y => hK _)
    (fun p => integrable_of_bdd_meas (hgm p) fun y => hL y p) hE hEm hBE hEgm hEg
  have h1m : Measurable fun y => ψ (zC eC N J (unflat y)) * gsE W μm N y := hAm.mul hEm
  have h1b : ∀ y, |ψ (zC eC N J (unflat y)) * gsE W μm N y| ≤ K * BE := fun y => by
    rw [abs_mul]; exact mul_le_mul (hK _) (hBE y) (abs_nonneg _) hK0
  have h1gm : ∀ p, Measurable fun y => gradZ eC N J ψ y p * gsE W μm N y +
      ψ (zC eC N J (unflat y)) * (-(1 / 2) * gsE W μm N y * gsG W μm N y p) := fun p =>
    ((hgm p).mul hEm).add (hAm.mul (hEgm p))
  have h1gb : ∀ y p, |gradZ eC N J ψ y p * gsE W μm N y +
      ψ (zC eC N J (unflat y)) * (-(1 / 2) * gsE W μm N y * gsG W μm N y p)| ≤
        L * BE + K * (BE * CG) := fun y p => by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul (hL y p) (hBE y) (abs_nonneg _) ((abs_nonneg _).trans (hL y p))
    · rw [abs_mul]; exact mul_le_mul (hK _) (hEg y p) (abs_nonneg _) hK0
  have h2 := h1.mul_lip (integrable_of_bdd_meas h1m h1b)
    (fun p => integrable_of_bdd_meas (h1gm p) fun y => h1gb y p) hE hEm hBE hEgm hEg
  refine ⟨h2, h1m.mul hEm, ⟨K * BE * BE, fun y => ?_⟩, fun p => ((h1gm p).mul hEm).add
    (h1m.mul (hEgm p)), ⟨(L * BE + K * (BE * CG)) * BE + K * BE * (BE * CG), fun y p => ?_⟩⟩
  · show |ψ (zC eC N J (unflat y)) * gsE W μm N y * gsE W μm N y| ≤ K * BE * BE
    rw [abs_mul]; exact mul_le_mul (h1b y) (hBE y) (abs_nonneg _) (by positivity)
  · show |(gradZ eC N J ψ y p * gsE W μm N y + ψ (zC eC N J (unflat y)) *
      (-(1 / 2) * gsE W μm N y * gsG W μm N y p)) * gsE W μm N y +
      ψ (zC eC N J (unflat y)) * gsE W μm N y * (-(1 / 2) * gsE W μm N y * gsG W μm N y p)| ≤ _
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul (h1gb y p) (hBE y) (abs_nonneg _)
        ((abs_nonneg _).trans (h1gb y p))
    · rw [abs_mul]; exact mul_le_mul (h1b y) (hEg y p) (abs_nonneg _) (by positivity)

end

end SharpLSI
