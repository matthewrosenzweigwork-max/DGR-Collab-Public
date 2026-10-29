import SharpSymmetricLSI.Paper.LemmaA2_10

/-!
# R25 (A.9), part 11: passing to the limit in the resolvent equation

* `tendsto_integral_dpart_mul`: if `uₙ → u` uniformly with `|∇uₙ| ≤ D` and `u` Lipschitz, then
  `∫ ∂ₖuₙ ψ → ∫ ∂ₖu ψ` for continuous `ψ` (approximate `ψ` by smooth `ψ_m` and integrate by
  parts);
* `limit_resolvent_eq`: if `ρₙ → ρ` pointwise (uniformly bounded), `Φₙ → h` and `uₙ → u`
  uniformly, and `∫ ρₙ(Φₙ - uₙ)Θ = -τ ∫ uₙ div(ρₙ∇Θ)`, then
  `∫ ρ(h - u)Θ = τ ∫ ρ ∇u·∇Θ` for all smooth periodic `Θ`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

theorem integrable_of_continuous_torus' {f : Torus d → ℝ} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem continuous_comp_secT {F : (Fin d → ℝ) → ℝ} (hF : Continuous F) (hp : IsPer F) :
    Continuous fun y => F (secT y) :=
  continuous_of_liftT' (by
    rw [show (fun y => F (secT y)) ∘ liftT = F from comp_secT_comp_liftT hp]
    exact hF)

/-- **Weak convergence of gradients against continuous functions.** -/
theorem tendsto_integral_dpart_mul {u : ℕ → Torus d → ℝ} {u₀ : Torus d → ℝ}
    (hu : ∀ n, ContDiff ℝ 1 (u n ∘ liftT)) {D : ℝ} (hD : ∀ n k y, |dpart (u n) k y| ≤ D)
    (hconv : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ y, |u n y - u₀ y| ≤ ε) (hu₀ : Continuous u₀) {L : ℝ≥0}
    (hL : LipschitzWith L (u₀ ∘ liftT)) {ψ : Torus d → ℝ} (hψ : Continuous ψ) (k : Fin d) :
    Tendsto (fun n => ∫ y, dpart (u n) k y * ψ y) atTop (𝓝 (∫ y, lipGrad u₀ y k * ψ y)) := by
  have hw₀ := isWeakGrad_lipGrad hu₀ hL
  have hgb : ∀ y, |lipGrad u₀ y k| ≤ L := fun y => abs_lipGrad_le hL y k
  have hgm : Measurable fun y => lipGrad u₀ y k := measurable_lipGrad hu₀ k
  have hdc : ∀ n, Continuous (dpart (u n) k) := fun n =>
    continuous_of_liftT' (contDiff_dpart (n := 0) (by simpa using hu n) k).continuous
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0 k 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := ε / (3 * (D + L + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨m, hm⟩ := (moll_uniform_of_continuous hψ hδ).exists
  set ψm := moll m ψ
  set Θ := ψm ∘ liftT
  have hΘ : ContDiff ℝ ∞ Θ := moll_comp_liftT_contDiff m (integrable_of_continuous_torus' hψ)
  have hΘp : IsPer Θ := fun m' x => by simp only [Θ, Function.comp, liftT_add_intVec]
  have hΘs : ∀ y, Θ (secT y) = ψm y := fun y => by simp [Θ, liftT_secT]
  obtain ⟨BΘ, hBΘ⟩ := periodic_bounded (contDiff_Dk hΘ k).continuous (hΘp.Dk k)
  have hBΘ0 : 0 ≤ BΘ := (norm_nonneg _).trans (hBΘ 0)
  set η := ε / (3 * (BΘ + 1))
  obtain ⟨N, hN⟩ := hconv η (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hDkc : Continuous fun y => Dk Θ k (secT y) := continuous_comp_secT (contDiff_Dk hΘ k).continuous
    (hΘp.Dk k)
  have hψmc : Continuous ψm := continuous_of_liftT' hΘ.continuous
  -- integration by parts against `ψm`
  have h1 : ∫ y, dpart (u n) k y * ψm y = -∫ y, u n y * Dk Θ k (secT y) := by
    have hw := isWeakGrad_of_contDiff (hu n)
    have := integral_mul_Dk_eq hw (integrable_of_continuous_torus'
      (continuous_of_liftT' (hu n).continuous))
      (fun j => integrable_of_continuous_torus' (continuous_of_liftT'
        (contDiff_dpart (n := 0) (by simpa using hu n) j).continuous)) hΘ hΘp k
    simp only [hΘs] at this
    rw [this, neg_neg]; rfl
  have h2 : ∫ y, lipGrad u₀ y k * ψm y = -∫ y, u₀ y * Dk Θ k (secT y) := by
    have := integral_mul_Dk_eq hw₀ (integrable_of_continuous_torus' hu₀)
      (fun j => (integrable_const (L : ℝ)).mono' (measurable_lipGrad hu₀ j).aestronglyMeasurable
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact abs_lipGrad_le hL y j))
      hΘ hΘp k
    simp only [hΘs] at this
    rw [this, neg_neg]
  have hi1 : Integrable fun y => dpart (u n) k y * ψ y :=
    integrable_of_continuous_torus' ((hdc n).mul hψ)
  have hi1m : Integrable fun y => dpart (u n) k y * ψm y :=
    integrable_of_continuous_torus' ((hdc n).mul hψmc)
  have hi2 : Integrable fun y => lipGrad u₀ y k * ψ y :=
    (integrable_of_continuous_torus' hψ).bdd_mul (c := L) hgm.aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hgb y)
  have hi2m : Integrable fun y => lipGrad u₀ y k * ψm y :=
    (integrable_of_continuous_torus' hψmc).bdd_mul (c := L) hgm.aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hgb y)
  have hi3 : Integrable fun y => u n y * Dk Θ k (secT y) :=
    integrable_of_continuous_torus' ((continuous_of_liftT' (hu n).continuous).mul hDkc)
  have hi4 : Integrable fun y => u₀ y * Dk Θ k (secT y) :=
    integrable_of_continuous_torus' (hu₀.mul hDkc)
  have hψψ : ∀ y, |ψ y - ψm y| ≤ δ := fun y => by
    rw [abs_sub_comm, ← Real.dist_eq]; exact hm y
  -- three estimates
  have e1 : |(∫ y, dpart (u n) k y * ψ y) - ∫ y, dpart (u n) k y * ψm y| ≤ D * δ := by
    rw [← integral_sub hi1 hi1m]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |dpart (u n) k y * ψ y - dpart (u n) k y * ψm y| ≤ ∫ _y : Torus d, D * δ :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const _)
            (Eventually.of_forall fun y => by
              show |dpart (u n) k y * ψ y - dpart (u n) k y * ψm y| ≤ D * δ
              rw [← mul_sub, abs_mul]
              exact mul_le_mul (hD n k y) (hψψ y) (abs_nonneg _) hD0)
      _ = D * δ := by simp
  have e2 : |(∫ y, lipGrad u₀ y k * ψm y) - ∫ y, lipGrad u₀ y k * ψ y| ≤ L * δ := by
    rw [← integral_sub hi2m hi2]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |lipGrad u₀ y k * ψm y - lipGrad u₀ y k * ψ y| ≤ ∫ _y : Torus d, (L : ℝ) * δ :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const _)
            (Eventually.of_forall fun y => by
              show |lipGrad u₀ y k * ψm y - lipGrad u₀ y k * ψ y| ≤ L * δ
              rw [← mul_sub, abs_mul, abs_sub_comm]
              exact mul_le_mul (hgb y) (hψψ y) (abs_nonneg _) L.2)
      _ = L * δ := by simp
  have e3 : |(∫ y, u n y * Dk Θ k (secT y)) - ∫ y, u₀ y * Dk Θ k (secT y)| ≤ η * BΘ := by
    rw [← integral_sub hi3 hi4]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |u n y * Dk Θ k (secT y) - u₀ y * Dk Θ k (secT y)| ≤ ∫ _y : Torus d, η * BΘ :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const _)
            (Eventually.of_forall fun y => by
              show |u n y * Dk Θ k (secT y) - u₀ y * Dk Θ k (secT y)| ≤ η * BΘ
              rw [← sub_mul, abs_mul]
              exact mul_le_mul (hN n hn y) (by rw [← Real.norm_eq_abs]; exact hBΘ _)
                (abs_nonneg _) (by positivity))
      _ = η * BΘ := by simp
  rw [Real.dist_eq]
  have hsplit : (∫ y, dpart (u n) k y * ψ y) - ∫ y, lipGrad u₀ y k * ψ y =
      ((∫ y, dpart (u n) k y * ψ y) - ∫ y, dpart (u n) k y * ψm y) +
      (-((∫ y, u n y * Dk Θ k (secT y)) - ∫ y, u₀ y * Dk Θ k (secT y))) +
      ((∫ y, lipGrad u₀ y k * ψm y) - ∫ y, lipGrad u₀ y k * ψ y) := by
    rw [h1, h2]; ring
  rw [hsplit]
  have hb1 : D * δ < ε / 3 := by
    simp only [δ]; rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hb2 : (L : ℝ) * δ < ε / 3 := by
    simp only [δ]; rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [L.2]
  have hb3 : η * BΘ < ε / 3 := by
    simp only [η]; rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  calc |((∫ y, dpart (u n) k y * ψ y) - ∫ y, dpart (u n) k y * ψm y) +
        (-((∫ y, u n y * Dk Θ k (secT y)) - ∫ y, u₀ y * Dk Θ k (secT y))) +
        ((∫ y, lipGrad u₀ y k * ψm y) - ∫ y, lipGrad u₀ y k * ψ y)|
      ≤ D * δ + η * BΘ + L * δ := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add e1 ?_)) e2)
        rw [abs_neg]; exact e3
    _ < ε := by linarith

end SharpLSI
