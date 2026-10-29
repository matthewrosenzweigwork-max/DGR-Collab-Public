import SharpSymmetricLSI.Paper.LemmaA2_28

/-!
# R25 Lemma A.2, part 29: helpers for the final assembly

* `tendsto_zero_of_forall_real`: an `ℝ≥0∞`-valued sequence tends to `0` if it is eventually
  bounded by `ofReal ε` for every real `ε > 0`;
* `slice_lipGrad_bound`: Euclidean Lipschitz bounds on lifts bound slice gradients;
* `weakGradC_add_ae`: the weak gradient of a sum of two Lipschitz kernels on `Config 2 d` is the
  sum of the slice gradients, `μ^{⊗2}`-a.e.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

theorem tendsto_zero_of_forall_real {f : ℕ → ℝ≥0∞}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ R in atTop, f R ≤ ENNReal.ofReal ε) : Tendsto f atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  by_cases htop : η = ⊤
  · exact Eventually.of_forall fun R => htop ▸ le_top
  have hpos : 0 < η.toReal := ENNReal.toReal_pos hη.ne' htop
  filter_upwards [h _ hpos] with R hR
  exact hR.trans (ENNReal.ofReal_toReal htop).le

theorem slice_lipGrad_bound (hd : 1 ≤ d) {f : Torus d → ℝ} {L : ℝ} (hL0 : 0 ≤ L)
    (hf : ∀ a b, f (liftT a) - f (liftT b) ≤ L * dE a b) (x : Torus d) (k : Fin d) :
    |lipGrad f x k| ≤ L * d := by
  have := abs_lipGrad_le (lipschitzWith_of_lift_bound hd hL0 hf) x k
  rwa [Real.coe_toNNReal _ (mul_nonneg hL0 (Nat.cast_nonneg _))] at this

theorem sqNorm_le_of_abs_le {v : Fin d → ℝ} {B : ℝ} (h : ∀ k, |v k| ≤ B) :
    sqNorm v ≤ d * B ^ 2 := by
  calc sqNorm v ≤ ∑ _k : Fin d, B ^ 2 := Finset.sum_le_sum fun k _ => by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h k) 2
    _ = d * B ^ 2 := by simp

/-- **Weak gradients of sums of Lipschitz kernels.** -/
theorem weakGradC_add_ae {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hac : μ ≪ haar d)
    {G₁ G₂ : Torus d → Torus d → ℝ} (hG₁ : Continuous (Function.uncurry G₁))
    (hG₂ : Continuous (Function.uncurry G₂)) {L : ℝ} (hL : 0 ≤ L)
    (h₁ : ∀ y a b, G₁ (liftT a) y - G₁ (liftT b) y ≤ L * dE a b)
    (h₂ : ∀ x a b, G₁ x (liftT a) - G₁ x (liftT b) ≤ L * dE a b)
    (h₃ : ∀ y a b, G₂ (liftT a) y - G₂ (liftT b) y ≤ L * dE a b)
    (h₄ : ∀ x a b, G₂ x (liftT a) - G₂ x (liftT b) ≤ L * dE a b) :
    ∀ᵐ X ∂Measure.pi (fun _ : Fin 2 => μ), ∀ k,
      weakGradC (kerC2 fun x y => G₁ x y + G₂ x y) X 0 k =
        lipGrad (fun x => G₁ x (X 1)) (X 0) k + lipGrad (fun x => G₂ x (X 1)) (X 0) k ∧
      weakGradC (kerC2 fun x y => G₁ x y + G₂ x y) X 1 k =
        lipGrad (fun y => G₁ (X 0) y) (X 1) k + lipGrad (fun y => G₂ (X 0) y) (X 1) k := by
  have hw₁ := isWeakGrad_lipGrad (continuous_kerC2_unflat hG₁) (lipschitz_kerC2 hL hL h₁ h₂)
  have hw₂ := isWeakGrad_lipGrad (continuous_kerC2_unflat hG₂) (lipschitz_kerC2 hL hL h₃ h₄)
  have hw := hw₁.add hw₂
  have hS : (fun Y => (kerC2 G₁ ∘ unflat) Y + (kerC2 G₂ ∘ unflat) Y) =
      kerC2 (fun x y => G₁ x y + G₂ x y) ∘ unflat := rfl
  rw [hS] at hw
  have hae := weakGrad_ae_unique (isWeakGrad_weakGrad ⟨_, hw⟩) hw
  filter_upwards [ae_pi_of_ae_flat hac hae] with X hX
  intro k
  simp only [weakGradC]
  rw [hX]
  simp only
  rw [lipGrad_kerC_zero, lipGrad_kerC_zero, lipGrad_kerC_one, lipGrad_kerC_one]
  exact ⟨rfl, rfl⟩

end SharpLSI
