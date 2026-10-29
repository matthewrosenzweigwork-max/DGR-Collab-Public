import SharpSymmetricLSI.Paper.LemmaA2_25
import SharpSymmetricLSI.Paper.R37Particle
import SharpSymmetricLSI.Paper.ForceExp

/-!
# R25 Lemma A.2, part 26: kernels on `Config 2 d`

For a kernel `G` with Euclidean Lipschitz bounds in each variable, `kerC2 G` is Lipschitz on the
flattened torus, and its weak gradient in block `0` (resp. `1`) is the gradient of the `x`-slice
(resp. `y`-slice) almost everywhere (`weakGradC_kerC_ae`); `μ^{⊗2}`-integrals are iterated
integrals (`lintegral_pi_two`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

theorem ae_pi_of_ae_flat {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hac : μ ≪ haar d)
    {p : UnitAddTorus (Fin 2 × Fin d) → Prop} (h : ∀ᵐ Y ∂(volume : Measure (UnitAddTorus (Fin 2 × Fin d))), p Y) :
    ∀ᵐ X ∂Measure.pi (fun _ : Fin 2 => μ), p (flat X) := by
  have hmp : MeasurePreserving (flat : Config 2 d → UnitAddTorus (Fin 2 × Fin d)) volume volume :=
    ⟨measurable_flat, map_flat_volume 2⟩
  exact (pi_ac_volume hac 2).ae_le (hmp.quasiMeasurePreserving.ae h)

/-- A kernel as a function on `Config 2 d` (same as `kerC`). -/
def kerC2 (G : Torus d → Torus d → ℝ) (X : Config 2 d) : ℝ := G (X 0) (X 1)

theorem kerC_unflat_liftT (G : Torus d → Torus d → ℝ) (z : Fin 2 × Fin d → ℝ) :
    (kerC2 G ∘ unflat) (liftT z) = G (liftT fun k => z (0, k)) (liftT fun k => z (1, k)) := rfl

theorem kerC2_unflat_liftT (G : Torus d → Torus d → ℝ) (z : Fin 2 × Fin d → ℝ) :
    kerC2 G (unflat (liftT z)) = G (liftT fun k => z (0, k)) (liftT fun k => z (1, k)) := rfl

/-- Block-`0` line derivatives of `kerC2 G` are slice line derivatives. -/
theorem lipGrad_kerC_zero (G : Torus d → Torus d → ℝ) (X : Config 2 d) (k : Fin d) :
    lipGrad (kerC2 G ∘ unflat) (flat X) (0, k) = lipGrad (fun x => G x (X 1)) (X 0) k := by
  simp only [lipGrad, lineDeriv]
  congr 1
  funext t
  simp only [Function.comp, kerC2_unflat_liftT]
  have hA : (fun k' : Fin d => (secT (flat X) + t • Pi.single ((0 : Fin 2), k) (1 : ℝ) :
      Fin 2 × Fin d → ℝ) (0, k')) = secT (X 0) + t • Pi.single k (1 : ℝ) := by
    funext k'
    by_cases h : k' = k
    · subst h; simp; rfl
    · simp [Pi.single_apply, h]; rfl
  have hB : (fun k' : Fin d => (secT (flat X) + t • Pi.single ((0 : Fin 2), k) (1 : ℝ) :
      Fin 2 × Fin d → ℝ) (1, k')) = secT (X 1) := by
    funext k'; simp [Pi.single_apply]; rfl
  rw [hA, hB, liftT_secT]

/-- Block-`1` line derivatives of `kerC2 G` are slice line derivatives. -/
theorem lipGrad_kerC_one (G : Torus d → Torus d → ℝ) (X : Config 2 d) (k : Fin d) :
    lipGrad (kerC2 G ∘ unflat) (flat X) (1, k) = lipGrad (fun y => G (X 0) y) (X 1) k := by
  simp only [lipGrad, lineDeriv]
  congr 1
  funext t
  simp only [Function.comp, kerC2_unflat_liftT]
  have hA : (fun k' : Fin d => (secT (flat X) + t • Pi.single ((1 : Fin 2), k) (1 : ℝ) :
      Fin 2 × Fin d → ℝ) (1, k')) = secT (X 1) + t • Pi.single k (1 : ℝ) := by
    funext k'
    by_cases h : k' = k
    · subst h; simp; rfl
    · simp [Pi.single_apply, h]; rfl
  have hB : (fun k' : Fin d => (secT (flat X) + t • Pi.single ((1 : Fin 2), k) (1 : ℝ) :
      Fin 2 × Fin d → ℝ) (0, k')) = secT (X 0) := by
    funext k'; simp [Pi.single_apply]; rfl
  rw [hA, hB, liftT_secT]

theorem lipschitz_kerC2 {G : Torus d → Torus d → ℝ} {L₁ L₂ : ℝ} (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (h₁ : ∀ y a b, G (liftT a) y - G (liftT b) y ≤ L₁ * dE a b)
    (h₂ : ∀ x a b, G x (liftT a) - G x (liftT b) ≤ L₂ * dE a b) :
    LipschitzWith (Real.toNNReal ((L₁ + L₂) * d)) ((kerC2 G ∘ unflat) ∘ liftT) := by
  refine LipschitzWith.of_dist_le_mul fun z z' => ?_
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  simp only [Function.comp_apply, kerC_unflat_liftT]
  set a : Fin d → ℝ := fun k => z (0, k)
  set a' : Fin d → ℝ := fun k => z' (0, k)
  set b : Fin d → ℝ := fun k => z (1, k)
  set b' : Fin d → ℝ := fun k => z' (1, k)
  have hD : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hdist : ∀ (u u' : Fin d → ℝ), (∀ k, |u k - u' k| ≤ dist z z') → dE u u' ≤ d * dist z z' := by
    intro u u' hu
    rw [dE, Real.sqrt_le_left (by positivity)]
    calc ∑ k, (u k - u' k) ^ 2 ≤ ∑ _k : Fin d, dist z z' ^ 2 := Finset.sum_le_sum fun k _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hu k) 2
      _ = d * dist z z' ^ 2 := by simp
      _ ≤ (d * dist z z') ^ 2 := by
          rcases Nat.eq_zero_or_pos d with h0 | hpos
          · subst h0; simp
          · have : (1 : ℝ) ≤ d := by exact_mod_cast hpos
            nlinarith [sq_nonneg (dist z z'), dist_nonneg (x := z) (y := z')]
  have hcoord : ∀ p, |z p - z' p| ≤ dist z z' := fun p => by
    rw [← Real.dist_eq]; exact dist_le_pi_dist z z' p
  have ha := hdist a a' fun k => hcoord _
  have hb := hdist b b' fun k => hcoord _
  have e1 : |G (liftT a) (liftT b) - G (liftT a') (liftT b)| ≤ L₁ * dE a a' := by
    rw [abs_le]; have g1 := h₁ (liftT b) a a'; have g2 := h₁ (liftT b) a' a
    rw [dE_symm'] at g2; constructor <;> linarith
  have e2 : |G (liftT a') (liftT b) - G (liftT a') (liftT b')| ≤ L₂ * dE b b' := by
    rw [abs_le]; have g1 := h₂ (liftT a') b b'; have g2 := h₂ (liftT a') b' b
    rw [dE_symm'] at g2; constructor <;> linarith
  calc |G (liftT a) (liftT b) - G (liftT a') (liftT b')|
      ≤ |G (liftT a) (liftT b) - G (liftT a') (liftT b)| +
        |G (liftT a') (liftT b) - G (liftT a') (liftT b')| := by
        have := abs_add_le (G (liftT a) (liftT b) - G (liftT a') (liftT b))
          (G (liftT a') (liftT b) - G (liftT a') (liftT b'))
        rwa [sub_add_sub_cancel] at this
    _ ≤ L₁ * dE a a' + L₂ * dE b b' := add_le_add e1 e2
    _ ≤ (L₁ + L₂) * d * dist z z' := by
        nlinarith [mul_le_mul_of_nonneg_left ha hL₁, mul_le_mul_of_nonneg_left hb hL₂]

theorem continuous_kerC2_unflat {G : Torus d → Torus d → ℝ} (hG : Continuous (Function.uncurry G)) :
    Continuous (kerC2 G ∘ unflat) := by
  have h0 : Continuous fun Y : UnitAddTorus (Fin 2 × Fin d) => unflat Y 0 :=
    continuous_pi fun k => continuous_apply ((0 : Fin 2), k)
  have h1 : Continuous fun Y : UnitAddTorus (Fin 2 × Fin d) => unflat Y 1 :=
    continuous_pi fun k => continuous_apply ((1 : Fin 2), k)
  exact hG.comp (h0.prodMk h1)

/-- **Weak gradients of kernels on `Config 2 d` are slice gradients.** -/
theorem weakGradC_kerC_ae {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hac : μ ≪ haar d)
    {G : Torus d → Torus d → ℝ} (hG : Continuous (Function.uncurry G)) {L₁ L₂ : ℝ}
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (h₁ : ∀ y a b, G (liftT a) y - G (liftT b) y ≤ L₁ * dE a b)
    (h₂ : ∀ x a b, G x (liftT a) - G x (liftT b) ≤ L₂ * dE a b) :
    ∀ᵐ X ∂Measure.pi (fun _ : Fin 2 => μ), ∀ k,
      weakGradC (kerC2 G) X 0 k = lipGrad (fun x => G x (X 1)) (X 0) k ∧
      weakGradC (kerC2 G) X 1 k = lipGrad (fun y => G (X 0) y) (X 1) k := by
  have hw := isWeakGrad_lipGrad (continuous_kerC2_unflat hG) (lipschitz_kerC2 hL₁ hL₂ h₁ h₂)
  have hae := weakGrad_ae_unique (isWeakGrad_weakGrad ⟨_, hw⟩) hw
  filter_upwards [ae_pi_of_ae_flat hac hae] with X hX
  intro k
  simp only [weakGradC]
  rw [hX, lipGrad_kerC_zero, lipGrad_kerC_one]
  exact ⟨rfl, rfl⟩

theorem lintegral_pi_two {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (f : Config 2 d → ℝ≥0∞) :
    ∫⁻ X, f X ∂Measure.pi (fun _ : Fin 2 => μ) = ∫⁻ p, f ![p.1, p.2] ∂μ.prod μ := by
  have h := (measurePreserving_finTwoArrow μ).lintegral_comp_emb
    (MeasurableEquiv.finTwoArrow.measurableEmbedding) (fun p => f ![p.1, p.2])
  rw [← h]
  congr 1; funext X
  congr 1; funext i; fin_cases i <;> rfl

theorem ae_pi_two_of_ae_prod {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {p : Torus d → Torus d → Prop} (h : ∀ᵐ q ∂μ.prod μ, p q.1 q.2) :
    ∀ᵐ X ∂Measure.pi (fun _ : Fin 2 => μ), p (X 0) (X 1) :=
  (measurePreserving_finTwoArrow μ).quasiMeasurePreserving.ae h

end SharpLSI
