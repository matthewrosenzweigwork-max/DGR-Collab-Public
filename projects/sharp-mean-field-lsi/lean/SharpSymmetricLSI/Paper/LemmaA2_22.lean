import SharpSymmetricLSI.Paper.LemmaA2_21

/-!
# R25 Lemma A.2, part 22: coefficients of `K_t` and convergence `K_t → K`

`K_t` has product coefficients `e^{-t(λ_i+λ_j)} T_{ij}` (`Kt_coeff2`); with Parseval and the
weighted Hilbert–Schmidt identity on `μ ⊗ μ` this gives `∬ (K_t - K)² → 0` and
`∬ |∇_x(K_t - K)|² → 0` as `t → 0` (`tendsto_L2_Kt`, `tendsto_energy_Kt`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

theorem continuous_uncurry_of_lip (hd : 1 ≤ d) {f : Torus d → Torus d → ℝ} {L₁ L₂ : ℝ}
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (h₁ : ∀ y a b, f (liftT a) y - f (liftT b) y ≤ L₁ * dE a b)
    (h₂ : ∀ x a b, f x (liftT a) - f x (liftT b) ≤ L₂ * dE a b) :
    Continuous (Function.uncurry f) := by
  have hD : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have e₁ : ∀ x x' y, |f x y - f x' y| ≤ L₁ * d * dist x x' := by
    intro x x' y
    obtain ⟨a, b, rfl, rfl, hab, -⟩ := dE_close_lifts hd x x'
    rw [abs_le]
    have h1 := h₁ y a b; have h2 := h₁ y b a; rw [dE_symm'] at h2
    have := mul_le_mul_of_nonneg_left hab hL₁
    constructor <;> nlinarith
  have e₂ : ∀ x y y', |f x y - f x y'| ≤ L₂ * d * dist y y' := by
    intro x y y'
    obtain ⟨a, b, rfl, rfl, hab, -⟩ := dE_close_lifts hd y y'
    rw [abs_le]
    have h1 := h₂ x a b; have h2 := h₂ x b a; rw [dE_symm'] at h2
    have := mul_le_mul_of_nonneg_left hab hL₂
    constructor <;> nlinarith
  refine LipschitzWith.continuous (K := Real.toNNReal ((L₁ + L₂) * d)) ?_
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  have hp : dist p.1 q.1 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hq : dist p.2 q.2 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_right _ _
  calc |f p.1 p.2 - f q.1 q.2| ≤ |f p.1 p.2 - f q.1 p.2| + |f q.1 p.2 - f q.1 q.2| := by
        have := abs_add_le (f p.1 p.2 - f q.1 p.2) (f q.1 p.2 - f q.1 q.2)
        rwa [sub_add_sub_cancel] at this
    _ ≤ L₁ * d * dist p.1 q.1 + L₂ * d * dist p.2 q.2 := add_le_add (e₁ _ _ _) (e₂ _ _ _)
    _ ≤ (L₁ + L₂) * d * dist p q := by nlinarith [mul_nonneg hL₁ hD, mul_nonneg hL₂ hD]

section fub

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (hb : IsRefEigenbasis (densMeasure ρ) e lam)
include hρ hb

/-- **Fubini for coefficients.** -/
theorem fubini_coeff {A : Torus d → Torus d → ℝ} (hA : Continuous (Function.uncurry A)) (i j : ℕ) :
    ∫ y, (∫ x, A x y * e i x ∂densMeasure ρ) * e j y ∂densMeasure ρ =
      ∫ x, (∫ y, A x y * e j y ∂densMeasure ρ) * e i x ∂densMeasure ρ := by
  haveI := hρ.isProb
  set P := densMeasure ρ
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hA.continuousOn
  have hei : ∀ i, Integrable (e i) P := fun i => ((hb.memH1 i).2.1).integrable one_le_two
  have hint : Integrable (fun p : Torus d × Torus d => A p.1 p.2 * (e i p.1 * e j p.2)) (P.prod P) :=
    ((hei i).mul_prod (hei j)).bdd_mul (c := B) hA.aestronglyMeasurable
      (Eventually.of_forall fun p => hB p (mem_univ _))
  have h1 := integral_prod _ hint
  have h2 := integral_prod_symm _ hint
  simp only at h1 h2
  have l : ∫ y, (∫ x, A x y * e i x ∂P) * e j y ∂P =
      ∫ y, ∫ x, A x y * (e i x * e j y) ∂P ∂P := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only; rw [← integral_mul_const]; congr 1; funext x; ring
  have r : ∫ x, (∫ y, A x y * e j y ∂P) * e i x ∂P =
      ∫ x, ∫ y, A x y * (e i x * e j y) ∂P ∂P := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only; rw [← integral_mul_const]; congr 1; funext y; ring
  rw [l, r, ← h1, ← h2]

end fub

section ktc

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C) (hρc : Continuous ρ) {K : ℝ}
  (hQ : ∀ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) →
      ∀ ξ : Fin d → ℝ, -K * (∑ k, ξ k ^ 2) * ∫ x, φ x ≤
        ∫ x, -Real.log (ρ (liftT x)) * secondDirDeriv φ ξ x)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (hb : IsRefEigenbasis (densMeasure ρ) e lam)
  {eC : ℕ → Torus d → ℝ} (heC1 : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT))
  (heCae : ∀ j, eC j =ᵐ[densMeasure ρ] e j)
  {M M' : ℕ → ℝ} (hM : ∀ j x, |eC j x| ≤ M j) (hM' : ∀ j x, ‖fderiv ℝ (eC j ∘ liftT) x‖ ≤ M' j)
  (hS : ∀ t, 0 < t → Summable (fun j => Real.exp (-t * lam j) * M j) ∧
    Summable (fun j => Real.exp (-t * lam j) * M' j))
  (hd : 1 ≤ d) (hK0 : 0 ≤ K) {Kf : Torus d → Torus d → ℝ}
  (hKc : Continuous (Function.uncurry Kf)) {BK : ℝ} (hBK : ∀ x y, |Kf x y| ≤ BK) {LK : ℝ}
  (hLK0 : 0 ≤ LK) (hL1 : ∀ y a b, Kf (liftT a) y - Kf (liftT b) y ≤ LK * dE a b)
  (hL2 : ∀ x a b, Kf x (liftT a) - Kf x (liftT b) ≤ LK * dE a b)
include hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2

theorem continuous_Kt {t : ℝ} (ht : 0 < t) :
    Continuous (Function.uncurry (Kt (densMeasure ρ) e eC lam t Kf)) := by
  obtain ⟨-, h1, h2, -, -⟩ := Kt_props hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 ht hKc hBK hLK0
    hL1 hL2
  have hE : 0 ≤ Real.exp (K * t) * LK := mul_nonneg (Real.exp_pos _).le hLK0
  exact continuous_uncurry_of_lip hd hE hE h1 h2

theorem continuous_Mt {t : ℝ} (ht : 0 < t) :
    Continuous (Function.uncurry (Mt (densMeasure ρ) e eC lam t Kf)) := by
  obtain ⟨h1, -, h2, -, -⟩ := Mt_facts hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 ht hKc hBK hLK0
    hL1 hL2
  have hE : 0 ≤ Real.exp (K * t) * LK := mul_nonneg (Real.exp_pos _).le hLK0
  exact continuous_uncurry_of_lip hd hLK0 hE h1 h2

/-- **Product coefficients of `K_t`.** -/
theorem Kt_coeff2 {t : ℝ} (ht : 0 < t) (i j : ℕ) :
    ∫ y, (∫ x, Kt (densMeasure ρ) e eC lam t Kf x y * e i x ∂densMeasure ρ) * e j y ∂densMeasure ρ =
      Real.exp (-t * lam i) * Real.exp (-t * lam j) *
        ∫ y, (∫ x, Kf x y * e i x ∂densMeasure ρ) * e j y ∂densMeasure ρ := by
  obtain ⟨-, -, -, -, hKcoef⟩ := Kt_props hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 ht hKc hBK hLK0
    hL1 hL2
  obtain ⟨-, -, -, hMcoef, -⟩ := Mt_facts hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 ht hKc hBK hLK0
    hL1 hL2
  simp_rw [hKcoef]
  have e1 : ∫ y, Real.exp (-t * lam i) * (∫ x, Mt (densMeasure ρ) e eC lam t Kf x y * e i x ∂densMeasure ρ) * e j y ∂densMeasure ρ =
      Real.exp (-t * lam i) * ∫ y, (∫ x, Mt (densMeasure ρ) e eC lam t Kf x y * e i x ∂densMeasure ρ) * e j y ∂densMeasure ρ := by
    rw [← integral_const_mul]; congr 1; funext y; ring
  rw [e1, fubini_coeff hρ hb (continuous_Mt hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0
    hL1 hL2 ht) i j, fubini_coeff hρ hb hKc i j]
  simp_rw [hMcoef]
  have e2 : ∫ x, Real.exp (-t * lam j) * (∫ y, Kf x y * e j y ∂densMeasure ρ) * e i x ∂densMeasure ρ =
      Real.exp (-t * lam j) * ∫ x, (∫ y, Kf x y * e j y ∂densMeasure ρ) * e i x ∂densMeasure ρ := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  rw [e2]; ring

end ktc

end SharpLSI
