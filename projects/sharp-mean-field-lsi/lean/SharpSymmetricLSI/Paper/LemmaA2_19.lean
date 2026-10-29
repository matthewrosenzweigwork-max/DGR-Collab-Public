import SharpSymmetricLSI.Paper.LemmaA2_18

/-!
# R25 Lemma A.2, part 19: the semigroup series

`∑ e^{-tλ_j} C(1+λ_j)^q < ∞` for `t > 0` (Weyl, `summable_exp_poly`), and the series
`semi t h = ∑ e^{-tλ_j}⟨h, e_j⟩ eC_j` is the Lipschitz, sup-bounded function of `euler_lipschitz`
(`semi_props`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

theorem exp_neg_le_factorial_div {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.exp (-x) ≤ (n.factorial : ℝ) / x ^ n := by
  have h := Real.pow_div_factorial_le_exp x hx.le n
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
  exact h

section summ

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (hb : IsRefEigenbasis (densMeasure ρ) e lam)
include hρ hb

theorem summable_exp_poly (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) (Cc : ℝ) (hCc : 0 ≤ Cc) (q : ℕ) :
    Summable fun j => Real.exp (-t * lam j) * (Cc * (1 + lam j) ^ q) := by
  have hlam0 : ∀ j, 0 ≤ lam j := fun j => refLam_nonneg hρ hb j
  obtain ⟨c₀, hc₀, hw⟩ := weyl hρ hb hd
  have hl1 : 0 < lam 1 := refLam_pos hρ hb hd le_rfl
  set κ := 1 + 1 / lam 1
  have hdd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set m := q + d
  refine summable_of_le_div_sq (fun j => mul_nonneg (Real.exp_pos _).le
      (mul_nonneg hCc (pow_nonneg (by linarith [hlam0 j]) q)))
    (K := (m.factorial : ℝ) / t ^ m * Cc * κ ^ q / c₀ ^ d) fun j hj => ?_
  have hlj : lam 1 ≤ lam j := hb.mono hj
  have hlpos : 0 < lam j := hl1.trans_le hlj
  have h1 : 1 + lam j ≤ κ * lam j := by
    simp only [κ]; rw [add_mul, one_mul, div_mul_eq_mul_div, one_mul, add_comm]
    have : 1 ≤ lam j / lam 1 := (one_le_div hl1).mpr hlj
    linarith
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hwj : c₀ ^ d * (j : ℝ) ^ 2 ≤ lam j ^ d := by
    have h2 := pow_le_pow_left₀ (by positivity) (hw j hj) d
    have e : (c₀ * (j : ℝ) ^ (2 / (d : ℝ))) ^ d = c₀ ^ d * (j : ℝ) ^ 2 := by
      rw [mul_pow, ← Real.rpow_natCast ((j : ℝ) ^ (2 / (d : ℝ))), ← Real.rpow_mul hj0.le,
        div_mul_cancel₀ _ hdd]
      norm_num
    rwa [e] at h2
  have hexp : Real.exp (-t * lam j) ≤ (m.factorial : ℝ) / (t * lam j) ^ m := by
    rw [neg_mul]; exact exp_neg_le_factorial_div (by positivity) m
  have hM : Cc * (1 + lam j) ^ q ≤ Cc * (κ ^ q * lam j ^ q) := by
    refine mul_le_mul_of_nonneg_left ?_ hCc
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith [hlam0 j]) h1 q
  calc Real.exp (-t * lam j) * (Cc * (1 + lam j) ^ q)
      ≤ (m.factorial : ℝ) / (t * lam j) ^ m * (Cc * (κ ^ q * lam j ^ q)) :=
        mul_le_mul hexp hM (mul_nonneg hCc (pow_nonneg (by linarith [hlam0 j]) q)) (by positivity)
    _ = (m.factorial : ℝ) / t ^ m * Cc * κ ^ q / lam j ^ d := by
        simp only [m]; rw [mul_pow, pow_add]; field_simp; ring
    _ ≤ (m.factorial : ℝ) / t ^ m * Cc * κ ^ q / (c₀ ^ d * (j : ℝ) ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hwj
    _ = (m.factorial : ℝ) / t ^ m * Cc * κ ^ q / c₀ ^ d / (j : ℝ) ^ 2 := by rw [div_div]

end summ

/-- The semigroup series. -/
noncomputable def semi (P : Measure (Torus d)) (e eC : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (t : ℝ)
    (h : Torus d → ℝ) : Torus d → ℝ :=
  series (fun j => Real.exp (-t * lam j) * ∫ y, h y * e j y ∂P) eC

section semiprops

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
include hρ hb heC1 heCae hM hM' hS

theorem summable_semi_coeff {t : ℝ} (ht : 0 < t) {h : Torus d → ℝ}
    (hhm : AEStronglyMeasurable h (densMeasure ρ)) {B : ℝ} (hB : ∀ y, |h y| ≤ B) :
    Summable (fun j => |Real.exp (-t * lam j) * ∫ y, h y * e j y ∂densMeasure ρ| * M j) ∧
    Summable (fun j => |Real.exp (-t * lam j) * ∫ y, h y * e j y ∂densMeasure ρ| * M' j) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary _))
  have hM0 : ∀ j, 0 ≤ M j := fun j => (abs_nonneg _).trans (hM j (Classical.arbitrary _))
  have hM0' : ∀ j, 0 ≤ M' j := fun j => (norm_nonneg _).trans (hM' j 0)
  have hc : ∀ j, |Real.exp (-t * lam j) * ∫ y, h y * e j y ∂densMeasure ρ| ≤
      B * Real.exp (-t * lam j) := fun j => by
    rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_coeff_le_sup hρ hb hhm hB j) (Real.exp_pos _).le
  constructor
  · refine Summable.of_nonneg_of_le (fun j => mul_nonneg (abs_nonneg _) (hM0 j))
      (fun j => ?_) (((hS t ht).1).mul_left B)
    calc _ ≤ B * Real.exp (-t * lam j) * M j := mul_le_mul_of_nonneg_right (hc j) (hM0 j)
      _ = B * (Real.exp (-t * lam j) * M j) := by ring
  · refine Summable.of_nonneg_of_le (fun j => mul_nonneg (abs_nonneg _) (hM0' j))
      (fun j => ?_) (((hS t ht).2).mul_left B)
    calc _ ≤ B * Real.exp (-t * lam j) * M' j := mul_le_mul_of_nonneg_right (hc j) (hM0' j)
      _ = B * (Real.exp (-t * lam j) * M' j) := by ring

include hρc hQ in
/-- **The semigroup on Lipschitz functions.** -/
theorem semi_props (hd : 1 ≤ d) (hK0 : 0 ≤ K) {t : ℝ} (ht : 0 < t) {h : Torus d → ℝ}
    (hhc : Continuous h) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x y, h (liftT x) - h (liftT y) ≤ L * dE x y) {B : ℝ} (hB : ∀ y, |h y| ≤ B) :
    ContDiff ℝ 1 (semi (densMeasure ρ) e eC lam t h ∘ liftT) ∧
    (∀ x y, semi (densMeasure ρ) e eC lam t h (liftT x) - semi (densMeasure ρ) e eC lam t h (liftT y)
      ≤ Real.exp (K * t) * L * dE x y) ∧
    (∀ y, |semi (densMeasure ρ) e eC lam t h y| ≤ B) ∧
    ∀ j, ∫ y, semi (densMeasure ρ) e eC lam t h y * e j y ∂densMeasure ρ =
      Real.exp (-t * lam j) * ∫ y, h y * e j y ∂densMeasure ρ := by
  obtain ⟨hs1, hs2⟩ := summable_semi_coeff hρ hb heC1 heCae hM hM' hS ht
    hhc.aestronglyMeasurable hB
  have hc1 : ContDiff ℝ 1 (semi (densMeasure ρ) e eC lam t h ∘ liftT) :=
    contDiff_series heC1 hM hM' hs1 hs2
  have hcoef : ∀ j, ∫ y, semi (densMeasure ρ) e eC lam t h y * e j y ∂densMeasure ρ =
      Real.exp (-t * lam j) * ∫ y, h y * e j y ∂densMeasure ρ := fun j =>
    coeff_series hρ hb heC1 heCae hM hs1 j
  obtain ⟨g, hgc, hgB, hgl, hgj⟩ := euler_lipschitz hρ hρc hQ hb hd hK0 ht hhc hL0 hL hB
  have heq : semi (densMeasure ρ) e eC lam t h = g :=
    eq_of_coeff_eq hρ hρc hb (continuous_of_liftT' hc1.continuous) hgc
      fun j => by rw [hcoef, hgj]
  rw [heq] at hc1 ⊢
  exact ⟨hc1, hgl, hgB, hgj⟩

end semiprops

end SharpLSI
