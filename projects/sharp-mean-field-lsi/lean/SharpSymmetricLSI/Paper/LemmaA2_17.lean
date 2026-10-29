import SharpSymmetricLSI.Paper.LemmaA2_16
import SharpSymmetricLSI.Defs.D07_rStar

/-!
# R25 (A.9), part 17: assembly of `semigroup_lipschitz`
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

theorem nonneg_of_flatLipschitz (hd : 1 ≤ d) {L : ℝ} {h : Torus d → ℝ}
    (hh : FlatLipschitzWith L h) : 0 ≤ L := by
  set y : Torus d := liftT fun _ => (1 / 2 : ℝ)
  have hy : y ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, hd⟩
    simp only [y, liftT, Pi.zero_apply] at this
    rw [AddCircle.coe_eq_zero_iff] at this
    obtain ⟨n, hn⟩ := this
    simp only [zsmul_eq_mul, mul_one] at hn
    have h1 : (0 : ℝ) < n := by linarith
    have h2 : (n : ℝ) < 1 := by linarith
    have h3 : (0 : ℤ) < n := by exact_mod_cast h1
    have h4 : n < (1 : ℤ) := by exact_mod_cast h2
    omega
  have hpos : 0 < flatDist (0 : Torus d) y :=
    lt_of_lt_of_le (dist_pos.mpr hy.symm) (flatDist_comparison 0 y).1
  have := (abs_nonneg _).trans (hh 0 y)
  by_contra hL
  push_neg at hL
  nlinarith

section main

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **(A.9).** -/
theorem semigroup_lipschitz_aux (hd : 1 ≤ d) (hyp : Hyp V W KV KW)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) {p : Torus d → ℝ}
    (hp : (∀ x, 0 < p x) ∧ (μ : Measure (Torus d)) = densMeasure p)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    ∃ KQ : ℝ, 0 ≤ KQ ∧
      (∀ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) →
        ∀ ξ : Fin d → ℝ, -KQ * (∑ k, ξ k ^ 2) * ∫ x, φ x ≤
          ∫ x, -Real.log (p (liftT x)) * secondDirDeriv φ ξ x) ∧
      ∀ (t : ℝ), 0 ≤ t → ∀ (L : ℝ) (h : Torus d → ℝ), FlatLipschitzWith L h →
        ∃ g : Torus d → ℝ, FlatLipschitzWith (Real.exp (KQ * t) * L) g ∧
          ∀ j, ∫ x, g x * e j x ∂(μ : Measure (Torus d)) =
            Real.exp (-t * lam j) * ∫ x, h x * e j x ∂(μ : Measure (Torus d)) := by
  obtain ⟨K1, hK1, hs1⟩ := semiconvex_negLog hyp hμ hp
  obtain ⟨ρ, c, C, Lσ, hμρ, hρ, hρc, -⟩ := refSetup hyp hμ
  obtain ⟨K2, hK2, hs2⟩ := semiconvex_negLog hyp hμ ⟨fun x => hρ.pos.trans_le (hρ.lower x), hμρ⟩
  set KQ := max K1 K2
  have hmono : ∀ {K : ℝ}, K ≤ KQ → ∀ (φ : (Fin d → ℝ) → ℝ), (∀ x, 0 ≤ φ x) → ∀ ξ : Fin d → ℝ,
      -KQ * (∑ k, ξ k ^ 2) * ∫ x, φ x ≤ -K * (∑ k, ξ k ^ 2) * ∫ x, φ x := by
    intro K hK φ hφ0 ξ
    have hS : 0 ≤ ∑ k, ξ k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hI : 0 ≤ ∫ x, φ x := integral_nonneg hφ0
    nlinarith [mul_nonneg hS hI, mul_nonneg (mul_nonneg hS hI) (sub_nonneg.mpr hK)]
  refine ⟨KQ, le_max_of_le_left hK1, fun φ hφ hφc hφ0 ξ =>
    (hmono (le_max_left _ _) φ hφ0 ξ).trans (hs1 φ hφ hφc hφ0 ξ), fun t ht L h hh => ?_⟩
  have hQ : ∀ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) →
      ∀ ξ : Fin d → ℝ, -KQ * (∑ k, ξ k ^ 2) * ∫ x, φ x ≤
        ∫ x, -Real.log (ρ (liftT x)) * secondDirDeriv φ ξ x := fun φ hφ hφc hφ0 ξ =>
    (hmono (le_max_right _ _) φ hφ0 ξ).trans (hs2 φ hφ hφc hφ0 ξ)
  have hL0 := nonneg_of_flatLipschitz hd hh
  rw [hμρ] at he ⊢
  rcases ht.eq_or_lt with h0 | htpos
  · subst h0
    exact ⟨h, by simpa using hh, fun j => by simp⟩
  have hlift := lift_bound_of_flat hL0 hh
  have hhc : Continuous h := by
    refine continuous_of_liftT' (LipschitzWith.continuous (K := Real.toNNReal (L * d)) ?_)
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, Real.coe_toNNReal _ (mul_nonneg hL0 (Nat.cast_nonneg _)), abs_le]
    have h1 := hlift x y
    have h2 := hlift y x
    have hs : dE y x = dE x y := by
      simp only [dE]; congr 1; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hs] at h2
    have h3 := mul_le_mul_of_nonneg_left (dE_le_card_mul_dist hd x y) hL0
    simp only [Function.comp]
    constructor <;> nlinarith
  obtain ⟨Bh0, hBh0⟩ := isCompact_univ.exists_bound_of_continuousOn hhc.continuousOn
  obtain ⟨g, -, -, hgl, hgj⟩ := euler_lipschitz hρ hρc hQ he hd (le_max_of_le_left hK1) htpos hhc
    hL0 hlift (Bh0 := Bh0) fun y => by simpa [Real.norm_eq_abs] using hBh0 y (mem_univ _)
  exact ⟨g, flat_bound_of_lift hgl, hgj⟩

end main

end SharpLSI
