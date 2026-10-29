import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Exact reduced quartic polynomial and its three minima (packet STR027)

With `a = hA`, `b = hB` the fourth-order angular deficit before stable-mode elimination is the
polynomial `quarticDeficit A B C D E F` (campaign/threefold_circle_lsi_base.md, section 4).

* `threefold_reducedQuartic`: `quarticDeficit - reducedQuartic` is an explicit sum of squares
  of the stable-mode offsets, so the minimum over `(C,D,E,F)` is attained exactly at
  `C = A/2 + (B²-A²)/12`, `D = -B/2 - AB/6`, `E = -A/10`, `F = -B/10`, with value
  `reducedQuartic A B = (A²+B²)²/48 - (A³-3AB²)/12 - 9(A²+B²)/20`.
* `reducedQuotient_exact_minimizers`: the quotient `Q = 2 J4red / R²` equals
  `-9/10 + R²/24 - R cos 3φ / 6`; its global minimum `-16/15` is attained exactly at
  `R = 2`, `φ ∈ {0, 2π/3, 4π/3} (mod 2π)`, i.e. at `(A,B) ∈ {(2,0), (-1,±√3)}`; both Hessians
  are nondegenerate (radial `1/12`, angular `3`), and `Q → -9/10` at the endpoint `R → 0`,
  strictly above `-16/15`.
-/

open Filter Topology

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The fourth-order angular deficit before stable-mode elimination. -/
noncomputable def quarticDeficit (A B C D E F : ℝ) : ℝ :=
  (3 * A ^ 4 - 20 * A ^ 3 + 6 * A ^ 2 * B ^ 2 + 24 * A ^ 2 * C + 60 * A * B ^ 2
    + 48 * A * B * D - 144 * A * C + 144 * A * E + 3 * B ^ 4 - 24 * B ^ 2 * C
    + 144 * B * D + 144 * B * F + 144 * C ^ 2 + 144 * D ^ 2 + 720 * E ^ 2 + 720 * F ^ 2) / 96

/-- The reduced quartic after eliminating the stable harmonics. -/
noncomputable def reducedQuartic (A B : ℝ) : ℝ :=
  (A ^ 2 + B ^ 2) ^ 2 / 48 - (A ^ 3 - 3 * A * B ^ 2) / 12 - 9 * (A ^ 2 + B ^ 2) / 20

/-- The optimal stable second/fourth harmonic coefficients. -/
noncomputable def stableC (A B : ℝ) : ℝ := A / 2 + (B ^ 2 - A ^ 2) / 12
noncomputable def stableD (A B : ℝ) : ℝ := -B / 2 - A * B / 6
noncomputable def stableE (A : ℝ) : ℝ := -A / 10
noncomputable def stableF (B : ℝ) : ℝ := -B / 10

/-- Leading quotient coefficient in polar form `-9/10 + R²/24 - R cos 3φ / 6`. -/
noncomputable def reducedQuotientPolar (R φ : ℝ) : ℝ :=
  -9 / 10 + R ^ 2 / 24 - R * Real.cos (3 * φ) / 6

/-- Leading quotient coefficient in Cartesian form `-9/10 + R²/24 - (A³-3AB²)/(6R²)`. -/
noncomputable def reducedQuotient (A B : ℝ) : ℝ :=
  -9 / 10 + (A ^ 2 + B ^ 2) / 24 - (A ^ 3 - 3 * A * B ^ 2) / (6 * (A ^ 2 + B ^ 2))

theorem quarticDeficit_sub_reduced (A B C D E F : ℝ) :
    quarticDeficit A B C D E F - reducedQuartic A B =
      (144 * (C - stableC A B) ^ 2 + 144 * (D - stableD A B) ^ 2
        + 720 * (E - stableE A) ^ 2 + 720 * (F - stableF B) ^ 2) / 96 := by
  unfold quarticDeficit reducedQuartic stableC stableD stableE stableF
  ring

theorem threefold_reducedQuartic (A B : ℝ) :
    (∀ C D E F : ℝ, reducedQuartic A B ≤ quarticDeficit A B C D E F) ∧
    quarticDeficit A B (stableC A B) (stableD A B) (stableE A) (stableF B)
      = reducedQuartic A B ∧
    (∀ C D E F : ℝ, quarticDeficit A B C D E F = reducedQuartic A B ↔
      C = stableC A B ∧ D = stableD A B ∧ E = stableE A ∧ F = stableF B) ∧
    reducedQuartic A B =
      (A ^ 2 + B ^ 2) ^ 2 / 48 - (A ^ 3 - 3 * A * B ^ 2) / 12 - 9 * (A ^ 2 + B ^ 2) / 20 := by
  refine ⟨fun C D E F => ?_, ?_, fun C D E F => ?_, rfl⟩
  · have := quarticDeficit_sub_reduced A B C D E F
    have h : 0 ≤ quarticDeficit A B C D E F - reducedQuartic A B := by
      rw [this]; positivity
    linarith
  · have := quarticDeficit_sub_reduced A B (stableC A B) (stableD A B) (stableE A) (stableF B)
    simp at this
    linarith
  · have h := quarticDeficit_sub_reduced A B C D E F
    constructor
    · intro e
      have h0 : (144 * (C - stableC A B) ^ 2 + 144 * (D - stableD A B) ^ 2
          + 720 * (E - stableE A) ^ 2 + 720 * (F - stableF B) ^ 2) = 0 := by
        have : quarticDeficit A B C D E F - reducedQuartic A B = 0 := by linarith
        rw [h] at this; linarith
      have h1 : 0 ≤ (C - stableC A B) ^ 2 := sq_nonneg _
      have h2 : 0 ≤ (D - stableD A B) ^ 2 := sq_nonneg _
      have h3 : 0 ≤ (E - stableE A) ^ 2 := sq_nonneg _
      have h4 : 0 ≤ (F - stableF B) ^ 2 := sq_nonneg _
      have e1 : (C - stableC A B) ^ 2 = 0 := by linarith
      have e2 : (D - stableD A B) ^ 2 = 0 := by linarith
      have e3 : (E - stableE A) ^ 2 = 0 := by linarith
      have e4 : (F - stableF B) ^ 2 = 0 := by linarith
      refine ⟨?_, ?_, ?_, ?_⟩
      · linarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 e1]
      · linarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 e2]
      · linarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 e3]
      · linarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 e4]
    · rintro ⟨rfl, rfl, rfl, rfl⟩
      simp at h
      linarith

theorem reducedQuotient_eq_two_mul_reducedQuartic_div (A B : ℝ) (h : A ^ 2 + B ^ 2 ≠ 0) :
    reducedQuotient A B = 2 * reducedQuartic A B / (A ^ 2 + B ^ 2) := by
  unfold reducedQuotient reducedQuartic
  field_simp
  ring

theorem reducedQuotient_polar (R φ : ℝ) :
    reducedQuotient (R * Real.cos φ) (R * Real.sin φ) = reducedQuotientPolar R φ := by
  have hs : (R * Real.cos φ) ^ 2 + (R * Real.sin φ) ^ 2 = R ^ 2 := by
    have := Real.sin_sq_add_cos_sq φ
    nlinarith
  have hc : (R * Real.cos φ) ^ 3 - 3 * (R * Real.cos φ) * (R * Real.sin φ) ^ 2
      = R ^ 3 * Real.cos (3 * φ) := by
    rw [Real.cos_three_mul]
    have := Real.sin_sq φ
    have e : (R * Real.sin φ) ^ 2 = R ^ 2 * (1 - Real.cos φ ^ 2) := by rw [mul_pow, this]
    rw [e]; ring
  unfold reducedQuotient reducedQuotientPolar
  rw [hs, hc]
  field_simp

theorem reducedQuotientPolar_sub (R φ : ℝ) :
    reducedQuotientPolar R φ + 16 / 15 = (R - 2) ^ 2 / 24 + R * (1 - Real.cos (3 * φ)) / 6 := by
  unfold reducedQuotientPolar; ring

theorem reducedQuotientPolar_minimizers (R φ : ℝ) (hR : 0 < R) :
    -16 / 15 ≤ reducedQuotientPolar R φ ∧
    (reducedQuotientPolar R φ = -16 / 15 ↔ R = 2 ∧ ∃ k : ℤ, φ = 2 * Real.pi * k / 3) := by
  have key := reducedQuotientPolar_sub R φ
  have hc := Real.cos_le_one (3 * φ)
  have t1 : 0 ≤ R * (1 - Real.cos (3 * φ)) := mul_nonneg hR.le (by linarith)
  refine ⟨by nlinarith [sq_nonneg (R - 2)], ⟨fun h => ?_, fun ⟨hR2, k, hk⟩ => ?_⟩⟩
  · have h0 : (R - 2) ^ 2 / 24 + R * (1 - Real.cos (3 * φ)) / 6 = 0 := by linarith
    have e1 : (R - 2) ^ 2 = 0 := by nlinarith [sq_nonneg (R - 2)]
    have e2 : R * (1 - Real.cos (3 * φ)) = 0 := by nlinarith [sq_nonneg (R - 2)]
    have hR2 : R = 2 := by linarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.1 e1]
    refine ⟨hR2, ?_⟩
    have : Real.cos (3 * φ) = 1 := by
      rcases mul_eq_zero.1 e2 with h | h
      · exact absurd h hR.ne'
      · linarith
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 this
    exact ⟨n, by linarith⟩
  · subst hR2
    have : Real.cos (3 * φ) = 1 := by
      rw [Real.cos_eq_one_iff]
      exact ⟨k, by rw [hk]; ring⟩
    rw [this] at key
    linarith

theorem reducedQuotient_minimizers (A B : ℝ) (h : A ^ 2 + B ^ 2 ≠ 0) :
    -16 / 15 ≤ reducedQuotient A B ∧
    (reducedQuotient A B = -16 / 15 ↔
      (A = 2 ∧ B = 0) ∨ (A = -1 ∧ B = Real.sqrt 3) ∨ (A = -1 ∧ B = -Real.sqrt 3)) := by
  have hs : 0 < A ^ 2 + B ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
  set s := A ^ 2 + B ^ 2 with hsdef
  set R := Real.sqrt s with hRdef
  have hR : 0 < R := Real.sqrt_pos.2 hs
  have hR2 : R ^ 2 = s := Real.sq_sqrt hs.le
  set c := A ^ 3 - 3 * A * B ^ 2 with hc
  have hcsq : c ^ 2 + (3 * A ^ 2 * B - B ^ 3) ^ 2 = s ^ 3 := by
    rw [hc, hsdef]; ring
  have hcle : c ≤ R ^ 3 := by
    have : c ^ 2 ≤ (R ^ 3) ^ 2 := by
      have : (R ^ 3) ^ 2 = s ^ 3 := by rw [← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul, hR2]
      nlinarith [sq_nonneg (3 * A ^ 2 * B - B ^ 3)]
    exact le_of_sq_le_sq this (by positivity) |>.trans le_rfl
  have eq : reducedQuotient A B + 16 / 15 = (R - 2) ^ 2 / 24 + (R ^ 3 - c) / (6 * s) := by
    unfold reducedQuotient
    rw [← hsdef, ← hc]
    have : R ^ 3 = R * s := by rw [← hR2]; ring
    rw [this]
    field_simp
    nlinarith [hR2]
  have t1 : 0 ≤ (R ^ 3 - c) / (6 * s) := div_nonneg (by linarith) (by positivity)
  refine ⟨by nlinarith [sq_nonneg (R - 2)], ⟨fun hq => ?_, fun hq => ?_⟩⟩
  · have h0 : (R - 2) ^ 2 / 24 + (R ^ 3 - c) / (6 * s) = 0 := by linarith
    have e1 : (R - 2) ^ 2 = 0 := by nlinarith [sq_nonneg (R - 2)]
    have e2 : (R ^ 3 - c) / (6 * s) = 0 := by nlinarith [sq_nonneg (R - 2)]
    have hR2' : R = 2 := by linarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.1 e1]
    have hs4 : s = 4 := by rw [← hR2, hR2']; norm_num
    have hc8 : c = 8 := by
      have : R ^ 3 - c = 0 := by
        rcases div_eq_zero_iff.1 e2 with h | h
        · exact h
        · exact absurd h (by positivity)
      rw [hR2'] at this; linarith
    have hB : B ^ 2 = 4 - A ^ 2 := by rw [hsdef] at hs4; linarith
    have hA : (A - 2) * (A + 1) ^ 2 = 0 := by
      rw [hc, hB] at hc8; nlinarith
    rcases mul_eq_zero.1 hA with h1 | h1
    · left
      have hA2 : A = 2 := by linarith
      refine ⟨hA2, ?_⟩
      rw [hA2] at hB; nlinarith
    · right
      have hA1 : A = -1 := by
        have := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 h1; linarith
      rw [hA1] at hB
      have h3 : B ^ 2 = Real.sqrt 3 ^ 2 := by rw [Real.sq_sqrt (by norm_num)]; linarith
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 h3 with h4 | h4
      · exact Or.inl ⟨hA1, h4⟩
      · exact Or.inr ⟨hA1, h4⟩
  · have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · unfold reducedQuotient; norm_num
    · unfold reducedQuotient
      have : (-1 : ℝ) ^ 2 + Real.sqrt 3 ^ 2 = 4 := by rw [hs3]; norm_num
      rw [this]
      have h3 : (-1 : ℝ) ^ 3 - 3 * (-1) * Real.sqrt 3 ^ 2 = 8 := by rw [hs3]; norm_num
      rw [h3]; norm_num
    · unfold reducedQuotient
      have : (-1 : ℝ) ^ 2 + (-Real.sqrt 3) ^ 2 = 4 := by rw [neg_sq (Real.sqrt 3), hs3]; norm_num
      rw [this]
      have h3 : (-1 : ℝ) ^ 3 - 3 * (-1) * (-Real.sqrt 3) ^ 2 = 8 := by rw [neg_sq (Real.sqrt 3), hs3]; norm_num
      rw [h3]; norm_num

theorem reducedQuotientPolar_hessians (k : ℤ) :
    iteratedDeriv 2 (fun R => reducedQuotientPolar R (2 * Real.pi * k / 3)) 2 = 1 / 12 ∧
    iteratedDeriv 2 (fun φ => reducedQuotientPolar 2 φ) (2 * Real.pi * k / 3) = 3 := by
  have hcos : Real.cos (3 * (2 * Real.pi * k / 3)) = 1 := by
    rw [Real.cos_eq_one_iff]; exact ⟨k, by ring⟩
  constructor
  · set c := Real.cos (3 * (2 * Real.pi * k / 3))
    have h1 : deriv (fun R => reducedQuotientPolar R (2 * Real.pi * k / 3)) =
        fun R => R / 12 - c / 6 := by
      funext R
      have : HasDerivAt (fun R : ℝ => reducedQuotientPolar R (2 * Real.pi * k / 3))
          (R / 12 - c / 6) R := by
        unfold reducedQuotientPolar
        have := (((hasDerivAt_pow 2 R).div_const 24).const_add (-9 / 10 : ℝ) |>.sub
          ((hasDerivAt_id R).mul_const c |>.div_const 6))
        exact this.congr_deriv (by simp; ring)
      exact this.deriv
    rw [iteratedDeriv_succ, iteratedDeriv_one, h1]
    have : HasDerivAt (fun R : ℝ => R / 12 - c / 6) (1 / 12) 2 := by
      simpa using ((hasDerivAt_id (2 : ℝ)).div_const 12).sub_const (c / 6)
    exact this.deriv
  · have h1 : deriv (fun φ => reducedQuotientPolar 2 φ) = fun φ => Real.sin (3 * φ) := by
      funext φ
      have h3 : HasDerivAt (fun φ : ℝ => 3 * φ) 3 φ := by
        simpa using (hasDerivAt_id φ).const_mul 3
      have := ((h3.cos).const_mul 2).div_const 6 |>.const_sub (-9 / 10 + 2 ^ 2 / 24 : ℝ)
      have e : HasDerivAt (fun φ : ℝ => reducedQuotientPolar 2 φ) (Real.sin (3 * φ)) φ := by
        convert this using 1
        · funext φ; unfold reducedQuotientPolar; ring
        · ring
      exact e.deriv
    rw [iteratedDeriv_succ, iteratedDeriv_one, h1]
    have h3 : HasDerivAt (fun φ : ℝ => 3 * φ) 3 (2 * Real.pi * k / 3) := by
      simpa using (hasDerivAt_id (2 * Real.pi * k / 3)).const_mul 3
    have := h3.sin
    rw [hcos] at this
    simpa using this.deriv

theorem reducedQuotientPolar_tendsto_endpoint (φ : ℝ) :
    Tendsto (fun R => reducedQuotientPolar R φ) (𝓝[>] 0) (𝓝 (-9 / 10)) := by
  have : Continuous (fun R => reducedQuotientPolar R φ) := by
    unfold reducedQuotientPolar; fun_prop
  have h := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simpa [reducedQuotientPolar] using h

theorem reducedQuotient_exact_minimizers :
    (∀ A B : ℝ, A ^ 2 + B ^ 2 ≠ 0 →
      reducedQuotient A B = 2 * reducedQuartic A B / (A ^ 2 + B ^ 2)) ∧
    (∀ R φ : ℝ, 0 < R →
      reducedQuotient (R * Real.cos φ) (R * Real.sin φ) = reducedQuotientPolar R φ) ∧
    (∀ R φ : ℝ, 0 < R → -16 / 15 ≤ reducedQuotientPolar R φ ∧
      (reducedQuotientPolar R φ = -16 / 15 ↔ R = 2 ∧ ∃ k : ℤ, φ = 2 * Real.pi * k / 3)) ∧
    (∀ A B : ℝ, A ^ 2 + B ^ 2 ≠ 0 → -16 / 15 ≤ reducedQuotient A B ∧
      (reducedQuotient A B = -16 / 15 ↔
        (A = 2 ∧ B = 0) ∨ (A = -1 ∧ B = Real.sqrt 3) ∨ (A = -1 ∧ B = -Real.sqrt 3))) ∧
    (∀ k : ℤ,
      iteratedDeriv 2 (fun R => reducedQuotientPolar R (2 * Real.pi * k / 3)) 2 = 1 / 12 ∧
      iteratedDeriv 2 (fun φ => reducedQuotientPolar 2 φ) (2 * Real.pi * k / 3) = 3) ∧
    (∀ φ : ℝ, Tendsto (fun R => reducedQuotientPolar R φ) (𝓝[>] 0) (𝓝 (-9 / 10))) ∧
    (-16 / 15 : ℝ) < -9 / 10 ∧ reducedQuotient 2 0 = -16 / 15 :=
  ⟨reducedQuotient_eq_two_mul_reducedQuartic_div, fun R φ _ => reducedQuotient_polar R φ,
    reducedQuotientPolar_minimizers, reducedQuotient_minimizers,
    reducedQuotientPolar_hessians, reducedQuotientPolar_tendsto_endpoint, by norm_num,
    by unfold reducedQuotient; norm_num⟩

end DGPS.Examples.ThreeSpeciesCircle
