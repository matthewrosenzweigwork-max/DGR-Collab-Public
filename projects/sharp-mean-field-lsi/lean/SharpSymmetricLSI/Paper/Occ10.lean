import SharpSymmetricLSI.Paper.Occ9

/-!
# The Newton recursion as a continuous map; its Hermite fixed point (Phase 3, lane D; R28(d))

`newtonRec q n α` solves the Newton recursion with input coefficients `q` (fuel `n ≥ |α|`). It is
continuous in `q`, it reproduces the coefficients of any solution, and at the Gaussian input
`q_{j,0} = z_j`, `q_{j,e_j} = -1` it gives `∏ₖ He_{αₖ}(zₖ)/αₖ!`.
-/

noncomputable section
open MvPolynomial Finset.HasAntidiagonal

namespace SharpLSI

variable {K : ℕ}

/-- The Newton recursion with fuel. -/
def newtonRec (q : Fin K → (Fin K →₀ ℕ) → ℝ) : ℕ → (Fin K →₀ ℕ) → ℝ
  | 0, α => if α = 0 then 1 else 0
  | n + 1, α => if h : α = 0 then 1 else
      ((α (α.support.min' (Finsupp.support_nonempty_iff.mpr h)) : ℝ))⁻¹ *
        ∑ x ∈ antidiagonal (α - Finsupp.single (α.support.min' (Finsupp.support_nonempty_iff.mpr h)) 1),
          newtonRec q n x.1 * q (α.support.min' (Finsupp.support_nonempty_iff.mpr h)) x.2

theorem newtonRec_eq {q : Fin K → (Fin K →₀ ℕ) → ℝ} {E : (Fin K →₀ ℕ) → ℝ} (h0 : E 0 = 1)
    (hrec : ∀ α j, ((α j : ℝ) + 1) * E (α + Finsupp.single j 1) =
      ∑ x ∈ antidiagonal α, E x.1 * q j x.2) :
    ∀ n α, α.degree ≤ n → newtonRec q n α = E α := by
  intro n
  induction n with
  | zero =>
    intro α hα
    have : α = 0 := (Finsupp.degree_eq_zero_iff α).mp (by omega)
    simp [newtonRec, this, h0]
  | succ n ih =>
    intro α hα
    by_cases h : α = 0
    · simp [newtonRec, h, h0]
    rw [newtonRec, dite_eq_right h]
    set j := α.support.min' (Finsupp.support_nonempty_iff.mpr h)
    have hj : α j ≠ 0 := Finsupp.mem_support_iff.mp (Finset.min'_mem _ _)
    have hle : Finsupp.single j 1 ≤ α := by
      rw [Finsupp.single_le_iff]; omega
    set α' := α - Finsupp.single j 1
    have hα' : α' + Finsupp.single j 1 = α := tsub_add_cancel_of_le hle
    have hα'j : (α' j : ℝ) + 1 = α j := by
      have : α' j + 1 = α j := by
        have := congrArg (fun f => f j) hα'
        simpa using this
      exact_mod_cast this
    have hdeg : α'.degree + 1 = α.degree := by
      rw [← hα', map_add, Finsupp.degree_single]
    have hsum : ∑ x ∈ antidiagonal α', newtonRec q n x.1 * q j x.2 =
        ∑ x ∈ antidiagonal α', E x.1 * q j x.2 :=
      Finset.sum_congr rfl fun x hx => by
        rw [ih x.1 (by have := (degree_le_of_mem_antidiagonal hx).2; omega)]
    rw [hsum, ← hrec α' j, hα', hα'j, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hj), one_mul]

theorem continuous_newtonRec {U : Type*} [TopologicalSpace U]
    {Q : U → Fin K → (Fin K →₀ ℕ) → ℝ} (hQ : ∀ j γ, Continuous fun u => Q u j γ) :
    ∀ n α, Continuous fun u => newtonRec (Q u) n α := by
  intro n
  induction n with
  | zero => intro α; simp only [newtonRec]; exact continuous_const
  | succ n ih =>
    intro α
    by_cases h : α = 0
    · simp only [newtonRec, dite_eq_left h]; exact continuous_const
    simp only [newtonRec, dite_eq_right h]
    exact continuous_const.mul (continuous_finsetSum _ fun x _ => (ih x.1).mul (hQ _ _))

/-! ### Hermite polynomials -/

theorem derivative_hermite_succ (n : ℕ) :
    Polynomial.derivative (Polynomial.hermite (n + 1)) = ((n : ℤ) + 1) • Polynomial.hermite n := by
  induction n with
  | zero => simp [Polynomial.hermite_zero]
  | succ n ih =>
    rw [Polynomial.hermite_succ (n + 1), Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_X, one_mul, ih, Polynomial.derivative_smul]
    have h' : Polynomial.derivative (Polynomial.hermite n) =
        Polynomial.X * Polynomial.hermite n - Polynomial.hermite (n + 1) := by
      rw [Polynomial.hermite_succ n]; ring
    simp only [zsmul_eq_mul]
    rw [h']
    push_cast
    ring

theorem aeval_hermite_add_two (x : ℝ) (n : ℕ) :
    Polynomial.aeval x (Polynomial.hermite (n + 2)) =
      x * Polynomial.aeval x (Polynomial.hermite (n + 1)) -
        ((n : ℝ) + 1) * Polynomial.aeval x (Polynomial.hermite n) := by
  rw [Polynomial.hermite_succ (n + 1), derivative_hermite_succ, map_sub, map_mul,
    Polynomial.aeval_X, map_zsmul, zsmul_eq_mul]
  push_cast; ring

/-- `He_n(x)/n!`. -/
def hermNorm (x : ℝ) (n : ℕ) : ℝ := Polynomial.aeval x (Polynomial.hermite n) / (n.factorial : ℝ)

theorem hermNorm_zero (x : ℝ) : hermNorm x 0 = 1 := by simp [hermNorm, Polynomial.hermite_zero]

theorem hermNorm_one (x : ℝ) : hermNorm x 1 = x := by simp [hermNorm]

theorem hermNorm_succ_succ (x : ℝ) (m : ℕ) :
    ((m : ℝ) + 2) * hermNorm x (m + 2) = x * hermNorm x (m + 1) - hermNorm x m := by
  unfold hermNorm
  rw [aeval_hermite_add_two, Nat.factorial_succ (m + 1), Nat.factorial_succ m]
  push_cast
  have h1 : (m.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The Gaussian limit of the normalized generating coefficients. -/
def hermLim (z : Fin K → ℝ) (α : Fin K →₀ ℕ) : ℝ := ∏ k, hermNorm (z k) (α k)

/-- The Gaussian limit of the Newton coefficients. -/
def qLim (z : Fin K → ℝ) (j : Fin K) (γ : Fin K →₀ ℕ) : ℝ :=
  if γ = 0 then z j else if γ = Finsupp.single j 1 then -1 else 0

theorem hermLim_zero (z : Fin K → ℝ) : hermLim z 0 = 1 := by simp [hermLim, hermNorm_zero]

theorem hermLim_split (z : Fin K → ℝ) (α : Fin K →₀ ℕ) (j : Fin K) :
    hermLim z α = hermNorm (z j) (α j) * ∏ k ∈ Finset.univ.erase j, hermNorm (z k) (α k) :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm

theorem hermLim_rec (z : Fin K → ℝ) (α : Fin K →₀ ℕ) (j : Fin K) :
    ((α j : ℝ) + 1) * hermLim z (α + Finsupp.single j 1) =
      ∑ x ∈ antidiagonal α, hermLim z x.1 * qLim z j x.2 := by
  classical
  set R := ∏ k ∈ Finset.univ.erase j, hermNorm (z k) (α k)
  have hR : ∀ β : Fin K →₀ ℕ, (∀ k, k ≠ j → β k = α k) →
      hermLim z β = hermNorm (z j) (β j) * R := fun β hβ => by
    rw [hermLim_split z β j]
    congr 1
    exact Finset.prod_congr rfl fun k hk => by rw [hβ k (Finset.ne_of_mem_erase hk)]
  have hplus : hermLim z (α + Finsupp.single j 1) = hermNorm (z j) (α j + 1) * R := by
    rw [hR _ fun k hk => by simp [Finsupp.single_eq_of_ne hk]]
    simp
  have hα : hermLim z α = hermNorm (z j) (α j) * R := hR α fun _ _ => rfl
  have hmem0 : (α, (0 : Fin K →₀ ℕ)) ∈ antidiagonal α := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal]; simp
  have hq : ∀ x ∈ antidiagonal α, x ≠ (α, 0) → x.2 ≠ Finsupp.single j 1 →
      hermLim z x.1 * qLim z j x.2 = 0 := fun x hx hne hs => by
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have h2 : x.2 ≠ 0 := fun h => hne (Prod.ext (by rw [← hx, h, add_zero]) h)
    simp [qLim, h2, hs]
  rcases Nat.eq_zero_or_pos (α j) with h0 | hpos
  · rw [Finset.sum_eq_single (α, 0)]
    · rw [hplus, hα, h0, hermNorm_one, hermNorm_zero]
      simp [qLim]; ring
    · intro x hx hne
      refine hq x hx hne fun hs => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      have := congrArg (fun f => f j) hx
      simp [hs] at this
      omega
    · intro h; exact absurd hmem0 h
  · have hle : Finsupp.single j 1 ≤ α := by rw [Finsupp.single_le_iff]; omega
    have hmem1 : (α - Finsupp.single j 1, Finsupp.single j 1) ∈ antidiagonal α := by
      rw [Finset.HasAntidiagonal.mem_antidiagonal]; exact tsub_add_cancel_of_le hle
    have hne : (α, (0 : Fin K →₀ ℕ)) ≠ (α - Finsupp.single j 1, Finsupp.single j 1) := by
      intro h
      have := congrArg (fun p => p.2 j) h
      simp at this
    rw [Finset.sum_eq_add _ _ hne (fun x hx hx' => hq x hx hx'.1 fun hs => hx'.2 (by
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        refine Prod.ext ?_ hs
        rw [← hx, hs, add_tsub_cancel_right])) (fun h => absurd hmem0 h) (fun h => absurd hmem1 h)]
    have hminus : hermLim z (α - Finsupp.single j 1) = hermNorm (z j) (α j - 1) * R := by
      rw [hR _ fun k hk => by simp [Finsupp.single_eq_of_ne hk]]
      simp
    have hsne : Finsupp.single j 1 ≠ (0 : Fin K →₀ ℕ) := Finsupp.single_ne_zero.mpr one_ne_zero
    simp only [qLim, hsne, ↓reduceIte]
    rw [hplus, hα, hminus]
    obtain ⟨m, hm⟩ : ∃ m, α j = m + 1 := ⟨α j - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel]
    have := hermNorm_succ_succ (z j) m
    push_cast
    rw [show (m : ℝ) + 1 + 1 = m + 2 by ring, ← mul_assoc, this]
    ring

end SharpLSI
