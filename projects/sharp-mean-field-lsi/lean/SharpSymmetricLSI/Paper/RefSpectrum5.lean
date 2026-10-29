import SharpSymmetricLSI.Paper.RefSpectrum4

/-!
# R23 (6.1), part 5: the successive Rayleigh minimizers

`e₀ = 1` and `e_{n+1}` is a minimizer of the Dirichlet energy over `Adm P e n` (chosen by
`Classical.epsilon`). By induction (`eSeq_spec`): `e_n ∈ H¹(P)`, orthonormal, weak eigenfunctions
with `λ_n = D(e_n)`, and `λ_n` is nondecreasing.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- Minimizers of the `(n+1)`-st Rayleigh problem. -/
def minSet (P : Measure (Torus d)) (F : ℕ → Torus d → ℝ) (n : ℕ) : Set (Torus d → ℝ) :=
  {f | f ∈ Adm P F n ∧ ∀ u ∈ Adm P F n, dirE P f ≤ dirE P u}

/-- The families `(e₀, …, eₙ)` (extended arbitrarily). -/
noncomputable def famSeq (P : Measure (Torus d)) : ℕ → ℕ → Torus d → ℝ
  | 0 => fun _ _ => 1
  | n + 1 => Function.update (famSeq P n) (n + 1) (Classical.epsilon (minSet P (famSeq P n) n))

/-- The successive minimizers. -/
noncomputable def eSeq (P : Measure (Torus d)) (n : ℕ) : Torus d → ℝ := famSeq P n n

theorem famSeq_stable (P : Measure (Torus d)) {n m : ℕ} (hnm : n ≤ m) {i : ℕ} (hi : i ≤ n) :
    famSeq P m i = famSeq P n i := by
  induction m with
  | zero => obtain rfl : n = 0 := by omega
            rfl
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hnm with h | h
    · rw [h]
    · rw [famSeq, Function.update_of_ne (by omega), ih (by omega)]

theorem famSeq_eq (P : Measure (Torus d)) {n i : ℕ} (hi : i ≤ n) : famSeq P n i = eSeq P i :=
  famSeq_stable P hi le_rfl

theorem adm_famSeq (P : Measure (Torus d)) (n : ℕ) : Adm P (famSeq P n) n = Adm P (eSeq P) n := by
  ext u
  simp only [Adm, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun i hi => by rw [← famSeq_eq P hi]; exact h3 i hi⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun i hi => by rw [famSeq_eq P hi]; exact h3 i hi⟩

theorem eSeq_zero (P : Measure (Torus d)) : eSeq P 0 = fun _ => 1 := rfl

theorem eSeq_succ (P : Measure (Torus d)) (n : ℕ) :
    eSeq P (n + 1) = Classical.epsilon (minSet P (famSeq P n) n) := by
  simp [eSeq, famSeq]

theorem eSeq_succ_mem (P : Measure (Torus d)) {n : ℕ} (h : (minSet P (eSeq P) n).Nonempty) :
    eSeq P (n + 1) ∈ minSet P (eSeq P) n := by
  have e : minSet P (famSeq P n) n = minSet P (eSeq P) n := by
    simp only [minSet, adm_famSeq]
  rw [eSeq_succ, e]
  exact Classical.epsilon_spec h

section spec

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C)
include hρ

theorem memH1_one : MemH1 (densMeasure ρ) (fun _ => (1 : ℝ)) :=
  memH1_of_vol hρ (memH1_of_contDiff contDiff_const)

theorem dirB_one (φ : Torus d → ℝ) : dirB (densMeasure ρ) (fun _ => (1 : ℝ)) φ = 0 := by
  have hw : weakGrad (fun _ : Torus d => (1 : ℝ)) =ᵐ[volume] 0 :=
    weakGrad_ae_unique (isWeakGrad_weakGrad ⟨0, isWeakGrad_const 1⟩) (isWeakGrad_const 1)
  have hwP : weakGrad (fun _ : Torus d => (1 : ℝ)) =ᵐ[densMeasure ρ] 0 := hρ.ac.ae_le hw
  unfold dirB
  rw [integral_congr_ae (g := fun _ => (0 : ℝ)) (hwP.mono fun x hx => by simp [hx])]
  simp

theorem dirE_one : dirE (densMeasure ρ) (fun _ => (1 : ℝ)) = 0 := by
  rw [dirE_eq_dirB hρ, dirB_one hρ]

/-- **The successive minimizers form an orthonormal system of weak eigenfunctions.** -/
theorem eSeq_spec (hd : 1 ≤ d) (n : ℕ) :
    (∀ i ≤ n, MemH1 (densMeasure ρ) (eSeq (densMeasure ρ) i)) ∧
    (∀ i ≤ n, ∀ j ≤ n, ∫ x, eSeq (densMeasure ρ) i x * eSeq (densMeasure ρ) j x ∂densMeasure ρ =
      if i = j then 1 else 0) ∧
    (∀ i ≤ n, ∀ φ, MemH1 (densMeasure ρ) φ →
      dirB (densMeasure ρ) (eSeq (densMeasure ρ) i) φ =
        dirE (densMeasure ρ) (eSeq (densMeasure ρ) i) *
          ∫ x, eSeq (densMeasure ρ) i x * φ x ∂densMeasure ρ) ∧
    (∀ i < n, eSeq (densMeasure ρ) (i + 1) ∈ minSet (densMeasure ρ) (eSeq (densMeasure ρ)) i) ∧
    (∀ i < n, dirE (densMeasure ρ) (eSeq (densMeasure ρ) i) ≤
      dirE (densMeasure ρ) (eSeq (densMeasure ρ) (i + 1))) := by
  set P := densMeasure ρ
  haveI := hρ.isProb
  induction n with
  | zero =>
    refine ⟨fun i hi => ?_, fun i hi j hj => ?_, fun i hi φ hφ => ?_, fun i hi => absurd hi
      (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · obtain rfl : i = 0 := by omega
      exact memH1_one hρ
    · obtain rfl : i = 0 := by omega
      obtain rfl : j = 0 := by omega
      simp [eSeq_zero]
    · obtain rfl : i = 0 := by omega
      rw [eSeq_zero, dirB_one hρ, dirE_one hρ, zero_mul]
  | succ n ih =>
    obtain ⟨hH, hon, heig, hmin, hmono⟩ := ih
    have hL2 : ∀ i ≤ n, MemLp (eSeq P i) 2 P := fun i hi => (hH i hi).2.1
    obtain ⟨f, hfA, hfmin⟩ := exists_min hρ hL2 (adm_nonempty hρ hd hL2)
    have hmem := eSeq_succ_mem P ⟨f, hfA, hfmin⟩
    set g := eSeq P (n + 1)
    have hgA := hmem.1
    have hgEL := euler_lagrange hρ hH hon heig hgA hmem.2
    have hg2 : ∫ x, g x * g x ∂P = 1 := by
      have := hgA.2.1; simp_rw [sq] at this; exact this
    refine ⟨fun i hi => ?_, fun i hi j hj => ?_, fun i hi φ hφ => ?_, fun i hi => ?_,
      fun i hi => ?_⟩
    · rcases Nat.lt_or_ge i (n + 1) with h | h
      · exact hH i (by omega)
      · obtain rfl : i = n + 1 := by omega
        exact hgA.1
    · rcases Nat.lt_or_ge i (n + 1) with h | h <;> rcases Nat.lt_or_ge j (n + 1) with h' | h'
      · exact hon i (by omega) j (by omega)
      · obtain rfl : j = n + 1 := by omega
        rw [if_neg (by omega)]
        rw [show ∫ x, eSeq P i x * g x ∂P = ∫ x, g x * eSeq P i x ∂P by
          congr 1; funext x; ring]
        exact hgA.2.2 i (by omega)
      · obtain rfl : i = n + 1 := by omega
        rw [if_neg (by omega)]
        exact hgA.2.2 j (by omega)
      · obtain rfl : i = n + 1 := by omega
        obtain rfl : j = n + 1 := by omega
        rw [if_pos rfl]; exact hg2
    · rcases Nat.lt_or_ge i (n + 1) with h | h
      · exact heig i (by omega) φ hφ
      · obtain rfl : i = n + 1 := by omega
        exact hgEL φ hφ
    · rcases Nat.lt_or_ge i n with h | h
      · exact hmin i h
      · obtain rfl : i = n := by omega
        exact hmem
    · rcases Nat.lt_or_ge i n with h | h
      · exact hmono i h
      · obtain rfl : i = n := by omega
        cases i with
        | zero => rw [eSeq_zero, dirE_one hρ]; exact dirE_nonneg hρ _
        | succ k =>
          have hk := hmin k (by omega)
          refine hk.2 g ⟨hgA.1, hgA.2.1, fun j hj => hgA.2.2 j (by omega)⟩

end spec

end SharpLSI
