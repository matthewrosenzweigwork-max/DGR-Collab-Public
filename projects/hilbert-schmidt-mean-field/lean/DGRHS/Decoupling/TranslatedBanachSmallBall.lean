import Mathlib.Analysis.Normed.Module.HahnBanach
import DGRHS.Decoupling.FiniteCubeNoiseStep
import DGRHS.Decoupling.FiniteAverageZeroMeanPositiveTail

/-!
Records-only scalarization and norm-event transfer leaf for the translated
finite-cube small-ball proof. This file consumes the scalar finite-average
leaf (0745Z/0750Z) but does not use or assume the translated small-ball
conclusion. It isolates the precise scalar moment facts needed from the later
Walsh mixed-degree calculation.

The pinned source for the norming functional is Mathlib revision
d13f23b723b8a846827a245b89c10fc7d3f11612,
Mathlib/Analysis/Normed/Module/HahnBanach.lean:61:
`exists_dual_vector (𝕜 : Type v) [RCLike 𝕜] (x : E) (h : ‖x‖ ≠ 0) :
  ∃ g : StrongDual 𝕜 E, ‖g‖ = 1 ∧ g x = ‖x‖`.
Here it is instantiated at `𝕜 = ℝ` for fixed nonzero x. The argument never
selects a functional measurably as the cube point varies.

No compiler, project source, or campaign forest was modified.
-/

noncomputable section
open DGRHS.Decoupling.FiniteCube

namespace DGRHS.Decoupling.FiniteCube

private lemma avgOn_cs_scalar {X : Type*} [Fintype X]
    (f g : X → ℝ) :
    (avgOn (fun x => f x * g x)) ^ 2 ≤
      avgOn (fun x => f x ^ 2) * avgOn (fun x => g x ^ 2) := by
  unfold avgOn
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset X) f g
  have hscale := mul_le_mul_of_nonneg_left hcs
    (sq_nonneg ((Fintype.card X : ℝ)⁻¹))
  convert hscale using 1 <;> ring

private lemma avgOn_constant_scalar {X : Type*} [Fintype X] [Nonempty X]
    (a : ℝ) : avgOn (fun _ : X => a) = a := by
  unfold avgOn
  have hcard : (Fintype.card X : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt Fintype.card_pos)
  simp only [Finset.sum_const, nsmul_eq_mul]
  simp only [Finset.card_univ]
  field_simp [hcard]

private lemma avgOn_mono_scalar {X : Type*} [Fintype X]
    (f g : X → ℝ) (h : ∀ x, f x ≤ g x) : avgOn f ≤ avgOn g := by
  unfold avgOn
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum (fun x _ => h x)
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)

private lemma avgOn_square_zero_forall
    {X : Type*} [Fintype X] [Nonempty X] (Y : X → ℝ)
    (hzero : avgOn (fun x => Y x ^ 2) = 0) :
    ∀ x, Y x = 0 := by
  classical
  have hcardNat : Fintype.card X ≠ 0 := Nat.ne_of_gt Fintype.card_pos
  have hcard : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast hcardNat
  have hcardavg : (Fintype.card X : ℝ) * avgOn (fun x => Y x ^ 2) =
      ∑ x : X, Y x ^ 2 := by
    unfold avgOn
    rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  have hsum : (∑ x : X, Y x ^ 2) = 0 := by
    have h := congrArg (fun z : ℝ => (Fintype.card X : ℝ) * z) hzero
    rw [hcardavg] at h
    simpa using h
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)] at hsum
  intro x
  have hx := hsum x (Finset.mem_univ x)
  nlinarith

/--
If every scalar projection of P has mean zero and fourth moment at most
`A` times the square of its second moment, then a fixed translation x has
selector probability at least `1/(4A)` of not decreasing the norm. The
condition `1 ≤ 4A` is used only to cover x=0 and zero projected variance.
For the intended `A_k = k^3 Σ_{r=1}^k 9^r`, it holds whenever k≥1.
-/
theorem translated_cube_norm_event_of_scalar_moments
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (P : (Fin n → Bool) → E) (x : E) (A : ℝ)
    (hA : 1 ≤ 4 * A)
    (hmean : ∀ φ : StrongDual ℝ E,
      avgOn (fun ω => φ (P ω)) = 0)
    (hfour : ∀ φ : StrongDual ℝ E,
      avgOn (fun ω => φ (P ω) ^ 4) ≤
        A * (avgOn (fun ω => φ (P ω) ^ 2)) ^ 2) :
    avgOn (fun ω =>
      if ‖x + P ω‖ ≥ ‖x‖ then (1 : ℝ) else 0) ≥ 1 / (4 * A) := by
  classical
  have hdenA : 0 < 4 * A := by linarith
  have hrecip_le_one : 1 / (4 * A) ≤ 1 := by
    apply (div_le_iff₀ hdenA).2
    linarith
  by_cases hx : x = 0
  · have hEvent : avgOn (fun ω : Fin n → Bool =>
        if ‖x + P ω‖ ≥ ‖x‖ then (1 : ℝ) else 0) = 1 := by
      calc
        avgOn (fun ω : Fin n → Bool =>
            if ‖x + P ω‖ ≥ ‖x‖ then (1 : ℝ) else 0) =
          avgOn (fun _ : Fin n → Bool => (1 : ℝ)) := by
            apply avgOn_congr
            intro ω
            simp [hx]
        _ = 1 := avgOn_constant_scalar (1 : ℝ)
    rw [hEvent]
    exact hrecip_le_one
  · obtain ⟨φ, hφnorm, hφx⟩ :=
      exists_dual_vector ℝ x (norm_ne_zero_iff.mpr hx)
    let Y : (Fin n → Bool) → ℝ := fun ω => φ (P ω)
    let m : ℝ := avgOn (fun ω => Y ω ^ 2)
    let q : ℝ := avgOn (fun ω => Y ω ^ 4)
    have hmeanY : avgOn Y = 0 := by simpa [Y] using hmean φ
    have hnonneg : 0 ≤ m := by
      dsimp [m]
      exact avgOn_nonneg _ (fun ω => sq_nonneg (Y ω))
    by_cases hm0 : m = 0
    · have hYzero := avgOn_square_zero_forall Y (by simpa [m] using hm0)
      have hpoint : ∀ ω : Fin n → Bool, ‖x‖ ≤ ‖x + P ω‖ := by
        intro ω
        have heval : φ (x + P ω) = ‖x‖ := by
          rw [map_add]
          have hzero : φ (P ω) = 0 := by simpa [Y] using hYzero ω
          rw [hzero, add_zero]
          simpa using hφx
        have hdual : ‖φ (x + P ω)‖ ≤ ‖x + P ω‖ := by
          simpa [hφnorm] using φ.le_opNorm (x + P ω)
        simpa [heval] using hdual
      have hEvent : avgOn (fun ω : Fin n → Bool =>
          if ‖x + P ω‖ ≥ ‖x‖ then (1 : ℝ) else 0) = 1 := by
        calc
          avgOn (fun ω : Fin n → Bool =>
              if ‖x + P ω‖ ≥ ‖x‖ then (1 : ℝ) else 0) =
            avgOn (fun _ : Fin n → Bool => (1 : ℝ)) := by
              apply avgOn_congr
              intro ω
              simp [hpoint ω]
          _ = 1 := avgOn_constant_scalar (1 : ℝ)
      rw [hEvent]
      exact hrecip_le_one
    · have hm : 0 < m := lt_of_le_of_ne hnonneg (Ne.symm hm0)
      have hscalar := avgOn_zeroMean_positiveProbability Y hmeanY hm
      have hq : 0 < q := by
        have hcs := avgOn_cs_scalar
          (fun ω : Fin n → Bool => Y ω ^ 2) (fun _ : Fin n → Bool => (1 : ℝ))
        have hconst : avgOn (fun _ : Fin n → Bool => (1 : ℝ) ^ 2) = 1 := by
          simpa using (avgOn_constant_scalar (X := Fin n → Bool) (1 : ℝ))
        have hpow : (fun ω : Fin n → Bool => (Y ω ^ 2) ^ 2) =
            (fun ω => Y ω ^ 4) := by
          funext ω
          ring
        have hsecondLe : m ^ 2 ≤ q := by
          calc
            m ^ 2 = (avgOn (fun ω => Y ω ^ 2 * 1)) ^ 2 := by simp [m]
            _ ≤ avgOn (fun ω => (Y ω ^ 2) ^ 2) *
                avgOn (fun _ : Fin n → Bool => (1 : ℝ) ^ 2) := hcs
            _ = q := by rw [hpow, hconst]; simp [q]
        exact lt_of_lt_of_le (sq_pos_of_pos hm) hsecondLe
      have hfourY : q ≤ A * m ^ 2 := by simpa [Y, m, q] using hfour φ
      have hcomp : 1 / (4 * A) ≤ m ^ 2 / (4 * q) := by
        apply (div_le_div_iff₀ hdenA (mul_pos (by norm_num) hq)).2
        have hmul := mul_le_mul_of_nonneg_left hfourY (by norm_num : (0 : ℝ) ≤ 4)
        nlinarith [hm, hq]
      have hscalarBound : 1 / (4 * A) ≤
          avgOn (fun ω => if 0 < Y ω then (1 : ℝ) else 0) := by
        have hscalar' : avgOn (fun ω => if 0 < Y ω then (1 : ℝ) else 0) ≥
            m ^ 2 / (4 * q) := by simpa [m, q] using hscalar
        exact hcomp.trans hscalar'
      have hcontain : ∀ ω : Fin n → Bool,
          (if 0 < Y ω then (1 : ℝ) else 0) ≤
            (if ‖x + P ω‖ ≥ ‖x‖ then (1 : ℝ) else 0) := by
        intro ω
        by_cases hy : 0 < Y ω
        · have heval : φ (x + P ω) = ‖x‖ + Y ω := by
            simp [map_add, hφx, Y]
          have hevalpos : 0 < φ (x + P ω) := by
            rw [heval]
            linarith [norm_nonneg x, hy]
          have hdual : ‖φ (x + P ω)‖ ≤ ‖x + P ω‖ := by
            simpa [hφnorm] using φ.le_opNorm (x + P ω)
          have habs : ‖φ (x + P ω)‖ = φ (x + P ω) := by
            rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hevalpos)]
          have hstrict : ‖x‖ < ‖x + P ω‖ := by
            calc
              ‖x‖ < φ (x + P ω) := by rw [heval]; linarith
              _ = ‖φ (x + P ω)‖ := habs.symm
              _ ≤ ‖x + P ω‖ := hdual
          simp [hy, hstrict.le]
        · by_cases hnorm : ‖x + P ω‖ ≥ ‖x‖ <;> simp [hy, hnorm]
      have hmono := avgOn_mono_scalar
        (fun ω => if 0 < Y ω then (1 : ℝ) else 0)
        (fun ω => if ‖x + P ω‖ ≥ ‖x‖ then (1 : ℝ) else 0)
        hcontain
      exact hscalarBound.trans hmono

#print DGRHS.Decoupling.FiniteCube.translated_cube_norm_event_of_scalar_moments
#print axioms DGRHS.Decoupling.FiniteCube.translated_cube_norm_event_of_scalar_moments

end DGRHS.Decoupling.FiniteCube
