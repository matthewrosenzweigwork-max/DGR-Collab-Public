import DGRHS.Decoupling.FiniteCubeNoiseStep

/-!
Records-only, uncompiled scalar finite-average interpolation leaf.

This is deliberately the smallest unit of the translated mixed-degree proof:
for a zero-average real function with positive second moment, prove the
positive-tail probability lower bound from two uses of the pinned finite
Cauchy–Schwarz API. No Walsh, Banach, Hahn–Banach, source-array, or compiler
dependency is introduced here. The parent `a4631aeb...` proposal is preserved.

API provenance: the local normalized-average Cauchy–Schwarz declaration is
`avgOn_mul_sq_le_sq_mul_sq` in the `12f406` predecessor, whose body reduces to
`Finset.sum_mul_sq_le_sq_mul_sq` exactly as the checked project helper does at
`proof/DGRHS/Decoupling/FiniteCubeNoiseStep.lean:98`. The pinned Mathlib
revision is `d13f23b723b8a846827a245b89c10fc7d3f11612`; captured
`Mathlib/Analysis/Real/Sqrt.lean` (SHA-256
`f4e96c735ead60a8983bcf8eb6e38dfd05d8102c3f741094f73639858605bb6a`) has
`Real.sq_sqrt (h : 0 ≤ x) : √x ^ 2 = x` at line 178. The scalar leaf has no
norming-functional API; Hahn–Banach belongs only to the following translated
Banach-valued step.
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

theorem avgOn_zeroMean_positiveProbability
    {X : Type*} [Fintype X] [Nonempty X]
    (Y : X → ℝ)
    (hmean : avgOn Y = 0)
    (hsecond : 0 < avgOn (fun x => Y x ^ 2)) :
    avgOn (fun x => if 0 < Y x then (1 : ℝ) else 0) ≥
      (avgOn (fun x => Y x ^ 2)) ^ 2 /
        (4 * avgOn (fun x => Y x ^ 4)) := by
  classical
  let U : X → ℝ := fun x => |Y x|
  let a : ℝ := avgOn U
  let b : ℝ := avgOn (fun x => U x ^ 3)
  let m : ℝ := avgOn (fun x => Y x ^ 2)
  let q : ℝ := avgOn (fun x => Y x ^ 4)
  let I : X → ℝ := fun x => if 0 < Y x then 1 else 0
  let f₁ : X → ℝ := fun x => Real.sqrt (U x)
  let g₁ : X → ℝ := fun x => U x * Real.sqrt (U x)

  have hm : 0 < m := by simpa [m] using hsecond
  have ha : 0 ≤ a := by
    dsimp [a]
    exact avgOn_nonneg U (fun x => abs_nonneg (Y x))
  have hb : 0 ≤ b := by
    dsimp [b]
    apply avgOn_nonneg
    intro x
    exact pow_nonneg (abs_nonneg (Y x)) 3

  have hfg₁ (x : X) : f₁ x * g₁ x = Y x ^ 2 := by
    dsimp [f₁, g₁, U]
    have hu : 0 ≤ |Y x| := abs_nonneg _
    calc
      Real.sqrt |Y x| * (|Y x| * Real.sqrt |Y x|) =
          |Y x| * (Real.sqrt |Y x| * Real.sqrt |Y x|) := by ring
      _ = |Y x| * (Real.sqrt |Y x|) ^ 2 := by ring
      _ = |Y x| * |Y x| := by rw [Real.sq_sqrt hu]
      _ = Y x ^ 2 := by
        calc
          |Y x| * |Y x| = |Y x| ^ 2 := by ring
          _ = Y x ^ 2 := by rw [sq_abs]
  have hf₁sq (x : X) : f₁ x ^ 2 = U x := by
    dsimp [f₁]
    exact Real.sq_sqrt (abs_nonneg (Y x))
  have hg₁sq (x : X) : g₁ x ^ 2 = U x ^ 3 := by
    dsimp [g₁]
    have hu : 0 ≤ U x := abs_nonneg _
    rw [mul_pow, Real.sq_sqrt hu]
    ring
  have hfg₁avg : avgOn (fun x => f₁ x * g₁ x) = m := by
    calc
      avgOn (fun x => f₁ x * g₁ x) = avgOn (fun x => Y x ^ 2) :=
        avgOn_congr hfg₁
      _ = m := rfl
  have hf₁sqavg : avgOn (fun x => f₁ x ^ 2) = a := by
    calc
      avgOn (fun x => f₁ x ^ 2) = avgOn U := avgOn_congr hf₁sq
      _ = a := rfl
  have hg₁sqavg : avgOn (fun x => g₁ x ^ 2) = b := by
    calc
      avgOn (fun x => g₁ x ^ 2) = avgOn (fun x => U x ^ 3) := avgOn_congr hg₁sq
      _ = b := rfl

  have hcs₁ := avgOn_cs_scalar f₁ g₁
  have hm2_le_ab : m ^ 2 ≤ a * b := by
    calc
      m ^ 2 = (avgOn (fun x => f₁ x * g₁ x)) ^ 2 := by rw [hfg₁avg]
      _ ≤ avgOn (fun x => f₁ x ^ 2) * avgOn (fun x => g₁ x ^ 2) := hcs₁
      _ = a * b := by rw [hf₁sqavg, hg₁sqavg]

  have hcs₂ := avgOn_cs_scalar U (fun x => U x ^ 2)
  have hU₂ : avgOn (fun x => U x ^ 2) = m := by
    calc
      avgOn (fun x => U x ^ 2) = avgOn (fun x => Y x ^ 2) := by
        apply avgOn_congr
        intro x
        dsimp [U]
        rw [sq_abs]
      _ = m := rfl
  have hU₃mul : avgOn (fun x => U x * U x ^ 2) = b := by
    calc
      avgOn (fun x => U x * U x ^ 2) = avgOn (fun x => U x ^ 3) := by
        apply avgOn_congr
        intro x
        ring
      _ = b := rfl
  have hU₄ : avgOn (fun x => (U x ^ 2) ^ 2) = q := by
    calc
      avgOn (fun x => (U x ^ 2) ^ 2) = avgOn (fun x => Y x ^ 4) := by
        apply avgOn_congr
        intro x
        dsimp [U]
        rw [sq_abs]
        ring
      _ = q := rfl
  have hb2_le_mq : b ^ 2 ≤ m * q := by
    calc
      b ^ 2 = (avgOn (fun x => U x * U x ^ 2)) ^ 2 := by rw [hU₃mul]
      _ ≤ avgOn (fun x => U x ^ 2) * avgOn (fun x => (U x ^ 2) ^ 2) := hcs₂
      _ = m * q := by rw [hU₂, hU₄]

  have habpos : 0 < a * b := by
    have hmSq : 0 < m ^ 2 := sq_pos_of_pos hm
    linarith [hm2_le_ab]
  have hbpos : 0 < b := by
    by_contra hnot
    have hble : b ≤ 0 := le_of_not_gt hnot
    have habnonpos : a * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hble
    linarith
  have hqpos : 0 < q := by
    by_contra hnot
    have hqle : q ≤ 0 := le_of_not_gt hnot
    have hmqnonpos : m * q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hm) hqle
    have hbSq : 0 < b ^ 2 := sq_pos_of_pos hbpos
    linarith [hb2_le_mq]

  have hsqInterp : m ^ 4 ≤ (a * b) ^ 2 := by
    have habsub : 0 ≤ a * b - m ^ 2 := sub_nonneg.mpr hm2_le_ab
    have habsum : 0 ≤ a * b + m ^ 2 :=
      add_nonneg (mul_nonneg ha (le_of_lt hbpos)) (sq_nonneg m)
    nlinarith [mul_nonneg habsub habsum]
  have htermInterp : a ^ 2 * b ^ 2 ≤ a ^ 2 * (m * q) :=
    mul_le_mul_of_nonneg_left hb2_le_mq (sq_nonneg a)
  have hfourInterp : m ^ 3 ≤ a ^ 2 * q := by
    have hfour : m ^ 4 ≤ a ^ 2 * m * q := by
      calc
        m ^ 4 ≤ (a * b) ^ 2 := hsqInterp
        _ = a ^ 2 * b ^ 2 := by ring
        _ ≤ a ^ 2 * (m * q) := htermInterp
        _ = a ^ 2 * m * q := by ring
    have hcancel : m ^ 3 * m ≤ (a ^ 2 * q) * m := by
      calc
        m ^ 3 * m = m ^ 4 := by ring
        _ ≤ a ^ 2 * m * q := hfour
        _ = (a ^ 2 * q) * m := by ring
    have hcancel' : m * m ^ 3 ≤ m * (a ^ 2 * q) := by
      calc
        m * m ^ 3 = m ^ 3 * m := by ring
        _ ≤ (a ^ 2 * q) * m := hcancel
        _ = m * (a ^ 2 * q) := by ring
    exact (mul_le_mul_iff_right₀ hm).mp hcancel'

  have hplus (x : X) : max (Y x) 0 = (U x + Y x) / 2 := by
    dsimp [U]
    by_cases hneg : Y x < 0
    · rw [abs_of_neg hneg, max_eq_right (le_of_lt hneg)]
      ring
    · have hnonneg : 0 ≤ Y x := le_of_not_gt hneg
      rw [abs_of_nonneg hnonneg, max_eq_left hnonneg]
      ring
  have hplusAvg : avgOn (fun x => max (Y x) 0) = a / 2 := by
    calc
      avgOn (fun x => max (Y x) 0) =
          avgOn (fun x => (U x + Y x) / 2) := avgOn_congr hplus
      _ = (1 / 2) * avgOn (fun x => U x + Y x) := by
        calc
          avgOn (fun x => (U x + Y x) / 2) =
              avgOn (fun x => (1 / 2) * (U x + Y x)) := by
                apply avgOn_congr
                intro x
                ring
          _ = (1 / 2) * avgOn (fun x => U x + Y x) :=
            avgOn_const_mul (1 / 2) (fun x => U x + Y x)
      _ = (1 / 2) * (a + 0) := by rw [avgOn_add, hmean]
      _ = a / 2 := by ring

  have hprod (x : X) : max (Y x) 0 = Y x * I x := by
    by_cases hpos : 0 < Y x
    · rw [max_eq_left (le_of_lt hpos)]
      simp [I, hpos]
    · have hnonpos : Y x ≤ 0 := le_of_not_gt hpos
      rw [max_eq_right hnonpos]
      simp [I, hpos]
  have hI₂ : avgOn (fun x => I x ^ 2) = avgOn I := by
    apply avgOn_congr
    intro x
    simp [I]
  let p : ℝ := avgOn I
  have hcs₃ := avgOn_cs_scalar Y I
  have hselectedCS : (avgOn (fun x => Y x * I x)) ^ 2 ≤ m * p := by
    calc
      (avgOn (fun x => Y x * I x)) ^ 2 ≤
          avgOn (fun x => Y x ^ 2) * avgOn (fun x => I x ^ 2) := hcs₃
      _ = m * p := by rw [hI₂]
  have hplusCS : (a / 2) ^ 2 ≤ m * p := by
    calc
      (a / 2) ^ 2 = (avgOn (fun x => max (Y x) 0)) ^ 2 := by rw [hplusAvg]
      _ = (avgOn (fun x => Y x * I x)) ^ 2 := by rw [avgOn_congr hprod]
      _ ≤ m * p := hselectedCS
  have ha₂_le : a ^ 2 ≤ 4 * m * p := by nlinarith [hplusCS]
  have hqmul : a ^ 2 * q ≤ (4 * m * p) * q :=
    mul_le_mul_of_nonneg_right ha₂_le (le_of_lt hqpos)
  have hm₂_cross : m ^ 2 ≤ 4 * p * q := by
    have hmul : m ^ 2 * m ≤ (4 * p * q) * m := by
      calc
        m ^ 2 * m = m ^ 3 := by ring
        _ ≤ a ^ 2 * q := hfourInterp
        _ ≤ (4 * m * p) * q := hqmul
        _ = (4 * p * q) * m := by ring
    have hmul' : m * m ^ 2 ≤ m * (4 * p * q) := by
      calc
        m * m ^ 2 = m ^ 2 * m := by ring
        _ ≤ (4 * p * q) * m := hmul
        _ = m * (4 * p * q) := by ring
    exact (mul_le_mul_iff_right₀ hm).mp hmul'
  have hden : 0 < 4 * q := mul_pos (by norm_num) hqpos
  have hfinal : m ^ 2 / (4 * q) ≤ p :=
    (div_le_iff₀ hden).2 (by calc m ^ 2 ≤ 4 * p * q := hm₂_cross
                                  _ = p * (4 * q) := by ring)
  simpa [p, I, m, q] using hfinal

#print DGRHS.Decoupling.FiniteCube.avgOn_zeroMean_positiveProbability
#print axioms DGRHS.Decoupling.FiniteCube.avgOn_zeroMean_positiveProbability

end DGRHS.Decoupling.FiniteCube
