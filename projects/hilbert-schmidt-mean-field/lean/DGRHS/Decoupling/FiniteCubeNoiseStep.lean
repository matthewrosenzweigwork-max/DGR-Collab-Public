import Mathlib.Algebra.BigOperators.Ring.Finset
import DGRHS.Decoupling.RademacherSignMoments

noncomputable section

namespace DGRHS.Decoupling.FiniteCube

open DGRHS.Decoupling

/-- The uniform average of a real-valued function on a finite type. -/
def avgOn {X : Type*} [Fintype X] (f : X → ℝ) : ℝ :=
  (Fintype.card X : ℝ)⁻¹ * ∑ x, f x

lemma avgOn_nonneg {X : Type*} [Fintype X] (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ avgOn f := by
  unfold avgOn
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun x _ => hf x)

lemma avgOn_congr {X : Type*} [Fintype X] {f g : X → ℝ}
    (h : ∀ x, f x = g x) : avgOn f = avgOn g := by
  unfold avgOn
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  exact h x

lemma avgOn_add {X : Type*} [Fintype X] (f g : X → ℝ) :
    avgOn (fun x => f x + g x) = avgOn f + avgOn g := by
  unfold avgOn
  rw [Finset.sum_add_distrib]
  ring

lemma avgOn_const_mul {X : Type*} [Fintype X] (c : ℝ) (f : X → ℝ) :
    avgOn (fun x => c * f x) = c * avgOn f := by
  unfold avgOn
  rw [← Finset.mul_sum]
  ring

lemma avgOn_half_add {X : Type*} [Fintype X] (f g : X → ℝ) :
    avgOn (fun x => (f x + g x) / 2) = (avgOn f + avgOn g) / 2 := by
  unfold avgOn
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  ring

lemma avgOn_bool_prod {X : Type*} [Fintype X] [Nonempty X]
    (f : Bool × X → ℝ) :
    avgOn f =
      (avgOn (fun x => f (false, x)) + avgOn (fun x => f (true, x))) / 2 := by
  have hcNat : Fintype.card X ≠ 0 := Nat.ne_of_gt Fintype.card_pos
  have hc : (Fintype.card X : ℝ) ≠ 0 := by
    exact_mod_cast hcNat
  have hcardNat : Fintype.card (Bool × X) = 2 * Fintype.card X := by
    simp
  have hcard : (Fintype.card (Bool × X) : ℝ) =
      2 * (Fintype.card X : ℝ) := by
    exact_mod_cast hcardNat
  unfold avgOn
  rw [Fintype.sum_prod_type, Fintype.sum_bool, hcard]
  field_simp [hc]
  ring

/-- One scalar fourth-moment step for the finite-cube noise operator with
    noise parameter `ρ² = 1/3`. -/
lemma avg_noiseStep_fourth_le
    {X : Type*} [Fintype X] [Nonempty X]
    (ρ : ℝ) (hρ : ρ ^ 2 = 1 / 3)
    (a b A B : X → ℝ)
    (hA : avgOn (fun x => A x ^ 4) ≤
      (avgOn (fun x => a x ^ 2)) ^ 2)
    (hB : avgOn (fun x => B x ^ 4) ≤
      (avgOn (fun x => b x ^ 2)) ^ 2) :
    avgOn (fun z : Bool × X =>
      (A z.2 + ρ * DGRHS.Decoupling.rademacherSign z.1 * B z.2) ^ 4)
      ≤ (avgOn (fun x => a x ^ 2) + avgOn (fun x => b x ^ 2)) ^ 2 := by
  let p : ℝ := avgOn (fun x => a x ^ 2)
  let q : ℝ := avgOn (fun x => b x ^ 2)
  let u : ℝ := avgOn (fun x => A x ^ 4)
  let v : ℝ := avgOn (fun x => B x ^ 4)
  let w : ℝ := avgOn (fun x => A x ^ 2 * B x ^ 2)

  have hp : 0 ≤ p := by
    dsimp [p]
    exact avgOn_nonneg _ fun x => sq_nonneg (a x)
  have hq : 0 ≤ q := by
    dsimp [q]
    exact avgOn_nonneg _ fun x => sq_nonneg (b x)
  have hv : 0 ≤ v := by
    dsimp [v]
    exact avgOn_nonneg _ fun x => by
      positivity
  have hw0 : 0 ≤ w := by
    dsimp [w]
    exact avgOn_nonneg _ fun x => mul_nonneg (sq_nonneg (A x)) (sq_nonneg (B x))
  have hp2 : 0 ≤ p ^ 2 := sq_nonneg p
  have hpq : 0 ≤ p * q := mul_nonneg hp hq

  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x : X => A x ^ 2) (fun x => B x ^ 2)
  have hwsq : w ^ 2 ≤ u * v := by
    have hA4sum : (∑ x : X, (A x ^ 2) ^ 2) = ∑ x : X, A x ^ 4 := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    have hB4sum : (∑ x : X, (B x ^ 2) ^ 2) = ∑ x : X, B x ^ 4 := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    dsimp [w, u, v, avgOn]
    have hscaled := mul_le_mul_of_nonneg_left hcs
      (sq_nonneg ((Fintype.card X : ℝ)⁻¹))
    rw [hA4sum, hB4sum] at hscaled
    nlinarith [hscaled]

  have hA' : u ≤ p ^ 2 := by simpa [u, p] using hA
  have hB' : v ≤ q ^ 2 := by simpa [v, q] using hB
  have huv : u * v ≤ p ^ 2 * q ^ 2 := by
    calc
      u * v ≤ p ^ 2 * v := mul_le_mul_of_nonneg_right hA' hv
      _ ≤ p ^ 2 * q ^ 2 := mul_le_mul_of_nonneg_left hB' hp2
  have hsquares : w ^ 2 ≤ (p * q) ^ 2 := by
    nlinarith [hwsq, huv]

  have hw : w ≤ p * q := by
    by_contra hn
    have hlt : p * q < w := lt_of_not_ge hn
    have hleft : 0 < w - p * q := sub_pos.mpr hlt
    have hright : 0 < w + p * q := by nlinarith [hw0, hpq, hlt]
    have hprod : 0 < (w - p * q) * (w + p * q) :=
      mul_pos hleft hright
    nlinarith [hsquares]

  have h6 : 6 * ρ ^ 2 = 2 := by
    rw [hρ]
    norm_num
  have hρ4 : ρ ^ 4 = (1 : ℝ) / 9 := by
    calc
      ρ ^ 4 = (ρ ^ 2) ^ 2 := by ring
      _ = (1 / 3 : ℝ) ^ 2 := by rw [hρ]
      _ = 1 / 9 := by norm_num

  have hexp :
      avgOn (fun z : Bool × X =>
        (A z.2 + ρ * DGRHS.Decoupling.rademacherSign z.1 * B z.2) ^ 4) =
        u + 6 * ρ ^ 2 * w + ρ ^ 4 * v := by
    calc
      _ = (avgOn (fun x : X =>
              (A x + ρ * DGRHS.Decoupling.rademacherSign false * B x) ^ 4) +
            avgOn (fun x : X =>
              (A x + ρ * DGRHS.Decoupling.rademacherSign true * B x) ^ 4)) / 2 :=
          avgOn_bool_prod (X := X) (f := fun z : Bool × X =>
            (A z.2 + ρ * DGRHS.Decoupling.rademacherSign z.1 * B z.2) ^ 4)
      _ = avgOn (fun x : X =>
            ((A x + ρ * DGRHS.Decoupling.rademacherSign false * B x) ^ 4 +
             (A x + ρ * DGRHS.Decoupling.rademacherSign true * B x) ^ 4) / 2) := by
          symm
          exact avgOn_half_add _ _
      _ = avgOn (fun x : X =>
            A x ^ 4 + (6 * ρ ^ 2) * (A x ^ 2 * B x ^ 2) + ρ ^ 4 * B x ^ 4) := by
          apply avgOn_congr
          intro x
          simp [DGRHS.Decoupling.rademacherSign]
          ring
      _ = u + 6 * ρ ^ 2 * w + ρ ^ 4 * v := by
          dsimp [u, w, v]
          rw [avgOn_add, avgOn_add, avgOn_const_mul, avgOn_const_mul]

  calc
    avgOn (fun z : Bool × X =>
        (A z.2 + ρ * DGRHS.Decoupling.rademacherSign z.1 * B z.2) ^ 4)
        = u + 6 * ρ ^ 2 * w + ρ ^ 4 * v := hexp
    _ = u + 2 * w + (1 / 9 : ℝ) * v := by rw [h6, hρ4]
    _ ≤ p ^ 2 + 2 * p * q + q ^ 2 := by
      nlinarith [hA', hB', hw, hv]
    _ = (p + q) ^ 2 := by ring

#print axioms DGRHS.Decoupling.FiniteCube.avg_noiseStep_fourth_le

end DGRHS.Decoupling.FiniteCube
