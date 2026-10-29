import LeanResearch.PeriodicAttractiveLogGas.FiniteEntropyLocalization
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! The actual normalization of the finite tent/shell family in the supplied
local-box proof. Bounded overlap gives the denominator bound and the
normalization map's squared Lipschitz estimate. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.FiniteSquaredPartition
open FiniteEntropyLocalization

variable {ι α : Type*} [Fintype ι]

def squaredLength (u : ι → ℝ) : ℝ := ∑ i, u i ^ 2
def length (u : ι → ℝ) : ℝ := Real.sqrt (squaredLength u)
def normalized (u : ι → ℝ) (i : ι) : ℝ := u i / length u
def squaredDistance (u v : ι → ℝ) : ℝ := ∑ i, (u i - v i) ^ 2

def activeCard (u : ι → ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => u i ≠ 0).card

theorem squaredLength_nonneg (u : ι → ℝ) : 0 ≤ squaredLength u :=
  Finset.sum_nonneg fun i _ => sq_nonneg (u i)

theorem length_nonneg (u : ι → ℝ) : 0 ≤ length u := Real.sqrt_nonneg _

theorem length_sq (u : ι → ℝ) : length u ^ 2 = squaredLength u :=
  Real.sq_sqrt (squaredLength_nonneg u)

theorem length_pos_of_sum_one (u : ι → ℝ) (hu : (∑ i, u i) = 1) : 0 < length u := by
  apply Real.sqrt_pos.mpr
  by_contra! h
  have hz (i : ι) : u i = 0 := by
    have hi : u i ^ 2 ≤ squaredLength u :=
      Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
    nlinarith only [hi, h, sq_nonneg (u i)]
  simp only [hz, Finset.sum_const_zero] at hu
  norm_num at hu

theorem sum_normalized_sq (u : ι → ℝ) (hu : (∑ i, u i) = 1) :
    (∑ i, normalized u i ^ 2) = 1 := by
  have hn := (length_pos_of_sum_one u hu).ne'
  simp only [normalized, div_pow, ← Finset.sum_div]
  change squaredLength u / length u ^ 2 = 1
  rw [← length_sq u, div_self (pow_ne_zero 2 hn)]

/-- Cauchy--Schwarz on the actual nonzero support, with the overlap count. -/
theorem overlap_denominator_bound (u : ι → ℝ) (hu : (∑ i, u i) = 1)
    {M : ℕ} (hM : activeCard u ≤ M) : 1 ≤ (M : ℝ) * length u ^ 2 := by
  classical
  let s := Finset.univ.filter fun i => u i ≠ 0
  have hs : (∑ i ∈ s, u i) = ∑ i, u i := by
    simp only [s, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : u i = 0 <;> simp [hi]
  have hsq : (∑ i ∈ s, u i ^ 2) = squaredLength u := by
    simp only [s, Finset.sum_filter, squaredLength]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : u i = 0 <;> simp [hi]
  have hh := Finset.sum_mul_sq_le_sq_mul_sq s u (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at hh
  rw [hs, hu, hsq] at hh
  have hc : (s.card : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hm := mul_le_mul_of_nonneg_left hc (squaredLength_nonneg u)
  rw [length_sq]
  nlinarith only [hh, hm]

theorem dot_le_lengths (u v : ι → ℝ) : (∑ i, u i * v i) ≤ length u * length v := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  change (∑ i, u i * v i) ^ 2 ≤ squaredLength u * squaredLength v at hh
  rw [← length_sq u, ← length_sq v] at hh
  have hn := mul_nonneg (length_nonneg u) (length_nonneg v)
  by_contra! h
  nlinarith only [hh, hn, h]

theorem squaredDistance_expand (u v : ι → ℝ) :
    squaredDistance u v = squaredLength u + squaredLength v - 2 * ∑ i, u i * v i := by
  have hp (i : ι) : (u i - v i) ^ 2 = u i ^ 2 + v i ^ 2 - 2 * (u i * v i) := by ring
  simp only [squaredDistance, hp, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, squaredLength]

/-- The reverse triangle inequality in the squared form used below. -/
theorem length_difference_sq_le (u v : ι → ℝ) :
    (length u - length v) ^ 2 ≤ squaredDistance u v := by
  rw [squaredDistance_expand, ← length_sq u, ← length_sq v]
  nlinarith only [dot_le_lengths u v]

theorem normalization_difference_mul_bound (u v : ι → ℝ)
    (hu : length u ≠ 0) (hv : length v ≠ 0) :
    length u ^ 2 * (∑ i, (normalized u i - normalized v i) ^ 2) ≤
      4 * squaredDistance u v := by
  have hd (i : ι) : length u * (normalized u i - normalized v i) =
      (u i - v i) + ((length v - length u) / length v) * v i := by
    unfold normalized
    field_simp
    ring
  have hi (i : ι) : (length u * (normalized u i - normalized v i)) ^ 2 ≤
      2 * (u i - v i) ^ 2 + (2 * ((length v - length u) / length v) ^ 2) * v i ^ 2 := by
    rw [hd]
    nlinarith only [sq_nonneg ((u i - v i) - ((length v - length u) / length v) * v i)]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp only [mul_pow, Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  change length u ^ 2 * (∑ i, (normalized u i - normalized v i) ^ 2) ≤
    2 * squaredDistance u v + (2 * ((length v - length u) / length v) ^ 2) * squaredLength v at hh
  rw [← length_sq v] at hh
  have hc : (2 * ((length v - length u) / length v) ^ 2) * length v ^ 2 =
      2 * (length v - length u) ^ 2 := by field_simp
  rw [hc] at hh
  nlinarith only [hh, length_difference_sq_le u v]

/-- A dimension-free normalization bound whose only parameter is actual overlap. -/
theorem normalization_difference_bound (u v : ι → ℝ)
    (hu : (∑ i, u i) = 1) (hv : (∑ i, v i) = 1)
    {M : ℕ} (hM : activeCard u ≤ M) :
    (∑ i, (normalized u i - normalized v i) ^ 2) ≤
      4 * (M : ℝ) * squaredDistance u v := by
  have hh := normalization_difference_mul_bound u v
    (length_pos_of_sum_one u hu).ne' (length_pos_of_sum_one v hv).ne'
  have hn : 0 ≤ ∑ i, (normalized u i - normalized v i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hlo := mul_le_mul_of_nonneg_right (overlap_denominator_bound u hu hM) hn
  have hup := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  nlinarith only [hlo, hup]

/-- The manuscript's actual normalized family, point by point. -/
def partition (g : ι → α → ℝ) (i : ι) (x : α) : ℝ := normalized (fun j => g j x) i

theorem partition_sq_sum (g : ι → α → ℝ) (hg : ∀ x, (∑ i, g i x) = 1) (x : α) :
    (∑ i, partition g i x ^ 2) = 1 := sum_normalized_sq _ (hg x)

theorem partition_nonneg (g : ι → α → ℝ) (hgn : ∀ i x, 0 ≤ g i x) (i : ι) (x : α) :
    0 ≤ partition g i x := div_nonneg (hgn i x) (length_nonneg _)

theorem partition_eq_zero (g : ι → α → ℝ) (i : ι) (x : α) (hx : g i x = 0) :
    partition g i x = 0 := by simp [partition, normalized, hx]

/-- Actual overlap controls the localization cost after vector normalization. -/
theorem localizationCost_partition_le [Fintype α] (g : ι → α → ℝ)
    (r : α → α → ℝ) (hr : ∀ x y, 0 ≤ r x y)
    (hg : ∀ x, (∑ i, g i x) = 1) {M : ℕ}
    (hM : ∀ x, activeCard (fun i => g i x) ≤ M) (x : α) :
    localizationCost r (partition g) x ≤ 4 * (M : ℝ) * localizationCost r g x := by
  unfold localizationCost
  calc
    _ ≤ ∑ y, r x y * (4 * (M : ℝ) * ∑ i, (g i y - g i x) ^ 2) := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left
        (normalization_difference_bound (fun i => g i y) (fun i => g i x) (hg y) (hg x) (hM y))
        (hr x y)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring

end PeriodicAttractiveLogGas.FiniteSquaredPartition
