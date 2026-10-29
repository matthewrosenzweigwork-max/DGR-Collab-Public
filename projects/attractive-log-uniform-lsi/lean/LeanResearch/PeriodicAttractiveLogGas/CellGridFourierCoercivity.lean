import LeanResearch.PeriodicAttractiveLogGas.OccupationChemicalCoercivity
import LeanResearch.PeriodicAttractiveLogGas.OccupationDrift
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Order.Chebyshev

/-! Discrete Fourier coercivity for the actual periodic cell grid, source
lines 1981--1985. The development record separates construction, central
diagnostics, integration and source review. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace PeriodicAttractiveLogGas.CellGridFourierCoercivity
open MeshCells MeshAdjacentCells BoundaryEdgeSummation OccupationDrift

open Classical in
/-- The existing adjacency relation has exactly the four enumerated neighbors
when J is at least three; the J=2 degeneracy is excluded explicitly. -/
theorem neighbor_sum {J : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (F : MeshIndex J → MeshIndex J → ℝ) (a : MeshIndex J) :
    (∑ b, if EdgeAdjacent J hJ a b then F a b else 0) =
      ∑ d : Fin 2, (F a (previousCell hJ a d) + F a (nextCell J hJ a d)) := by
  classical
  calc
    _ = ∑ b ∈ cellNeighbors hJ a, F a b := by
      simp only [cellNeighbors, Finset.sum_filter]
    _ = ∑ r : Fin 2 × Bool, F a (cellNeighbor hJ a r) := by
      rw [cellNeighbors_eq_image, Finset.sum_image]
      intro r _ s _ hrs
      exact cellNeighbor_injective hJ hJ3 a hrs
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro d _
      simp [cellNeighbor, add_comm]

theorem previous_sum_eq_next_sum {J : ℕ} (hJ : 0 < J)
    (F : MeshIndex J → MeshIndex J → ℝ) (hF : ∀ a b, F a b = F b a) (d : Fin 2) :
    (∑ a, F a (previousCell hJ a d)) = ∑ a, F a (nextCell J hJ a d) := by
  classical
  calc
    _ = ∑ a, F (nextCell J hJ a d) (previousCell hJ (nextCell J hJ a d) d) :=
      ((nextCellEquiv hJ d).sum_comp (fun a ↦ F a (previousCell hJ a d))).symm
    _ = ∑ a, F (nextCell J hJ a d) a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [show previousCell hJ (nextCell J hJ a d) d = a from
        (nextCellEquiv hJ d).symm_apply_apply a]
    _ = _ := Finset.sum_congr rfl (fun a _ ↦ hF _ _)

/-- Positive coordinate edges enumerate each actual unordered edge exactly once. -/
theorem unorderedSum_eq_positive_edges {J : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (F : MeshIndex J → MeshIndex J → ℝ) (hF : ∀ a b, F a b = F b a) :
    unorderedSum hJ F = ∑ a, ∑ d : Fin 2, F a (nextCell J hJ a d) := by
  classical
  have hd := directed_eq_twice_unordered hJ (by omega) F hF
  have hp : directedSum hJ F = 2 * ∑ a, ∑ d : Fin 2, F a (nextCell J hJ a d) := by
    unfold directedSum
    simp_rw [neighbor_sum hJ hJ3]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_add_distrib, previous_sum_eq_next_sum hJ F hF]
    simp only [← two_mul]
    rw [Finset.sum_comm]
  linarith only [hd, hp]

section Fourier
variable {J : ℕ} [NeZero J]

theorem sum_translate {A B : Type*} [Fintype A] [AddGroup A] [AddCommMonoid B]
    (F : A → B) (a : A) : (∑ j, F (j + a)) = ∑ j, F j :=
  Equiv.sum_comp (Equiv.addRight a) F

/-- The unnormalized finite Fourier pairing, proved from the actual DFT
inversion formula. Counting measure has mass J. -/
theorem dft_pairing (f g : ZMod J → ℂ) :
    (∑ k, conj (ZMod.dft f k) * ZMod.dft g k) =
      (J : ℂ) * ∑ j, conj (f j) * g j := by
  have hc (k : ZMod J) : conj (ZMod.dft f k) =
      ∑ j : ZMod J, ZMod.stdAddChar (j * k) * conj (f j) := by
    rw [ZMod.dft_apply]
    simp only [smul_eq_mul, map_sum, map_mul, ← AddChar.map_neg_eq_conj, neg_neg]
  have hi (j : ZMod J) : (∑ k : ZMod J, ZMod.stdAddChar (j * k) * ZMod.dft g k) =
      (J : ℂ) * g j := by
    have hh := congrFun (ZMod.dft_dft g) (-j)
    simpa only [ZMod.dft_apply, smul_eq_mul, mul_neg, neg_neg, mul_comm] using hh
  simp_rw [hc, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ j, conj (f j) * (∑ k : ZMod J, ZMod.stdAddChar (j * k) * ZMod.dft g k) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ j, conj (f j) * ((J : ℂ) * g j) := by simp_rw [hi]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem dft_parseval (f : ZMod J → ℂ) :
    (∑ k, ‖ZMod.dft f k‖ ^ 2) = (J : ℝ) * ∑ j, ‖f j‖ ^ 2 := by
  have hh := dft_pairing f f
  simp only [Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_sum,
    ← Complex.ofReal_natCast, ← Complex.ofReal_mul] at hh
  exact Complex.ofReal_injective hh

/-- A positive cyclic difference has the literal Fourier multiplier chi(k)-1. -/
theorem dft_shift (f : ZMod J → ℂ) (k : ZMod J) :
    ZMod.dft (fun j ↦ f (j + 1)) k = ZMod.stdAddChar k * ZMod.dft f k := by
  rw [ZMod.dft_apply, ZMod.dft_apply]
  simp only [smul_eq_mul]
  have he (j : ZMod J) : ZMod.stdAddChar (-(j * k)) * f (j + 1) =
      ZMod.stdAddChar k * (ZMod.stdAddChar (-((j + 1) * k)) * f (j + 1)) := by
    have ha : -(j * k) = k + -((j + 1) * k) := by ring
    rw [ha, AddChar.map_add_eq_mul]
    ring
  calc
    _ = ∑ j, ZMod.stdAddChar k *
        (ZMod.stdAddChar (-((j + 1) * k)) * f (j + 1)) :=
      Finset.sum_congr rfl (fun j _ ↦ he j)
    _ = ZMod.stdAddChar k *
        ∑ j, ZMod.stdAddChar (-((j + 1) * k)) * f (j + 1) :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := congrArg (fun z : ℂ ↦ ZMod.stdAddChar k * z)
      (sum_translate (fun j : ZMod J ↦ ZMod.stdAddChar (-(j * k)) * f j) 1)

theorem dft_difference (f : ZMod J → ℂ) (k : ZMod J) :
    ZMod.dft (fun j ↦ f (j + 1) - f j) k =
      (ZMod.stdAddChar k - 1) * ZMod.dft f k := by
  change ZMod.dft ((fun j ↦ f (j + 1)) - f) k = _
  rw [map_sub, Pi.sub_apply, dft_shift]
  ring

theorem dft_difference_energy (f : ZMod J → ℂ) :
    (J : ℝ) * (∑ j, ‖f (j + 1) - f j‖ ^ 2) =
      ∑ k, ‖ZMod.stdAddChar k - 1‖ ^ 2 * ‖ZMod.dft f k‖ ^ 2 := by
  rw [← dft_parseval (fun j ↦ f (j + 1) - f j)]
  simp_rw [dft_difference, norm_mul, mul_pow]

end Fourier

def gridGap (J : ℕ) : ℝ := 4 * Real.sin (Real.pi / J) ^ 2

theorem gridGap_nonneg (J : ℕ) : 0 ≤ gridGap J := by
  unfold gridGap
  positivity

theorem sin_frequency_min {J : ℕ} [NeZero J] (hJ2 : 2 ≤ J) {k : ZMod J} (hk : k ≠ 0) :
    Real.sin (Real.pi / J) ≤ Real.sin (Real.pi * k.val / J) := by
  have hJ : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hk0 : 1 ≤ k.val := by
    by_contra hh
    have hv : k.val = 0 := by omega
    have he := ZMod.natCast_zmod_val k
    rw [hv, Nat.cast_zero] at he
    exact hk he.symm
  have hk1 : k.val + 1 ≤ J := by have := ZMod.val_lt k; omega
  have hkl : (1 : ℝ) ≤ k.val := by exact_mod_cast hk0
  have hku : (k.val : ℝ) + 1 ≤ J := by exact_mod_cast hk1
  have hlo : Real.pi / J ≤ Real.pi * k.val / J :=
    div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) hJ.le
  have hhi : Real.pi * k.val / J ≤ Real.pi - Real.pi / J := by
    apply (div_le_iff₀ hJ).mpr
    rw [sub_mul, div_mul_cancel₀ _ hJ.ne']
    nlinarith [Real.pi_pos]
  have hbase : -(Real.pi / 2) ≤ Real.pi / J :=
    (neg_nonpos.mpr (div_nonneg Real.pi_pos.le (by norm_num))).trans
      (div_nonneg Real.pi_pos.le hJ.le)
  by_cases hm : Real.pi * k.val / J ≤ Real.pi / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two hbase hm hlo
  · have hr : Real.pi / J ≤ Real.pi - Real.pi * k.val / J := by linarith
    have hr' : Real.pi - Real.pi * k.val / J ≤ Real.pi / 2 := by linarith
    simpa only [Real.sin_pi_sub] using
      Real.sin_le_sin_of_le_of_le_pi_div_two hbase hr' hr

theorem gridGap_lower {J : ℕ} (hJ2 : 2 ≤ J) : 16 / (J : ℝ) ^ 2 ≤ gridGap J := by
  have hJ : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hJ2r : (2 : ℝ) ≤ J := by exact_mod_cast hJ2
  have hx : Real.pi / J ≤ Real.pi / 2 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hJ2r
  have hh := Real.mul_le_sin (div_nonneg Real.pi_pos.le hJ.le) hx
  have hl : 2 / (J : ℝ) ≤ Real.sin (Real.pi / J) := by
    have he : 2 / Real.pi * (Real.pi / J) = 2 / (J : ℝ) := by
      field_simp
    rwa [he] at hh
  have hn : 0 ≤ Real.sin (Real.pi / J) := (div_nonneg (by norm_num) hJ.le).trans hl
  have hs := (sq_le_sq₀ (div_nonneg (by norm_num) hJ.le) hn).mpr hl
  unfold gridGap
  have he : 16 / (J : ℝ) ^ 2 = 4 * (2 / (J : ℝ)) ^ 2 := by ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hs (by norm_num)

section Cycle
variable {J : ℕ} [NeZero J]

theorem character_difference_norm_sq (k : ZMod J) :
    ‖ZMod.stdAddChar k - 1‖ ^ 2 = 4 * Real.sin (Real.pi * k.val / J) ^ 2 := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  have he : 2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (J : ℂ) =
      Complex.I * ((2 * Real.pi * k.val / J : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, sq_abs]
  have hh : (2 * Real.pi * k.val / J : ℝ) / 2 = Real.pi * k.val / J := by ring
  rw [hh]
  ring

theorem character_multiplier_lower (hJ2 : 2 ≤ J) {k : ZMod J} (hk : k ≠ 0) :
    gridGap J ≤ ‖ZMod.stdAddChar k - 1‖ ^ 2 := by
  have hJ : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hJ2r : (2 : ℝ) ≤ J := by exact_mod_cast hJ2
  have hangle : Real.pi / J ≤ Real.pi / 2 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hJ2r
  have hbase : 0 ≤ Real.sin (Real.pi / J) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (div_nonneg Real.pi_pos.le hJ.le)
      (by nlinarith [Real.pi_pos])
  have hs := sin_frequency_min hJ2 hk
  rw [character_difference_norm_sq]
  exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ hbase (hbase.trans hs)).mpr hs) (by norm_num)

/-- The first nonzero Fourier mode attains the claimed multiplier. -/
theorem first_mode_multiplier (hJ2 : 2 ≤ J) :
    (1 : ZMod J) ≠ 0 ∧ ‖ZMod.stdAddChar (1 : ZMod J) - 1‖ ^ 2 = gridGap J := by
  have hv : (1 : ZMod J).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (show 1 < J by omega)
  constructor
  · intro hz
    have hh := congrArg ZMod.val hz
    rw [hv, ZMod.val_zero] at hh
    norm_num at hh
  · rw [character_difference_norm_sq, hv, Nat.cast_one, mul_one]
    rfl

/-- The actual cyclic Fourier gap for an arbitrary complex mean-zero vector. -/
theorem cycle_zero_mean (hJ2 : 2 ≤ J) (f : ZMod J → ℂ) (hmean : ∑ j, f j = 0) :
    gridGap J * (∑ j, ‖f j‖ ^ 2) ≤ ∑ j, ‖f (j + 1) - f j‖ ^ 2 := by
  have hb : gridGap J * (∑ k, ‖ZMod.dft f k‖ ^ 2) ≤
      ∑ k, ‖ZMod.stdAddChar k - 1‖ ^ 2 * ‖ZMod.dft f k‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    by_cases hk : k = 0
    · subst k
      simp only [ZMod.dft_apply_zero, hmean, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
        mul_zero, le_refl]
    · exact mul_le_mul_of_nonneg_right (character_multiplier_lower hJ2 hk) (sq_nonneg _)
  rw [dft_parseval, ← dft_difference_energy] at hb
  have hJ : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  apply (mul_le_mul_iff_right₀ hJ).mp
  convert hb using 1
  ring

def cycleMean (f : ZMod J → ℝ) : ℝ := (J : ℝ)⁻¹ * ∑ j, f j

theorem sum_cycle_centered (f : ZMod J → ℝ) : ∑ j, (f j - cycleMean f) = 0 := by
  have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne J)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, cycleMean, ← mul_assoc, mul_inv_cancel₀ hJ0, one_mul, sub_self]

theorem cycleMean_sub (f g : ZMod J → ℝ) :
    cycleMean (fun j ↦ f j - g j) = cycleMean f - cycleMean g := by
  simp only [cycleMean, Finset.sum_sub_distrib, mul_sub]

theorem cycle_poincare (hJ2 : 2 ≤ J) (f : ZMod J → ℝ) :
    gridGap J * (∑ j, (f j - cycleMean f) ^ 2) ≤ ∑ j, (f (j + 1) - f j) ^ 2 := by
  let g : ZMod J → ℂ := fun j ↦ ((f j - cycleMean f : ℝ) : ℂ)
  have hg : ∑ j, g j = 0 := by
    change (∑ j, ((f j - cycleMean f : ℝ) : ℂ)) = 0
    rw [← Complex.ofReal_sum, sum_cycle_centered, Complex.ofReal_zero]
  have hh := cycle_zero_mean hJ2 g hg
  have hd (j : ZMod J) : g (j + 1) - g j = ((f (j + 1) - f j : ℝ) : ℂ) := by
    dsimp [g]
    push_cast
    ring
  simp_rw [hd] at hh
  simpa only [g, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hh

theorem cycle_variance_decomposition (f : ZMod J → ℝ) (m : ℝ) :
    (∑ j, (f j - m) ^ 2) = (∑ j, (f j - cycleMean f) ^ 2) +
      (J : ℝ) * (cycleMean f - m) ^ 2 := by
  have he (j : ZMod J) : (f j - m) ^ 2 = (f j - cycleMean f) ^ 2 +
      2 * (cycleMean f - m) * (f j - cycleMean f) + (cycleMean f - m) ^ 2 := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, sum_cycle_centered]
  simp only [mul_zero, add_zero, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

theorem cycle_mean_square_le (f : ZMod J → ℝ) :
    (J : ℝ) * cycleMean f ^ 2 ≤ ∑ j, f j ^ 2 := by
  have hJ : (0 : ℝ) < J := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne J))
  have hm : cycleMean f * (J : ℝ) = ∑ j, f j := by
    unfold cycleMean
    field_simp
  apply (mul_le_mul_iff_right₀ hJ).mp
  calc
    _ = (cycleMean f * (J : ℝ)) ^ 2 := by ring
    _ = (∑ j, f j) ^ 2 := by rw [hm]
    _ ≤ (J : ℝ) * (∑ j, f j ^ 2) := by
      simpa only [Finset.card_univ, ZMod.card] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := f))

theorem cycleMean_cycleMean (f : ZMod J → ZMod J → ℝ) :
    cycleMean (fun y ↦ cycleMean (fun x ↦ f x y)) =
      ((J : ℝ) ^ 2)⁻¹ * ∑ x, ∑ y, f x y := by
  unfold cycleMean
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [pow_two]
  ring

/-- Tensorization of the genuine cyclic Fourier gap; the row-mean term is
controlled by finite Cauchy--Schwarz, without loss in the constant. -/
theorem grid_tensor_poincare (hJ2 : 2 ≤ J) (f : ZMod J → ZMod J → ℝ) :
    gridGap J * (∑ x, ∑ y, (f x y - ((J : ℝ) ^ 2)⁻¹ * ∑ u, ∑ v, f u v) ^ 2) ≤
      ∑ x, ∑ y, ((f (x + 1) y - f x y) ^ 2 + (f x (y + 1) - f x y) ^ 2) := by
  let r : ZMod J → ℝ := fun y ↦ cycleMean (fun x ↦ f x y)
  let m : ℝ := cycleMean r
  have hv : (∑ y, ∑ x, (f x y - m) ^ 2) =
      (∑ y, ∑ x, (f x y - r y) ^ 2) + (J : ℝ) * ∑ y, (r y - m) ^ 2 := by
    calc
      _ = ∑ y, ((∑ x, (f x y - r y) ^ 2) + (J : ℝ) * (r y - m) ^ 2) :=
        Finset.sum_congr rfl (fun y _ ↦ cycle_variance_decomposition (fun x ↦ f x y) m)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hrow : gridGap J * (∑ y, ∑ x, (f x y - r y) ^ 2) ≤
      ∑ y, ∑ x, (f (x + 1) y - f x y) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun y _ ↦ cycle_poincare hJ2 (fun x ↦ f x y))
  have hmean : gridGap J * (∑ y, (r y - m) ^ 2) ≤ ∑ y, (r (y + 1) - r y) ^ 2 :=
    cycle_poincare hJ2 r
  have hcs : (J : ℝ) * (∑ y, (r (y + 1) - r y) ^ 2) ≤
      ∑ y, ∑ x, (f x (y + 1) - f x y) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _
    have hh := cycle_mean_square_le (fun x ↦ f x (y + 1) - f x y)
    rw [cycleMean_sub] at hh
    exact hh
  have ht : gridGap J * (∑ y, ∑ x, (f x y - m) ^ 2) ≤
      ∑ y, ∑ x, ((f (x + 1) y - f x y) ^ 2 + (f x (y + 1) - f x y) ^ 2) := by
    calc
      _ = gridGap J * (∑ y, ∑ x, (f x y - r y) ^ 2) +
          (J : ℝ) * (gridGap J * ∑ y, (r y - m) ^ 2) := by rw [hv]; ring
      _ ≤ (∑ y, ∑ x, (f (x + 1) y - f x y) ^ 2) +
          (J : ℝ) * (∑ y, (r (y + 1) - r y) ^ 2) :=
        add_le_add hrow (mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg J))
      _ ≤ (∑ y, ∑ x, (f (x + 1) y - f x y) ^ 2) +
          (∑ y, ∑ x, (f x (y + 1) - f x y) ^ 2) := add_le_add le_rfl hcs
      _ = _ := by simp only [Finset.sum_add_distrib]
  have hm : m = ((J : ℝ) ^ 2)⁻¹ * ∑ x, ∑ y, f x y := cycleMean_cycleMean f
  rw [hm, Finset.sum_comm (f := fun y x ↦
      (f x y - ((J : ℝ) ^ 2)⁻¹ * ∑ u, ∑ v, f u v) ^ 2),
    Finset.sum_comm (f := fun y x ↦
      (f (x + 1) y - f x y) ^ 2 + (f x (y + 1) - f x y) ^ 2)] at ht
  exact ht

end Cycle

section MeshTransfer
variable {J : ℕ} [NeZero J]
open MeshNearbyGeometry

/-- Literal two cyclic coordinates of the existing finite mesh labels. -/
def cellCoordinates (J : ℕ) [NeZero J] : MeshIndex J ≃ ZMod J × ZMod J where
  toFun a := ((a 0).val, (a 1).val)
  invFun p := ![⟨p.1.val, ZMod.val_lt _⟩, ⟨p.2.val, ZMod.val_lt _⟩]
  left_inv a := by
    funext j
    fin_cases j
    · apply Fin.ext
      exact ZMod.val_natCast_of_lt (a 0).isLt
    · apply Fin.ext
      exact ZMod.val_natCast_of_lt (a 1).isLt
  right_inv p := by
    apply Prod.ext
    · exact ZMod.natCast_zmod_val p.1
    · exact ZMod.natCast_zmod_val p.2

theorem sum_cellCoordinates (c : MeshIndex J → ℝ) :
    (∑ a, c a) = ∑ x : ZMod J, ∑ y : ZMod J, c ((cellCoordinates J).symm (x, y)) := by
  have hh := Equiv.sum_comp (cellCoordinates J).symm c
  rw [Fintype.sum_prod_type] at hh
  exact hh.symm

theorem cellCoordinates_next_zero (hJ : 0 < J) (a : MeshIndex J) :
    cellCoordinates J (nextCell J hJ a 0) =
      ((cellCoordinates J a).1 + 1, (cellCoordinates J a).2) := by
  apply Prod.ext
  · change indexClass (nextCell J hJ a 0) 0 = indexClass a 0 + 1
    rw [nextCell_indexClass]
    norm_num [integerEdgeStep]
  · change indexClass (nextCell J hJ a 0) 1 = indexClass a 1
    rw [nextCell_indexClass]
    norm_num [integerEdgeStep]

theorem cellCoordinates_next_one (hJ : 0 < J) (a : MeshIndex J) :
    cellCoordinates J (nextCell J hJ a 1) =
      ((cellCoordinates J a).1, (cellCoordinates J a).2 + 1) := by
  apply Prod.ext
  · change indexClass (nextCell J hJ a 1) 0 = indexClass a 0
    rw [nextCell_indexClass]
    norm_num [integerEdgeStep]
  · change indexClass (nextCell J hJ a 1) 1 = indexClass a 1 + 1
    rw [nextCell_indexClass]
    norm_num [integerEdgeStep]

theorem cellCoordinates_symm_next_zero (hJ : 0 < J) (x y : ZMod J) :
    nextCell J hJ ((cellCoordinates J).symm (x, y)) 0 =
      (cellCoordinates J).symm (x + 1, y) := by
  apply (cellCoordinates J).injective
  simp only [cellCoordinates_next_zero, Equiv.apply_symm_apply]

theorem cellCoordinates_symm_next_one (hJ : 0 < J) (x y : ZMod J) :
    nextCell J hJ ((cellCoordinates J).symm (x, y)) 1 =
      (cellCoordinates J).symm (x, y + 1) := by
  apply (cellCoordinates J).injective
  simp only [cellCoordinates_next_one, Equiv.apply_symm_apply]

end MeshTransfer

/-- The Fourier gap on the actual once-counted unordered cell grid. -/
theorem cell_grid_poincare {J : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J) (c : MeshIndex J → ℝ) :
    gridGap J * (∑ a, (c a - ((J : ℝ) ^ 2)⁻¹ * ∑ b, c b) ^ 2) ≤
      unorderedSum hJ (fun a b ↦ (c a - c b) ^ 2) := by
  let : NeZero J := ⟨hJ.ne'⟩
  let f : ZMod J → ZMod J → ℝ := fun x y ↦ c ((cellCoordinates J).symm (x, y))
  have ht := grid_tensor_poincare (by omega : 2 ≤ J) f
  have hm : (∑ x, ∑ y, f x y) = ∑ a, c a := (sum_cellCoordinates c).symm
  rw [hm] at ht
  have hv : (∑ x, ∑ y, (f x y - ((J : ℝ) ^ 2)⁻¹ * ∑ b, c b) ^ 2) =
      ∑ a, (c a - ((J : ℝ) ^ 2)⁻¹ * ∑ b, c b) ^ 2 :=
    (sum_cellCoordinates (fun a ↦ (c a - ((J : ℝ) ^ 2)⁻¹ * ∑ b, c b) ^ 2)).symm
  have he : (∑ x, ∑ y, ((f (x + 1) y - f x y) ^ 2 + (f x (y + 1) - f x y) ^ 2)) =
      unorderedSum hJ (fun a b ↦ (c a - c b) ^ 2) := by
    rw [unorderedSum_eq_positive_edges hJ hJ3 _ (fun a b ↦ by ring)]
    rw [sum_cellCoordinates]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [Fin.sum_univ_two, cellCoordinates_symm_next_zero, cellCoordinates_symm_next_one]
    dsimp only [f]
    ring
  rwa [hv, he] at ht

theorem cell_grid_poincare_lower {J : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J) (c : MeshIndex J → ℝ) :
    16 / (J : ℝ) ^ 2 * (∑ a, (c a - ((J : ℝ) ^ 2)⁻¹ * ∑ b, c b) ^ 2) ≤
      unorderedSum hJ (fun a b ↦ (c a - c b) ^ 2) :=
  (mul_le_mul_of_nonneg_right (gridGap_lower (by omega : 2 ≤ J))
    (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)).trans (cell_grid_poincare hJ hJ3 c)

open OccupationNearContraction OccupationChemicalCoercivity

/-- Source chemical edge coercivity with the explicit coefficient obtained
from the actual grid Fourier gap and the actual nearby fixed point. -/
theorem chemical_edge_coercivity {J : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
    {θ : MeshIndex J → ℝ} {β β₀ : ℝ} (h : NearParameters θ β β₀)
    (hnear : profileDeviation θ ≤ neighborhood β₀) (hsub : β₀ < 4) :
    4 * (GreenL2Coercivity.gap β₀) ^ 2 * (J : ℝ) ^ 2 *
        (∑ a, (θ a - ((J : ℝ) ^ 2)⁻¹) ^ 2) ≤
      unorderedSum hJ (fun a b ↦
        (coefficient hJ θ β (nearFixedPoint hJ h).val a -
          coefficient hJ θ β (nearFixedPoint hJ h).val b) ^ 2) := by
  let f := (nearFixedPoint hJ h).val
  have hg := cell_grid_poincare_lower hJ hJ3 (coefficient hJ θ β f)
  rw [← integral_cellValue hJ (coefficient hJ θ β f)] at hg
  have hc := fixedPoint_chemical_variance_lower hJ h hnear hsub
  have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ 16 / (J : ℝ) ^ 2 by positivity)
  have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have he : 16 / (J : ℝ) ^ 2 *
      ((GreenL2Coercivity.gap β₀) ^ 2 * (J : ℝ) ^ 4 / 4 *
        (∑ a, (θ a - ((J : ℝ) ^ 2)⁻¹) ^ 2)) =
      4 * (GreenL2Coercivity.gap β₀) ^ 2 * (J : ℝ) ^ 2 *
        (∑ a, (θ a - ((J : ℝ) ^ 2)⁻¹) ^ 2) := by
    field_simp
    ring
  rw [he] at hh
  exact hh.trans hg

end PeriodicAttractiveLogGas.CellGridFourierCoercivity
