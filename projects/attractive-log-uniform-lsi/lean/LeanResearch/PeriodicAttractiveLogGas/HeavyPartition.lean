import LeanResearch.PeriodicAttractiveLogGas.SeparatedRadius
import LeanResearch.PeriodicAttractiveLogGas.SmoothObservableInterfaces
import LeanResearch.PeriodicAttractiveLogGas.CollectiveSecondMoment
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! The actual squared partition from `lem:heavy-partition`. The normalization
and support are derived from the constructed occupation and separation cutoffs.
No partition or derivative estimate is supplied as an interface premise. -/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal

namespace PeriodicAttractiveLogGas.HeavyPartition

open MeshCells SmoothOccupations HeavyScales LocalizedVirialCutoffs SeparatedRadius

def theta (N J : ℕ) (hJ : 0 < J) (δ : ℝ) (a : MeshIndex J)
    (X : Configuration N) : ℝ :=
  H ((occupationFraction N J hJ a X - δ / 2) / (δ / 2))

def weight (N J : ℕ) (hJ : 0 < J) (β₀ δ : ℝ) (a : MeshIndex J) (m : ℕ)
    (X : Configuration N) : ℝ :=
  theta N J hJ δ a X *
    sigma β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) m) X *
      ∏ r ∈ Finset.range m,
        (1 - sigma β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) r) X)

def squareSum (N J : ℕ) (hJ : 0 < J) (β₀ δ : ℝ) (X : Configuration N) : ℝ :=
  ∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ), weight N J hJ β₀ δ a m X ^ 2

def zeta (N J : ℕ) (hJ : 0 < J) (β₀ δ : ℝ) (a : MeshIndex J)
    (m : Fin (sourceScaleCount β₀ δ)) (X : Configuration N) : ℝ :=
  weight N J hJ β₀ δ a m X /
    Real.sqrt (max (squareSum N J hJ β₀ δ X) ((sourceScaleCount β₀ δ : ℝ)⁻¹))

def scaleGradientConstant (β₀ δ : ℝ) : ℝ :=
  17 + 6 * sourceScaleCount β₀ δ / (separationConstant β₀ * (4 - β₀))

theorem theta_mem_Icc (N J : ℕ) (hJ : 0 < J) (δ : ℝ) (a : MeshIndex J)
    (X : Configuration N) : theta N J hJ δ a X ∈ Icc (0 : ℝ) 1 := H_mem_Icc _

theorem theta_eq_zero_of_occupation_le {N J : ℕ} (hJ : 0 < J) {δ : ℝ}
    (hδ : 0 < δ) (a : MeshIndex J) {X : Configuration N}
    (hX : occupationFraction N J hJ a X ≤ δ / 2) : theta N J hJ δ a X = 0 :=
  H_eq_zero_of_le (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hX) (by positivity))

theorem theta_eq_one_of_occupation_ge {N J : ℕ} (hJ : 0 < J) {δ : ℝ}
    (hδ : 0 < δ) (a : MeshIndex J) {X : Configuration N}
    (hX : δ ≤ occupationFraction N J hJ a X) : theta N J hJ δ a X = 1 := by
  apply H_eq_one_of_one_le
  apply (le_div_iff₀ (by positivity : 0 < δ / 2)).2
  linarith

theorem occupation_gt_of_theta_pos {N J : ℕ} (hJ : 0 < J) {δ : ℝ}
    (hδ : 0 < δ) (a : MeshIndex J) {X : Configuration N}
    (hX : 0 < theta N J hJ δ a X) : δ / 2 < occupationFraction N J hJ a X := by
  by_contra h
  rw [theta_eq_zero_of_occupation_le hJ hδ a (le_of_not_gt h)] at hX
  exact lt_irrefl _ hX

private theorem survival_mem_Icc (N J : ℕ) (β₀ δ : ℝ) (a : MeshIndex J) (m : ℕ)
    (X : Configuration N) :
    (∏ r ∈ Finset.range m,
      (1 - sigma β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) r) X)) ∈
        Icc (0 : ℝ) 1 := by
  constructor
  · apply Finset.prod_nonneg
    intro r _
    exact sub_nonneg.mpr (sigma_mem_Icc _ _ _ _ _).2
  · apply Finset.prod_le_one₀
    · intro r _
      exact sub_nonneg.mpr (sigma_mem_Icc _ _ _ _ _).2
    · intro r _
      linarith [(sigma_mem_Icc β₀ δ (cellCenter J a)
        (scaleRadius J (separationRadius β₀) r) X).1]

theorem weight_mem_Icc (N J : ℕ) (hJ : 0 < J) (β₀ δ : ℝ) (a : MeshIndex J) (m : ℕ)
    (X : Configuration N) : weight N J hJ β₀ δ a m X ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hθ0, hθ1⟩ := theta_mem_Icc N J hJ δ a X
  obtain ⟨hσ0, hσ1⟩ := sigma_mem_Icc β₀ δ (cellCenter J a)
    (scaleRadius J (separationRadius β₀) m) X
  obtain ⟨hP0, hP1⟩ := survival_mem_Icc N J β₀ δ a m X
  constructor
  · exact mul_nonneg (mul_nonneg hθ0 hσ0) hP0
  · exact (mul_le_mul (mul_le_mul hθ1 hσ1 hσ0 (by norm_num)) hP1 hP0
      (by norm_num : (0 : ℝ) ≤ 1 * 1)).trans_eq (by ring)

theorem weight_eq_zero_of_occupation_le {N J : ℕ} (hJ : 0 < J) {β₀ δ : ℝ}
    (hδ : 0 < δ) (a : MeshIndex J) (m : ℕ) {X : Configuration N}
    (hX : occupationFraction N J hJ a X ≤ δ / 2) : weight N J hJ β₀ δ a m X = 0 := by
  simp only [weight, theta_eq_zero_of_occupation_le hJ hδ a hX, zero_mul]

theorem squareSum_nonneg (N J : ℕ) (hJ : 0 < J) (β₀ δ : ℝ) (X : Configuration N) :
    0 ≤ squareSum N J hJ β₀ δ X :=
  Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun m _ ↦
    sq_nonneg (weight N J hJ β₀ δ a m X)

private theorem first_hit_telescope (q : ℕ → ℝ) (M : ℕ) :
    (∑ m ∈ Finset.range M, q m * ∏ r ∈ Finset.range m, (1 - q r)) =
      1 - ∏ r ∈ Finset.range M, (1 - q r) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ, ih]
    ring

theorem sum_weight_of_sigma_eq_one {N J : ℕ} (hJ : 0 < J) (β₀ δ : ℝ)
    (a : MeshIndex J) (X : Configuration N) {m : ℕ} (hm : m < sourceScaleCount β₀ δ)
    (hσ : sigma β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) m) X = 1) :
    (∑ r : Fin (sourceScaleCount β₀ δ), weight N J hJ β₀ δ a r X) = theta N J hJ δ a X := by
  let q : ℕ → ℝ := fun r ↦
    sigma β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) r) X
  have hz : ∏ r ∈ Finset.range (sourceScaleCount β₀ δ), (1 - q r) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hm)
    change 1 - sigma β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) m) X = 0
    rw [hσ, sub_self]
  rw [Fin.sum_univ_eq_sum_range
    (fun r : ℕ ↦ weight N J hJ β₀ δ a r X) (sourceScaleCount β₀ δ)]
  change (∑ r ∈ Finset.range (sourceScaleCount β₀ δ),
    theta N J hJ δ a X * q r * ∏ k ∈ Finset.range r, (1 - q k)) = _
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [first_hit_telescope, hz]
  ring

/-- The actual normalization lower bound follows from one occupied center
and the first successful scale, not from a partition assumption. -/
theorem squareSum_lower_bound {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hJ : sourceResolution β₀ δ ≤ J) (X : Configuration N)
    (hheavy : δ < maximumOccupation N J (source_mesh_pos hJ) X) :
    (sourceScaleCount β₀ δ : ℝ)⁻¹ ≤ squareSum N J (source_mesh_pos hJ) β₀ δ X := by
  obtain ⟨a, ha⟩ := maximumOccupation_attained N J (source_mesh_pos hJ) X
  have hocc : δ < occupationFraction N J (source_mesh_pos hJ) a X := by
    simpa only [ha] using hheavy
  obtain ⟨m, hm, hσ⟩ := (separated_radius hN hβ₀ hβ hδ hδ1 hJ a X (by linarith)).2
  have ht := theta_eq_one_of_occupation_ge (source_mesh_pos hJ) hδ a hocc.le
  have hw : (∑ r : Fin (sourceScaleCount β₀ δ),
      weight N J (source_mesh_pos hJ) β₀ δ a r X) = 1 := by
    rw [sum_weight_of_sigma_eq_one _ _ _ _ _ hm hσ, ht]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin (sourceScaleCount β₀ δ))) (fun _ ↦ (1 : ℝ))
    (fun r ↦ weight N J (source_mesh_pos hJ) β₀ δ a r X)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, hw, one_pow] at hc
  have hsingle : (∑ r : Fin (sourceScaleCount β₀ δ),
      weight N J (source_mesh_pos hJ) β₀ δ a r X ^ 2) ≤
      squareSum N J (source_mesh_pos hJ) β₀ δ X := by
    unfold squareSum
    exact Finset.single_le_sum
      (f := fun b : MeshIndex J ↦ ∑ r : Fin (sourceScaleCount β₀ δ),
        weight N J (source_mesh_pos hJ) β₀ δ b r X ^ 2)
      (fun b _ ↦ Finset.sum_nonneg fun r _ ↦
        sq_nonneg (weight N J (source_mesh_pos hJ) β₀ δ b r X))
      (Finset.mem_univ a)
  have hM : (0 : ℝ) < sourceScaleCount β₀ δ := by
    exact_mod_cast sourceScaleCount_pos hβ₀ hβ hδ hδ1
  rw [← one_div]
  apply (div_le_iff₀ hM).2
  have hmul := mul_le_mul_of_nonneg_left hsingle hM.le
  nlinarith

theorem squared_partition_unity {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hJ : sourceResolution β₀ δ ≤ J) (X : Configuration N)
    (hheavy : δ < maximumOccupation N J (source_mesh_pos hJ) X) :
    (∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ),
      zeta N J (source_mesh_pos hJ) β₀ δ a m X ^ 2) = 1 := by
  have hS := squareSum_lower_bound hN hβ₀ hβ hδ hδ1 hJ X hheavy
  have hM : (0 : ℝ) < sourceScaleCount β₀ δ := by
    exact_mod_cast sourceScaleCount_pos hβ₀ hβ hδ hδ1
  have hp : 0 < squareSum N J (source_mesh_pos hJ) β₀ δ X := (inv_pos.mpr hM).trans_le hS
  simp only [zeta, div_pow, ← Finset.sum_div]
  change squareSum N J (source_mesh_pos hJ) β₀ δ X /
    (Real.sqrt (max (squareSum N J (source_mesh_pos hJ) β₀ δ X)
      ((sourceScaleCount β₀ δ : ℝ)⁻¹))) ^ 2 = 1
  rw [max_eq_left hS, Real.sq_sqrt hp.le]
  exact div_self hp.ne'

theorem weight_support_subset {N J : ℕ} (hJ : 0 < J) {β₀ δ : ℝ}
    (hδ : 0 < δ) (a : MeshIndex J) (m : ℕ) :
    Function.support (weight N J hJ β₀ δ a m) ⊆ separatedOpenSet N J hJ β₀ δ a m := by
  intro X hX
  have hθ : theta N J hJ δ a X ≠ 0 := by
    intro h
    exact hX (by simp only [weight, h, zero_mul])
  have hσ : sigma β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) m) X ≠ 0 := by
    intro h
    exact hX (by simp only [weight, h, mul_zero, zero_mul])
  refine ⟨occupation_gt_of_theta_pos hJ hδ a
    (lt_of_le_of_ne (theta_mem_Icc N J hJ δ a X).1 hθ.symm), ?_⟩
  exact lt_of_le_of_ne (sigma_mem_Icc _ _ _ _ _).1 hσ.symm

theorem zeta_support_subset {N J : ℕ} (hJ : 0 < J) {β₀ δ : ℝ}
    (hδ : 0 < δ) (a : MeshIndex J) (m : Fin (sourceScaleCount β₀ δ)) :
    Function.support (zeta N J hJ β₀ δ a m) ⊆ separatedOpenSet N J hJ β₀ δ a m := by
  intro X hX
  apply weight_support_subset hJ hδ a m
  intro hz
  exact hX (by simp only [zeta, hz, zero_div])

theorem zeta_eq_zero_off_openSet {N J : ℕ} (hJ : 0 < J) {β₀ δ : ℝ}
    (hδ : 0 < δ) (a : MeshIndex J) (m : Fin (sourceScaleCount β₀ δ)) {X : Configuration N}
    (hX : X ∉ separatedOpenSet N J hJ β₀ δ a m) : zeta N J hJ β₀ δ a m X = 0 := by
  by_contra h
  exact hX (zeta_support_subset hJ hδ a m h)

theorem active_centers_card_le {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hδ : 0 < δ) (hJ : sourceResolution β₀ δ ≤ J) (X : Configuration N) :
    ((heavyCenters N J (source_mesh_pos hJ) (δ / 2) X).card : ℝ) ≤ 8 / δ := by
  have h := heavyCenters_card_le N J hN (source_mesh_ge_three hJ)
    (by positivity : 0 < δ / 2) X
  convert h using 1
  ring

theorem openSet_mass_gt_four {N J : ℕ} {β₀ δ : ℝ} (hδ : 0 < δ)
    (hN : 8 / δ ≤ (N : ℝ)) (hJ : sourceResolution β₀ δ ≤ J)
    (a : MeshIndex J) (m : ℕ) {X : Configuration N}
    (hX : X ∈ separatedOpenSet N J (source_mesh_pos hJ) β₀ δ a m) :
    4 < mass (cellCenter J a) (scaleRadius J (separationRadius β₀) m) X := by
  have hNr : (0 : ℝ) < N := (by positivity : (0 : ℝ) < 8 / δ).trans_le hN
  have hNn : 0 < N := by exact_mod_cast hNr
  have hm := mass_gt_of_heavy hNn hJ a X hX.1 m
  have hn := (div_le_iff₀ hδ).mp hN
  nlinarith

theorem continuous_theta (N J : ℕ) (hJ : 0 < J) (δ : ℝ) (a : MeshIndex J) :
    Continuous (theta N J hJ δ a) :=
  contDiff_H.continuous.comp
    (((occupationFraction_continuous N J hJ a).sub continuous_const).div_const _)

theorem continuous_weight {N J : ℕ} (hN : 0 < N) (hJ : 0 < J) {δ : ℝ}
    (hδ : 0 < δ) (β₀ : ℝ) (a : MeshIndex J) (m : ℕ) :
    Continuous (weight N J hJ β₀ δ a m) := by
  apply Continuous.mul
    ((continuous_theta N J hJ δ a).mul (continuous_sigma hN hδ β₀ _ _))
  exact continuous_finsetProd _ fun r _ ↦
    continuous_const.sub (continuous_sigma hN hδ β₀ (cellCenter J a)
      (scaleRadius J (separationRadius β₀) r))

theorem continuous_squareSum {N J : ℕ} (hN : 0 < N) (hJ : 0 < J) {δ : ℝ}
    (hδ : 0 < δ) (β₀ : ℝ) : Continuous (squareSum N J hJ β₀ δ) := by
  exact continuous_finsetSum _ fun a _ ↦ continuous_finsetSum _ fun m _ ↦
    (continuous_weight hN hJ hδ β₀ a m).pow 2

theorem continuous_zeta {N J : ℕ} (hN : 0 < N) (hJ : 0 < J) {δ : ℝ}
    (hδ : 0 < δ) (β₀ : ℝ) (a : MeshIndex J) (m : Fin (sourceScaleCount β₀ δ)) :
    Continuous (zeta N J hJ β₀ δ a m) := by
  apply (continuous_weight hN hJ hδ β₀ a m).div
    (((continuous_squareSum hN hJ hδ β₀).max continuous_const).sqrt)
  intro X
  apply (Real.sqrt_pos.2 _).ne'
  have hM : (0 : ℝ) < sourceScaleCount β₀ δ := by
    exact_mod_cast Nat.zero_lt_of_lt m.isLt
  exact (inv_pos.mpr hM).trans_le (le_max_right _ _)

def zetaValue {N J : ℕ} (hN : 0 < N) (hJ : 0 < J) {δ : ℝ}
    (hδ : 0 < δ) (β₀ : ℝ) (a : MeshIndex J) (m : Fin (sourceScaleCount β₀ δ)) :
    C(Configuration N, ℝ) :=
  ⟨zeta N J hJ β₀ δ a m, continuous_zeta hN hJ hδ β₀ a m⟩

private theorem affine_threshold_lipschitz {t : ℝ} (ht : 0 < t) :
    LipschitzWith (Real.toNNReal (1 / t)) (fun r : ℝ ↦ (r - t) / t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.dist_eq,
    show (x - t) / t - (y - t) / t = (x - y) / t by ring,
    abs_div, abs_of_pos ht, Real.toNNReal_of_nonneg (by positivity)]
  change |x - y| / t ≤ (1 / t) * |x - y|
  exact le_of_eq (by ring)

theorem theta_lift_lipschitz {N J : ℕ} (hN : 0 < N) (hJ : 3 ≤ J)
    {δ : ℝ} (hδ : 0 < δ) (a : MeshIndex J) :
    LipschitzWith (2 * Real.toNNReal (1 / (δ / 2)) * occupationLipschitzConstant N J)
      (fun y ↦ theta N J (by omega) δ a (configurationQuotient N y)) := by
  simpa only [theta, Function.comp_def, mul_assoc] using
    H_lipschitz.comp ((affine_threshold_lipschitz (by positivity)).comp
      (occupationFraction_lift_lipschitz N J hN hJ a))

private theorem lipschitz_mul_Icc {E : Type*} [PseudoMetricSpace E]
    {f g : E → ℝ} {Cf Cg : ℝ≥0} (hf : LipschitzWith Cf f) (hg : LipschitzWith Cg g)
    (hfI : ∀ x, f x ∈ Icc (0 : ℝ) 1) (hgI : ∀ x, g x ∈ Icc (0 : ℝ) 1) :
    LipschitzWith (Cf + Cg) (fun x ↦ f x * g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, show f x * g x - f y * g y =
    (f x - f y) * g x + f y * (g x - g y) by ring]
  calc
    _ ≤ |(f x - f y) * g x| + |f y * (g x - g y)| := abs_add_le _ _
    _ ≤ |f x - f y| + |g x - g y| := by
      simp only [abs_mul, abs_of_nonneg (hgI x).1, abs_of_nonneg (hfI y).1]
      exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (hgI x).2)
        (mul_le_of_le_one_left (abs_nonneg _) (hfI y).2)
    _ ≤ (Cf : ℝ) * dist x y + (Cg : ℝ) * dist x y := by
      exact add_le_add (by simpa only [Real.dist_eq] using hf.dist_le_mul x y)
        (by simpa only [Real.dist_eq] using hg.dist_le_mul x y)
    _ = _ := by simp only [NNReal.coe_add]; ring

private theorem exists_lipschitz_prod_Icc {E ι : Type*} [PseudoMetricSpace E]
    (s : Finset ι) (f : ι → E → ℝ)
    (hI : ∀ i ∈ s, ∀ x, f i x ∈ Icc (0 : ℝ) 1)
    (hL : ∀ i ∈ s, ∃ C, LipschitzWith C (f i)) :
    ∃ C, LipschitzWith C (fun x ↦ ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨Ci, hCi⟩ := hL i (Finset.mem_insert_self _ _)
    obtain ⟨Cs, hCs⟩ := ih
      (fun j hj ↦ hI j (Finset.mem_insert_of_mem hj))
      (fun j hj ↦ hL j (Finset.mem_insert_of_mem hj))
    have hprod (x : E) : (∏ j ∈ s, f j x) ∈ Icc (0 : ℝ) 1 := by
      exact ⟨Finset.prod_nonneg fun j hj ↦ (hI j (Finset.mem_insert_of_mem hj) x).1,
        Finset.prod_le_one₀ (fun j hj ↦ (hI j (Finset.mem_insert_of_mem hj) x).1)
          (fun j hj ↦ (hI j (Finset.mem_insert_of_mem hj) x).2)⟩
    refine ⟨Ci + Cs, ?_⟩
    simpa only [Finset.prod_insert hi] using lipschitz_mul_Icc hCi hCs
      (hI i (Finset.mem_insert_self _ _)) hprod

private theorem exists_lipschitz_sum {E ι : Type*} [PseudoMetricSpace E]
    (s : Finset ι) (f : ι → E → ℝ) (hL : ∀ i ∈ s, ∃ C, LipschitzWith C (f i)) :
    ∃ C, LipschitzWith C (fun x ↦ ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨Ci, hCi⟩ := hL i (Finset.mem_insert_self _ _)
    obtain ⟨Cs, hCs⟩ := ih (fun j hj ↦ hL j (Finset.mem_insert_of_mem hj))
    exact ⟨Ci + Cs, by simpa only [Finset.sum_insert hi] using hCi.add hCs⟩

theorem weight_lift_lipschitz {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ)
    (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) {m : ℕ}
    (hm : m < sourceScaleCount β₀ δ) :
    ∃ C, LipschitzWith C
      (fun y ↦ weight N J (source_mesh_pos hJ) β₀ δ a m (configurationQuotient N y)) := by
  let q : ℕ → Gradient N → ℝ := fun r y ↦
    sigma β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) r)
      (configurationQuotient N y)
  have hq (r : ℕ) (hr : r < sourceScaleCount β₀ δ) : ∃ C, LipschitzWith C (q r) :=
    ⟨_, (source_rho_sigma_physical_lipschitz hN hβ₀ hβ hδ hJ a hr).2.lift⟩
  have hI (r : ℕ) (y : Gradient N) : 1 - q r y ∈ Icc (0 : ℝ) 1 := by
    have h := sigma_mem_Icc β₀ δ (cellCenter J a)
      (scaleRadius J (separationRadius β₀) r) (configurationQuotient N y)
    exact ⟨by linarith [h.2], by linarith [h.1]⟩
  obtain ⟨Cp, hCp⟩ := exists_lipschitz_prod_Icc (Finset.range m) (fun r y ↦ 1 - q r y)
    (fun r _ ↦ hI r) (by
      intro r hr
      obtain ⟨Cr, hCr⟩ := hq r ((Finset.mem_range.mp hr).trans hm)
      exact ⟨Cr, by simpa only [zero_add] using (LipschitzWith.const (1 : ℝ)).sub hCr⟩)
  obtain ⟨Cm, hCm⟩ := hq m hm
  have htm := lipschitz_mul_Icc (theta_lift_lipschitz hN (source_mesh_ge_three hJ) hδ a)
    hCm (fun y ↦ theta_mem_Icc _ _ _ _ _ _) (fun y ↦ sigma_mem_Icc _ _ _ _ _)
  have htmI (y : Gradient N) :
      theta N J (source_mesh_pos hJ) δ a (configurationQuotient N y) * q m y ∈ Icc (0 : ℝ) 1 := by
    have ht := theta_mem_Icc N J (source_mesh_pos hJ) δ a (configurationQuotient N y)
    have hs := sigma_mem_Icc β₀ δ (cellCenter J a)
      (scaleRadius J (separationRadius β₀) m) (configurationQuotient N y)
    exact ⟨mul_nonneg ht.1 hs.1,
      (mul_le_mul ht.2 hs.2 hs.1 (by norm_num)).trans_eq (by ring)⟩
  exact ⟨_, lipschitz_mul_Icc htm hCp htmI
    (fun y ↦ survival_mem_Icc N J β₀ δ a m (configurationQuotient N y))⟩

theorem squareSum_lift_lipschitz {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ)
    (hJ : sourceResolution β₀ δ ≤ J) :
    ∃ C, LipschitzWith C
      (fun y ↦ squareSum N J (source_mesh_pos hJ) β₀ δ (configurationQuotient N y)) := by
  apply exists_lipschitz_sum
  intro a _
  apply exists_lipschitz_sum
  intro m _
  obtain ⟨C, hC⟩ := weight_lift_lipschitz hN hβ₀ hβ hδ hJ a m.isLt
  refine ⟨C + C, ?_⟩
  simpa only [sq] using (lipschitz_mul_Icc hC hC
    (fun y ↦ weight_mem_Icc _ _ _ _ _ _ _ _) (fun y ↦ weight_mem_Icc _ _ _ _ _ _ _ _))

private theorem squareSum_le_card (N J : ℕ) (hJ : 0 < J) (β₀ δ : ℝ)
    (X : Configuration N) :
    squareSum N J hJ β₀ δ X ≤ (Fintype.card (MeshIndex J) : ℝ) * sourceScaleCount β₀ δ := by
  calc
    _ ≤ ∑ _a : MeshIndex J, ∑ _m : Fin (sourceScaleCount β₀ δ), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro m _
      have h := weight_mem_Icc N J hJ β₀ δ a m X
      nlinarith [h.1, h.2]
    _ = _ := by simp

private theorem exists_lipschitz_div_sqrt {E : Type*} [PseudoMetricSpace E]
    {f g : E → ℝ} {Cf Cg : ℝ≥0} {ε B : ℝ}
    (hf : LipschitzWith Cf f) (hg : LipschitzWith Cg g) (hε : 0 < ε)
    (hfI : ∀ x, f x ∈ Icc (0 : ℝ) 1) (hgI : ∀ x, g x ∈ Icc ε B) :
    ∃ C, LipschitzWith C (fun x ↦ f x / Real.sqrt (g x)) := by
  let R : Set (ℝ × ℝ) := Icc (0, ε) (1, B)
  have hp (p : ℝ × ℝ) (hp : p ∈ R) : 0 < p.2 := hε.trans_le hp.1.2
  have hq : ContDiffOn ℝ 1 (fun p : ℝ × ℝ ↦ p.1 / Real.sqrt p.2) R := by
    exact contDiffOn_fst.div (contDiffOn_snd.sqrt fun p hp' ↦ (hp p hp').ne')
      (fun p hp' ↦ (Real.sqrt_pos.2 (hp p hp')).ne')
  obtain ⟨C, hC⟩ := hq.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  refine ⟨C * max Cf Cg, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hmem (x : E) : (f x, g x) ∈ R := ⟨⟨(hfI x).1, (hgI x).1⟩, ⟨(hfI x).2, (hgI x).2⟩⟩
  exact (hC.dist_le_mul _ (hmem x) _ (hmem y)).trans
    (by simpa only [NNReal.coe_mul, mul_assoc] using
      mul_le_mul_of_nonneg_left ((hf.prodMk hg).dist_le_mul x y) C.coe_nonneg)

/-- The floor is used here only to construct global physical Lipschitz
regularity. The sharp localization cost below uses the local ratio instead. -/
theorem zeta_physical_lipschitz {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ)
    (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) (m : Fin (sourceScaleCount β₀ δ)) :
    ∃ C, ConfigurationEuclideanLipschitzWith C (zeta N J (source_mesh_pos hJ) β₀ δ a m) := by
  obtain ⟨Cw, hw⟩ := weight_lift_lipschitz hN hβ₀ hβ hδ hJ a m.isLt
  obtain ⟨CS, hS⟩ := squareSum_lift_lipschitz hN hβ₀ hβ hδ hJ
  have hM : (0 : ℝ) < sourceScaleCount β₀ δ := by
    exact_mod_cast Nat.zero_lt_of_lt m.isLt
  obtain ⟨C, hC⟩ := exists_lipschitz_div_sqrt hw
    (hS.max_const ((sourceScaleCount β₀ δ : ℝ)⁻¹)) (inv_pos.mpr hM)
    (fun y ↦ weight_mem_Icc N J (source_mesh_pos hJ) β₀ δ a m (configurationQuotient N y))
    (B := max ((Fintype.card (MeshIndex J) : ℝ) * sourceScaleCount β₀ δ)
      ((sourceScaleCount β₀ δ : ℝ)⁻¹)) (fun y ↦ ⟨le_max_right _ _,
        max_le_max (squareSum_le_card N J (source_mesh_pos hJ) β₀ δ _) le_rfl⟩)
  exact ⟨C, configurationEuclideanLipschitzWith_iff_lift.mpr hC⟩

private theorem configuration_sum_lipschitz_sharp {N : ℕ} {f : Torus → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C (fun y : PlanarSpace ↦ f (torusQuotient y))) :
    LipschitzWith (⟨Real.sqrt N, Real.sqrt_nonneg _⟩ * C)
      (fun y : Gradient N ↦ ∑ i : Fin N, f (configurationQuotient N y i)) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  let d : Fin N → ℝ := fun i ↦
    f (configurationQuotient N y i) - f (configurationQuotient N z i)
  have hd (i : Fin N) : (d i) ^ 2 ≤ (C : ℝ) ^ 2 * ‖particleProjection N i (y - z)‖ ^ 2 := by
    have h := hf.dist_le_mul (particleProjection N i y) (particleProjection N i z)
    simp only [quotient_particleProjection, dist_eq_norm, ← map_sub] at h
    simpa only [d, sq_abs, mul_pow] using pow_le_pow_left₀ (abs_nonneg (d i)) h 2
  have hsum : (∑ i : Fin N, (d i) ^ 2) ≤ (C : ℝ) ^ 2 * ‖y - z‖ ^ 2 := by
    calc
      _ ≤ ∑ i : Fin N, (C : ℝ) ^ 2 * ‖particleProjection N i (y - z)‖ ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ hd i
      _ = _ := by rw [← Finset.mul_sum, sum_particleProjection_norm_sq]
  have hcs : (∑ i : Fin N, d i) ^ 2 ≤ (N : ℝ) * (C : ℝ) ^ 2 * ‖y - z‖ ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N))
      (fun _ ↦ (1 : ℝ)) d
    have h' : (∑ i : Fin N, d i) ^ 2 ≤ (N : ℝ) * ∑ i : Fin N, (d i) ^ 2 := by
      simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one] using h
    exact h'.trans (by nlinarith [mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg N)])
  rw [Real.dist_eq, ← Finset.sum_sub_distrib, dist_eq_norm]
  change |∑ i : Fin N, d i| ≤ (Real.sqrt N * (C : ℝ)) * ‖y - z‖
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  simpa only [sq_abs, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N), mul_assoc] using hcs

theorem contDiff_mass_lift {N : ℕ} {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 64)
    (ξ : Torus) : ContDiff ℝ 2 (fun y : Gradient N ↦ mass ξ s (configurationQuotient N y)) := by
  simpa only [mass, Function.comp_def, quotient_particleProjection] using
    (ContDiff.sum fun i _ ↦ (contDiff_phi_lift hs hsmall ξ).comp (particleProjection N i).contDiff)

theorem contDiff_shellMass_lift {N : ℕ} {s K : ℝ} (hs : 0 < s) (hK : 0 < K)
    (houter : 2 * K * s ≤ 1 / 4) (ξ : Torus) :
    ContDiff ℝ 2 (fun y : Gradient N ↦ shellMass ξ s K (configurationQuotient N y)) := by
  simpa only [shellMass, Function.comp_def, quotient_particleProjection] using
    (ContDiff.sum fun i _ ↦ (contDiff_omega_lift hs hK houter ξ).comp
      (particleProjection N i).contDiff)

theorem norm_fderiv_mass_lift_le {N : ℕ} {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 64)
    (ξ : Torus) (y : Gradient N) :
    ‖fderiv ℝ (fun z ↦ mass ξ s (configurationQuotient N z)) y‖ ≤ Real.sqrt N / s := by
  have hφ : LipschitzWith (Real.toNNReal (1 / s))
      (fun x : PlanarSpace ↦ phi ξ s (torusQuotient x)) := by
    apply lipschitzWith_of_nnnorm_fderiv_le
      ((contDiff_phi_lift hs hsmall ξ).differentiable (by norm_num))
    intro x
    change ‖fderiv ℝ (fun z : PlanarSpace ↦ phi ξ s (torusQuotient z)) x‖ ≤
      (Real.toNNReal (1 / s) : ℝ)
    rw [Real.toNNReal_of_nonneg (by positivity)]
    exact norm_fderiv_phi_lift_le hs hsmall ξ x
  have h := norm_fderiv_le_of_lipschitz ℝ (configuration_sum_lipschitz_sharp (N := N) hφ)
    (x₀ := y)
  change ‖fderiv ℝ (fun z ↦ mass ξ s (configurationQuotient N z)) y‖ ≤
    Real.sqrt N * (Real.toNNReal (1 / s) : ℝ) at h
  rw [Real.toNNReal_of_nonneg (by positivity)] at h
  change ‖fderiv ℝ (fun z ↦ mass ξ s (configurationQuotient N z)) y‖ ≤
    Real.sqrt N * (1 / s) at h
  simpa only [mul_one_div] using h

theorem norm_fderiv_shellMass_lift_le {N : ℕ} {s K : ℝ} (hs : 0 < s) (hK : 2 ≤ K)
    (houter : 2 * K * s ≤ 1 / 4) (ξ : Torus) (y : Gradient N) :
    ‖fderiv ℝ (fun z ↦ shellMass ξ s K (configurationQuotient N z)) y‖ ≤
      2 * Real.sqrt N / s := by
  have hω : LipschitzWith (Real.toNNReal (2 / s))
      (fun x : PlanarSpace ↦ omega ξ s K (torusQuotient x)) := by
    apply lipschitzWith_of_nnnorm_fderiv_le
      ((contDiff_omega_lift hs (by linarith) houter ξ).differentiable (by norm_num))
    intro x
    change ‖fderiv ℝ (fun z : PlanarSpace ↦ omega ξ s K (torusQuotient z)) x‖ ≤
      (Real.toNNReal (2 / s) : ℝ)
    rw [Real.toNNReal_of_nonneg (by positivity)]
    exact norm_fderiv_omega_lift_le hs hK houter ξ x
  have h := norm_fderiv_le_of_lipschitz ℝ (configuration_sum_lipschitz_sharp (N := N) hω)
    (x₀ := y)
  change ‖fderiv ℝ (fun z ↦ shellMass ξ s K (configurationQuotient N z)) y‖ ≤
    Real.sqrt N * (Real.toNNReal (2 / s) : ℝ) at h
  rw [Real.toNNReal_of_nonneg (by positivity)] at h
  change ‖fderiv ℝ (fun z ↦ shellMass ξ s K (configurationQuotient N z)) y‖ ≤
    Real.sqrt N * (2 / s) at h
  exact h.trans_eq (by ring)

private theorem norm_fderiv_div_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} {Cf Cg : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hgp : 0 < g x) (hf0 : 0 ≤ f x) (hfg : f x ≤ g x)
    (hCf : ‖fderiv ℝ f x‖ ≤ Cf) (hCg : ‖fderiv ℝ g x‖ ≤ Cg) :
    ‖fderiv ℝ (fun y ↦ f y / g y) x‖ ≤ (Cf + Cg) / g x := by
  have hi := (hasDerivAt_inv hgp.ne').comp_hasFDerivAt x hg.hasFDerivAt
  have hd := hf.hasFDerivAt.mul hi
  change HasFDerivAt (fun y ↦ f y * (g y)⁻¹) _ x at hd
  rw [show (fun y ↦ f y / g y) = (fun y ↦ f y * (g y)⁻¹) by ext; exact div_eq_mul_inv _ _,
    hd.fderiv]
  have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans hCg
  calc
    _ ≤ ‖f x • (-(g x ^ 2)⁻¹ • fderiv ℝ g x)‖ + ‖(g x)⁻¹ • fderiv ℝ f x‖ := norm_add_le _ _
    _ = f x * (g x ^ 2)⁻¹ * ‖fderiv ℝ g x‖ + (g x)⁻¹ * ‖fderiv ℝ f x‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hf0, abs_neg, abs_inv,
        abs_of_pos hgp, abs_of_nonneg (sq_nonneg (g x)), mul_assoc]
    _ ≤ f x * (g x ^ 2)⁻¹ * Cg + (g x)⁻¹ * Cf := by
      exact add_le_add (mul_le_mul_of_nonneg_left hCg (by positivity))
        (mul_le_mul_of_nonneg_left hCf (by positivity))
    _ ≤ g x * (g x ^ 2)⁻¹ * Cg + (g x)⁻¹ * Cf := by
      gcongr
    _ = _ := by field_simp [hgp.ne']; ring

private theorem rho_lift_eventuallyEq {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hδ : 0 < δ) (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) (m : ℕ)
    (y : Gradient N)
    (hocc : δ / 2 < occupationFraction N J (source_mesh_pos hJ) a (configurationQuotient N y)) :
    (fun z ↦ rho β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) m)
      (configurationQuotient N z)) =ᶠ[𝓝 y]
    (fun z ↦ shellMass (cellCenter J a) (scaleRadius J (separationRadius β₀) m)
      (separationRadius β₀) (configurationQuotient N z) /
      mass (cellCenter J a) (scaleRadius J (separationRadius β₀) m) (configurationQuotient N z)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hm := mass_gt_of_heavy hN hJ a (configurationQuotient N y) hocc m
  have hmf : δ * N / 4 < mass (cellCenter J a) (scaleRadius J (separationRadius β₀) m)
      (configurationQuotient N y) := by nlinarith
  have hc := (continuous_mass (N := N) (cellCenter J a)
    (scaleRadius J (separationRadius β₀) m)).comp (continuous_configurationQuotient N)
  filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hmf] with z hz
  exact congrArg (fun d : ℝ ↦ _ / d) (max_eq_left hz.le)

theorem rho_lift_differentiableAt_of_heavy {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ)
    (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) {m : ℕ}
    (hm : m < sourceScaleCount β₀ δ) (y : Gradient N)
    (hocc : δ / 2 < occupationFraction N J (source_mesh_pos hJ) a (configurationQuotient N y)) :
    DifferentiableAt ℝ
      (fun z ↦ rho β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) m)
        (configurationQuotient N z)) y := by
  obtain ⟨hs, hs', ho, _⟩ := source_scale_admissibility hβ₀ hβ hJ hm
  have hp := source_radius_pos hJ m
  have hM := (contDiff_mass_lift (N := N) hp (hs.trans hs') (cellCenter J a)).differentiable
    (by norm_num)
  have hS := (contDiff_shellMass_lift (N := N) hp
    (by linarith [separationRadius_ge_eight β₀]) ho (cellCenter J a)).differentiable (by norm_num)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMp := mass_gt_of_heavy hN hJ a (configurationQuotient N y) hocc m
  have hpM : 0 < mass (cellCenter J a) (scaleRadius J (separationRadius β₀) m)
      (configurationQuotient N y) := lt_trans (by positivity) hMp
  have hi := (hasDerivAt_inv hpM.ne').comp_hasFDerivAt y (hM y).hasFDerivAt
  have hd := (hS y).hasFDerivAt.mul hi
  have hq : DifferentiableAt ℝ (fun z : Gradient N ↦
      shellMass (cellCenter J a) (scaleRadius J (separationRadius β₀) m)
        (separationRadius β₀) (configurationQuotient N z) /
      mass (cellCenter J a) (scaleRadius J (separationRadius β₀) m) (configurationQuotient N z)) y := by
    simpa only [div_eq_mul_inv, Function.comp_def, Pi.mul_apply] using! hd.differentiableAt
  exact hq.congr_of_eventuallyEq (rho_lift_eventuallyEq hN hδ hJ a m y hocc)

/-- The source ratio estimate uses the actual mass denominator and the
condition `rho ≤ 1`. No global floor constant enters this bound. -/
theorem norm_fderiv_rho_lift_le_of_heavy {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ)
    (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) {m : ℕ}
    (hm : m < sourceScaleCount β₀ δ) (y : Gradient N)
    (hocc : δ / 2 < occupationFraction N J (source_mesh_pos hJ) a (configurationQuotient N y))
    (hr : rho β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) m)
      (configurationQuotient N y) ≤ 1) :
    ‖fderiv ℝ (fun z ↦ rho β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) m)
      (configurationQuotient N z)) y‖ ≤
      3 * Real.sqrt N /
        (scaleRadius J (separationRadius β₀) m *
          mass (cellCenter J a) (scaleRadius J (separationRadius β₀) m) (configurationQuotient N y)) := by
  obtain ⟨hs, hs', ho, _⟩ := source_scale_admissibility hβ₀ hβ hJ hm
  have hp := source_radius_pos hJ m
  have hK : 2 ≤ separationRadius β₀ := by linarith [separationRadius_ge_eight β₀]
  have hM := (contDiff_mass_lift (N := N) hp (hs.trans hs') (cellCenter J a)).differentiable
    (by norm_num)
  have hS := (contDiff_shellMass_lift (N := N) hp (by linarith) ho
    (cellCenter J a)).differentiable (by norm_num)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMp : 0 < mass (cellCenter J a) (scaleRadius J (separationRadius β₀) m)
      (configurationQuotient N y) :=
    lt_trans (by positivity) (mass_gt_of_heavy hN hJ a (configurationQuotient N y) hocc m)
  have he := rho_lift_eventuallyEq hN hδ hJ a m y hocc
  rw [he.eq_of_nhds] at hr
  have hfg := (div_le_iff₀ hMp).mp hr
  rw [he.fderiv_eq]
  have h := norm_fderiv_div_le (hS y) (hM y) hMp (shellMass_nonneg _ _ _ _)
    (by simpa only [one_mul] using hfg)
    (norm_fderiv_shellMass_lift_le hp hK ho (cellCenter J a) y)
    (norm_fderiv_mass_lift_le hp (hs.trans hs') (cellCenter J a) y)
  convert h using 1
  ring

private theorem norm_fderiv_rho_lift_mesh_bound {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ)
    (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) {m : ℕ}
    (hm : m < sourceScaleCount β₀ δ) (y : Gradient N)
    (hocc : δ / 2 < occupationFraction N J (source_mesh_pos hJ) a (configurationQuotient N y))
    (hr : rho β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) m)
      (configurationQuotient N y) ≤ 1) :
    ‖fderiv ℝ (fun z ↦ rho β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) m)
      (configurationQuotient N z)) y‖ ≤ 3 * J / (δ * Real.sqrt N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hJr : (0 : ℝ) < J := by exact_mod_cast source_mesh_pos hJ
  have hsr := source_radius_pos hJ m
  have hmass := mass_gt_of_heavy hN hJ a (configurationQuotient N y) hocc m
  have hMp : 0 < mass (cellCenter J a) (scaleRadius J (separationRadius β₀) m)
      (configurationQuotient N y) := lt_trans (by positivity) hmass
  have hs0 : 2 / (J : ℝ) ≤ scaleRadius J (separationRadius β₀) m := by
    simpa only [scaleRadius, pow_zero, mul_one] using
      (scaleRadius_mono (J := J) (K := separationRadius β₀)
        (by linarith [separationRadius_ge_eight β₀]) (Nat.zero_le m))
  have hsJ := (div_le_iff₀ hJr).mp hs0
  have hsm : δ * N ≤ (J : ℝ) * scaleRadius J (separationRadius β₀) m *
      mass (cellCenter J a) (scaleRadius J (separationRadius β₀) m) (configurationQuotient N y) := by
    nlinarith [mul_le_mul_of_nonneg_right hsJ hMp.le]
  apply (norm_fderiv_rho_lift_le_of_heavy hN hβ₀ hβ hδ hJ a hm y hocc hr).trans
  apply (div_le_div_iff₀ (mul_pos hsr hMp) (mul_pos hδ (Real.sqrt_pos.2 hNr))).2
  calc
    _ = 3 * δ * N := by nlinarith [Real.sq_sqrt hNr.le]
    _ ≤ _ := by nlinarith [hsm]

private theorem hasFDerivAt_complement_H {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E} (hf : HasFDerivAt f f' x) (t : ℝ) :
    HasFDerivAt (fun y ↦ 1 - H ((f y - t) / t))
      (-(b ((f x - t) / t) • (t⁻¹ • f'))) x := by
  have ha := (hf.sub_const t).mul_const t⁻¹
  have hh := (hasDerivAt_H ((f x - t) / t)).comp_hasFDerivAt x ha
  simpa only [Function.comp_def, div_eq_mul_inv] using hh.const_sub 1

private theorem fderiv_eq_zero_of_nonneg_of_eq_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E}
    (hf : ∀ y, 0 ≤ f y) (hx : f x = 0) : fderiv ℝ f x = 0 := by
  apply IsLocalMin.fderiv_eq_zero
  exact Filter.Eventually.of_forall fun y ↦ by simpa only [hx] using hf y

theorem sigma_lift_differentiableAt_of_heavy {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ)
    (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) {m : ℕ}
    (hm : m < sourceScaleCount β₀ δ) (y : Gradient N)
    (hocc : δ / 2 < occupationFraction N J (source_mesh_pos hJ) a (configurationQuotient N y)) :
    DifferentiableAt ℝ
      (fun z ↦ sigma β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) m)
        (configurationQuotient N z)) y :=
  (hasFDerivAt_complement_H
    (rho_lift_differentiableAt_of_heavy hN hβ₀ hβ hδ hJ a hm y hocc).hasFDerivAt
    (separationConstant β₀ * (4 - β₀))).differentiableAt

/-- At a zero of sigma, its nonnegativity forces the total derivative to
vanish. This includes the transition endpoint, with no null-level-set premise. -/
theorem norm_fderiv_sigma_lift_le_of_heavy {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ)
    (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) {m : ℕ}
    (hm : m < sourceScaleCount β₀ δ) (y : Gradient N)
    (hocc : δ / 2 < occupationFraction N J (source_mesh_pos hJ) a (configurationQuotient N y)) :
    ‖fderiv ℝ (fun z ↦ sigma β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) m)
      (configurationQuotient N z)) y‖ ≤
        6 * J / (separationConstant β₀ * (4 - β₀) * δ * Real.sqrt N) := by
  have ht := separation_threshold_pos hβ₀ hβ
  by_cases hz : sigma β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) m)
      (configurationQuotient N y) = 0
  · rw [fderiv_eq_zero_of_nonneg_of_eq_zero
      (f := fun z : Gradient N ↦ sigma β₀ δ (cellCenter J a)
        (scaleRadius J (separationRadius β₀) m) (configurationQuotient N z))
      (fun z ↦ (sigma_mem_Icc _ _ _ _ _).1) hz,
      norm_zero]
    positivity
  have hσp : 0 < sigma β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) m)
      (configurationQuotient N y) := lt_of_le_of_ne (sigma_mem_Icc _ _ _ _ _).1 (Ne.symm hz)
  have hr : rho β₀ δ (cellCenter J a) (scaleRadius J (separationRadius β₀) m)
      (configurationQuotient N y) ≤ 1 := by
    have hr' := rho_lt_twice_threshold_of_sigma_pos hβ₀ hβ hσp
    have ht' := separation_fraction_lt hβ₀
    nlinarith
  have hd := hasFDerivAt_complement_H
    (rho_lift_differentiableAt_of_heavy hN hβ₀ hβ hδ hJ a hm y hocc).hasFDerivAt
    (separationConstant β₀ * (4 - β₀))
  change HasFDerivAt (fun z ↦ sigma β₀ δ (cellCenter J a)
    (scaleRadius J (separationRadius β₀) m) (configurationQuotient N z)) _ y at hd
  rw [hd.fderiv, norm_neg, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (b_nonneg _), abs_inv, abs_of_pos ht]
  calc
    _ ≤ 2 * ((separationConstant β₀ * (4 - β₀))⁻¹ *
        (3 * J / (δ * Real.sqrt N))) :=
      mul_le_mul (b_le_two _) (mul_le_mul_of_nonneg_left
        (norm_fderiv_rho_lift_mesh_bound hN hβ₀ hβ hδ hJ a hm y hocc hr)
        (inv_nonneg.mpr ht.le)) (by positivity) (by norm_num)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

theorem theta_lift_differentiable (N J : ℕ) (hJ : 0 < J) (δ : ℝ) (a : MeshIndex J) :
    Differentiable ℝ (fun y : Gradient N ↦ theta N J hJ δ a (configurationQuotient N y)) := by
  have ho := ((occupationFraction_smooth N J hJ a).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ ∞))
  exact (contDiff_H.comp ((ho.sub contDiff_const).div_const _)).differentiable (by norm_num)

theorem norm_fderiv_theta_lift_le {N J : ℕ} (hN : 0 < N) (hJ : 3 ≤ J)
    {δ : ℝ} (hδ : 0 < δ) (a : MeshIndex J) (y : Gradient N) :
    ‖fderiv ℝ (fun z ↦ theta N J (by omega) δ a (configurationQuotient N z)) y‖ ≤
      17 * J / (δ * Real.sqrt N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hC := occupationLipschitzConstant_sq N J
  have hCS : ((occupationLipschitzConstant N J : ℝ) * Real.sqrt N) ^ 2 = 18 * (J : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hNr.le, hC]
    field_simp [hNr.ne']
  have hsmall : 4 * (occupationLipschitzConstant N J : ℝ) * Real.sqrt N ≤ 17 * J := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith [hCS, sq_nonneg (J : ℝ)]
  have h := norm_fderiv_le_of_lipschitz ℝ (theta_lift_lipschitz hN hJ hδ a) (x₀ := y)
  change ‖fderiv ℝ (fun z ↦ theta N J (by omega) δ a (configurationQuotient N z)) y‖ ≤
    (2 * (Real.toNNReal (1 / (δ / 2)) : ℝ)) * (occupationLipschitzConstant N J : ℝ) at h
  rw [Real.toNNReal_of_nonneg (by positivity)] at h
  change ‖fderiv ℝ (fun z ↦ theta N J (by omega) δ a (configurationQuotient N z)) y‖ ≤
    (2 * (1 / (δ / 2))) * (occupationLipschitzConstant N J : ℝ) at h
  apply (le_div_iff₀ (mul_pos hδ (Real.sqrt_pos.2 hNr))).2
  calc
    _ ≤ (2 * (1 / (δ / 2)) * (occupationLipschitzConstant N J : ℝ)) *
        (δ * Real.sqrt N) := mul_le_mul_of_nonneg_right h (by positivity)
    _ = 4 * (occupationLipschitzConstant N J : ℝ) * Real.sqrt N := by field_simp [hδ.ne']; ring
    _ ≤ _ := hsmall

theorem scaleGradientConstant_nonneg {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (δ : ℝ) :
    0 ≤ scaleGradientConstant β₀ δ := by
  have ht := separation_threshold_pos hβ₀ hβ
  unfold scaleGradientConstant
  positivity

private theorem norm_fderiv_mul_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hfI : f x ∈ Icc (0 : ℝ) 1) (hgI : g x ∈ Icc (0 : ℝ) 1) :
    ‖fderiv ℝ (fun y ↦ f y * g y) x‖ ≤ ‖fderiv ℝ f x‖ + ‖fderiv ℝ g x‖ := by
  rw [fderiv_fun_mul hf hg]
  calc
    _ ≤ ‖f x • fderiv ℝ g x‖ + ‖g x • fderiv ℝ f x‖ := norm_add_le _ _
    _ = f x * ‖fderiv ℝ g x‖ + g x * ‖fderiv ℝ f x‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hfI.1, abs_of_nonneg hgI.1]
    _ ≤ ‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖ :=
      add_le_add (mul_le_of_le_one_left (norm_nonneg _) hfI.2)
        (mul_le_of_le_one_left (norm_nonneg _) hgI.2)
    _ = _ := add_comm _ _

private theorem norm_fderiv_prod_Icc {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (f : ι → E → ℝ) (x : E)
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x)
    (hI : ∀ i ∈ s, f i x ∈ Icc (0 : ℝ) 1) :
    ‖fderiv ℝ (fun y ↦ ∏ i ∈ s, f i y) x‖ ≤ ∑ i ∈ s, ‖fderiv ℝ (f i) x‖ := by
  classical
  have hd := HasFDerivAt.finsetProd fun i hi ↦ (hf i hi).hasFDerivAt
  change HasFDerivAt (fun y ↦ ∏ i ∈ s, f i y) _ x at hd
  rw [hd.fderiv]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have hp0 : 0 ≤ ∏ j ∈ s.erase i, f j x :=
    Finset.prod_nonneg fun j hj ↦ (hI j (Finset.mem_of_mem_erase hj)).1
  have hp1 : (∏ j ∈ s.erase i, f j x) ≤ 1 :=
    Finset.prod_le_one₀ (fun j hj ↦ (hI j (Finset.mem_of_mem_erase hj)).1)
      (fun j hj ↦ (hI j (Finset.mem_of_mem_erase hj)).2)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp0]
  exact mul_le_of_le_one_left (norm_nonneg _) hp1

/-- Zero occupation cutoffs give zero total derivatives, including the
occupation threshold itself. No exceptional level set is discarded. -/
theorem fderiv_weight_lift_eq_zero_of_occupation_le {N J : ℕ} (hJ : 0 < J)
    {β₀ δ : ℝ} (hδ : 0 < δ) (a : MeshIndex J) (m : ℕ) (y : Gradient N)
    (hocc : occupationFraction N J hJ a (configurationQuotient N y) ≤ δ / 2) :
    fderiv ℝ (fun z ↦ weight N J hJ β₀ δ a m (configurationQuotient N z)) y = 0 := by
  apply fderiv_eq_zero_of_nonneg_of_eq_zero
    (fun z ↦ (weight_mem_Icc N J hJ β₀ δ a m (configurationQuotient N z)).1)
  exact weight_eq_zero_of_occupation_le hJ hδ a m hocc

theorem norm_fderiv_weight_lift_le {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ)
    (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) {m : ℕ}
    (hm : m < sourceScaleCount β₀ δ) (y : Gradient N) :
    ‖fderiv ℝ (fun z ↦ weight N J (source_mesh_pos hJ) β₀ δ a m (configurationQuotient N z)) y‖ ≤
      scaleGradientConstant β₀ δ * J / (δ * Real.sqrt N) := by
  have hA := scaleGradientConstant_nonneg hβ₀ hβ δ
  by_cases hocc : δ / 2 < occupationFraction N J (source_mesh_pos hJ) a (configurationQuotient N y)
  · let q : ℕ → Gradient N → ℝ := fun r z ↦ sigma β₀ δ (cellCenter J a)
      (scaleRadius J (separationRadius β₀) r) (configurationQuotient N z)
    let T : Gradient N → ℝ := fun z ↦ theta N J (source_mesh_pos hJ) δ a (configurationQuotient N z)
    let P : Gradient N → ℝ := fun z ↦ ∏ r ∈ Finset.range m, (1 - q r z)
    let Cσ : ℝ := 6 * J / (separationConstant β₀ * (4 - β₀) * δ * Real.sqrt N)
    have hCσ : 0 ≤ Cσ := by
      have ht := separation_threshold_pos hβ₀ hβ
      dsimp [Cσ]
      positivity
    have hqd (r : ℕ) (hr : r < sourceScaleCount β₀ δ) : DifferentiableAt ℝ (q r) y :=
      sigma_lift_differentiableAt_of_heavy hN hβ₀ hβ hδ hJ a hr y hocc
    have hqb (r : ℕ) (hr : r < sourceScaleCount β₀ δ) : ‖fderiv ℝ (q r) y‖ ≤ Cσ :=
      norm_fderiv_sigma_lift_le_of_heavy hN hβ₀ hβ hδ hJ a hr y hocc
    have hqI (r : ℕ) : 1 - q r y ∈ Icc (0 : ℝ) 1 := by
      have h := sigma_mem_Icc β₀ δ (cellCenter J a)
        (scaleRadius J (separationRadius β₀) r) (configurationQuotient N y)
      exact ⟨by linarith [h.2], by linarith [h.1]⟩
    have hpd (r : ℕ) (hr : r ∈ Finset.range m) :
        DifferentiableAt ℝ (fun z ↦ 1 - q r z) y :=
      (hqd r ((Finset.mem_range.mp hr).trans hm)).const_sub 1
    have hP := (HasFDerivAt.finsetProd fun r hr ↦ (hpd r hr).hasFDerivAt).differentiableAt
    change DifferentiableAt ℝ P y at hP
    have hPb : ‖fderiv ℝ P y‖ ≤ m * Cσ := by
      apply (norm_fderiv_prod_Icc (Finset.range m) (fun r z ↦ 1 - q r z) y hpd
        (fun r _ ↦ hqI r)).trans
      calc
        _ ≤ ∑ _r ∈ Finset.range m, Cσ := by
          apply Finset.sum_le_sum
          intro r hr
          rw [fderiv_const_sub, norm_neg]
          exact hqb r ((Finset.mem_range.mp hr).trans hm)
        _ = _ := by simp
    have hTd : DifferentiableAt ℝ T y := theta_lift_differentiable N J (source_mesh_pos hJ) δ a y
    have hTI := theta_mem_Icc N J (source_mesh_pos hJ) δ a (configurationQuotient N y)
    have hQI := sigma_mem_Icc β₀ δ (cellCenter J a)
      (scaleRadius J (separationRadius β₀) m) (configurationQuotient N y)
    have hTQI : T y * q m y ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg hTI.1 hQI.1,
        (mul_le_mul hTI.2 hQI.2 hQI.1 (by norm_num)).trans_eq (by ring)⟩
    have hw := norm_fderiv_mul_Icc (hTd.mul (hqd m hm)) hP hTQI
      (survival_mem_Icc N J β₀ δ a m (configurationQuotient N y))
    have hw' := norm_fderiv_mul_Icc hTd (hqd m hm) hTI hQI
    have hmM : (m : ℝ) + 1 ≤ sourceScaleCount β₀ δ := by
      exact_mod_cast Nat.succ_le_of_lt hm
    calc
      _ ≤ ‖fderiv ℝ T y‖ + ‖fderiv ℝ (q m) y‖ + ‖fderiv ℝ P y‖ := by
        exact hw.trans (add_le_add hw' le_rfl)
      _ ≤ 17 * J / (δ * Real.sqrt N) + Cσ + m * Cσ :=
        add_le_add (add_le_add (norm_fderiv_theta_lift_le hN (source_mesh_ge_three hJ) hδ a y)
          (hqb m hm)) hPb
      _ ≤ 17 * J / (δ * Real.sqrt N) + sourceScaleCount β₀ δ * Cσ := by
        nlinarith [mul_le_mul_of_nonneg_right hmM hCσ]
      _ = _ := by dsimp [Cσ, scaleGradientConstant]; simp only [div_eq_mul_inv, mul_inv_rev]; ring
  · rw [fderiv_weight_lift_eq_zero_of_occupation_le (source_mesh_pos hJ) hδ a m y
      (le_of_not_gt hocc), norm_zero]
    positivity

theorem sum_weight_derivative_sq_le {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ)
    (hJ : sourceResolution β₀ δ ≤ J) (y : Gradient N) :
    (∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ),
      ‖fderiv ℝ (fun z ↦ weight N J (source_mesh_pos hJ) β₀ δ a m (configurationQuotient N z)) y‖ ^ 2) ≤
      8 * sourceScaleCount β₀ δ * scaleGradientConstant β₀ δ ^ 2 * (J : ℝ) ^ 2 /
        (δ ^ 3 * N) := by
  classical
  let B : ℝ := scaleGradientConstant β₀ δ * J / (δ * Real.sqrt N)
  have hB : 0 ≤ B := by
    have hA := scaleGradientConstant_nonneg hβ₀ hβ δ
    dsimp [B]
    positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcard := active_centers_card_le hN hδ hJ (configurationQuotient N y)
  calc
    _ ≤ ∑ a : MeshIndex J,
        if δ / 2 < occupationFraction N J (source_mesh_pos hJ) a (configurationQuotient N y)
        then (sourceScaleCount β₀ δ : ℝ) * B ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs with ha
      · calc
          _ ≤ ∑ _m : Fin (sourceScaleCount β₀ δ), B ^ 2 :=
            Finset.sum_le_sum fun m _ ↦ pow_le_pow_left₀ (norm_nonneg _)
              (norm_fderiv_weight_lift_le hN hβ₀ hβ hδ hJ a m.isLt y) 2
          _ = _ := by simp
      · apply le_of_eq
        apply Finset.sum_eq_zero
        intro m _
        rw [fderiv_weight_lift_eq_zero_of_occupation_le (source_mesh_pos hJ) hδ a m y
          (le_of_not_gt ha), norm_zero, zero_pow (by decide)]
    _ = ((heavyCenters N J (source_mesh_pos hJ) (δ / 2) (configurationQuotient N y)).card : ℝ) *
        ((sourceScaleCount β₀ δ : ℝ) * B ^ 2) := by
      rw [← Finset.sum_filter]
      simp only [heavyCenters, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (8 / δ) * ((sourceScaleCount β₀ δ : ℝ) * B ^ 2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      dsimp [B]
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hNr.le]
      field_simp [hδ.ne', hNr.ne']

private theorem normalized_fields_sq_le {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (a : ι → ℝ) (d : ι → F)
    (hS : 0 < ∑ i, a i ^ 2) :
    (∑ i, ‖(Real.sqrt (∑ j, a j ^ 2))⁻¹ • d i -
      (a i / ((∑ j, a j ^ 2) * Real.sqrt (∑ j, a j ^ 2))) • (∑ j, a j • d j)‖ ^ 2) ≤
      (4 / (∑ i, a i ^ 2)) * ∑ i, ‖d i‖ ^ 2 := by
  let S : ℝ := ∑ i, a i ^ 2
  let L : ℝ := ∑ i, ‖d i‖ ^ 2
  let P : F := ∑ i, a i • d i
  have hSp : 0 < S := hS
  have hsqrt := Real.sqrt_pos.2 hSp
  have hsq := Real.sq_sqrt hSp.le
  have hPn : ‖P‖ ≤ ∑ i, |a i| * ‖d i‖ := by
    simpa only [P, norm_smul, Real.norm_eq_abs] using
      (norm_sum_le (Finset.univ : Finset ι) (fun i ↦ a i • d i))
  have hP : ‖P‖ ^ 2 ≤ S * L := by
    apply (pow_le_pow_left₀ (norm_nonneg _) hPn 2).trans
    simpa only [S, L, sq_abs] using
      Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) (fun i ↦ |a i|) (fun i ↦ ‖d i‖)
  have hi (i : ι) : ‖(Real.sqrt S)⁻¹ • d i - (a i / (S * Real.sqrt S)) • P‖ ^ 2 ≤
      (2 / S) * ‖d i‖ ^ 2 + (2 / S ^ 3 * ‖P‖ ^ 2) * a i ^ 2 := by
    calc
      _ ≤ (‖(Real.sqrt S)⁻¹ • d i‖ + ‖(a i / (S * Real.sqrt S)) • P‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
      _ ≤ 2 * (‖(Real.sqrt S)⁻¹ • d i‖ ^ 2 + ‖(a i / (S * Real.sqrt S)) • P‖ ^ 2) := add_sq_le
      _ = _ := by
        simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, div_pow, hsq]
        field_simp [hSp.ne']
  change (∑ i, ‖(Real.sqrt S)⁻¹ • d i - (a i / (S * Real.sqrt S)) • P‖ ^ 2) ≤ 4 / S * L
  calc
    _ ≤ ∑ i, ((2 / S) * ‖d i‖ ^ 2 + (2 / S ^ 3 * ‖P‖ ^ 2) * a i ^ 2) :=
      Finset.sum_le_sum fun i _ ↦ hi i
    _ = (2 / S) * L + (2 / S ^ 3 * ‖P‖ ^ 2) * S := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (2 / S) * L + (2 / S ^ 3 * (S * L)) * S :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hP (by positivity)) hSp.le)
    _ = _ := by field_simp [hSp.ne']; ring

private theorem normalized_fderiv_sum_sq_le {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Fintype ι] (f : ι → E → ℝ) (x : E)
    (hf : ∀ i, DifferentiableAt ℝ (f i) x) (hS : 0 < ∑ i, f i x ^ 2) :
    (∑ i, ‖fderiv ℝ (fun y ↦ f i y / Real.sqrt (∑ j, f j y ^ 2)) x‖ ^ 2) ≤
      (4 / (∑ i, f i x ^ 2)) * ∑ i, ‖fderiv ℝ (f i) x‖ ^ 2 := by
  let S : ℝ := ∑ i, f i x ^ 2
  let P : E →L[ℝ] ℝ := ∑ i, f i x • fderiv ℝ (f i) x
  have hSp : 0 < S := hS
  have hsqrt := Real.sqrt_pos.2 hSp
  have hsq := Real.sq_sqrt hSp.le
  have hfi (i : ι) : HasFDerivAt (fun y ↦ f i y ^ 2) ((2 * f i x) • fderiv ℝ (f i) x) x := by
    simpa only [Function.comp_def, Nat.cast_ofNat, show 2 - 1 = (1 : ℕ) by decide, pow_one] using
      (hasDerivAt_pow 2 (f i x)).comp_hasFDerivAt x (hf i).hasFDerivAt
  have hSd : HasFDerivAt (fun y ↦ ∑ i, f i y ^ 2) ((2 : ℝ) • P) x := by
    have hd := HasFDerivAt.fun_sum fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦ hfi i
    change HasFDerivAt (fun y ↦ ∑ i, f i y ^ 2) (∑ i, (2 * f i x) • fderiv ℝ (f i) x) x at hd
    simpa only [P, Finset.smul_sum, mul_smul] using hd
  have hinv := (Real.hasDerivAt_sqrt hSp.ne').inv hsqrt.ne'
  change HasDerivAt (fun r : ℝ ↦ (Real.sqrt r)⁻¹) (-(1 / (2 * Real.sqrt S)) / (Real.sqrt S) ^ 2) S at hinv
  have hc : HasDerivAt (fun r : ℝ ↦ (Real.sqrt r)⁻¹) (-1 / (2 * S * Real.sqrt S)) S := by
    convert hinv using 1
    rw [hsq]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hF (i : ι) : fderiv ℝ (fun y ↦ f i y / Real.sqrt (∑ j, f j y ^ 2)) x =
      (Real.sqrt S)⁻¹ • fderiv ℝ (f i) x - (f i x / (S * Real.sqrt S)) • P := by
    have hd := (hf i).hasFDerivAt.mul (hc.comp_hasFDerivAt x hSd)
    change HasFDerivAt (fun y ↦ f i y / Real.sqrt (∑ j, f j y ^ 2)) _ x at hd
    have hd' : HasFDerivAt (fun y ↦ f i y / Real.sqrt (∑ j, f j y ^ 2))
        ((Real.sqrt S)⁻¹ • fderiv ℝ (f i) x - (f i x / (S * Real.sqrt S)) • P) x := by
      apply hd.congr_fderiv
      ext v
      simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, div_eq_mul_inv, mul_inv_rev,
        Function.comp_apply, S]
      ring
    exact hd'.fderiv
  calc
    _ = ∑ i, ‖(Real.sqrt S)⁻¹ • fderiv ℝ (f i) x -
        (f i x / (S * Real.sqrt S)) • P‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hF i]
    _ ≤ _ := normalized_fields_sq_le (fun i ↦ f i x) (fun i ↦ fderiv ℝ (f i) x) hS

private theorem zeta_lift_eventuallyEq_on_heavy {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) (m : Fin (sourceScaleCount β₀ δ))
    (y : Gradient N)
    (hy : δ < maximumOccupation N J (source_mesh_pos hJ) (configurationQuotient N y)) :
    (fun z ↦ zeta N J (source_mesh_pos hJ) β₀ δ a m (configurationQuotient N z)) =ᶠ[𝓝 y]
      (fun z ↦ weight N J (source_mesh_pos hJ) β₀ δ a m (configurationQuotient N z) /
        Real.sqrt (squareSum N J (source_mesh_pos hJ) β₀ δ (configurationQuotient N z))) := by
  have hc := (maximumOccupation_continuous N J (source_mesh_pos hJ)).comp
    (continuous_configurationQuotient N)
  filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hy] with z hz
  simp only [zeta, max_eq_left (squareSum_lower_bound hN hβ₀ hβ hδ hδ1 hJ
    (configurationQuotient N z) hz)]

private theorem zeta_lift_derivative_cost_at {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hJ : sourceResolution β₀ δ ≤ J) (y : Gradient N)
    (hy : δ < maximumOccupation N J (source_mesh_pos hJ) (configurationQuotient N y))
    (hw : ∀ a : MeshIndex J, ∀ m : Fin (sourceScaleCount β₀ δ),
      DifferentiableAt ℝ
        (fun z ↦ weight N J (source_mesh_pos hJ) β₀ δ a m (configurationQuotient N z)) y) :
    (∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ),
      ‖fderiv ℝ (fun z ↦ zeta N J (source_mesh_pos hJ) β₀ δ a m (configurationQuotient N z)) y‖ ^ 2) ≤
      32 * (sourceScaleCount β₀ δ : ℝ) ^ 2 * scaleGradientConstant β₀ δ ^ 2 * (J : ℝ) ^ 2 /
        (δ ^ 3 * N) := by
  let w : (MeshIndex J × Fin (sourceScaleCount β₀ δ)) → Gradient N → ℝ := fun p z ↦
    weight N J (source_mesh_pos hJ) β₀ δ p.1 p.2 (configurationQuotient N z)
  have hM : (0 : ℝ) < sourceScaleCount β₀ δ := by
    exact_mod_cast sourceScaleCount_pos hβ₀ hβ hδ hδ1
  have hSlow := squareSum_lower_bound hN hβ₀ hβ hδ hδ1 hJ (configurationQuotient N y) hy
  have hSp : 0 < squareSum N J (source_mesh_pos hJ) β₀ δ (configurationQuotient N y) :=
    (inv_pos.mpr hM).trans_le hSlow
  have hwp : 0 < ∑ p, w p y ^ 2 := by
    simpa only [w, Fintype.sum_prod_type, squareSum] using hSp
  have hn := normalized_fderiv_sum_sq_le w y (fun p ↦ hw p.1 p.2) hwp
  have hn' : (∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ),
      ‖fderiv ℝ (fun z ↦ weight N J (source_mesh_pos hJ) β₀ δ a m (configurationQuotient N z) /
        Real.sqrt (squareSum N J (source_mesh_pos hJ) β₀ δ (configurationQuotient N z))) y‖ ^ 2) ≤
      (4 / squareSum N J (source_mesh_pos hJ) β₀ δ (configurationQuotient N y)) *
        ∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ),
          ‖fderiv ℝ (fun z ↦ weight N J (source_mesh_pos hJ) β₀ δ a m (configurationQuotient N z)) y‖ ^ 2 := by
    simpa only [w, Fintype.sum_prod_type, squareSum] using hn
  have hcoef : 4 / squareSum N J (source_mesh_pos hJ) β₀ δ (configurationQuotient N y) ≤
      4 * sourceScaleCount β₀ δ := by
    have hMS : 1 ≤ squareSum N J (source_mesh_pos hJ) β₀ δ (configurationQuotient N y) *
        sourceScaleCount β₀ δ := by
      apply (div_le_iff₀ hM).mp
      simpa only [one_div] using hSlow
    apply (div_le_iff₀ hSp).2
    nlinarith
  calc
    _ = ∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ),
        ‖fderiv ℝ (fun z ↦ weight N J (source_mesh_pos hJ) β₀ δ a m (configurationQuotient N z) /
          Real.sqrt (squareSum N J (source_mesh_pos hJ) β₀ δ (configurationQuotient N z))) y‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro m _
      rw [(zeta_lift_eventuallyEq_on_heavy hN hβ₀ hβ hδ hδ1 hJ a m y hy).fderiv_eq]
    _ ≤ _ := hn'
    _ ≤ (4 * sourceScaleCount β₀ δ) *
        ∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ),
          ‖fderiv ℝ (fun z ↦ weight N J (source_mesh_pos hJ) β₀ δ a m (configurationQuotient N z)) y‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (Finset.sum_nonneg fun _ _ ↦
        Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    _ ≤ (4 * sourceScaleCount β₀ δ) *
        (8 * sourceScaleCount β₀ δ * scaleGradientConstant β₀ δ ^ 2 * (J : ℝ) ^ 2 /
          (δ ^ 3 * N)) := mul_le_mul_of_nonneg_left
      (sum_weight_derivative_sq_le hN hβ₀ hβ hδ hJ y) (by positivity)
    _ = _ := by ring

/-- A single Haar-full set supplies genuine derivatives of every actual
partition function at every representative in the physical Euclidean cover. -/
theorem ae_zeta_hasFDerivAt {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ)
    (hJ : sourceResolution β₀ δ ≤ J) :
    ∀ᵐ X ∂referenceMeasure N, ∀ a : MeshIndex J, ∀ m : Fin (sourceScaleCount β₀ δ),
      ∀ y : Gradient N, configurationQuotient N y = X →
      HasFDerivAt (fun z ↦ zeta N J (source_mesh_pos hJ) β₀ δ a m (configurationQuotient N z))
        (innerSL ℝ (descendedLiftGradient (zetaValue hN (source_mesh_pos hJ) hδ β₀ a m) X)) y := by
  apply ae_all_iff.2
  intro a
  apply ae_all_iff.2
  intro m
  obtain ⟨C, hC⟩ := zeta_physical_lipschitz hN hβ₀ hβ hδ hJ a m
  exact ae_hasFDerivAt_configurationLift_descendedGradient
    (zetaValue hN (source_mesh_pos hJ) hδ β₀ a m) hC.lift

/-- Exact source constant in the existing full physical gradient. All
almost-everywhere differentiability comes from the actual Lipschitz functions. -/
theorem ae_partition_gradient_sq_le {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hJ : sourceResolution β₀ δ ≤ J) :
    ∀ᵐ X ∂referenceMeasure N, δ < maximumOccupation N J (source_mesh_pos hJ) X →
      (∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ),
        ‖descendedLiftGradient (zetaValue hN (source_mesh_pos hJ) hδ β₀ a m) X‖ ^ 2) ≤
        32 * (sourceScaleCount β₀ δ : ℝ) ^ 2 * scaleGradientConstant β₀ δ ^ 2 * (J : ℝ) ^ 2 /
          (δ ^ 3 * N) := by
  have hw : ∀ᵐ X ∂referenceMeasure N, ∀ a : MeshIndex J, ∀ m : Fin (sourceScaleCount β₀ δ),
      ∀ y : Gradient N, configurationQuotient N y = X →
      DifferentiableAt ℝ
        (fun z ↦ weight N J (source_mesh_pos hJ) β₀ δ a m (configurationQuotient N z)) y := by
    apply ae_all_iff.2
    intro a
    apply ae_all_iff.2
    intro m
    obtain ⟨C, hC⟩ := weight_lift_lipschitz hN hβ₀ hβ hδ hJ a m.isLt
    exact ae_differentiableAt_configurationLift_all_representatives
      ⟨weight N J (source_mesh_pos hJ) β₀ δ a m, continuous_weight hN (source_mesh_pos hJ) hδ β₀ a m⟩ hC
  filter_upwards [hw] with X hX
  intro hheavy
  calc
    _ = ∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ),
        ‖fderiv ℝ (fun z ↦ zeta N J (source_mesh_pos hJ) β₀ δ a m (configurationQuotient N z))
          (configurationCenteredLift X)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro m _
      rw [norm_descendedLiftGradient_eq_differential]
      rfl
    _ ≤ _ := zeta_lift_derivative_cost_at hN hβ₀ hβ hδ hδ1 hJ (configurationCenteredLift X)
      (by simpa only [configurationQuotient_centeredLift] using hheavy)
      (fun a m ↦ hX a m (configurationCenteredLift X) (configurationQuotient_centeredLift X))

private theorem coordinate_gradient_eq_of_hasFDerivAt {N : ℕ} (f : C(Configuration N, ℝ))
    (y G : Gradient N)
    (hf : HasFDerivAt (fun z ↦ f (configurationQuotient N z)) (innerSL ℝ G) y) (i : Fin N) :
    coordinateOrdinaryGradient f i (configurationQuotient N y) =
      MovingPoleNumerators.sourceProjection i G := by
  have hd := MovingPoleDerivativeIdentification.hasFDerivAt_sourceBlock hf i
  have hd' : HasFDerivAt (fun z : PlanarSpace ↦
      f (Function.update (configurationQuotient N y) i (torusQuotient z)))
      (InnerProductSpace.toDual ℝ PlanarSpace
        (MovingPoleNumerators.sourceProjection i G))
      (MovingPoleNumerators.sourceProjection i y) := by
    simpa only [configurationQuotient_sourceVariation] using hd
  change torusOrdinaryGradient (fun z ↦ f (Function.update (configurationQuotient N y) i z))
    (torusQuotient (MovingPoleNumerators.sourceProjection i y)) = _
  rw [torusOrdinaryGradient_lift, rectangleOrdinaryGradient, hd'.fderiv]
  exact (InnerProductSpace.toDual ℝ PlanarSpace).symm_apply_apply _

/-- The same exact cost for the manuscript's unscaled ordinary coordinate
gradients, with the original particle number and no permutation assumption. -/
theorem ae_partition_coordinate_gradient_sq_le {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hJ : sourceResolution β₀ δ ≤ J) :
    ∀ᵐ X ∂referenceMeasure N, δ < maximumOccupation N J (source_mesh_pos hJ) X →
      (∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ), ∑ i : Fin N,
        ‖coordinateOrdinaryGradient (zeta N J (source_mesh_pos hJ) β₀ δ a m) i X‖ ^ 2) ≤
        32 * (sourceScaleCount β₀ δ : ℝ) ^ 2 * scaleGradientConstant β₀ δ ^ 2 * (J : ℝ) ^ 2 /
          (δ ^ 3 * N) := by
  filter_upwards [ae_partition_gradient_sq_le hN hβ₀ hβ hδ hδ1 hJ,
    ae_zeta_hasFDerivAt hN hβ₀ hβ hδ hJ] with X hX hd
  intro hheavy
  have he (a : MeshIndex J) (m : Fin (sourceScaleCount β₀ δ)) :
      (∑ i : Fin N, ‖coordinateOrdinaryGradient (zeta N J (source_mesh_pos hJ) β₀ δ a m) i X‖ ^ 2) =
        ‖descendedLiftGradient (zetaValue hN (source_mesh_pos hJ) hδ β₀ a m) X‖ ^ 2 := by
    rw [gradient_norm_sq]
    apply Finset.sum_congr rfl
    intro i _
    have hi := coordinate_gradient_eq_of_hasFDerivAt (zetaValue hN (source_mesh_pos hJ) hδ β₀ a m)
      (configurationCenteredLift X) _
      (hd a m (configurationCenteredLift X) (configurationQuotient_centeredLift X)) i
    rw [configurationQuotient_centeredLift] at hi
    change coordinateOrdinaryGradient (zeta N J (source_mesh_pos hJ) β₀ δ a m) i X = _ at hi
    rw [hi, EuclideanSpace.real_norm_sq_eq]
    rfl
  simpa only [he] using hX hheavy

theorem ae_partition_gradient_sq_le_gibbs {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hJ : sourceResolution β₀ δ ≤ J) (g : Torus → ℝ) (β : ℝ) :
    ∀ᵐ X ∂gibbsMeasure g N β, δ < maximumOccupation N J (source_mesh_pos hJ) X →
      (∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ),
        ‖descendedLiftGradient (zetaValue hN (source_mesh_pos hJ) hδ β₀ a m) X‖ ^ 2) ≤
        32 * (sourceScaleCount β₀ δ : ℝ) ^ 2 * scaleGradientConstant β₀ δ ^ 2 * (J : ℝ) ^ 2 /
          (δ ^ 3 * N) :=
  (gibbsMeasure_absolutelyContinuous g N β).ae_le
    (ae_partition_gradient_sq_le hN hβ₀ hβ hδ hδ1 hJ)

theorem ae_partition_coordinate_gradient_sq_le_gibbs {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hJ : sourceResolution β₀ δ ≤ J) (g : Torus → ℝ) (β : ℝ) :
    ∀ᵐ X ∂gibbsMeasure g N β, δ < maximumOccupation N J (source_mesh_pos hJ) X →
      (∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ), ∑ i : Fin N,
        ‖coordinateOrdinaryGradient (zeta N J (source_mesh_pos hJ) β₀ δ a m) i X‖ ^ 2) ≤
        32 * (sourceScaleCount β₀ δ : ℝ) ^ 2 * scaleGradientConstant β₀ δ ^ 2 * (J : ℝ) ^ 2 /
          (δ ^ 3 * N) :=
  (gibbsMeasure_absolutelyContinuous g N β).ae_le
    (ae_partition_coordinate_gradient_sq_le hN hβ₀ hβ hδ hδ1 hJ)

/-- Actual hard shell count on the source open set. The count includes
annulus boundaries with exactly the conventions of the collective test. -/
theorem openSet_shellCount_lt {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ)
    (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) (m : ℕ) {X : Configuration N}
    (hX : X ∈ separatedOpenSet N J (source_mesh_pos hJ) β₀ δ a m) :
    (CollectiveSecondMoment.shellCount (cellCenter J a) (scaleRadius J (separationRadius β₀) m)
      (separationRadius β₀) X : ℝ) <
      2 * (separationConstant β₀ * (4 - β₀)) *
        mass (cellCenter J a) (scaleRadius J (separationRadius β₀) m) X :=
  (CollectiveSecondMoment.shellCount_le_shellMass (source_radius_pos hJ m)
    (by linarith [separationRadius_ge_eight β₀]) (cellCenter J a) X).trans_lt
      (separatedOpenSet_conditions hN hβ₀ hβ hδ hJ a m hX).2

end PeriodicAttractiveLogGas.HeavyPartition
