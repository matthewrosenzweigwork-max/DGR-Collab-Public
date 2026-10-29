import LeanResearch.PeriodicAttractiveLogGas.Periodization
import Mathlib.Analysis.Normed.Group.AddCircle

/-! The Euclidean quotient distance on the square torus. The existing topology
and default metric on `Torus` are left unchanged. The norm defined here is the
`L²` combination of the two circle norms, with an attained minimum over all
ordinary Euclidean lifts. The centered section takes values in `(-1/2, 1/2]²`.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace PeriodicAttractiveLogGas

/-- The canonical centered Euclidean lift, including the positive endpoint
and excluding the negative endpoint in each coordinate. -/
def centeredLift (z : Torus) : PlanarSpace :=
  WithLp.toLp 2 (fun j ↦
    (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) (z j) : ℝ))

@[simp] theorem centeredLift_apply (z : Torus) (j : Fin 2) :
    centeredLift z j = (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) (z j) : ℝ) := rfl

@[simp] theorem torusQuotient_centeredLift (z : Torus) :
    torusQuotient (centeredLift z) = z := by
  ext j
  exact AddCircle.coe_equivIoc

theorem centeredLift_coordinate_mem (z : Torus) (j : Fin 2) :
    centeredLift z j ∈ Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
  have h : -(1 / 2 : ℝ) < centeredLift z j ∧
      centeredLift z j ≤ -(1 / 2 : ℝ) + 1 :=
    (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) (z j)).property
  exact ⟨h.1, by linarith [h.2]⟩

theorem centeredLift_abs_le_half (z : Torus) (j : Fin 2) :
    |centeredLift z j| ≤ (1 / 2 : ℝ) :=
  abs_le.mpr ⟨(centeredLift_coordinate_mem z j).1.le,
    (centeredLift_coordinate_mem z j).2⟩

theorem centeredLift_mem_fundamentalBox (z : Torus) :
    centeredLift z ∈ euclideanFundamentalBox (centeredBoxAnchor 0) := by
  intro j _
  change 0 - 1 / 2 < centeredLift z j ∧ centeredLift z j ≤ 0 - 1 / 2 + 1
  obtain ⟨hl, hu⟩ := centeredLift_coordinate_mem z j
  constructor <;> linarith

theorem measurable_centeredLift : Measurable centeredLift := by
  have hm : Measurable (fun z : Torus ↦ fun j : Fin 2 ↦
      (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) (z j) : ℝ)) := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIoc (1 : ℝ) (-(1 / 2 : ℝ))).measurable.comp
        (measurable_pi_apply j))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).measurable.comp hm

theorem centeredLift_torusQuotient_of_mem_box {x : PlanarSpace}
    (hx : x ∈ euclideanFundamentalBox (centeredBoxAnchor 0)) :
    centeredLift (torusQuotient x) = x :=
  injOn_torusQuotient_box (centeredBoxAnchor 0)
    (centeredLift_mem_fundamentalBox _) hx (torusQuotient_centeredLift _)

/-- The source norm on the square torus, using Euclidean combination of the
individual circle quotient distances to zero. -/
def torusEuclideanNorm (z : Torus) : ℝ :=
  Real.sqrt (∑ j : Fin 2, ‖z j‖ ^ 2)

theorem torusEuclideanNorm_eq_sqrt_sum_dist_sq (z : Torus) :
    torusEuclideanNorm z = Real.sqrt (∑ j : Fin 2, dist (z j) 0 ^ 2) := by
  simp only [torusEuclideanNorm, dist_zero_right]

theorem torusEuclideanNorm_eq_piLp_norm (z : Torus) :
    torusEuclideanNorm z = ‖(WithLp.toLp 2 z : PiLp 2 (fun _ : Fin 2 ↦ UnitAddCircle))‖ :=
  (PiLp.norm_eq_of_L2 _).symm

theorem torusEuclideanNorm_nonneg (z : Torus) : 0 ≤ torusEuclideanNorm z :=
  Real.sqrt_nonneg _

@[simp] theorem torusEuclideanNorm_eq_zero_iff (z : Torus) :
    torusEuclideanNorm z = 0 ↔ z = 0 := by
  rw [torusEuclideanNorm_eq_piLp_norm, norm_eq_zero, WithLp.toLp_eq_zero]

@[simp] theorem torusEuclideanNorm_zero : torusEuclideanNorm (0 : Torus) = 0 :=
  (torusEuclideanNorm_eq_zero_iff 0).mpr rfl

theorem torusEuclideanNorm_pos_iff (z : Torus) :
    0 < torusEuclideanNorm z ↔ z ≠ 0 := by
  constructor
  · intro hz he
    subst z
    simp only [torusEuclideanNorm_zero, lt_self_iff_false] at hz
  · intro hz
    apply lt_of_le_of_ne (torusEuclideanNorm_nonneg z)
    intro he
    exact hz ((torusEuclideanNorm_eq_zero_iff z).mp he.symm)

@[simp] theorem torusEuclideanNorm_neg (z : Torus) :
    torusEuclideanNorm (-z) = torusEuclideanNorm z := by
  simp only [torusEuclideanNorm_eq_piLp_norm, WithLp.toLp_neg, norm_neg]

theorem torusEuclideanNorm_add_le (z w : Torus) :
    torusEuclideanNorm (z + w) ≤ torusEuclideanNorm z + torusEuclideanNorm w := by
  simpa only [torusEuclideanNorm_eq_piLp_norm, WithLp.toLp_add] using
    (norm_add_le (WithLp.toLp 2 z : PiLp 2 (fun _ : Fin 2 ↦ UnitAddCircle))
      (WithLp.toLp 2 w))

theorem continuous_torusEuclideanNorm : Continuous torusEuclideanNorm := by
  exact (continuous_finsetSum Finset.univ
    (fun j _ ↦ ((continuous_apply j).norm.pow 2))).sqrt

theorem measurable_torusEuclideanNorm : Measurable torusEuclideanNorm :=
  continuous_torusEuclideanNorm.measurable

theorem norm_centeredLift_apply (z : Torus) (j : Fin 2) :
    ‖centeredLift z j‖ = ‖z j‖ := by
  have h : ‖((centeredLift z j : ℝ) : UnitAddCircle)‖ = |centeredLift z j| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).mpr
      (by simpa using centeredLift_abs_le_half z j)
  have hq : ((centeredLift z j : ℝ) : UnitAddCircle) = z j :=
    congrFun (torusQuotient_centeredLift z) j
  rw [hq] at h
  simpa only [Real.norm_eq_abs] using h.symm

theorem norm_centeredLift (z : Torus) : ‖centeredLift z‖ = torusEuclideanNorm z := by
  simp only [EuclideanSpace.norm_eq, norm_centeredLift_apply, torusEuclideanNorm]

@[simp] theorem centeredLift_zero : centeredLift (0 : Torus) = 0 := by
  apply norm_eq_zero.mp
  rw [norm_centeredLift, torusEuclideanNorm_zero]

@[simp] theorem centeredLift_eq_zero_iff (z : Torus) : centeredLift z = 0 ↔ z = 0 := by
  rw [← norm_eq_zero, norm_centeredLift, torusEuclideanNorm_eq_zero_iff]

/-- Projection cannot increase the ordinary Euclidean norm. -/
theorem torusEuclideanNorm_quotient_le (x : PlanarSpace) :
    torusEuclideanNorm (torusQuotient x) ≤ ‖x‖ := by
  rw [torusEuclideanNorm, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro j _
  have h : ‖(x j : UnitAddCircle)‖ ≤ ‖x j‖ :=
    QuotientAddGroup.norm_mk_le_norm
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem torusEuclideanNorm_le_norm_of_lift {z : Torus} {x : PlanarSpace}
    (hx : torusQuotient x = z) : torusEuclideanNorm z ≤ ‖x‖ := by
  simpa only [hx] using torusEuclideanNorm_quotient_le x

theorem norm_centeredLift_le_norm_of_lift {z : Torus} {x : PlanarSpace}
    (hx : torusQuotient x = z) : ‖centeredLift z‖ ≤ ‖x‖ := by
  rw [norm_centeredLift]
  exact torusEuclideanNorm_le_norm_of_lift hx

/-- The quotient norm is an attained minimum, with no convergence or
compactness premise hidden in the definition. -/
theorem torusEuclideanNorm_isLeast (z : Torus) :
    IsLeast {r : ℝ | ∃ x : PlanarSpace, torusQuotient x = z ∧ ‖x‖ = r}
      (torusEuclideanNorm z) := by
  refine ⟨⟨centeredLift z, torusQuotient_centeredLift z, norm_centeredLift z⟩, ?_⟩
  rintro r ⟨x, hx, rfl⟩
  exact torusEuclideanNorm_le_norm_of_lift hx

/-- In ordinary coordinates the same minimum is the minimum over the integer
lattice translates. Both signs of translation occur because the index is `ℤ²`. -/
theorem torusEuclideanNorm_quotient_isLeast_lattice (x : PlanarSpace) :
    IsLeast (Set.range (fun k : Frequency ↦ ‖x + frequencyVector k‖))
      (torusEuclideanNorm (torusQuotient x)) := by
  obtain ⟨k, hk⟩ := exists_frequencyVector_of_torusQuotient_eq
    (torusQuotient_centeredLift (torusQuotient x)).symm
  refine ⟨⟨k, ?_⟩, ?_⟩
  · change ‖x + frequencyVector k‖ = torusEuclideanNorm (torusQuotient x)
    rw [← hk, norm_centeredLift]
  · rintro r ⟨m, rfl⟩
    exact torusEuclideanNorm_le_norm_of_lift (torusQuotient_add_frequencyVector x m)

theorem mem_centeredOpenBox_of_norm_lt_half {x : PlanarSpace} (hx : ‖x‖ < (1 / 2 : ℝ)) :
    x ∈ euclideanOpenBox (centeredBoxAnchor 0) := by
  intro j _
  have hj : |x j| < (1 / 2 : ℝ) :=
    lt_of_le_of_lt (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j) hx
  obtain ⟨hl, hu⟩ := abs_lt.mp hj
  change 0 - 1 / 2 < x j ∧ x j < 0 - 1 / 2 + 1
  constructor <;> linarith

theorem centeredLift_torusQuotient_of_norm_lt_half {x : PlanarSpace}
    (hx : ‖x‖ < (1 / 2 : ℝ)) : centeredLift (torusQuotient x) = x :=
  centeredLift_torusQuotient_of_mem_box
    (euclideanOpenBox_subset_fundamentalBox _ (mem_centeredOpenBox_of_norm_lt_half hx))

/-- The Euclidean chart is exact below the injectivity radius `1/2`. -/
theorem torusEuclideanNorm_quotient_eq_of_norm_lt_half {x : PlanarSpace}
    (hx : ‖x‖ < (1 / 2 : ℝ)) : torusEuclideanNorm (torusQuotient x) = ‖x‖ := by
  rw [← norm_centeredLift, centeredLift_torusQuotient_of_norm_lt_half hx]

/-- The norm identity also holds at the boundary, although the selected lift
need not equal the original vector at a negative coordinate endpoint. -/
theorem torusEuclideanNorm_quotient_eq_of_norm_le_half {x : PlanarSpace}
    (hx : ‖x‖ ≤ (1 / 2 : ℝ)) : torusEuclideanNorm (torusQuotient x) = ‖x‖ := by
  rw [torusEuclideanNorm, EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hj : |x j| ≤ (1 / 2 : ℝ) :=
    le_trans (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j) hx
  have h : ‖(x j : UnitAddCircle)‖ = |x j| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).mpr (by simpa using hj)
  change ‖(x j : UnitAddCircle)‖ ^ 2 = ‖x j‖ ^ 2
  rw [h, Real.norm_eq_abs]

theorem torusEuclideanNorm_le_sqrt_half (z : Torus) :
    torusEuclideanNorm z ≤ Real.sqrt (1 / 2 : ℝ) := by
  unfold torusEuclideanNorm
  apply Real.sqrt_le_sqrt
  have h (j : Fin 2) : ‖z j‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _)
    simpa using (AddCircle.norm_le_half_period (1 : ℝ) (x := z j) (by norm_num))
  rw [Fin.sum_univ_two]
  nlinarith [h 0, h 1]

theorem torusEuclideanNorm_le_one_div_sqrt_two (z : Torus) :
    torusEuclideanNorm z ≤ 1 / Real.sqrt 2 := by
  calc
    torusEuclideanNorm z ≤ Real.sqrt (1 / 2 : ℝ) := torusEuclideanNorm_le_sqrt_half z
    _ = 1 / Real.sqrt 2 := by rw [Real.sqrt_div zero_le_one, Real.sqrt_one]

@[simp] theorem torusQuotient_add (x y : PlanarSpace) :
    torusQuotient (x + y) = torusQuotient x + torusQuotient y := by
  ext j
  rfl

@[simp] theorem torusQuotient_sub (x y : PlanarSpace) :
    torusQuotient (x - y) = torusQuotient x - torusQuotient y := by
  ext j
  rfl

/-- The Euclidean quotient distance; no global metric instance is replaced. -/
def torusEuclideanDist (z w : Torus) : ℝ := torusEuclideanNorm (z - w)

theorem torusEuclideanDist_eq_sqrt_sum_dist_sq (z w : Torus) :
    torusEuclideanDist z w = Real.sqrt (∑ j : Fin 2, dist (z j) (w j) ^ 2) := by
  simp only [torusEuclideanDist, torusEuclideanNorm, Pi.sub_apply, dist_eq_norm]

theorem torusEuclideanDist_eq_piLp_dist (z w : Torus) :
    torusEuclideanDist z w =
      dist (WithLp.toLp 2 z : PiLp 2 (fun _ : Fin 2 ↦ UnitAddCircle)) (WithLp.toLp 2 w) := by
  simp only [torusEuclideanDist, torusEuclideanNorm_eq_piLp_norm,
    WithLp.toLp_sub, dist_eq_norm]

theorem torusEuclideanDist_nonneg (z w : Torus) : 0 ≤ torusEuclideanDist z w :=
  torusEuclideanNorm_nonneg _

@[simp] theorem torusEuclideanDist_eq_zero_iff (z w : Torus) :
    torusEuclideanDist z w = 0 ↔ z = w := by
  simp only [torusEuclideanDist, torusEuclideanNorm_eq_zero_iff, sub_eq_zero]

@[simp] theorem torusEuclideanDist_self (z : Torus) : torusEuclideanDist z z = 0 :=
  (torusEuclideanDist_eq_zero_iff z z).mpr rfl

@[simp] theorem torusEuclideanDist_zero (z : Torus) :
    torusEuclideanDist z 0 = torusEuclideanNorm z := by
  simp only [torusEuclideanDist, sub_zero]

theorem torusEuclideanDist_comm (z w : Torus) : torusEuclideanDist z w = torusEuclideanDist w z := by
  simp only [torusEuclideanDist_eq_piLp_dist]
  exact dist_comm _ _

theorem torusEuclideanDist_triangle (x y z : Torus) :
    torusEuclideanDist x z ≤ torusEuclideanDist x y + torusEuclideanDist y z := by
  simp only [torusEuclideanDist_eq_piLp_dist]
  exact dist_triangle _ _ _

theorem continuous_torusEuclideanDist :
    Continuous (fun p : Torus × Torus ↦ torusEuclideanDist p.1 p.2) :=
  continuous_torusEuclideanNorm.comp (continuous_fst.sub continuous_snd)

theorem torusEuclideanDist_le_sqrt_half (z w : Torus) :
    torusEuclideanDist z w ≤ Real.sqrt (1 / 2 : ℝ) :=
  torusEuclideanNorm_le_sqrt_half _

theorem torusEuclideanDist_quotient_le (x y : PlanarSpace) :
    torusEuclideanDist (torusQuotient x) (torusQuotient y) ≤ dist x y := by
  rw [torusEuclideanDist, ← torusQuotient_sub, dist_eq_norm]
  exact torusEuclideanNorm_quotient_le (x - y)

/-- The distance is the attained minimum of the Euclidean distances between
all pairs of lifts of its two arguments. -/
theorem torusEuclideanDist_isLeast (z w : Torus) :
    IsLeast {r : ℝ | ∃ x y : PlanarSpace,
      torusQuotient x = z ∧ torusQuotient y = w ∧ dist x y = r}
      (torusEuclideanDist z w) := by
  refine ⟨⟨centeredLift (z - w) + centeredLift w, centeredLift w, ?_,
    torusQuotient_centeredLift w, ?_⟩, ?_⟩
  · rw [torusQuotient_add, torusQuotient_centeredLift, torusQuotient_centeredLift,
      sub_add_cancel]
  · rw [dist_eq_norm, add_sub_cancel_right, norm_centeredLift]
    rfl
  · rintro r ⟨x, y, hx, hy, rfl⟩
    simpa only [hx, hy] using torusEuclideanDist_quotient_le x y

theorem torusEuclideanDist_quotient_eq_of_dist_lt_half {x y : PlanarSpace}
    (hxy : dist x y < (1 / 2 : ℝ)) :
    torusEuclideanDist (torusQuotient x) (torusQuotient y) = dist x y := by
  rw [torusEuclideanDist, ← torusQuotient_sub, dist_eq_norm]
  exact torusEuclideanNorm_quotient_eq_of_norm_lt_half (by simpa only [dist_eq_norm] using hxy)

theorem torusEuclideanDist_quotient_isLeast_lattice (x y : PlanarSpace) :
    IsLeast (Set.range (fun k : Frequency ↦ ‖x - y + frequencyVector k‖))
      (torusEuclideanDist (torusQuotient x) (torusQuotient y)) := by
  rw [torusEuclideanDist, ← torusQuotient_sub]
  exact torusEuclideanNorm_quotient_isLeast_lattice (x - y)

end PeriodicAttractiveLogGas
