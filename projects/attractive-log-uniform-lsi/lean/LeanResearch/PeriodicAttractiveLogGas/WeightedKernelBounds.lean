import LeanResearch.PeriodicAttractiveLogGas.DyadicKernelBounds

/-! Actual row and weighted-column bounds for the cube potential.
The coefficient is the source 4^d times the diameter. Euclidean distance,
Lebesgue measure and the original product weight retain their normalizations. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology BigOperators
namespace PeriodicAttractiveLogGas.WeightedKernelBounds
open PhysicalCubes WeightedCubeBounds DyadicKernelBounds
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma convex_cube (c : EuclideanSpace ℝ ι) (ℓ : ℝ) : Convex ℝ (cube c ℓ) := by
  intro x hx y hy a b ha hb hab j hj
  change c j - ℓ / 2 ≤ a * x j + b * y j ∧ a * x j + b * y j ≤ c j + ℓ / 2
  have hc : Convex ℝ (Icc (c j - ℓ / 2) (c j + ℓ / 2)) := convex_Icc _ _
  exact hc (hx j hj) (hy j hj) ha hb hab

lemma cube_subset_ball_at_point (c : EuclideanSpace ℝ ι) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    {x : EuclideanSpace ℝ ι} (hx : x ∈ cube c ℓ) :
    cube c ℓ ⊆ closedBall x (Real.sqrt (Fintype.card ι) * ℓ) := by
  intro y hy
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ Fintype.card ι by positivity)
  have hn (z : EuclideanSpace ℝ ι) (hz : z ∈ cube c ℓ) :
      ‖z - c‖ ≤ Real.sqrt (Fintype.card ι) * (ℓ / 2) := by
    have hh := norm_sub_sq_le c z hℓ hz
    have ht : (Real.sqrt (Fintype.card ι) * (ℓ / 2)) ^ 2 =
        (Fintype.card ι : ℝ) * (ℓ / 2) ^ 2 := by rw [mul_pow, hs]
    have hpos : 0 ≤ Real.sqrt (Fintype.card ι) * (ℓ / 2) := by positivity
    nlinarith only [hh, ht, hpos, norm_nonneg (z - c)]
  have htri : ‖y - x‖ ≤ ‖y - c‖ + ‖x - c‖ := by
    simpa only [sub_sub_sub_cancel_right] using norm_sub_le (y - c) (x - c)
  change dist y x ≤ _
  rw [dist_eq_norm]
  linarith only [htri, hn y hy, hn x hx]

lemma unweighted_ball (x : EuclideanSpace ℝ ι) {D : ℝ} (hD : 0 < D) :
    (∫⁻ y in closedBall x D, ‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ))) ≤
      ENNReal.ofReal ((4 : ℝ) ^ Fintype.card ι * D) := by
  have hb (r : ℝ) (hr : 0 < r) :
      volume (closedBall x r) ≤ ENNReal.ofReal ((2 : ℝ) ^ Fintype.card ι * r ^ Fintype.card ι) := by
    calc
      _ ≤ volume (cube x (2 * r)) := measure_mono (closedBall_subset_cube x r)
      _ = _ := by rw [cube_volume x (by positivity), mul_pow]
  have hh := kernel_integral_le_of_ball_growth (μ := volume) Fintype.card_pos x
    (by positivity : 0 ≤ (2 : ℝ) ^ Fintype.card ι) hD (measure_singleton x) hb
  have he : (2 : ℝ) ^ Fintype.card ι * 2 ^ Fintype.card ι = 4 ^ Fintype.card ι := by
    rw [← mul_pow]
    norm_num
  simpa only [he] using hh

lemma weighted_ball {w : EuclideanSpace ℝ ι → ℝ} {A : ℝ} {Z : Set (EuclideanSpace ℝ ι)}
    (h : Bounds w A Z) (x : EuclideanSpace ℝ ι) (hx : x ∉ Z) {D : ℝ} (hD : 0 < D) :
    (∫⁻ y in closedBall x D, ‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ)) ∂weightedMeasure w) ≤
      ENNReal.ofReal ((4 : ℝ) ^ Fintype.card ι * D * A * w x) := by
  have hA : 0 ≤ A := zero_le_one.trans h.constant_ge_one
  have hb (r : ℝ) (hr : 0 < r) :
      weightedMeasure w (closedBall x r) ≤
        ENNReal.ofReal (((2 : ℝ) ^ Fintype.card ι * A * w x) * r ^ Fintype.card ι) := by
    apply (h.measure_closedBall_le x hr (mem_closedBall_self hr.le) hx).trans_eq
    congr 1
    rw [mul_pow]
    ring
  have hnull : weightedMeasure w {x} = 0 :=
    weightedMeasure_absolutelyContinuous w (measure_singleton x)
  have hh := kernel_integral_le_of_ball_growth Fintype.card_pos x
    (mul_nonneg (mul_nonneg (by positivity) hA) (h.nonneg x)) hD hnull hb
  have he : (2 : ℝ) ^ Fintype.card ι * 2 ^ Fintype.card ι = 4 ^ Fintype.card ι := by
    rw [← mul_pow]
    norm_num
  apply hh.trans_eq
  congr 1
  calc
    _ = ((2 : ℝ) ^ Fintype.card ι * 2 ^ Fintype.card ι) * D * A * w x := by ring
    _ = _ := by rw [he]

lemma unweighted_cube (c : EuclideanSpace ℝ ι) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {x : EuclideanSpace ℝ ι} (hx : x ∈ cube c ℓ) :
    (∫⁻ y in cube c ℓ, ‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ))) ≤
      ENNReal.ofReal ((4 : ℝ) ^ Fintype.card ι * (Real.sqrt (Fintype.card ι) * ℓ)) :=
  (lintegral_mono_set (cube_subset_ball_at_point c hℓ.le hx)).trans
    (unweighted_ball x (mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos (α := ι))) hℓ))

lemma weighted_cube {w : EuclideanSpace ℝ ι → ℝ} {A : ℝ} {Z : Set (EuclideanSpace ℝ ι)}
    (h : Bounds w A Z) (c : EuclideanSpace ℝ ι) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {x : EuclideanSpace ℝ ι} (hx : x ∈ cube c ℓ) (hxZ : x ∉ Z) :
    (∫⁻ y in cube c ℓ, ‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ)) ∂weightedMeasure w) ≤
      ENNReal.ofReal ((4 : ℝ) ^ Fintype.card ι * (Real.sqrt (Fintype.card ι) * ℓ) * A * w x) :=
  (lintegral_mono_set (cube_subset_ball_at_point c hℓ.le hx)).trans
    (weighted_ball h x hxZ (mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos (α := ι))) hℓ))

end PeriodicAttractiveLogGas.WeightedKernelBounds
