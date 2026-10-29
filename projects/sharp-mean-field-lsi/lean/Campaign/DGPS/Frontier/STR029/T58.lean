import DGPS.Frontier.STR029.T56
import DGPS.Frontier.STR029.T57

/-!
# STR029.58: Weighted remainder retaining the amplitude factor

Task id: STR029.58 (node STR029). Title: Weighted remainder retaining the amplitude factor.
Prerequisites: STR029.56 (`Fred_STR02956`, its smoothness, its vanishing on the slice `a = b = 0`
and the vanishing of its `(a, b)`-derivative there), STR029.57 (the graph `ψ`, the open sets `U`,
`V` and the weight-four polynomial `poly19_STR02957`), STR029.54 and STR029.55 (smoothness of the
entropy ingredients `Z`, `rho`, `e0`, `e1`).

Statement formalized. Let `U`, `V`, `ψ` be the data of STR029.57: open sets `U ∋ 0` in the
parameter space `Par_STR02916 = ℝ × ℝ × ℝ × ℝ` (sup norm) and `V ∋ 0` in the carrier `E`, and a
smooth graph `ψ : Par → E` on `U` with `ψ 0 = 0`, `ψ p ∈ V` and
`Rpar p w = 0 ↔ w = ψ p` for `p ∈ U`, `w ∈ V`. Let `F̂ (a, b, h, γ) = Fred ψ (a, b) (h, γ)` be the
reduced functional viewed as a function of the four parameters. There is `r > 0` such that the
closed coordinate box `box r = closedBall 0 r` (convex and compact) lies in `U`; there is a finite
`M ≥ 0` bounding the operator norms `‖D^k F̂ (p)‖` for all `p` in the box and all `k ≤ 5`; and for
every such bound `M` and every `(a, b, h, γ)` in the box
`|F̂ - poly19| ≤ M R0² ((|h| + R0)³ + |γ| (|h| + R0) + γ²)` with `R0 = √(a² + b²)`.

Provides (every declaration is in the namespace `DGPS.Frontier.STR029`):

* `DGPS.Frontier.STR029.str029_58_weighted_remainder_retaining_amplitude_factor`: the main
  statement described above.
* `DGPS.Frontier.STR029.str029_58_weighted_remainder_retaining_amplitude_factor_box_convex`: the
  coordinate box is convex.
* `DGPS.Frontier.STR029.str029_58_weighted_remainder_retaining_amplitude_factor_box_compact`: the
  coordinate box is compact.
* `DGPS.Frontier.STR029.str029_58_weighted_remainder_retaining_amplitude_factor_mem_box`:
  membership in the box is the four coordinatewise bounds `|a|, |b|, |h|, |γ| ≤ r`.
* `DGPS.Frontier.STR029.str029_58_weighted_remainder_retaining_amplitude_factor_derivative_bound`:
  for a smooth graph on an open set containing the box, the iterated derivatives of `F̂` of order
  at most five are bounded by a single constant on the box.

Supporting declarations (all carry the suffix `_STR02958`):

* `mvt01_STR02958`, `taylor3_crude_STR02958`, `taylor2_poly_STR02958`: one-variable mean value and
  Taylor estimates on `[0, 1]`.
* `eq_zero_of_le_mul_STR02958`, `coeff_zero_STR02958`: coefficients of a polynomial that is
  `O(l⁵)` as `l → 0+` vanish.
* `d2_STR02958`, `d3_STR02958`, `d4_STR02958`, `d5_STR02958`: the iterated derivative of order
  two to five evaluated on a list of vectors (`iteratedFDeriv ℝ k f x ![...]`);
  `abs_d3_STR02958`, `abs_d4_STR02958`, `abs_d5_STR02958` bound their absolute values by the
  operator norm of the iterated derivative; `d2_smul0_STR02958`, `d2_smul1_STR02958`,
  `d3_smul0_STR02958`, ..., `d4_smul3_STR02958`, `d3_add0_STR02958`, `d4_add0_STR02958`,
  `d4_add1_STR02958` are the slotwise homogeneity and additivity rules.
* `diffAt_STR02958`, `diffAt_iter_STR02958`, `hasDerivAt_ray_STR02958`, `hasDerivAt_iter_STR02958`,
  `hasDerivAt_fderiv_STR02958`, `hasDerivAt_d2_STR02958`, `hasDerivAt_d3_STR02958`,
  `hasDerivAt_d4_STR02958`: differentiability and derivatives along rays; `rem_ray_STR02958`,
  `rem_v_STR02958`, `rem_STR02958`: second-derivative remainder estimates.
* `Q2_STR02958`, `Q3_STR02958`, `Q4_STR02958` and the homogeneity lemmas `Q2_smul_STR02958`,
  `Q3_smul_STR02958`, `Q4_smul_STR02958`: the Taylor jets in the directions `u`, `h e3`, `γ e4`.
* `taylor_rem_STR02958`, `taylor_rem'_STR02958`: the pointwise Taylor remainder with the amplitude
  factor `‖u‖²`; `jet_coeff_STR02958`, `jet_coeff'_STR02958`: identification of the jet from a
  scaled bound.
* `JJ_STR02958`, `Fhat_STR02958` and their smoothness, slice and ray-derivative lemmas.
* `box_STR02958` and its basic properties; the directions `e3_STR02958`, `e4_STR02958`,
  `uu_STR02958`.
* `slice_zero_STR02958`, `jet_vanish_STR02958`, `qsum_scaled_STR02958`, `qsum_eq_STR02958`,
  `remainder_core_STR02958`, `remainder_all_STR02958`, `exists_bound_STR02958`: the steps of the
  proof of the main statement.

R5 notes:

1. Quantifier prefix. The statement re-states the data `U`, `V`, `ψ` of STR029.57 in its own
   existential prefix (open sets, smoothness, `ψ 0 = 0`, graph characterization), and obtains them
   from `str029_57_weighted_fourth_jet_reduced_functional`. Because `ψ p` is the unique zero of
   `Rpar p` in `V`, the graph is determined by `(U, V)`; the statement does not claim any further
   relation to the particular triple produced by STR029.57.
2. Box. The "sufficiently small closed convex coordinate box inside the smoothness neighborhood" is
   `box r = Metric.closedBall 0 r` in the sup norm of `ℝ × ℝ × ℝ × ℝ`, with `r > 0` and
   `box r ⊆ U`. Its convexity and compactness are separate public lemmas.
3. The constant. "A finite constant controlled by the operator norms of derivatives of `F` through
   order five on that box" is read as follows. A bound `M ≥ 0` for `‖iteratedFDeriv ℝ k F̂ p‖`,
   for all `p` in the box and all `k ≤ 5`, exists, and for any such `M` the constant `C` of the
   bound on `𝓔 = F - poly19` can be taken to be exactly `M`. The proof uses only `k = 4` and
   `k = 5`; the hypothesis keeps all orders through five, as in the brief. The norm is the operator
   norm of the continuous multilinear map `iteratedFDeriv ℝ k F̂ p` for the sup norm on
   `ℝ × ℝ × ℝ × ℝ`; derivatives are taken in all four variables, not only in `(a, b)`.
4. The function `F`. The remainder is taken for `F̂ p = Fred_STR02956 ψ (p.1, p.2.1) (p.2.2.1, p.2.2.2)`,
   the reduced functional of STR029.56 (the common optimizer-chart functional, not the Euler range
   map and not the variational range map), and the leading part is `poly19_STR02957 a b h γ`, so
   `𝓔 = F̂ - poly19`.
5. The amplitude. `R0_STR02918 a b = √(a² + b²)` is the Euclidean amplitude of STR029.18. The proof
   works with the sup norm of the direction `(a, b, 0, 0)`, which is at most `R0`; the final bound
   is stated with `R0` exactly as in the brief.
6. The slice. The vanishing of the graph on the slice `a = b = 0` is not an extra hypothesis. It is
   derived inside the proof from the graph characterization together with the equilibrium of
   `Rpar_STR02916` on the slice.
7. The jet. The vanishing of the order two and three weighted jet terms and the value of the order
   four term are derived from the uniform scaled bound of STR029.57 (applied to a singleton
   compact set) and the homogeneity of the Taylor jets; they are not assumed.
8. The case `h = 0`. For `h ≠ 0` the bound comes from the pointwise Taylor estimate and the
   identification of the jet with `poly19`; at `h = 0` it follows by continuity of both sides in
   `h` along `h → 0` with `h ≠ 0`, inside the box.
9. Derivatives of order two to five. Throughout the argument they are handled as evaluations of
   `iteratedFDeriv ℝ k` (continuous multilinear maps) on vectors, not as nested continuous linear
   maps; the operator norm is that of `iteratedFDeriv ℝ k`, so no hypothesis on nested maps
   enters and the constant in the conclusion is exactly the bound `M` of the statement.
-/

open scoped ContDiff
open DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.STR029

/-! ### One-variable estimates -/

/-- Mean value estimate on `[0, 1]` for a function with bounded derivative. -/
theorem mvt01_STR02958 (g g' : ℝ → ℝ) (C : ℝ)
    (hg : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (g' s) s)
    (hC : ∀ s ∈ Set.Icc (0 : ℝ) 1, |g' s| ≤ C) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |g t - g 0| ≤ C := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 h0)
  have key := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := g) (f' := g') (C := C) (fun s hs => (hg s hs).hasDerivWithinAt)
    (fun s hs => by simpa [Real.norm_eq_abs] using hC s hs) h0 ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at key
  calc |g t - g 0| ≤ C * |t| := key
    _ ≤ C * 1 := by
      gcongr
      rw [abs_of_nonneg ht.1]
      exact ht.2
    _ = C := mul_one C

/-- Crude third-order Taylor estimate on `[0, 1]`. -/
theorem taylor3_crude_STR02958 (φ φ1 φ2 φ3 : ℝ → ℝ) (B : ℝ)
    (h0 : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ (φ1 s) s)
    (h1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ1 (φ2 s) s)
    (h2 : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ2 (φ3 s) s)
    (hB : ∀ s ∈ Set.Icc (0 : ℝ) 1, |φ3 s| ≤ B) :
    |φ 1 - (φ 0 + φ1 0 + φ2 0 / 2)| ≤ B := by
  have hs1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, |φ2 t - φ2 0| ≤ B := fun t ht =>
    mvt01_STR02958 φ2 φ3 B h2 hB ht
  have hg1 : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun r => φ1 r - φ1 0 - r * φ2 0) (φ2 s - φ2 0) s := by
    intro s hs
    have := ((h1 s hs).sub_const (φ1 0)).sub ((hasDerivAt_id s).mul_const (φ2 0))
    exact this.congr_deriv (by simp)
  have hs2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, |φ1 t - φ1 0 - t * φ2 0| ≤ B := by
    intro t ht
    have := mvt01_STR02958 (fun r => φ1 r - φ1 0 - r * φ2 0) (fun s => φ2 s - φ2 0) B hg1 hs1 ht
    simpa using this
  have hg0 : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun r => φ r - φ 0 - r * φ1 0 - r ^ 2 / 2 * φ2 0)
        (φ1 s - φ1 0 - s * φ2 0) s := by
    intro s hs
    have h3 := (((h0 s hs).sub_const (φ 0)).sub ((hasDerivAt_id s).mul_const (φ1 0))).sub
      (((hasDerivAt_pow 2 s).div_const 2).mul_const (φ2 0))
    refine h3.congr_deriv ?_
    simp
  have := mvt01_STR02958 (fun r => φ r - φ 0 - r * φ1 0 - r ^ 2 / 2 * φ2 0)
    (fun s => φ1 s - φ1 0 - s * φ2 0) B hg0 hs2 (t := 1) ⟨zero_le_one, le_rfl⟩
  have e : φ 1 - φ 0 - 1 * φ1 0 - 1 ^ 2 / 2 * φ2 0 - (φ 0 - φ 0 - 0 * φ1 0 - 0 ^ 2 / 2 * φ2 0)
      = φ 1 - (φ 0 + φ1 0 + φ2 0 / 2) := by ring
  rw [e] at this
  exact this

/-- Second-order Taylor estimate on `[0, 1]` against a quadratic model of the second derivative. -/
theorem taylor2_poly_STR02958 (φ φ1 φ2 : ℝ → ℝ) (c0 c1 c2 B : ℝ)
    (h0 : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ (φ1 s) s)
    (h1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ1 (φ2 s) s)
    (hφ0 : φ 0 = 0) (hφ10 : φ1 0 = 0)
    (hB : ∀ s ∈ Set.Icc (0 : ℝ) 1, |φ2 s - (c0 + c1 * s + c2 * s ^ 2)| ≤ B) :
    |φ 1 - (c0 / 2 + c1 / 6 + c2 / 12)| ≤ B := by
  have hg1 : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun r => φ1 r - (c0 * r + c1 * r ^ 2 / 2 + c2 * r ^ 3 / 3))
        (φ2 s - (c0 + c1 * s + c2 * s ^ 2)) s := by
    intro s hs
    have hp : HasDerivAt (fun r : ℝ => c0 * r + c1 * r ^ 2 / 2 + c2 * r ^ 3 / 3)
        (c0 + c1 * s + c2 * s ^ 2) s := by
      have a1 := (hasDerivAt_id' s).const_mul c0
      have a2 := ((hasDerivAt_pow 2 s).const_mul c1).div_const 2
      have a3 := ((hasDerivAt_pow 3 s).const_mul c2).div_const 3
      refine ((a1.add a2).add a3).congr_deriv ?_
      simp
      ring
    exact (h1 s hs).sub hp
  have hs1 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |φ1 t - (c0 * t + c1 * t ^ 2 / 2 + c2 * t ^ 3 / 3)| ≤ B := by
    intro t ht
    have key := mvt01_STR02958 (fun r => φ1 r - (c0 * r + c1 * r ^ 2 / 2 + c2 * r ^ 3 / 3))
      (fun s => φ2 s - (c0 + c1 * s + c2 * s ^ 2)) B hg1 hB ht
    have key2 : |(φ1 t - (c0 * t + c1 * t ^ 2 / 2 + c2 * t ^ 3 / 3)) -
        (φ1 0 - (c0 * 0 + c1 * 0 ^ 2 / 2 + c2 * 0 ^ 3 / 3))| ≤ B := key
    have e : (φ1 t - (c0 * t + c1 * t ^ 2 / 2 + c2 * t ^ 3 / 3)) -
        (φ1 0 - (c0 * 0 + c1 * 0 ^ 2 / 2 + c2 * 0 ^ 3 / 3)) =
        φ1 t - (c0 * t + c1 * t ^ 2 / 2 + c2 * t ^ 3 / 3) := by
      rw [hφ10]; ring
    rwa [e] at key2
  have hg0 : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun r => φ r - (c0 * r ^ 2 / 2 + c1 * r ^ 3 / 6 + c2 * r ^ 4 / 12))
        (φ1 s - (c0 * s + c1 * s ^ 2 / 2 + c2 * s ^ 3 / 3)) s := by
    intro s hs
    have hp : HasDerivAt (fun r : ℝ => c0 * r ^ 2 / 2 + c1 * r ^ 3 / 6 + c2 * r ^ 4 / 12)
        (c0 * s + c1 * s ^ 2 / 2 + c2 * s ^ 3 / 3) s := by
      have a1 := ((hasDerivAt_pow 2 s).const_mul c0).div_const 2
      have a2 := ((hasDerivAt_pow 3 s).const_mul c1).div_const 6
      have a3 := ((hasDerivAt_pow 4 s).const_mul c2).div_const 12
      refine ((a1.add a2).add a3).congr_deriv ?_
      simp
      ring
    exact (h0 s hs).sub hp
  have key := mvt01_STR02958 (fun r => φ r - (c0 * r ^ 2 / 2 + c1 * r ^ 3 / 6 + c2 * r ^ 4 / 12))
    (fun s => φ1 s - (c0 * s + c1 * s ^ 2 / 2 + c2 * s ^ 3 / 3)) B hg0 hs1
    (t := 1) ⟨zero_le_one, le_rfl⟩
  have key2 : |(φ 1 - (c0 * 1 ^ 2 / 2 + c1 * 1 ^ 3 / 6 + c2 * 1 ^ 4 / 12)) -
      (φ 0 - (c0 * 0 ^ 2 / 2 + c1 * 0 ^ 3 / 6 + c2 * 0 ^ 4 / 12))| ≤ B := key
  have e : (φ 1 - (c0 * 1 ^ 2 / 2 + c1 * 1 ^ 3 / 6 + c2 * 1 ^ 4 / 12)) -
      (φ 0 - (c0 * 0 ^ 2 / 2 + c1 * 0 ^ 3 / 6 + c2 * 0 ^ 4 / 12)) =
      φ 1 - (c0 / 2 + c1 / 6 + c2 / 12) := by
    rw [hφ0]; ring
  rwa [e] at key2

/-- A number bounded by a multiple of `l` for all small `l > 0` is zero. -/
theorem eq_zero_of_le_mul_STR02958 (c L δ : ℝ) (hδ : 0 < δ)
    (h : ∀ l : ℝ, 0 < l → l ≤ δ → |c| ≤ L * l) : c = 0 := by
  by_contra hc
  have hpos : 0 < |c| := abs_pos.mpr hc
  have hL : 0 < 2 * (|L| + 1) := by positivity
  have hl0 : 0 < min δ (|c| / (2 * (|L| + 1))) := lt_min hδ (div_pos hpos hL)
  have hl1 : min δ (|c| / (2 * (|L| + 1))) ≤ δ := min_le_left _ _
  have hl2 : min δ (|c| / (2 * (|L| + 1))) ≤ |c| / (2 * (|L| + 1)) := min_le_right _ _
  have key := h _ hl0 hl1
  have h3 : min δ (|c| / (2 * (|L| + 1))) * (2 * (|L| + 1)) ≤ |c| := by
    rwa [le_div_iff₀ hL] at hl2
  have h4 : L * min δ (|c| / (2 * (|L| + 1))) ≤ |L| * min δ (|c| / (2 * (|L| + 1))) :=
    mul_le_mul_of_nonneg_right (le_abs_self L) hl0.le
  nlinarith [mul_nonneg (abs_nonneg L) hl0.le]

/-- The coefficients of `c2 l² + c3 l³ + c4 l⁴` vanish when it is `O(l⁵)` for small `l > 0`. -/
theorem coeff_zero_STR02958 (c2 c3 c4 K δ : ℝ) (hδ : 0 < δ)
    (h : ∀ l : ℝ, 0 < l → l ≤ δ → |c2 * l ^ 2 + c3 * l ^ 3 + c4 * l ^ 4| ≤ K * l ^ 5) :
    c2 = 0 ∧ c3 = 0 ∧ c4 = 0 := by
  have hg : ∀ x : ℝ, 0 < x → x ≤ δ → |c2 + c3 * x + c4 * x ^ 2| ≤ |K| * x ^ 3 := by
    intro x hx hxδ
    have h1 := h x hx hxδ
    have hx2 : 0 < x ^ 2 := by positivity
    have e : c2 * x ^ 2 + c3 * x ^ 3 + c4 * x ^ 4 = (c2 + c3 * x + c4 * x ^ 2) * x ^ 2 := by
      ring
    rw [e, abs_mul, abs_of_pos hx2] at h1
    have h2 : K * x ^ 5 ≤ |K| * x ^ 5 :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    have h3 : |c2 + c3 * x + c4 * x ^ 2| * x ^ 2 ≤ (|K| * x ^ 3) * x ^ 2 := by
      calc |c2 + c3 * x + c4 * x ^ 2| * x ^ 2 ≤ K * x ^ 5 := h1
        _ ≤ |K| * x ^ 5 := h2
        _ = (|K| * x ^ 3) * x ^ 2 := by ring
    exact le_of_mul_le_mul_right h3 hx2
  have hδ3 : 0 < min (δ / 3) 1 := lt_min (by positivity) one_pos
  have key : ∀ l : ℝ, 0 < l → l ≤ min (δ / 3) 1 →
      |c2| ≤ 54 * |K| * l ∧ |c3| ≤ 75 * |K| * l ∧ |c4| ≤ 22 * |K| * l := by
    intro l hl hlm
    have hl3 : l ≤ δ / 3 := hlm.trans (min_le_left _ _)
    have hl1 : l ≤ 1 := hlm.trans (min_le_right _ _)
    have g1 := abs_le.mp (hg l hl (by linarith))
    have g2 := abs_le.mp (hg (2 * l) (by positivity) (by linarith))
    have g3 := abs_le.mp (hg (3 * l) (by positivity) (by linarith))
    have hK : 0 ≤ |K| := abs_nonneg K
    have hl2 : l ^ 3 ≤ l := by
      have : l ^ 3 = l * l ^ 2 := by ring
      nlinarith [pow_le_one₀ hl.le hl1 (n := 2), pow_pos hl 2]
    have hl2' : l ^ 2 ≤ l := by nlinarith
    have hKl3 : |K| * l ^ 3 ≤ |K| * l := mul_le_mul_of_nonneg_left hl2 hK
    have hKl2 : |K| * l ^ 3 ≤ |K| * l ^ 2 := by
      have : l ^ 3 ≤ l ^ 2 := by nlinarith [pow_pos hl 2]
      exact mul_le_mul_of_nonneg_left this hK
    have hl3pos : 0 < l ^ 3 := by positivity
    refine ⟨?_, ?_, ?_⟩
    · have h2 : |c2| ≤ 54 * |K| * l ^ 3 := abs_le.mpr ⟨by linarith [g1.1, g1.2, g2.1, g2.2, g3.1, g3.2], by linarith [g1.1, g1.2, g2.1, g2.2, g3.1, g3.2]⟩
      linarith
    · have h3 : |c3 * l| ≤ 75 * |K| * l ^ 3 := abs_le.mpr ⟨by linarith [g1.1, g1.2, g2.1, g2.2, g3.1, g3.2], by linarith [g1.1, g1.2, g2.1, g2.2, g3.1, g3.2]⟩
      rw [abs_mul, abs_of_pos hl] at h3
      have h4 : |c3| * l ≤ (75 * |K| * l ^ 2) * l := by linarith
      have h5 := le_of_mul_le_mul_right h4 hl
      nlinarith [mul_le_mul_of_nonneg_left hl2' hK]
    · have h3 : |c4 * l ^ 2| ≤ 22 * |K| * l ^ 3 := abs_le.mpr ⟨by linarith [g1.1, g1.2, g2.1, g2.2, g3.1, g3.2], by linarith [g1.1, g1.2, g2.1, g2.2, g3.1, g3.2]⟩
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < l ^ 2)] at h3
      have h4 : |c4| * l ^ 2 ≤ (22 * |K| * l) * l ^ 2 := by linarith
      exact le_of_mul_le_mul_right h4 (by positivity)
  exact ⟨eq_zero_of_le_mul_STR02958 c2 (54 * |K|) _ hδ3 fun l hl hlm => (key l hl hlm).1,
    eq_zero_of_le_mul_STR02958 c3 (75 * |K|) _ hδ3 fun l hl hlm => (key l hl hlm).2.1,
    eq_zero_of_le_mul_STR02958 c4 (22 * |K|) _ hδ3 fun l hl hlm => (key l hl hlm).2.2⟩

/-! ### Iterated derivatives and calculus along rays -/

section Generic

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The second derivative `D² f` at `x`, evaluated on two vectors. -/
noncomputable def d2_STR02958 (f : X → ℝ) (x a b : X) : ℝ := iteratedFDeriv ℝ 2 f x ![a, b]

/-- The third derivative `D³ f` at `x`, evaluated on three vectors. -/
noncomputable def d3_STR02958 (f : X → ℝ) (x a b c : X) : ℝ :=
  iteratedFDeriv ℝ 3 f x ![a, b, c]

/-- The fourth derivative `D⁴ f` at `x`, evaluated on four vectors. -/
noncomputable def d4_STR02958 (f : X → ℝ) (x a b c d : X) : ℝ :=
  iteratedFDeriv ℝ 4 f x ![a, b, c, d]

/-- The fifth derivative `D⁵ f` at `x`, evaluated on five vectors. -/
noncomputable def d5_STR02958 (f : X → ℝ) (x a b c d e : X) : ℝ :=
  iteratedFDeriv ℝ 5 f x ![a, b, c, d, e]

theorem diffAt_STR02958 {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {g : X → Y}
    {W : Set X} (hW : IsOpen W) (hg : ContDiffOn ℝ ∞ g W) {q : X} (hq : q ∈ W) :
    DifferentiableAt ℝ g q :=
  (hg.contDiffAt (hW.mem_nhds hq)).differentiableAt (by simp)

theorem diffAt_iter_STR02958 {f : X → ℝ} {W : Set X} (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    (k : ℕ) {q : X} (hq : q ∈ W) : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) q :=
  (hf.contDiffAt (hW.mem_nhds hq)).differentiableAt_iteratedFDeriv
    (by exact_mod_cast WithTop.coe_lt_top _)

theorem hasDerivAt_ray_STR02958 {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (c : X → Y) (a w : X) (t : ℝ) (hc : DifferentiableAt ℝ c (a + t • w)) :
    HasDerivAt (fun s : ℝ => c (a + s • w)) (fderiv ℝ c (a + t • w) w) t := by
  have hline : HasDerivAt (fun s : ℝ => a + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add a
  exact hc.hasFDerivAt.comp_hasDerivAt t hline

theorem hasDerivAt_iter_STR02958 {f : X → ℝ} (k : ℕ) (a p : X) (m : Fin k → X) (r : ℝ)
    (hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) (a + r • p)) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ k f (a + s • p) m)
      (iteratedFDeriv ℝ (k + 1) f (a + r • p) (Fin.cons p m)) r := by
  have h1 : DifferentiableAt ℝ (fun y => iteratedFDeriv ℝ k f y m) (a + r • p) :=
    hd.continuousMultilinear_apply_const m
  have h2 := hasDerivAt_ray_STR02958 (fun y => iteratedFDeriv ℝ k f y m) a p r h1
  have h3 := hd.iteratedFDeriv_succ_apply_left' (m := (Fin.cons p m : Fin (k + 1) → X))
  rw [h3]
  simpa using h2

theorem abs_d3_STR02958 (f : X → ℝ) (q a b c : X) :
    |d3_STR02958 f q a b c| ≤ ‖iteratedFDeriv ℝ 3 f q‖ * ‖a‖ * ‖b‖ * ‖c‖ := by
  have h := (iteratedFDeriv ℝ 3 f q).le_opNorm ![a, b, c]
  simpa [d3_STR02958, Fin.prod_univ_three, Real.norm_eq_abs, mul_assoc] using h

theorem abs_d4_STR02958 (f : X → ℝ) (q a b c d : X) :
    |d4_STR02958 f q a b c d| ≤ ‖iteratedFDeriv ℝ 4 f q‖ * ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ := by
  have h := (iteratedFDeriv ℝ 4 f q).le_opNorm ![a, b, c, d]
  simpa [d4_STR02958, Fin.prod_univ_four, Real.norm_eq_abs, mul_assoc] using h

theorem abs_d5_STR02958 (f : X → ℝ) (q a b c d e : X) :
    |d5_STR02958 f q a b c d e| ≤ ‖iteratedFDeriv ℝ 5 f q‖ * ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ * ‖e‖ := by
  have h := (iteratedFDeriv ℝ 5 f q).le_opNorm ![a, b, c, d, e]
  simpa [d5_STR02958, Fin.prod_univ_five, Real.norm_eq_abs, mul_assoc] using h

theorem d2_smul0_STR02958 (f : X → ℝ) (x a b : X) (c : ℝ) :
    d2_STR02958 f x (c • a) b = c * d2_STR02958 f x a b := by
  have h := (iteratedFDeriv ℝ 2 f x).map_update_smul ![a, b] 0 c a
  have e1 : Function.update ![a, b] 0 (c • a) = ![c • a, b] := by
    ext i; fin_cases i <;> simp
  have e2 : Function.update ![a, b] 0 a = ![a, b] := by
    ext i; fin_cases i <;> simp
  rw [e1, e2] at h
  simpa [d2_STR02958] using h

theorem d2_smul1_STR02958 (f : X → ℝ) (x a b : X) (c : ℝ) :
    d2_STR02958 f x a (c • b) = c * d2_STR02958 f x a b := by
  have h := (iteratedFDeriv ℝ 2 f x).map_update_smul ![a, b] 1 c b
  have e1 : Function.update ![a, b] 1 (c • b) = ![a, c • b] := by
    ext i; fin_cases i <;> simp
  have e2 : Function.update ![a, b] 1 b = ![a, b] := by
    ext i; fin_cases i <;> simp
  rw [e1, e2] at h
  simpa [d2_STR02958] using h

theorem d3_smul0_STR02958 (f : X → ℝ) (x a b e : X) (c : ℝ) :
    d3_STR02958 f x (c • a) b e = c * d3_STR02958 f x a b e := by
  have h := (iteratedFDeriv ℝ 3 f x).map_update_smul ![a, b, e] 0 c a
  have e1 : Function.update ![a, b, e] 0 (c • a) = ![c • a, b, e] := by
    ext i; fin_cases i <;> simp
  have e2 : Function.update ![a, b, e] 0 a = ![a, b, e] := by
    ext i; fin_cases i <;> simp
  rw [e1, e2] at h
  simpa [d3_STR02958] using h

theorem d3_smul1_STR02958 (f : X → ℝ) (x a b e : X) (c : ℝ) :
    d3_STR02958 f x a (c • b) e = c * d3_STR02958 f x a b e := by
  have h := (iteratedFDeriv ℝ 3 f x).map_update_smul ![a, b, e] 1 c b
  have e1 : Function.update ![a, b, e] 1 (c • b) = ![a, c • b, e] := by
    ext i; fin_cases i <;> simp
  have e2 : Function.update ![a, b, e] 1 b = ![a, b, e] := by
    ext i; fin_cases i <;> simp
  rw [e1, e2] at h
  simpa [d3_STR02958] using h

theorem d3_smul2_STR02958 (f : X → ℝ) (x a b e : X) (c : ℝ) :
    d3_STR02958 f x a b (c • e) = c * d3_STR02958 f x a b e := by
  have h := (iteratedFDeriv ℝ 3 f x).map_update_smul ![a, b, e] 2 c e
  have e1 : Function.update ![a, b, e] 2 (c • e) = ![a, b, c • e] := by
    ext i; fin_cases i <;> simp
  have e2 : Function.update ![a, b, e] 2 e = ![a, b, e] := by
    ext i; fin_cases i <;> simp
  rw [e1, e2] at h
  simpa [d3_STR02958] using h

theorem d3_add0_STR02958 (f : X → ℝ) (x a a' b e : X) :
    d3_STR02958 f x (a + a') b e = d3_STR02958 f x a b e + d3_STR02958 f x a' b e := by
  have h := (iteratedFDeriv ℝ 3 f x).map_update_add ![a, b, e] 0 a a'
  have e1 : Function.update ![a, b, e] 0 (a + a') = ![a + a', b, e] := by
    ext i; fin_cases i <;> simp
  have e2 : Function.update ![a, b, e] 0 a = ![a, b, e] := by
    ext i; fin_cases i <;> simp
  have e3 : Function.update ![a, b, e] 0 a' = ![a', b, e] := by
    ext i; fin_cases i <;> simp
  rw [e1, e2, e3] at h
  simpa [d3_STR02958] using h

theorem d4_smul0_STR02958 (f : X → ℝ) (x a b e g : X) (c : ℝ) :
    d4_STR02958 f x (c • a) b e g = c * d4_STR02958 f x a b e g := by
  have h := (iteratedFDeriv ℝ 4 f x).map_update_smul ![a, b, e, g] 0 c a
  have e1 : Function.update ![a, b, e, g] 0 (c • a) = ![c • a, b, e, g] := by
    ext i; fin_cases i <;> simp
  have e2 : Function.update ![a, b, e, g] 0 a = ![a, b, e, g] := by
    ext i; fin_cases i <;> simp
  rw [e1, e2] at h
  simpa [d4_STR02958] using h

theorem d4_smul1_STR02958 (f : X → ℝ) (x a b e g : X) (c : ℝ) :
    d4_STR02958 f x a (c • b) e g = c * d4_STR02958 f x a b e g := by
  have h := (iteratedFDeriv ℝ 4 f x).map_update_smul ![a, b, e, g] 1 c b
  have e1 : Function.update ![a, b, e, g] 1 (c • b) = ![a, c • b, e, g] := by
    ext i; fin_cases i <;> simp
  have e2 : Function.update ![a, b, e, g] 1 b = ![a, b, e, g] := by
    ext i; fin_cases i <;> simp
  rw [e1, e2] at h
  simpa [d4_STR02958] using h

theorem d4_smul2_STR02958 (f : X → ℝ) (x a b e g : X) (c : ℝ) :
    d4_STR02958 f x a b (c • e) g = c * d4_STR02958 f x a b e g := by
  have h := (iteratedFDeriv ℝ 4 f x).map_update_smul ![a, b, e, g] 2 c e
  have e1 : Function.update ![a, b, e, g] 2 (c • e) = ![a, b, c • e, g] := by
    ext i; fin_cases i <;> simp
  have e2 : Function.update ![a, b, e, g] 2 e = ![a, b, e, g] := by
    ext i; fin_cases i <;> simp
  rw [e1, e2] at h
  simpa [d4_STR02958] using h

theorem d4_smul3_STR02958 (f : X → ℝ) (x a b e g : X) (c : ℝ) :
    d4_STR02958 f x a b e (c • g) = c * d4_STR02958 f x a b e g := by
  have h := (iteratedFDeriv ℝ 4 f x).map_update_smul ![a, b, e, g] 3 c g
  have e1 : Function.update ![a, b, e, g] 3 (c • g) = ![a, b, e, c • g] := by
    ext i; fin_cases i <;> simp
  have e2 : Function.update ![a, b, e, g] 3 g = ![a, b, e, g] := by
    ext i; fin_cases i <;> simp
  rw [e1, e2] at h
  simpa [d4_STR02958] using h

theorem d4_add0_STR02958 (f : X → ℝ) (x a a' b e g : X) :
    d4_STR02958 f x (a + a') b e g = d4_STR02958 f x a b e g + d4_STR02958 f x a' b e g := by
  have h := (iteratedFDeriv ℝ 4 f x).map_update_add ![a, b, e, g] 0 a a'
  have e1 : Function.update ![a, b, e, g] 0 (a + a') = ![a + a', b, e, g] := by
    ext i; fin_cases i <;> simp
  have e2 : Function.update ![a, b, e, g] 0 a = ![a, b, e, g] := by
    ext i; fin_cases i <;> simp
  have e3 : Function.update ![a, b, e, g] 0 a' = ![a', b, e, g] := by
    ext i; fin_cases i <;> simp
  rw [e1, e2, e3] at h
  simpa [d4_STR02958] using h

theorem d4_add1_STR02958 (f : X → ℝ) (x a b b' e g : X) :
    d4_STR02958 f x a (b + b') e g = d4_STR02958 f x a b e g + d4_STR02958 f x a b' e g := by
  have h := (iteratedFDeriv ℝ 4 f x).map_update_add ![a, b, e, g] 1 b b'
  have e1 : Function.update ![a, b, e, g] 1 (b + b') = ![a, b + b', e, g] := by
    ext i; fin_cases i <;> simp
  have e2 : Function.update ![a, b, e, g] 1 b = ![a, b, e, g] := by
    ext i; fin_cases i <;> simp
  have e3 : Function.update ![a, b, e, g] 1 b' = ![a, b', e, g] := by
    ext i; fin_cases i <;> simp
  rw [e1, e2, e3] at h
  simpa [d4_STR02958] using h

theorem hasDerivAt_fderiv_STR02958 {f : X → ℝ} {W : Set X} (hW : IsOpen W)
    (hf : ContDiffOn ℝ ∞ f W) (a p u : X) {r : ℝ} (hr : a + r • p ∈ W) :
    HasDerivAt (fun s : ℝ => fderiv ℝ f (a + s • p) u)
      (d2_STR02958 f (a + r • p) p u) r := by
  have h := hasDerivAt_iter_STR02958 1 a p ![u] r (diffAt_iter_STR02958 hW hf 1 hr)
  simpa [d2_STR02958] using h

theorem hasDerivAt_d2_STR02958 {f : X → ℝ} {W : Set X} (hW : IsOpen W)
    (hf : ContDiffOn ℝ ∞ f W) (a p u : X) {r : ℝ} (hr : a + r • p ∈ W) :
    HasDerivAt (fun s : ℝ => d2_STR02958 f (a + s • p) u u)
      (d3_STR02958 f (a + r • p) p u u) r :=
  hasDerivAt_iter_STR02958 2 a p ![u, u] r (diffAt_iter_STR02958 hW hf 2 hr)

theorem hasDerivAt_d3_STR02958 {f : X → ℝ} {W : Set X} (hW : IsOpen W)
    (hf : ContDiffOn ℝ ∞ f W) (a p b u : X) {r : ℝ} (hr : a + r • p ∈ W) :
    HasDerivAt (fun s : ℝ => d3_STR02958 f (a + s • p) b u u)
      (d4_STR02958 f (a + r • p) p b u u) r :=
  hasDerivAt_iter_STR02958 3 a p ![b, u, u] r (diffAt_iter_STR02958 hW hf 3 hr)

theorem hasDerivAt_d4_STR02958 {f : X → ℝ} {W : Set X} (hW : IsOpen W)
    (hf : ContDiffOn ℝ ∞ f W) (a p b c u : X) {r : ℝ} (hr : a + r • p ∈ W) :
    HasDerivAt (fun s : ℝ => d4_STR02958 f (a + s • p) b c u u)
      (d5_STR02958 f (a + r • p) p b c u u) r :=
  hasDerivAt_iter_STR02958 4 a p ![b, c, u, u] r (diffAt_iter_STR02958 hW hf 4 hr)

theorem rem_ray_STR02958 {f : X → ℝ} {W : Set X} (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    {S : Set X} (hS : Convex ℝ S) (h0 : (0 : X) ∈ S) (hSW : S ⊆ W) (w u : X) (hw : w ∈ S)
    (B5 : ℝ) (hB5 : ∀ q ∈ S, ‖iteratedFDeriv ℝ 5 f q‖ ≤ B5) :
    |d2_STR02958 f w u u - (d2_STR02958 f 0 u u + d3_STR02958 f 0 w u u +
        d4_STR02958 f 0 w w u u / 2)| ≤ B5 * ‖w‖ ^ 3 * ‖u‖ ^ 2 := by
  have hmem : ∀ s ∈ Set.Icc (0 : ℝ) 1, s • w ∈ S := fun s hs =>
    hS.smul_mem_of_zero_mem h0 hw hs
  have hmemW : ∀ s ∈ Set.Icc (0 : ℝ) 1, (0 : X) + s • w ∈ W := fun s hs => by
    rw [zero_add]; exact hSW (hmem s hs)
  have key := taylor3_crude_STR02958 (fun s : ℝ => d2_STR02958 f (s • w) u u)
    (fun s : ℝ => d3_STR02958 f (s • w) w u u) (fun s : ℝ => d4_STR02958 f (s • w) w w u u)
    (fun s : ℝ => d5_STR02958 f (s • w) w w w u u) (B5 * ‖w‖ ^ 3 * ‖u‖ ^ 2) ?_ ?_ ?_ ?_
  · simpa using key
  · intro s hs
    simpa using hasDerivAt_d2_STR02958 hW hf 0 w u (r := s) (hmemW s hs)
  · intro s hs
    simpa using hasDerivAt_d3_STR02958 hW hf 0 w w u (r := s) (hmemW s hs)
  · intro s hs
    simpa using hasDerivAt_d4_STR02958 hW hf 0 w w w u (r := s) (hmemW s hs)
  · intro s hs
    have h1 := abs_d5_STR02958 f (s • w) w w w u u
    have h2 := hB5 _ (hmem s hs)
    calc |d5_STR02958 f (s • w) w w w u u|
        ≤ ‖iteratedFDeriv ℝ 5 f (s • w)‖ * ‖w‖ * ‖w‖ * ‖w‖ * ‖u‖ * ‖u‖ := h1
      _ ≤ B5 * ‖w‖ * ‖w‖ * ‖w‖ * ‖u‖ * ‖u‖ := by gcongr
      _ = B5 * ‖w‖ ^ 3 * ‖u‖ ^ 2 := by ring

theorem rem_v_STR02958 {f : X → ℝ} {W : Set X} (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    {S : Set X} (hS : Convex ℝ S) (h0 : (0 : X) ∈ S) (hSW : S ⊆ W) (w v u : X)
    (hw : w ∈ S) (hwv : w + v ∈ S)
    (B4 : ℝ) (hB4 : ∀ q ∈ S, ‖iteratedFDeriv ℝ 4 f q‖ ≤ B4) :
    |d2_STR02958 f (w + v) u u - d2_STR02958 f w u u - d3_STR02958 f 0 v u u| ≤
      B4 * ((‖w‖ + ‖v‖) * ‖v‖) * ‖u‖ ^ 2 := by
  have hmem1 : ∀ σ ∈ Set.Icc (0 : ℝ) 1, w + σ • v ∈ S := by
    intro σ hσ
    have := hS hw hwv (a := 1 - σ) (b := σ) (by linarith [hσ.2]) hσ.1 (by ring)
    have e : (1 - σ) • w + σ • (w + v) = w + σ • v := by
      rw [smul_add, sub_smul, one_smul]; abel
    rwa [e] at this
  have hbound : ∀ σ ∈ Set.Icc (0 : ℝ) 1,
      |d3_STR02958 f (w + σ • v) v u u - d3_STR02958 f 0 v u u| ≤
        B4 * ((‖w‖ + ‖v‖) * ‖v‖) * ‖u‖ ^ 2 := by
    intro σ hσ
    have hB4nn : 0 ≤ B4 := (norm_nonneg _).trans (hB4 0 h0)
    have hp := hmem1 σ hσ
    have hnp : ‖w + σ • v‖ ≤ ‖w‖ + ‖v‖ := by
      calc ‖w + σ • v‖ ≤ ‖w‖ + ‖σ • v‖ := norm_add_le _ _
        _ ≤ ‖w‖ + ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ.1]
          have := norm_nonneg v
          nlinarith [hσ.2]
    have hmemr : ∀ r ∈ Set.Icc (0 : ℝ) 1, r • (w + σ • v) ∈ S := fun r hr =>
      hS.smul_mem_of_zero_mem h0 hp hr
    have key := mvt01_STR02958 (fun r : ℝ => d3_STR02958 f (r • (w + σ • v)) v u u)
      (fun r : ℝ => d4_STR02958 f (r • (w + σ • v)) (w + σ • v) v u u)
      (B4 * ((‖w‖ + ‖v‖) * ‖v‖) * ‖u‖ ^ 2) ?_ ?_ (t := 1) ⟨zero_le_one, le_rfl⟩
    · simpa using key
    · intro r hr
      simpa using hasDerivAt_d3_STR02958 hW hf 0 (w + σ • v) v u (r := r)
        (by rw [zero_add]; exact hSW (hmemr r hr))
    · intro r hr
      have h1 := abs_d4_STR02958 f (r • (w + σ • v)) (w + σ • v) v u u
      have h2 := hB4 _ (hmemr r hr)
      calc |d4_STR02958 f (r • (w + σ • v)) (w + σ • v) v u u|
          ≤ ‖iteratedFDeriv ℝ 4 f (r • (w + σ • v))‖ * ‖w + σ • v‖ * ‖v‖ * ‖u‖ * ‖u‖ := h1
        _ ≤ B4 * (‖w‖ + ‖v‖) * ‖v‖ * ‖u‖ * ‖u‖ := by gcongr
        _ = B4 * ((‖w‖ + ‖v‖) * ‖v‖) * ‖u‖ ^ 2 := by ring
  have key := mvt01_STR02958
    (fun σ : ℝ => d2_STR02958 f (w + σ • v) u u - σ * d3_STR02958 f 0 v u u)
    (fun σ : ℝ => d3_STR02958 f (w + σ • v) v u u - d3_STR02958 f 0 v u u)
    (B4 * ((‖w‖ + ‖v‖) * ‖v‖) * ‖u‖ ^ 2) ?_ ?_ (t := 1) ⟨zero_le_one, le_rfl⟩
  · have e : d2_STR02958 f (w + v) u u - d2_STR02958 f w u u - d3_STR02958 f 0 v u u =
        (d2_STR02958 f (w + (1 : ℝ) • v) u u - (1 : ℝ) * d3_STR02958 f 0 v u u) -
        (d2_STR02958 f (w + (0 : ℝ) • v) u u - (0 : ℝ) * d3_STR02958 f 0 v u u) := by
      rw [one_smul, zero_smul, add_zero, one_mul, zero_mul]; ring
    rw [e]
    exact key
  · intro σ hσ
    have h1 := hasDerivAt_d2_STR02958 hW hf w v u (r := σ) (hSW (hmem1 σ hσ))
    have h2 := (hasDerivAt_id σ).mul_const (d3_STR02958 f 0 v u u)
    exact (h1.sub h2).congr_deriv (by simp)
  · exact hbound

theorem rem_STR02958 {f : X → ℝ} {W : Set X} (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    {S : Set X} (hS : Convex ℝ S) (h0 : (0 : X) ∈ S) (hSW : S ⊆ W) (w v u : X)
    (hw : w ∈ S) (hwv : w + v ∈ S)
    (B4 B5 : ℝ) (hB4 : ∀ q ∈ S, ‖iteratedFDeriv ℝ 4 f q‖ ≤ B4)
    (hB5 : ∀ q ∈ S, ‖iteratedFDeriv ℝ 5 f q‖ ≤ B5) :
    |d2_STR02958 f (w + v) u u - (d2_STR02958 f 0 u u + d3_STR02958 f 0 w u u +
        d4_STR02958 f 0 w w u u / 2 + d3_STR02958 f 0 v u u)| ≤
      ‖u‖ ^ 2 * (B5 * ‖w‖ ^ 3 + B4 * ((‖w‖ + ‖v‖) * ‖v‖)) := by
  have h1 := rem_ray_STR02958 hW hf hS h0 hSW w u hw B5 hB5
  have h2 := rem_v_STR02958 hW hf hS h0 hSW w v u hw hwv B4 hB4
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

end Generic

/-! ### Taylor jets in the directions of the box -/

section Jets

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The weighted quadratic jet term in the direction `u`. -/
noncomputable def Q2_STR02958 (f : X → ℝ) (u : X) : ℝ := d2_STR02958 f 0 u u / 2

/-- The weighted cubic jet term in the directions `h e3` and `u`. -/
noncomputable def Q3_STR02958 (f : X → ℝ) (e3 u : X) (h : ℝ) : ℝ :=
  d3_STR02958 f 0 (h • e3) u u / 2 + d3_STR02958 f 0 u u u / 6

/-- The weighted quartic jet term in the directions `h e3`, `γ e4` and `u`. -/
noncomputable def Q4_STR02958 (f : X → ℝ) (e3 e4 u : X) (h γ : ℝ) : ℝ :=
  (d4_STR02958 f 0 (h • e3) (h • e3) u u / 2 + d3_STR02958 f 0 (γ • e4) u u) / 2 +
    (d4_STR02958 f 0 u (h • e3) u u + d4_STR02958 f 0 (h • e3) u u u) / 12 +
    d4_STR02958 f 0 u u u u / 24

/-- The constant coefficient of the second derivative along the segment. -/
noncomputable def C0_STR02958 (f : X → ℝ) (e3 e4 u : X) (h γ : ℝ) : ℝ :=
  d2_STR02958 f 0 u u + d3_STR02958 f 0 (h • e3) u u +
    d4_STR02958 f 0 (h • e3) (h • e3) u u / 2 + d3_STR02958 f 0 (γ • e4) u u

/-- The linear coefficient of the second derivative along the segment. -/
noncomputable def C1_STR02958 (f : X → ℝ) (e3 u : X) (h : ℝ) : ℝ :=
  d3_STR02958 f 0 u u u + (d4_STR02958 f 0 u (h • e3) u u + d4_STR02958 f 0 (h • e3) u u u) / 2

/-- The quadratic coefficient of the second derivative along the segment. -/
noncomputable def C2_STR02958 (f : X → ℝ) (u : X) : ℝ := d4_STR02958 f 0 u u u u / 2

theorem Q2_smul_STR02958 (f : X → ℝ) (u : X) (l : ℝ) :
    Q2_STR02958 f (l • u) = l ^ 2 * Q2_STR02958 f u := by
  unfold Q2_STR02958
  simp only [d2_smul0_STR02958, d2_smul1_STR02958]
  ring

theorem Q3_smul_STR02958 (f : X → ℝ) (e3 u : X) (l : ℝ) :
    Q3_STR02958 f e3 (l • u) l = l ^ 3 * Q3_STR02958 f e3 u 1 := by
  unfold Q3_STR02958
  simp only [one_smul, d3_smul0_STR02958, d3_smul1_STR02958, d3_smul2_STR02958]
  ring

theorem Q4_smul_STR02958 (f : X → ℝ) (e3 e4 u : X) (l s : ℝ) :
    Q4_STR02958 f e3 e4 (l • u) l (l ^ 2 * s) = l ^ 4 * Q4_STR02958 f e3 e4 u 1 s := by
  unfold Q4_STR02958
  simp only [one_smul, d3_smul0_STR02958, d3_smul1_STR02958, d3_smul2_STR02958,
    d4_smul0_STR02958, d4_smul1_STR02958, d4_smul2_STR02958, d4_smul3_STR02958]
  ring

theorem expand_STR02958 (f : X → ℝ) (e3 e4 u : X) (h γ t : ℝ) :
    d2_STR02958 f 0 u u + d3_STR02958 f 0 (t • u + h • e3) u u +
      d4_STR02958 f 0 (t • u + h • e3) (t • u + h • e3) u u / 2 +
      d3_STR02958 f 0 (γ • e4) u u =
    C0_STR02958 f e3 e4 u h γ + C1_STR02958 f e3 u h * t + C2_STR02958 f u * t ^ 2 := by
  unfold C0_STR02958 C1_STR02958 C2_STR02958
  simp only [d3_add0_STR02958, d4_add0_STR02958, d4_add1_STR02958, d3_smul0_STR02958,
    d4_smul0_STR02958, d4_smul1_STR02958]
  ring

theorem Qsum_STR02958 (f : X → ℝ) (e3 e4 u : X) (h γ : ℝ) :
    Q2_STR02958 f u + Q3_STR02958 f e3 u h + Q4_STR02958 f e3 e4 u h γ =
    C0_STR02958 f e3 e4 u h γ / 2 + C1_STR02958 f e3 u h / 6 + C2_STR02958 f u / 12 := by
  unfold Q2_STR02958 Q3_STR02958 Q4_STR02958 C0_STR02958 C1_STR02958 C2_STR02958
  ring

/-- Pointwise Taylor remainder of order five, with the amplitude factor `‖u‖²` retained, in
terms of the evaluated iterated derivatives. -/
theorem taylor_rem_STR02958 {f : X → ℝ} {W : Set X} (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    {S : Set X} (hS : Convex ℝ S) (h0 : (0 : X) ∈ S) (hSW : S ⊆ W) (e3 e4 u : X) (h γ : ℝ)
    (he3 : ‖e3‖ ≤ 1) (he4 : ‖e4‖ ≤ 1)
    (hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, t • u + h • e3 ∈ S ∧ t • u + h • e3 + γ • e4 ∈ S)
    (hz : f (h • e3 + γ • e4) = 0) (hd : fderiv ℝ f (h • e3 + γ • e4) u = 0)
    (B4 B5 : ℝ) (hB4 : ∀ q ∈ S, ‖iteratedFDeriv ℝ 4 f q‖ ≤ B4)
    (hB5 : ∀ q ∈ S, ‖iteratedFDeriv ℝ 5 f q‖ ≤ B5) :
    |f (h • e3 + γ • e4 + u) -
        (Q2_STR02958 f u + Q3_STR02958 f e3 u h + Q4_STR02958 f e3 e4 u h γ)| ≤
      ‖u‖ ^ 2 * (B5 * (|h| + ‖u‖) ^ 3 + B4 * ((|h| + ‖u‖ + |γ|) * |γ|)) := by
  have hB4nn : 0 ≤ B4 := (norm_nonneg _).trans (hB4 0 h0)
  have hB5nn : 0 ≤ B5 := (norm_nonneg _).trans (hB5 0 h0)
  have hmemW : ∀ t ∈ Set.Icc (0 : ℝ) 1, h • e3 + γ • e4 + t • u ∈ W := by
    intro t ht
    have e : h • e3 + γ • e4 + t • u = t • u + h • e3 + γ • e4 := by abel
    rw [e]
    exact hSW (hmem t ht).2
  have hφ : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => f (h • e3 + γ • e4 + t • u))
        (fderiv ℝ f (h • e3 + γ • e4 + s • u) u) s := fun s hs =>
    hasDerivAt_ray_STR02958 f (h • e3 + γ • e4) u s (diffAt_STR02958 hW hf (hmemW s hs))
  have hφ1 : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => fderiv ℝ f (h • e3 + γ • e4 + t • u) u)
        (d2_STR02958 f (h • e3 + γ • e4 + s • u) u u) s := fun s hs =>
    hasDerivAt_fderiv_STR02958 hW hf (h • e3 + γ • e4) u u (hmemW s hs)
  have hrem : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |d2_STR02958 f (h • e3 + γ • e4 + t • u) u u -
        (C0_STR02958 f e3 e4 u h γ + C1_STR02958 f e3 u h * t + C2_STR02958 f u * t ^ 2)| ≤
      ‖u‖ ^ 2 * (B5 * (|h| + ‖u‖) ^ 3 + B4 * ((|h| + ‖u‖ + |γ|) * |γ|)) := by
    intro t ht
    obtain ⟨hw, hwv⟩ := hmem t ht
    have key := rem_STR02958 hW hf hS h0 hSW (t • u + h • e3) (γ • e4) u hw hwv B4 B5 hB4 hB5
    have e1 : h • e3 + γ • e4 + t • u = t • u + h • e3 + γ • e4 := by abel
    rw [e1, ← expand_STR02958 f e3 e4 u h γ t]
    refine key.trans ?_
    have a1 : t * ‖u‖ ≤ ‖u‖ := by nlinarith [norm_nonneg u, ht.2]
    have a2 : |h| * ‖e3‖ ≤ |h| := mul_le_of_le_one_right (abs_nonneg h) he3
    have hw1 : ‖t • u + h • e3‖ ≤ |h| + ‖u‖ := by
      calc ‖t • u + h • e3‖ ≤ ‖t • u‖ + ‖h • e3‖ := norm_add_le _ _
        _ = t * ‖u‖ + |h| * ‖e3‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht.1]
        _ ≤ |h| + ‖u‖ := by linarith
    have hv : ‖γ • e4‖ ≤ |γ| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg γ) he4
    gcongr
  have key2 := taylor2_poly_STR02958 (fun t : ℝ => f (h • e3 + γ • e4 + t • u))
    (fun t : ℝ => fderiv ℝ f (h • e3 + γ • e4 + t • u) u)
    (fun t : ℝ => d2_STR02958 f (h • e3 + γ • e4 + t • u) u u)
    (C0_STR02958 f e3 e4 u h γ) (C1_STR02958 f e3 u h) (C2_STR02958 f u)
    (‖u‖ ^ 2 * (B5 * (|h| + ‖u‖) ^ 3 + B4 * ((|h| + ‖u‖ + |γ|) * |γ|)))
    hφ hφ1 (by simpa using hz) (by simpa using hd) hrem
  rw [← Qsum_STR02958 f e3 e4 u h γ] at key2
  simpa only [one_smul] using key2

/-- Identification of the jet coefficients from a scaled bound of order five. -/
theorem jet_coeff_STR02958 {f : X → ℝ} {W : Set X} (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    {S : Set X} (hS : Convex ℝ S) (h0 : (0 : X) ∈ S) (hSW : S ⊆ W) (e3 e4 u1 : X) (s P1 : ℝ)
    (he3 : ‖e3‖ ≤ 1) (he4 : ‖e4‖ ≤ 1)
    (B4 B5 : ℝ) (hB4 : ∀ q ∈ S, ‖iteratedFDeriv ℝ 4 f q‖ ≤ B4)
    (hB5 : ∀ q ∈ S, ‖iteratedFDeriv ℝ 5 f q‖ ≤ B5) (δ M : ℝ) (hδ : 0 < δ)
    (hmem : ∀ l : ℝ, 0 < l → l ≤ δ → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      t • (l • u1) + l • e3 ∈ S ∧ t • (l • u1) + l • e3 + (l ^ 2 * s) • e4 ∈ S)
    (hz : ∀ l : ℝ, 0 < l → l ≤ δ → f (l • e3 + (l ^ 2 * s) • e4) = 0)
    (hd : ∀ l : ℝ, 0 < l → l ≤ δ → fderiv ℝ f (l • e3 + (l ^ 2 * s) • e4) (l • u1) = 0)
    (hF : ∀ l : ℝ, 0 < l → l ≤ δ →
      |f (l • e3 + (l ^ 2 * s) • e4 + l • u1) - l ^ 4 * P1| ≤ M * l ^ 5) :
    Q2_STR02958 f u1 = 0 ∧ Q3_STR02958 f e3 u1 1 = 0 ∧ Q4_STR02958 f e3 e4 u1 1 s = P1 := by
  have hB4nn : 0 ≤ B4 := (norm_nonneg _).trans (hB4 0 h0)
  have hB5nn : 0 ≤ B5 := (norm_nonneg _).trans (hB5 0 h0)
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ‖u1‖ ^ 2 * (B5 * (1 + ‖u1‖) ^ 3 +
      B4 * ((1 + ‖u1‖ + |s|) * |s|)) := ⟨_, rfl⟩
  have hmain : ∀ l : ℝ, 0 < l → l ≤ min δ 1 →
      |l ^ 2 * Q2_STR02958 f u1 + l ^ 3 * Q3_STR02958 f e3 u1 1 +
          l ^ 4 * Q4_STR02958 f e3 e4 u1 1 s - l ^ 4 * P1| ≤ (M + R) * l ^ 5 := by
    intro l hl hlm
    have hlδ : l ≤ δ := hlm.trans (min_le_left _ _)
    have hl1 : l ≤ 1 := hlm.trans (min_le_right _ _)
    have key := taylor_rem_STR02958 hW hf hS h0 hSW e3 e4 (l • u1) l (l ^ 2 * s) he3 he4
      (hmem l hl hlδ) (hz l hl hlδ) (hd l hl hlδ) B4 B5 hB4 hB5
    rw [Q2_smul_STR02958, Q3_smul_STR02958, Q4_smul_STR02958] at key
    have hF' := hF l hl hlδ
    have hnu : ‖l • u1‖ = l * ‖u1‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl]
    have hbd : ‖l • u1‖ ^ 2 * (B5 * (|l| + ‖l • u1‖) ^ 3 +
        B4 * ((|l| + ‖l • u1‖ + |l ^ 2 * s|) * |l ^ 2 * s|)) ≤ R * l ^ 5 := by
      rw [hnu, abs_of_pos hl, abs_mul, abs_of_nonneg (sq_nonneg l)]
      have e : (l * ‖u1‖) ^ 2 * (B5 * (l + l * ‖u1‖) ^ 3 +
          B4 * ((l + l * ‖u1‖ + l ^ 2 * |s|) * (l ^ 2 * |s|))) =
          l ^ 5 * (‖u1‖ ^ 2 * (B5 * (1 + ‖u1‖) ^ 3 +
            B4 * ((1 + ‖u1‖ + l * |s|) * |s|))) := by ring
      rw [e, hR]
      have h1 : l * |s| ≤ |s| := mul_le_of_le_one_left (abs_nonneg s) hl1
      have h2 : ‖u1‖ ^ 2 * (B5 * (1 + ‖u1‖) ^ 3 + B4 * ((1 + ‖u1‖ + l * |s|) * |s|)) ≤
          ‖u1‖ ^ 2 * (B5 * (1 + ‖u1‖) ^ 3 + B4 * ((1 + ‖u1‖ + |s|) * |s|)) := by
        gcongr
      nlinarith [pow_pos hl 5]
    have k1 := abs_le.mp (key.trans hbd)
    have k2 := abs_le.mp hF'
    rw [abs_le]
    constructor <;> linarith [k1.1, k1.2, k2.1, k2.2]
  obtain ⟨h2, h3, h4⟩ := coeff_zero_STR02958 (Q2_STR02958 f u1) (Q3_STR02958 f e3 u1 1)
    (Q4_STR02958 f e3 e4 u1 1 s - P1) (M + R) (min δ 1) (lt_min hδ one_pos) (fun l hl hlm => by
      have := hmain l hl hlm
      have e : Q2_STR02958 f u1 * l ^ 2 + Q3_STR02958 f e3 u1 1 * l ^ 3 +
          (Q4_STR02958 f e3 e4 u1 1 s - P1) * l ^ 4 =
          l ^ 2 * Q2_STR02958 f u1 + l ^ 3 * Q3_STR02958 f e3 u1 1 +
            l ^ 4 * Q4_STR02958 f e3 e4 u1 1 s - l ^ 4 * P1 := by ring
      rw [e]
      exact this)
  exact ⟨h2, h3, by linarith⟩

/-- Pointwise Taylor remainder with a common bound on the iterated derivatives. -/
theorem taylor_rem'_STR02958 {f : X → ℝ} {W : Set X} (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    {S : Set X} (hS : Convex ℝ S) (h0 : (0 : X) ∈ S) (hSW : S ⊆ W) (e3 e4 u : X) (h γ : ℝ)
    (he3 : ‖e3‖ ≤ 1) (he4 : ‖e4‖ ≤ 1)
    (hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, t • u + h • e3 ∈ S ∧ t • u + h • e3 + γ • e4 ∈ S)
    (hz : f (h • e3 + γ • e4) = 0) (hd : fderiv ℝ f (h • e3 + γ • e4) u = 0)
    (M : ℝ) (hB4 : ∀ q ∈ S, ‖iteratedFDeriv ℝ 4 f q‖ ≤ M)
    (hB5 : ∀ q ∈ S, ‖iteratedFDeriv ℝ 5 f q‖ ≤ M) :
    |f (h • e3 + γ • e4 + u) -
        (Q2_STR02958 f u + Q3_STR02958 f e3 u h + Q4_STR02958 f e3 e4 u h γ)| ≤
      ‖u‖ ^ 2 * (M * (|h| + ‖u‖) ^ 3 + M * ((|h| + ‖u‖ + |γ|) * |γ|)) :=
  taylor_rem_STR02958 hW hf hS h0 hSW e3 e4 u h γ he3 he4 hmem hz hd M M hB4 hB5

/-- Identification of the jet coefficients with a common bound on the iterated derivatives. -/
theorem jet_coeff'_STR02958 {f : X → ℝ} {W : Set X} (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    {S : Set X} (hS : Convex ℝ S) (h0 : (0 : X) ∈ S) (hSW : S ⊆ W) (e3 e4 u1 : X) (s P1 : ℝ)
    (he3 : ‖e3‖ ≤ 1) (he4 : ‖e4‖ ≤ 1)
    (N : ℝ) (hB4 : ∀ q ∈ S, ‖iteratedFDeriv ℝ 4 f q‖ ≤ N)
    (hB5 : ∀ q ∈ S, ‖iteratedFDeriv ℝ 5 f q‖ ≤ N) (δ M : ℝ) (hδ : 0 < δ)
    (hmem : ∀ l : ℝ, 0 < l → l ≤ δ → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      t • (l • u1) + l • e3 ∈ S ∧ t • (l • u1) + l • e3 + (l ^ 2 * s) • e4 ∈ S)
    (hz : ∀ l : ℝ, 0 < l → l ≤ δ → f (l • e3 + (l ^ 2 * s) • e4) = 0)
    (hd : ∀ l : ℝ, 0 < l → l ≤ δ → fderiv ℝ f (l • e3 + (l ^ 2 * s) • e4) (l • u1) = 0)
    (hF : ∀ l : ℝ, 0 < l → l ≤ δ →
      |f (l • e3 + (l ^ 2 * s) • e4 + l • u1) - l ^ 4 * P1| ≤ M * l ^ 5) :
    Q2_STR02958 f u1 = 0 ∧ Q3_STR02958 f e3 u1 1 = 0 ∧ Q4_STR02958 f e3 e4 u1 1 s = P1 :=
  jet_coeff_STR02958 hW hf hS h0 hSW e3 e4 u1 s P1 he3 he4 N N hB4 hB5 δ M hδ hmem hz hd hF

end Jets

/-! ### The four-variable reduced functional -/

/-- The reduced functional in the variables `(h, γ, u)` with the entropy normalization written
through `Z (h, 0)`. -/
noncomputable def JJ_STR02958 (x : ℝ × ℝ × PeriodicC2_STR02969) : ℝ :=
  meanCLM_STR02954
      (e1_STR02955 x.2.2 * e1_STR02955 x.2.2 * rho_STR02954 (x.1, e0_STR02955 x.2.2)) -
    2 * (1 + x.2.1) *
      (meanCLM_STR02954 (e0_STR02955 x.2.2 * rho_STR02954 (x.1, e0_STR02955 x.2.2)) -
        Real.log (Z_STR02954 (x.1, e0_STR02955 x.2.2)) + Real.log (Z_STR02954 (x.1, 0)))

theorem JJ_smooth_STR02958 : ContDiff ℝ ∞ JJ_STR02958 := by
  have hh : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => x.1) := contDiff_fst
  have hg : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => x.2.1) :=
    contDiff_fst.comp contDiff_snd
  have hu : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => x.2.2) :=
    contDiff_snd.comp contDiff_snd
  have h0 : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => e0_STR02955 x.2.2) :=
    e0_STR02955.contDiff.comp hu
  have h1 : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => e1_STR02955 x.2.2) :=
    e1_STR02955.contDiff.comp hu
  have hρ : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 =>
      rho_STR02954 (x.1, e0_STR02955 x.2.2)) :=
    rho_smooth_STR02954.comp (hh.prodMk h0)
  have hZ : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 =>
      Real.log (Z_STR02954 (x.1, e0_STR02955 x.2.2))) :=
    logZ_smooth_STR02954.comp (hh.prodMk h0)
  have hZ0 : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 =>
      Real.log (Z_STR02954 (x.1, 0))) :=
    logZ_smooth_STR02954.comp (hh.prodMk contDiff_const)
  have hI : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 =>
      meanCLM_STR02954 (e1_STR02955 x.2.2 * e1_STR02955 x.2.2 *
        rho_STR02954 (x.1, e0_STR02955 x.2.2))) :=
    meanCLM_STR02954.contDiff.comp ((h1.mul h1).mul hρ)
  have hE : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 =>
      meanCLM_STR02954 (e0_STR02955 x.2.2 * rho_STR02954 (x.1, e0_STR02955 x.2.2))) :=
    meanCLM_STR02954.contDiff.comp (h0.mul hρ)
  unfold JJ_STR02958
  exact hI.sub ((contDiff_const.mul (contDiff_const.add hg)).mul ((hE.sub hZ).add hZ0))

theorem JC2_eq_JJ_STR02958 (h γ : ℝ) (u : PeriodicC2_STR02969) :
    JC2_STR02956 h γ u = JJ_STR02958 (h, γ, u) := by
  have hz : Real.log (meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s)))) =
      Real.log (Z_STR02954 (h, 0)) := by
    have h0 : ∀ s, PeriodicHolder_STR02968.val (0 : PeriodicHolder_STR02968) s = 0 :=
      fun s => rfl
    rw [Z_eq_meanT_STR02954]
    simp [h0]
  unfold JC2_STR02956 JJ_STR02958
  rw [hz]

/-- The reduced functional of STR029.56 as a function of the four parameters `(a, b, h, γ)`. -/
noncomputable def Fhat_STR02958 (ψ : Par_STR02916 → E_STR02969) (p : Par_STR02916) : ℝ :=
  Fred_STR02956 ψ (p.1, p.2.1) (p.2.2.1, p.2.2.2)

theorem Fhat_eq_JJ_STR02958 (ψ : Par_STR02916 → E_STR02969) (p : Par_STR02916) :
    Fhat_STR02958 ψ p = JJ_STR02958 (p.2.2.1, p.2.2.2,
      p.1 • cosC2_STR02915 + p.2.1 • sinC2_STR02915 +
        ((ψ p : E_STR02969) : PeriodicC2_STR02969)) := by
  unfold Fhat_STR02958
  rw [Fred_eq_STR02956, JC2_eq_JJ_STR02958]
  rfl

theorem Fhat_contDiffOn_STR02958 {U : Set Par_STR02916} {ψ : Par_STR02916 → E_STR02969}
    (hψ : ContDiffOn ℝ ∞ ψ U) : ContDiffOn ℝ ∞ (Fhat_STR02958 ψ) U := by
  have hψ' : ContDiffOn ℝ ∞ (fun p : Par_STR02916 => ((ψ p : E_STR02969) : PeriodicC2_STR02969))
      U := E_STR02969.subtypeL.contDiff.comp_contDiffOn hψ
  have hlin : ContDiff ℝ ∞ (fun p : Par_STR02916 =>
      p.1 • cosC2_STR02915 + p.2.1 • sinC2_STR02915) :=
    (contDiff_fst.smul contDiff_const).add ((contDiff_fst.comp contDiff_snd).smul contDiff_const)
  have hth1 : ContDiff ℝ ∞ (fun p : Par_STR02916 => p.2.2.1) :=
    contDiff_fst.comp (contDiff_snd.comp contDiff_snd)
  have hth2 : ContDiff ℝ ∞ (fun p : Par_STR02916 => p.2.2.2) :=
    contDiff_snd.comp (contDiff_snd.comp contDiff_snd)
  have hg : ContDiffOn ℝ ∞ (fun p : Par_STR02916 =>
      ((p.2.2.1, p.2.2.2, p.1 • cosC2_STR02915 + p.2.1 • sinC2_STR02915 +
        ((ψ p : E_STR02969) : PeriodicC2_STR02969)) : ℝ × ℝ × PeriodicC2_STR02969)) U :=
    hth1.contDiffOn.prodMk (hth2.contDiffOn.prodMk (hlin.contDiffOn.add hψ'))
  have hcomp := JJ_smooth_STR02958.comp_contDiffOn hg
  refine hcomp.congr ?_
  intro p _
  exact Fhat_eq_JJ_STR02958 ψ p

theorem Fhat_zero_amp_STR02958 {ψ : Par_STR02916 → E_STR02969} (h γ : ℝ)
    (h0 : ψ (0, 0, h, γ) = 0) : Fhat_STR02958 ψ ((0, 0, h, γ) : Par_STR02916) = 0 :=
  Fred_zero_STR02956 ψ (h, γ) h0

theorem fderiv_Fhat_ray_STR02958 {U : Set Par_STR02916} {ψ : Par_STR02916 → E_STR02969}
    (hU : IsOpen U) (hψ : ContDiffOn ℝ ∞ ψ U) (h γ : ℝ)
    (h0U : ((0, 0, h, γ) : Par_STR02916) ∈ U) (h0 : ψ (0, 0, h, γ) = 0) (a b : ℝ) :
    fderiv ℝ (Fhat_STR02958 ψ) ((0, 0, h, γ) : Par_STR02916) ((a, b, 0, 0) : Par_STR02916) = 0 := by
  have hFd : DifferentiableAt ℝ (Fhat_STR02958 ψ) ((0, 0, h, γ) : Par_STR02916) :=
    diffAt_STR02958 hU (Fhat_contDiffOn_STR02958 hψ) h0U
  have h1 := hasDerivAt_ray_STR02958 (Fhat_STR02958 ψ) ((0, 0, h, γ) : Par_STR02916)
    ((a, b, 0, 0) : Par_STR02916) 0 (by simpa using hFd)
  have hW := isOpen_iota_preimage_STR02956 hU (h, γ)
  have h0W : (0 : ℝ × ℝ) ∈ iota_STR02956 (h, γ) ⁻¹' U := by
    rw [mem_iota_preimage_STR02956]
    simpa using h0U
  have hGd : DifferentiableAt ℝ (fun y => Fred_STR02956 ψ y (h, γ)) ((0 : ℝ × ℝ) + (0 : ℝ) • (a, b)) := by
    simpa using ((Fred_contDiffOn_STR02956 hψ (h, γ)).contDiffAt (hW.mem_nhds h0W)).differentiableAt
      (by simp)
  have h2 := hasDerivAt_ray_STR02958 (fun y => Fred_STR02956 ψ y (h, γ)) (0 : ℝ × ℝ) (a, b) 0 hGd
  have hfun : (fun s : ℝ => Fhat_STR02958 ψ (((0, 0, h, γ) : Par_STR02916) +
      s • ((a, b, 0, 0) : Par_STR02916))) =
      (fun s : ℝ => Fred_STR02956 ψ ((0 : ℝ × ℝ) + s • (a, b)) (h, γ)) := by
    funext s
    simp [Fhat_STR02958]
  rw [hfun] at h1
  have h3 := h1.unique h2
  have h4 := fderiv_Fred_zero_STR02956 hU hψ (h, γ) h0U h0
  simp only [zero_smul, add_zero] at h3
  rw [h4] at h3
  simpa using h3

/-! ### Boxes and the coordinate directions -/

/-- The closed coordinate box of radius `r` (a closed ball for the sup norm). -/
def box_STR02958 (r : ℝ) : Set Par_STR02916 := Metric.closedBall 0 r

theorem mem_box_STR02958 (r a b h γ : ℝ) :
    ((a, b, h, γ) : Par_STR02916) ∈ box_STR02958 r ↔
      |a| ≤ r ∧ |b| ≤ r ∧ |h| ≤ r ∧ |γ| ≤ r := by
  simp [box_STR02958, Prod.norm_def]

theorem box_convex_STR02958 (r : ℝ) : Convex ℝ (box_STR02958 r) := convex_closedBall 0 r

theorem box_isCompact_STR02958 (r : ℝ) : IsCompact (box_STR02958 r) := isCompact_closedBall 0 r

theorem zero_mem_box_STR02958 {r : ℝ} (hr : 0 ≤ r) : (0 : Par_STR02916) ∈ box_STR02958 r :=
  Metric.mem_closedBall_self hr

/-- The coordinate direction of the amplitude `h`. -/
def e3_STR02958 : Par_STR02916 := (0, 0, 1, 0)

/-- The coordinate direction of the parameter `γ`. -/
def e4_STR02958 : Par_STR02916 := (0, 0, 0, 1)

/-- The direction `(a, b, 0, 0)` of the planar amplitude. -/
def uu_STR02958 (a b : ℝ) : Par_STR02916 := (a, b, 0, 0)

theorem comb_STR02958 (a b h γ : ℝ) :
    h • e3_STR02958 + γ • e4_STR02958 + uu_STR02958 a b = ((a, b, h, γ) : Par_STR02916) := by
  simp [e3_STR02958, e4_STR02958, uu_STR02958]

theorem comb2_STR02958 (h γ : ℝ) :
    h • e3_STR02958 + γ • e4_STR02958 = ((0, 0, h, γ) : Par_STR02916) := by
  simp [e3_STR02958, e4_STR02958]

theorem smul_uu_STR02958 (l a b : ℝ) :
    l • uu_STR02958 a b = uu_STR02958 (l * a) (l * b) := by
  simp [uu_STR02958]

theorem norm_e3_STR02958 : ‖e3_STR02958‖ ≤ 1 := by
  simp [e3_STR02958, Prod.norm_def]

theorem norm_e4_STR02958 : ‖e4_STR02958‖ ≤ 1 := by
  simp [e4_STR02958, Prod.norm_def]

theorem norm_uu_le_STR02958 (a b : ℝ) : ‖uu_STR02958 a b‖ ≤ R0_STR02918 a b := by
  have ha : |a| ≤ R0_STR02918 a b := Real.abs_le_sqrt (by nlinarith [sq_nonneg b])
  have hb : |b| ≤ R0_STR02918 a b := Real.abs_le_sqrt (by nlinarith [sq_nonneg a])
  simp [uu_STR02958, Prod.norm_def, ha, hb]

/-! ### The jet of the reduced functional and the remainder bound -/

/-- The graph vanishes on the slice `a = b = 0`, by the graph characterization and the equilibrium
of `Rpar_STR02916`. -/
theorem slice_zero_STR02958 {U : Set Par_STR02916} {V : Set E_STR02969}
    {ψ : Par_STR02916 → E_STR02969} (h0V : (0 : E_STR02969) ∈ V)
    (hiff : ∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p) (h γ : ℝ)
    (hp : ((0, 0, h, γ) : Par_STR02916) ∈ U) : ψ (0, 0, h, γ) = 0 :=
  ((hiff _ hp 0 h0V).mp (Rpar_equilibrium_STR02916 h γ)).symm

/-- The weighted jet of the reduced functional: the quadratic and cubic terms vanish and the
quartic term is the weight-four polynomial of STR029.57. -/
theorem jet_vanish_STR02958 {U : Set Par_STR02916} {ψ : Par_STR02916 → E_STR02969}
    (hU : IsOpen U) (hψ : ContDiffOn ℝ ∞ ψ U)
    (hsl : ∀ h γ : ℝ, ((0, 0, h, γ) : Par_STR02916) ∈ U → ψ (0, 0, h, γ) = 0)
    (hK : ∀ K : Set (ℝ × ℝ × ℝ), IsCompact K →
        ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ A B s : ℝ, (A, B, s) ∈ K →
          ∀ h : ℝ, |h| ≤ δ →
            ((h * A, h * B, h, h ^ 2 * s) : Par_STR02916) ∈ U ∧
            |Jchart_STR02950 h (h ^ 2 * s)
                (uT_STR02901 (h * A) (h * B)
                  (vE_STR02957 (ψ ((h * A, h * B, h, h ^ 2 * s) : Par_STR02916)))) -
              poly19_STR02957 (h * A) (h * B) h (h ^ 2 * s)| ≤ M * |h| ^ 5)
    {r : ℝ} (hr : 0 < r) (hbox : box_STR02958 r ⊆ U) (N : ℝ)
    (hN4 : ∀ q ∈ box_STR02958 r, ‖iteratedFDeriv ℝ 4 (Fhat_STR02958 ψ) q‖ ≤ N)
    (hN5 : ∀ q ∈ box_STR02958 r, ‖iteratedFDeriv ℝ 5 (Fhat_STR02958 ψ) q‖ ≤ N) (A B s : ℝ) :
    Q2_STR02958 (Fhat_STR02958 ψ) (uu_STR02958 A B) = 0 ∧
    Q3_STR02958 (Fhat_STR02958 ψ) e3_STR02958 (uu_STR02958 A B) 1 = 0 ∧
    Q4_STR02958 (Fhat_STR02958 ψ) e3_STR02958 e4_STR02958 (uu_STR02958 A B) 1 s =
      Jred_STR02918 A B - 2 * s * ((A ^ 2 + B ^ 2) / 4) := by
  obtain ⟨δ, hδ, M, hM, hall⟩ := hK {(A, B, s)} isCompact_singleton
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 + |A| + |B| + |s| := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hc]; positivity
  obtain ⟨δ', hδ'⟩ : ∃ δ' : ℝ, δ' = min δ (min 1 (r / c)) := ⟨_, rfl⟩
  have hδ'pos : 0 < δ' := by
    rw [hδ']
    exact lt_min hδ (lt_min one_pos (div_pos hr hcpos))
  have hδ'1 : δ' ≤ δ := by rw [hδ']; exact min_le_left _ _
  have hδ'2 : δ' ≤ 1 := by rw [hδ']; exact (min_le_right _ _).trans (min_le_left _ _)
  have hδ'3 : δ' ≤ r / c := by rw [hδ']; exact (min_le_right _ _).trans (min_le_right _ _)
  have hlc : ∀ l : ℝ, 0 < l → l ≤ δ' → l * c ≤ r := by
    intro l hl hlδ
    have : l ≤ r / c := hlδ.trans hδ'3
    rwa [le_div_iff₀ hcpos] at this
  have hmem : ∀ l : ℝ, 0 < l → l ≤ δ' → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      t • (l • uu_STR02958 A B) + l • e3_STR02958 ∈ box_STR02958 r ∧
      t • (l • uu_STR02958 A B) + l • e3_STR02958 + (l ^ 2 * s) • e4_STR02958 ∈
        box_STR02958 r := by
    intro l hl hlδ t ht
    have hl1 : l ≤ 1 := hlδ.trans hδ'2
    have hlc' := hlc l hl hlδ
    rw [hc] at hlc'
    have bA' : l * |A| ≤ r := by
      nlinarith [mul_nonneg hl.le (abs_nonneg A), mul_nonneg hl.le (abs_nonneg B),
        mul_nonneg hl.le (abs_nonneg s)]
    have bB' : l * |B| ≤ r := by
      nlinarith [mul_nonneg hl.le (abs_nonneg A), mul_nonneg hl.le (abs_nonneg B),
        mul_nonneg hl.le (abs_nonneg s)]
    have bl' : l ≤ r := by
      nlinarith [mul_nonneg hl.le (abs_nonneg A), mul_nonneg hl.le (abs_nonneg B),
        mul_nonneg hl.le (abs_nonneg s)]
    have bs' : l * |s| ≤ r := by
      nlinarith [mul_nonneg hl.le (abs_nonneg A), mul_nonneg hl.le (abs_nonneg B),
        mul_nonneg hl.le (abs_nonneg s)]
    have bA : |t * (l * A)| ≤ r := by
      rw [abs_mul, abs_mul, abs_of_nonneg ht.1, abs_of_pos hl]
      have : t * (l * |A|) ≤ 1 * (l * |A|) :=
        mul_le_mul_of_nonneg_right ht.2 (mul_nonneg hl.le (abs_nonneg A))
      linarith
    have bB : |t * (l * B)| ≤ r := by
      rw [abs_mul, abs_mul, abs_of_nonneg ht.1, abs_of_pos hl]
      have : t * (l * |B|) ≤ 1 * (l * |B|) :=
        mul_le_mul_of_nonneg_right ht.2 (mul_nonneg hl.le (abs_nonneg B))
      linarith
    have bs : |l ^ 2 * s| ≤ r := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg l)]
      nlinarith [mul_nonneg hl.le (abs_nonneg s)]
    have e1 : t • (l • uu_STR02958 A B) + l • e3_STR02958 =
        ((t * (l * A), t * (l * B), l, 0) : Par_STR02916) := by
      simp [uu_STR02958, e3_STR02958]
    have e2 : t • (l • uu_STR02958 A B) + l • e3_STR02958 + (l ^ 2 * s) • e4_STR02958 =
        ((t * (l * A), t * (l * B), l, l ^ 2 * s) : Par_STR02916) := by
      simp [uu_STR02958, e3_STR02958, e4_STR02958]
    rw [e2, e1, mem_box_STR02958, mem_box_STR02958]
    refine ⟨⟨bA, bB, by rwa [abs_of_pos hl], by simpa using hr.le⟩, bA, bB,
      by rwa [abs_of_pos hl], bs⟩
  have hpU : ∀ l : ℝ, 0 < l → l ≤ δ' →
      ((0, 0, l, l ^ 2 * s) : Par_STR02916) ∈ U := by
    intro l hl hlδ
    have h0pt := (hmem l hl hlδ 0 ⟨le_rfl, zero_le_one⟩).2
    simp only [zero_smul, zero_add] at h0pt
    rw [comb2_STR02958] at h0pt
    exact hbox h0pt
  have hz : ∀ l : ℝ, 0 < l → l ≤ δ' →
      Fhat_STR02958 ψ (l • e3_STR02958 + (l ^ 2 * s) • e4_STR02958) = 0 := by
    intro l hl hlδ
    rw [comb2_STR02958]
    exact Fhat_zero_amp_STR02958 l (l ^ 2 * s) (hsl _ _ (hpU l hl hlδ))
  have hd : ∀ l : ℝ, 0 < l → l ≤ δ' →
      fderiv ℝ (Fhat_STR02958 ψ) (l • e3_STR02958 + (l ^ 2 * s) • e4_STR02958)
        (l • uu_STR02958 A B) = 0 := by
    intro l hl hlδ
    rw [comb2_STR02958, smul_uu_STR02958]
    exact fderiv_Fhat_ray_STR02958 hU hψ l (l ^ 2 * s) (hpU l hl hlδ)
      (hsl _ _ (hpU l hl hlδ)) (l * A) (l * B)
  have hF : ∀ l : ℝ, 0 < l → l ≤ δ' →
      |Fhat_STR02958 ψ (l • e3_STR02958 + (l ^ 2 * s) • e4_STR02958 + l • uu_STR02958 A B) -
        l ^ 4 * (Jred_STR02918 A B - 2 * s * ((A ^ 2 + B ^ 2) / 4))| ≤ M * l ^ 5 := by
    intro l hl hlδ
    have h1 := (hall A B s (Set.mem_singleton _) l
      (by rw [abs_of_pos hl]; exact hlδ.trans hδ'1)).2
    rw [abs_of_pos hl] at h1
    have e : l • e3_STR02958 + (l ^ 2 * s) • e4_STR02958 + l • uu_STR02958 A B =
        ((l * A, l * B, l, l ^ 2 * s) : Par_STR02916) := by
      rw [smul_uu_STR02958, comb_STR02958]
    have h2 : Fhat_STR02958 ψ ((l * A, l * B, l, l ^ 2 * s) : Par_STR02916) =
        Jchart_STR02950 l (l ^ 2 * s)
          (uT_STR02901 (l * A) (l * B)
            (vE_STR02957 (ψ ((l * A, l * B, l, l ^ 2 * s) : Par_STR02916)))) := rfl
    have h4 : poly19_STR02957 (l * A) (l * B) l (l ^ 2 * s) =
        l ^ 4 * (Jred_STR02918 A B - 2 * s * ((A ^ 2 + B ^ 2) / 4)) := by
      rw [poly19_scaled_STR02957]
      ring
    rw [e, h2, ← h4]
    exact h1
  exact jet_coeff'_STR02958 hU (Fhat_contDiffOn_STR02958 hψ) (box_convex_STR02958 r)
    (zero_mem_box_STR02958 hr.le) hbox e3_STR02958 e4_STR02958 (uu_STR02958 A B) s
    (Jred_STR02918 A B - 2 * s * ((A ^ 2 + B ^ 2) / 4)) norm_e3_STR02958 norm_e4_STR02958 N hN4 hN5
    δ' M hδ'pos hmem hz hd hF

/-- Homogeneity: the jet sum on the scaled ray is the weight-four polynomial. -/
theorem qsum_scaled_STR02958 {ψ : Par_STR02916 → E_STR02969}
    (hjet : ∀ A B s : ℝ,
      Q2_STR02958 (Fhat_STR02958 ψ) (uu_STR02958 A B) = 0 ∧
      Q3_STR02958 (Fhat_STR02958 ψ) e3_STR02958 (uu_STR02958 A B) 1 = 0 ∧
      Q4_STR02958 (Fhat_STR02958 ψ) e3_STR02958 e4_STR02958 (uu_STR02958 A B) 1 s =
        Jred_STR02918 A B - 2 * s * ((A ^ 2 + B ^ 2) / 4))
    (A B s h : ℝ) :
    Q2_STR02958 (Fhat_STR02958 ψ) (uu_STR02958 (h * A) (h * B)) +
      Q3_STR02958 (Fhat_STR02958 ψ) e3_STR02958 (uu_STR02958 (h * A) (h * B)) h +
      Q4_STR02958 (Fhat_STR02958 ψ) e3_STR02958 e4_STR02958 (uu_STR02958 (h * A) (h * B)) h
        (h ^ 2 * s) = poly19_STR02957 (h * A) (h * B) h (h ^ 2 * s) := by
  obtain ⟨j2, j3, j4⟩ := hjet A B s
  rw [← smul_uu_STR02958, Q2_smul_STR02958, Q3_smul_STR02958, Q4_smul_STR02958, j2, j3, j4,
    poly19_scaled_STR02957]
  ring

/-- For `h ≠ 0` the jet sum at `(a, b, h, γ)` is the weight-four polynomial. -/
theorem qsum_eq_STR02958 {ψ : Par_STR02916 → E_STR02969}
    (hjet : ∀ A B s : ℝ,
      Q2_STR02958 (Fhat_STR02958 ψ) (uu_STR02958 A B) = 0 ∧
      Q3_STR02958 (Fhat_STR02958 ψ) e3_STR02958 (uu_STR02958 A B) 1 = 0 ∧
      Q4_STR02958 (Fhat_STR02958 ψ) e3_STR02958 e4_STR02958 (uu_STR02958 A B) 1 s =
        Jred_STR02918 A B - 2 * s * ((A ^ 2 + B ^ 2) / 4))
    (a b h γ : ℝ) (hh : h ≠ 0) :
    Q2_STR02958 (Fhat_STR02958 ψ) (uu_STR02958 a b) +
      Q3_STR02958 (Fhat_STR02958 ψ) e3_STR02958 (uu_STR02958 a b) h +
      Q4_STR02958 (Fhat_STR02958 ψ) e3_STR02958 e4_STR02958 (uu_STR02958 a b) h γ =
        poly19_STR02957 a b h γ := by
  have key := qsum_scaled_STR02958 hjet (a / h) (b / h) (γ / h ^ 2) h
  have e1 : h * (a / h) = a := by field_simp
  have e2 : h * (b / h) = b := by field_simp
  have e3 : h ^ 2 * (γ / h ^ 2) = γ := by field_simp
  rw [e1, e2, e3] at key
  exact key

/-- The pointwise remainder bound with the amplitude factor, once the jet is identified. -/
theorem remainder_core_STR02958 {U : Set Par_STR02916} {ψ : Par_STR02916 → E_STR02969}
    (hU : IsOpen U) (hψ : ContDiffOn ℝ ∞ ψ U)
    (hsl : ∀ h γ : ℝ, ((0, 0, h, γ) : Par_STR02916) ∈ U → ψ (0, 0, h, γ) = 0)
    {r : ℝ} (hr : 0 < r) (hbox : box_STR02958 r ⊆ U) (M : ℝ)
    (hM4 : ∀ q ∈ box_STR02958 r, ‖iteratedFDeriv ℝ 4 (Fhat_STR02958 ψ) q‖ ≤ M)
    (hM5 : ∀ q ∈ box_STR02958 r, ‖iteratedFDeriv ℝ 5 (Fhat_STR02958 ψ) q‖ ≤ M)
    (a b h γ : ℝ) (hp : ((a, b, h, γ) : Par_STR02916) ∈ box_STR02958 r)
    (hq : Q2_STR02958 (Fhat_STR02958 ψ) (uu_STR02958 a b) +
      Q3_STR02958 (Fhat_STR02958 ψ) e3_STR02958 (uu_STR02958 a b) h +
      Q4_STR02958 (Fhat_STR02958 ψ) e3_STR02958 e4_STR02958 (uu_STR02958 a b) h γ =
        poly19_STR02957 a b h γ) :
    |Fred_STR02956 ψ (a, b) (h, γ) - poly19_STR02957 a b h γ| ≤
      M * R0_STR02918 a b ^ 2 *
        ((|h| + R0_STR02918 a b) ^ 3 + |γ| * (|h| + R0_STR02918 a b) + γ ^ 2) := by
  obtain ⟨ha, hb, hh, hγ⟩ := (mem_box_STR02958 r a b h γ).mp hp
  have hM : 0 ≤ M := (norm_nonneg _).trans (hM4 0 (zero_mem_box_STR02958 hr.le))
  have hpt : ((0, 0, h, γ) : Par_STR02916) ∈ box_STR02958 r :=
    (mem_box_STR02958 r 0 0 h γ).mpr ⟨by simpa using hr.le, by simpa using hr.le, hh, hγ⟩
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      t • uu_STR02958 a b + h • e3_STR02958 ∈ box_STR02958 r ∧
      t • uu_STR02958 a b + h • e3_STR02958 + γ • e4_STR02958 ∈ box_STR02958 r := by
    intro t ht
    have bA : |t * a| ≤ r := by
      rw [abs_mul, abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (abs_nonneg a) ht.2).trans ha
    have bB : |t * b| ≤ r := by
      rw [abs_mul, abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (abs_nonneg b) ht.2).trans hb
    have e1 : t • uu_STR02958 a b + h • e3_STR02958 =
        ((t * a, t * b, h, 0) : Par_STR02916) := by
      simp [uu_STR02958, e3_STR02958]
    have e2 : t • uu_STR02958 a b + h • e3_STR02958 + γ • e4_STR02958 =
        ((t * a, t * b, h, γ) : Par_STR02916) := by
      simp [uu_STR02958, e3_STR02958, e4_STR02958]
    rw [e2, e1, mem_box_STR02958, mem_box_STR02958]
    exact ⟨⟨bA, bB, hh, by simpa using hr.le⟩, bA, bB, hh, hγ⟩
  have hz : Fhat_STR02958 ψ (h • e3_STR02958 + γ • e4_STR02958) = 0 := by
    rw [comb2_STR02958]
    exact Fhat_zero_amp_STR02958 h γ (hsl h γ (hbox hpt))
  have hd : fderiv ℝ (Fhat_STR02958 ψ) (h • e3_STR02958 + γ • e4_STR02958)
      (uu_STR02958 a b) = 0 := by
    rw [comb2_STR02958]
    exact fderiv_Fhat_ray_STR02958 hU hψ h γ (hbox hpt) (hsl h γ (hbox hpt)) a b
  have key := taylor_rem'_STR02958 hU (Fhat_contDiffOn_STR02958 hψ) (box_convex_STR02958 r)
    (zero_mem_box_STR02958 hr.le) hbox e3_STR02958 e4_STR02958 (uu_STR02958 a b) h γ
    norm_e3_STR02958 norm_e4_STR02958 hmem hz hd M hM4 hM5
  rw [comb_STR02958, hq] at key
  have hn : ‖uu_STR02958 a b‖ ≤ R0_STR02918 a b := norm_uu_le_STR02958 a b
  have hfin : ‖uu_STR02958 a b‖ ^ 2 * (M * (|h| + ‖uu_STR02958 a b‖) ^ 3 +
      M * ((|h| + ‖uu_STR02958 a b‖ + |γ|) * |γ|)) ≤
      M * R0_STR02918 a b ^ 2 *
        ((|h| + R0_STR02918 a b) ^ 3 + |γ| * (|h| + R0_STR02918 a b) + γ ^ 2) := by
    have e : M * R0_STR02918 a b ^ 2 *
        ((|h| + R0_STR02918 a b) ^ 3 + |γ| * (|h| + R0_STR02918 a b) + γ ^ 2) =
        R0_STR02918 a b ^ 2 * (M * (|h| + R0_STR02918 a b) ^ 3 +
          M * ((|h| + R0_STR02918 a b + |γ|) * |γ|)) := by
      rw [← sq_abs γ]
      ring
    rw [e]
    gcongr
  exact key.trans hfin

/-- The remainder bound on the whole box, including `h = 0`, from the bound for `h ≠ 0`. -/
theorem remainder_all_STR02958 {U : Set Par_STR02916} {ψ : Par_STR02916 → E_STR02969}
    (hU : IsOpen U) (hψ : ContDiffOn ℝ ∞ ψ U) {r : ℝ} (hr : 0 < r)
    (hbox : box_STR02958 r ⊆ U) (M : ℝ)
    (hne : ∀ a b h γ : ℝ, ((a, b, h, γ) : Par_STR02916) ∈ box_STR02958 r → h ≠ 0 →
      |Fred_STR02956 ψ (a, b) (h, γ) - poly19_STR02957 a b h γ| ≤
        M * R0_STR02918 a b ^ 2 *
          ((|h| + R0_STR02918 a b) ^ 3 + |γ| * (|h| + R0_STR02918 a b) + γ ^ 2))
    (a b h γ : ℝ) (hp : ((a, b, h, γ) : Par_STR02916) ∈ box_STR02958 r) :
    |Fred_STR02956 ψ (a, b) (h, γ) - poly19_STR02957 a b h γ| ≤
      M * R0_STR02918 a b ^ 2 *
        ((|h| + R0_STR02918 a b) ^ 3 + |γ| * (|h| + R0_STR02918 a b) + γ ^ 2) := by
  by_cases hh : h = 0
  · subst hh
    have hpU : ((a, b, 0, γ) : Par_STR02916) ∈ U := hbox hp
    have hFc : ContinuousOn (Fhat_STR02958 ψ) U := (Fhat_contDiffOn_STR02958 hψ).continuousOn
    have hc1 : ContinuousAt (Fhat_STR02958 ψ)
        ((fun h' : ℝ => ((a, b, h', γ) : Par_STR02916)) 0) :=
      hFc.continuousAt (hU.mem_nhds hpU)
    have hcm : Continuous (fun h' : ℝ => ((a, b, h', γ) : Par_STR02916)) := by fun_prop
    have hφ : ContinuousAt (fun h' : ℝ => Fhat_STR02958 ψ ((a, b, h', γ) : Par_STR02916)) 0 :=
      ContinuousAt.comp (g := Fhat_STR02958 ψ) (f := fun h' : ℝ => ((a, b, h', γ) : Par_STR02916))
        hc1 hcm.continuousAt
    have hpoly : ContinuousAt (fun h' : ℝ => poly19_STR02957 a b h' γ) 0 :=
      Continuous.continuousAt (by unfold poly19_STR02957; fun_prop)
    have hg : ContinuousAt (fun h' : ℝ =>
        |Fhat_STR02958 ψ ((a, b, h', γ) : Par_STR02916) - poly19_STR02957 a b h' γ|) 0 :=
      (hφ.sub hpoly).abs
    have hk : ContinuousAt (fun h' : ℝ => M * R0_STR02918 a b ^ 2 *
        ((|h'| + R0_STR02918 a b) ^ 3 + |γ| * (|h'| + R0_STR02918 a b) + γ ^ 2)) 0 :=
      Continuous.continuousAt (by fun_prop)
    have hev : ∀ᶠ h' in nhdsWithin (0 : ℝ) {0}ᶜ,
        |Fhat_STR02958 ψ ((a, b, h', γ) : Par_STR02916) - poly19_STR02957 a b h' γ| ≤
          M * R0_STR02918 a b ^ 2 *
            ((|h'| + R0_STR02918 a b) ^ 3 + |γ| * (|h'| + R0_STR02918 a b) + γ ^ 2) := by
      have h1 : ∀ᶠ h' in nhdsWithin (0 : ℝ) {0}ᶜ, h' ∈ Metric.ball (0 : ℝ) r :=
        eventually_nhdsWithin_of_eventually_nhds (Metric.ball_mem_nhds 0 hr)
      filter_upwards [h1, self_mem_nhdsWithin] with h' hh1 hh2
      have hh1' : |h'| < r := by simpa using hh1
      have hmem : ((a, b, h', γ) : Par_STR02916) ∈ box_STR02958 r := by
        obtain ⟨ha, hb, _, hγ⟩ := (mem_box_STR02958 r a b 0 γ).mp hp
        exact (mem_box_STR02958 r a b h' γ).mpr ⟨ha, hb, hh1'.le, hγ⟩
      exact hne a b h' γ hmem hh2
    exact le_of_tendsto_of_tendsto (hg.tendsto.mono_left nhdsWithin_le_nhds)
      (hk.tendsto.mono_left nhdsWithin_le_nhds) hev
  · exact hne a b h γ hp hh

/-- Compactness of the box gives a single bound for the derivatives of order at most five. -/
theorem exists_bound_STR02958 {U : Set Par_STR02916} {ψ : Par_STR02916 → E_STR02969}
    (hU : IsOpen U) (hψ : ContDiffOn ℝ ∞ ψ U) {r : ℝ}
    (hbox : box_STR02958 r ⊆ U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ box_STR02958 r, ∀ k : ℕ, k ≤ 5 →
      ‖iteratedFDeriv ℝ k (Fhat_STR02958 ψ) p‖ ≤ M := by
  have hF := Fhat_contDiffOn_STR02958 hψ
  have hk : ∀ k : ℕ, ∃ C : ℝ, ∀ p ∈ box_STR02958 r,
      ‖iteratedFDeriv ℝ k (Fhat_STR02958 ψ) p‖ ≤ C := by
    intro k
    have h1 : ContinuousOn (iteratedFDerivWithin ℝ k (Fhat_STR02958 ψ) U) U :=
      hF.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hU.uniqueDiffOn
    have h2 : ContinuousOn (iteratedFDeriv ℝ k (Fhat_STR02958 ψ)) U :=
      h1.congr (fun p hp => (iteratedFDerivWithin_of_isOpen k hU hp).symm)
    obtain ⟨C, hC⟩ := (box_isCompact_STR02958 r).exists_bound_of_continuousOn (h2.mono hbox)
    exact ⟨C, hC⟩
  obtain ⟨C, hC⟩ := exists_bound_upto_STR02954 (box_STR02958 r)
    (fun k p => ‖iteratedFDeriv ℝ k (Fhat_STR02958 ψ) p‖) hk 5
  exact ⟨max C 0, le_max_right _ _, fun p hp k hk5 => (hC p hp k hk5).trans (le_max_left _ _)⟩

/-! ### Public statements -/

/-- The coordinate box is convex. -/
theorem str029_58_weighted_remainder_retaining_amplitude_factor_box_convex (r : ℝ) :
    Convex ℝ (box_STR02958 r) :=
  box_convex_STR02958 r

/-- The coordinate box is compact. -/
theorem str029_58_weighted_remainder_retaining_amplitude_factor_box_compact (r : ℝ) :
    IsCompact (box_STR02958 r) :=
  box_isCompact_STR02958 r

/-- Membership in the coordinate box is the four coordinatewise bounds. -/
theorem str029_58_weighted_remainder_retaining_amplitude_factor_mem_box
    (r a b h γ : ℝ) :
    ((a, b, h, γ) : Par_STR02916) ∈ box_STR02958 r ↔
      |a| ≤ r ∧ |b| ≤ r ∧ |h| ≤ r ∧ |γ| ≤ r :=
  mem_box_STR02958 r a b h γ

/-- For a smooth graph on an open set containing the box, the derivatives of the reduced
functional of order at most five are bounded by one constant on the box. -/
theorem str029_58_weighted_remainder_retaining_amplitude_factor_derivative_bound
    {U : Set Par_STR02916} {ψ : Par_STR02916 → E_STR02969}
    (hU : IsOpen U) (hψ : ContDiffOn ℝ ∞ ψ U) {r : ℝ} (hbox : box_STR02958 r ⊆ U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ box_STR02958 r, ∀ k : ℕ, k ≤ 5 →
      ‖iteratedFDeriv ℝ k (Fhat_STR02958 ψ) p‖ ≤ M :=
  exists_bound_STR02958 hU hψ hbox

/-- The weighted remainder retaining the amplitude factor: on a small closed convex box inside the
smoothness neighborhood, `F - poly19` is bounded by `M R0² ((|h| + R0)³ + |γ| (|h| + R0) + γ²)`,
where `M` bounds the operator norms of the derivatives of `F` of order at most five on the box. -/
theorem str029_58_weighted_remainder_retaining_amplitude_factor :
    ∃ (U : Set Par_STR02916) (V : Set E_STR02969) (ψ : Par_STR02916 → E_STR02969),
      IsOpen U ∧ (0 : Par_STR02916) ∈ U ∧ IsOpen V ∧ (0 : E_STR02969) ∈ V ∧
      ContDiffOn ℝ ∞ ψ U ∧ ψ 0 = 0 ∧ (∀ p ∈ U, ψ p ∈ V) ∧
      (∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p) ∧
      ∃ r : ℝ, 0 < r ∧ box_STR02958 r ⊆ U ∧
        (∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ box_STR02958 r, ∀ k : ℕ, k ≤ 5 →
          ‖iteratedFDeriv ℝ k (Fhat_STR02958 ψ) p‖ ≤ M) ∧
        ∀ M : ℝ, 0 ≤ M → (∀ p ∈ box_STR02958 r, ∀ k : ℕ, k ≤ 5 →
            ‖iteratedFDeriv ℝ k (Fhat_STR02958 ψ) p‖ ≤ M) →
          ∀ a b h γ : ℝ, ((a, b, h, γ) : Par_STR02916) ∈ box_STR02958 r →
            |Fred_STR02956 ψ (a, b) (h, γ) - poly19_STR02957 a b h γ| ≤
              M * R0_STR02918 a b ^ 2 *
                ((|h| + R0_STR02918 a b) ^ 3 + |γ| * (|h| + R0_STR02918 a b) + γ ^ 2) := by
  obtain ⟨U, V, ψ, hU, h0U, hV, h0V, hψ, hψ0, hψV, hiff, hK⟩ :=
    str029_57_weighted_fourth_jet_reduced_functional
  have hsl : ∀ h γ : ℝ, ((0, 0, h, γ) : Par_STR02916) ∈ U → ψ (0, 0, h, γ) = 0 :=
    fun h γ hp => slice_zero_STR02958 h0V hiff h γ hp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU 0 h0U
  have hr : 0 < ε / 2 := half_pos hε
  have hbox : box_STR02958 (ε / 2) ⊆ U := fun p hp =>
    hball (Metric.closedBall_subset_ball (half_lt_self hε) hp)
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_bound_STR02958 hU hψ hbox
  have hjet := jet_vanish_STR02958 hU hψ hsl hK hr hbox M₁
    (fun q hq => hM₁ q hq 4 (by norm_num)) (fun q hq => hM₁ q hq 5 (by norm_num))
  refine ⟨U, V, ψ, hU, h0U, hV, h0V, hψ, hψ0, hψV, hiff, ε / 2, hr, hbox,
    ⟨M₁, hM₁0, hM₁⟩, ?_⟩
  intro M _ hMb a b h γ hp
  refine remainder_all_STR02958 hU hψ hr hbox M ?_ a b h γ hp
  intro a' b' h' γ' hp' hh'
  exact remainder_core_STR02958 hU hψ hsl hr hbox M
    (fun q hq => hMb q hq 4 (by norm_num)) (fun q hq => hMb q hq 5 (by norm_num))
    a' b' h' γ' hp' (qsum_eq_STR02958 hjet a' b' h' γ' hh')

end DGPS.Frontier.STR029
