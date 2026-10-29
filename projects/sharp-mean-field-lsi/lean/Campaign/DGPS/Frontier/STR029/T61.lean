import DGPS.Frontier.STR029.T19

/-!
# STR029.61: Recover the scaled rate from the value equation

Task id: STR029.61 (node STR029, frontier unit). Title: Recover the scaled rate from the value
equation. Prerequisite: STR029.19 (the amplitude-factored unscaled expansion of the reduced
functional `Fred_STR02956`), through which the data of STR029.56 to STR029.58 enter.

Statement formalized. Let `F (a, b, h, γ) = Fred_STR02956 ψ (a, b) (h, γ)` and let `Q (A, B) =
2 J_4^red (A, B) / (A² + B²)`. Suppose `h n → 0`, `h n ≠ 0`, `γ n → 0`, `F (a n, b n, h n, γ n) = 0`,
all coordinates eventually lie in the coordinate neighbourhood (box) of STR029.19, and the Euclidean
distance from `(a n / h n, b n / h n)` to `{(2, 0), (-1, √3), (-1, -√3)}` tends to `0`. Then
`γ n = O (h n ^ 2)`, `γ n / h n ^ 2 - Q (a n / h n, b n / h n) → 0` and `γ n / h n ^ 2 → -16/15`.

Proof route. Eventually `1 ≤ A² + B² ≤ 9` for `(A, B) = (a n / h n, b n / h n)`, hence
`|h| ≤ R₀ ≤ 3 |h|` with `R₀ = √(a² + b²)`. Dividing the expansion of STR029.19 by `R₀²` gives
`|γ| ≤ Γ h²` with `Γ = 4 (71/80 + 64 M)` once `M (4 |h| + |γ|) ≤ 1/4` and `|h| ≤ 1`. Dividing again
by `h²` and using the scaled form of the polynomial (`poly19_scaled_STR02957`), the difference
`γ / h² - Q` is at most `2 M ((64 + 4 Γ) |h| + Γ² h²)` in absolute value. The value `-16/15` at the
three points follows from `A² + B² = 4` and `A³ - 3 A B² = 8` there, and from the continuity of the
rational function `Q` at each of them.

## Provides

* `DGPS.Frontier.STR029.str029_61_recover_scaled_rate_value_equation`: the main statement. It
  re-states the data of STR029.19 (`U`, `V`, `ψ`, a radius `r > 0` with the box `box_STR02958 r`, a
  finite derivative bound `M`), and for every sequence with the displayed hypotheses it gives
  `γ n = O (h n ^ 2)`, `γ n / h n ^ 2 - Q (a n / h n, b n / h n) → 0` and `γ n / h n ^ 2 → -16/15`.
* `DGPS.Frontier.STR029.str029_61_recover_scaled_rate_value_equation_Q_formula`: `Q` is, by
  definition, `2 J_4^red (A, B) / (A² + B²)` with `J_4^red = Jred_STR02918`.
* `DGPS.Frontier.STR029.str029_61_recover_scaled_rate_value_equation_Q_minimizers`: `Q` takes the
  value `-16/15` at each of the three points `(2, 0)`, `(-1, √3)`, `(-1, -√3)`.
* `DGPS.Frontier.STR029.plane_STR02961`: the point `(A, B)` of the Euclidean plane
  `EuclideanSpace ℝ (Fin 2)`.
* `DGPS.Frontier.STR029.minimizers_STR02961`: the three-point set in the Euclidean plane.
* `DGPS.Frontier.STR029.pts_STR02961`: the same three points as pairs of reals.
* `DGPS.Frontier.STR029.Qrate_STR02961`: the scaled rate quotient `Q`.

The remaining declarations carry the suffix `_STR02961` and are helpers: the geometry of the
three-point set, the continuity estimate for `Q`, the absorption estimate `|γ| ≤ Γ h²`, the bound on
`γ / h² - Q`, and the sequence statement from which the main theorem follows.

## R5 notes

1. Data and neighbourhood. "The neighbourhood of .19" is read as the closed sup-norm box
   `box_STR02958 r` of STR029.19. As in STR029.19 and STR029.58 the data `U`, `V`, `ψ`, `r` are
   quantified existentially in the statement (properties as in STR029.19, including
   `box_STR02958 r ⊆ U` and `box_STR02958 r ∈ nhds 0`), followed by a finite `M ≥ 0` that bounds the
   operator norms of the derivatives of `Fhat_STR02958 ψ` through order five on the box, and then
   the statement about all sequences. The box is the one supplied by STR029.19, not an arbitrary
   neighbourhood. The conjunct on `M` is carried so that `M` is the derivative bound; the constant
   in `O (h n ^ 2)` is `Γ = 4 (71/80 + 64 M)`, as in the proof sketch, and depends on nothing else.
2. The functional. `F` is `Fred_STR02956 ψ (a, b) (h, γ)` with the variational range graph `ψ` of
   STR029.57. The Euler range map is not used and nothing is assumed about a relation between it and
   the variational range map. The common optimizer-chart predicate, the weighted carriers and the
   AbsoluteDensity domain enter only through `Jchart_STR02950` and `E_STR02969` as fixed by the
   prerequisites; their identification with `ordinaryEntropy`, `ordinaryFisher` and
   `AbsoluteDensity 1` is not part of this unit. The angular normalization `dt/(2π)` of the
   prerequisites is kept, with no rescaling by `a₀ = 4π²`; `γ` is the unscaled coordinate and
   `γ / h²` is the scaled rate.
3. Sequences. Sequences are indexed by `ℕ` and limits are along `atTop`. The hypotheses `h n ≠ 0`
   and `F (a n, b n, h n, γ n) = 0` are required only eventually (a tail of the sequence), which is
   weaker as a hypothesis than "for all `n`" and so gives a stronger statement; the same holds for
   the membership in the box, which is "eventually" in the specification. At indices with `h n = 0`
   the quotients `a n / h n` take the junk value of division by zero, which does not affect any
   tail statement.
4. `O (h n ^ 2)`. The conclusion `γ n = O (h n ^ 2)` is `Asymptotics.IsBigO atTop γ (fun n => h n ^ 2)`.
5. Euclidean distance. The distance from `(a n / h n, b n / h n)` to the set
   `{(2, 0), (-1, √3), (-1, -√3)}` is read as `Metric.infDist` in `EuclideanSpace ℝ (Fin 2)`
   (the `L²` metric) to `minimizers_STR02961`, and it is required to tend to `0`. Since the set is
   finite, this is equivalent to the distance to the nearest of the three points tending to `0`.
6. The quotient `Q`. `Q (A, B) = 2 J_4^red (A, B) / (A² + B²)` is `Qrate_STR02961`, with
   `J_4^red = Jred_STR02918 = R₀⁴/48 - P₃/12 - 9 R₀²/20` of STR029.18, the coefficient that
   STR029.57 identifies with the scaled form of the polynomial of STR029.19. The specification
   defines `Q` for nonzero `(A, B)`; in Lean the quotient at `(0, 0)` is the junk value `0`, which is
   never used because the distance hypothesis keeps `(A, B)` away from the origin eventually.
7. The estimates. Eventually the distance is below `1/2`, which gives `1 ≤ A² + B² ≤ 9` and so
   `1 ≤ R₀ / |h| ≤ 3`. The bound `|E| ≤ M R₀² ((|h| + R₀)³ + |γ| (|h| + R₀) + γ²)` of STR029.19 is
   used with that same `M`. The cubic invariant satisfies `|a³ - 3 a b²| ≤ R₀³`, which is what gives
   the contribution `(1/12) |h| R₀³` in the proof sketch.
8. No added hypothesis. The vanishing of the polynomial remainder at zero amplitude and the
   expansion itself come from STR029.19; none is a hypothesis here. The hypotheses are exactly those
   of the specification, in the readings above.
9. Library facts. The unit uses elementary limits of sequences and the continuity of an explicit
   rational function; these are proved here from the Mathlib API at the pin and are not assumed.
-/

open scoped ContDiff
open Filter Topology

namespace DGPS.Frontier.STR029

/-! ### The plane, the minimizer set and the scaled rate quotient -/

/-- The point `(A, B)` of the Euclidean plane `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def plane_STR02961 (A B : ℝ) : EuclideanSpace ℝ (Fin 2) := !₂[A, B]

/-- The set `{(2, 0), (-1, √3), (-1, -√3)}` of the three scaled minimizers, in the Euclidean plane. -/
noncomputable def minimizers_STR02961 : Set (EuclideanSpace ℝ (Fin 2)) :=
  {plane_STR02961 2 0, plane_STR02961 (-1) (Real.sqrt 3), plane_STR02961 (-1) (-Real.sqrt 3)}

/-- The same three points as coordinate pairs. -/
noncomputable def pts_STR02961 : Set (ℝ × ℝ) :=
  {(2, 0), (-1, Real.sqrt 3), (-1, -Real.sqrt 3)}

/-- The scaled rate quotient `Q(A, B) = 2 J_4^red(A, B) / (A² + B²)`. -/
noncomputable def Qrate_STR02961 (A B : ℝ) : ℝ :=
  2 * Jred_STR02918 A B / (A ^ 2 + B ^ 2)

theorem plane_dist_STR02961 (A B x y : ℝ) :
    dist (plane_STR02961 A B) (plane_STR02961 x y) = Real.sqrt ((A - x) ^ 2 + (B - y) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp [plane_STR02961, Real.dist_eq, sq_abs]

theorem near_STR02961 (A B δ : ℝ) (hδ : 0 < δ)
    (h : Metric.infDist (plane_STR02961 A B) minimizers_STR02961 < δ) :
    ∃ p ∈ pts_STR02961, (A - p.1) ^ 2 + (B - p.2) ^ 2 < δ ^ 2 := by
  have hne : minimizers_STR02961.Nonempty := ⟨plane_STR02961 2 0, by simp [minimizers_STR02961]⟩
  obtain ⟨y, hy, hd⟩ := (Metric.infDist_lt_iff hne).1 h
  simp only [minimizers_STR02961, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl
  · refine ⟨(2, 0), by simp [pts_STR02961], ?_⟩
    rw [plane_dist_STR02961, Real.sqrt_lt' hδ] at hd
    simpa using hd
  · refine ⟨(-1, Real.sqrt 3), by simp [pts_STR02961], ?_⟩
    rw [plane_dist_STR02961, Real.sqrt_lt' hδ] at hd
    simpa using hd
  · refine ⟨(-1, -Real.sqrt 3), by simp [pts_STR02961], ?_⟩
    rw [plane_dist_STR02961, Real.sqrt_lt' hδ] at hd
    simpa using hd

theorem pts_props_STR02961 (p : ℝ × ℝ) (hp : p ∈ pts_STR02961) :
    p.1 ^ 2 + p.2 ^ 2 = 4 ∧ p.1 ^ 3 - 3 * p.1 * p.2 ^ 2 = 8 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [pts_STR02961, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · norm_num
  · simp only [neg_sq, h3]; constructor <;> nlinarith [h3]
  · simp only [neg_sq, h3]; constructor <;> nlinarith [h3]

theorem Qrate_eq_STR02961 (A B : ℝ) :
    Qrate_STR02961 A B =
      2 * ((A ^ 2 + B ^ 2) ^ 2 / 48 - (A ^ 3 - 3 * A * B ^ 2) / 12 - 9 * (A ^ 2 + B ^ 2) / 20) /
        (A ^ 2 + B ^ 2) := by
  rw [Qrate_STR02961, Jred_eq_STR02918]

theorem Qrate_pts_STR02961 (p : ℝ × ℝ) (hp : p ∈ pts_STR02961) :
    Qrate_STR02961 p.1 p.2 = -16 / 15 := by
  obtain ⟨h1, h2⟩ := pts_props_STR02961 p hp
  rw [Qrate_eq_STR02961, h1, h2]
  norm_num

theorem Qrate_continuousAt_STR02961 (p : ℝ × ℝ) (hp : p.1 ^ 2 + p.2 ^ 2 ≠ 0) :
    ContinuousAt (fun q : ℝ × ℝ => Qrate_STR02961 q.1 q.2) p := by
  simp only [Qrate_eq_STR02961]
  exact ContinuousAt.div (by fun_prop) (by fun_prop) hp

theorem Q_near_STR02961 (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A B : ℝ, Metric.infDist (plane_STR02961 A B) minimizers_STR02961 < δ →
      |Qrate_STR02961 A B + 16 / 15| < ε := by
  have key : ∀ p ∈ pts_STR02961, ∃ δ : ℝ, 0 < δ ∧ ∀ A B : ℝ,
      (A - p.1) ^ 2 + (B - p.2) ^ 2 < δ ^ 2 → |Qrate_STR02961 A B + 16 / 15| < ε := by
    intro p hp
    have hcont := Qrate_continuousAt_STR02961 p (by rw [(pts_props_STR02961 p hp).1]; norm_num)
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hcont ε hε
    refine ⟨δ, hδ, fun A B hAB => ?_⟩
    have hA : |A - p.1| < δ :=
      abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg (B - p.2)]) hδ.le
    have hB : |B - p.2| < δ :=
      abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg (A - p.1)]) hδ.le
    have hd : dist ((A, B) : ℝ × ℝ) p < δ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_lt hA hB
    have := hball hd
    rw [Real.dist_eq, Qrate_pts_STR02961 p hp] at this
    have e : Qrate_STR02961 A B + 16 / 15 = Qrate_STR02961 A B - (-16 / 15) := by ring
    rw [e]
    exact this
  obtain ⟨δ1, hδ1, h1⟩ := key (2, 0) (by simp [pts_STR02961])
  obtain ⟨δ2, hδ2, h2⟩ := key (-1, Real.sqrt 3) (by simp [pts_STR02961])
  obtain ⟨δ3, hδ3, h3⟩ := key (-1, -Real.sqrt 3) (by simp [pts_STR02961])
  have hpos : 0 < min δ1 (min δ2 δ3) := lt_min hδ1 (lt_min hδ2 hδ3)
  refine ⟨min δ1 (min δ2 δ3), hpos, fun A B hAB => ?_⟩
  obtain ⟨p, hp, hd⟩ := near_STR02961 A B _ hpos hAB
  have hm1 : min δ1 (min δ2 δ3) ^ 2 ≤ δ1 ^ 2 :=
    pow_le_pow_left₀ hpos.le (min_le_left _ _) 2
  have hm2 : min δ1 (min δ2 δ3) ^ 2 ≤ δ2 ^ 2 :=
    pow_le_pow_left₀ hpos.le ((min_le_right _ _).trans (min_le_left _ _)) 2
  have hm3 : min δ1 (min δ2 δ3) ^ 2 ≤ δ3 ^ 2 :=
    pow_le_pow_left₀ hpos.le ((min_le_right _ _).trans (min_le_right _ _)) 2
  simp only [pts_STR02961, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact h1 A B (lt_of_lt_of_le hd hm1)
  · exact h2 A B (lt_of_lt_of_le hd hm2)
  · exact h3 A B (lt_of_lt_of_le hd hm3)

theorem near_bounds_STR02961 (A B : ℝ)
    (h : Metric.infDist (plane_STR02961 A B) minimizers_STR02961 < 1 / 2) :
    1 ≤ A ^ 2 + B ^ 2 ∧ A ^ 2 + B ^ 2 ≤ 9 := by
  obtain ⟨p, hp, hd⟩ := near_STR02961 A B _ (by norm_num) h
  obtain ⟨h1, -⟩ := pts_props_STR02961 p hp
  have hcs : (p.1 * (A - p.1) + p.2 * (B - p.2)) ^ 2 ≤ 4 * ((A - p.1) ^ 2 + (B - p.2) ^ 2) := by
    nlinarith [sq_nonneg (p.1 * (B - p.2) - p.2 * (A - p.1))]
  have hlt : (p.1 * (A - p.1) + p.2 * (B - p.2)) ^ 2 < 1 := by nlinarith
  have habs : |p.1 * (A - p.1) + p.2 * (B - p.2)| < 1 :=
    abs_lt_of_sq_lt_sq (by simpa using hlt) zero_le_one
  obtain ⟨hl, hu⟩ := abs_lt.1 habs
  constructor <;> nlinarith [sq_nonneg (A - p.1), sq_nonneg (B - p.2)]

/-! ### Pointwise estimates -/

theorem P3_le_STR02961 (a b : ℝ) : |a ^ 3 - 3 * a * b ^ 2| ≤ R0_STR02918 a b ^ 3 := by
  have h2 := R0_sq_STR02918 a b
  have hsq : (a ^ 3 - 3 * a * b ^ 2) ^ 2 ≤ (R0_STR02918 a b ^ 3) ^ 2 := by
    have e : (R0_STR02918 a b ^ 3) ^ 2 = (a ^ 2 + b ^ 2) ^ 3 := by
      rw [← h2]; ring
    rw [e]
    nlinarith [sq_nonneg (3 * a ^ 2 * b - b ^ 3)]
  exact abs_le_of_sq_le_sq hsq (pow_nonneg (Real.sqrt_nonneg _) 3)

theorem gamma_bound_STR02961 (M a b h γ E : ℝ) (hM : 0 ≤ M) (hh0 : h ≠ 0)
    (hF : poly19_STR02957 a b h γ + E = 0)
    (hE : |E| ≤ M * R0_STR02918 a b ^ 2 *
      ((|h| + R0_STR02918 a b) ^ 3 + |γ| * (|h| + R0_STR02918 a b) + γ ^ 2))
    (hR1 : |h| ≤ R0_STR02918 a b) (hR3 : R0_STR02918 a b ≤ 3 * |h|)
    (hsmall : M * (4 * |h| + |γ|) ≤ 1 / 4) (hh1 : |h| ≤ 1) :
    |γ| ≤ 4 * (71 / 80 + 64 * M) * h ^ 2 := by
  have hP3 := P3_le_STR02961 a b
  unfold poly19_STR02957 at hF
  generalize R0_STR02918 a b = R at hP3 hF hE hR1 hR3
  have hhpos : 0 < |h| := abs_pos.mpr hh0
  have hRpos : 0 < R := lt_of_lt_of_le hhpos hR1
  have hR2pos : 0 < R ^ 2 := pow_pos hRpos 2
  have hsqh : |h| ^ 2 = h ^ 2 := sq_abs h
  generalize hX : h * (a ^ 3 - 3 * a * b ^ 2) = X at hF
  have hXabs : |X| ≤ |h| * R ^ 3 := by
    rw [← hX, abs_mul]
    exact mul_le_mul_of_nonneg_left hP3 (abs_nonneg h)
  generalize hK : (|h| + R) ^ 3 + |γ| * (|h| + R) + γ ^ 2 = K at hE
  have hKnn : 0 ≤ K := by rw [← hK]; positivity
  have hh2R : 0 ≤ h ^ 2 * R ^ 2 := by positivity
  have hR4 : 0 ≤ R ^ 4 := by positivity
  have hEle := le_abs_self E
  have hEge := neg_abs_le E
  have hXle := le_abs_self X
  have hXge := neg_abs_le X
  have h2 : |γ| * R ^ 2 / 2 ≤
      9 * h ^ 2 * R ^ 2 / 20 + |h| * R ^ 3 / 12 + R ^ 4 / 48 + M * R ^ 2 * K := by
    rcases abs_cases γ with ⟨hg, _⟩ | ⟨hg, _⟩
    · rw [hg]
      linarith
    · rw [hg]
      linarith
  have h2' : R ^ 2 * (|γ| / 2) ≤
      R ^ 2 * (9 * h ^ 2 / 20 + |h| * R / 12 + R ^ 2 / 48 + M * K) := by
    linarith
  have h3 : |γ| / 2 ≤ 9 * h ^ 2 / 20 + |h| * R / 12 + R ^ 2 / 48 + M * K :=
    le_of_mul_le_mul_left h2' hR2pos
  have hhR : |h| * R ≤ 3 * h ^ 2 := by
    have := mul_le_mul_of_nonneg_left hR3 (abs_nonneg h)
    linarith
  have hR2 : R ^ 2 ≤ 9 * h ^ 2 := by
    have := pow_le_pow_left₀ hRpos.le hR3 2
    rw [mul_pow, hsqh] at this
    linarith
  have hsum : |h| + R ≤ 4 * |h| := by linarith
  have hcube : (|h| + R) ^ 3 ≤ 64 * |h| ^ 3 := by
    have := pow_le_pow_left₀ (by positivity) hsum 3
    rw [mul_pow] at this
    linarith
  have hK2 : K ≤ 64 * |h| ^ 3 + |γ| * (4 * |h| + |γ|) := by
    have h1 : |γ| * (|h| + R) ≤ |γ| * (4 * |h|) := mul_le_mul_of_nonneg_left hsum (abs_nonneg γ)
    have h2 : γ ^ 2 = |γ| * |γ| := by rw [← sq_abs γ]; ring
    linarith
  have hMK : M * K ≤ 64 * M * |h| ^ 3 + |γ| / 4 := by
    calc M * K ≤ M * (64 * |h| ^ 3 + |γ| * (4 * |h| + |γ|)) :=
          mul_le_mul_of_nonneg_left hK2 hM
      _ = 64 * M * |h| ^ 3 + |γ| * (M * (4 * |h| + |γ|)) := by ring
      _ ≤ 64 * M * |h| ^ 3 + |γ| * (1 / 4) := by
          gcongr
      _ = 64 * M * |h| ^ 3 + |γ| / 4 := by ring
  have h13 : |h| ^ 3 ≤ h ^ 2 := by
    have : |h| ^ 3 = |h| * |h| ^ 2 := by ring
    rw [this, hsqh]
    exact mul_le_of_le_one_left (sq_nonneg h) hh1
  have hM13 : 64 * M * |h| ^ 3 ≤ 64 * M * h ^ 2 := by
    exact mul_le_mul_of_nonneg_left h13 (by positivity)
  linarith

theorem scaled_core_STR02961 (M h A B s E Γ : ℝ) (hM : 0 ≤ M) (hh0 : h ≠ 0)
    (hF : poly19_STR02957 (h * A) (h * B) h (h ^ 2 * s) + E = 0)
    (hE : |E| ≤ M * R0_STR02918 (h * A) (h * B) ^ 2 *
      ((|h| + R0_STR02918 (h * A) (h * B)) ^ 3 + |h ^ 2 * s| * (|h| + R0_STR02918 (h * A) (h * B)) +
        (h ^ 2 * s) ^ 2))
    (hR1 : |h| ≤ R0_STR02918 (h * A) (h * B)) (hR3 : R0_STR02918 (h * A) (h * B) ≤ 3 * |h|)
    (hΓ : |h ^ 2 * s| ≤ Γ * h ^ 2) (hΓ0 : 0 ≤ Γ) :
    |s - Qrate_STR02961 A B| ≤ 2 * M * ((64 + 4 * Γ) * |h| + Γ ^ 2 * h ^ 2) := by
  have hs := poly19_scaled_STR02957 A B s h
  rw [hs] at hF
  have hRD : R0_STR02918 (h * A) (h * B) ^ 2 = h ^ 2 * (A ^ 2 + B ^ 2) := by
    rw [R0_sq_STR02918]; ring
  generalize R0_STR02918 (h * A) (h * B) = R at hRD hE hR1 hR3
  have hhpos : 0 < |h| := abs_pos.mpr hh0
  have hh2pos : 0 < h ^ 2 := by positivity
  have hRpos : 0 < R := lt_of_lt_of_le hhpos hR1
  have hsqh : |h| ^ 2 = h ^ 2 := sq_abs h
  have hD1 : 1 ≤ A ^ 2 + B ^ 2 := by
    have h1 : |h| ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hhpos.le hR1 2
    rw [hRD, hsqh] at h1
    by_contra hlt
    have hlt' := not_le.mp hlt
    nlinarith
  have hDpos : 0 < A ^ 2 + B ^ 2 := by linarith
  generalize hDdef : A ^ 2 + B ^ 2 = D at hRD hD1 hDpos hF
  have hh4D : 0 < h ^ 4 * D := by positivity
  have hEeq : E = h ^ 4 * s * D / 2 - h ^ 4 * Jred_STR02918 A B := by
    linear_combination hF
  have hQ : Qrate_STR02961 A B = 2 * Jred_STR02918 A B / D := by
    rw [Qrate_STR02961, hDdef]
  have hid : s - Qrate_STR02961 A B = 2 * E / (h ^ 4 * D) := by
    rw [hQ, hEeq]
    field_simp
  -- bound on the bracket
  have hsum : |h| + R ≤ 4 * |h| := by linarith
  have hcube : (|h| + R) ^ 3 ≤ 64 * |h| ^ 3 := by
    have := pow_le_pow_left₀ (by positivity) hsum 3
    rw [mul_pow] at this
    linarith
  have hg1 : |h ^ 2 * s| * (|h| + R) ≤ Γ * h ^ 2 * (4 * |h|) :=
    mul_le_mul hΓ hsum (by positivity) (by positivity)
  have hg2 : (h ^ 2 * s) ^ 2 ≤ (Γ * h ^ 2) ^ 2 := by
    rw [← sq_abs (h ^ 2 * s)]
    exact pow_le_pow_left₀ (abs_nonneg _) hΓ 2
  have hh3 : |h| ^ 3 = h ^ 2 * |h| := by rw [← hsqh]; ring
  have hK : (|h| + R) ^ 3 + |h ^ 2 * s| * (|h| + R) + (h ^ 2 * s) ^ 2 ≤
      h ^ 2 * ((64 + 4 * Γ) * |h| + Γ ^ 2 * h ^ 2) := by
    nlinarith [hcube, hg1, hg2, hh3]
  have hE2 : |E| ≤ M * (h ^ 2 * D) * (h ^ 2 * ((64 + 4 * Γ) * |h| + Γ ^ 2 * h ^ 2)) := by
    rw [hRD] at hE
    refine hE.trans ?_
    exact mul_le_mul_of_nonneg_left hK (by positivity)
  rw [hid, abs_div, abs_mul, abs_of_pos hh4D, div_le_iff₀ hh4D]
  have : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
  rw [this]
  nlinarith [hE2]

theorem pointwise_STR02961 (M a b h γ E : ℝ) (hM : 0 ≤ M) (hh0 : h ≠ 0)
    (hF : poly19_STR02957 a b h γ + E = 0)
    (hE : |E| ≤ M * R0_STR02918 a b ^ 2 *
      ((|h| + R0_STR02918 a b) ^ 3 + |γ| * (|h| + R0_STR02918 a b) + γ ^ 2))
    (hR1 : |h| ≤ R0_STR02918 a b) (hR3 : R0_STR02918 a b ≤ 3 * |h|)
    (hsmall : M * (4 * |h| + |γ|) ≤ 1 / 4) (hh1 : |h| ≤ 1) :
    |γ| ≤ 4 * (71 / 80 + 64 * M) * h ^ 2 ∧
      |γ / h ^ 2 - Qrate_STR02961 (a / h) (b / h)| ≤
        2 * M * ((64 + 4 * (4 * (71 / 80 + 64 * M))) * |h| +
          (4 * (71 / 80 + 64 * M)) ^ 2 * h ^ 2) := by
  have hg := gamma_bound_STR02961 M a b h γ E hM hh0 hF hE hR1 hR3 hsmall hh1
  refine ⟨hg, ?_⟩
  have hΓ0 : 0 ≤ 4 * (71 / 80 + 64 * M) := by positivity
  have ha : h * (a / h) = a := by field_simp
  have hb : h * (b / h) = b := by field_simp
  have hc : h ^ 2 * (γ / h ^ 2) = γ := by field_simp
  exact scaled_core_STR02961 M h (a / h) (b / h) (γ / h ^ 2) E (4 * (71 / 80 + 64 * M)) hM hh0
    (by rw [ha, hb, hc]; exact hF) (by rw [ha, hb, hc]; exact hE) (by rw [ha, hb]; exact hR1)
    (by rw [ha, hb]; exact hR3) (by rw [hc]; exact hg) hΓ0

theorem ray_bounds_STR02961 (a b h : ℝ) (hh0 : h ≠ 0)
    (hd : Metric.infDist (plane_STR02961 (a / h) (b / h)) minimizers_STR02961 < 1 / 2) :
    |h| ≤ R0_STR02918 a b ∧ R0_STR02918 a b ≤ 3 * |h| := by
  obtain ⟨h1, h9⟩ := near_bounds_STR02961 _ _ hd
  have hRD : R0_STR02918 a b ^ 2 = h ^ 2 * ((a / h) ^ 2 + (b / h) ^ 2) := by
    rw [R0_sq_STR02918]; field_simp
  have hR0 : 0 ≤ R0_STR02918 a b := Real.sqrt_nonneg _
  have hh2 : 0 ≤ h ^ 2 := sq_nonneg h
  constructor
  · apply abs_le_of_sq_le_sq _ hR0
    rw [hRD]
    nlinarith [mul_le_mul_of_nonneg_left h1 hh2]
  · have : |R0_STR02918 a b| ≤ |3 * h| := by
      apply abs_le_of_sq_le_sq _ (abs_nonneg _)
      rw [hRD, sq_abs]
      nlinarith [mul_le_mul_of_nonneg_left h9 hh2]
    rw [abs_of_nonneg hR0, abs_mul] at this
    simpa using this

/-! ### The sequence statement -/

theorem seq_core_STR02961 (M : ℝ) (hM : 0 ≤ M) (a b h γ E : ℕ → ℝ)
    (hh : Tendsto h atTop (𝓝 0)) (hγ : Tendsto γ atTop (𝓝 0))
    (hh0 : ∀ᶠ n in atTop, h n ≠ 0)
    (hF : ∀ᶠ n in atTop, poly19_STR02957 (a n) (b n) (h n) (γ n) + E n = 0)
    (hE : ∀ᶠ n in atTop, |E n| ≤ M * R0_STR02918 (a n) (b n) ^ 2 *
      ((|h n| + R0_STR02918 (a n) (b n)) ^ 3 + |γ n| * (|h n| + R0_STR02918 (a n) (b n)) +
        γ n ^ 2))
    (hd : Tendsto (fun n => Metric.infDist (plane_STR02961 (a n / h n) (b n / h n))
      minimizers_STR02961) atTop (𝓝 0)) :
    Asymptotics.IsBigO atTop γ (fun n => h n ^ 2) ∧
      Tendsto (fun n => γ n / h n ^ 2 - Qrate_STR02961 (a n / h n) (b n / h n)) atTop (𝓝 0) ∧
      Tendsto (fun n => γ n / h n ^ 2) atTop (𝓝 (-16 / 15)) := by
  set Γ : ℝ := 4 * (71 / 80 + 64 * M) with hΓdef
  have hdist : ∀ᶠ n in atTop,
      Metric.infDist (plane_STR02961 (a n / h n) (b n / h n)) minimizers_STR02961 < 1 / 2 :=
    hd.eventually (eventually_lt_nhds (by norm_num))
  have hsmallT : Tendsto (fun n => M * (4 * |h n| + |γ n|)) atTop (𝓝 0) := by
    have := ((hh.abs.const_mul 4).add hγ.abs).const_mul M
    simpa using this
  have hsmall : ∀ᶠ n in atTop, M * (4 * |h n| + |γ n|) < 1 / 4 :=
    hsmallT.eventually (eventually_lt_nhds (by norm_num))
  have hh1 : ∀ᶠ n in atTop, |h n| < 1 := by
    have := hh.abs
    rw [abs_zero] at this
    exact this.eventually (eventually_lt_nhds (by norm_num))
  have hpt : ∀ᶠ n in atTop, |γ n| ≤ Γ * h n ^ 2 ∧
      |γ n / h n ^ 2 - Qrate_STR02961 (a n / h n) (b n / h n)| ≤
        2 * M * ((64 + 4 * Γ) * |h n| + Γ ^ 2 * h n ^ 2) := by
    filter_upwards [hh0, hF, hE, hdist, hsmall, hh1] with n hn0 hFn hEn hdn hsn h1n
    obtain ⟨hR1, hR3⟩ := ray_bounds_STR02961 (a n) (b n) (h n) hn0 hdn
    exact pointwise_STR02961 M (a n) (b n) (h n) (γ n) (E n) hM hn0 hFn hEn hR1 hR3 hsn.le
      h1n.le
  have hbig : Asymptotics.IsBigO atTop γ (fun n => h n ^ 2) := by
    refine Asymptotics.IsBigO.of_bound Γ ?_
    filter_upwards [hpt] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (h n))]
    exact hn.1
  have hdiff : Tendsto
      (fun n => γ n / h n ^ 2 - Qrate_STR02961 (a n / h n) (b n / h n)) atTop (𝓝 0) := by
    have hbound : Tendsto (fun n => 2 * M * ((64 + 4 * Γ) * |h n| + Γ ^ 2 * h n ^ 2)) atTop
        (𝓝 0) := by
      have h1 := (hh.abs.const_mul (64 + 4 * Γ)).add ((hh.pow 2).const_mul (Γ ^ 2))
      have h2 := h1.const_mul (2 * M)
      simpa using h2
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hpt] with n hn
    rw [Real.norm_eq_abs]
    exact hn.2
  have hQ : Tendsto (fun n => Qrate_STR02961 (a n / h n) (b n / h n)) atTop (𝓝 (-16 / 15)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hQδ⟩ := Q_near_STR02961 ε hε
    filter_upwards [hd.eventually (eventually_lt_nhds hδ)] with n hn
    rw [Real.dist_eq]
    have := hQδ _ _ hn
    have e : Qrate_STR02961 (a n / h n) (b n / h n) - -16 / 15 =
        Qrate_STR02961 (a n / h n) (b n / h n) + 16 / 15 := by ring
    rw [e]
    exact this
  refine ⟨hbig, hdiff, ?_⟩
  have := hdiff.add hQ
  rw [zero_add] at this
  exact this.congr (fun n => by ring)

/-- `Q` is, by definition, `2 J_4^red (A, B) / (A² + B²)`. -/
theorem str029_61_recover_scaled_rate_value_equation_Q_formula (A B : ℝ) :
    Qrate_STR02961 A B = 2 * Jred_STR02918 A B / (A ^ 2 + B ^ 2) :=
  rfl

/-- `Q` takes the value `-16/15` at each of the three points `(2, 0)`, `(-1, √3)`, `(-1, -√3)`. -/
theorem str029_61_recover_scaled_rate_value_equation_Q_minimizers (p : ℝ × ℝ)
    (hp : p ∈ pts_STR02961) : Qrate_STR02961 p.1 p.2 = -16 / 15 :=
  Qrate_pts_STR02961 p hp

/-- STR029.61: the scaled rate from the value equation. With the data and the coordinate box of
STR029.19 (and a finite bound `M` of the derivatives of `F` through order five on the box), every
sequence `(a n, b n, h n, γ n)` with `h n → 0`, `h n ≠ 0` eventually, `γ n → 0`, `F = 0`
eventually, eventually in the box, and with the scaled point `(a n / h n, b n / h n)` approaching
the three points `(2, 0)`, `(-1, ±√3)` in the Euclidean distance, satisfies `γ n = O(h n ^ 2)`,
`γ n / h n ^ 2 - Q (a n / h n, b n / h n) → 0` and `γ n / h n ^ 2 → -16/15`. -/
theorem str029_61_recover_scaled_rate_value_equation :
    ∃ (U : Set Par_STR02916) (V : Set E_STR02969) (ψ : Par_STR02916 → E_STR02969),
      IsOpen U ∧ (0 : Par_STR02916) ∈ U ∧ IsOpen V ∧ (0 : E_STR02969) ∈ V ∧
      ContDiffOn ℝ ∞ ψ U ∧ ψ 0 = 0 ∧ (∀ p ∈ U, ψ p ∈ V) ∧
      (∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p) ∧
      ∃ r : ℝ, 0 < r ∧ box_STR02958 r ⊆ U ∧ box_STR02958 r ∈ nhds (0 : Par_STR02916) ∧
        ∃ M : ℝ, 0 ≤ M ∧
          (∀ p ∈ box_STR02958 r, ∀ k : ℕ, k ≤ 5 →
            ‖iteratedFDeriv ℝ k (Fhat_STR02958 ψ) p‖ ≤ M) ∧
          ∀ a b h γ : ℕ → ℝ,
            Tendsto h atTop (𝓝 0) → (∀ᶠ n in atTop, h n ≠ 0) → Tendsto γ atTop (𝓝 0) →
            (∀ᶠ n in atTop, Fred_STR02956 ψ (a n, b n) (h n, γ n) = 0) →
            (∀ᶠ n in atTop, ((a n, b n, h n, γ n) : Par_STR02916) ∈ box_STR02958 r) →
            Tendsto (fun n => Metric.infDist (plane_STR02961 (a n / h n) (b n / h n))
              minimizers_STR02961) atTop (𝓝 0) →
            Asymptotics.IsBigO atTop γ (fun n => h n ^ 2) ∧
              Tendsto (fun n => γ n / h n ^ 2 - Qrate_STR02961 (a n / h n) (b n / h n)) atTop
                (𝓝 0) ∧
              Tendsto (fun n => γ n / h n ^ 2) atTop (𝓝 (-16 / 15)) := by
  obtain ⟨U, V, ψ, hU, h0U, hV, h0V, hψ, hψ0, hψV, hiff, r, hr, hbox, hnhds, ⟨M, hM0, hMb⟩, 𝓔,
    hexp, hbound⟩ := str029_19_amplitude_factored_unscaled_expansion
  refine ⟨U, V, ψ, hU, h0U, hV, h0V, hψ, hψ0, hψV, hiff, r, hr, hbox, hnhds, M, hM0, hMb, ?_⟩
  intro a b h γ hh hh0 hγ hF hbx hd
  refine seq_core_STR02961 M hM0 a b h γ (fun n => 𝓔 (a n) (b n) (h n) (γ n)) hh hγ hh0 ?_ ?_ hd
  · filter_upwards [hF, hbx] with n hFn hbn
    have h1 := hexp (a n) (b n) (h n) (γ n) hbn
    rw [hFn] at h1
    rw [str029_19_amplitude_factored_unscaled_expansion_poly19]
    exact h1.symm
  · filter_upwards [hbx] with n hbn
    exact hbound M hM0 hMb (a n) (b n) (h n) (γ n) hbn

end DGPS.Frontier.STR029
