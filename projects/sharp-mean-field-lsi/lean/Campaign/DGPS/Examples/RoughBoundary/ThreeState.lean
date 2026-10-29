import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Three-state landscape of the rough counterexample (RUF010-RUF017)

This module collects the discrete three-state landscape (source `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md`
section 2).

Main results so far:
* `DGPS.Examples.RoughBoundary.ThreeState.three_state_simplex_normalization` (RUF010): the
  three unit vectors at angles `0, 2π/3, 4π/3` satisfy `|M|² = (3/2)(∑ pᵢ² - 1/3)` for `M = ∑ pᵢ vᵢ`
  on the simplex, so entropy minus `κ|M|²/2` is `F_β` with `β = 3κ/2` (`β = 11/4` for `κ = 11/6`),
  and `F_β` is continuous (with `0 log 0 = 0`).
* `DGPS.Examples.RoughBoundary.ThreeState.simplex_boundary_cannot_minimize` (RUF011): no boundary
  point of the simplex is a local minimum of `F_β` on the simplex, a global minimizer exists, and
  every global minimizer is interior.
* `DGPS.Examples.RoughBoundary.ThreeState.complete_interior_critical_point_reduction` (RUF012):
  every interior critical point of `F_β` is uniform or a permutation of `p(r) = (r,1,1)/(r+2)`,
  `r > 0`, `r ≠ 1`, `f_β(r) = 0`, with the exact derivative `f_β'`.
* `DGPS.Examples.RoughBoundary.ThreeState.exact_logarithmic_inequalities` (RUF013):
  `log 2 > 56/81 > 11/16 > 2/3`, `log 2 < 3/4`, `log 3 ≤ 923/840 < 11/10`.
* `DGPS.Examples.RoughBoundary.ThreeState.constrained_simplex_hessian` (RUF016): the second
  derivative of `F_β` along a line is `Q(h) = ∑ (1/pᵢ - β) hᵢ²`; at `p(r)` the tangent vectors
  `v = (0,1,-1)`, `w = (-2,1,1)` are `Q`-orthogonal with `Q(v) = 2(r+2-β)`,
  `Q(w) = 2(r+2)² f_β'(r)`; at the uniform point `Q(h) = (3-β)∑ hᵢ²`.
* `DGPS.Examples.RoughBoundary.ThreeState.coexistence_parameter_and_global_positivity` (RUF014):
  at `β_c = 4 log 2` the positive roots of `f` are `1, 2, 4`, the global minimizers are the uniform
  point and the permutations of `(2/3, 1/6, 1/6)` (value `0`), so `F_{β_c} ≥ 0`; below `β_c`
  uniform is the unique global minimizer.
-/

namespace DGPS.Examples.RoughBoundary.ThreeState

open Real

/-- The simplex `{p ∈ [0,1]³ : p₁ + p₂ + p₃ = 1}`, written as `pᵢ ≥ 0`, `∑ pᵢ = 1`. -/
def simplex : Set (Fin 3 → ℝ) := {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

/-- The unit vector `vᵢ` of angle `2π i / 3` in the plane `ℝ²`. -/
noncomputable def vertex (i : Fin 3) : EuclideanSpace ℝ (Fin 2) :=
  !₂[Real.cos (2 * π * (i : ℕ) / 3), Real.sin (2 * π * (i : ℕ) / 3)]

/-- The mean vector `M = ∑ pᵢ vᵢ`. -/
noncomputable def meanVector (p : Fin 3 → ℝ) : EuclideanSpace ℝ (Fin 2) :=
  ∑ i, p i • vertex i

/-- The entropy `∑ pᵢ log (3 pᵢ)` relative to the uniform distribution (`0 log 0 = 0` since
`Real.log 0 = 0`). -/
noncomputable def entropy (p : Fin 3 → ℝ) : ℝ := ∑ i, p i * Real.log (3 * p i)

/-- The reduced free energy `F_β(p) = ∑ pᵢ log (3 pᵢ) - (β/2)(∑ pᵢ² - 1/3)`. -/
noncomputable def freeEnergy (β : ℝ) (p : Fin 3 → ℝ) : ℝ :=
  entropy p - β / 2 * (∑ i, p i ^ 2 - 1 / 3)

lemma vertex_zero : vertex 0 = !₂[1, 0] := by simp [vertex]

lemma vertex_one : vertex 1 = !₂[-1/2, √3/2] := by
  have a : 2 * π * 1 / 3 = π - π/3 := by ring
  simp only [vertex, Fin.val_one, Nat.cast_one, a, Real.cos_pi_sub, Real.sin_pi_sub,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  congr 2
  ring

lemma vertex_two : vertex 2 = !₂[-1/2, -(√3/2)] := by
  have b : 2 * π * 2 / 3 = π/3 + π := by ring
  simp only [vertex, Fin.val_two, Nat.cast_ofNat, b, Real.cos_add_pi, Real.sin_add_pi,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  congr 2
  ring

lemma continuous_entropy : Continuous entropy := by
  unfold entropy
  refine continuous_finsetSum _ fun i _ => ?_
  have h : Continuous fun x : ℝ => (3 * x) * Real.log (3 * x) :=
    Real.continuous_mul_log.comp (continuous_const.mul continuous_id)
  have h' := (continuous_apply i).comp (continuous_id (X := Fin 3 → ℝ))
  have := (h.comp h').div_const 3
  convert this using 2 with p
  simp only [Function.comp, id]
  ring

lemma continuous_freeEnergy (β : ℝ) : Continuous (freeEnergy β) := by
  unfold freeEnergy
  refine continuous_entropy.sub (continuous_const.mul ?_)
  exact (continuous_finsetSum _ fun i _ => ((continuous_apply i).pow 2)).sub continuous_const

lemma norm_vertex (i : Fin 3) : ‖vertex i‖ = 1 := by
  fin_cases i
  · simp [vertex_zero, EuclideanSpace.norm_eq]
  · simp [vertex_one, EuclideanSpace.norm_eq]
    have : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith
  · simp [vertex_two, EuclideanSpace.norm_eq]
    have : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith

/-- **RUF010, three-state simplex normalization.** The vertices `vᵢ` are unit vectors at angles
`0, 2π/3, 4π/3` with `vᵢ · vⱼ = -1/2` for `i ≠ j`; for `p` in the simplex and `M = ∑ pᵢ vᵢ`,
`|M|² = (3/2)(∑ pᵢ² - 1/3)`. Hence for every coupling `κ` and `β = 3κ/2`, entropy minus `κ|M|²/2`
equals `F_β(p) = ∑ pᵢ log (3 pᵢ) - (β/2)(∑ pᵢ² - 1/3)`; `κ = 11/6` gives `β = 11/4`; and `F_β`
is continuous (with `0 log 0 = 0`), in particular on the closed simplex. -/
theorem three_state_simplex_normalization :
    (∀ i, ‖vertex i‖ = 1) ∧
    (∀ i, vertex i = !₂[Real.cos (2 * π * (i : ℕ) / 3), Real.sin (2 * π * (i : ℕ) / 3)]) ∧
    (∀ i j, i ≠ j → inner ℝ (vertex i) (vertex j) = -1 / 2) ∧
    (∀ p ∈ simplex, ‖meanVector p‖ ^ 2 = 3 / 2 * (∑ i, p i ^ 2 - 1 / 3)) ∧
    (∀ κ β : ℝ, β = 3 * κ / 2 → ∀ p ∈ simplex,
      entropy p - κ * ‖meanVector p‖ ^ 2 / 2 = freeEnergy β p) ∧
    (3 * (11 / 6 : ℝ) / 2 = 11 / 4) ∧
    (∀ β : ℝ, Continuous (freeEnergy β)) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hnorm : ∀ p ∈ simplex, ‖meanVector p‖ ^ 2 = 3 / 2 * (∑ i, p i ^ 2 - 1 / 3) := by
    rintro p ⟨-, hp⟩
    rw [Fin.sum_univ_three] at hp
    have : p 0 = 1 - p 1 - p 2 := by linarith
    simp only [meanVector, Fin.sum_univ_three, vertex_zero, vertex_one, vertex_two,
      EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, this]
    nlinarith [h3]
  refine ⟨norm_vertex, fun i => rfl, ?_, hnorm, ?_, by norm_num, continuous_freeEnergy⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | (simp [vertex_zero, vertex_one, vertex_two, Fin.sum_univ_two, inner]; try nlinarith [h3])
  · intro κ β hβ p hp
    unfold freeEnergy
    rw [hnorm p hp, hβ]
    ring

/-- **RUF013, exact logarithmic inequalities.**
`log 2 > 56/81 > 11/16 > 2/3`, `log 2 < 3/4`, and `log 3 ≤ 923/840 < 11/10`. -/
theorem exact_logarithmic_inequalities :
    Real.log 2 > 56 / 81 ∧ (56 / 81 : ℝ) > 11 / 16 ∧ (11 / 16 : ℝ) > 2 / 3 ∧
    Real.log 2 < 3 / 4 ∧ Real.log 3 ≤ 923 / 840 ∧ (923 / 840 : ℝ) < 11 / 10 := by
  have h2a := Real.log_two_gt_d9
  have h2b := Real.log_two_lt_d9
  have h3 : Real.log 3 ≤ 923 / 840 := by
    have hs := Real.hasSum_log_one_add_inv (a := (1 / 2 : ℝ)) (by norm_num)
    have e : (1 : ℝ) + (1 / 2 : ℝ)⁻¹ = 3 := by norm_num
    rw [e] at hs
    have hs' := (hasSum_nat_add_iff' 3).2 hs
    have hg : HasSum (fun k : ℕ => (2 / 7 : ℝ) * (1 / 2 : ℝ) ^ (2 * (k + 3) + 1))
        ((2 / 7 * (1 / 2) ^ 7 : ℝ) * (1 - 1 / 4)⁻¹) := by
      have := (hasSum_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)).mul_left
        ((2 / 7 : ℝ) * (1 / 2) ^ 7)
      convert this using 2 with k
      rw [show 2 * (k + 3) + 1 = 7 + 2 * k by ring, pow_add, pow_mul]
      norm_num
      ring
    have hle := hasSum_le (fun k => ?_) hs' hg
    · have : (1 - 1 / 4 : ℝ)⁻¹ = 4 / 3 := by norm_num
      rw [this] at hle
      simp [Finset.sum_range_succ] at hle
      norm_num at hle
      linarith
    · have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have h7 : (1 : ℝ) / (2 * ((k + 3 : ℕ) : ℝ) + 1) ≤ 1 / 7 := by
        apply one_div_le_one_div_of_le (by norm_num)
        push_cast
        linarith
      have hp : (0 : ℝ) ≤ (1 / (2 * (1 / 2 : ℝ) + 1)) ^ (2 * (k + 3) + 1) := by positivity
      have : (1 / (2 * (1 / 2 : ℝ) + 1)) = 1 / 2 := by norm_num
      rw [this] at hp ⊢
      nlinarith
  refine ⟨?_, ?_, ?_, ?_, h3, ?_⟩ <;> norm_num at * <;> linarith

/-- Real-variable core of the inward variation (RUF011). -/
lemma boundary_descent_real (β b c ε : ℝ) (hb1 : b ≤ 1) (hε : 0 < ε)
    (hεb : ε < b / 2 * Real.exp (-|β|)) :
    (ε * Real.log (3 * ε) + (b - ε) * Real.log (3 * (b - ε)) + c * Real.log (3 * c))
        - β / 2 * (ε ^ 2 + (b - ε) ^ 2 + c ^ 2 - 1 / 3)
      < (0 * Real.log (3 * 0) + b * Real.log (3 * b) + c * Real.log (3 * c))
        - β / 2 * (0 ^ 2 + b ^ 2 + c ^ 2 - 1 / 3) := by
  have hexp : Real.exp (-|β|) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [abs_nonneg β])
  have hexp0 : 0 < Real.exp (-|β|) := Real.exp_pos _
  have hb : 0 < b := by
    by_contra h
    have h := not_lt.1 h
    nlinarith
  have hεb2 : ε < b / 2 := by nlinarith
  have hby : 0 < b - ε := by linarith
  -- log inequality  b log(b/(b-ε)) ≥ ε
  have h1 : ε ≤ b * (Real.log b - Real.log (b - ε)) := by
    have := Real.one_sub_inv_le_log_of_pos (div_pos hb hby)
    rw [Real.log_div hb.ne' hby.ne'] at this
    have e : 1 - (b / (b - ε))⁻¹ = ε / b := by field_simp; ring
    rw [e] at this
    have := mul_le_mul_of_nonneg_left this hb.le
    rwa [mul_div_cancel₀ _ hb.ne'] at this
  have h3 : ∀ x : ℝ, 0 < x → Real.log (3 * x) = Real.log 3 + Real.log x :=
    fun x hx => Real.log_mul (by norm_num) hx.ne'
  have h2 : Real.log (3 * b / 2) ≤ Real.log (3 * (b - ε)) :=
    Real.log_le_log (by positivity) (by linarith)
  have h4 : Real.log (3 * ε) < Real.log (3 * b / 2) + (-|β|) := by
    rw [← Real.log_exp (-|β|), ← Real.log_mul (by positivity) (Real.exp_pos _).ne']
    exact Real.log_lt_log (by positivity) (by nlinarith)
  have h5 : (b - ε) * Real.log (3 * (b - ε)) - b * Real.log (3 * b)
      ≤ -ε * (Real.log (3 * (b - ε)) + 1) := by
    rw [h3 b hb, h3 _ hby]
    nlinarith
  have h6 : β * (b - ε) ≤ |β| := by
    have : β * (b - ε) ≤ |β| * (b - ε) := mul_le_mul_of_nonneg_right (le_abs_self β) hby.le
    nlinarith [abs_nonneg β]
  simp only [mul_zero, Real.log_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow]
  have hq : ε * (Real.log (3 * ε) - Real.log (3 * (b - ε)) - 1 + β * (b - ε)) < 0 := by
    apply mul_neg_of_pos_of_neg hε
    linarith
  nlinarith [hq, h5]


/-- The inward variation of `p` moving mass `ε` from coordinate `i` to coordinate `j`. -/
def inwardVariation (p : Fin 3 → ℝ) (i j : Fin 3) (ε : ℝ) : Fin 3 → ℝ :=
  fun m => if m = j then ε else if m = i then p i - ε else p m

lemma freeEnergy_inwardVariation_lt (β : ℝ) (p : Fin 3 → ℝ) (hp : p ∈ simplex) (i j : Fin 3)
    (hij : i ≠ j) (hj : p j = 0) (hi : 0 < p i) (ε : ℝ) (hε : 0 < ε)
    (hεb : ε < p i / 2 * Real.exp (-|β|)) :
    freeEnergy β (inwardVariation p i j ε) < freeEnergy β p := by
  obtain ⟨hp0, hp1⟩ := hp
  have hb1 : p i ≤ 1 := by
    rw [← hp1]
    exact Finset.single_le_sum (fun m _ => hp0 m) (Finset.mem_univ i)
  rw [Fin.sum_univ_three] at hp1
  unfold freeEnergy entropy inwardVariation
  simp only [Fin.sum_univ_three]
  revert hij hj hi hεb hb1
  fin_cases i <;> fin_cases j <;> simp <;> intro hj hi hεb hb1 <;> simp [hj] <;>
  first
  | linarith [boundary_descent_real β (p 0) (p 1) ε hb1 hε hεb]
  | linarith [boundary_descent_real β (p 0) (p 2) ε hb1 hε hεb]
  | linarith [boundary_descent_real β (p 1) (p 0) ε hb1 hε hεb]
  | linarith [boundary_descent_real β (p 1) (p 2) ε hb1 hε hεb]
  | linarith [boundary_descent_real β (p 2) (p 0) ε hb1 hε hεb]


lemma isCompact_simplex : IsCompact simplex := by
  have hc : IsCompact (Set.pi Set.univ fun _ : Fin 3 => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  refine hc.of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {p : Fin 3 → ℝ | ∀ i, 0 ≤ p i} :=
      by
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed {p : Fin 3 → ℝ | ∑ i, p i = 1} :=
      isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    exact h1.inter h2
  · rintro p ⟨hp0, hp1⟩ i -
    refine ⟨hp0 i, ?_⟩
    rw [← hp1]
    exact Finset.single_le_sum (fun m _ => hp0 m) (Finset.mem_univ i)

lemma uniform_mem_simplex : (fun _ : Fin 3 => (1 / 3 : ℝ)) ∈ simplex := by
  refine ⟨fun _ => by norm_num, ?_⟩
  simp

/-- **RUF011, simplex boundary cannot minimize.** For every real `β`, no boundary point `p ∈ S`
(a point of the simplex with some coordinate `0`, including the vertices) is a local minimum of
`F_β` on `S`; a global minimizer of `F_β` on `S` exists (compactness) and every global minimizer
has all coordinates positive (it lies in the interior). -/
theorem simplex_boundary_cannot_minimize (β : ℝ) :
    (∀ p ∈ simplex, (∃ j, p j = 0) → ¬ IsLocalMinOn (freeEnergy β) simplex p) ∧
    (∃ p ∈ simplex, IsMinOn (freeEnergy β) simplex p) ∧
    (∀ p ∈ simplex, IsMinOn (freeEnergy β) simplex p → ∀ i, 0 < p i) := by
  have boundary : ∀ p ∈ simplex, (∃ j, p j = 0) → ¬ IsLocalMinOn (freeEnergy β) simplex p := by
    intro p hp ⟨j, hj⟩ hloc
    obtain ⟨hp0, hp1⟩ := hp
    have hex : ∃ i, 0 < p i := by
      by_contra h
      push Not at h
      have : ∑ i, p i ≤ 0 := Finset.sum_nonpos fun i _ => h i
      linarith
    obtain ⟨i, hi⟩ := hex
    have hij : i ≠ j := by
      rintro rfl
      linarith
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hloc
    set ε : ℝ := min (δ / 2) (p i / 4 * Real.exp (-|β|)) with hε
    have hexp0 : 0 < Real.exp (-|β|) := Real.exp_pos _
    have hεpos : 0 < ε := lt_min (by linarith) (by positivity)
    have hε1 : ε ≤ δ / 2 := min_le_left _ _
    have hε2 : ε < p i / 2 * Real.exp (-|β|) := by
      have : ε ≤ p i / 4 * Real.exp (-|β|) := min_le_right _ _
      have : 0 < p i / 4 * Real.exp (-|β|) := by positivity
      linarith
    have hmem : inwardVariation p i j ε ∈ simplex := by
      have hexp1 : Real.exp (-|β|) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [abs_nonneg β])
      have hεi : ε < p i / 2 := by nlinarith
      refine ⟨fun m => ?_, ?_⟩
      · unfold inwardVariation
        split_ifs
        · exact hεpos.le
        · linarith
        · exact hp0 m
      · rw [Fin.sum_univ_three] at hp1 ⊢
        unfold inwardVariation
        revert hij hj
        fin_cases i <;> fin_cases j <;> simp <;> intro hj <;> linarith
    have hnear : inwardVariation p i j ε ∈ Metric.ball p δ := by
      rw [Metric.mem_ball, dist_pi_lt_iff hδ]
      intro m
      rw [Real.dist_eq]
      unfold inwardVariation
      split_ifs with h1 h2
      · subst h1
        rw [hj, sub_zero, abs_of_pos hεpos]
        linarith
      · subst h2
        rw [sub_sub_cancel_left, abs_neg, abs_of_pos hεpos]
        linarith
      · simp [hδ]
    have := hball ⟨hnear, hmem⟩
    have hlt := freeEnergy_inwardVariation_lt β p ⟨hp0, hp1⟩ i j hij hj hi ε hεpos hε2
    exact absurd this (not_le.2 hlt)
  refine ⟨boundary, ?_, ?_⟩
  · obtain ⟨p, hp, hmin⟩ :=
      isCompact_simplex.exists_isMinOn ⟨_, uniform_mem_simplex⟩ (continuous_freeEnergy β).continuousOn
    exact ⟨p, hp, hmin⟩
  · intro p hp hmin i
    rcases (hp.1 i).lt_or_eq with h | h
    · exact h
    · exact absurd (hmin.isLocalMinOn) (boundary p hp ⟨i, h.symm⟩)

lemma hasDerivAt_freeEnergy_line (β : ℝ) (p h : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) :
    HasDerivAt (fun t : ℝ => freeEnergy β (p + t • h))
      (∑ i, h i * (Real.log (3 * p i) + 1 - β * p i)) 0 := by
  have hterm : ∀ i : Fin 3, HasDerivAt
      (fun t : ℝ => (p i + t * h i) * Real.log (3 * (p i + t * h i)) -
        β / 2 * (p i + t * h i) ^ 2)
      (h i * (Real.log (3 * p i) + 1 - β * p i)) 0 := by
    intro i
    have hl : HasDerivAt (fun t : ℝ => p i + t * h i) (h i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (h i)).const_add (p i)
    have h0 : p i + 0 * h i = p i := by ring
    have hpos : 0 < p i + 0 * h i := by rw [h0]; exact hp i
    have hlog : HasDerivAt (fun t : ℝ => Real.log (3 * (p i + t * h i)))
        (3 * h i / (3 * (p i + 0 * h i))) 0 :=
      (hl.const_mul 3).log (by rw [h0]; exact (mul_pos (by norm_num) (hp i)).ne')
    have := (hl.mul hlog).sub ((hl.pow 2).const_mul (β / 2))
    convert this using 1
    rw [h0]
    have := (hp i).ne'
    simp
    field_simp
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun i _ => hterm i)
  have hfun : (fun t : ℝ => freeEnergy β (p + t • h)) =
      fun t : ℝ => ∑ i, ((p i + t * h i) * Real.log (3 * (p i + t * h i)) -
        β / 2 * (p i + t * h i) ^ 2) + β / 2 * (1 / 3) := by
    funext t
    simp only [freeEnergy, entropy, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hfun]
  simpa using hsum.add_const (β / 2 * (1 / 3))


/-- Three distinct positive points cannot share a value of `s ↦ log s - β s` (strict concavity). -/
lemma log_sub_mul_not_three {β a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (h1 : Real.log a - β * a = Real.log b - β * b)
    (h2 : Real.log c - β * c = Real.log b - β * b) : False := by
  have hb : 0 < b := ha.trans hab
  have hc : 0 < c := hb.trans hbc
  have hca : 0 < c - a := by linarith
  set t : ℝ := (c - b) / (c - a) with ht
  set u : ℝ := (b - a) / (c - a) with hu
  have ht0 : 0 < t := div_pos (by linarith) hca
  have hu0 : 0 < u := div_pos (by linarith) hca
  have htu : t + u = 1 := by
    rw [ht, hu, ← add_div, show c - b + (b - a) = c - a by ring]
    exact div_self hca.ne'
  have hmix : t * a + u * c = b := by
    rw [ht, hu]
    field_simp
    ring
  have := strictConcaveOn_log_Ioi.2 (Set.mem_Ioi.2 ha) (Set.mem_Ioi.2 hc) (ne_of_lt (hab.trans hbc))
    ht0 hu0 htu
  simp only [smul_eq_mul, hmix] at this
  have e1 : Real.log a = β * a + (Real.log b - β * b) := by linarith
  have e2 : Real.log c = β * c + (Real.log b - β * b) := by linarith
  rw [e1, e2] at this
  have eq : t * (β * a + (Real.log b - β * b)) + u * (β * c + (Real.log b - β * b))
      = Real.log b := by
    linear_combination β * hmix + (Real.log b - β * b) * htu
  linarith


lemma log_sub_mul_two_equal {β x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : Real.log x - β * x = Real.log y - β * y)
    (h2 : Real.log z - β * z = Real.log y - β * y) : x = y ∨ y = z ∨ x = z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hxy, hyz, hxz⟩ := hcon
  rcases lt_or_gt_of_ne hxy with a | a <;> rcases lt_or_gt_of_ne hyz with b | b <;>
    rcases lt_or_gt_of_ne hxz with c | c <;>
  first
  | exact absurd (a.trans b) (not_lt.2 c.le)
  | exact absurd (b.trans a) (not_lt.2 c.le)
  | exact absurd (c.trans a) (not_lt.2 b.le)
  | exact absurd (c.trans b) (not_lt.2 a.le)
  | exact log_sub_mul_not_three (β := β) hx a b (by linarith) (by linarith)
  | exact log_sub_mul_not_three (β := β) hx c b (by linarith) (by linarith)
  | exact log_sub_mul_not_three (β := β) hy a c (by linarith) (by linarith)
  | exact log_sub_mul_not_three (β := β) hy b c (by linarith) (by linarith)
  | exact log_sub_mul_not_three (β := β) hz c a (by linarith) (by linarith)
  | exact log_sub_mul_not_three (β := β) hz b a (by linarith) (by linarith)


/-- The one-parameter family `p(r) = (r, 1, 1) / (r + 2)`. -/
noncomputable def pointR (r : ℝ) : Fin 3 → ℝ := ![r / (r + 2), 1 / (r + 2), 1 / (r + 2)]

/-- The scalar critical-point function `f_β(r) = log r - β (r - 1) / (r + 2)`. -/
noncomputable def criticalFunction (β r : ℝ) : ℝ := Real.log r - β * (r - 1) / (r + 2)

/-- `p` is an interior critical point of `F_β` on the simplex: it lies in the simplex with all
coordinates positive and `F_β` has zero derivative at `p` along every tangent direction `h`
(`∑ hᵢ = 0`). -/
def IsInteriorCriticalPoint (β : ℝ) (p : Fin 3 → ℝ) : Prop :=
  p ∈ simplex ∧ (∀ i, 0 < p i) ∧
    ∀ h : Fin 3 → ℝ, ∑ i, h i = 0 → HasDerivAt (fun t : ℝ => freeEnergy β (p + t • h)) 0 0

lemma exists_r_of_two_equal (β t s : ℝ) (ht : 0 < t) (hs : 0 < s) (hsum : t + 2 * s = 1)
    (hne : t ≠ s) (hφ : Real.log t - β * t = Real.log s - β * s) :
    ∃ r : ℝ, 0 < r ∧ r ≠ 1 ∧ criticalFunction β r = 0 ∧ t = r / (r + 2) ∧ s = 1 / (r + 2) := by
  have hr2 : t / s + 2 = 1 / s := by
    field_simp
    linarith
  refine ⟨t / s, div_pos ht hs, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hne ((div_eq_one_iff_eq hs.ne').1 h)
  · unfold criticalFunction
    rw [hr2, Real.log_div ht.ne' hs.ne']
    have : β * (t / s - 1) / (1 / s) = β * (t - s) := by
      field_simp
    rw [this]
    linarith
  · rw [hr2]
    field_simp
  · rw [hr2]
    field_simp

lemma hasDerivAt_criticalFunction (β : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (criticalFunction β) ((r ^ 2 + (4 - 3 * β) * r + 4) / (r * (r + 2) ^ 2)) r := by
  have h2 : r + 2 ≠ 0 := by positivity
  have hnum : HasDerivAt (fun r : ℝ => β * (r - 1)) β r := by
    simpa using ((hasDerivAt_id r).sub_const 1).const_mul β
  have hden : HasDerivAt (fun r : ℝ => r + 2) 1 r := (hasDerivAt_id r).add_const 2
  have := (Real.hasDerivAt_log hr.ne').sub (hnum.div hden h2)
  convert this using 1
  · funext x
    simp [criticalFunction]
  · field_simp
    ring


/-- The Lagrange multiplier equation: at an interior critical point the quantities
`log pᵢ - β pᵢ` agree. -/
lemma lagrange_of_interior_critical {β : ℝ} {p : Fin 3 → ℝ} (hc : IsInteriorCriticalPoint β p) :
    Real.log (p 0) - β * p 0 = Real.log (p 1) - β * p 1 ∧
    Real.log (p 2) - β * p 2 = Real.log (p 1) - β * p 1 := by
  obtain ⟨-, hpos, hcrit⟩ := hc
  have key : ∀ h : Fin 3 → ℝ, ∑ i, h i = 0 →
      ∑ i, h i * (Real.log (3 * p i) + 1 - β * p i) = 0 := fun h hh =>
    (hasDerivAt_freeEnergy_line β p h hpos).unique (hcrit h hh)
  have l3 : ∀ i, Real.log (3 * p i) = Real.log 3 + Real.log (p i) := fun i =>
    Real.log_mul (by norm_num) (hpos i).ne'
  have e1 := key ![1, -1, 0] (by simp [Fin.sum_univ_three])
  have e2 := key ![0, -1, 1] (by simp [Fin.sum_univ_three])
  simp only [Fin.sum_univ_three, l3] at e1 e2
  simp at e1 e2
  constructor <;> linarith

/-- **RUF012, complete interior critical-point reduction.** For `β > 0`, every interior critical
point `p` of `F_β` on the simplex is the uniform point `(1/3, 1/3, 1/3)` or a permutation
`i ↦ p(r)_{σ i}` of `p(r) = (r, 1, 1)/(r + 2)` with `r > 0`, `r ≠ 1` and `f_β(r) = 0`, where
`f_β(r) = log r - β (r - 1)/(r + 2)`; moreover `f_β'(r) = (r² + (4 - 3β) r + 4)/(r (r + 2)²)`
for every `r > 0`. (The hypothesis `β > 0` is not needed by the proof.) -/
theorem complete_interior_critical_point_reduction (β : ℝ) (_hβ : 0 < β) :
    (∀ p : Fin 3 → ℝ, IsInteriorCriticalPoint β p →
      p = (fun _ => 1 / 3) ∨
        ∃ r : ℝ, 0 < r ∧ r ≠ 1 ∧ criticalFunction β r = 0 ∧
          ∃ σ : Equiv.Perm (Fin 3), p = fun i => pointR r (σ i)) ∧
    (∀ r : ℝ, 0 < r →
      HasDerivAt (criticalFunction β) ((r ^ 2 + (4 - 3 * β) * r + 4) / (r * (r + 2) ^ 2)) r) := by
  refine ⟨fun p hc => ?_, fun r hr => hasDerivAt_criticalFunction β hr⟩
  obtain ⟨l1, l2⟩ := lagrange_of_interior_critical hc
  obtain ⟨⟨-, hp1⟩, hpos, -⟩ := hc
  rw [Fin.sum_univ_three] at hp1
  have h0 := hpos 0
  have h1 := hpos 1
  have h2 := hpos 2
  have uniform : p 0 = p 1 → p 1 = p 2 → p = fun _ => 1 / 3 := by
    intro a b
    funext i
    fin_cases i <;> simp <;> linarith
  rcases log_sub_mul_two_equal h0 h1 h2 l1 l2 with a | b | c
  · -- p 0 = p 1
    by_cases hb : p 1 = p 2
    · exact Or.inl (uniform a hb)
    · right
      obtain ⟨r, hr, hr1, hf, ht, hs⟩ := exists_r_of_two_equal β (p 2) (p 0) h2 h0
        (by linarith) (Ne.symm (by rwa [a])) (by rw [a]; linarith)
      refine ⟨r, hr, hr1, hf, Equiv.swap 0 2, ?_⟩
      have sw : Equiv.swap (0 : Fin 3) 2 1 = 1 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
      funext i
      fin_cases i <;> simp [pointR, sw, ← ht, ← hs, a]
  · -- p 1 = p 2
    by_cases ha : p 0 = p 1
    · exact Or.inl (uniform ha b)
    · right
      obtain ⟨r, hr, hr1, hf, ht, hs⟩ := exists_r_of_two_equal β (p 0) (p 1) h0 h1
        (by linarith) ha l1
      refine ⟨r, hr, hr1, hf, 1, ?_⟩
      funext i
      fin_cases i <;> simp [pointR, ← ht, ← hs, b]
  · -- p 0 = p 2
    by_cases ha : p 0 = p 1
    · exact Or.inl (uniform ha (by rw [← ha, c]))
    · right
      obtain ⟨r, hr, hr1, hf, ht, hs⟩ := exists_r_of_two_equal β (p 1) (p 0) h1 h0
        (by linarith) (Ne.symm ha) (by linarith)
      refine ⟨r, hr, hr1, hf, Equiv.swap 0 1, ?_⟩
      have sw : Equiv.swap (0 : Fin 3) 1 2 = 2 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
      funext i
      fin_cases i <;> simp [pointR, sw, ← ht, ← hs, c]

open Filter Topology

/-- The constrained Hessian bilinear form `∑ (1/pᵢ - β) hᵢ kᵢ` of `F_β` at `p`. -/
noncomputable def hessianBilin (β : ℝ) (p h k : Fin 3 → ℝ) : ℝ :=
  ∑ i, (1 / p i - β) * h i * k i

/-- The constrained Hessian quadratic form `Q(h) = ∑ (1/pᵢ - β) hᵢ²` of `F_β` at `p`. -/
noncomputable def hessianForm (β : ℝ) (p h : Fin 3 → ℝ) : ℝ :=
  ∑ i, (1 / p i - β) * h i ^ 2

/-- The tangent vector `v = (0, 1, -1)`. -/
def tangentV : Fin 3 → ℝ := ![0, 1, -1]

/-- The tangent vector `w = (-2, 1, 1)`. -/
def tangentW : Fin 3 → ℝ := ![-2, 1, 1]

lemma hessianForm_eq_bilin (β : ℝ) (p h : Fin 3 → ℝ) :
    hessianForm β p h = hessianBilin β p h h := by
  unfold hessianForm hessianBilin
  exact Finset.sum_congr rfl fun i _ => by ring

lemma hasDerivAt_line_shift (β : ℝ) (p h : Fin 3 → ℝ) {t : ℝ} (hp : ∀ i, 0 < p i + t * h i) :
    HasDerivAt (fun s : ℝ => freeEnergy β (p + s • h))
      (∑ i, h i * (Real.log (3 * (p i + t * h i)) + 1 - β * (p i + t * h i))) t := by
  have hpos : ∀ i, 0 < (p + t • h) i := fun i => by simpa using hp i
  have h1 := hasDerivAt_freeEnergy_line β (p + t • h) h hpos
  have h2 : HasDerivAt (fun s : ℝ => freeEnergy β ((p + t • h) + s • h))
      (∑ i, h i * (Real.log (3 * (p i + t * h i)) + 1 - β * (p i + t * h i))) (t - t) := by
    rw [sub_self]
    simpa using h1
  have h3 := h2.comp_sub_const t t
  convert h3 using 2 with s
  congr 1
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The second derivative of `F_β` along the line `p + t h` at a positive point is the
quadratic form `Q(h)`. -/
lemma secondDeriv_freeEnergy_line (β : ℝ) (p h : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) :
    HasDerivAt (deriv fun t : ℝ => freeEnergy β (p + t • h)) (hessianForm β p h) 0 := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, 0 < p i + t * h i := by
    rw [Filter.eventually_all]
    intro i
    have hc : Continuous fun t : ℝ => p i + t * h i := by fun_prop
    exact (hc.tendsto 0).eventually (lt_mem_nhds (by simpa using hp i))
  have hEq : (deriv fun t : ℝ => freeEnergy β (p + t • h)) =ᶠ[𝓝 0]
      fun t => ∑ i, h i * (Real.log (3 * (p i + t * h i)) + 1 - β * (p i + t * h i)) := by
    filter_upwards [hev] with t ht
    exact (hasDerivAt_line_shift β p h ht).deriv
  refine HasDerivAt.congr_of_eventuallyEq ?_ hEq
  have hterm : ∀ i : Fin 3, HasDerivAt
      (fun t : ℝ => h i * (Real.log (3 * (p i + t * h i)) + 1 - β * (p i + t * h i)))
      ((1 / p i - β) * h i ^ 2) 0 := by
    intro i
    have hl : HasDerivAt (fun t : ℝ => p i + t * h i) (h i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (h i)).const_add (p i)
    have h0 : p i + 0 * h i = p i := by ring
    have hlog : HasDerivAt (fun t : ℝ => Real.log (3 * (p i + t * h i)))
        (3 * h i / (3 * (p i + 0 * h i))) 0 :=
      (hl.const_mul 3).log (by rw [h0]; exact (mul_pos (by norm_num) (hp i)).ne')
    have := (hlog.add_const 1).sub (hl.const_mul β) |>.const_mul (h i)
    convert this using 1
    rw [h0]
    have := (hp i).ne'
    field_simp
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hterm i)
  simpa [hessianForm] using hsum


lemma sum_tangentV : ∑ i, tangentV i = 0 := by simp [tangentV, Fin.sum_univ_three]

lemma sum_tangentW : ∑ i, tangentW i = 0 := by
  simp [tangentW, Fin.sum_univ_three]
  norm_num

lemma tangent_decomposition (h : Fin 3 → ℝ) (hh : ∑ i, h i = 0) :
    ∃ a b : ℝ, h = a • tangentV + b • tangentW := by
  rw [Fin.sum_univ_three] at hh
  refine ⟨(h 1 - h 2) / 2, (h 1 + h 2) / 2, ?_⟩
  funext i
  fin_cases i <;> simp [tangentV, tangentW] <;> linarith

lemma linearIndependent_tangent : LinearIndependent ℝ ![tangentV, tangentW] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun hg 0
  have h1 := congrFun hg 1
  simp [Fin.sum_univ_two, tangentV, tangentW] at h0 h1
  intro i
  fin_cases i
  · simp; linarith
  · simp; linarith

lemma hessianForm_pointR_tangent (β r : ℝ) (hr : 0 < r) (a b : ℝ) :
    hessianForm β (pointR r) (a • tangentV + b • tangentW) =
      a ^ 2 * hessianForm β (pointR r) tangentV + b ^ 2 * hessianForm β (pointR r) tangentW := by
  have h2 : r + 2 ≠ 0 := by positivity
  simp [hessianForm, Fin.sum_univ_three, pointR, tangentV, tangentW]
  ring

lemma hessianForm_pointR_v (β r : ℝ) (hr : 0 < r) :
    hessianForm β (pointR r) tangentV = 2 * (r + 2 - β) := by
  have h2 : r + 2 ≠ 0 := by positivity
  simp [hessianForm, Fin.sum_univ_three, pointR, tangentV]
  ring

lemma hessianForm_pointR_w (β r : ℝ) (hr : 0 < r) :
    hessianForm β (pointR r) tangentW =
      2 * (r + 2) ^ 2 * deriv (criticalFunction β) r := by
  have h2 : r + 2 ≠ 0 := by positivity
  rw [(hasDerivAt_criticalFunction β hr).deriv]
  simp [hessianForm, Fin.sum_univ_three, pointR, tangentW]
  field_simp
  ring

lemma hessianBilin_pointR_vw (β r : ℝ) :
    hessianBilin β (pointR r) tangentV tangentW = 0 := by
  simp [hessianBilin, Fin.sum_univ_three, pointR, tangentV, tangentW]

/-- **RUF016, constrained simplex Hessian.** -/
theorem constrained_simplex_hessian (β : ℝ) :
    (∀ p h : Fin 3 → ℝ, (∀ i, 0 < p i) →
      HasDerivAt (deriv fun t : ℝ => freeEnergy β (p + t • h)) (hessianForm β p h) 0) ∧
    (∑ i, tangentV i = 0 ∧ ∑ i, tangentW i = 0 ∧
      LinearIndependent ℝ ![tangentV, tangentW] ∧
      ∀ h : Fin 3 → ℝ, ∑ i, h i = 0 → ∃ a b : ℝ, h = a • tangentV + b • tangentW) ∧
    (∀ r : ℝ, 0 < r →
      hessianBilin β (pointR r) tangentV tangentW = 0 ∧
      hessianForm β (pointR r) tangentV = 2 * (r + 2 - β) ∧
      hessianForm β (pointR r) tangentW = 2 * (r + 2) ^ 2 * deriv (criticalFunction β) r ∧
      ∀ a b : ℝ, hessianForm β (pointR r) (a • tangentV + b • tangentW) =
        a ^ 2 * hessianForm β (pointR r) tangentV + b ^ 2 * hessianForm β (pointR r) tangentW) ∧
    (∀ h : Fin 3 → ℝ,
      hessianForm β (fun _ => 1 / 3) h = (3 - β) * ∑ i, h i ^ 2) ∧
    (∀ r : ℝ, 1 < r → β < 3 →
      0 < hessianForm β (pointR r) tangentV ∧
      (0 < deriv (criticalFunction β) r →
        ∀ h : Fin 3 → ℝ, ∑ i, h i = 0 → h ≠ 0 → 0 < hessianForm β (pointR r) h) ∧
      (deriv (criticalFunction β) r < 0 → hessianForm β (pointR r) tangentW < 0)) := by
  refine ⟨fun p h hp => secondDeriv_freeEnergy_line β p h hp,
    ⟨sum_tangentV, sum_tangentW, linearIndependent_tangent, tangent_decomposition⟩,
    fun r hr => ⟨hessianBilin_pointR_vw β r, hessianForm_pointR_v β r hr,
      hessianForm_pointR_w β r hr, hessianForm_pointR_tangent β r hr⟩, ?_, ?_⟩
  · intro h
    simp only [hessianForm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    norm_num
  · intro r hr1 hβ
    have hr : 0 < r := by linarith
    have hv : 0 < hessianForm β (pointR r) tangentV := by
      rw [hessianForm_pointR_v β r hr]; linarith
    refine ⟨hv, fun hf h hh hne => ?_, fun hf => ?_⟩
    · obtain ⟨a, b, rfl⟩ := tangent_decomposition h hh
      rw [hessianForm_pointR_tangent β r hr, hessianForm_pointR_w β r hr]
      have hw : 0 < 2 * (r + 2) ^ 2 * deriv (criticalFunction β) r := by positivity
      have hab : a ≠ 0 ∨ b ≠ 0 := by
        by_contra hc
        push Not at hc
        simp [hc.1, hc.2] at hne
      rcases hab with ha | hb
      · have h1 := mul_pos (pow_pos (abs_pos.2 ha) 2) hv
        rw [sq_abs] at h1
        have h2 := mul_nonneg (sq_nonneg b) hw.le
        linarith
      · have h1 := mul_pos (pow_pos (abs_pos.2 hb) 2) hw
        rw [sq_abs] at h1
        have h2 := mul_nonneg (sq_nonneg a) hv.le
        linarith
    · rw [hessianForm_pointR_w β r hr]
      have : 0 < (r + 2) ^ 2 := by positivity
      nlinarith

/-! ### RUF014: the coexistence parameter `β_c = 4 log 2` and global positivity -/

lemma freeEnergy_perm (β : ℝ) (q : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) :
    freeEnergy β (fun i => q (σ i)) = freeEnergy β q := by
  simp only [freeEnergy, entropy]
  rw [Equiv.sum_comp σ (fun j => q j * Real.log (3 * q j)), Equiv.sum_comp σ (fun j => q j ^ 2)]

lemma freeEnergy_uniform (β : ℝ) : freeEnergy β (fun _ => 1 / 3) = 0 := by
  simp [freeEnergy, entropy]
  norm_num

lemma freeEnergy_pointR_four : freeEnergy (4 * Real.log 2) (pointR 4) = 0 := by
  have h1 : Real.log (3 * (2 / 3 : ℝ)) = Real.log 2 := by norm_num
  have h2 : Real.log (3 * (1 / 6 : ℝ)) = - Real.log 2 := by
    rw [show (3 * (1 / 6 : ℝ)) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  simp only [freeEnergy, entropy, Fin.sum_univ_three, pointR]
  norm_num [h1, h2]
  simp only [one_div, Real.log_inv]
  ring

lemma freeEnergy_pointR_two_pos : 0 < freeEnergy (4 * Real.log 2) (pointR 2) := by
  have h1 : Real.log (3 * (1 / 2 : ℝ)) = Real.log 3 - Real.log 2 := by
    rw [show (3 * (1 / 2 : ℝ)) = 3 / 2 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  have h2 : Real.log (3 * (1 / 4 : ℝ)) = Real.log 3 - 2 * Real.log 2 := by
    rw [show (3 * (1 / 4 : ℝ)) = 3 / 2 ^ 2 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hlt : 19 * Real.log 2 < 12 * Real.log 3 := by
    have := Real.log_lt_log (by positivity : (0 : ℝ) < 2 ^ 19) (by norm_num : (2 : ℝ) ^ 19 < 3 ^ 12)
    rw [Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith
  simp only [freeEnergy, entropy, Fin.sum_univ_three, pointR]
  norm_num [h1, h2]
  nlinarith [hlt]

lemma pointR_four_perm_iff (p : Fin 3 → ℝ) :
    (∃ σ : Equiv.Perm (Fin 3), p = fun i => pointR 4 (σ i)) ↔
      p = ![2 / 3, 1 / 6, 1 / 6] ∨ p = ![1 / 6, 2 / 3, 1 / 6] ∨ p = ![1 / 6, 1 / 6, 2 / 3] := by
  have e0 : pointR 4 0 = 2 / 3 := by simp [pointR]; norm_num
  have e1 : pointR 4 1 = 1 / 6 := by simp [pointR]; norm_num
  have e2 : pointR 4 2 = 1 / 6 := by simp [pointR]; norm_num
  constructor
  · rintro ⟨σ, rfl⟩
    have : ∀ σ : Equiv.Perm (Fin 3),
        (σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2) ∨ (σ 0 = 0 ∧ σ 1 = 2 ∧ σ 2 = 1) ∨
        (σ 0 = 1 ∧ σ 1 = 0 ∧ σ 2 = 2) ∨ (σ 0 = 1 ∧ σ 1 = 2 ∧ σ 2 = 0) ∨
        (σ 0 = 2 ∧ σ 1 = 0 ∧ σ 2 = 1) ∨ (σ 0 = 2 ∧ σ 1 = 1 ∧ σ 2 = 0) := by decide
    rcases this σ with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
    · left; funext i; fin_cases i <;> simp [a, b, c, e0, e1, e2]
    · left; funext i; fin_cases i <;> simp [a, b, c, e0, e1, e2]
    · right; left; funext i; fin_cases i <;> simp [a, b, c, e0, e1, e2]
    · right; right; funext i; fin_cases i <;> simp [a, b, c, e0, e1, e2]
    · right; left; funext i; fin_cases i <;> simp [a, b, c, e0, e1, e2]
    · right; right; funext i; fin_cases i <;> simp [a, b, c, e0, e1, e2]
  · rintro (rfl | rfl | rfl)
    · refine ⟨1, ?_⟩
      funext i; fin_cases i <;> simp [e0, e1, e2]
    · have s2 : Equiv.swap (0 : Fin 3) 1 2 = 2 :=
        Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
      refine ⟨Equiv.swap 0 1, ?_⟩
      funext i; fin_cases i <;> simp [s2, e0, e1, e2]
    · have s1 : Equiv.swap (0 : Fin 3) 2 1 = 1 :=
        Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
      refine ⟨Equiv.swap 0 2, ?_⟩
      funext i; fin_cases i <;> simp [s1, e0, e1, e2]

/-- An interior global minimizer of `F_β` on the simplex is an interior critical point. -/
lemma isInteriorCriticalPoint_of_isMinOn (β : ℝ) {p : Fin 3 → ℝ} (hp : p ∈ simplex)
    (hpos : ∀ i, 0 < p i) (hmin : IsMinOn (freeEnergy β) simplex p) :
    IsInteriorCriticalPoint β p := by
  refine ⟨hp, hpos, fun h hh => ?_⟩
  have hd := hasDerivAt_freeEnergy_line β p h hpos
  have hloc : IsLocalMin (fun t : ℝ => freeEnergy β (p + t • h)) 0 := by
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, 0 < p i + t * h i := by
      rw [Filter.eventually_all]
      intro i
      have hc : ContinuousAt (fun t : ℝ => p i + t * h i) 0 := by fun_prop
      exact (continuousAt_const (y := (0 : ℝ))).eventually_lt hc (by simpa using hpos i)
    filter_upwards [hev] with t ht
    have hmem : p + t • h ∈ simplex := by
      refine ⟨fun i => ?_, ?_⟩
      · simpa using (ht i).le
      · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hh, hp.2]
    simpa using (isMinOn_iff.1 hmin) _ hmem
  have h0 := hloc.hasDerivAt_eq_zero hd
  rw [h0] at hd
  exact hd

/-- Four positive zeros of `f_β` are impossible: Rolle gives three distinct roots of the
quadratic numerator of `f_β'`. -/
lemma criticalFunction_no_four_zeros (β : ℝ) {a b c d : ℝ} (ha : 0 < a) (hab : a < b)
    (hbc : b < c) (hcd : c < d) (fa : criticalFunction β a = 0) (fb : criticalFunction β b = 0)
    (fc : criticalFunction β c = 0) (fd : criticalFunction β d = 0) : False := by
  have rolle : ∀ x y : ℝ, 0 < x → x < y → criticalFunction β x = criticalFunction β y →
      ∃ z ∈ Set.Ioo x y, z ^ 2 + (4 - 3 * β) * z + 4 = 0 := by
    intro x y hx hxy hfxy
    have hcont : ContinuousOn (criticalFunction β) (Set.Icc x y) := fun z hz =>
      (hasDerivAt_criticalFunction β (lt_of_lt_of_le hx hz.1)).continuousAt.continuousWithinAt
    obtain ⟨z, hz, hz0⟩ := exists_hasDerivAt_eq_zero hxy hcont hfxy
      (fun z hz => hasDerivAt_criticalFunction β (by linarith [hz.1]))
    have hzpos : 0 < z := by linarith [hz.1]
    refine ⟨z, hz, ?_⟩
    have hden : z * (z + 2) ^ 2 ≠ 0 := by positivity
    rcases div_eq_zero_iff.1 hz0 with h | h
    · exact h
    · exact absurd h hden
  obtain ⟨z1, hz1, q1⟩ := rolle a b ha hab (by rw [fa, fb])
  obtain ⟨z2, hz2, q2⟩ := rolle b c (by linarith) hbc (by rw [fb, fc])
  obtain ⟨z3, hz3, q3⟩ := rolle c d (by linarith) hcd (by rw [fc, fd])
  obtain ⟨-, h1⟩ := hz1
  obtain ⟨h2, h2'⟩ := hz2
  obtain ⟨h3, -⟩ := hz3
  have e12 : (z1 - z2) * (z1 + z2 + (4 - 3 * β)) = 0 := by linear_combination q1 - q2
  have e13 : (z1 - z3) * (z1 + z3 + (4 - 3 * β)) = 0 := by linear_combination q1 - q3
  have n12 : z1 - z2 ≠ 0 := by intro h; linarith
  have n13 : z1 - z3 ≠ 0 := by intro h; linarith
  have s12 := (mul_eq_zero.1 e12).resolve_left n12
  have s13 := (mul_eq_zero.1 e13).resolve_left n13
  linarith

/-- At `β_c = 4 log 2` the positive zeros of `f_β` are exactly `1, 2, 4`. -/
lemma criticalFunction_coexistence_zeros (r : ℝ) (hr : 0 < r) :
    criticalFunction (4 * Real.log 2) r = 0 ↔ r = 1 ∨ r = 2 ∨ r = 4 := by
  have z1 : criticalFunction (4 * Real.log 2) 1 = 0 := by simp [criticalFunction]
  have z2 : criticalFunction (4 * Real.log 2) 2 = 0 := by
    simp only [criticalFunction]; norm_num
  have z4 : criticalFunction (4 * Real.log 2) 4 = 0 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    simp only [criticalFunction, this]; norm_num; ring
  constructor
  · intro hf
    by_contra hne
    push Not at hne
    obtain ⟨n1, n2, n4⟩ := hne
    rcases lt_or_gt_of_ne n1 with h1 | h1
    · exact criticalFunction_no_four_zeros _ hr h1 (by norm_num) (by norm_num) hf z1 z2 z4
    · rcases lt_or_gt_of_ne n2 with h2 | h2
      · exact criticalFunction_no_four_zeros _ (by norm_num) h1 h2 (by norm_num) z1 hf z2 z4
      · rcases lt_or_gt_of_ne n4 with h4 | h4
        · exact criticalFunction_no_four_zeros _ (by norm_num) (by norm_num) h2 h4 z1 z2 hf z4
        · exact criticalFunction_no_four_zeros _ (by norm_num) (by norm_num) (by norm_num) h4
            z1 z2 z4 hf
  · rintro (rfl | rfl | rfl) <;> assumption

/-- **RUF014, coexistence parameter and global positivity.** At `β_c = 4 log 2` (which satisfies
`8/3 < β_c < 3`) the positive roots of `f_{β_c}` are exactly `1, 2, 4`; the global minimizers of
`F_{β_c}` on the simplex are exactly the uniform point and the three permutations of
`p(4) = (2/3, 1/6, 1/6)`, all with value `0`; hence `F_{β_c} ≥ 0` on the simplex. For every
`β` (in particular `β < β_c`) one has `F_β = F_{β_c} + ((β_c - β)/2) ∑ (pᵢ - 1/3)²` on the
simplex, and for `β < β_c` the uniform point is the unique global minimizer. -/
theorem coexistence_parameter_and_global_positivity :
    (8 / 3 < 4 * Real.log 2 ∧ 4 * Real.log 2 < 3) ∧
    (∀ r : ℝ, 0 < r → (criticalFunction (4 * Real.log 2) r = 0 ↔ r = 1 ∨ r = 2 ∨ r = 4)) ∧
    (∀ p ∈ simplex, (IsMinOn (freeEnergy (4 * Real.log 2)) simplex p ↔
      (p = fun _ => 1 / 3) ∨ p = ![2 / 3, 1 / 6, 1 / 6] ∨ p = ![1 / 6, 2 / 3, 1 / 6] ∨
        p = ![1 / 6, 1 / 6, 2 / 3])) ∧
    freeEnergy (4 * Real.log 2) (fun _ => 1 / 3) = 0 ∧
    freeEnergy (4 * Real.log 2) ![2 / 3, 1 / 6, 1 / 6] = 0 ∧
    freeEnergy (4 * Real.log 2) ![1 / 6, 2 / 3, 1 / 6] = 0 ∧
    freeEnergy (4 * Real.log 2) ![1 / 6, 1 / 6, 2 / 3] = 0 ∧
    (∀ p ∈ simplex, 0 ≤ freeEnergy (4 * Real.log 2) p) ∧
    (∀ β : ℝ, ∀ p ∈ simplex, freeEnergy β p =
      freeEnergy (4 * Real.log 2) p + ((4 * Real.log 2 - β) / 2) * ∑ i, (p i - 1 / 3) ^ 2) ∧
    (∀ β : ℝ, β < 4 * Real.log 2 → ∀ p ∈ simplex,
      (IsMinOn (freeEnergy β) simplex p ↔ p = fun _ => 1 / 3)) := by
  obtain ⟨hl1, -, -, hl2, -, -⟩ := exact_logarithmic_inequalities
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hβpos : 0 < 4 * Real.log 2 := by linarith
  set βc : ℝ := 4 * Real.log 2 with hβc
  have hpt : ∀ σ : Equiv.Perm (Fin 3), freeEnergy βc (fun i => pointR 4 (σ i)) = 0 := fun σ => by
    rw [freeEnergy_perm]; exact freeEnergy_pointR_four
  have hp4 : pointR 4 = ![2 / 3, 1 / 6, 1 / 6] := by
    funext i; fin_cases i <;> simp [pointR] <;> norm_num
  have hF4a : freeEnergy βc ![2 / 3, 1 / 6, 1 / 6] = 0 := by rw [← hp4]; exact freeEnergy_pointR_four
  have hF4b : freeEnergy βc ![1 / 6, 2 / 3, 1 / 6] = 0 := by
    obtain ⟨σ, hσ⟩ := (pointR_four_perm_iff ![1 / 6, 2 / 3, 1 / 6]).2 (Or.inr (Or.inl rfl))
    rw [hσ]; exact hpt σ
  have hF4c : freeEnergy βc ![1 / 6, 1 / 6, 2 / 3] = 0 := by
    obtain ⟨σ, hσ⟩ := (pointR_four_perm_iff ![1 / 6, 1 / 6, 2 / 3]).2 (Or.inr (Or.inr rfl))
    rw [hσ]; exact hpt σ
  have hpt2 : ∀ σ : Equiv.Perm (Fin 3), 0 < freeEnergy βc (fun i => pointR 2 (σ i)) := fun σ => by
    rw [freeEnergy_perm]; exact freeEnergy_pointR_two_pos
  have hzeros := criticalFunction_coexistence_zeros
  have hunif : freeEnergy βc (fun _ => 1 / 3) = 0 := freeEnergy_uniform βc
  -- classification of a minimizer of value at most `0`
  have classify : ∀ p ∈ simplex, IsMinOn (freeEnergy βc) simplex p →
      (p = fun _ => 1 / 3) ∨ ∃ σ : Equiv.Perm (Fin 3), p = fun i => pointR 4 (σ i) := by
    intro p hp hmin
    have hpos := (simplex_boundary_cannot_minimize βc).2.2 p hp hmin
    have hcrit := isInteriorCriticalPoint_of_isMinOn βc hp hpos hmin
    have hle : freeEnergy βc p ≤ 0 := by
      rw [← hunif]; exact (isMinOn_iff.1 hmin) _ uniform_mem_simplex
    rcases (complete_interior_critical_point_reduction βc hβpos).1 p hcrit with h | ⟨r, hr, hr1, hf, σ, hσ⟩
    · exact Or.inl h
    · right
      rcases (hzeros r hr).1 hf with h | h | h
      · exact absurd h hr1
      · subst h
        have := hpt2 σ
        rw [← hσ] at this
        linarith
      · subst h
        exact ⟨σ, hσ⟩
  have hnonneg : ∀ p ∈ simplex, 0 ≤ freeEnergy βc p := by
    obtain ⟨m, hm, hmin⟩ := (simplex_boundary_cannot_minimize βc).2.1
    have hm0 : freeEnergy βc m = 0 := by
      rcases classify m hm hmin with h | ⟨σ, h⟩
      · rw [h]; exact hunif
      · rw [h]; exact hpt σ
    intro p hp
    have := (isMinOn_iff.1 hmin) p hp
    linarith
  have hident : ∀ β : ℝ, ∀ p ∈ simplex, freeEnergy β p =
      freeEnergy βc p + ((βc - β) / 2) * ∑ i, (p i - 1 / 3) ^ 2 := by
    intro β p hp
    have hs := hp.2
    rw [Fin.sum_univ_three] at hs
    simp only [freeEnergy, Fin.sum_univ_three]
    linear_combination ((βc - β) / 2 * (2 / 3)) * hs
  refine ⟨⟨by linarith [hl1], by linarith [hl2]⟩, hzeros, ?_, hunif, hF4a, hF4b, hF4c, hnonneg,
    hident, ?_⟩
  · intro p hp
    constructor
    · intro hmin
      rcases classify p hp hmin with h | h
      · exact Or.inl h
      · exact Or.inr ((pointR_four_perm_iff p).1 h)
    · intro h
      have hv : ∀ q, freeEnergy βc q = 0 → q ∈ simplex → IsMinOn (freeEnergy βc) simplex q := by
        intro q hq _
        refine isMinOn_iff.2 fun x hx => ?_
        rw [hq]; exact hnonneg x hx
      rcases h with rfl | h | h | h
      · exact hv _ hunif uniform_mem_simplex
      · subst h; exact hv _ hF4a hp
      · subst h; exact hv _ hF4b hp
      · subst h; exact hv _ hF4c hp
  · intro β hβ p hp
    have hc : 0 < (βc - β) / 2 := by linarith
    have hsq : 0 ≤ ∑ i, (p i - 1 / 3) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    constructor
    · intro hmin
      have hle : freeEnergy β p ≤ 0 := by
        rw [← freeEnergy_uniform β]; exact (isMinOn_iff.1 hmin) _ uniform_mem_simplex
      have h1 := hident β p hp
      have h2 := hnonneg p hp
      have hz : ∑ i, (p i - 1 / 3) ^ 2 = 0 := by nlinarith
      have hz' := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (p i - 1 / 3))).1 hz
      funext i
      have := hz' i (Finset.mem_univ i)
      have := pow_eq_zero_iff (two_ne_zero) |>.1 this
      linarith
    · rintro rfl
      refine isMinOn_iff.2 fun x hx => ?_
      rw [freeEnergy_uniform]
      have h1 := hident β x hx
      have h2 := hnonneg x hx
      have : 0 ≤ ∑ i, (x i - 1 / 3) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      nlinarith

/-! ### RUF015: complete roots and critical landscape at `β₀ = 11/4` -/

section RUF015

open Filter Topology


/-! ### RUF015: complete roots and critical landscape at `β₀ = 11/4` -/

/-- The first derivative `∑ hᵢ (log (3 pᵢ) + 1 - β pᵢ)` of `F_β` at `p` in direction `h`. -/
noncomputable def freeDeriv (β : ℝ) (p h : Fin 3 → ℝ) : ℝ :=
  ∑ i, h i * (Real.log (3 * p i) + 1 - β * p i)

lemma freeDeriv_perm (β : ℝ) (p h : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) :
    freeDeriv β (fun i => p (σ i)) h = freeDeriv β p (fun i => h (σ.symm i)) := by
  unfold freeDeriv
  rw [← Equiv.sum_comp σ (fun j => h (σ.symm j) * (Real.log (3 * p j) + 1 - β * p j))]
  simp

lemma hessianForm_perm (β : ℝ) (p h : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) :
    hessianForm β (fun i => p (σ i)) h = hessianForm β p (fun i => h (σ.symm i)) := by
  unfold hessianForm
  rw [← Equiv.sum_comp σ (fun j => (1 / p j - β) * h (σ.symm j) ^ 2)]
  simp

lemma freeDeriv_eq_zero_of_crit {β : ℝ} {p : Fin 3 → ℝ} (hc : IsInteriorCriticalPoint β p)
    (h : Fin 3 → ℝ) (hh : ∑ i, h i = 0) : freeDeriv β p h = 0 :=
  (hasDerivAt_freeEnergy_line β p h hc.2.1).unique (hc.2.2 h hh)

lemma isInteriorCriticalPoint_of_freeDeriv {β : ℝ} {p : Fin 3 → ℝ} (hp : p ∈ simplex)
    (hpos : ∀ i, 0 < p i) (h0 : ∀ h : Fin 3 → ℝ, ∑ i, h i = 0 → freeDeriv β p h = 0) :
    IsInteriorCriticalPoint β p := by
  refine ⟨hp, hpos, fun h hh => ?_⟩
  have := hasDerivAt_freeEnergy_line β p h hpos
  have e : (∑ i, h i * (Real.log (3 * p i) + 1 - β * p i)) = 0 := h0 h hh
  rw [e] at this
  exact this

lemma isInteriorCriticalPoint_perm {β : ℝ} {p : Fin 3 → ℝ} (hc : IsInteriorCriticalPoint β p)
    (σ : Equiv.Perm (Fin 3)) : IsInteriorCriticalPoint β (fun i => p (σ i)) := by
  refine isInteriorCriticalPoint_of_freeDeriv ⟨fun i => hc.1.1 _, ?_⟩ (fun i => hc.2.1 _)
    (fun h hh => ?_)
  · rw [Equiv.sum_comp σ p]; exact hc.1.2
  · rw [freeDeriv_perm]
    refine freeDeriv_eq_zero_of_crit hc _ ?_
    rw [Equiv.sum_comp σ.symm h]; exact hh

lemma isInteriorCriticalPoint_pointR (β r : ℝ) (hr : 0 < r) (hf : criticalFunction β r = 0) :
    IsInteriorCriticalPoint β (pointR r) := by
  have h2 : 0 < r + 2 := by linarith
  have hpos : ∀ i, 0 < pointR r i := by
    intro i; fin_cases i <;> simp [pointR] <;> positivity
  refine isInteriorCriticalPoint_of_freeDeriv ⟨fun i => (hpos i).le, ?_⟩ hpos (fun h hh => ?_)
  · simp [Fin.sum_univ_three, pointR]
    field_simp
    ring
  · have l0 : Real.log (3 * (r / (r + 2))) = Real.log 3 + Real.log r - Real.log (r + 2) := by
      rw [show 3 * (r / (r + 2)) = 3 * r / (r + 2) by ring, Real.log_div (by positivity) h2.ne',
        Real.log_mul (by norm_num) hr.ne']
    have l1 : Real.log (3 * (1 / (r + 2))) = Real.log 3 - Real.log (r + 2) := by
      rw [show 3 * (1 / (r + 2)) = 3 / (r + 2) by ring, Real.log_div (by norm_num) h2.ne']
    rw [Fin.sum_univ_three] at hh
    have hf' : Real.log r = β * (r - 1) / (r + 2) := by
      unfold criticalFunction at hf; linarith
    simp only [freeDeriv, Fin.sum_univ_three, pointR]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, l0, l1]
    have e : β * (r - 1) / (r + 2) = β * (r / (r + 2)) - β * (1 / (r + 2)) := by
      field_simp
    have h0 : h 0 = -(h 1 + h 2) := by linarith
    rw [h0]
    rw [e] at hf'
    linear_combination (-(h 1 + h 2)) * hf'

lemma hasDerivAt_lineDeriv (β : ℝ) (p h : Fin 3 → ℝ) {t : ℝ} (hp : ∀ i, 0 < p i + t * h i) :
    HasDerivAt (fun s : ℝ => ∑ i, h i * (Real.log (3 * (p i + s * h i)) + 1 - β * (p i + s * h i)))
      (∑ i, (1 / (p i + t * h i) - β) * h i ^ 2) t := by
  have hterm : ∀ i : Fin 3, HasDerivAt
      (fun s : ℝ => h i * (Real.log (3 * (p i + s * h i)) + 1 - β * (p i + s * h i)))
      ((1 / (p i + t * h i) - β) * h i ^ 2) t := by
    intro i
    have hl : HasDerivAt (fun s : ℝ => p i + s * h i) (h i) t := by
      simpa using ((hasDerivAt_id t).mul_const (h i)).const_add (p i)
    have hlog : HasDerivAt (fun s : ℝ => Real.log (3 * (p i + s * h i)))
        (3 * h i / (3 * (p i + t * h i))) t :=
      (hl.const_mul 3).log (mul_pos (by norm_num) (hp i)).ne'
    have := (hlog.add_const 1).sub (hl.const_mul β) |>.const_mul (h i)
    convert this using 1
    have := (hp i).ne'
    field_simp
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hterm i)

lemma tendsto_line_nhdsWithin_simplex {p : Fin 3 → ℝ} (hp : p ∈ simplex) (hpos : ∀ i, 0 < p i)
    {h : Fin 3 → ℝ} (hh : ∑ i, h i = 0) :
    Tendsto (fun t : ℝ => p + t • h) (𝓝 0) (𝓝[simplex] p) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Continuous fun t : ℝ => p + t • h := by fun_prop
    simpa using this.tendsto 0
  · have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, 0 < p i + t * h i := by
      rw [Filter.eventually_all]
      intro i
      have hc : ContinuousAt (fun t : ℝ => p i + t * h i) 0 := by fun_prop
      exact (continuousAt_const (y := (0 : ℝ))).eventually_lt hc (by simpa using hpos i)
    filter_upwards [hev] with t ht
    refine ⟨fun i => ?_, ?_⟩
    · simpa using (ht i).le
    · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hh, hp.2]

lemma isLocalMin_line_of_isLocalMinOn (β : ℝ) {p : Fin 3 → ℝ} (hp : p ∈ simplex)
    (hpos : ∀ i, 0 < p i) (hloc : IsLocalMinOn (freeEnergy β) simplex p) {h : Fin 3 → ℝ}
    (hh : ∑ i, h i = 0) : IsLocalMin (fun t : ℝ => freeEnergy β (p + t • h)) 0 := by
  have := (tendsto_line_nhdsWithin_simplex hp hpos hh).eventually hloc
  filter_upwards [this] with t ht
  simpa using ht

/-- A local minimizer of `F_β` on the simplex with positive coordinates is an interior critical
point. -/
lemma isInteriorCriticalPoint_of_isLocalMinOn (β : ℝ) {p : Fin 3 → ℝ} (hp : p ∈ simplex)
    (hpos : ∀ i, 0 < p i) (hloc : IsLocalMinOn (freeEnergy β) simplex p) :
    IsInteriorCriticalPoint β p := by
  refine ⟨hp, hpos, fun h hh => ?_⟩
  have hd := hasDerivAt_freeEnergy_line β p h hpos
  have h0 := (isLocalMin_line_of_isLocalMinOn β hp hpos hloc hh).hasDerivAt_eq_zero hd
  rw [h0] at hd
  exact hd

/-- A critical point whose constrained Hessian is negative in some tangent direction is not a
local minimizer on the simplex. -/
lemma not_isLocalMinOn_of_hessian_neg (β : ℝ) {p : Fin 3 → ℝ} (hc : IsInteriorCriticalPoint β p)
    {h : Fin 3 → ℝ} (hh : ∑ i, h i = 0) (hneg : hessianForm β p h < 0) :
    ¬ IsLocalMinOn (freeEnergy β) simplex p := by
  intro hloc
  obtain ⟨hp, hpos, -⟩ := hc
  set G : ℝ → ℝ := fun t => freeEnergy β (p + t • h) with hG
  have hmin : IsLocalMin G 0 := isLocalMin_line_of_isLocalMinOn β hp hpos hloc hh
  have hd1 : HasDerivAt G (freeDeriv β p h) 0 := hasDerivAt_freeEnergy_line β p h hpos
  have hcrit : freeDeriv β p h = 0 := by
    have := hmin.hasDerivAt_eq_zero hd1
    exact this
  have hd2 : HasDerivAt (deriv G) (hessianForm β p h) 0 := secondDeriv_freeEnergy_line β p h hpos
  have hdG0 : deriv G 0 = 0 := by rw [hd1.deriv, hcrit]
  have hGc : Continuous G := (continuous_freeEnergy β).comp (by fun_prop)
  have hQ := hd2.tendsto_slope_zero_right
  have hneg' : ∀ᶠ t in 𝓝[>] (0 : ℝ), deriv G t < 0 := by
    have hlt : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (deriv G (0 + t) - deriv G 0) < 0 :=
      hQ.eventually (gt_mem_nhds hneg)
    filter_upwards [hlt, self_mem_nhdsWithin] with t ht ht0
    have ht0' : 0 < t := ht0
    simp only [zero_add, hdG0, sub_zero, smul_eq_mul] at ht
    by_contra hcon
    exact absurd ht (not_lt.2 (mul_nonneg (inv_nonneg.2 ht0'.le) (not_lt.1 hcon)))
  obtain ⟨u, hu0, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hneg'
  have hu : 0 < u := hu0
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 hmin
  set t0 : ℝ := min (ρ / 2) (u / 2) with ht0
  have ht0pos : 0 < t0 := lt_min (by linarith) (by linarith)
  have ht0u : t0 ≤ u / 2 := min_le_right _ _
  have ht0ρ : t0 ≤ ρ / 2 := min_le_left _ _
  have hanti : StrictAntiOn G (Set.Icc 0 t0) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc 0 t0) hGc.continuousOn fun x hx => ?_
    rw [interior_Icc] at hx
    exact hsub ⟨hx.1, by linarith [hx.2]⟩
  have hlt : G t0 < G 0 := hanti ⟨le_refl 0, ht0pos.le⟩ ⟨ht0pos.le, le_refl _⟩ ht0pos
  have hge : G 0 ≤ G t0 := hball (by rw [Real.dist_eq, sub_zero, abs_of_pos ht0pos]; linarith)
  linarith

/-- Quantitative second-order sufficient condition: a critical point with constrained Hessian
bounded below by `κ ∑ hᵢ²` has a neighbourhood in the simplex on which
`F_β(q) ≥ F_β(p) + (κ/4) ∑ (qᵢ - pᵢ)²`. -/
lemma quadratic_lower_of_hessian_pos (β : ℝ) {p : Fin 3 → ℝ} (hc : IsInteriorCriticalPoint β p)
    {κ : ℝ} (hκ : 0 < κ)
    (hQ : ∀ h : Fin 3 → ℝ, ∑ i, h i = 0 → κ * ∑ i, h i ^ 2 ≤ hessianForm β p h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ simplex, dist q p < δ →
      freeEnergy β p + κ / 4 * ∑ i, (q i - p i) ^ 2 ≤ freeEnergy β q := by
  obtain ⟨hp, hpos, hcrit⟩ := hc
  set m : ℝ := min (p 0) (min (p 1) (p 2)) with hm
  have hm0 : 0 < m := lt_min (hpos 0) (lt_min (hpos 1) (hpos 2))
  have hmi : ∀ i, m ≤ p i := by
    intro i; fin_cases i
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  set δ : ℝ := min (m / 2) (κ * m ^ 2 / 4) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by positivity)
  have hδ1 : δ ≤ m / 2 := min_le_left _ _
  have hδ2 : δ ≤ κ * m ^ 2 / 4 := min_le_right _ _
  have hball : ∀ q ∈ Metric.ball p δ, q ∈ simplex →
      freeEnergy β p + κ / 4 * ∑ i, (q i - p i) ^ 2 ≤ freeEnergy β q := by
    intro q hqb hq
    rw [Metric.mem_ball, dist_pi_lt_iff hδ0] at hqb
    set h : Fin 3 → ℝ := q - p with hhdef
    have hh : ∑ i, h i = 0 := by
      simp [hhdef, Finset.sum_sub_distrib, hq.2, hp.2]
    have hhi : ∀ i, |h i| < δ := fun i => by
      have := hqb i
      rw [Real.dist_eq] at this
      simpa [hhdef, abs_sub_comm] using this
    have hqeq : q = p + (1 : ℝ) • h := by simp [hhdef]
    -- lower bound on p i + t h i
    have hpt : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ i, p i / 2 ≤ p i + t * h i := by
      intro t ht i
      have h1 : |t * h i| ≤ |h i| := by
        rw [abs_mul, abs_of_nonneg ht.1]
        exact mul_le_of_le_one_left (abs_nonneg _) ht.2
      have h2 := (abs_le.1 (h1.trans (hhi i).le)).1
      have := hmi i
      linarith
    have hptpos : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ i, 0 < p i + t * h i := fun t ht i => by
      have := hpt t ht i; have := hpos i; linarith
    set S : ℝ := ∑ i, h i ^ 2 with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
    set c : ℝ := κ / 2 * S with hcdef
    have hc0 : 0 ≤ c := by positivity
    set D : ℝ → ℝ := fun t => ∑ i, h i * (Real.log (3 * (p i + t * h i)) + 1 - β * (p i + t * h i))
      with hD
    set E : ℝ → ℝ := fun t => ∑ i, (1 / (p i + t * h i) - β) * h i ^ 2 with hE
    have hDd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt D (E t) t := fun t ht =>
      hasDerivAt_lineDeriv β p h (hptpos t ht)
    have hGd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => freeEnergy β (p + s • h)) (D t) t := fun t ht =>
      hasDerivAt_line_shift β p h (hptpos t ht)
    have hD0 : D 0 = 0 := by
      have := freeDeriv_eq_zero_of_crit ⟨hp, hpos, hcrit⟩ h hh
      simpa [hD, freeDeriv] using this
    have hinv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i, 1 / p i - κ / 2 ≤ 1 / (p i + t * h i) := by
      intro t ht i
      have hapos := hpos i
      have hs := hptpos t ht i
      have hma := hmi i
      have hsδ : t * h i < δ := by
        have h1 : |t * h i| ≤ |h i| := by
          rw [abs_mul, abs_of_nonneg ht.1]
          exact mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _) |>.trans (by simp)
        exact lt_of_le_of_lt (le_abs_self _) (h1.trans_lt (hhi i))
      rw [le_div_iff₀ hs]
      have e : (1 / p i - κ / 2) * (p i + t * h i) = 1 + t * h i / p i - κ / 2 * (p i + t * h i) := by
        field_simp
      rw [e]
      suffices t * h i / p i ≤ κ / 2 * (p i + t * h i) by linarith
      rcases le_or_gt (t * h i) 0 with hle | hgt
      · have : t * h i / p i ≤ 0 := div_nonpos_of_nonpos_of_nonneg hle hapos.le
        have : 0 < κ / 2 * (p i + t * h i) := by positivity
        linarith
      · rw [div_le_iff₀ hapos]
        have h1 : κ * m ^ 2 ≤ κ * p i ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0.le hma 2) hκ.le
        nlinarith
    have hEc : ∀ t ∈ Set.Icc (0 : ℝ) 1, c ≤ E t := by
      intro t ht
      have hQh := hQ h hh
      have hterm : ∀ i : Fin 3, ((1 / p i - β) * h i ^ 2) - κ / 2 * h i ^ 2 ≤
          (1 / (p i + t * h i) - β) * h i ^ 2 := by
        intro i
        have := mul_le_mul_of_nonneg_right (hinv t ht i) (sq_nonneg (h i))
        nlinarith
      have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
      have e1 : (∑ i, (1 / p i - β) * h i ^ 2) = hessianForm β p h := rfl
      rw [e1] at hsum
      simp only [hE, hcdef]
      linarith
    have hA : MonotoneOn (fun t : ℝ => D t - c * t) (Set.Icc 0 1) := by
      have hAd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt (fun t : ℝ => D t - c * t) (E t - c * 1) t := fun t ht =>
        (hDd t ht).sub ((hasDerivAt_id' t).const_mul c)
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (fun t ht => ?_) (fun t ht => ?_)
        (fun t ht => ?_)
      · exact (hAd t ht).continuousAt.continuousWithinAt
      · rw [interior_Icc] at ht
        exact (hAd t ⟨ht.1.le, ht.2.le⟩).differentiableAt.differentiableWithinAt
      · rw [interior_Icc] at ht
        rw [(hAd t ⟨ht.1.le, ht.2.le⟩).deriv]
        have := hEc t ⟨ht.1.le, ht.2.le⟩
        linarith
    have hD1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, c * t ≤ D t := by
      intro t ht
      have := hA ⟨le_refl 0, zero_le_one⟩ ht ht.1
      simp only [hD0, mul_zero, sub_zero] at this
      linarith
    have hB : MonotoneOn (fun t : ℝ => freeEnergy β (p + t • h) - c / 2 * (t * t)) (Set.Icc 0 1) := by
      have hBd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt (fun t : ℝ => freeEnergy β (p + t • h) - c / 2 * (t * t))
            (D t - c / 2 * (1 * t + t * 1)) t := fun t ht =>
        (hGd t ht).sub (((hasDerivAt_id' t).mul (hasDerivAt_id' t)).const_mul (c / 2))
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (fun t ht => ?_) (fun t ht => ?_)
        (fun t ht => ?_)
      · exact (hBd t ht).continuousAt.continuousWithinAt
      · rw [interior_Icc] at ht
        exact (hBd t ⟨ht.1.le, ht.2.le⟩).differentiableAt.differentiableWithinAt
      · rw [interior_Icc] at ht
        rw [(hBd t ⟨ht.1.le, ht.2.le⟩).deriv]
        have := hD1 t ⟨ht.1.le, ht.2.le⟩
        linarith
    have h01 := hB ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
    simp only [zero_smul, add_zero, mul_zero, sub_zero, one_smul, mul_one] at h01
    have hS' : ∑ i, (q i - p i) ^ 2 = S := by simp [hS, hhdef]
    rw [hS', hqeq, one_smul]
    linarith
  exact ⟨δ, hδ0, fun q hq hqb => hball q (Metric.mem_ball.2 hqb) hq⟩

/-- Second-order sufficient condition: a critical point with positive-definite constrained
Hessian is a local minimizer of `F_β` on the simplex. -/
lemma isLocalMinOn_of_hessian_pos (β : ℝ) {p : Fin 3 → ℝ} (hc : IsInteriorCriticalPoint β p)
    {κ : ℝ} (hκ : 0 < κ)
    (hQ : ∀ h : Fin 3 → ℝ, ∑ i, h i = 0 → κ * ∑ i, h i ^ 2 ≤ hessianForm β p h) :
    IsLocalMinOn (freeEnergy β) simplex p := by
  obtain ⟨δ, hδ, hb⟩ := quadratic_lower_of_hessian_pos β hc hκ hQ
  rw [IsLocalMinOn, IsMinFilter, eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds p hδ] with q hqb hq
  have := hb q hq (Metric.mem_ball.1 hqb)
  have h0 : 0 ≤ ∑ i, (q i - p i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith

lemma sqrt33_bounds : 5 < √33 ∧ √33 < 6 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 33 by norm_num)
  have h0 := Real.sqrt_nonneg 33
  constructor <;> nlinarith

lemma numerator_eleven_quarters_factor (r : ℝ) :
    r ^ 2 + (4 - 3 * (11 / 4 : ℝ)) * r + 4 = (r - (17 - √33) / 8) * (r - (17 + √33) / 8) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 33 by norm_num)
  linear_combination (1 / 64 : ℝ) * hs

lemma deriv_criticalFunction_eleven_quarters {r : ℝ} (hr : 0 < r) :
    deriv (criticalFunction (11 / 4)) r =
      ((r - (17 - √33) / 8) * (r - (17 + √33) / 8)) / (r * (r + 2) ^ 2) := by
  rw [(hasDerivAt_criticalFunction (11 / 4) hr).deriv, numerator_eleven_quarters_factor]

lemma criticalFunction_eleven_quarters_values :
    criticalFunction (11 / 4) 2 = Real.log 2 - 11 / 16 ∧
    criticalFunction (11 / 4) 3 = Real.log 3 - 11 / 10 ∧
    criticalFunction (11 / 4) 4 = 2 * Real.log 2 - 11 / 8 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · simp only [criticalFunction]; norm_num
  · simp only [criticalFunction]; norm_num
  · simp only [criticalFunction, h4]; norm_num

lemma criticalFunction_eleven_quarters_signs :
    0 < criticalFunction (11 / 4) 2 ∧ criticalFunction (11 / 4) 3 < 0 ∧
      0 < criticalFunction (11 / 4) 4 := by
  obtain ⟨a, b, c⟩ := criticalFunction_eleven_quarters_values
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := exact_logarithmic_inequalities
  rw [a, b, c]
  refine ⟨?_, ?_, ?_⟩ <;> linarith

lemma criticalFunction_continuousOn_pos {s : Set ℝ} (hs : s ⊆ Set.Ioi 0) (β : ℝ) :
    ContinuousOn (criticalFunction β) s := fun _ hx =>
  (hasDerivAt_criticalFunction β (hs hx)).continuousAt.continuousWithinAt

/-- Roots of `f_{11/4}` and the sign pattern of its derivative. -/
lemma criticalFunction_eleven_quarters_roots :
    ∃ rs rm : ℝ, 2 < rs ∧ rs < (17 + √33) / 8 ∧ 3 < rm ∧ rm < 4 ∧
      criticalFunction (11 / 4) rs = 0 ∧ criticalFunction (11 / 4) rm = 0 ∧
      ∀ r : ℝ, 0 < r → (criticalFunction (11 / 4) r = 0 ↔ r = 1 ∨ r = rs ∨ r = rm) := by
  obtain ⟨s5, s6⟩ := sqrt33_bounds
  set dm : ℝ := (17 - √33) / 8 with hdm
  set dp : ℝ := (17 + √33) / 8 with hdp
  have hdm1 : 1 < dm := by rw [hdm]; linarith
  have hdm2 : dm < 2 := by rw [hdm]; linarith
  have hdp2 : 2 < dp := by rw [hdp]; linarith
  have hdp3 : dp < 3 := by rw [hdp]; linarith
  set f := criticalFunction (11 / 4) with hf
  obtain ⟨f2, f3, f4⟩ := criticalFunction_eleven_quarters_signs
  have f1 : f 1 = 0 := by simp [hf, criticalFunction]
  have hmono1 : StrictMonoOn f (Set.Ioc 0 dm) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioc 0 dm)
      (criticalFunction_continuousOn_pos (fun x hx => hx.1) _) fun x hx => ?_
    rw [interior_Ioc] at hx
    rw [hf, deriv_criticalFunction_eleven_quarters hx.1]
    have : 0 < (x - dm) * (x - dp) := mul_pos_of_neg_of_neg (by linarith [hx.2]) (by linarith [hx.2])
    have hx0 : 0 < x := hx.1
    exact div_pos this (by positivity)
  have hmono2 : StrictAntiOn f (Set.Icc dm dp) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc dm dp)
      (criticalFunction_continuousOn_pos (fun x hx => by
        have := hx.1; exact lt_of_lt_of_le (by linarith) this) _) fun x hx => ?_
    rw [interior_Icc] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [hf, deriv_criticalFunction_eleven_quarters hx0]
    have : (x - dm) * (x - dp) < 0 := mul_neg_of_pos_of_neg (by linarith [hx.1]) (by linarith [hx.2])
    have h2 : 0 < x * (x + 2) ^ 2 := by positivity
    exact div_neg_of_neg_of_pos this h2
  have hmono3 : StrictMonoOn f (Set.Ici dp) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici dp)
      (criticalFunction_continuousOn_pos (fun x hx => by
        have := hx.out; exact lt_of_lt_of_le (by linarith) this) _) fun x hx => ?_
    rw [interior_Ici] at hx
    have hx0 : 0 < x := by have := hx.out; linarith
    rw [hf, deriv_criticalFunction_eleven_quarters hx0]
    have : 0 < (x - dm) * (x - dp) :=
      mul_pos (by have := hx.out; linarith) (by have := hx.out; linarith)
    positivity
  -- the root `rs`
  have hfdp : f dp < 0 := by
    have := hmono3 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hdp3.le) hdp3
    linarith
  obtain ⟨rs, hrs, hfrs⟩ := intermediate_value_Ioo' (a := 2) (b := dp) hdp2.le
    (criticalFunction_continuousOn_pos (fun x hx => by have := hx.1; exact lt_of_lt_of_le (by norm_num) this) _)
    (show (0 : ℝ) ∈ Set.Ioo (f dp) (f 2) from ⟨hfdp, f2⟩)
  obtain ⟨rm, hrm, hfrm⟩ := intermediate_value_Ioo (a := 3) (b := 4) (by norm_num)
    (criticalFunction_continuousOn_pos (fun x hx => by have := hx.1; exact lt_of_lt_of_le (by norm_num) this) _)
    (show (0 : ℝ) ∈ Set.Ioo (f 3) (f 4) from ⟨f3, f4⟩)
  refine ⟨rs, rm, hrs.1, hrs.2, hrm.1, hrm.2, hfrs, hfrm, fun r hr => ⟨fun h0 => ?_, ?_⟩⟩
  · by_cases h1 : r ≤ dm
    · left
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := hmono1 ⟨hr, h1⟩ ⟨one_pos, hdm1.le⟩ hlt
        linarith
      · have := hmono1 ⟨one_pos, hdm1.le⟩ ⟨hr, h1⟩ hgt
        linarith
    · right
      by_cases h2 : r ≤ dp
      · left
        have hmem : r ∈ Set.Icc dm dp := ⟨(not_le.1 h1).le, h2⟩
        have hmem' : rs ∈ Set.Icc dm dp := ⟨by linarith [hrs.1], hrs.2.le⟩
        exact hmono2.injOn hmem hmem' (h0.trans hfrs.symm)
      · right
        have hmem : r ∈ Set.Ici dp := (not_le.1 h2).le
        have hmem' : rm ∈ Set.Ici dp := by
          have := hrm.1; exact Set.mem_Ici.2 (by linarith)
        exact hmono3.injOn hmem hmem' (h0.trans hfrm.symm)
  · rintro (rfl | rfl | rfl)
    · exact f1
    · exact hfrs
    · exact hfrm

/-- The orbit of `p(r) = (r, 1, 1)/(r + 2)` under the coordinate permutations. -/
def pointROrbit (r : ℝ) : Set (Fin 3 → ℝ) :=
  {p | ∃ σ : Equiv.Perm (Fin 3), p = fun i => pointR r (σ i)}

lemma pointROrbit_iff (r : ℝ) (p : Fin 3 → ℝ) :
    p ∈ pointROrbit r ↔
      p = ![r / (r + 2), 1 / (r + 2), 1 / (r + 2)] ∨
        p = ![1 / (r + 2), r / (r + 2), 1 / (r + 2)] ∨
        p = ![1 / (r + 2), 1 / (r + 2), r / (r + 2)] := by
  have e0 : pointR r 0 = r / (r + 2) := by simp [pointR]
  have e1 : pointR r 1 = 1 / (r + 2) := by simp [pointR]
  have e2 : pointR r 2 = 1 / (r + 2) := by simp [pointR]
  constructor
  · rintro ⟨σ, rfl⟩
    have : ∀ σ : Equiv.Perm (Fin 3),
        (σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2) ∨ (σ 0 = 0 ∧ σ 1 = 2 ∧ σ 2 = 1) ∨
        (σ 0 = 1 ∧ σ 1 = 0 ∧ σ 2 = 2) ∨ (σ 0 = 1 ∧ σ 1 = 2 ∧ σ 2 = 0) ∨
        (σ 0 = 2 ∧ σ 1 = 0 ∧ σ 2 = 1) ∨ (σ 0 = 2 ∧ σ 1 = 1 ∧ σ 2 = 0) := by decide
    rcases this σ with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
    · left; funext i; fin_cases i <;> simp [a, b, c, e0, e1, e2]
    · left; funext i; fin_cases i <;> simp [a, b, c, e0, e1, e2]
    · right; left; funext i; fin_cases i <;> simp [a, b, c, e0, e1, e2]
    · right; right; funext i; fin_cases i <;> simp [a, b, c, e0, e1, e2]
    · right; left; funext i; fin_cases i <;> simp [a, b, c, e0, e1, e2]
    · right; right; funext i; fin_cases i <;> simp [a, b, c, e0, e1, e2]
  · rintro (rfl | rfl | rfl)
    · refine ⟨1, ?_⟩
      funext i; fin_cases i <;> simp [e0, e1, e2]
    · have s2 : Equiv.swap (0 : Fin 3) 1 2 = 2 :=
        Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
      refine ⟨Equiv.swap 0 1, ?_⟩
      funext i; fin_cases i <;> simp [s2, e0, e1, e2]
    · have s1 : Equiv.swap (0 : Fin 3) 2 1 = 1 :=
        Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
      refine ⟨Equiv.swap 0 2, ?_⟩
      funext i; fin_cases i <;> simp [s1, e0, e1, e2]

lemma ncard_pointROrbit {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) : (pointROrbit r).ncard = 3 := by
  rw [Set.ncard_eq_three]
  have h2 : (0 : ℝ) < r + 2 := by linarith
  have hab : r / (r + 2) ≠ 1 / (r + 2) := by
    intro h
    rw [div_left_inj' h2.ne'] at h
    exact hr1 h
  refine ⟨![r / (r + 2), 1 / (r + 2), 1 / (r + 2)], ![1 / (r + 2), r / (r + 2), 1 / (r + 2)],
    ![1 / (r + 2), 1 / (r + 2), r / (r + 2)], ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    exact hab this
  · intro h
    have := congrFun h 0
    exact hab this
  · intro h
    have := congrFun h 1
    exact hab this
  · ext p
    rw [pointROrbit_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

lemma sum_comp_perm (h : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) : ∑ i, h (σ i) = ∑ i, h i :=
  Equiv.sum_comp σ h

lemma sum_sq_comp_perm_symm (h : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) :
    ∑ i, h (σ.symm i) ^ 2 = ∑ i, h i ^ 2 :=
  Equiv.sum_comp σ.symm (fun j => h j ^ 2)

lemma exists_hessian_lower_pointR (β r : ℝ) (hr : 1 < r) (hβ : β < 3)
    (hf : 0 < deriv (criticalFunction β) r) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ h : Fin 3 → ℝ, ∑ i, h i = 0 →
      κ * ∑ i, h i ^ 2 ≤ hessianForm β (pointR r) h := by
  have hr0 : 0 < r := by linarith
  have hA : 0 < r + 2 - β := by linarith
  have hB : 0 < (r + 2) ^ 2 * deriv (criticalFunction β) r / 3 := by positivity
  refine ⟨min (r + 2 - β) ((r + 2) ^ 2 * deriv (criticalFunction β) r / 3), lt_min hA hB,
    fun h hh => ?_⟩
  obtain ⟨a, b, rfl⟩ := tangent_decomposition h hh
  rw [hessianForm_pointR_tangent β r hr0, hessianForm_pointR_v β r hr0,
    hessianForm_pointR_w β r hr0]
  have hsq : ∑ i, (a • tangentV + b • tangentW) i ^ 2 = 2 * a ^ 2 + 6 * b ^ 2 := by
    simp [Fin.sum_univ_three, tangentV, tangentW]
    ring
  rw [hsq]
  have k1 := min_le_left (r + 2 - β) ((r + 2) ^ 2 * deriv (criticalFunction β) r / 3)
  have k2 := min_le_right (r + 2 - β) ((r + 2) ^ 2 * deriv (criticalFunction β) r / 3)
  nlinarith [mul_le_mul_of_nonneg_left k1 (sq_nonneg a), mul_le_mul_of_nonneg_left k2 (sq_nonneg b)]

lemma isLocalMinOn_orbit {β r : ℝ} (hc : IsInteriorCriticalPoint β (pointR r)) {κ : ℝ}
    (hκ : 0 < κ)
    (hQ : ∀ h : Fin 3 → ℝ, ∑ i, h i = 0 → κ * ∑ i, h i ^ 2 ≤ hessianForm β (pointR r) h)
    (σ : Equiv.Perm (Fin 3)) :
    IsLocalMinOn (freeEnergy β) simplex (fun i => pointR r (σ i)) := by
  refine isLocalMinOn_of_hessian_pos β (isInteriorCriticalPoint_perm hc σ) hκ fun h hh => ?_
  rw [hessianForm_perm]
  have := hQ (fun i => h (σ.symm i)) (by rw [Equiv.sum_comp σ.symm h]; exact hh)
  rwa [Equiv.sum_comp σ.symm (fun j => h j ^ 2)] at this

lemma exists_negative_direction_orbit (β r : ℝ) (hr : 1 < r) (hβ : β < 3)
    (hf : deriv (criticalFunction β) r < 0) (σ : Equiv.Perm (Fin 3)) :
    ∃ h : Fin 3 → ℝ, ∑ i, h i = 0 ∧ hessianForm β (fun i => pointR r (σ i)) h < 0 := by
  refine ⟨fun i => tangentW (σ i), ?_, ?_⟩
  · rw [Equiv.sum_comp σ tangentW]; exact sum_tangentW
  · rw [hessianForm_perm]
    have hfun : (fun i => tangentW (σ (σ.symm i))) = tangentW := by
      funext i; simp
    rw [hfun]
    exact ((constrained_simplex_hessian β).2.2.2.2 r hr hβ).2.2 hf

lemma pointR_one : pointR 1 = fun _ => (1 / 3 : ℝ) := by
  funext i; fin_cases i <;> simp [pointR] <;> norm_num

lemma uniform_not_mem_pointROrbit {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    (fun _ : Fin 3 => (1 / 3 : ℝ)) ∉ pointROrbit r := by
  rintro ⟨σ, hσ⟩
  have h := congrFun hσ (σ.symm 0)
  simp only [Equiv.apply_symm_apply] at h
  have h2 : (0 : ℝ) < r + 2 := by linarith
  have h0 : pointR r 0 = r / (r + 2) := by simp [pointR]
  rw [h0] at h
  field_simp at h
  exact hr1 (by linarith)

/-- The common gap lower bound: `F_{11/4}(p(r)) ≥ (β_c - 11/4) (r-1)² / (3 (r+2)²)`. -/
lemma freeEnergy_pointR_gap {r : ℝ} (hr : 3 < r) :
    1 / 1215 < freeEnergy (11 / 4) (pointR r) := by
  obtain ⟨-, -, -, -, -, -, -, hnonneg, hident, -⟩ := coexistence_parameter_and_global_positivity
  obtain ⟨hl, -, -, -, -, -⟩ := exact_logarithmic_inequalities
  have hr0 : 0 < r := by linarith
  have h2 : 0 < r + 2 := by linarith
  have hmem : pointR r ∈ simplex := by
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> simp [pointR] <;> positivity
    · simp [Fin.sum_univ_three, pointR]
      field_simp
      ring
  have h1 := hident (11 / 4) _ hmem
  have h3 := hnonneg _ hmem
  have hsum : ∑ i, (pointR r i - 1 / 3) ^ 2 = 2 * (r - 1) ^ 2 / (3 * (r + 2) ^ 2) := by
    simp [Fin.sum_univ_three, pointR]
    field_simp
    ring
  rw [hsum] at h1
  have hx : 2 / 5 ≤ (r - 1) / (r + 2) := by
    rw [le_div_iff₀ h2]; linarith
  have hy : 4 / 25 ≤ ((r - 1) / (r + 2)) ^ 2 := by nlinarith
  have hz : ((r - 1) / (r + 2)) ^ 2 = (r - 1) ^ 2 / (r + 2) ^ 2 := by rw [div_pow]
  have hq : 2 * (r - 1) ^ 2 / (3 * (r + 2) ^ 2) = (2 / 3) * ((r - 1) / (r + 2)) ^ 2 := by
    rw [hz]; field_simp
  rw [hq] at h1
  have hβ : (4 * Real.log 2 - 11 / 4) / 2 > 5 / 648 := by linarith
  have hpos : 0 < (4 * Real.log 2 - 11 / 4) / 2 := by linarith
  nlinarith [mul_pos hpos (by linarith : (0 : ℝ) < ((r - 1) / (r + 2)) ^ 2)]

/-- **RUF015, complete roots and critical landscape at `β₀ = 11/4`.**
The derivative roots `d_± = (17 ± √33)/8` satisfy `1 < d_- < 2 < d_+ < 3`; the positive roots of
`f_{11/4}` are exactly `1`, `r_s ∈ (2, d_+)` and `r_m ∈ (3, 4)`, with `f'(r_s) < 0 < f'(r_m)`.
The interior critical points of `F_{11/4}` are the uniform point and the two orbits
`pointROrbit r_s` (three saddles, each with a negative Hessian direction) and `pointROrbit r_m`
(three nondegenerate local minima); the local minimizers on the simplex are exactly the uniform
point and `pointROrbit r_m`, no boundary point is a local minimizer, the uniform point is the unique
global minimizer, and the common gap `F_{11/4}(p) - F_{11/4}(uniform)` over `p ∈ pointROrbit r_m`
exceeds `1/1215`. -/
theorem complete_roots_and_critical_landscape_at_eleven_quarters :
    (1 < (17 - √33) / 8 ∧ (17 - √33) / 8 < 2 ∧ 2 < (17 + √33) / 8 ∧ (17 + √33) / 8 < 3) ∧
    (∀ r : ℝ, 0 < r → (deriv (criticalFunction (11 / 4)) r = 0 ↔
      r = (17 - √33) / 8 ∨ r = (17 + √33) / 8)) ∧
    ∃ rs rm : ℝ, 2 < rs ∧ rs < (17 + √33) / 8 ∧ 3 < rm ∧ rm < 4 ∧
      (∀ r : ℝ, 0 < r → (criticalFunction (11 / 4) r = 0 ↔ r = 1 ∨ r = rs ∨ r = rm)) ∧
      deriv (criticalFunction (11 / 4)) rs < 0 ∧ 0 < deriv (criticalFunction (11 / 4)) rm ∧
      (∀ p : Fin 3 → ℝ, IsInteriorCriticalPoint (11 / 4) p ↔
        (p = fun _ => 1 / 3) ∨ p ∈ pointROrbit rs ∨ p ∈ pointROrbit rm) ∧
      (∀ p ∈ simplex, IsLocalMinOn (freeEnergy (11 / 4)) simplex p ↔
        (p = fun _ => 1 / 3) ∨ p ∈ pointROrbit rm) ∧
      (∀ p ∈ pointROrbit rs, ¬ IsLocalMinOn (freeEnergy (11 / 4)) simplex p ∧
        ∃ h : Fin 3 → ℝ, ∑ i, h i = 0 ∧ hessianForm (11 / 4) p h < 0) ∧
      (∀ p ∈ simplex, (∃ j, p j = 0) → ¬ IsLocalMinOn (freeEnergy (11 / 4)) simplex p) ∧
      ({fun _ : Fin 3 => (1 / 3 : ℝ)} : Set (Fin 3 → ℝ)).ncard = 1 ∧
      (pointROrbit rs).ncard = 3 ∧ (pointROrbit rm).ncard = 3 ∧
      (fun _ : Fin 3 => (1 / 3 : ℝ)) ∉ pointROrbit rs ∧
      (fun _ : Fin 3 => (1 / 3 : ℝ)) ∉ pointROrbit rm ∧
      Disjoint (pointROrbit rs) (pointROrbit rm) ∧
      (∀ p ∈ simplex, IsMinOn (freeEnergy (11 / 4)) simplex p ↔ p = fun _ => 1 / 3) ∧
      (∀ p ∈ pointROrbit rm, freeEnergy (11 / 4) p = freeEnergy (11 / 4) (pointR rm) ∧
        1 / 1215 < freeEnergy (11 / 4) p - freeEnergy (11 / 4) (fun _ => 1 / 3)) := by
  obtain ⟨s5, s6⟩ := sqrt33_bounds
  obtain ⟨rs, rm, h2rs, hrsdp, h3rm, hrm4, hfrs, hfrm, hroots⟩ :=
    criticalFunction_eleven_quarters_roots
  have hdm1 : 1 < (17 - √33) / 8 := by linarith
  have hdm2 : (17 - √33) / 8 < 2 := by linarith
  have hdp2 : 2 < (17 + √33) / 8 := by linarith
  have hdp3 : (17 + √33) / 8 < 3 := by linarith
  have hder : ∀ r : ℝ, 0 < r → deriv (criticalFunction (11 / 4)) r =
      ((r - (17 - √33) / 8) * (r - (17 + √33) / 8)) / (r * (r + 2) ^ 2) :=
    fun r hr => deriv_criticalFunction_eleven_quarters hr
  have hds : deriv (criticalFunction (11 / 4)) rs < 0 := by
    rw [hder rs (by linarith)]
    refine div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) (by linarith)) ?_
    have : 0 < rs := by linarith
    positivity
  have hdm : 0 < deriv (criticalFunction (11 / 4)) rm := by
    rw [hder rm (by linarith)]
    refine div_pos (mul_pos (by linarith) (by linarith)) ?_
    have : 0 < rm := by linarith
    positivity
  have hrs0 : 0 < rs := by linarith
  have hrm0 : 0 < rm := by linarith
  have hrs1 : rs ≠ 1 := by intro h; linarith
  have hrm1 : rm ≠ 1 := by intro h; linarith
  -- critical points and local-minimum data
  have hcrs := isInteriorCriticalPoint_pointR (11 / 4) rs hrs0 hfrs
  have hcrm := isInteriorCriticalPoint_pointR (11 / 4) rm hrm0 hfrm
  have hu : IsInteriorCriticalPoint (11 / 4) (fun _ => 1 / 3) := by
    have := isInteriorCriticalPoint_pointR (11 / 4) 1 one_pos (by simp [criticalFunction])
    rwa [pointR_one] at this
  obtain ⟨κ, hκ, hQ⟩ := exists_hessian_lower_pointR (11 / 4) rm (by linarith) (by norm_num) hdm
  have hminrm : ∀ σ : Equiv.Perm (Fin 3),
      IsLocalMinOn (freeEnergy (11 / 4)) simplex (fun i => pointR rm (σ i)) :=
    isLocalMinOn_orbit hcrm hκ hQ
  have hsad : ∀ p ∈ pointROrbit rs, ¬ IsLocalMinOn (freeEnergy (11 / 4)) simplex p ∧
      ∃ h : Fin 3 → ℝ, ∑ i, h i = 0 ∧ hessianForm (11 / 4) p h < 0 := by
    rintro p ⟨σ, rfl⟩
    obtain ⟨h, hh, hneg⟩ := exists_negative_direction_orbit (11 / 4) rs (by linarith)
      (by norm_num) hds σ
    exact ⟨not_isLocalMinOn_of_hessian_neg _ (isInteriorCriticalPoint_perm hcrs σ) hh hneg,
      h, hh, hneg⟩
  have hminu : IsLocalMinOn (freeEnergy (11 / 4)) simplex (fun _ => 1 / 3) := by
    refine isLocalMinOn_of_hessian_pos (11 / 4) hu (κ := 1 / 4) (by norm_num) fun h _ => ?_
    rw [(constrained_simplex_hessian (11 / 4)).2.2.2.1 h]
    have : 0 ≤ ∑ i, h i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith
  have hcrit : ∀ p : Fin 3 → ℝ, IsInteriorCriticalPoint (11 / 4) p ↔
      (p = fun _ => 1 / 3) ∨ p ∈ pointROrbit rs ∨ p ∈ pointROrbit rm := by
    intro p
    constructor
    · intro hc
      rcases (complete_interior_critical_point_reduction (11 / 4) (by norm_num)).1 p hc with
        h | ⟨r, hr, hr1, hf, σ, hσ⟩
      · exact Or.inl h
      · rcases (hroots r hr).1 hf with h | h | h
        · exact absurd h hr1
        · subst h; exact Or.inr (Or.inl ⟨σ, hσ⟩)
        · subst h; exact Or.inr (Or.inr ⟨σ, hσ⟩)
    · rintro (rfl | ⟨σ, rfl⟩ | ⟨σ, rfl⟩)
      · exact hu
      · exact isInteriorCriticalPoint_perm hcrs σ
      · exact isInteriorCriticalPoint_perm hcrm σ
  have hloc : ∀ p ∈ simplex, IsLocalMinOn (freeEnergy (11 / 4)) simplex p ↔
      (p = fun _ => 1 / 3) ∨ p ∈ pointROrbit rm := by
    intro p hp
    constructor
    · intro hl
      have hpos : ∀ i, 0 < p i := by
        intro i
        rcases (hp.1 i).lt_or_eq with h | h
        · exact h
        · exact absurd hl ((simplex_boundary_cannot_minimize (11 / 4)).1 p hp ⟨i, h.symm⟩)
      rcases (hcrit p).1 (isInteriorCriticalPoint_of_isLocalMinOn _ hp hpos hl) with h | h | h
      · exact Or.inl h
      · exact absurd hl (hsad p h).1
      · exact Or.inr h
    · rintro (rfl | ⟨σ, rfl⟩)
      · exact hminu
      · exact hminrm σ
  have hβc : (11 / 4 : ℝ) < 4 * Real.log 2 := by
    obtain ⟨hl, -, -, -, -, -⟩ := exact_logarithmic_inequalities
    linarith
  obtain ⟨-, -, -, -, -, -, -, -, -, hglob⟩ := coexistence_parameter_and_global_positivity
  refine ⟨⟨hdm1, hdm2, hdp2, hdp3⟩, ?_, rs, rm, h2rs, hrsdp, h3rm, hrm4, hroots, hds, hdm,
    hcrit, hloc, hsad, (simplex_boundary_cannot_minimize (11 / 4)).1, Set.ncard_singleton _,
    ncard_pointROrbit hrs0 hrs1, ncard_pointROrbit hrm0 hrm1,
    uniform_not_mem_pointROrbit hrs0 hrs1, uniform_not_mem_pointROrbit hrm0 hrm1, ?_,
    hglob (11 / 4) hβc, ?_⟩
  · intro r hr
    rw [hder r hr]
    have h2 : 0 < r * (r + 2) ^ 2 := by positivity
    rw [div_eq_zero_iff, mul_eq_zero, sub_eq_zero, sub_eq_zero]
    simp only [h2.ne', or_false]
  · rw [Set.disjoint_left]
    intro p hs hm
    obtain ⟨σ, rfl⟩ := hm
    exact (hsad _ hs).1 (hminrm σ)
  · rintro p ⟨σ, rfl⟩
    have hg : freeEnergy (11 / 4) (fun i => pointR rm (σ i)) = freeEnergy (11 / 4) (pointR rm) :=
      freeEnergy_perm _ _ σ
    refine ⟨hg, ?_⟩
    rw [hg, freeEnergy_uniform, sub_zero]
    exact freeEnergy_pointR_gap h3rm

end RUF015

section RUF017

lemma two_mul_le_log_div {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    2 * x ≤ Real.log ((1 + x) / (1 - x)) := by
  have habs : |x| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hle := le_hasSum hs 0 (fun j _ => by
    have : 0 ≤ x ^ (2 * j + 1) := pow_nonneg h0 _
    positivity)
  rw [Real.log_div (by linarith) (by linarith)]
  simpa using hle

/-- Symmetrisation of the two last coordinates at a fixed first coordinate. -/
lemma freeEnergy_symm_le {β : ℝ} {a b c : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hbc : c ≤ b) (hβm : β * (b + c) ≤ 2) :
    freeEnergy β ![a, (b + c) / 2, (b + c) / 2] ≤ freeEnergy β ![a, b, c] := by
  set m : ℝ := (b + c) / 2 with hm
  set t : ℝ := (b - c) / 2 with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have htm : t ≤ m := by rw [ht, hm]; linarith
  have hm0 : 0 ≤ m := by rw [hm]; linarith
  set p : Fin 3 → ℝ := ![a, m, m] with hp
  set h : Fin 3 → ℝ := ![0, 1, -1] with hh
  have hq : p + t • h = ![a, b, c] := by
    funext i; fin_cases i <;> simp [hp, hh, hm, ht] <;> ring
  have hp0 : p + (0 : ℝ) • h = p := by simp
  have hmono : MonotoneOn (fun s : ℝ => freeEnergy β (p + s • h)) (Set.Icc 0 m) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 m) ?_ ?_ ?_
    · exact ((continuous_freeEnergy β).comp (by fun_prop)).continuousOn
    · intro s hs
      rw [interior_Icc] at hs
      have hpos : ∀ i, 0 < p i + s * h i := by
        intro i; fin_cases i <;> simp [hp, hh] <;> linarith [hs.1, hs.2]
      exact (hasDerivAt_line_shift β p h hpos).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hpos : ∀ i, 0 < p i + s * h i := by
        intro i; fin_cases i <;> simp [hp, hh] <;> linarith [hs.1, hs.2]
      rw [(hasDerivAt_line_shift β p h hpos).deriv]
      simp only [Fin.sum_univ_three, hp, hh]
      simp
      have hlt : s / m < 1 := by rw [div_lt_one (by linarith [hs.1, hs.2])]; exact hs.2
      have key := two_mul_le_log_div (div_nonneg hs.1.le (by linarith [hs.1, hs.2])) hlt
      have hmpos : 0 < m := by linarith [hs.1, hs.2]
      have e : (1 + s / m) / (1 - s / m) = (m + s) / (m - s) := by
        have : m - s ≠ 0 := by linarith [hs.2]
        field_simp
      rw [e] at key
      rw [Real.log_div (by linarith [hs.1]) (by linarith [hs.2])] at key
      have hmul3 : Real.log (3 * (m + s)) - Real.log (3 * (m - s)) =
          Real.log (m + s) - Real.log (m - s) := by
        rw [Real.log_mul (by norm_num) (by linarith [hs.1]),
          Real.log_mul (by norm_num) (by linarith [hs.2])]
        ring
      have h2 : 2 * (s / m) ≥ β * (2 * s) := by
        have h3 : β * m ≤ 1 := by
          have : β * (b + c) ≤ 2 := hβm
          rw [hm]; nlinarith
        rw [ge_iff_le, ← sub_nonneg]
        have : 2 * (s / m) - β * (2 * s) = 2 * s * (1 - β * m) / m := by field_simp
        rw [this]
        exact div_nonneg (mul_nonneg (by linarith [hs.1]) (by linarith)) hmpos.le
      have e2 : m + -s = m - s := by ring
      rw [e2]
      linarith
  have := hmono ⟨le_refl _, hm0⟩ ⟨ht0, htm⟩ ht0
  beta_reduce at this
  rw [hp0, hq] at this
  exact this

lemma freeEnergy_section_ge {q : Fin 3 → ℝ} (hq : q ∈ simplex) {j : Fin 3} (hj : 1 / 2 ≤ q j) :
    freeEnergy (11 / 4) ![q j, (1 - q j) / 2, (1 - q j) / 2] ≤ freeEnergy (11 / 4) q := by
  have core : ∀ q ∈ simplex, 1 / 2 ≤ q 0 → q 2 ≤ q 1 →
      freeEnergy (11 / 4) ![q 0, (1 - q 0) / 2, (1 - q 0) / 2] ≤ freeEnergy (11 / 4) q := by
    intro q hq h0 h21
    have hsum : q 0 + q 1 + q 2 = 1 := by
      have := hq.2; simpa [Fin.sum_univ_three, add_assoc] using this
    have hqe : q = ![q 0, q 1, q 2] := by funext i; fin_cases i <;> rfl
    have e : (1 - q 0) / 2 = (q 1 + q 2) / 2 := by linarith
    rw [e]
    conv_rhs => rw [hqe]
    refine freeEnergy_symm_le (by linarith) (hq.1 1) (hq.1 2) h21 ?_
    have := hq.1 1; have := hq.1 2
    nlinarith
  have core' : ∀ q ∈ simplex, 1 / 2 ≤ q 0 →
      freeEnergy (11 / 4) ![q 0, (1 - q 0) / 2, (1 - q 0) / 2] ≤ freeEnergy (11 / 4) q := by
    intro q hq h0
    rcases le_total (q 2) (q 1) with h | h
    · exact core q hq h0 h
    · have hq' : (fun i => q (Equiv.swap (1 : Fin 3) 2 i)) ∈ simplex := by
        refine ⟨fun i => hq.1 _, ?_⟩
        rw [Equiv.sum_comp (Equiv.swap (1 : Fin 3) 2) q]; exact hq.2
      have s0 : Equiv.swap (1 : Fin 3) 2 0 = 0 := by decide
      have s1 : Equiv.swap (1 : Fin 3) 2 1 = 2 := by decide
      have s2 : Equiv.swap (1 : Fin 3) 2 2 = 1 := by decide
      have := core _ hq' (by simpa [s0] using h0) (by simpa [s1, s2] using h)
      rw [freeEnergy_perm] at this
      simpa [s0] using this
  have hq' : (fun i => q (Equiv.swap (0 : Fin 3) j i)) ∈ simplex := by
    refine ⟨fun i => hq.1 _, ?_⟩
    rw [Equiv.sum_comp (Equiv.swap (0 : Fin 3) j) q]; exact hq.2
  have := core' _ hq' (by simpa using hj)
  rw [freeEnergy_perm] at this
  simpa using this

lemma pointR_pos {r : ℝ} (hr : 0 < r) (i : Fin 3) : 0 < pointR r i := by
  fin_cases i <;> simp [pointR] <;> positivity

lemma pointR_mem_simplex {r : ℝ} (hr : 0 < r) : pointR r ∈ simplex := by
  refine ⟨fun i => (pointR_pos hr i).le, ?_⟩
  simp [Fin.sum_univ_three, pointR]
  field_simp
  ring

lemma freeEnergy_pointR_eq (β : ℝ) {r : ℝ} (hr : 0 < r) :
    freeEnergy β (pointR r) =
      Real.log 3 - Real.log (r + 2) + r / (r + 2) * Real.log r - β * (r - 1) ^ 2 / (3 * (r + 2) ^ 2) := by
  have h2 : 0 < r + 2 := by linarith
  simp only [freeEnergy, entropy, Fin.sum_univ_three, pointR]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  have e1 : Real.log (3 * (r / (r + 2))) = Real.log 3 + Real.log r - Real.log (r + 2) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_div hr.ne' h2.ne']; ring
  have e2 : Real.log (3 * (1 / (r + 2))) = Real.log 3 - Real.log (r + 2) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_div one_ne_zero h2.ne']
    simp
    ring
  rw [e1, e2]
  field_simp
  ring

lemma hasDerivAt_freeEnergy_pointR (β : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun x : ℝ => freeEnergy β (pointR x)) (2 * criticalFunction β r / (r + 2) ^ 2) r := by
  have h2 : 0 < r + 2 := by linarith
  have hr2 : r + 2 ≠ 0 := h2.ne'
  have hlin : HasDerivAt (fun x : ℝ => x + 2) 1 r := (hasDerivAt_id r).add_const 2
  have hlog2 : HasDerivAt (fun x : ℝ => Real.log (x + 2)) (1 / (r + 2)) r := by
    simpa using hlin.log hr2
  have hlogr : HasDerivAt Real.log (r⁻¹) r := Real.hasDerivAt_log hr.ne'
  have hq : HasDerivAt (fun x : ℝ => x / (x + 2)) ((1 * (r + 2) - r * 1) / (r + 2) ^ 2) r :=
    (hasDerivAt_id r).div hlin hr2
  have hn : HasDerivAt (fun x : ℝ => (x - 1) ^ 2) (2 * (r - 1)) r := by
    refine (((hasDerivAt_pow 2 (r - 1)).comp r ((hasDerivAt_id r).sub_const 1))).congr_deriv ?_
    norm_num
  have hd : HasDerivAt (fun x : ℝ => 3 * (x + 2) ^ 2) (3 * (2 * (r + 2))) r := by
    refine ((((hasDerivAt_pow 2 (r + 2)).comp r hlin)).const_mul 3).congr_deriv ?_
    norm_num
  have hfrac : HasDerivAt (fun x : ℝ => β * (x - 1) ^ 2 / (3 * (x + 2) ^ 2))
      ((β * (2 * (r - 1)) * (3 * (r + 2) ^ 2) - β * (r - 1) ^ 2 * (3 * (2 * (r + 2)))) /
        (3 * (r + 2) ^ 2) ^ 2) r := by
    exact (hn.const_mul β).fun_div hd (by positivity)
  have hall := (((hasDerivAt_const r (Real.log 3)).sub hlog2).add (hq.mul hlogr)).sub hfrac
  have hev : (fun x : ℝ => freeEnergy β (pointR x)) =ᶠ[𝓝 r]
      fun x : ℝ => Real.log 3 - Real.log (x + 2) + x / (x + 2) * Real.log x -
        β * (x - 1) ^ 2 / (3 * (x + 2) ^ 2) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx using freeEnergy_pointR_eq β hx
  refine (hall.congr_of_eventuallyEq hev).congr_deriv ?_
  simp only [criticalFunction]
  field_simp
  ring

/-- Sign pattern of `f_{11/4}` between its consecutive positive roots `1 < rs < rm`. -/
lemma criticalFunction_sign_between {rs rm : ℝ} (h2rs : 2 < rs) (hrs3 : rs < 3) (h3rm : 3 < rm)
    (hroots : ∀ r : ℝ, 0 < r → (criticalFunction (11 / 4) r = 0 ↔ r = 1 ∨ r = rs ∨ r = rm)) :
    (∀ r : ℝ, 1 < r → r < rs → 0 < criticalFunction (11 / 4) r) ∧
      (∀ r : ℝ, rs < r → r < rm → criticalFunction (11 / 4) r < 0) := by
  obtain ⟨f2, f3, -⟩ := criticalFunction_eleven_quarters_signs
  have hroot : ∀ x y : ℝ, 0 < x → 0 < y →
      (criticalFunction (11 / 4) x ≤ 0 ∧ 0 ≤ criticalFunction (11 / 4) y ∨
        criticalFunction (11 / 4) y ≤ 0 ∧ 0 ≤ criticalFunction (11 / 4) x) →
      ∃ c ∈ Set.uIcc x y, criticalFunction (11 / 4) c = 0 := by
    intro x y hx hy h
    have hcont : ContinuousOn (criticalFunction (11 / 4)) (Set.uIcc x y) :=
      criticalFunction_continuousOn_pos (fun z hz => by
        rw [Set.mem_uIcc] at hz
        rcases hz with hz | hz <;> exact lt_of_lt_of_le (by assumption) hz.1) _
    have h0 : (0 : ℝ) ∈ Set.uIcc (criticalFunction (11 / 4) x) (criticalFunction (11 / 4) y) := by
      rw [Set.mem_uIcc]
      rcases h with h | h
      · exact Or.inl ⟨h.1, h.2⟩
      · exact Or.inr ⟨h.1, h.2⟩
    obtain ⟨c, hc, hc0⟩ := intermediate_value_uIcc hcont h0
    exact ⟨c, hc, hc0⟩
  refine ⟨fun r hr1 hr2 => ?_, fun r hr1 hr2 => ?_⟩
  · by_contra hneg
    rw [not_lt] at hneg
    obtain ⟨c, hc, hc0⟩ := hroot r 2 (by linarith) (by norm_num) (Or.inl ⟨hneg, f2.le⟩)
    rw [Set.mem_uIcc] at hc
    have hc1 : 1 < c := by rcases hc with hc | hc <;> linarith [hc.1]
    have hc2 : c < rs := by rcases hc with hc | hc <;> linarith [hc.2]
    rcases (hroots c (by linarith)).1 hc0 with h | h | h <;> linarith
  · by_contra hneg
    rw [not_lt] at hneg
    obtain ⟨c, hc, hc0⟩ := hroot r 3 (by linarith) (by norm_num) (Or.inr ⟨f3.le, hneg⟩)
    rw [Set.mem_uIcc] at hc
    have hc1 : rs < c := by rcases hc with hc | hc <;> linarith [hc.1]
    have hc2 : c < rm := by rcases hc with hc | hc <;> linarith [hc.2]
    rcases (hroots c (by linarith)).1 hc0 with h | h | h <;> linarith

lemma continuousOn_pointR : ContinuousOn pointR (Set.Ioi 0) := by
  have hden : ∀ x ∈ Set.Ioi (0 : ℝ), x + 2 ≠ 0 := fun x hx => by
    have : (0 : ℝ) < x := hx
    linarith
  have h0 : ContinuousOn (fun x : ℝ => x / (x + 2)) (Set.Ioi 0) :=
    continuousOn_id.div (continuousOn_id.add continuousOn_const) hden
  have h1 : ContinuousOn (fun x : ℝ => 1 / (x + 2)) (Set.Ioi 0) :=
    continuousOn_const.div (continuousOn_id.add continuousOn_const) hden
  rw [continuousOn_pi]
  intro i
  fin_cases i
  · exact h0.congr (fun x _ => by simp [pointR])
  · exact h1.congr (fun x _ => by simp [pointR])
  · exact h1.congr (fun x _ => by simp [pointR])

/-- A continuous path in the simplex from `x` to `y`, parametrized by `[0,1]`. -/
def IsSimplexPath (x y : Fin 3 → ℝ) (γ : ℝ → Fin 3 → ℝ) : Prop :=
  ContinuousOn γ (Set.Icc 0 1) ∧ (∀ s ∈ Set.Icc (0 : ℝ) 1, γ s ∈ simplex) ∧ γ 0 = x ∧ γ 1 = y

lemma pointR_eq_section {r : ℝ} (hr : 0 < r) :
    ![r / (r + 2), (1 - r / (r + 2)) / 2, (1 - r / (r + 2)) / 2] = pointR r := by
  have h2 : r + 2 ≠ 0 := by linarith
  funext i
  fin_cases i <;> simp [pointR] <;> field_simp <;> ring

lemma quadratic_lower_orbit {β r : ℝ} (hc : IsInteriorCriticalPoint β (pointR r)) {κ : ℝ}
    (hκ : 0 < κ)
    (hQ : ∀ h : Fin 3 → ℝ, ∑ i, h i = 0 → κ * ∑ i, h i ^ 2 ≤ hessianForm β (pointR r) h)
    (σ : Equiv.Perm (Fin 3)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ simplex, dist q (fun i => pointR r (σ i)) < δ →
      freeEnergy β (pointR r) + κ / 4 * ∑ i, (q i - pointR r (σ i)) ^ 2 ≤ freeEnergy β q := by
  have hQ' : ∀ h : Fin 3 → ℝ, ∑ i, h i = 0 →
      κ * ∑ i, h i ^ 2 ≤ hessianForm β (fun i => pointR r (σ i)) h := by
    intro h hh
    rw [hessianForm_perm]
    have := hQ (fun i => h (σ.symm i)) (by rw [Equiv.sum_comp σ.symm h]; exact hh)
    rwa [Equiv.sum_comp σ.symm (fun j => h j ^ 2)] at this
  obtain ⟨δ, hδ, hb⟩ := quadratic_lower_of_hessian_pos β (isInteriorCriticalPoint_perm hc σ) hκ hQ'
  refine ⟨δ, hδ, fun q hq hd => ?_⟩
  have := hb q hq hd
  rwa [freeEnergy_perm] at this

/-- **RUF017, exact discrete path barrier** at `β₀ = 11/4`.  With `rs < rm` the saddle and
minimum radii of RUF015, `Δ∞ = F(p(rm))` and `B∞ = F(p(rs))` satisfy `B∞ > Δ∞ > 0`, with the branch
derivative `d/dr F(p(r)) = 2 f(r)/(r+2)²`; for every ordered minimum `p` (a permutation of
`p(rm)`) the minimax value over continuous simplex paths from `p` to the uniform point is exactly
`B∞` (it is attained by the branch, and every path reaches at least `B∞`); and around each ordered
minimum a small closed ball inside the simplex interior carries the quadratic lower bound
`F(q) ≥ Δ∞ + c ∑ (qᵢ - pᵢ)²`, hence a strict positive boundary barrier `c ε²`. -/
theorem exact_discrete_path_barrier :
    ∃ rs rm : ℝ, 2 < rs ∧ rs < rm ∧ 3 < rm ∧ rm < 4 ∧
      (∀ r : ℝ, 0 < r → (criticalFunction (11 / 4) r = 0 ↔ r = 1 ∨ r = rs ∨ r = rm)) ∧
      (∀ r : ℝ, 0 < r → HasDerivAt (fun x : ℝ => freeEnergy (11 / 4) (pointR x))
        (2 * criticalFunction (11 / 4) r / (r + 2) ^ 2) r) ∧
      0 < freeEnergy (11 / 4) (pointR rm) ∧
      freeEnergy (11 / 4) (pointR rm) < freeEnergy (11 / 4) (pointR rs) ∧
      (∀ p ∈ pointROrbit rm,
        IsLeast {c : ℝ | ∃ γ : ℝ → Fin 3 → ℝ, IsSimplexPath p (fun _ => 1 / 3) γ ∧
          ∃ s ∈ Set.Icc (0 : ℝ) 1, IsMaxOn (fun t => freeEnergy (11 / 4) (γ t)) (Set.Icc 0 1) s ∧
            c = freeEnergy (11 / 4) (γ s)} (freeEnergy (11 / 4) (pointR rs))) ∧
      (∀ p ∈ pointROrbit rm, ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ (∀ i, ε < p i) ∧
        (∀ q ∈ simplex, dist q p ≤ ε →
          freeEnergy (11 / 4) (pointR rm) + c * ∑ i, (q i - p i) ^ 2 ≤ freeEnergy (11 / 4) q) ∧
        (∀ q ∈ simplex, dist q p = ε →
          freeEnergy (11 / 4) (pointR rm) + c * ε ^ 2 ≤ freeEnergy (11 / 4) q)) := by
  obtain ⟨-, -, rs, rm, h2rs, hrsdp, h3rm, hrm4, hroots, hds, hdm, -⟩ :=
    complete_roots_and_critical_landscape_at_eleven_quarters
  obtain ⟨s5, s6⟩ := sqrt33_bounds
  have hrs3 : rs < 3 := by linarith
  have hrs0 : 0 < rs := by linarith
  have hrm0 : 0 < rm := by linarith
  have hrsrm : rs < rm := by linarith
  obtain ⟨hsg1, hsg2⟩ := criticalFunction_sign_between h2rs hrs3 h3rm hroots
  set g : ℝ → ℝ := fun x => freeEnergy (11 / 4) (pointR x) with hg
  have hgd : ∀ r : ℝ, 0 < r → HasDerivAt g (2 * criticalFunction (11 / 4) r / (r + 2) ^ 2) r :=
    fun r hr => hasDerivAt_freeEnergy_pointR (11 / 4) hr
  have hgcont : ContinuousOn g (Set.Ioi 0) := fun r hr => (hgd r hr).continuousAt.continuousWithinAt
  -- monotone pieces
  have hmonoL : MonotoneOn g (Set.Icc 1 rs) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 1 rs)
      (hgcont.mono fun x hx => by have := hx.1; exact lt_of_lt_of_le one_pos this) ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      exact (hgd x (by linarith [hx.1])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hgd x (by linarith [hx.1])).deriv]
      have := hsg1 x hx.1 hx.2
      exact div_nonneg (by linarith) (sq_nonneg _)
  have hantiR : StrictAntiOn g (Set.Icc rs rm) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc rs rm)
      (hgcont.mono fun x hx => by have := hx.1; exact lt_of_lt_of_le hrs0 this) ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hgd x (by linarith [hx.1])).deriv]
    have := hsg2 x hx.1 hx.2
    have hx0 : 0 < x := by linarith [hx.1]
    have : 0 < (x + 2) ^ 2 := by positivity
    exact div_neg_of_neg_of_pos (by linarith) this
  have hBmax : ∀ r ∈ Set.Icc 1 rm, g r ≤ g rs := by
    intro r hr
    rcases le_total r rs with h | h
    · exact hmonoL ⟨hr.1, h⟩ ⟨by linarith [hr.1], le_refl _⟩ h
    · exact hantiR.antitoneOn ⟨le_refl _, hrsrm.le⟩ ⟨h, hr.2⟩ h
  have hlt : g rm < g rs := hantiR ⟨le_refl _, hrsrm.le⟩ ⟨hrsrm.le, le_refl _⟩ hrsrm
  have hΔ : 0 < g rm := by
    have := freeEnergy_pointR_gap h3rm
    exact lt_trans (by norm_num) this
  have hcrm : IsInteriorCriticalPoint (11 / 4) (pointR rm) :=
    isInteriorCriticalPoint_pointR (11 / 4) rm hrm0 ((hroots rm hrm0).2 (Or.inr (Or.inr rfl)))
  have hmemσ : ∀ (σ : Equiv.Perm (Fin 3)) {r : ℝ}, 0 < r →
      (fun i => pointR r (σ i)) ∈ simplex := fun σ r hr => by
    refine ⟨fun i => (pointR_mem_simplex hr).1 _, ?_⟩
    rw [Equiv.sum_comp σ (pointR r)]; exact (pointR_mem_simplex hr).2
  refine ⟨rs, rm, h2rs, hrsrm, h3rm, hrm4, hroots, hgd, hΔ, hlt, ?_, ?_⟩
  · rintro p ⟨σ, rfl⟩
    set ρ : ℝ → ℝ := fun s => rm + s * (1 - rm) with hρ
    have hρmem : ∀ s ∈ Set.Icc (0 : ℝ) 1, ρ s ∈ Set.Icc 1 rm := fun s hs =>
      ⟨by simp only [hρ]; nlinarith [hs.1, hs.2], by simp only [hρ]; nlinarith [hs.1, hs.2]⟩
    have hρpos : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < ρ s := fun s hs => by
      have := (hρmem s hs).1; linarith
    constructor
    · have hs0 : (rm - rs) / (rm - 1) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (by linarith) (by linarith),
          (div_le_one (by linarith)).2 (by linarith)⟩
      have hρs : ρ ((rm - rs) / (rm - 1)) = rs := by
        have hne : rm - 1 ≠ 0 := by linarith
        simp only [hρ]
        field_simp
        ring
      have hc : ContinuousOn (fun s => pointR (ρ s)) (Set.Icc 0 1) :=
        continuousOn_pointR.comp (by fun_prop) (fun s hs => hρpos s hs)
      refine ⟨fun s i => pointR (ρ s) (σ i),
        ⟨continuousOn_pi.2 fun i => (continuousOn_pi.1 hc) (σ i),
          fun s hs => hmemσ σ (hρpos s hs), ?_, ?_⟩,
        (rm - rs) / (rm - 1), hs0, ?_, ?_⟩
      · funext i; simp [hρ]
      · funext i
        have : ρ 1 = 1 := by simp [hρ]
        simp only [this, pointR_one]
      · rw [isMaxOn_iff]
        intro t ht
        rw [freeEnergy_perm, freeEnergy_perm, hρs]
        exact hBmax _ (hρmem t ht)
      · rw [freeEnergy_perm, hρs]
    · rintro c ⟨γ, ⟨hcont, hsimp, h0, h1⟩, s0, hs0, hmax, rfl⟩
      set j : Fin 3 := σ.symm 0 with hj
      have hfj : ContinuousOn (fun s => γ s j) (Set.Icc 0 1) :=
        (continuous_apply j).comp_continuousOn hcont
      have hf0 : γ 0 j = rm / (rm + 2) := by
        rw [h0]; simp [hj, pointR]
      have hf1 : γ 1 j = 1 / 3 := by rw [h1]
      have has : rs / (rs + 2) ∈ Set.Icc (γ 1 j) (γ 0 j) := by
        rw [hf0, hf1]
        refine ⟨?_, ?_⟩
        · rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
        · rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
      obtain ⟨s1, hs1, hs1e⟩ := intermediate_value_Icc' zero_le_one hfj has
      have hsec := freeEnergy_section_ge (hsimp s1 hs1) (j := j)
        (by simp only at hs1e; rw [hs1e, le_div_iff₀ (by linarith)]; linarith)
      simp only at hs1e
      rw [hs1e, pointR_eq_section hrs0] at hsec
      exact hsec.trans ((isMaxOn_iff.1 hmax) s1 hs1)
  · rintro p ⟨σ, rfl⟩
    obtain ⟨κ, hκ, hQ⟩ := exists_hessian_lower_pointR (11 / 4) rm (by linarith) (by norm_num) hdm
    obtain ⟨δ, hδ, hb⟩ := quadratic_lower_orbit hcrm hκ hQ σ
    set m0 : ℝ := min (pointR rm 0) (min (pointR rm 1) (pointR rm 2)) with hm0
    have hm0pos : 0 < m0 := lt_min (pointR_pos hrm0 0)
      (lt_min (pointR_pos hrm0 1) (pointR_pos hrm0 2))
    have hm0le : ∀ j, m0 ≤ pointR rm j := by
      intro j; fin_cases j
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (min_le_left _ _)
      · exact (min_le_right _ _).trans (min_le_right _ _)
    set ε : ℝ := min (δ / 2) (m0 / 2) with hε
    have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
    have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hεm : ε < m0 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hlow : ∀ q ∈ simplex, dist q (fun i => pointR rm (σ i)) ≤ ε →
        freeEnergy (11 / 4) (pointR rm) +
          κ / 4 * ∑ i, (q i - pointR rm (σ i)) ^ 2 ≤ freeEnergy (11 / 4) q :=
      fun q hq hd => hb q hq (lt_of_le_of_lt hd hεδ)
    refine ⟨ε, κ / 4, hε0, by positivity, fun i => lt_of_lt_of_le hεm (hm0le _), hlow, ?_⟩
    intro q hq hd
    have hex : ∃ i, ε ≤ |q i - pointR rm (σ i)| := by
      by_contra hcon
      rw [not_exists] at hcon
      have : dist q (fun i => pointR rm (σ i)) < ε := by
        rw [dist_pi_lt_iff hε0]
        intro i
        rw [Real.dist_eq]
        exact not_le.1 (hcon i)
      linarith
    obtain ⟨i, hi⟩ := hex
    have hsq : ε ^ 2 ≤ ∑ i, (q i - pointR rm (σ i)) ^ 2 := by
      have h1 : ε ^ 2 ≤ (q i - pointR rm (σ i)) ^ 2 := by
        rw [← sq_abs (q i - pointR rm (σ i))]
        exact pow_le_pow_left₀ hε0.le hi 2
      exact h1.trans (Finset.single_le_sum (f := fun i => (q i - pointR rm (σ i)) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ i))
    have := hlow q hq hd.le
    nlinarith

end RUF017

end DGPS.Examples.RoughBoundary.ThreeState
